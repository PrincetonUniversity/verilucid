include "AST.dfy"

include "LAST.dfy"
include "PPrintAst.dfy"
include "MapVisitor.dfy"
include "Analysis.dfy"

module Translator {
  import opened Std.Wrappers
  import opened Std.Collections


  import opened DAST
  import opened LAST
  import opened MapVisitor
  import Analysis
  import PPrint

  /* translators */
  datatype err = 
    | Base(msg:string)
    | Acc(msg:string, causes:seq<err>)

  function errStr(e:err) : string 
  decreases e, 0
  {
    match e {
      case Base(msg) => msg
      case Acc(msg, causes) => 
          msg + "(" + "\n" 
        + PPrint.indent(errStrs(causes)) + "\n"
        + ")"
    }
  }

  function errStrs(es:seq<err>) : string 
  decreases es, 1
  {
    // var argStr := seq(|args|, i requires 0 <= i < |args| => ExpressionToString(args[i]));         
    var strs := seq(|es|, i requires 0 <= i < |es| => errStr(es[i]));
    PPrint.newline_sep(strs, x => x)
  }

  datatype res<t> = 
    | Res(t)
    | Err(err)

  function baseErr<t>(msg:string) : res<t> {
    Err(Base(msg))
  }
  function accErr<t>(msg:string, causes:seq<err>) : res<t> {
    Err(Acc(msg, causes))
  }

  // names to idenfify program components
  const progClassName := Name("Program")
  const eventDatatypeName := Name("Event")
  // const dispatchMethodName := Name("dispatch")
  const ctorMethodName := Name("__ctor")

  // Attribute tags the user places on declarations to be compiled. See
  // design-and-roadmap.md: user declarations are recognized by tag, library
  // types by name.
  const lucidProgramTag := "lucid_program"
  const lucidModuleTag  := "lucid_module"
  const lucidEventTag   := "lucid_event"
  const lucidRecordTag  := "lucid_record"

  predicate hasTag(attrs: seq<Attribute>, tag: string)
  {
    if |attrs| == 0 then false
    else attrs[0].name == tag || hasTag(attrs[1..], tag)
  }

  // Match a type path by its final segment (the type name), ignoring the
  // enclosing module qualifier.
  predicate pathLeafIs(path: seq<Ident>, name: string)
  {
    |path| > 0 && path[|path| - 1].id.dafny_name == name
  }

  function pathLeafName(path: seq<Ident>): string
    requires |path| > 0
  {
    path[|path| - 1].id.dafny_name
  }

  // The Lucid library's sized integer types (LucidTypes.uintN) are subset types
  // that encode their bit width in the name, so we recognize any `uint<N>` by
  // parsing the width. Returns 0 for non-uint names (no valid uint has width 0).
  predicate isDigit(c: char) { '0' <= c <= '9' }
  predicate allDigits(s: string) { forall i :: 0 <= i < |s| ==> isDigit(s[i]) }
  function charToNat(c: char): nat requires isDigit(c) { (c as int) - ('0' as int) }
  function parseNat(s: string): nat
    requires allDigits(s)
  {
    if |s| == 0 then 0
    else parseNat(s[..|s| - 1]) * 10 + charToNat(s[|s| - 1])
  }
  function uintWidthOrZero(name: string): nat
  {
    if |name| > 4 && name[..4] == "uint" && allDigits(name[4..])
    then parseNat(name[4..])
    else 0
  }

  // The library width-cast helpers `to_uintN` (e.g. `to_uint32`). Dafny escapes
  // `_` as `__` in DAST identifiers, so the name arrives as `to__uintN`.
  predicate isToUintName(name: string)
  {
    (|name| > 7 && name[..7] == "to_uint" && allDigits(name[7..])) ||
    (|name| > 8 && name[..8] == "to__uint" && allDigits(name[8..]))
  }
  // the target width N of a `to_uintN` / `to__uintN` name.
  function toUintWidth(name: string): nat
    requires isToUintName(name)
  {
    if |name| > 7 && name[..7] == "to_uint" && allDigits(name[7..]) then parseNat(name[7..])
    else parseNat(name[8..])
  }

  function countLeadingDigits(s: string): nat
  {
    if |s| == 0 || !isDigit(s[0]) then 0 else 1 + countLeadingDigits(s[1..])
  }
  // Dafny leaves a `for i := ...` loop header's boundName as `i`, but uniquifies
  // uses of `i` in the body to `_<n>_i`. Recognize that uniquified form so the
  // comprehension binder and its body uses can be reconciled to one name.
  predicate isUniqLoopVar(s: string, base: string)
  {
    |s| >= 3 && s[0] == '_' &&
    var d := countLeadingDigits(s[1..]);
    d > 0 && 1 + d < |s| && s[1 + d] == '_' && s[2 + d..] == base
  }

  // Fixed-length sequence types (`LucidTypes.seqN`) are subset types of `seq<t>`
  // that encode their length in the name (`seq16` -> 16). Returns 0 for names
  // that aren't `seq<digits>` (no valid fixed-length seq has length 0).
  function seqLenOrZero(name: string): nat
  {
    if |name| > 3 && name[..3] == "seq" && allDigits(name[3..])
    then parseNat(name[3..])
    else 0
  }

  // The array data-structure type: old `ArrayMemops.ArrayVar` and new
  // `LucidObjects.VarArray`, matched by leaf name.
  predicate isArrayVarType(t: Type)
  {
    match t {
      case UserDefined(ResolvedType(path, _, _, _, _, _)) =>
        pathLeafIs(path, "VarArray") || pathLeafIs(path, "ArrayVar")
      case _ => false
    }
  }

  // Dafny compiles a `const` field to a DAST name with an `_i_` prefix (and
  // escapes `_` as `__`), but reads of it in method bodies use the unprefixed
  // name. Strip the prefix so a global's definition and its uses agree.
  function normFieldName(s: string): string
  {
    if |s| >= 3 && s[..3] == "_i_" then s[3..] else s
  }

  // If `t` is a reference to a user-defined `{:lucid_module}` instance, the
  // module's name (so a method call `x.op(..)` becomes `Module.op(x, ..)`).
  function moduleTypeName(t: Type): Option<string>
  {
    match t {
      case UserDefined(ResolvedType(path, _, _, attrs, _, _)) =>
        if |path| > 0 && hasTag(attrs, lucidModuleTag) then Some(pathLeafName(path)) else None
      case _ => None
    }
  }

  // The switch model type (`LucidSwitch.Switch`). It has no Lucid representation
  // (the switch is implicit hardware): the field is dropped and its methods
  // translate to generate statements.
  predicate isSwitchType(t: Type)
  {
    match t {
      case UserDefined(ResolvedType(path, _, _, _, _, _)) => pathLeafIs(path, "Switch")
      case _ => false
    }
  }

  predicate anySwitchType(tys: seq<Type>)
  {
    if |tys| == 0 then false else isSwitchType(tys[0]) || anySwitchType(tys[1..])
  }

  // The event field the switch will set before dispatch (like timestamp).
  // Modeled today as an explicit event/handler parameter; dropped in translation
  // so bodies referencing `ingress_port` bind to the Lucid builtin. Temporary.
  // Dafny escapes `_` as `__` in DAST identifiers, so accept either form.
  predicate isIngressPortName(s: string)
  {
    s == "ingress_port" || s == "ingress__port"
  }

  // methods  and modules that don't get translated because they represent 
  // builtin mechanisms of the platform.
  // ArrayMemops / StateMemops hold library types recognized by name; their
  // classes are untagged, so trClass skips them anyway. Kept as a cheap
  // short-circuit. `_module` (the flat top-level) is intentionally NOT skipped:
  // tag-based programs live there.
  const SkipModules := {
    Name("ArrayMemops"),
    Name("StateMemops")
  }
  const SkipMethods := {
    Name("dispatch"),
    Name("simulateArrival"),
    Name("pickNextEvent"),
    Name("generateRecircEvent"),
    Name("simulatedClockTick"),
    Name("simulatedHardwareFailure")
  }

  // fully qualified names of types
  const arrayIdent := Ident.Ident(Name("ArrayMemops"))

  // special data structure types
  const arrayVarTyPath := [arrayIdent, Ident.Ident(Name("ArrayVar"))]
  const arrayTy := "Array.t"
  const boolArrayTy := "BoolArray.t"

  // primitive types
  const natTyPath := [Ident.Ident(Name("_System")), Ident.Ident(Name("nat"))]
  const intSz :nat := 32
  // TODO: parse "bits" and "counter" sizes from the program,
  //       or force users to use some specific sized int types.
  const bitsSz :nat := 8
  const counterSz := 32

  // Reserved leaf type-names recognized by name, independent of the enclosing
  // module (retires the old LucidProg-qualified path matching). See
  // design-and-roadmap.md.
  const eventTyName := "Event"
  const recircCmdTyName := "RecircCmd"
  const bitsTyName := "bits"
  const counterTyName := "counter"

  method trType(typ: Type) returns (r:res<ty>) {
    var typ_str := PPrint.typeToString(typ);
    match typ {
      case Primitive(Int) => {
        r := Res(TInt(intSz));
      }
      case Primitive(Bool) => {
        r := Res(TBool);
      }
      case UserDefined(ResolvedType(path, typeArgs, kind, attributes, properMethods, extendedTypes)) => {
        if path == arrayVarTyPath || pathLeafIs(path, "VarArray") {
          if |typeArgs| == 1 {
              var cellTy := trType(typeArgs[0]);
              match cellTy {
                case Res(TBool) => {r := Res(TGlobal(boolArrayTy, NoTyArgs));}
                case Res(TInt(sz)) => {r := Res(TGlobal(arrayTy, Sizes([sz])));}
                case _ => {
                  print ("[trType]: unsupported cell type in array.\n");
                  r := baseErr("unsupported cell type in array");
                }
              }
          }
          else {
            print ("[trType]: wrong number of type args for array type.\n");
            r := baseErr("[trType]: wrong number of type args for array type.");
          }
        } else if (|path| > 0 && uintWidthOrZero(pathLeafName(path)) > 0) {
          r := Res(TInt(uintWidthOrZero(pathLeafName(path))));
        } else if (pathLeafIs(path, bitsTyName)) {
          r := Res(TInt(bitsSz));
        } else if (pathLeafIs(path, counterTyName)) {
          r := Res(TInt(counterSz));
        } else if (path == natTyPath) {
          r := Res(TInt(intSz));
        } else if (pathLeafIs(path, recircCmdTyName)) {
          r := Res(TDafnyGenerateCmd);
        } else if (|path| > 0 && seqLenOrZero(pathLeafName(path)) > 0) {
          // a fixed-length sequence type (`seqN<t>`) -> Lucid vector `elem[N]`.
          // Length is parsed from the name; the element type is the type arg.
          if |typeArgs| == 1 {
            var elemTy := trType(typeArgs[0]);
            match elemTy {
              case Res(et) => r := Res(TVec(et, seqLenOrZero(pathLeafName(path))));
              case Err(e) => r := Err(e);
            }
          } else {
            print ("[trType]: wrong number of type args for seq type.\n");
            r := baseErr("[trType]: wrong number of type args for seq type.");
          }
        } else if (|path| > 0 && hasTag(attributes, lucidRecordTag)) {
          // a reference to a user record type -> the Lucid record type name
          r := Res(TRecord(pathLeafName(path)));
        } else if (|path| > 0 && hasTag(attributes, lucidModuleTag)) {
          // a reference to a user module instance -> the module's `t` type
          r := Res(TGlobal(pathLeafName(path) + ".t", NoTyArgs));
        }
        else {
          match kind {
            // a subset/synonym type (e.g. `index = x: nat | ...`) resolves to its
            // base type; verification already checked the constraint.
            case SynonymType(baseType) => r := trType(baseType);
            case _ => {
              print ("[trType]: unsupported type\n" + typ_str + "\n");
              r := baseErr("unsupported type");
            }
          }
        }
      }
      case typ => {
        print ("[trType]: unsupported type.\n");
        print ("-------------------------\n");
        print (PPrint.typeToString(typ));
        print ("\n-------------------------\n");
        r := baseErr("[trType]: unsupported type");
      }
    }        
  }
  method trTypes(typs: seq<Type>) returns (r:res<seq<ty>>) {
    var inner_rs := [];
    var errs := [];
    for i:=0 to |typs| {
      var tmp := trType(typs[i]);
      match tmp {
        case Res(ty) => {inner_rs := inner_rs + [ty];}
        case Err(e) => {errs := errs + [e];}
      }
    }
    if |errs| > 0 {
      r := accErr("[trTypes]", errs);
    } else {
      r := Res(inner_rs);
    }
  }

  method trTypeToSize(typ: Type) returns (r:res<nat>) {
    r := match typ {
      case Primitive(Int) => Res(intSz)
      case Primitive(Bool) => Res(8)
      case UserDefined(ResolvedType(path, typeArgs, kind, attributes, properMethods, extendedTypes)) => 
        if |path| > 0 && uintWidthOrZero(pathLeafName(path)) > 0 then
          Res(uintWidthOrZero(pathLeafName(path)))
        else if pathLeafIs(path, bitsTyName) then
          Res(bitsSz)
        else if pathLeafIs(path, counterTyName) then
          Res(counterSz)
        else baseErr("[tyTypeToSize] unsupported type")
      case _ => baseErr("[tyTypeToSize] unsupported type")
    };
  }


  method trFormal(fml: Formal) returns (r:res<param>) {
    var ty := trType(fml.typ);
    match ty {
      case Err(s) => {
        print ("[trFormal]: error translating type\n");
        r :=  accErr("[trFormal]", [s]);} 
      case Res(ty) => {r := Res((fml.name.dafny_name, ty));}
    }
  }

  method trFormals(fmls: seq<Formal>) returns (r:res<seq<param>>) {
    var inner_rs := [];
    var errs := [];
    for i:=0 to |fmls| {
      // drop the `ingress_port` param (temporary: modeled as builtin).
      if isIngressPortName(fmls[i].name.dafny_name) {
      } else {
        var tmp := trFormal(fmls[i]);
        match tmp {
          case Res(p) => {inner_rs := inner_rs + [p];}
          case Err(e) => {errs := errs + [e];}
        }
      }
    }
    if |errs| > 0 {
      r := accErr("[trFormals]", errs);
    } else {
      r := Res(inner_rs);
    }
  }

  // datatype op = 
  //   | Add | Sub
  //   | BitOr | BitAnd
  //   | Eq | Neq | Lt | Lte | Gt | Gte
  //   | Or | And | Neg | Not

  // hashn(w, seed, v...) -> hash<w>(seed, v...). `w` must be an integer literal;
  // any seq-literal value arg is flattened into the trailing args.
  method trHash(args: seq<Expression>) returns (r: res<exp>)
  {
    if |args| < 2 {
      r := baseErr("[trHash] hashn expects at least (width, seed)");
      return;
    }
    match args[0] {
      case Literal(IntLiteral(wstr, _)) => {
        if |wstr| == 0 || !allDigits(wstr) {
          r := baseErr("[trHash] hash width must be a non-negative integer literal");
        } else {
          var width := parseNat(wstr);
          var hashArgs : seq<Expression> := [args[1]];
          for i := 2 to |args| {
            match args[i] {
              case SeqValue(elems, _) => hashArgs := hashArgs + elems;
              case _ => hashArgs := hashArgs + [args[i]];
            }
          }
          var translated := trExpressions(hashArgs);
          match translated {
            // hash<w>(...) has type int<w>; our model types the result as `nat`
            // (int<intSz>), so cast to keep assignments/uses well-typed.
            case Res(exps) => r := Res(EOp(IntCast(intSz), [EHash(width, exps)]));
            case Err(e) => r := accErr("[trHash]", [e]);
          }
        }
      }
      case _ => r := baseErr("[trHash] hash width must be an integer literal");
    }
  }

  method trExpression(expr : Expression) returns (r: res<exp>)
  decreases expr
  {
    var estr := PPrint.expressionToString(expr);
    var outstr := "\n[trExpression] current expr--------\n" + estr + "\n--------------------------------\n";
    match expr {
      case Literal(BoolLiteral(b)) => {r:= Res(EVal(VBool(b)));}
      case Literal(IntLiteral(str, typ)) => { 
        var s := trTypeToSize(typ);
        match s {
          case Res(s) => {
            r := Res(EVal(VInt(str, s)));
          }
          case Err(s) => {
            r := accErr("[trExpression.IntLiteral]", [s]);
          }
        }
      }
      case Ident(name) => {
        // a bare `ingress_port` reference binds to the Lucid builtin (canonical
        // single-underscore name), not the escaped `ingress__port`. Temporary.
        if isIngressPortName(name.dafny_name) {
          r := Res(EVar("ingress_port"));
        } else {
          r := Res(EVar(name.dafny_name));
        }
      }
      case Call(on, callName, typeArgs, args) => {
        // hash builtin: hashn(w, seed, v) -> hash<w>(seed, v...) with a seq v flattened.
        var isHash := match callName { case CallName(hn, _, _, _, _) => hn.dafny_name == "hashn" case _ => false };
        if isHash {
          r := trHash(args);
          return;
        }
        // width-cast helpers `to_uintN(x)` -> a Lucid cast `(int<N>)x`. (Memops,
        // which forbid casts, express overflow with `% maxN` instead, which the
        // compiler drops as a same-width no-op.)
        var callId := match callName { case CallName(nm, _, _, _, _) => nm.dafny_name case _ => "" };
        if isToUintName(callId) && |args| == 1 {
          var ce := trExpression(args[0]);
          match ce {
            case Res(c) => r := Res(EOp(IntCast(toUintWidth(callId)), [c]));
            case Err(e) => r := accErr("[trExpression] to_uintN cast operand", [e]);
          }
          return;
        }
        // randomness builtin: rand32() -> Sys.random() (a 32-bit random value).
        if callId == "rand32" && |args| == 0 {
          r := Res(ECall("Sys.random", []));
          return;
        }
        var name_prefix := "";
        match on {
          case Companion(idents, _) => {
            match |idents| {
              case 0 => {}
              case 1 => {
                  print("[trExpression] error: call with 1 ident\n");
                  print(outstr);
                  return baseErr("invalid 'on' in call");
              }
              case 2 => {
                if (idents[0] == arrayIdent) {
                  name_prefix := idents[0].id.dafny_name + ".";
                } else {
                  print ("[trExpression] error: call with 2 idents, but first one is not 'ArrayMemops'\n");
                  print(outstr);
                  return baseErr("[trExpression] unsupported feature: call with on that is not 'this' or 'ArrayMemops'");
                }
              }
              case _ => {
                  print("[trExpression] error: call with >2 idents\n");
                  print(outstr);
                  return baseErr("invalid 'on' in call");
              }
            }
          }
          case This() => {}
          case _ => {
            print ("[trExpression] unsupported feature: call with on that is not 'this' or 'ArrayMemops'\n");
            print(outstr);
            return baseErr("[trExpression] unsupported feature: call with on that is not 'this' or 'ArrayMemops'");
          }
        }
        match callName {
          case CallName(name, _, _, _, _) => {
            var args_rs := trExpressions(args);
            match args_rs {
              case Res(args_rs) => {
                r := Res(ECall(name_prefix + name.dafny_name, args_rs));
              }
              case Err(e) => {
                r := accErr("[trExpression.Call]", [e]);
              }
            }
          }
          //TODO: handle other cases
          case _ => {r := baseErr("[trExpression.Call] unsupported call name");}          
        }
      }
      case BinOp(binop, left, right, format2) => {
        // 1. figure out the op.
        var lucid_op : op;
        match binop.op {
          // the supported operations.
          case Plus(_) => {lucid_op := Add;}
          case Minus(_) => {lucid_op := Sub;}
          case BitwiseAnd => {lucid_op := BitAnd;}
          case BitwiseOr => {lucid_op := BitOr;}
          case BitwiseXor => {lucid_op := BitXor;}
          case BitwiseShiftLeft => {lucid_op := BitShiftL;}
          case BitwiseShiftRight => {lucid_op := BitShiftR;}
          case And => {lucid_op := op.And;}
          case Or => {lucid_op := op.Or;}
          case Eq(_) => {lucid_op := op.Eq;}
          case Lt => {lucid_op := op.Lt;}
          case Mod => {
            print("WARNING: Mod operation may not be translateable >>>>" + estr + "<<<<\n");
            lucid_op := op.DafnyMod;
          }
          case EuclidianMod => {
            print("WARNING: Mod operation may not be translateable >>>>" + estr + "<<<<\n");
            lucid_op := op.DafnyMod;
          }
          case Div(_) => {
            print("WARNING: Divide operation may not be translateable >>>>" + estr + "<<<<\n");
            lucid_op := op.DafnyDiv;
          }
          case EuclidianDiv => {
            print("WARNING: Divide operation may not be translateable >>>>" + estr + "<<<<\n");
            lucid_op := op.DafnyDiv;
          }
          // the restof the operations will likely _never_ be supported
          // because they are about primitive types that lucid doesn't have.
          case _ => {
            print("[trExpression] unsupported op\n");
            print ("-----------\n");
            print (PPrint.expressionToString(expr));
            print ("\n-----------\n");
            r := baseErr("[trExpression] unsupported op");
            return r;
          }
        }
        // 2. translate the left and right expressions
        var left_exp := trExpression(left);
        var right_exp := trExpression(right);
        // 3. match the results
        match (left_exp, right_exp) {
          case (Res(left_exp), Res(right_exp)) => {
            r := Res(EOp(lucid_op, [left_exp, right_exp]));
          }
          case (Err(left_err), Res(_)) => {
            r := accErr("[trExpression] error translating left expression\n" + errStr(left_err), []);
          }
          case (Res(_), Err(right_err)) => {
            r := accErr("[trExpression] error translating right expression\n" + errStr(right_err), []);
          }
          case (Err(left_err), Err(right_err)) => {
            r := accErr("[trExpression] error translating left and right expressions\n" + errStr(left_err) + "\n" + errStr(right_err), []);
          }
        }
      }
      case UnOp(unop, expr, format1) => {
        var lucid_op : op;
        match unop {
          case Cardinality => {
            print("[trExpression] unsupported op: cardinality\n");
            r := baseErr("[trExpression] unsupported op: cardinality");
            return r;
          }
          case BitwiseNot => {
            print("[trExpression] unsupported op: bitwise not\n");
            r := baseErr("[trExpression] unsupported op: bitwise not");
            return r;
          }
          case Not => {lucid_op := op.Not;}
        }
        var exp := trExpression(expr);
        match exp {
          case Res(exp) => {
            r := Res(EOp(lucid_op, [exp]));
          }
          case Err(e) => {
            r := accErr("[trExpression] error translating expression\n" + errStr(e), []);
          }
        }
      }
      case DatatypeValue(dtt, typeArgs, variant, isCo, contents) => {
        // special case: a "recircCmd" that will later be translated 
        // into either a return (for a function) or a generate statement
        // (for a handler).
        if pathLeafIs(dtt.path, recircCmdTyName) {
          if (|typeArgs| > 0) {
            print("[trExpression] unsupported feature: datatype value with type args\n");
            r := baseErr("[trExpression] unsupported feature: datatype value with type args");
          } 
          else {            
            if (|contents| == 2) {
              var doit := trExpression(contents[0].1);
              var e := trExpression(contents[1].1);
              match (doit, e) {
                case (Res(doit), Res(e)) => {
                  r := Res(EDafnyGenerateCmd(doit, e));
                }
                case (Err(doit), Res(_)) => {
                  r := accErr("[trExpression] error translating doit\n" + errStr(doit), []);
                }
                case (Res(_), Err(e)) => {
                  r := accErr("[trExpression] error translating e\n" + errStr(e), []);
                }
                case (Err(doit), Err(e)) => {
                  r := accErr("[trExpression] error translating doit and e\n" + errStr(doit) + "\n" + errStr(e), []);
                }            
              }
            }
            else {
              print("[trExpression] unsupported feature: recircCmd with wrong number of args\n");
              r := baseErr("[trExpression] unsupported feature: recircCmd with wrong number of args");
            }
          }
        }
        // record construction: RecordName(a, b) -> { f1 = a; f2 = b }
        else if hasTag(dtt.attributes, lucidRecordTag) {
          var fields : seq<(id, exp)> := [];
          var errs := [];
          for i := 0 to |contents| {
            var fe := trExpression(contents[i].1);
            match fe {
              case Res(e) => fields := fields + [(contents[i].0.dafny_name, e)];
              case Err(er) => errs := errs + [er];
            }
          }
          if |errs| > 0 { r := accErr("[trExpression] record construction", errs); }
          else { r := Res(ERecord(fields)); }
        }
        // the only other datatype that is supported is the "event" datatype.
        else {
          if pathLeafIs(dtt.path, eventTyName) {
            if (|typeArgs| > 0) {
              print("[trExpression] unsupported feature: datatype value with type args\n");
              r := baseErr("[trExpression] unsupported feature: datatype value with type args");
            } 
            else {
              var args := [];
              var errs := [];
              for i := 0 to |contents| {
                // drop the `ingress_port` field (temporary: modeled as builtin).
                if !isIngressPortName(contents[i].0.dafny_name) {
                  var tmp := trExpression(contents[i].1);
                  match tmp {
                    case Res(arg) => {
                      args := args + [arg];
                    }
                    case Err(e) => {
                      errs := errs + [e];
                    }
                  }
                }
              }
              if |errs| > 0 {
                r := accErr("[trExpression]", errs);
              } else {
                r := Res(EEvent(variant.dafny_name, args));
              }
            }
          }
          else {
            print("[trExpression] unsupported feature: datatype value\n");
            r := baseErr("[trExpression] unsupported feature: datatype value");
          }
        }
        // var datatypeidents := datatypeType.path;
        // var datatypestrs := seq(|datatypeidents|, i requires 0 <= i < |datatypeidents| => datatypeidents[i].id.dafny_name);
        // var datatypestr := PPrint.comma_sep(datatypestrs, x => x);
        // print ("[trExpression] datatype: " + datatypestr + "\n");
        // r := baseErr("[trExpression] unsupported feature: datatype value");
      }
      case This() => {
        print "[trExpression] COMPILER ERROR: 'this' expressions cannot be translated directly \n";
        r := baseErr("[trExpression] COMPILER ERROR: 'this' expressions cannot be translated directly");
      }
      // record field projection: record.field -> record#field
      case Select(rexpr, field, _, SelectContextDatatype, _) => {
        var re := trExpression(rexpr);
        match re {
          case Res(r_e) => r := Res(EProject(r_e, field.dafny_name));
          case Err(e) => r := accErr("[trExpression] record projection", [e]);
        }
      }
      // ref to a constant or global
      case Select(This(), field, _, _, _) => {
        r := Res(EVar(field.dafny_name));
      }
      // ref to a top-level / module const (e.g. `_module.__default.numRows`)
      case Select(Companion(_, _), field, _, _, _) => {
        r := Res(EVar(field.dafny_name));
      }
      case SelectFn(This(), field, _, _, _, _) => {
        r := Res(EVar(field.dafny_name));
      }
      // special case: array helper
      case SelectFn(Companion(idents, _), field, _, _, _, _) => {
        if |idents| == 2 && idents[0] == arrayIdent {
          var var_str := idents[0].id.dafny_name + "." + field.dafny_name;
          r := Res(EVar(var_str));
        } else {
          print("[trExpression] calling a function that belongs to a module besides builtin ArrayMemops\n");
          r := baseErr("[trExpression] calling a function that belongs to a module besides builtin ArrayMemops");
        }
      }
      // vector literal by enumeration: [a, b, c] -> [a; b; c]
      case SeqValue(elements, _) => {
        var es := trExpressions(elements);
        match es {
          case Res(es) => r := Res(EVecLit(es));
          case Err(e) => r := accErr("[trExpression] seq literal", [e]);
        }
      }
      case Convert(value, from, typ) => {
        // Some converts are no-ops, we are not clear when else they may 
        // occur (nothing in test programs)
        if from == typ {
          r := trExpression(value);
        } else {
          print("[trExpression] unexpected construct: non-identity Convert (from "
            + PPrint.typeToString(from) + " to " + PPrint.typeToString(typ) + ")\n");
          r := baseErr("[trExpression] unexpected construct: non-identity Convert");
        }
      }
      // vector indexing: s[i] -> s[i] (seqs only; arrays use method calls)
      case Index(e, _, indices) => {
        if |indices| == 1 {
          var ve := trExpression(e);
          var ie := trExpression(indices[0]);
          match (ve, ie) {
            case (Res(ve), Res(ie)) => r := Res(EIndex(ve, ie));
            case (Err(er), _) => r := accErr("[trExpression] index target", [er]);
            case (_, Err(er)) => r := accErr("[trExpression] index", [er]);
          }
        } else {
          print("[trExpression] unsupported feature: multi-dimensional index\n");
          r := baseErr("[trExpression] unsupported feature: multi-dimensional index");
        }
      }
      // case Ite(cond, thn, els) => {

      // }
      case _ => {
        print ("[trExpression]: unsupported expression type\n");
        print ("-------------------------\n");
        print (PPrint.expressionToString(expr));
        print ("\n-------------------------\n");
        r:= baseErr("[trExpression] unimplemented / supported expression type");
      }
    }
  }

  method trExpressions(exprs : seq<Expression>) returns (r: res<seq<exp>>) {
    var inner_rs := [];
    var errs := [];
    for i:=0 to |exprs| {
      var tmp := trExpression(exprs[i]);
      match tmp {
        case Res(e) => {inner_rs := inner_rs + [e];}
        case Err(e) => {
          errs := errs + [e];
        }
      }
    }
    if |errs| > 0 {
      r := accErr("[trExpressions]", errs);
    } else {
      r := Res(inner_rs);
    }
  }

  // A type backed by mutable pipeline state (an array, or a vector of arrays)
  // vs. a compile-time value (scalar, or a vector of values).
  predicate isGlobalTy(t: ty)
  {
    match t {
      case TGlobal(_, _) => true
      case TVec(elem, _) => isGlobalTy(elem)
      case _ => false
    }
  }
  // The right decl for a field initialization: a `global` for pipeline objects,
  // a `const` for values (including value vectors).
  function mkFieldDecl(id: id, t: ty, ctor: exp): decl
  {
    if isGlobalTy(t) then DGlobal(id, t, ctor) else DConst(id, t, ctor)
  }

  // translate a statement inside of a constructor
  type VarMap = map<string, (Type, Expression)>
  datatype StmtCtx = StmtCtx(vars : VarMap, stmts : seq<stmt>, decls : seq<decl>)
  method trConstrStatement(ctx : StmtCtx, stmt : Statement, fieldTypes : map<string, Type>)
    returns (outctx : StmtCtx)
    {
      var vars := ctx.vars;
      var stmts := ctx.stmts;
      var decls : seq<decl> := ctx.decls;
      match stmt {
        case DeclareVar(name, typ, Some(val)) => {
          vars := vars + map[name.dafny_name := (typ, val)];
        }
        case Call(_, CallName(nm, _, _, _, _), _, cargs, _) => {
          // New-object array init lowers to `_nw.Create(_nw, size, init)`. The
          // `New` bound to `_nw` carries no size; the size lives here. Rewrite
          // the temp's stored value into the old-style
          // `ArrayMemops.Create(size, init)` form so the Assign below emits the
          // global exactly as the legacy syntax did.
          if nm.dafny_name == "Create" && |cargs| >= 1 {
            match cargs[0] {
              case Ident(nwk) =>
                if nwk.dafny_name in vars && isArrayVarType(vars[nwk.dafny_name].0) {
                  var arrTy := vars[nwk.dafny_name].0;
                  // The call handler expects a 2-ident Companion (it reads
                  // idents[0]); mirror the shape the old `ArrayMemops.Create`
                  // form produces.
                  var createCall := Expression.Call(
                    Companion([arrayIdent, arrayIdent], []),
                    CallName(Name("Create"), None, None, false, CallSignature([], [])),
                    [], cargs[1..]);
                  vars := vars[nwk.dafny_name := (arrTy, createCall)];
                }
              case _ => {}
            }
          }
        }
        case Assign(Select(this_exp, real_var_name, _), rhs) => {
          var init : Option<(Type, Expression)> := None;
          match rhs {
            case Ident(rhs_name) =>
              if rhs_name.dafny_name in vars {
                init := Some(vars[rhs_name.dafny_name]);
              }
            case _ =>
              if real_var_name.dafny_name in fieldTypes {
                init := Some((fieldTypes[real_var_name.dafny_name], rhs));
              }
          }
          if init.Some? && isSwitchType(init.value.0) {
            // switch field: no Lucid global (the switch is implicit hardware).
          }
          else if init.Some? {
            var (typ, expr) := init.value;
            var ty := trType(typ);
            var ctor := trExpression(expr);
            match (ty, ctor) {
              case (Res(ty), Res(ctor)) => {
                decls := decls + [mkFieldDecl(normFieldName(real_var_name.dafny_name), ty, ctor)];
              }
              case (Err(ty_err), Res(_)) => {
                decls := decls + [DComment("[trConstrStatement] error translating type\n" + errStr(ty_err))];
              }
              case (Res(_), Err(ctor_err)) => {
                decls := decls + [DComment("[trConstrStatement] error translating ctor\n" + errStr(ctor_err))];
              }
              case (Err(ty_err), Err(ctor_err)) => {
                decls := decls + [DComment("[trConstrStatement] error translating type and ctor\n" + errStr(ty_err) + "\n" + errStr(ctor_err))];
              }
            }
          }
        }
        case _ => {}
      }
      outctx := StmtCtx(vars, stmts, decls);
    }

    method trConstr(m:Method, fieldTypes : map<string, Type>) returns (decls : seq<decl>)
    {
      print("      trConstr: " + m.name.dafny_name + "\n");
      var ctx := StmtCtx(map[], [], []);
      // transformations that we might want to do in a separate pass before translation
      // (casts are handled in trExpression, not stripped, so widths survive)
      var body := exprInStatementsVisitor(m.body, elimArgSelects);

      var i := 0;
      while i < |body| {
        // Fixed-length global vectors: a `seq(n, ...)` field init, or the
        // append-loop convention assigning a tmp vector to a field.
        var vecR := tryCtorVecField(body, i, fieldTypes);
        match vecR {
          case Some((Res(ds), consumed)) => { ctx := ctx.(decls := ctx.decls + ds); i := i + consumed; }
          case Some((Err(e), consumed)) => { ctx := ctx.(decls := ctx.decls + [DComment("[trConstr] vector field: " + errStr(e))]); i := i + consumed; }
          case None => {
            ctx := trConstrStatement(ctx, body[i], fieldTypes);
            i := i + 1;
          }
        }
      }
      return ctx.decls;
    }

    // Recognize a fixed-length vector field initialization in a constructor:
    //   (A) `field := seq(n, i => e);`                       (1 statement)
    //   (B) the append-loop convention ending in `field := tmp;`
    // and emit the corresponding `DGlobal(field, TVec, EComp/...)`.
    method tryCtorVecField(body: seq<Statement>, i: nat, fieldTypes: map<string, Type>)
      returns (r: Option<(res<seq<decl>>, nat)>)
      requires i <= |body|
    {
      r := None;
      if i >= |body| { return; }
      // (A) seq-comprehension field init
      match body[i] {
        case Assign(Select(_, fld, _), SeqConstruct(_, elem)) => {
          var key := fld.dafny_name;
          if key !in fieldTypes { return; }
          var tyR := trType(fieldTypes[key]);
          match tyR {
            case Res(TVec(el, len)) => {
              var compR := trSeqComprehension(elem, len);
              match compR {
                case Res(comp) => r := Some((Res([mkFieldDecl(normFieldName(key), TVec(el, len), comp)]), 1));
                case Err(e) => r := Some((Err(e), 1));
              }
            }
            case _ => r := Some((baseErr("[tryCtorVecField] seq field type is not a fixed-length seq"), 1));
          }
          return;
        }
        case _ => {}
      }
      // (C) enumerated vector of global/module instances: `field := [p0, p1, ...]`
      // where each pX is a `new VarArray.Create(...)` or `new Module()` local.
      match body[i] {
        case Assign(Select(_, fld, _), SeqValue(elems, _)) => {
          var key := fld.dafny_name;
          if key !in fieldTypes { return; }
          var tyR := trType(fieldTypes[key]);
          match tyR {
            // only vectors whose elements are pipeline objects (globals) go here;
            // value-vector enumerations fall through to the generic exp path.
            case Res(TVec(TGlobal(gt, ga), len)) => {
              var elemsR := resolveGlobalVecElems(elems, body[..i]);
              match elemsR {
                case Res(es) => r := Some((Res([mkFieldDecl(normFieldName(key), TVec(TGlobal(gt, ga), len), EVecLit(es))]), 1));
                case Err(e) => r := Some((Err(e), 1));
              }
              return;
            }
            case _ => return;
          }
        }
        case _ => {}
      }
      // (B) append-loop assigned to a field
      if i + 1 >= |body| { return; }
      var tmpName;
      match body[i] { case DeclareVar(n, _, None) => tmpName := n.dafny_name; case _ => return; }
      match body[i+1] {
        case Assign(Ident(t), SeqValue(elems, _)) =>
          if t.dafny_name != tmpName || |elems| != 0 { return; }
        case _ => return;
      }
      var fi := i + 2;
      if fi < |body| && !body[fi].Foreach? {
        match body[fi] { case DeclareVar(_, _, Some(_)) => fi := fi + 1; case _ => {} }
      }
      if fi >= |body| { return; }
      var loopVar; var loopBody;
      match body[fi] {
        case Foreach(bn, _, _, b) => { loopVar := bn.dafny_name; loopBody := b; }
        case _ => return;
      }
      if fi + 1 >= |body| { return; }
      var fieldKey;
      match body[fi+1] {
        case Assign(Select(_, fld, _), Ident(src)) =>
          if src.dafny_name != tmpName { return; } else { fieldKey := fld.dafny_name; }
        case _ => return;
      }
      if fieldKey !in fieldTypes { return; }
      var consumed := (fi + 2) - i;
      var tyR := trType(fieldTypes[fieldKey]);
      var itemR := trAppendItem(loopBody, tmpName, loopVar);
      match (tyR, itemR) {
        case (Err(e), _) => r := Some((Err(e), consumed));
        case (_, Err(e)) => r := Some((Err(e), consumed));
        case (Res(TVec(el, len)), Res(item)) =>
          r := Some((Res([mkFieldDecl(normFieldName(fieldKey), TVec(el, len), EComp(canonLoopVar(item, loopVar), loopVar, len))]), consumed));
        case (Res(_), Res(_)) =>
          r := Some((baseErr("[tryCtorVecField] field type is not a fixed-length seq"), consumed));
      }
    }

    // Translate a call on the switch field into a Lucid generate statement.
    //   generateRecircEvent(ev)          -> generate (ev);
    //   generateOutput({p}, ev)          -> generate_port (p, ev);
    //   generateOutput({flood(p)}, ev)   -> generate_ports (flood(p), ev);
    method trSwitchGenerate(mname: string, args: seq<Expression>) returns (r: res<seq<stmt>>)
    {
      if mname == "generateRecircEvent" && |args| == 1 {
        var ev := trExpression(args[0]);
        match ev {
          case Res(e) => r := Res([SGenerate(e)]);
          case Err(err) => r := accErr("[trSwitchGenerate] generateRecircEvent", [err]);
        }
      }
      else if mname == "generateOutput" && |args| == 2 {
        var evr := trExpression(args[1]);
        match evr {
          case Err(err) => { r := accErr("[trSwitchGenerate] generateOutput event", [err]); }
          case Res(ev) => {
            match args[0] {
              case SetValue(elements) => {
                if |elements| != 1 {
                  r := baseErr("[trSwitchGenerate] unsupported: multi-port generateOutput; use a single port or flood(p)");
                } else {
                  // detect the flood(p) sentinel to choose generate_ports vs generate_port
                  var floodArg : Option<Expression> := None;
                  match elements[0] {
                    case Call(_, CallName(fname, _, _, _, _), _, fargs) =>
                      if fname.dafny_name == "flood" && |fargs| == 1 { floodArg := Some(fargs[0]); }
                    case _ =>
                  }
                  if floodArg.Some? {
                    var fa := trExpression(floodArg.value);
                    match fa {
                      case Res(fae) => r := Res([SGeneratePorts(ECall("flood", [fae]), ev)]);
                      case Err(err) => r := accErr("[trSwitchGenerate] flood arg", [err]);
                    }
                  } else {
                    var pe := trExpression(elements[0]);
                    match pe {
                      case Res(p) => r := Res([SGeneratePort(p, ev)]);
                      case Err(err) => r := accErr("[trSwitchGenerate] output port", [err]);
                    }
                  }
                }
              }
              case _ => r := baseErr("[trSwitchGenerate] generateOutput ports must be a set literal");
            }
          }
        }
      }
      else {
        r := baseErr("[trSwitchGenerate] unsupported switch method: " + mname);
      }
    }

    method printTrStmtErr(stmtStr : string, err : err) {
      print("[trStatement] error translating " + stmtStr + "\n");
      print(errStr(err));
      print ("\n-------------------\n");
    }

    method trStatement(s:Statement, vecLengths: map<string, nat>) returns (ls : res<seq<stmt>>) {
        var dbg_str := 
        "[trStatement] entering stmt--------\n" 
        + PPrint.statementToString(s) 
        + "\n--------------------------------\n";
        match s {
            case DeclareVar(name, typ, None) => {
                var ty := trType(typ);
                match ty {
                    case Res(ty) => {
                        return Res([DafnyDeclare(name.dafny_name, ty)]);
                    }
                    case Err(e) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating type\n" + errStr(e), []);
                    }
                }
            }
            case DeclareVar(name, typ, Some(InitializationValue(_))) => {
              var ty := trType(typ);
              match ty {
                case Res(ty) => {
                  return Res([DafnyDeclare(name.dafny_name, ty)]);
                }
                case Err(e) => {
                  printTrStmtErr(dbg_str, e);
                  return accErr("[trStatement] error translating type\n" + errStr(e), []);
                }
              }
            }
            case DeclareVar(name, typ, Some(This())) => {
              // if you assign "this" to an intermediate variable, it's a no-op.
              return Res([]);
            }
            case DeclareVar(name, typ, Some(val)) => {
                var ty := trType(typ);
                var exp := trExpression(val);
                match (ty, exp) {
                    case (Res(ty), Res(exp)) => {
                        return Res([SLocal(name.dafny_name, ty, exp)]);
                    }
                    case (Err(e), Res(_)) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating type\n" + errStr(e), []);
                    }
                    case (Res(_), Err(e)) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating expression\n" + errStr(e), []);
                    }
                    case (Err(ty_err), Err(e)) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating type and expression\n" + errStr(ty_err) + "\n" + errStr(e), []);
                    }
                }
            }
            case Assign(Ident(lhs), rhs) => {
                var exp := trExpression(rhs);
                match exp {
                    case Res(exp) => {
                        return Res([SAssign(lhs.dafny_name, exp)]);
                    }
                    case Err(e) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating expression\n" + errStr(e), []);
                    }
                }
            }
            case Assign(Select(select_expr, field, _), rhs) => {
                var sstr := PPrint.statementToString(s);
                print("[trStatement] WARNING: field assignment. >>> " + sstr + "<<<.\n");
                var exp := trExpression(rhs);
                /* field assignments mean that we are updating an array variable. 
                   This is done internally in lucid, by the Array helpers. 
                   So we delete these nodes. */
                match exp {
                    case Res(exp) => {
                        return Res([SNoop]);
                        // return Res([SAssign(field.dafny_name, exp)]);
                    }
                    case Err(e) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating expression\n" + errStr(e), []);
                    }
                }
            }
            case Assign(Index(_, _), _) => {
                var e := Base("[trStatement] unsupported feature: array assignment");
                printTrStmtErr(dbg_str, e);
                return baseErr("[trStatement] unsupported feature: array assignment");
            }
            case If(cond, thn, els) => {
                var cond_exp := trExpression(cond);
                var thn_stmts := trStatements(thn, vecLengths);
                var els_stmts := trStatements(els, vecLengths);
                match (cond_exp, thn_stmts, els_stmts) {
                    case (Res(cond_exp), Res(thn_stmts), Res(els_stmts)) => {
                        return Res([SIf(cond_exp, thn_stmts, els_stmts)]);
                    }
                    case (Err(e), Res(_), Res(_)) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating condition\n" + errStr(e), []);
                    }
                    case (Res(_), Err(e), Res(_)) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating then branch\n" + errStr(e), []);
                    }
                    case (Res(_), Res(_), Err(e)) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating else branch\n" + errStr(e), []);
                    }
                    case (Err(e1), Err(e2), Res(_)) => {
                        printTrStmtErr(dbg_str, e1);
                        return accErr("[trStatement] error translating condition and then branch\n" + errStr(e1) + "\n" + errStr(e2), []);
                    }
                    case (Err(e1), Res(_), Err(e2)) => {
                        printTrStmtErr(dbg_str, e1);
                        return accErr("[trStatement] error translating condition and else branch\n" + errStr(e1) + "\n" + errStr(e2), []);
                    }
                    case (Res(_), Err(e1), Err(e2)) => {
                        printTrStmtErr(dbg_str, e1);
                        return accErr("[trStatement] error translating then and else branches\n" + errStr(e1) + "\n" + errStr(e2), []);
                    }
                    case (Err(e1), Err(e2), Err(e3)) => {
                        printTrStmtErr(dbg_str, e1);
                        return accErr("[trStatement] error translating condition, then, and else branches\n" + errStr(e1) + "\n" + errStr(e2) + "\n" + errStr(e3), []);
                    }
                }                
            }
            case Labeled(_, stmts) => {
                var inner_rs := trStatements(stmts, vecLengths);
                return inner_rs;
            }
            case While(_, _) => {
                printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: while loop"));
                return baseErr("[trStatement] unsupported feature: while loop");
            }
            case Foreach(bn, _, _, fbody) => {
                // A side-effecting `for i := 0 to n` loop over a vector -> a Lucid
                // `for (i < N)` loop (append-loops that build a vector are caught
                // earlier in trStatements). The bound N is the iterated vector's
                // length; the loop var is canonicalized to the header name.
                var loopVar := bn.dafny_name;
                var boundOpt := findLoopBound(fbody, vecLengths);
                match boundOpt {
                    case None => {
                        printTrStmtErr(dbg_str, Base("[trStatement] could not determine for-loop bound (no indexed vector field)"));
                        return baseErr("[trStatement] could not determine for-loop bound");
                    }
                    case Some(bound) => {
                        var bodyR := trStatements(fbody, vecLengths);
                        match bodyR {
                            case Res(bodyStmts) => {
                                var canonBody := canonLoopVarStmts(bodyStmts, loopVar);
                                return Res([SFor(loopVar, bound, canonBody)]);
                            }
                            case Err(e) => {
                                printTrStmtErr(dbg_str, e);
                                return accErr("[trStatement] for-loop body\n" + errStr(e), []);
                            }
                        }
                    }
                }
            }
            case Call(on, callName, typeArgs, args, outs) => {
                // Calls on the switch field become generate statements, not
                // Lucid calls; handle before the generic call translation.
                match callName {
                  case CallName(sname, Some(sonty), _, _, _) =>
                    if isSwitchType(sonty) {
                      var g := trSwitchGenerate(sname.dafny_name, args);
                      match g {
                        case Res(gs) => return Res(gs);
                        case Err(e) => {
                          printTrStmtErr(dbg_str, e);
                          return accErr("[trStatement] switch generate\n" + errStr(e), []);
                        }
                      }
                    }
                  case _ =>
                }
                var args_rs := trExpressions(args);
                var args_out := [];
                match args_rs {
                    case Res(args_rs) => {
                        args_out := args_rs;
                    }
                    case Err(e) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating call args\n" + errStr(e), []);
                    }
                }
                var outs_out := match outs {
                    case None => []
                    case Some(outs) => Seq.Map(((x : VarName) => x.dafny_name), outs)
                };
                var callName_out : string;
                var callOnType : Option<Type> := None;
                match callName {
                    case CallName(name, onType, _, _, _) => {
                        callName_out := name.dafny_name;
                        callOnType := onType;
                    }
                    case _ => {
                        printTrStmtErr(dbg_str, Base("[trStatement] unsupported callName kind"));
                        return baseErr("[trStatement] unsupported callName kind.");
                    }
                }
                // add the prefix if there is one.
                match on {
                  case Companion(idents, _) => {
                    match |idents| {
                      case 0 => {}
                      case 2 => {
                        if (idents[0] == arrayIdent) {
                          callName_out := idents[0].id.dafny_name + "." + callName_out;
                        } else {
                          printTrStmtErr(dbg_str, Base("[trStatement] error: 2 idents, but first one is not 'ArrayMemops'"));
                          return baseErr("[trStatement] unsupported feature: call with on that is not 'this' or 'ArrayMemops'");
                        }
                      }
                      case _ => {
                        printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: call with on that is not 'this' or 'ArrayMemops'"));
                        return baseErr("[trStatement] unsupported feature: call with on that is not 'this' or 'ArrayMemops'");
                      }
                    }
                  }
                  case This => {}
                  case _ => {
                    // Instance-method call: on a VarArray receiver (new-object
                    // syntax) it becomes an ArrayMemops builtin; on a user-module
                    // instance it becomes `Module.method(recv, args)`. Either way
                    // the receiver (a field, local, or vector element `panes[i]`)
                    // is hoisted to the first argument.
                    var qualifier := "";
                    if callOnType.Some? && isArrayVarType(callOnType.value) {
                      qualifier := arrayIdent.id.dafny_name;
                    } else {
                      var modName := if callOnType.Some? then moduleTypeName(callOnType.value) else None;
                      match modName {
                        case Some(m) => qualifier := m;
                        case None => {
                          printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: call with on that is not 'this' or 'ArrayMemops'"));
                          return baseErr("[trStatement] unsupported feature: call with on that is not 'this' or 'ArrayMemops'");
                        }
                      }
                    }
                    var recvR := trArrayReceiver(on);
                    match recvR {
                      case Res(recv_exp) => {
                        callName_out := qualifier + "." + callName_out;
                        args_out := [recv_exp] + args_out;
                      }
                      case Err(e) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] instance-method receiver\n" + errStr(e), []);
                      }
                    }
                  }
                }


                return Res([DafnyCall(callName_out, args_out, outs_out)]);
            }
            case Return(expr) => {
                var exp := trExpression(expr);
                match exp {
                    case Res(exp) => {
                        return Res([SRet(Some(exp))]);
                    }
                    case Err(e) => {
                        printTrStmtErr(dbg_str, e);
                        return accErr("[trStatement] error translating expression\n" + errStr(e), []);
                    }
                }
            }
            case EarlyReturn() => {
                return Res([SRet(None)]);
            }
            case Break(_) => {
                printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: break"));
                return baseErr("[trStatement] unsupported feature: break");
            }
            case TailRecursive(_) => {
                printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: tail recursive"));
                return baseErr("[trStatement] unsupported feature: tail recursive");
            }
            case JumpTailCallStart() => {
                printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: jump tail call start"));
                return baseErr("[trStatement] unsupported feature: jump tail call start");
            }
            case Halt() => {
                printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: halt"));
                return baseErr("[trStatement] unsupported feature: halt");
            }
            case Print(exp) => {
                var strs := Analysis.getStringLiterals(exp);
                if |strs| == 1 {
                    return Res([SComment("print: " + strs[0])]);
                } else {
                    printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: print with 0 or multiple strings"));
                    return baseErr("[trStatement] unsupported feature: print with 0 or multiple strings");
                }
            }
            case ConstructorNewSeparator(_) => {
                printTrStmtErr(dbg_str, Base("[trStatement] unsupported feature: constructor new separator"));
                return baseErr("[trStatement] unsupported feature: constructor new separator");
            }
        }
    }

    // ss[i] is the hoisted loop-bound temp (`var _hi := n;`) of the for-loop at
    // ss[i+1] (i.e. the loop's IntRange upper bound is exactly this variable).
    predicate isForLoopBoundTemp(ss: seq<Statement>, i: nat)
    {
      i + 1 < |ss| &&
      (match ss[i]
         case DeclareVar(n, _, Some(_)) =>
           (match ss[i+1]
              case Foreach(_, _, IntRange(_, _, hi, _), _) =>
                (match hi case Ident(h) => h.dafny_name == n.dafny_name case _ => false)
              case _ => false)
         case _ => false)
    }

    // The bound of a `for` loop over a vector = the iterated vector's length.
    // Found by scanning the loop body for a method call on a vector-field
    // element (`field[i].op(..)`) and looking up the field's length.
    function boundFromStmt(s: Statement, vecLengths: map<string, nat>): Option<nat>
      decreases s
    {
      match s {
        case Call(Index(Select(_, fld, _, _, _), _, _), _, _, _, _) =>
          if normFieldName(fld.dafny_name) in vecLengths
          then Some(vecLengths[normFieldName(fld.dafny_name)]) else None
        case If(_, thn, els) =>
          var t := findLoopBound(thn, vecLengths);
          if t.Some? then t else findLoopBound(els, vecLengths)
        case _ => None
      }
    }
    function findLoopBound(stmts: seq<Statement>, vecLengths: map<string, nat>): Option<nat>
      decreases stmts
    {
      if |stmts| == 0 then None
      else
        var here := boundFromStmt(stmts[0], vecLengths);
        if here.Some? then here else findLoopBound(stmts[1..], vecLengths)
    }

    method trStatements(ss: seq<Statement>, vecLengths: map<string, nat>) returns (ls : res<seq<stmt>>) {
        var inner_rs := [];
        var errs := [];
        var i := 0;
        while i < |ss| {
            // Drop the hoisted loop-bound temp (`var _hi := n;`) that Dafny emits
            // right before a `for` loop -- the bound comes from the vector type.
            if isForLoopBoundTemp(ss, i) { i := i + 1; }
            else {
                // Try the fixed-length-vector patterns first: they span several
                // consecutive statements (append-loop ending in `final := tmp`, or
                // a split typed-declare + `seq(n, ...)` comprehension assign).
                var loop := tryAppendLoop(ss, i);
                if loop.None? { loop := trySeqConstruct(ss, i); }
                match loop {
                    case Some((Res(s), consumed)) => { inner_rs := inner_rs + [s]; i := i + consumed; }
                    case Some((Err(e), consumed)) => { errs := errs + [e]; i := i + consumed; }
                    case None => {
                        var tmp := trStatement(ss[i], vecLengths);
                        match tmp {
                            case Res(s) => {inner_rs := inner_rs + s;}
                            case Err(e) => {errs := errs + [e];}
                        }
                        i := i + 1;
                    }
                }
            }
        }
        if |errs| > 0 {
            ls := accErr("[trStatements]", errs);
        } else {
            ls := Res(inner_rs);
        }
    }

    // Recognize the 3-step append-loop convention for constructing a
    // fixed-length value vector inside a method body, at statement index `i`:
    //   var tmp : seq<T> := [];               // (a) DeclareVar + (b) Assign []
    //   [ var _hi := n; ]                      // (c) optional hoisted bound
    //   for j := 0 to n { ...; tmp := tmp + [item]; }   // (d) Foreach
    //   var final : seqN<T> := tmp;            // (e) DeclareVar + (f) Assign tmp
    // Returns the translated `SLocal(final, TVec, EComp(item, j, N))` and the
    // number of consumed statements, or None if the window doesn't match.
    method tryAppendLoop(ss: seq<Statement>, i: nat) returns (r: Option<(res<stmt>, nat)>)
      requires i <= |ss|
    {
      r := None;
      // (a) empty tmp declare + (b) init to []
      if i + 1 >= |ss| { return; }
      var tmpName;
      match ss[i] { case DeclareVar(n, _, None) => tmpName := n.dafny_name; case _ => return; }
      match ss[i+1] {
        case Assign(Ident(t), SeqValue(elems, _)) =>
          if t.dafny_name != tmpName || |elems| != 0 { return; }
        case _ => return;
      }
      // (c) optional hoisted loop-bound temp, then (d) the Foreach
      var fi := i + 2;
      if fi < |ss| && !ss[fi].Foreach? {
        match ss[fi] { case DeclareVar(_, _, Some(_)) => fi := fi + 1; case _ => {} }
      }
      if fi >= |ss| { return; }
      var loopVar; var body;
      match ss[fi] {
        case Foreach(bn, _, _, b) => { loopVar := bn.dafny_name; body := b; }
        case _ => return;
      }
      // (e) final declare (carries the seqN type) + (f) final := tmp
      if fi + 2 >= |ss| { return; }
      var finalName; var finalTy;
      match ss[fi+1] {
        case DeclareVar(n, ty, None) => { finalName := n.dafny_name; finalTy := ty; }
        case _ => return;
      }
      match ss[fi+2] {
        case Assign(Ident(fn), Ident(src)) =>
          if fn.dafny_name != finalName || src.dafny_name != tmpName { return; }
        case _ => return;
      }
      // Matched the shape: translate the final type and the lifted item.
      var consumed := (fi + 3) - i;
      var tyR := trType(finalTy);
      var itemR := trAppendItem(body, tmpName, loopVar);
      match (tyR, itemR) {
        case (Err(e), _) => r := Some((Err(e), consumed));
        case (_, Err(e)) => r := Some((Err(e), consumed));
        case (Res(TVec(elem, len)), Res(item)) =>
          r := Some((Res(SLocal(finalName, TVec(elem, len), EComp(canonLoopVar(item, loopVar), loopVar, len))), consumed));
        case (Res(_), Res(_)) =>
          r := Some((baseErr("[tryAppendLoop] final type is not a fixed-length seq"), consumed));
      }
    }

    // Lift the per-iteration item expression out of an append-loop body. The
    // body must end in `tmp := tmp + [ref]`; everything before it constructs
    // `ref`. We follow single-variable renames back to either a value-returning
    // array call (lifted to an expression) or a plain expression.
    method trAppendItem(body: seq<Statement>, tmpName: string, loopVar: string) returns (r: res<exp>)
    {
      if |body| == 0 { return baseErr("[trAppendItem] empty loop body"); }
      var refName;
      match body[|body|-1] {
        case Assign(Ident(t), BinOp(binop, Ident(t2), SeqValue(elems, _), _)) => {
          if !binop.op.Concat? || t.dafny_name != tmpName || t2.dafny_name != tmpName || |elems| != 1 {
            return baseErr("[trAppendItem] loop body does not end in tmp := tmp + [item]");
          }
          match elems[0] { case Ident(v) => refName := v.dafny_name; case _ => { r := trExpression(elems[0]); return; } }
        }
        case _ => return baseErr("[trAppendItem] loop body does not end in an append");
      }
      r := resolveAppendItem(body[..|body|-1], refName);
    }

    // Resolve `name` to the expression that defines it, within the given
    // straight-line statements: a value-returning Call becomes an expression,
    // a rename `name := other` recurses, any other single assignment yields its
    // RHS expression.
    method resolveAppendItem(stmts: seq<Statement>, name: string) returns (r: res<exp>)
      decreases |stmts|
    {
      var idx := |stmts|;
      while idx > 0
        decreases idx
      {
        idx := idx - 1;
        var s := stmts[idx];
        // a value-returning call whose out is `name`
        match s {
          // new-object array construction: `var name := new VarArray();
          // VarArray.Create(name, size, init)` -> ArrayMemops.Create(size, init)
          case Call(_, CallName(cnm, _, _, _, _), _, cargs, _) =>
            if cnm.dafny_name == "Create" && |cargs| >= 1 && cargs[0].Ident? && cargs[0].name.dafny_name == name {
              var a := trExpressions(cargs[1..]);
              match a {
                case Res(a) => { r := Res(ECall(arrayIdent.id.dafny_name + ".Create", a)); return; }
                case Err(e) => { r := Err(e); return; }
              }
            }
          case _ => {}
        }
        match s {
          case Call(on, cn, _, args, Some(outs)) =>
            if |outs| == 1 && outs[0].dafny_name == name {
              r := trCallAsExp(on, cn, args);
              return;
            }
          case Assign(Ident(lhs), rhs) =>
            if lhs.dafny_name == name {
              match rhs {
                case Ident(w) => { r := resolveAppendItem(stmts[..idx], w.dafny_name); return; }
                case _ => { r := trExpression(rhs); return; }
              }
            }
          case DeclareVar(n, _, Some(rhs)) =>
            if n.dafny_name == name {
              match rhs {
                case Ident(w) => { r := resolveAppendItem(stmts[..idx], w.dafny_name); return; }
                case _ => { r := trExpression(rhs); return; }
              }
            }
          case _ => {}
        }
      }
      r := baseErr("[resolveAppendItem] could not resolve item variable " + name);
    }

    // Resolve each element of an enumerated global/module vector to its ctor
    // expression: an array `new VarArray.Create(size,init)` -> `ArrayMemops.Create`
    // (via resolveAppendItem), a module `new Module()` -> `Module.create(args)`.
    method resolveGlobalVecElems(elems: seq<Expression>, stmts: seq<Statement>) returns (r: res<seq<exp>>)
    {
      var out := [];
      for k := 0 to |elems| {
        match elems[k] {
          case Ident(v) => {
            var cr := resolveGlobalInstance(stmts, v.dafny_name);
            match cr {
              case Res(c) => out := out + [c];
              case Err(e) => return accErr("[resolveGlobalVecElems]", [e]);
            }
          }
          case _ => return baseErr("[resolveGlobalVecElems] non-variable element in vector enumeration");
        }
      }
      r := Res(out);
    }

    // Resolve a local bound to `new Module()` / `new VarArray.Create(...)` to its
    // Lucid constructor expression, following single-variable renames.
    method resolveGlobalInstance(stmts: seq<Statement>, name: string) returns (r: res<exp>)
      decreases |stmts|
    {
      var idx := |stmts|;
      while idx > 0
        decreases idx
      {
        idx := idx - 1;
        match stmts[idx] {
          // `new Module()` object: `_nw : Module := new Module()`
          case DeclareVar(n, _, Some(New(path, _, nargs))) =>
            if n.dafny_name == name && |path| > 0 {
              var a := trExpressions(nargs);
              match a {
                case Res(a) => { r := Res(ECall(pathLeafName(path) + ".create", a)); return; }
                case Err(e) => { r := Err(e); return; }
              }
            }
          // rename `name := other`
          case Assign(Ident(lhs), Ident(rhs)) =>
            if lhs.dafny_name == name { r := resolveGlobalInstance(stmts[..idx], rhs.dafny_name); return; }
          case _ => {}
        }
      }
      // fall back to the array-instance resolver (`new VarArray.Create`).
      r := resolveAppendItem(stmts, name);
    }

    // Translate a value-returning instance/array method call into an
    // expression (the comprehension form of an append-loop item). Mirrors the
    // array-receiver handling in trStatement's Call case.
    method trCallAsExp(on: Expression, callName: CallName, args: seq<Expression>) returns (r: res<exp>)
    {
      var name; var onTy;
      match callName {
        case CallName(nm, oty, _, _, _) => { name := nm.dafny_name; onTy := oty; }
        case _ => return baseErr("[trCallAsExp] unsupported call name");
      }
      var argsR := trExpressions(args);
      match argsR {
        case Err(e) => return accErr("[trCallAsExp] args", [e]);
        case Res(argExps) =>
          if onTy.Some? && isArrayVarType(onTy.value) {
            var recvR := trArrayReceiver(on);
            match recvR {
              case Res(recv) => r := Res(ECall(arrayIdent.id.dafny_name + "." + name, [recv] + argExps));
              case Err(e) => r := Err(e);
            }
          } else {
            r := baseErr("[trCallAsExp] unsupported call receiver in append loop");
          }
      }
    }

    // The receiver of an array instance-method call, as an expression:
    // a field (`arr`), a local (`arr`), or a vector element (`pool[i]`).
    method trArrayReceiver(on: Expression) returns (r: res<exp>)
    {
      match on {
        case Select(_, f, _, _, _) => r := Res(EVar(normFieldName(f.dafny_name)));
        case Ident(v) => r := Res(EVar(normFieldName(v.dafny_name)));
        case Index(vec, _, idxs) =>
          if |idxs| == 1 {
            var ve := trExpression(vec);
            var ie := trExpression(idxs[0]);
            match (ve, ie) {
              case (Res(ve), Res(ie)) => r := Res(EIndex(ve, ie));
              case (Err(e), _) => r := Err(e);
              case (_, Err(e)) => r := Err(e);
            }
          } else {
            r := baseErr("[trArrayReceiver] multi-dimensional array receiver");
          }
        case _ => r := baseErr("[trArrayReceiver] unsupported array receiver");
      }
    }

    // The return expression of a lambda body (`i => e` lowers to `[return e]`).
    function findReturnExpr(body: seq<Statement>): Option<Expression>
    {
      if |body| == 0 then None
      else match body[0]
        case Return(e) => Some(e)
        case _ => findReturnExpr(body[1..])
    }

    // Rewrite a translated `seq(n, i => e)` body for the Lucid comprehension:
    // (1) apply BetaRedex renames (captured vars like `_3_xs` -> `xs`);
    // (2) the loop var is a Lucid `size`, so any use of it as an integer value
    //     needs `size_to_int(i)`, except when it indexes a vector (`v[i]`).
    function transformCompBody(e: exp, ivar: string, rn: map<string, string>): exp
    {
      match e {
        case EVar(id) =>
          if id == ivar then ECall("size_to_int", [EVar(ivar)])
          else if id in rn then EVar(rn[id]) else e
        case EVal(_) => e
        case ECall(id, args) => ECall(id, transformCompArgs(args, ivar, rn))
        case EHash(w, args) => EHash(w, transformCompArgs(args, ivar, rn))
        case EProject(rec, f) => EProject(transformCompBody(rec, ivar, rn), f)
        case ERecord(fields) =>
          ERecord(seq(|fields|, k requires 0 <= k < |fields| => (fields[k].0, transformCompBody(fields[k].1, ivar, rn))))
        case EIndex(vec, idx) =>
          var nvec := transformCompBody(vec, ivar, rn);
          // keep a bare loop-var index as a size (no size_to_int)
          var nidx := match idx
            case EVar(id) => if id == ivar then EVar(ivar) else (if id in rn then EVar(rn[id]) else idx)
            case _ => transformCompBody(idx, ivar, rn);
          EIndex(nvec, nidx)
        case EComp(b, iv, bd) => EComp(transformCompBody(b, ivar, rn), iv, bd)
        case EVecLit(elems) => EVecLit(transformCompArgs(elems, ivar, rn))
        case EEvent(id, args) => EEvent(id, transformCompArgs(args, ivar, rn))
        case EOp(op, args) => EOp(op, transformCompArgs(args, ivar, rn))
        case EDafnyGenerateCmd(d, x) => EDafnyGenerateCmd(transformCompBody(d, ivar, rn), transformCompBody(x, ivar, rn))
      }
    }
    function transformCompArgs(args: seq<exp>, ivar: string, rn: map<string, string>): seq<exp>
    {
      seq(|args|, k requires 0 <= k < |args| => transformCompBody(args[k], ivar, rn))
    }

    // Rewrite an append-loop item so that uses of the loop variable (Dafny's
    // uniquified `_<n>_<boundName>`) become `boundName`, matching the EComp
    // binder. (Append-loop items only use the loop var as an index, so no
    // size_to_int is needed, unlike `seq(n, ...)` comprehensions.)
    function canonLoopVar(e: exp, boundName: string): exp
    {
      match e {
        case EVar(id) => if isUniqLoopVar(id, boundName) then EVar(boundName) else e
        case EVal(_) => e
        case ECall(id, args) => ECall(id, canonLoopVarArgs(args, boundName))
        case EHash(w, args) => EHash(w, canonLoopVarArgs(args, boundName))
        case EProject(rec, f) => EProject(canonLoopVar(rec, boundName), f)
        case ERecord(fields) =>
          ERecord(seq(|fields|, k requires 0 <= k < |fields| => (fields[k].0, canonLoopVar(fields[k].1, boundName))))
        case EIndex(vec, idx) => EIndex(canonLoopVar(vec, boundName), canonLoopVar(idx, boundName))
        case EComp(b, iv, bd) => EComp(canonLoopVar(b, boundName), iv, bd)
        case EVecLit(elems) => EVecLit(canonLoopVarArgs(elems, boundName))
        case EEvent(id, args) => EEvent(id, canonLoopVarArgs(args, boundName))
        case EOp(op, args) => EOp(op, canonLoopVarArgs(args, boundName))
        case EDafnyGenerateCmd(d, x) => EDafnyGenerateCmd(canonLoopVar(d, boundName), canonLoopVar(x, boundName))
      }
    }
    function canonLoopVarArgs(args: seq<exp>, boundName: string): seq<exp>
    {
      seq(|args|, k requires 0 <= k < |args| => canonLoopVar(args[k], boundName))
    }

    // Statement-level loop-var canonicalization for `for`-loop bodies: rewrite
    // the uniquified loop var (`_<n>_i`) in every embedded expression to the
    // `for` header name, matching the SFor binder.
    function canonLoopVarStmt(s: stmt, boundName: string): stmt
    {
      match s {
        case SNoop => s
        case SIf(e, st, sf) => SIf(canonLoopVar(e, boundName), canonLoopVarStmts(st, boundName), canonLoopVarStmts(sf, boundName))
        case SLocal(id, ty, e) => SLocal(id, ty, canonLoopVar(e, boundName))
        case SAssign(id, e) => SAssign(id, canonLoopVar(e, boundName))
        case SUnit(e) => SUnit(canonLoopVar(e, boundName))
        case SRet(None) => s
        case SRet(Some(e)) => SRet(Some(canonLoopVar(e, boundName)))
        case SGenerate(e) => SGenerate(canonLoopVar(e, boundName))
        case SGeneratePort(p, e) => SGeneratePort(canonLoopVar(p, boundName), canonLoopVar(e, boundName))
        case SGeneratePorts(p, e) => SGeneratePorts(canonLoopVar(p, boundName), canonLoopVar(e, boundName))
        case SPrint(_) => s
        case SComment(_) => s
        case DafnyCall(id, args, outs) => DafnyCall(id, canonLoopVarArgs(args, boundName), outs)
        case DafnyDeclare(_, _) => s
        case SFor(iv, b, body) => SFor(iv, b, canonLoopVarStmts(body, boundName))
      }
    }
    function canonLoopVarStmts(ss: seq<stmt>, boundName: string): seq<stmt>
    {
      seq(|ss|, k requires 0 <= k < |ss| => canonLoopVarStmt(ss[k], boundName))
    }

    // Translate a `seq(n, i => e)` comprehension element into `[e' for i < len]`,
    // where len comes from the declared fixed-length type (not `n`).
    method trSeqComprehension(elem: Expression, len: nat) returns (r: res<exp>)
    {
      var renames : map<string, string> := map[];
      var lam := elem;
      match elem {
        case BetaRedex(values, _, inner) => {
          for k := 0 to |values| {
            match values[k].1 {
              case Ident(v) => renames := renames[values[k].0.name.dafny_name := v.dafny_name];
              case _ => {}
            }
          }
          lam := inner;
        }
        case _ => {}
      }
      match lam {
        case Lambda(params, _, body) => {
          if |params| != 1 {
            return baseErr("[trSeqComprehension] expected a single lambda parameter");
          }
          var ivar := params[0].name.dafny_name;
          var be := findReturnExpr(body);
          match be {
            case None => r := baseErr("[trSeqComprehension] lambda body has no return");
            case Some(be) => {
              var teR := trExpression(be);
              match teR {
                case Res(te) => r := Res(EComp(transformCompBody(te, ivar, renames), ivar, len));
                case Err(e) => r := Err(e);
              }
            }
          }
        }
        case _ => r := baseErr("[trSeqComprehension] expected a lambda element");
      }
    }

    // Recognize `var x : seqN<T> := seq(n, i => e);`, which Dafny splits into a
    // typed declare and an assign. Returns the collapsed SLocal and consumed
    // count, or None.
    method trySeqConstruct(ss: seq<Statement>, i: nat) returns (r: Option<(res<stmt>, nat)>)
      requires i <= |ss|
    {
      r := None;
      if i + 1 >= |ss| { return; }
      var xName; var xTy;
      match ss[i] { case DeclareVar(n, ty, None) => { xName := n.dafny_name; xTy := ty; } case _ => return; }
      var elem;
      match ss[i+1] {
        case Assign(Ident(t), SeqConstruct(_, e)) =>
          if t.dafny_name != xName { return; } else { elem := e; }
        case _ => return;
      }
      var tyR := trType(xTy);
      match tyR {
        case Res(TVec(el, len)) => {
          var compR := trSeqComprehension(elem, len);
          match compR {
            case Res(comp) => r := Some((Res(SLocal(xName, TVec(el, len), comp)), 2));
            case Err(e) => r := Some((Err(e), 2));
          }
        }
        case Res(_) => r := Some((baseErr("[trySeqConstruct] target is not a fixed-length seq"), 2));
        case Err(e) => r := Some((Err(e), 2));
      }
    }

    method trMethod(m:Method, vecLengths: map<string, nat>) returns (decls : res<seq<decl>>) {
      if (m.name in SkipMethods) {
        print("      trMethod skipping " + m.name.dafny_name + "\n");
        return Res([]);
      }
      else if anySwitchType(m.outTypes) {
        // auto-generated getter for the (dropped) switch field
        print("      trMethod skipping switch getter " + m.name.dafny_name + "\n");
        return Res([]);
      }
      else {
        print("      trMethod translating " + m.name.dafny_name + "\n");
        if (|m.typeParams| > 0) {
          print("[trMethod] unsupported feature: method with type params");
          return baseErr("[trMethod] unsupported feature: method " + m.name.dafny_name + " has type params");
        } else {
          var params_res := trFormals(m.params);
          var params := [];
          match params_res {
            case Res(v) => {params := v;}
            case Err(e) => {
              print ("[trMethod] error translating params\n");
              return accErr("[trMethod] error translating params\n" + errStr(e), []);
            }
          }
          var rtys_res := trTypes(m.outTypes);
          var rtys := [];
          match rtys_res {
            case Res(v) => {rtys := v;}
            case Err(e) => {
              print ("[trMethod] error translating return types\n");
              return accErr("[trMethod] error translating return types\n" + errStr(e), []);
            }
          }
          var outvars := match m.outVars {
              case None => []
              case Some(outVars) => Seq.Map(((x : VarName) => x.dafny_name), outVars)
          };
          var mbody := exprInStatementsVisitor(m.body, elimArgSelects);
          var body_res := trStatements(mbody, vecLengths);
          var body := [];
          match body_res {
            case Res(v) => { body := v; }
            case Err(e) => {
              print ("[trMethod] error translating body\n");
              return accErr("[trMethod] error translating body\n" + errStr(e), []);
            }
          }
          var dout := DDafnyMethod(m.name.dafny_name, rtys, params, body, outvars);
          decls := Res([dout]);

          // if (m.name.dafny_name == "Q") || (m.name.dafny_name == "A") {
          //   print ("-----[trMethod] debug: Q method-----\n");
          //   var methodStr := PPrint.methodToString(m);
          //   print(methodStr);
          //   print ("------------------------------------\n");
          //   var doutStr := LAST.declStr(dout);
          //   print(doutStr);
          //   print ("------------------------------------\n");
          // }

        }
      }
    }


    method trMethodOuter(m:Method, fieldTypes : map<string, Type>, vecLengths : map<string, nat>) returns (decls : seq<decl>)
    {
      // the constructor gets translated to declarations
      // instead of statements
      if (m.name == ctorMethodName) {
        decls := trConstr(m, fieldTypes);
      } else {
        var lucidDecl := trMethod(m, vecLengths);
        match lucidDecl {
          case Res(ds) => decls := ds;
          case Err(e) => {
            print ("[trMethodOrConstr] error translating method\n");
            decls := [DComment("error translating method\n" + errStr(e))];
          }
        }
      }
    }

    // A `{:lucid_module}` class -> a Lucid module: the fields become the module
    // type `t`, the constructor a `constr`, and each method a `fun` taking a
    // `t self` first arg (field refs are rewritten to `self#field` in a later pass).
    method trModuleClass(c:Class) returns (decls : seq<decl>)
    {
      print("    trClass: module " + c.name.dafny_name + "\n");
      // field types + translated field types, keyed by normalized name.
      var fieldTypes : map<string, Type> := map[];
      var fieldTyMap : map<string, ty> := map[];
      var fieldNames : set<string> := {};
      var vecLengths : map<string, nat> := map[];
      for i := 0 to |c.fields| {
        var rawName := c.fields[i].formal.name.dafny_name;
        fieldTypes := fieldTypes[rawName := c.fields[i].formal.typ];
        fieldNames := fieldNames + {rawName, normFieldName(rawName)};
        var fty := trType(c.fields[i].formal.typ);
        match fty {
          case Res(t) => {
            fieldTyMap := fieldTyMap[normFieldName(rawName) := t];
            match t { case TVec(_, len) => vecLengths := vecLengths[normFieldName(rawName) := len]; case _ => {} }
          }
          case Err(e) => print("[trModuleClass] field type error: " + errStr(e) + "\n");
        }
      }
      // Translate the constructor first: its init order defines the module's
      // global (pipeline) order, which the `type t` field order must match, so
      // that field accesses in the methods respect Lucid's global ordering.
      var ctorDecl : seq<decl> := [];
      var initOrder : seq<id> := [];
      for i := 0 to |c.body| {
        match c.body[i] {
          case Method(m) =>
            if m.outVarsAreUninitFieldsToAssign {
              var cdecls := trConstr(m, fieldTypes);
              var inits : seq<(id, exp)> := [];
              for j := 0 to |cdecls| {
                match cdecls[j] {
                  case DGlobal(fid, _, e) => { inits := inits + [(fid, e)]; initOrder := initOrder + [fid]; }
                  case DConst(fid, _, e) => { inits := inits + [(fid, e)]; initOrder := initOrder + [fid]; }
                  case _ => {}
                }
              }
              var psr := trFormals(m.params);
              var ps := match psr { case Res(p) => p case Err(_) => [] };
              ctorDecl := [DConstr("t", "create", ps, inits)];
            }
        }
      }
      // `type t` fields: constructor-init order first, then any leftovers.
      var tFields : seq<param> := [];
      var emitted : set<id> := {};
      for i := 0 to |initOrder| {
        if initOrder[i] in fieldTyMap && initOrder[i] !in emitted {
          tFields := tFields + [(initOrder[i], fieldTyMap[initOrder[i]])];
          emitted := emitted + {initOrder[i]};
        }
      }
      for i := 0 to |c.fields| {
        var nm := normFieldName(c.fields[i].formal.name.dafny_name);
        if nm in fieldTyMap && nm !in emitted {
          tFields := tFields + [(nm, fieldTyMap[nm])];
          emitted := emitted + {nm};
        }
      }
      var members : seq<decl> := [DRecord("t", tFields)] + ctorDecl;
      // remaining members (non-constructor methods).
      for i := 0 to |c.body| {
        match c.body[i] {
          case Method(m) => {
            if m.outVarsAreUninitFieldsToAssign {
              // constructor already emitted above
            } else if normFieldName(m.name.dafny_name) in fieldNames {
              // auto-generated const-field getter -> not a module method; skip
            } else {
              var mdecls := trMethod(m, vecLengths);
              match mdecls {
                case Res(ds) => members := members + ds;
                case Err(e) => members := members + [DComment("[trModuleClass] method error " + errStr(e))];
              }
            }
          }
        }
      }
      decls := [DModule(c.name.dafny_name, members)];
    }

    method trClass(c:Class) returns (decls : seq<decl>)
    {
      // Data-structure module class -> a Lucid module.
      if hasTag(c.attributes, lucidModuleTag) {
        decls := trModuleClass(c);
        return;
      }
      // The root module's implicit __default class holds the program's top-level
      // declarations. Emit its value-returning members (consts / functions), e.g.
      // a top-level `const numRows`; skip procedures like a test-harness method.
      // (Library modules have their own __default — those stay externs.)
      else if c.name.dafny_name == "__default" && c.enclosingModule.id.dafny_name == "_module" {
        decls := [];
        for i := 0 to |c.body| {
          match c.body[i] {
            case Method(m) => {
              if |m.outTypes| == 1 {
                var mdecls := trMethod(m, map[]);
                match mdecls {
                  case Res(ds) => decls := decls + ds;
                  case Err(e) => decls := decls + [DComment("[trClass __default] " + errStr(e))];
                }
              }
            }
          }
        }
        return;
      }
      // Program class: tag, or (transitional) the legacy name "Program".
      else if !hasTag(c.attributes, lucidProgramTag) && c.name != progClassName {
        print("    trClass: skipping " + c.name.dafny_name + "\n");
        return [];
      }
      else {
        print("    trClass: translating " + c.name.dafny_name + "\n");
        var fieldIds : seq<string> := [];
        var fieldTypes : map<string, Type> := map[];
        var vecLengths : map<string, nat> := map[];
        for i := 0 to |c.fields| {
          // The switch field has no Lucid representation; drop it entirely.
          if !isSwitchType(c.fields[i].formal.typ) {
            // Field order (used to order emitted globals) must match the global
            // names, which are normalized; the fieldTypes key must stay raw to
            // match the constructor's assignment target.
            fieldIds := fieldIds + [normFieldName(c.fields[i].formal.name.dafny_name)];
            fieldTypes := fieldTypes[c.fields[i].formal.name.dafny_name := c.fields[i].formal.typ];
            var fty := trType(c.fields[i].formal.typ);
            match fty {
              case Res(TVec(_, len)) => vecLengths := vecLengths[normFieldName(c.fields[i].formal.name.dafny_name) := len];
              case _ => {}
            }
          }
        }
        var fieldOrderDecl := DDafnyFieldOrder(fieldIds);
        print("\n");
        decls := [fieldOrderDecl];
        for i:=0 to |c.body| {
          match c.body[i] {
            case Method(m) => {
              var new_decls := trMethodOuter(m, fieldTypes, vecLengths);
              decls := decls + new_decls;
            }
          }
        }
      }
    }

    method trDatatypeCtor(c:DatatypeCtor) returns (decl : decl)
    {
      print ("    trDatatypeCtor: translating " + c.name.dafny_name + "\n");
      var params := [];
      var errs := [];
      for i := 0 to |c.args| {
        match c.args[i] {
          case DatatypeDtor(formal, _) => {
            // drop the `ingress_port` event field (temporary: modeled as builtin).
            if isIngressPortName(formal.name.dafny_name) {
            } else {
              var param := trFormal(formal);
              match param {
                case Res(param) => params := params + [param];
                case Err(err) => errs := errs + [err];
              }
            }
          }
        }
      }
      if |errs| > 0 {
        print ("    trDatatypeCtor: error in datatype args\n");
        var ctorStr := PPrint.datatypeCtorToString(c);
        print ("    trDatatypeCtor: " + ctorStr + "\n");
        decl := DComment(ctorStr + " " + errStrs(errs));
      } else {
        decl := DEvent(c.name.dafny_name, params);
      }
    }

    // A `{:lucid_record}` datatype -> a Lucid record type. The datatype must have
    // exactly one constructor whose fields become the record fields.
    method trRecord(d:Datatype) returns (decls : seq<decl>)
    {
      if |d.ctors| != 1 {
        return [DComment("[trRecord] " + d.name.dafny_name +
                         " must have exactly one variant to be a lucid record")];
      }
      var ctor := d.ctors[0];
      var fields : seq<param> := [];
      var errs := [];
      for i := 0 to |ctor.args| {
        match ctor.args[i] {
          case DatatypeDtor(formal, _) => {
            var ty := trType(formal.typ);
            match ty {
              case Res(t) => fields := fields + [(formal.name.dafny_name, t)];
              case Err(e) => errs := errs + [e];
            }
          }
        }
      }
      if |errs| > 0 {
        decls := [DComment("[trRecord] error in fields of " + d.name.dafny_name + " " + errStrs(errs))];
      } else {
        decls := [DRecord(d.name.dafny_name, fields)];
      }
    }

    method trDatatype(d:Datatype) returns (decls : seq<decl>)
    {
      // Record type -> a Lucid record type.
      if hasTag(d.attributes, lucidRecordTag) {
        print("  trDatatype: record " + d.name.dafny_name + "\n");
        decls := trRecord(d);
        return;
      }
      // Event datatype: tag, or (transitional) the legacy name "Event".
      else if !hasTag(d.attributes, lucidEventTag) && d.name != eventDatatypeName {
        print("  trDatatype: skipping " + d.name.dafny_name + "\n");
        return [];
      }
      else {
        print("  trDatatype: translating " + d.name.dafny_name + "\n");
        decls := [];
        for i := 0 to |d.ctors| {
          var decl := trDatatypeCtor(d.ctors[i]);
          decls := decls + [decl];
        }
      }
    }


    method trModule(m : Module) returns (decls : seq<decl>)
    {
      // print(PPrint.moduleToString(m));
      // print("\n");
      if m.name in SkipModules {
        print ("trModule: skipping " + m.name.dafny_name + "\n");
        return [];
      } else {
        print ("trModule: translating  " + m.name.dafny_name + "\n");
        decls := [];
        match m.body {
          case None => return [];
          case Some(body) => {
            for i := 0 to |body| {
              match (body[i]) {
                case Class(c) => {
                  var newdecls := trClass(c);
                  decls := decls + newdecls;
                }
                case Datatype(d) => {
                  var newdecls := trDatatype(d);
                  decls := decls + newdecls;
                }
                case _ => {}
              }
            }
          }
        }
      }
    }

    method trModules(ms : seq<Module>) returns (decls : seq<decl>)
    {
      decls := [];
      for i := 0 to |ms| {
        var newdecls := trModule(ms[i]);
        var istr := PPrint.natToString(i);
        var num_decls := |newdecls|;
        var numdeclsstr := PPrint.natToString(num_decls);
        decls := decls + newdecls;
      }
    }
  
}