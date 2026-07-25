include "AST.dfy"

include "PPrintAst.dfy"
include "MapVisitor.dfy"

module LAST {
  import opened Std.Wrappers
  import opened Std.Collections

  import opened DAST
  import opened MapVisitor
  import PPrint


  // minimal lucid AST for translation from Dafny
  type id = string

  // datatype fun_kind = 
  //   | FFun
  //   | FMemop
  //   | FHandler
  //   | FEvent

  datatype gtyargs = 
    | Sizes(seq<nat>)
    // | Tys(seq<ty>)
    | NoTyArgs

  datatype ty = 
    | TInt(nat) // bit width
    | TBool
    | TEvent
    | TGlobal(id:id, args:gtyargs) // Arrays
    | TRecord(id:id) // user-defined record types (value types)
    | TVec(elem:ty, len:nat) // fixed-length vectors: elem[len]
    | TVoid
    | TDafnyGenerateCmd // handlers generate events by returning this type
    // | TFun(argtys:seq<ty>, retty : Option<ty>)
    // | TArrow(argtys:seq<ty>, retty:seq<ty>) // not really needed for printing.

  type param = (id, ty)

  datatype val = 
    | VInt(string, int)
    | VBool(bool)
    | VInvalid(string)
  datatype op = 
    | Add | Sub
    | BitOr | BitAnd | BitXor
    | BitShiftL | BitShiftR
    | Eq | Neq | Lt | Lte | Gt | Gte
    | Or | And | Neg
    | Not
    | DafnyDiv | DafnyMod
    | IntCast(sz:nat) // cast to int of width n
    // Division is not supported, but 
    // we can support a certain subset 
    // of division operations by using
    // right shifts. (the divisor has 
    // to be a const and a power of 2)

    // Mod is also not supported in general, 
    // but we can eliminate modulo operations 
    // when they fit the following pattern:
    // given a : size(a) == n and b : size(b) == n
    // (a <+|-> b) \mod (2^n) \equiv (a <+|-> b)
    
  datatype exp = 
    | EVar(id:id)
    | EVal(val)
    | ECall(id:id, args:seq<exp>) // foo(x, y, z)
    | EHash(width:nat, args:seq<exp>) // hash<width>(seed, v...)
    | EProject(record:exp, field:id) // record#field
    | ERecord(fields:seq<(id, exp)>) // { f1 = e1; f2 = e2 }
    | EIndex(vec:exp, idx:exp) // vec[idx]
    | EComp(body:exp, ivar:id, bound:nat) // [body for ivar < bound]
    | EVecLit(elems:seq<exp>) // [e1; e2; ...]
    | EEvent(id:id, args:seq<exp>)
    | EOp(op:op, args:seq<exp>)
    | EDafnyGenerateCmd(doit:exp, e:exp) // expression returned by a handler

  datatype stmt = 
    | SNoop
    | SIf(exp:exp, strue:seq<stmt>, sfalse:seq<stmt>)
    | SLocal(id:id, ty:ty, exp:exp)
    | SAssign(id:id, exp:exp)
    | SUnit(exp)
    | SRet(Option<exp>)
    | SGenerate(exp) // generate event (recirculation)
    | SGeneratePort(port:exp, e:exp) // generate an event to a single output port
    | SGeneratePorts(ports:exp, e:exp) // generate an event to a port group / set
    | SFor(ivar:id, bound:nat, body:seq<stmt>) // for (ivar < bound) { body }
    | SPrint(string)
    | SComment(string)
    | DafnyCall(id:id, args:seq<exp>, outs:seq<id>)
    | DafnyDeclare(id:id, ty:ty) // declare a local with no initializer
  
  datatype decl = 
    | DEvent(id:id, params:seq<param>)
    | DGlobal(id:id, ty:ty, ctor:exp)
    | DComment(string)
    | DRaw(string)
    | DDafnyMethod(id:id, rtys:seq<ty>, params:seq<param>, body:seq<stmt>, outvars:seq<id>)
    // everything below starts out as a "DafnyMethod"
    // and gets converted in a second pass
    | DConst(id:id, ty:ty, init:exp) // const: a scalar or a value vector
    | DSymbolic(id:id, ty:ty)
    | DHandler(id:id, params:seq<param>, body:seq<stmt>)
    | DFunction(id:id, rty:ty, params:seq<param>, body:seq<stmt>)
    | DMemop(id:id, rty:ty, params:seq<param>, body:seq<stmt>)
    | DDafnyFieldOrder(ids:seq<id>)
    | DRecord(id:id, fields:seq<param>) // type id = { ty f; ... }
    | DModule(id:id, members:seq<decl>) // module id { ... }
    | DConstr(tyname:id, cname:id, params:seq<param>, inits:seq<(id, exp)>) // constr t name(params) = { f = e; ... };

  /* printers */
  function tyStr(ty : ty) : string {
    match ty {
        case TInt(i) => "int<"+PPrint.natToString(i)+">"
        case TBool => "bool"
        case TEvent => "event"
        case TGlobal(id, Sizes(sizes)) => 
            id + "<" + PPrint.comma_sep(sizes, PPrint.natToString) + ">"
        case TGlobal(id, NoTyArgs) => id
        case TRecord(id) => id
        case TVec(elem, len) => tyStr(elem) + "[" + PPrint.natToString(len) + "]"
        case TVoid => "void"
        case TDafnyGenerateCmd => "dafny_generate_cmd"
    }
  }
  function tyStrs(tys : seq<ty>) : string {
    var strs := seq(|tys|, i requires 0 <= i < |tys| => tyStr(tys[i]));
    PPrint.comma_sep(strs, x => x)
  }

  // ty id
  function paramStr(p : param) : string {
    match p {
      case (id, ty) => tyStr(ty) + " " + id
    }
  }
  function paramStrs(ps : seq<param>) : string {
    var strs := seq(|ps|, i requires 0 <= i < |ps| => paramStr(ps[i]));
    PPrint.comma_sep(strs, x => x)
  }

  function valStr(v : val) : string {
    match v {
      case VInt(s, _) => s
      case VBool(b) => if b then "true" else "false"
      case VInvalid(str) => "(INVALID_VALUE = "+ str + ")"
    }
  }

  function opStr(op : op) : string {
    match op {
      case Add => "+"
      case Sub => "-"
      case BitOr => "|"
      case BitAnd => "&"
      case BitXor => "^"
      case BitShiftL => "<<"
      case BitShiftR => ">>"
      case Eq => "=="
      case Neq => "!="
      case Lt => "<"
      case Lte => "<="
      case Gt => ">"
      case Gte => ">="
      case Or => "||"
      case And => "&&"
      case Neg => "-"
      case Not => "!"
      case DafnyDiv => "/"
      case DafnyMod => "%"
      case IntCast(n) => "(int<" + PPrint.natToString(n) + ">)"
    }
  }

  function expStr(e : exp) : string {
    match e {
      case EVar(id) => id
      case EVal(v) => valStr(v)
      case ECall(id, args) => id + "(" + expStrs(args) + ")"
      case EHash(width, args) => "hash<" + PPrint.natToString(width) + ">(" + expStrs(args) + ")"
      case EProject(record, field) => expStr(record) + "#" + field
      case ERecord(fields) => "{" + PPrint.sep("; ", fields, (fe : (id, exp)) => fe.0 + " = " + expStr(fe.1)) + "}"
      case EIndex(vec, idx) => expStr(vec) + "[" + expStr(idx) + "]"
      case EComp(body, ivar, bound) => "[" + expStr(body) + " for " + ivar + " < " + PPrint.natToString(bound) + "]"
      case EVecLit(elems) => "[" + PPrint.sep("; ", elems, (e : exp) => expStr(e)) + "]"
      case EEvent(id, args) => id + "(" + expStrs(args) + ")"
      case EOp(op, args) => 
        match |args| {
          case 1 => "(" + opStr(op) + expStr(args[0]) + ")"
          case 2 => 
            var arg0 := expStr(args[0]);
            var arg1 := expStr(args[1]);
            "(" + arg0 + " " + opStr(op) + " " + arg1 + ")"
          case _ => "/* ERROR: unsupported op arity */"      
        }
      // case EDafnyThis() => "/*This()*/"
      case EDafnyGenerateCmd(doit, e) => 
       "generate_cmd( " + expStr(doit) + ", " + expStr(e) + ")"
    }
  }

  function expStrs(es : seq<exp>) : string {
    var strs := seq(|es|, i requires 0 <= i < |es| => expStr(es[i]));
    PPrint.comma_sep(strs, x => x)
  }

  function stmtStr(s : stmt) : string {
    match s {
      case SNoop => "skip;"
      case SIf(e, strue, sfalse) => 
        "if (" + expStr(e) + ") {\n" 
        + PPrint.indent(stmtStrs(strue)) + "\n"
        + "} " + 
        if |sfalse| > 0 then "else {\n"
          + PPrint.indent(stmtStrs(sfalse)) + "\n"
          + "}"
        else ""
      case SLocal(id, ty, e) => 
        tyStr(ty) + " " + id + " = " + expStr(e) + ";"
      case SAssign(id, e) => id + " = " + expStr(e) + ";"
      case SUnit(e) => expStr(e) + ";"
      case SRet(None) => "return;"
      case SRet(Some(e)) => "return " + expStr(e) + ";"
      case SComment(s) => "/* " + s + " */"
      case DafnyCall(id, args, outs) => 
        "/* DafnyCall */ " + PPrint.comma_sep(outs, x => x) + " = " + id + "(" + expStrs(args) + ");"
      case SPrint(s) => "print(" + s + ");"
      case DafnyDeclare(id, ty) => "/*" + " UNINITIALIZED"  + "*/" +  tyStr(ty) + " " + id + ";"
      case SGenerate(e) => "generate (" + expStr(e) + ");"
      case SGeneratePort(port, e) => "generate_port (" + expStr(port) + ", " + expStr(e) + ");"
      case SGeneratePorts(ports, e) => "generate_ports (" + expStr(ports) + ", " + expStr(e) + ");"
      case SFor(ivar, bound, body) =>
        "for (" + ivar + " < " + PPrint.natToString(bound) + ") {\n"
        + PPrint.indent(stmtStrs(body)) + "\n"
        + "}"
    }
  }

  function stmtStrs(ss : seq<stmt>) : string {
    var strs := seq(|ss|, i requires 0 <= i < |ss| => stmtStr(ss[i]));
    PPrint.newline_sep(strs, x => x)
  }

  function declStr(d : decl) : string {
    match d {
      case DEvent(id, params) => 
        "event " + id + "(" + paramStrs(params) + ");"
      case DGlobal(id, ty, ctor) =>
        "global " + tyStr(ty) + " " + id + " = " + expStr(ctor) + ";"
      case DConst(id, ty, init) =>
        "const " + tyStr(ty) + " " + id + " = " + expStr(init) + ";"
      case DSymbolic(id, ty) =>
        "symbolic " + tyStr(ty) + " " + id + ";"
      case DHandler(id, params, body) =>
        "handle " + id + "(" + paramStrs(params) + ") {\n" 
        + PPrint.indent(stmtStrs(body)) + "\n"
        + "}"
      case DFunction(id, rty, params, body) =>
        "fun " + tyStr(rty) + " " + id + "(" + paramStrs(params) + ") {\n"
        + PPrint.indent(stmtStrs(body)) + "\n"
        + "}"
      case DMemop(id, rty, params, body) =>
        "memop " + id + "(" + paramStrs(params) + ") {\n"
        + PPrint.indent(stmtStrs(body)) + "\n"
        + "}"
      case DComment(s) => "/* " + s + " */"
      case DRaw(s) => s
      case DDafnyMethod(id, rtys, params, body, outvars) => 
        "dafny_method (" + tyStrs(rtys) + ") " + id + "(" + paramStrs(params) + ")" + " returns (" + PPrint.comma_sep(outvars, x => x) + ") {\n"
         + PPrint.indent(stmtStrs(body)) + "\n"
        + "}"
      case DDafnyFieldOrder(_) => ""
      case DRecord(id, fields) =>
        var fieldStrs := seq(|fields|, i requires 0 <= i < |fields| => paramStr(fields[i]) + ";");
        "type " + id + " = {\n" + PPrint.indent(PPrint.newline_sep(fieldStrs, x => x)) + "\n}"
      case DModule(id, members) =>
        "module " + id + " {\n" + PPrint.indent(declStrs(members)) + "\n}"
      case DConstr(rty, name, params, inits) =>
        var initStrs := seq(|inits|, i requires 0 <= i < |inits| => inits[i].0 + " = " + expStr(inits[i].1) + ";");
        "constr " + rty + " " + name + "(" + paramStrs(params) + ") = {\n"
        + PPrint.indent(PPrint.newline_sep(initStrs, x => x)) + "\n};"
    }
  }

  function declStrs(ds : seq<decl>) : string {
    var strs := seq(|ds|, i requires 0 <= i < |ds| => declStr(ds[i]));
    PPrint.newline_sep(strs, x => x)
  }
}
