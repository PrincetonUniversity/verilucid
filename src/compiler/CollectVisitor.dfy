include "AST.dfy"

  
module CollectVisitor {
  import opened DAST
  import opened Std.Wrappers
  import opened DAST.Format
  import opened Std.Collections


  datatype Node = 
    | NExp(Expression)
    | NStmt(Statement)
    | NType(Type)
    | NLiteral(Literal)


  method resolvedTypeCollector<t>(typ : ResolvedType, f : Node -> seq<t>) returns (res : seq<t>)
  {
    res := [];
    var more := [];
    for i:=0 to |typ.typeArgs| {
        more := typeCollector(typ.typeArgs[i], f);
        res := res + more;
    }
    for i:=0 to |typ.extendedTypes| {
        more := typeCollector(typ.extendedTypes[i], f);
        res := res + more;
    }
    match typ.kind {
        case Class() => { }
        case Datatype(_, _) => { }
        case Trait(_) => { }
        case Newtype(baseType, range, erase) => {
            more := typeCollector(baseType, f);
            res := res + more;
        }
    }
  }

  method typeCollector<t>(typ : Type, f : Node -> seq<t>) returns (res : seq<t>)
  {
    var more := [];
    res := f(NType(typ));
    match typ {
        case UserDefined(resolved) => { 
            more := resolvedTypeCollector(resolved, f);
            res := res + more;
        }
        case Tuple(types) => {
            for i:=0 to |types| {
                more := typeCollector(types[i], f);
                res := res + more;
            }
        }
        case Array(element, dims) => {
            more := typeCollector(element, f);
            res := res + more;
        }
        case Seq(element) => {
            more := typeCollector(element, f);
            res := res + more;
        }
        case Set(element) => {
            more := typeCollector(element, f);
            res := res + more;
        }
        case Multiset(element) => {
            more := typeCollector(element, f);
            res := res + more;
        }
        case Map(key, value) => {
            more := typeCollector(key, f);
            res := res + more;
            more := typeCollector(value, f);
            res := res + more;
        }
        case SetBuilder(element) => {
            more := typeCollector(element, f);
            res := res + more;
        }
        case MapBuilder(key, value) => {
            more := typeCollector(key, f);
            res := res + more;
            more := typeCollector(value, f);
            res := res + more;
        }
        case Arrow(args, result) => {
            for i:=0 to |args| {
                more := typeCollector(args[i], f);
                res := res + more;
            }
            more := typeCollector(result, f);
            res := res + more;
        }
        case Primitive(primitive) => { }
        case Passthrough(str) => { }
        case TypeArg(ident) => { }
        case Object() => { }
    }
  }


  method literalCollector<t>(lit : Literal, f : Node -> seq<t>) returns (res : seq<t>)
  {
    res := f(NLiteral(lit));
    match lit {
        case BoolLiteral(b) => { }
        case IntLiteral(s, typ) => {
            var more := typeCollector(typ, f);
            res := res + more;
         }
        case DecLiteral(s1, s2, typ) => {
            var more := typeCollector(typ, f);
            res := res + more;
         }
        case StringLiteral(s, verbatim) => { }
        case CharLiteral(c) => { }
        case CharLiteralUTF16(n) => { }
        case Null(typ) => {
            var more := typeCollector(typ, f);
            res := res + more;
         }
    }
  }

  method exprCollector<t>(exp : Expression, f : Node -> seq<t>) returns (res : seq<t>)
  {
    var more := [];
    res := f(NExp(exp));
    match exp {
      case Literal(lit) => { 
          more := literalCollector(lit, f);
          res := res + more;
      }
      case Ident(name) => { }
      case Companion(idents, typeArgs) => { 
          for i:=0 to |typeArgs| {
              more := typeCollector(typeArgs[i], f);
              res := res + more;
          }
      }
      case Tuple(exps) => {
          more := exprsCollector(exps, f);
          res := res + more;
      }
      case New(path, typeArgs, args) => {
          more := exprsCollector(args, f);
          res := res + more;
          for i:=0 to |typeArgs| {
              more := typeCollector(typeArgs[i], f);
              res := res + more;
          }
      }
      case NewUninitArray(dims, typ) => {
          more := exprsCollector(dims, f);
          res := res + more;
          more := typeCollector(typ, f);
          res := res + more;
      }
      case ArrayIndexToInt(value) => {
          more := exprCollector(value, f);
          res := res + more;
      }
      case FinalizeNewArray(value, typ) => {
          more := exprCollector(value, f);
          res := res + more;
          more := typeCollector(typ, f);
          res := res + more;
      }
      case DatatypeValue(datatypeType, typeArgs, variant, isCo, contents) => {
          for i:=0 to |typeArgs| {
              more := typeCollector(typeArgs[i], f);
              res := res + more;
          }
          for i:=0 to |contents| {
              more := exprCollector(contents[i].1, f);
              res := res + more;
          }
      }
      case Convert(value, from, typ) => {
          more := exprCollector(value, f);
          res := res + more;
          more := typeCollector(from, f);
          res := res + more;
      }
      case SeqConstruct(length, elem) => {
          more := exprCollector(length, f);
          res := res + more;
          more := exprCollector(elem, f);
          res := res + more;
      }
      case SeqValue(elements, typ) => {
          more := exprsCollector(elements, f);
          res := res + more;
          more := typeCollector(typ, f);
          res := res + more;
      }
      case SetValue(elements) => {
          more := exprsCollector(elements, f);
          res := res + more;
      }
      case MultisetValue(elements) => {
          more := exprsCollector(elements, f);
          res := res + more;
      }
      case MapValue(mapElems, _, _) => {
          for i:=0 to |mapElems| {
              more := exprCollector(mapElems[i].0, f);
              res := res + more;
              more := exprCollector(mapElems[i].1, f);
              res := res + more;
          }
      }
      case MapBuilder(keyType, valueType) => {
          more := typeCollector(keyType, f);
          res := res + more;
          more := typeCollector(valueType, f);
          res := res + more;
      }
      case SeqUpdate(expr, indexExpr, value, _, _) => {
          more := exprCollector(expr, f);
          res := res + more;
          more := exprCollector(indexExpr, f);
          res := res + more;
          more := exprCollector(value, f);
          res := res + more;
      }
      case MapUpdate(expr, indexExpr, value, _, _) => {
          more := exprCollector(expr, f);
          res := res + more;
          more := exprCollector(indexExpr, f);
          res := res + more;
          more := exprCollector(value, f);
          res := res + more;
      }
      case SetBuilder(elemType) => { 
          more := typeCollector(elemType, f);
          res := res + more;
      }
      case ToMultiset(expr) => {
          more := exprCollector(expr, f);
          res := res + more;
      }
      case This() => { }
      case Ite(cond, thn, els) => {
          more := exprCollector(cond, f);
          res := res + more;
          more := exprCollector(thn, f);
          res := res + more;
          more := exprCollector(els, f);
          res := res + more;
      }
      case UnOp(unOp, expr, format1) => {
          more := exprCollector(expr, f);
          res := res + more;
      }
      case BinOp(op, left, right, format2) => {
          more := exprCollector(left, f);
          res := res + more;
          more := exprCollector(right, f);
          res := res + more;
      }
      case ArrayLen(expr, exprType, dim, native) => {
          more := exprCollector(expr, f);
          res := res + more;
          more := typeCollector(exprType, f);
          res := res + more;
      }
      case MapKeys(expr) => {
          more := exprCollector(expr, f);
          res := res + more;
      }
      case MapValues(expr) => {
          more := exprCollector(expr, f);
          res := res + more;
      }
      case Select(expr, field, isConstant, onDatatype, fieldType) => {
          more := exprCollector(expr, f);
          res := res + more;
      }
      case SelectFn(expr, field, onDatatype, isStatic, isConstant, arguments) => {
          more := exprCollector(expr, f);
          res := res + more;
      }
      case Index(expr, collKind, indices) => {
          more := exprCollector(expr, f);
          res := res + more;
          more := exprsCollector(indices, f);
          res := res + more;
      }
      case IndexRange(expr, isArray, low, high) => {
          more := exprCollector(expr, f);
          res := res + more;
          match low {
              case Some(l) => {
                  more := exprCollector(l, f);
                  res := res + more;
              }
              case None => { }
          }
          match high {
              case Some(h) => {
                  more := exprCollector(h, f);
                  res := res + more;
              }
              case None => { }
          }
      }
      case TupleSelect(expr, index, fieldType) => {
          more := exprCollector(expr, f);
          res := res + more;
          more := typeCollector(fieldType, f);
          res := res + more;
      }
      case Call(on, callName, typeArgs, args) => {
          more := exprCollector(on, f);
          res := res + more;
          more := exprsCollector(args, f);
          res := res + more;
          for i:=0 to |typeArgs| {
              more := typeCollector(typeArgs[i], f);
              res := res + more;
          }
      }
      case Lambda(params, retType, body) => { 
          more := stmtsCollector(body, f);
          res := res + more;
          more := typeCollector(retType, f);
          res := res + more;
      }
      case BetaRedex(values, retType, expr) => {
          for i:=0 to |values| {
              more := exprCollector(values[i].1, f);
              res := res + more;
          }
          more := exprCollector(expr, f);
          res := res + more;
          more := typeCollector(retType, f);
          res := res + more;
      }
      case IIFE(ident, typ, value, iifeBody) => {
          more := exprCollector(value, f);
          res := res + more;
          more := exprCollector(iifeBody, f);
          res := res + more;
          more := typeCollector(typ, f);
      }
      case Apply(expr, args) => {
          more := exprCollector(expr, f);
          res := res + more;
          more := exprsCollector(args, f);
          res := res + more;
      }
      case TypeTest(on, dType, variant) => {
          more := exprCollector(on, f);
          res := res + more;
      }
      case InitializationValue(typ) => { }
      case BoolBoundedPool() => { }
      case SetBoundedPool(of) => {
          more := exprCollector(of, f);
          res := res + more;
      }
      case MapBoundedPool(of) => {
          more := exprCollector(of, f);
          res := res + more;
      }
      case SeqBoundedPool(of, includeDuplicates) => {
          more := exprCollector(of, f);
          res := res + more;
      }
      case IntRange(_, lo, hi, up) => {
          more := exprCollector(lo, f);
          res := res + more;
          more := exprCollector(hi, f);
          res := res + more;
      }
      case UnboundedIntRange(start, up) => {
          more := exprCollector(start, f);
          res := res + more;
      }
      case Quantifier(elemType, collection, is_forall, lambda) => {
          more := exprCollector(collection, f);
          res := res + more;
          more := exprCollector(lambda, f);
          res := res + more;
          more := typeCollector(elemType, f);
          res := res + more;
      }
    }    
  }

  method exprsCollector<t>(exps : seq<Expression>, f : Node -> seq<t>) returns (res : seq<t>)
  {
    res := [];
    for i:=0 to |exps| {
      var more := exprCollector(exps[i], f);
      res := res + more;
    }
  }

  method stmtCollector<t>(stmt : Statement, f : Node -> seq<t>) returns (res : seq<t>)
  {
      var more := [];
      res := f(NStmt(stmt));
      match stmt {
        case DeclareVar(name, typ, maybeValue) => {
          match maybeValue {
              case Some(value) => {
                more := exprCollector(value, f);
                res := res + more;
              }
              case None => { }
          }
          more := typeCollector(typ, f);
          res := res + more;
        }
        case Assign(lhs, value) => {
          more := exprCollector(value, f);
          res := res + more;
        }
        case If(cond, thn, els) => {
          more := exprCollector(cond, f);
          res := res + more;
          more := stmtsCollector(thn, f);
          res := res + more;
          more := stmtsCollector(els, f);
          res := res + more;
        }
        case Labeled(lbl, body) => {
          more := stmtsCollector(body, f);
          res := res + more;
        }
        case While(cond, body) => {
          more := exprCollector(cond, f);
          res := res + more;
          more := stmtsCollector(body, f);
          res := res + more;
        }
        case Foreach(boundName, boundType, over, body) => {
          more := exprCollector(over, f);
          res := res + more;
          more := typeCollector(boundType, f);
          res := res + more;
          more := stmtsCollector(body, f);
          res := res + more;
        }
        case Call(on, callName, typeArgs, args, outs) => {
          more := exprCollector(on, f);
          res := res + more;
          for i:=0 to |typeArgs| {
              more := typeCollector(typeArgs[i], f);
              res := res + more;
          }
          more := exprsCollector(args, f);
          res := res + more;
        }
        case Return(expr) => {
          more := exprCollector(expr, f);
          res := res + more;
        }
        case EarlyReturn() => { }
        case Break(toLabel) => { }
        case TailRecursive(body) => {
          more := stmtsCollector(body, f);
          res := res + more;
        }
        case JumpTailCallStart() => { }
        case Halt() => { }
        case Print(expr) => {
          more := exprCollector(expr, f);
          res := res + more;
        }
        case ConstructorNewSeparator(fields) => { }
      }
  }

  method stmtsCollector<t>(stmts : seq<Statement>, f : Node -> seq<t>) returns (res : seq<t>)
  {
      res := [];
      for i:=0 to |stmts| {
        var more := stmtCollector(stmts[i], f);
        res := res + more;
      }
  }


  // datatype Method = Method(
  //   isStatic: bool,
  //   hasBody: bool,
  //   outVarsAreUninitFieldsToAssign: bool, // For constructors
  //   wasFunction: bool, // To choose between "&self" and "&mut self"
  //   overridingPath: Option<seq<Ident>>,
  //   name: Name,
  //   typeParams: seq<TypeArgDecl>,
  //   params: seq<Formal>,
  //   body: seq<Statement>,
  //   outTypes: seq<Type>,
  //   outVars: Option<seq<Ident>>)
  method methodCollector<t>(m : Method, f : Node -> seq<t>) returns (res : seq<t>) {
    var more := [];
    res := [];
    for i:=0 to |m.body| {
      more := stmtCollector(m.body[i], f);
      res := res + more;
    }
    for i:=0 to |m.outTypes| {
      more := typeCollector(m.outTypes[i], f);
      res := res + more;
    }
  }


  // datatype Class = Class(name: Name, 
    // enclosingModule: Ident, 
    //   typeParams: seq<TypeArgDecl>, 
    //   superClasses: seq<Type>, 
    //   fields: seq<Field>, body: seq<ClassItem>, attributes: seq<Attribute>)
  // datatype ClassItem = Method(Method)

  method classCollector<t>(cls : Class, f : Node -> seq<t>) returns (res : seq<t>)
  {
    var more := [];
    res := [];
    for i:=0 to |cls.superTraitTypes| {
      more := typeCollector(cls.superTraitTypes[i], f);
      res := res + more;
    }
    for i:=0 to |cls.body| {
      match cls.body[i] {
        case Method(m) => {
          more := methodCollector(m, f);
          res := res + more;
        }
      }
    }
  }

  // datatype Module = Module(name: Name, attributes: seq<Attribute>, body: Option<seq<ModuleItem>>)

  // datatype ModuleItem =
  //   | Module(Module)
  //   | Class(Class)

  function sum(ns : seq<nat>) : nat {
    if |ns| == 0
      then 0 
      else (ns[0] + sum(ns[1..])) as nat
  }

  method moduleCollector_inner<t>(mod : Module, f : Node -> seq<t>, n_steps : nat) returns (res : seq<t>)
  decreases n_steps
  {
    if n_steps == 0 {
      res := [];
    }
    else {
      res := [];
      var more := [];
      match mod.body {
        case Some(items) => {
          for i:=0 to |items| {
            match items[i] {
              case Module(m) => {
                more := moduleCollector_inner(m, f, n_steps - 1);
                res := res + more;
              }
              case Class(cls) => {
                more := classCollector(cls, f);
                res := res + more;
              }
              case _ => { }
            }            
            res := res + more;
          }
        }
        case None => { }
      }
    }    
  }
  method moduleCollector<t>(mod : Module, f : Node -> seq<t>) returns (res : seq<t>) {
    res := moduleCollector_inner(mod, f, 99999999999999999);
  }


}

