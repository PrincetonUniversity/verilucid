include "AST.dfy"

module MapVisitor {
  import opened DAST
  import opened Std.Wrappers
  import opened DAST.Format
  import opened Std.Collections

  // simplifiers to use with exprVisitor
  function elimConvert(expr : Expression) : Expression {
    match expr {
      case Convert(value, from, typ) => value
      case _ => expr
    }
  }
  function elimSelect(expr: Expression) : Expression {
    match expr {
      case Select(expr, field, isConstant, onDatatype, fieldType) => 
        Expression.Ident(field)
      case _ => expr
    }
  }
  function elimArgSelects(expr: Expression) : Expression {
    match expr {
      case Call(on, callName, typeArgs, args) => 
        Expression.Call(on, callName, typeArgs, Seq.Map(elimSelect, args))
      case _ => expr
    }
  }

  // post-visiting replacer for expressions  
  function exprVisitor(exp : Expression, f : Expression -> Expression) : Expression   
  decreases exp, 1
  {
    match exp {
      case Tuple(exps) => 
        var newExps :=  exprSeqVisitor(exps, f);
        f(Expression.Tuple(newExps))
      case New(path, typeArgs, args) =>
        var newArgs := exprSeqVisitor(args, f);
        f(Expression.New(path, typeArgs, newArgs))
      case NewUninitArray(dims, typ) =>
        var newDims := exprSeqVisitor(dims, f);
        f(Expression.NewUninitArray(newDims, typ))
      case ArrayIndexToInt(value) =>
        f(Expression.ArrayIndexToInt(exprVisitor(value, f)))
      case FinalizeNewArray(value, typ) =>
        f(Expression.FinalizeNewArray(exprVisitor(value, f), typ))
      case DatatypeValue(datatypeType, typeArgs, variant, isCo, contents) =>
        var new_contents := exprSeqSndVisitor(contents, f);
        f(Expression.DatatypeValue(datatypeType, typeArgs, variant, isCo, new_contents))
      case Convert(value, from, typ) =>
        f(Expression.Convert(exprVisitor(value, f), from, typ))
      case SeqConstruct(length, elem) =>
        f(Expression.SeqConstruct(exprVisitor(length, f), exprVisitor(elem, f)))
      case SeqValue(elements, typ) =>
        var newElements := exprSeqVisitor(elements, f);
        f(Expression.SeqValue(newElements, typ))
      case SetValue(elements) =>
        var newElements := exprSeqVisitor(elements, f);
        f(Expression.SetValue(newElements))
      case MultisetValue(elements) =>
        var newElements := exprSeqVisitor(elements, f);
        f(Expression.MultisetValue(newElements))
      case MapValue(mapElems, domainType, rangeType) =>
        var newMapElems := exprSeqBothVisitor(mapElems, f);
        f(Expression.MapValue(newMapElems, domainType, rangeType))
      case SeqUpdate(expr, indexExpr, value, collectionType, exprType) =>
        f(Expression.SeqUpdate(exprVisitor(expr, f), exprVisitor(indexExpr, f), exprVisitor(value, f), collectionType, exprType))
      case MapUpdate(expr, indexExpr, value, collectionType, exprType) =>
        f(Expression.MapUpdate(exprVisitor(expr, f), exprVisitor(indexExpr, f), exprVisitor(value, f), collectionType, exprType))
      case ToMultiset(expr) =>
        f(Expression.ToMultiset(exprVisitor(expr, f)))
      case Ite(cond, thn, els) =>
        f(Expression.Ite(exprVisitor(cond, f), exprVisitor(thn, f), exprVisitor(els, f)))
      case UnOp(unOp, expr, format1) =>
        f(Expression.UnOp(unOp, exprVisitor(expr, f), format1))
      case BinOp(op, left, right, format2) =>
        f(Expression.BinOp(op, exprVisitor(left, f), exprVisitor(right, f), format2))
      case ArrayLen(expr, exprType, dim, native) =>
        f(Expression.ArrayLen(exprVisitor(expr, f), exprType, dim, native))
      case MapKeys(expr) =>
        f(Expression.MapKeys(exprVisitor(expr, f)))
      case MapValues(expr) =>
        f(Expression.MapValues(exprVisitor(expr, f)))
      case Select(expr, field, isConstant, onDatatype, fieldType) =>
        f(Expression.Select(exprVisitor(expr, f), field, isConstant, onDatatype, fieldType))
      case SelectFn(expr, field, onDatatype, isStatic, isConstant, arguments) =>
        f(Expression.SelectFn(exprVisitor(expr, f), field, onDatatype, isStatic, isConstant, arguments))
      case Index(expr, collKind, indices) =>
        var newIndices := exprSeqVisitor(indices, f);
        f(Expression.Index(exprVisitor(expr, f), collKind, newIndices))
      case IndexRange(expr, isArray, low, high) =>
        f(Expression.IndexRange(exprVisitor(expr, f), isArray, exprOptionVisitor(low, f), exprOptionVisitor(high, f)))
      case TupleSelect(expr, index, fieldType) =>
        f(Expression.TupleSelect(exprVisitor(expr, f), index, fieldType))
      case Call(on, callName, typeArgs, args) =>
        var newArgs := exprSeqVisitor(args, f);
        f(Expression.Call(exprVisitor(on, f), callName, typeArgs, newArgs))
      case BetaRedex(values, retType, expr) =>
        var newValues := exprSeqSndVisitor(values, f);
        f(Expression.BetaRedex(newValues, retType, exprVisitor(expr, f)))
      case IIFE(ident, typ, value, iifeBody) =>
        f(Expression.IIFE(ident, typ, exprVisitor(value, f), exprVisitor(iifeBody, f)))
      case Apply(expr, args) =>
        var newArgs := exprSeqVisitor(args, f);
        f(Expression.Apply(exprVisitor(expr, f), newArgs))
      case TypeTest(on, dType, variant) =>
        f(Expression.TypeTest(exprVisitor(on, f), dType, variant))
      case SetBoundedPool(of) =>  
        f(Expression.SetBoundedPool(exprVisitor(of, f)))
      case MapBoundedPool(of) =>  
        f(Expression.MapBoundedPool(exprVisitor(of, f)))
      case SeqBoundedPool(of, includeDuplicates) =>
        f(Expression.SeqBoundedPool(exprVisitor(of, f), includeDuplicates))
      case IntRange(elemType, lo, hi, up) =>
        f(Expression.IntRange(elemType, exprVisitor(lo, f), exprVisitor(hi, f), up))
      case UnboundedIntRange(start, up) =>
        f(Expression.UnboundedIntRange(exprVisitor(start, f), up))
      case Quantifier(elemType, collection, is_forall, lambda) =>
        f(Expression.Quantifier(elemType, exprVisitor(collection, f), is_forall, exprVisitor(lambda, f)))
      case _ => f(exp)
    }
  }
  function exprOptionVisitor(exp : Option<Expression>, f : Expression -> Expression) : Option<Expression>
    decreases exp, 0
  {
    match exp {
      case None => None
      case Some(e) => Some(exprVisitor(e, f))
    }
  }

  function exprSeqSndVisitor<T>(t_exps: seq<(T, Expression)>, f : Expression -> Expression) : seq<(T, Expression)> 
  decreases t_exps, 0
  {
    match |t_exps| {
      case 0 => t_exps
      case 1 => [(t_exps[0].0, exprVisitor(t_exps[0].1, f))]
      case _ => 
        [(t_exps[0].0, exprVisitor(t_exps[0].1, f))] + exprSeqSndVisitor(t_exps[1..], f)
    }
    // Seq.Map((x : Expression) => exprVisitor(x, f), exps)
  }
  function exprSeqBothVisitor(t_exps: seq<(Expression, Expression)>, f : Expression -> Expression) : seq<(Expression, Expression)> 
  decreases t_exps, 0
  {
    match |t_exps| {
      case 0 => t_exps
      case 1 => [(exprVisitor(t_exps[0].0, f), exprVisitor(t_exps[0].1, f))]
      case _ => 
        [(t_exps[0].0, exprVisitor(t_exps[0].1, f))] + exprSeqSndVisitor(t_exps[1..], f)
    }
    // Seq.Map((x : Expression) => exprVisitor(x, f), exps)
  }
  function exprSeqVisitor(exps: seq<Expression>, f : Expression -> Expression) : seq<Expression> 
  decreases exps, 0
  {
    match |exps| {
      case 0 => exps
      case 1 => [exprVisitor(exps[0], f)]
      case _ => 
        [exprVisitor(exps[0], f)] + exprSeqVisitor(exps[1..], f)
    }
    // Seq.Map((x : Expression) => exprVisitor(x, f), exps)
  }

  function exprInAssignLhsVisitor(lhs : AssignLhs, f : Expression -> Expression) : AssignLhs
  decreases lhs, 1
  {
    match lhs {
      case Ident(ident) => AssignLhs.Ident(ident)
      case Select(expr, field, isConstant) => AssignLhs.Select(exprVisitor(expr, f), field, isConstant)
      case Index(expr, indices) => AssignLhs.Index(exprVisitor(expr, f), exprSeqVisitor(indices, f))
    }
  }

  function exprInStatementVisitor(stmt : Statement, f : Expression -> Expression) : Statement
  decreases stmt, 1
  {
    match stmt {
      case DeclareVar(name, typ, maybeValue) => 
        var maybeValue := match maybeValue {
          case None => None
          case Some(value) => Some(exprVisitor(value, f))
        };
        Statement.DeclareVar(name, typ, maybeValue)
      case Assign(lhs, value) => 
        Statement.Assign(exprInAssignLhsVisitor(lhs, f), exprVisitor(value, f))
      case If(cond, thn, els) => 
        Statement.If(exprVisitor(cond, f), exprInStatementsVisitor(thn, f), exprInStatementsVisitor(els, f))
      case Labeled(lbl, body) => 
        Statement.Labeled(lbl, exprInStatementsVisitor(body, f))
      case While(cond, body) => 
        Statement.While(exprVisitor(cond, f), exprInStatementsVisitor(body, f))
      case Foreach(boundName, boundType, over, body) => 
        Statement.Foreach(boundName, boundType, exprVisitor(over, f), exprInStatementsVisitor(body, f))
      case Call(on, callName, typeArgs, args, outs) => 
        var newArgs := exprSeqVisitor(args, f);
        Statement.Call(exprVisitor(on, f), callName, typeArgs, newArgs, outs)
      case Return(expr) => 
        Statement.Return(exprVisitor(expr, f))
      case EarlyReturn() => 
        Statement.EarlyReturn()
      case Break(toLabel) => 
        Statement.Break(toLabel)
      case TailRecursive(body) => 
        Statement.TailRecursive(exprInStatementsVisitor(body, f))
      case JumpTailCallStart() => 
        Statement.JumpTailCallStart()
      case Halt() => 
        Statement.Halt()
      case Print(expr) => 
        Statement.Print(exprVisitor(expr, f))
      case ConstructorNewSeparator(fields) => 
        Statement.ConstructorNewSeparator(fields)
    }
  }

  function exprInStatementsVisitor(stmts : seq<Statement>, f : Expression -> Expression) : seq<Statement>
  decreases stmts, 0
  {
    match |stmts| {
      case 0 => stmts
      case 1 => [exprInStatementVisitor(stmts[0], f)]
      case _ => 
        [exprInStatementVisitor(stmts[0], f)] + exprInStatementsVisitor(stmts[1..], f)
    }
  }

}


