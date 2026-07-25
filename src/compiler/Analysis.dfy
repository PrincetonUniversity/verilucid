include "AST.dfy"

include "CollectVisitor.dfy"
module Analysis {
  import opened DAST
  import opened Std.Wrappers
  import opened DAST.Format
  import opened Std.Collections
  import opened CollectVisitor


  // collect all the call expressions in a program
  function accCallNames(node : Node) : seq<CallName>
  {
    match node {
        case NExp(Call(_, callname, _, _)) => [callname]
        case NStmt(Call(_, callname, _, _, _)) => [callname]
        case _ => []
    }
  }

  method getCallNames(m : Module) returns (rv : seq<CallName>) {
    rv := moduleCollector(m, accCallNames);
  }

  function accStringLiterals(node : Node) : seq<string>
  {
    match node {
      case NLiteral(StringLiteral(str, _)) => [str]
      case _ => []
    }
  }
  
  method getStringLiterals(e :Expression) returns (rv : seq<string>) {
    rv := exprCollector(e, accStringLiterals);
  }

}