include "AST.dfy"

include "MapVisitor.dfy"
include "LAST.dfy"
include "DastToLast.dfy"
include "NormalizeLucidAst.dfy"

module {:extern "LucidPlugin"} LucidPlugin {
  import opened DAST
  import opened Std.Wrappers
  import opened DAST.Format
  import opened Std.Collections
  import PPrint
  import opened LAST
  import opened Translator
  import opened Normalizer

  class COMP {
    
    static method Compile(p: seq<Module>) returns (s: string) {
      print("\ntranslating Dafny IR to Lucid IR\n");
      var ds : seq<decl> := trModules(p);
      print("\n------- initial program -------\n");
      var pass := wellformedCheck(ds);
      s := LAST.declStrs(ds);      
      print("\n------- pre-normalized program -------\n");
      print(s);
      print("\nreducing abstractions\n");
      ds := ProcessProg(ds);
      print("\n------- final program -------\n");
      pass := wellformedCheck(ds);
      print ("-------------\n");
      s := LAST.declStrs(ds);      
      print(s);
    }

    static method EmitCallToMain(companion: Expression) returns (s: string) {
      s := "";
    }

  }
}