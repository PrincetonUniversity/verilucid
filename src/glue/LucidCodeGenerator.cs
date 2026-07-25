// ADDED
using System;
using System.IO;
using System.Linq;
using Dafny;

using LucidPlugin;

namespace Microsoft.Dafny.Compilers;

class LucidCodeGenerator : DafnyWrittenCodeGenerator {

  public override void Compile(Sequence<DAST.Module> program, Sequence<ISequence<Rune>> otherFiles, ConcreteSyntaxTree w) {
    w.Write(COMP.Compile(program).ToVerbatimString(false));
  }

  public override ISequence<Rune> EmitCallToMain(DAST.Expression companion, Sequence<Rune> mainMethodName, bool hasArguments) {
    return COMP.EmitCallToMain(companion);
  }
}
