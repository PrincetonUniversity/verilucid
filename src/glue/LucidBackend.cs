// ADDED
// copy from ResolvedDesugaredExecutableDafnyBackend to LucidBackend

using System.Collections.Generic;
using System.IO;
using System.Text.RegularExpressions;

namespace Microsoft.Dafny.Compilers;

public class LucidBackend : DafnyExecutableBackend
{

  protected override bool CanEmitUncompilableCode => false;
  public override IReadOnlySet<string> SupportedExtensions => new HashSet<string> { ".dfy" };
  public override string TargetName => "Lucid";
  public override bool IsStable => false;
  public override bool IsInternal => true;
  public override string TargetExtension => "dpt";
  public override bool SupportsInMemoryCompilation => false;
  public override bool TextualTargetIsExecutable => true;
  public override string TargetBaseDir(string dafnyProgramName) =>
    $"{Path.GetFileNameWithoutExtension(dafnyProgramName)}-Lucid/src";
  protected override DafnyWrittenCodeGenerator CreateDafnyWrittenCompiler() {
    return new LucidCodeGenerator();
  }

  public LucidBackend(DafnyOptions options) : base(options) {
  }


    
}
