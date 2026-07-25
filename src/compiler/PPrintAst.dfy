include "AST.dfy"

module {:options "/functionSyntax:4"} NatPrinter {

  type stringNat = s: string |
    |s| > 0 && (|s| > 1 ==> s[0] != '0') &&
    forall i | 0 <= i < |s| :: s[i] in "0123456789"
    witness "1"

  function natToString(n: nat): stringNat {
    match n
    case 0 => "0" case 1 => "1" case 2 => "2" case 3 => "3" case 4 => "4"
    case 5 => "5" case 6 => "6" case 7 => "7" case 8 => "8" case 9 => "9"
    case _ => natToString(n / 10) + natToString(n % 10)
  }

  function stringToNat(s: stringNat): nat
    decreases |s|
  {
    if |s| == 1 then
      match s[0]
      case '0' => 0 case '1' => 1 case '2' => 2 case '3' => 3 case '4' => 4
      case '5' => 5 case '6' => 6 case '7' => 7 case '8' => 8 case '9' => 9
    else
      stringToNat(s[..|s|-1])*10 + stringToNat(s[|s|-1..|s|])
  }

  lemma natToStringThenStringToNatIdem(n: nat)
    ensures stringToNat(natToString(n)) == n
  { // Proof is automatic
  }
  lemma stringToNatThenNatToStringIdem(n: stringNat)
    ensures natToString(stringToNat(n)) == n
  { // Proof is automatic
  }
}


module PPrint {
  import opened DAST
  import opened Std.Wrappers
  import opened DAST.Format
  import opened Std.Collections
  import opened NatPrinter

  function natToString (i : nat) : string {
    NatPrinter.natToString(i)
  }

  function  strFlatten_inner (s: seq<string>, sep : string) : string {
    match |s| {
      case 0 => ""
      case 1 => s[0]
      case n => 
        s[0] + sep + strFlatten_inner(s[1..], sep)
    }
  }
  function strFlatten_brackets (s: seq<string>, sep : string) : string {
    "[ " + strFlatten_inner(s, sep) + " ]"
  }

  function strFlatten (s: seq<string>, sep : string) : string {
    strFlatten_inner(s, sep)
  }

  function indent_rest(s:string): string {
    if |s| == 0 then ""
    else 
      var new_start := if s[0] == '\n' 
        then [s[0]] + "  "
        else [s[0]]
      ;
      if |s| > 1 
        then new_start + indent_rest(s[1..])
        else new_start
  }

  function indent(s:string): string {
    "  " + indent_rest(s)
  }

  function  boolToString(b: bool) : string {
    if b then "true" else "false"
  }

  function  optionToString<T>(opt: Option<T>, f: (T) -> string) : string {
    match opt
    {
        case None => "None"
        case Some(x) => "Some(" + f(x) + ")"
    }
  }

  function  nameToString(n: Name) : string {
    n.dafny_name
  }
  function  varNameToString(v: VarName) : string {
    v.dafny_name
  }
  function  moduleToString(m: Module) : string
  {
      var nameStr := nameToString(m.name);
      var attributes := seq(|m.attributes|, i requires 0 <= i < |m.attributes| => attributeToString(m.attributes[i]));
      var body := match m.body {
        case None => "None"
        case Some(b) => 
          var body := seq(|b|, i requires 0 <= i < |b| => moduleItemToString(b[i], 9999));
          strFlatten(body, "\n,")
      };
      "Module(\nname: " + nameStr + ",\nattributes: " + indent(strFlatten(attributes, ",\n")) + ",\nbody: " + indent(body) + "\n)"
  }
  function  modulesToString(ms : seq<Module>) : string 
  {
    match |ms| {
      case 0 => ""
      case 1 => moduleToString(ms[0])
      case _ => moduleToString(ms[0]) + "\n" + modulesToString(ms[1..])
    }
  }

  function  moduleItemToString(mi: ModuleItem, counter : nat) : string
  decreases counter
  {
      if counter == 0 then ".."
      else 
      match mi
      {
          // case Module(m) => "Module(" + "..." + ")"
          case Module(m) => 
            var nameStr := nameToString(m.name);
            var attributes := seq(|m.attributes|, i requires 0 <= i < |m.attributes| => attributeToString(m.attributes[i]));
            var body := match m.body {
              case None => "None"
              case Some(b) => 
              var body := seq(|b|, i requires 0 <= i < |b| => moduleItemToString(b[i], counter - 1));
              strFlatten_brackets(body, ",")
            };
            "Module(name: " + nameStr + ", attributes: " + strFlatten_brackets(attributes, ",") + ", body: " + body + ")"
          case Class(c) => indent(classToString(c))
          case Trait(t) => indent(traitToString(t))
          case Newtype(n) => indent(newtypeToString(n))
          case SynonymType(st) => indent(synonymTypeToString(st))
          case Datatype(d) => indent(datatypeToString(d))
      }
  } 
  // function  moduleItemsToString(mis : seq<ModuleItem>) : string 
  // decreases mis
  // {
  //   match |mis| {
  //     case 0 => ""
  //     case 1 => moduleItemToString(mis[0])
  //     case _ => moduleItemToString(mis[0]) + "," + moduleItemsToString(mis[1..])
  //   }
  // }


  function  typeToString(t: Type) : string
  {        
      match t
      {
          case UserDefined(resolved) => resolvedTypeToString(resolved)
          case Tuple(types) => 
            var types := seq(|types|, i requires 0 <= i < |types| => typeToString(types[i]));
            var types := strFlatten_brackets(types, ",");
            "(" + types + ")"
          case Array(element, _) =>  "DafnyArray<"+ typeToString(element) + ">"
          case Seq(element) => "Seq<" + typeToString(element) + ">"
          case Set(element) => "Set<" + typeToString(element) + ">"
          case Multiset(element) => "Multiset(" + typeToString(element) + ")"
          case Map(key, value) => "Map(key: " + typeToString(key) + ", value: " + typeToString(value) + ")"
          case SetBuilder(element) => "SetBuilder(" + typeToString(element) + ")"
          case MapBuilder(key, value) => "MapBuilder(key: " + typeToString(key) + ", value: " + typeToString(value) + ")"
          case Arrow(args, result) => 
            var args := seq(|args|, i requires 0 <= i < |args| => typeToString(args[i]));
            "Arrow(args: " + strFlatten_brackets(args, ",") + ", result: " + typeToString(result) + ")"
          case Primitive(primitive) => primitiveToString(primitive)          
        //   "Primitive(" + primitiveToString(primitive) + ")"
          case Passthrough(str) => "Passthrough(" + str + ")"
          case TypeArg(ident) => identToString(ident)          
        //   "TypeArg(" + identToString(ident) + ")"
          case Object() => "Object"
      }
  }

  function  seqToStringInner<T>(ss: seq<T>, elemToString: (T) -> string) : string
  {
      if |ss| == 0 then
          ""
      else if |ss| == 1 then
          elemToString(ss[0])
      else
        elemToString(ss[0]) + ", " + seqToStringInner(ss[1..], elemToString)
  }
  function  seqToString<T>(ss: seq<T>, elemToString: (T) -> string) : string
  {
      "[" + seqToStringInner(ss, elemToString) + "]"
  }

  function sep<T>(s : string, ss : seq<T>, elemToString : T -> string) : string {
    match |ss| {
      case 0 => ""
      case 1 => elemToString(ss[0])
      case _ => elemToString(ss[0]) + s + sep(s, ss[1..], elemToString)
    }
  }

  function comma_sep<T>(ss : seq<T>, elemToString : T -> string) : string {
    sep(", ", ss, elemToString)
  }
  function newline_sep<T>(ss : seq<T>, elemToString : T -> string) : string {
    sep("\n", ss, elemToString)
  }

  function  varianceToString(v: Variance) : string
  {
      match v
      {
          case Nonvariant => "Nonvariant"
          case Covariant => "Covariant"
          case Contravariant => "Contravariant"
      }
  }

  function  typeArgDeclToString(tad: TypeArgDecl) : string
  {
      "TypeArgDecl(name: " + identToString(tad.name) + 
      ", bounds: " + seqToString(tad.bounds, typeArgBoundToString) + ")"
  }

  function  typeArgBoundToString(tab: TypeArgBound) : string
  {
      match tab
      {
          case SupportsEquality => "SupportsEquality"
          case SupportsDefault => "SupportsDefault"
      }
  }

  function  primitiveToString(p: Primitive) : string
  {
      match p
      {
          case Int => "Int"
          case Real => "Real"
          case String => "String"
          case Bool => "Bool"
          case Char => "Char"
      }
  }    

  function  newtypeRangeToString(nr: NewtypeRange) : string
  {
      match nr
      {
          case U8(_) => "U8"
          case I8(_) => "I8"
          case U16(_) => "U16"
          case I16(_) => "I16"
          case U32(_) => "U32"
          case I32(_) => "I32"
          case U64(_) => "U64"
          case I64(_) => "I64"
          case U128(_) => "U128"
          case I128(_) => "I128"
          case BigInt => "BigInt"
          case NoRange => "NoRange"
          case _ => "OtherRange"
      }
  }

  function  attributeToString(attr: Attribute) : string
  {
      "Attribute(name: " + attr.name + ", args: " + seqToString(attr.args, x => x) + ")"
  }


  function  traitTypeToString(tt: TraitType) : string
  {
      "TraitType()"
  }

  function  newtypeTypeToString(nt: NewtypeType) : string
  {
      "NewtypeType(baseType: " + typeToString(nt.baseType) + 
      ", range: " + newtypeRangeToString(nt.range) + 
      ", erase: " + boolToString(nt.erase) + ")"
  }    

  function  resolvedTypeBaseToString(rtb: ResolvedTypeBase) : string
  {
      match rtb
      {
          case Class() => "Class()"
          case Datatype(_, _) => "Datatype()"
          case Trait(_) => "Trait()"
          case Newtype(baseType, range, erase) => "Newtype(baseType: " + typeToString(baseType) + 
                                                  ", range: " + newtypeRangeToString(range) + 
                                                  ", erase: " + boolToString(erase) + ")"
      }
  }

  function  resolvedTypeToString(rt: ResolvedType) : string
  {
      var typeArgs := seq(|rt.typeArgs|, i requires 0 <= i < |rt.typeArgs| => typeToString(rt.typeArgs[i]));
      var path := seq(|rt.path|, i requires 0 <= i < |rt.path| => identToString(rt.path[i]));
      strFlatten(path, ".") 
      + if |typeArgs| > 0 
        then "<" + strFlatten(typeArgs, ", ") + ">"
        else ""
    //   "ResolvedType(path: " + seqToString(rt.path, identToString) + "\n" + 
    //   ", typeArgs: " + strFlatten_brackets(typeArgs, ", ") + "\n" +
    //   ", kind: " + resolvedTypeBaseToString(rt.kind) + "\n" +
    //   ", attributes: " + seqToString(rt.attributes, attributeToString) + "\n" +
    //   ", properMethods: " +  strFlatten_brackets(properMethods, ",") + "\n" +
    //   ", extendedTypes: "  + strFlatten_brackets(extendedTypes, ",") + ")" + "\n"
  }

  function  identToString(id: Ident) : string
  {
    nameToString(id.id)
  }

  function  classToString(cls: Class) : string
  {
      "Class(name: " + nameToString(cls.name) + "\n" +
      ", enclosingModule: " + identToString(cls.enclosingModule) + "\n" +
      ", typeParams: " + seqToString(cls.typeParams, typeArgDeclToString) + "\n" +
      ", superClasses: " + seqToString(cls.superTraitTypes, typeToString) + "\n" +
      ", fields: " + seqToString(cls.fields, fieldToString) + "\n" +
      ", body: " + indent(seqToString(cls.body, classItemToString)) + "\n" +
      ", attributes: " + seqToString(cls.attributes, attributeToString) + ")"
  }

  function  traitToString(tr: Trait) : string
  {
      "Trait(name: " + nameToString(tr.name) + "\n" +
      ", typeParams: " + seqToString(tr.typeParams, typeArgDeclToString) + "\n" +
      ", parents: " + seqToString(tr.parents, typeToString) + "\n" +
      ", body: " + indent(seqToString(tr.body, classItemToString)) + "\n" +
      ", attributes: " + seqToString(tr.attributes, attributeToString) + ")"
  }

  function  datatypeToString(dt: Datatype) : string
  {
      "Datatype(name: " + nameToString(dt.name) + "\n" + 
      ", enclosingModule: " + identToString(dt.enclosingModule) + "\n" +
      ", typeParams: " + seqToString(dt.typeParams, typeArgDeclToString) + "\n" +
      ", ctors: " + indent(seqToString(dt.ctors, datatypeCtorToString)) + "\n" +
      ", body: " + seqToString(dt.body, classItemToString) + "\n" +
      ", isCo: " + boolToString(dt.isCo) + "\n" +
      ", attributes: " + seqToString(dt.attributes, attributeToString) + ")"
  }

  function  datatypeDtorToString(dd: DatatypeDtor) : string
  {
      "DatatypeDtor(formal: " + formalToString(dd.formal) + 
      ", callName: " + optionToString(dd.callName, x => x) + ")"
  }

  function  datatypeCtorToString(dc: DatatypeCtor) : string
  {
      "DatatypeCtor(name: " + nameToString(dc.name) + 
      ", args: " + seqToString(dc.args, datatypeDtorToString) + 
      ", hasAnyArgs: " + boolToString(dc.hasAnyArgs) + ")" + "\n"
  }

  function  newtypeToString(nt: Newtype) : string
  {
      "Newtype(name: " + nameToString(nt.name) + 
      ", typeParams: " + seqToString(nt.typeParams, typeArgDeclToString) + 
      ", base: " + typeToString(nt.base) + 
      ", range: " + newtypeRangeToString(nt.range) + 
      ", constraint: " + optionToString(nt.constraint, newtypeConstraintToString) + 
      ", witnessStmts: " + seqToString(nt.witnessStmts, statementToString) + 
      ", witnessExpr: " + optionToString(nt.witnessExpr, expressionToString) + 
      ", attributes: " + seqToString(nt.attributes, attributeToString) + ")"
  }

  function  newtypeConstraintToString(nc: NewtypeConstraint) : string
  {
      "NewtypeConstraint(variable: " + formalToString(nc.variable) + 
      ", constraintStmts: " + seqToString(nc.constraintStmts, statementToString) + ")"
  }

  function  synonymTypeToString(st: SynonymType) : string
  {
      "SynonymType(name: " + nameToString(st.name) + 
      ", typeParams: " + seqToString(st.typeParams, typeArgDeclToString) + 
      ", base: " + typeToString(st.base) + 
      ", witnessStmts: " + seqToString(st.witnessStmts, statementToString) + 
      ", witnessExpr: " + optionToString(st.witnessExpr, expressionToString) + 
      ", attributes: " + seqToString(st.attributes, attributeToString) + ")"
  }

  function  classItemToString(ci: ClassItem) : string
  {
      match ci
      {
          case Method(m) => methodToString(m)
      }
  }

  function  fieldToString(f: Field) : string
  {
      "Field(formal: " + formalToString(f.formal) +
      ", defaultValue: " + optionToString(f.defaultValue, e => expressionToString(e)) + ")"
  }

  function  formalToString(f: Formal) : string
  {
        varNameToString(f.name) + " : " + typeToString(f.typ)
    //   "Formal(name: " + nameToString(f.name) + 
    //   ", typ: " + typeToString(f.typ) + 
    //   ", attributes: " + seqToString(f.attributes, attributeToString) + ")"
  }

  function  methodToString(m: Method) : string
  {
      var overridingPathStr := match m.overridingPath
          case None => "None"
          case Some(path) => seqToString(path, identToString);    
      var outVarsStr := match m.outVars
          case None => "None"
          case Some(vars) => seqToString(vars, varNameToString);
      "Method(name: " + nameToString(m.name) + "\n" +
      ", hasBody: " + boolToString(m.hasBody) + "\n" +
      ", outVarsAreUninitFieldsToAssign: " + boolToString(m.outVarsAreUninitFieldsToAssign) + "\n" +
      ", wasFunction: " + boolToString(m.wasFunction) + "\n" +
      ", overridingPath: " + overridingPathStr + "\n" +
      ", isStatic: " + boolToString(m.isStatic) + "\n" +
      ", typeParams: " + seqToString(m.typeParams, typeArgDeclToString) + "\n" +
      ", params: " + indent(sep(",\n", m.params, formalToString)) + "\n" +
      ", body: " + indent(sep(",\n", m.body, statementToString)) + "\n" +
      ", outTypes: " + seqToString(m.outTypes, typeToString) + "\n" +
      ", outVars: " + outVarsStr + ")"
  }

  function  callNameToString(cn: CallName) : string
  {
      match cn
      {
          case CallName(name, onType, receiverArg, receiverAsArgument, signature) =>
              nameToString(name) + "(" + seqToStringInner(signature.parameters, formalToString) + ")"
            //   "CallName(name: " + nameToString(name) + 
            //   ", onType: ..." + 
            //   ", receiverArgs: ..." + 
            //   ", onType: " + optionToString(onType, typeToString) + 
            //   ", receiverArgs: " + optionToString(receiverArgs, formalToString) + 
            //   ", signature: " + seqToString(signature.parameters, formalToString) + ")"
          case MapBuilderAdd => "MapBuilderAdd"
          case MapBuilderBuild => "MapBuilderBuild"
          case SetBuilderAdd => "SetBuilderAdd"
          case SetBuilderBuild => "SetBuilderBuild"
      }
  }

  function  statementToString(s: Statement) : string
  {
      match s
      {
          case DeclareVar(name, typ, maybeValue) =>
              var maybeValue := match maybeValue
                  case None => ""
                  case Some(value) => ":= " +expressionToString(value);
              varNameToString(name) + " : " + typeToString(typ) + maybeValue + ";"
            //   "DeclareVar(name: " + nameToString(name) + 
            //   ", typ: " + typeToString(typ) + 
            //   ", maybeValue: " + maybeValue + ")"
          case Assign(lhs, value) =>
                assignLhsToString(lhs) + " := " + expressionToString(value) + ";"
            //   "Assign(lhs: " + assignLhsToString(lhs) + 
            //   ", value: " + expressionToString(value) + ")"
          case If(cond, thn, els) =>
              var thn := seq(|thn|, i requires 0 <= i < |thn| => statementToString(thn[i]));
              var els := seq(|els|, i requires 0 <= i < |els| => statementToString(els[i]));
              "if(" + expressionToString(cond) + ") {\n" 
              + indent(strFlatten(thn, "\n")) + "\n} else {\n" 
              + indent(strFlatten(els, "\n")) + "\n}"
          case Labeled(lbl, body) =>
              var body := seq(|body|, i requires 0 <= i < |body| => statementToString(body[i]));
              lbl + "{\n" + indent(strFlatten_brackets(body, "\n")) + "\n}"
          case While(cond, body) =>
              var body := seq(|body|, i requires 0 <= i < |body| => statementToString(body[i]));
                "while (" + expressionToString(cond) + ") {\n" + indent(strFlatten_brackets(body, "\n")) + "\n}"
          case Foreach(boundName, boundType, over, body) =>
              var body := seq(|body|, i requires 0 <= i < |body| => statementToString(body[i]));
                "foreach(" + varNameToString(boundName) + " : " + typeToString(boundType) + " in " + expressionToString(over) + ") {\n" + indent(strFlatten_brackets(body, "\n")) + "\n}"
            //   "Foreach(boundName: " + nameToString(boundName) + 
            //   ", boundType: " + typeToString(boundType) + 
            //   ", over: " + expressionToString(over) + 
            //   ", body: " + strFlatten_brackets(body, ",") + ")"
          case Call(on, callName, typeArgs, args, outs) =>
              var argsStrs := seq(|args|, i requires 0 <= i < |args| => expressionToString(args[i]));
              var outsStr := match outs
                  case None => ""
                  case Some(vars) => seqToStringInner(vars, varNameToString) + " = ";
              outsStr 
                + expressionToString(on) + "." + callNameToString(callName) + "<"
                + seqToStringInner(typeArgs, typeToString) + ">("
                + strFlatten_inner(argsStrs, ",") + ")"
                
            //   var outsStr := match outs
            //       case None => "None"
            //       case Some(vars) => seqToString(vars, identToString);
            //   var args := seq(|args|, i requires 0 <= i < |args|  => expressionToString(args[i]));                
            //   "Call(on: " + expressionToString(on) + 
            //   ", callName: " + callNameToString(callName) + 
            //   ", typeArgs: " + seqToString(typeArgs, typeToString) + 
            //   ", args: " + strFlatten_brackets(args, ",") + 
            //   ", outs: " + outsStr + ")"
          case Return(expr) =>
              "return " + expressionToString(expr) + ";"
          case EarlyReturn() =>
              "return"
          case Break(toLabel) =>
              "Break(" + optionToString(toLabel, (x => x)) + ")"
          case TailRecursive(body) =>
              var body := seq(|body|, i requires 0 <= i < |body| => statementToString(body[i]));
              "TailRecursive(body: " +  strFlatten_brackets(body, ",") + ")"
          case JumpTailCallStart() =>
              "JumpTailCallStart(;)"
          case Halt() =>
              "Halt();"
          case Print(expr) =>
              "print(" + expressionToString(expr) + ");"
            //   "Print(expr: " + expressionToString(expr) + ")"
          case ConstructorNewSeparator(fields) =>
              var fields := seq(|fields|, i requires 0 <= i < |fields| => fieldToString(fields[i]));
              "new(" + strFlatten_brackets(fields, ",") + ");"
            //   "new(" + seqToString(fields, contentElemToString) + ");"
            //   "ConstructorNewSeparator(fields: " + seqToString(fields, formalToString) + ")"
      }
  }


  function  assignLhsToString(lhs: AssignLhs) : string
  {
      match lhs
      {
          case Ident(ident) => varNameToString(ident)
          case Select(expr, field, _) =>
              expressionToString(expr) + "." + field.dafny_name
          case Index(expr, indices) =>
              var indices := seq(|indices|, i requires 0 <= i < |indices| => expressionToString(indices[i]));
              expressionToString(expr) + "[" + strFlatten_brackets(indices, ",") + "]"
            //   "Index(expr: " + expressionToString(expr) + 
            //   ", indices: " + strFlatten_brackets(indices, ",") + ")"
      }
  }

  function  collKindToString(ck: CollKind) : string
  {
      match ck
      {
          case Seq => "Seq"
          case Array => "Array"
          case Map => "Map"
      }
  }

  function  binOpToString(bo: BinOp) : string
  {
      match bo
      {
          case Eq(referential) =>
              "Eq(referential: " + boolToString(referential) + ")"
          case Div(_) => "/"
          case EuclidianDiv() => "/"
          case Mod() => "%"
          case EuclidianMod() => "%"
          case Lt() => "<"
          case LtChar() => "<"
          case Plus(_) => "+"
          case Minus(_) => "-"
          case Times(_) => "*"
          case BitwiseAnd() => "&"
          case BitwiseOr() => "|"
          case BitwiseXor() => "^"
          case BitwiseShiftRight() => ">>"
          case BitwiseShiftLeft() => "<<"
          case And() => "&&"
          case Or() => "||"
          case In() => "in"
          case SeqProperPrefix() => "SeqProperPrefix()"
          case SeqPrefix() => "SeqPrefix()"
          case SetMerge() => "SetMerge()"
          case SetSubtraction() => "SetSubtraction()"
          case SetIntersection() => "SetIntersection()"
          case Subset() => "Subset()"
          case ProperSubset() => "ProperSubset()"
          case SetDisjoint() => "SetDisjoint()"
          case MapMerge() => "MapMerge()"
          case MapSubtraction() => "MapSubtraction()"
          case MultisetMerge() => "MultisetMerge()"
          case MultisetSubtraction() => "MultisetSubtraction()"
          case MultisetIntersection() => "MultisetIntersection()"
          case Submultiset() => "Submultiset()"
          case ProperSubmultiset() => "ProperSubmultiset()"
          case MultisetDisjoint() => "MultisetDisjoint()"
          case Concat() => "++"
          case Passthrough(str) =>
              "passthrough_op<" + str + ">"
      }
  }


  function  mapElemToString(es : (Expression, Expression)) : string {
    "(" + expressionToString(es.0) + ", " + expressionToString(es.1) + ")"
  }
  function  contentElemToString(es : (VarName, Expression)) : string {
    "(" + es.0.dafny_name + ", " + expressionToString(es.1) + ")"
  }
  function  valueElemToString(es : (Formal, Expression)) : string {
    "(" + formalToString(es.0) + ", " + expressionToString(es.1) + ")"
  }


  function  expressionToString(expr: Expression) : string
  {
      match expr
      {
          case Literal(value) => literalToString(value)
            //   "Literal(value: " + literalToString(value) + ")"
          case Ident(name) => varNameToString(name)
            //   "Ident(name: " + nameToString(name) + ")"
          case Companion(idents, typeArgs) =>
                var idents := seq(|idents|, i requires 0 <= i < |idents| => identToString(idents[i]));
                var typeArgs := seq(|typeArgs|, i requires 0 <= i < |typeArgs| => typeToString(typeArgs[i]));
                strFlatten(idents, ".") 
                + if |typeArgs| > 0 
                    then "<" + strFlatten(typeArgs, ",") + ">"
                    else ""
            //   seqToStringInner(idents, identToString) + "<" 
            //   + seqToStringInner(typeArgs, typeToString) + ">"
            //   "Companion(idents: " + seqToString(idents, identToString) + 
            //   ", typeArgs: " + seqToString(typeArgs, typeToString) + ")"
          case Tuple(elements) =>
              var elementsStr := seq(|elements|, i requires 0 <= i < |elements| => expressionToString(elements[i]));
              "(" + strFlatten_inner(elementsStr, ",") + ")"
            //   var elementsStr := strFlatten_brackets(elementsStr, ",");
            //   "Tuple(elements: " + elementsStr + ")"
          case New(path, typeArgs, args) =>
              var pathStr := seq(|path|, i requires 0 <= i < |path| => identToString(path[i]));
              var typeArgsStr := seq(|typeArgs|, i requires 0 <= i < |typeArgs| => typeToString(typeArgs[i]));
              var argsStr := seq(|args|, i requires 0 <= i < |args| => expressionToString(args[i]));               
              "new " + strFlatten_inner(pathStr, ".") 
              + "<" + strFlatten_inner(typeArgsStr, ",") 
              + ">(" + strFlatten_inner(argsStr, ",") + ")"
            //   "New(path: " + strFlatten_brackets(pathStr, ",") + 
            //   ", typeArgs: " + strFlatten_brackets(typeArgsStr, ",") + 
            //   ", args: " + strFlatten_brackets(argsStr, ",") + ")"
          case NewUninitArray(dims, typ) =>
              var dims := seq(|dims|, i requires 0 <= i < |dims| => expressionToString(dims[i]));
              "NewUninitArray(dims: " + strFlatten_brackets(dims, ",") + 
              ", typ: " + typeToString(typ) + ")"
          case ArrayIndexToInt(value) =>
              "ArrayIndexToInt(value: " + expressionToString(value) + ")"
          case FinalizeNewArray(value, typ) =>
              "FinalizeNewArray(value: " + expressionToString(value) + 
              ", typ: " + typeToString(typ) + ")"
          case DatatypeValue(datatypeType, typeArgs, variant, isCo, contents) =>
              var typeArgsStr := seq(|typeArgs|, i requires 0 <= i < |typeArgs| => typeToString(typeArgs[i]));
              var contentsStr := seq(|contents|, i requires 0 <= i < |contents| => contentElemToString(contents[i]));
              resolvedTypeToString(datatypeType) + "<" 
              + strFlatten_inner(typeArgsStr, ",") + ">" 
              + "." + nameToString(variant) + "(" 
              + strFlatten_inner(contentsStr, ",") + ")"
            //   "DatatypeValue(datatypeType: " + resolvedTypeToString(datatypeType) + 
            //   ", typeArgs: " + strFlatten_brackets(typeArgsStr, ",") + 
            //   ", variant: " + nameToString(variant) + 
            //   ", isCo: " + boolToString(isCo) + 
            //   ", contents: " + strFlatten_brackets(contentsStr, ",") + ")"
          case Convert(value, from, typ) =>
              "(" + typeToString(typ) + ")" + expressionToString(value)
            //   "Convert(value: " + expressionToString(value) + 
            //   ", from: " + typeToString(from) + 
            //   ", typ: " + typeToString(typ) + ")"
          case SeqConstruct(length, elem) =>
              "SeqConstruct(length: " + expressionToString(length) + 
              ", elem: " + expressionToString(elem) + ")"
          case SeqValue(elements, typ) =>
              var elements := seq(|elements|, i requires 0 <= i < |elements| => expressionToString(elements[i]));
              var elements := strFlatten_brackets(elements, ",");
              "SeqValue(elements: " +elements + 
              ", typ: " + typeToString(typ) + ")"
          case SetValue(elements) =>
              var elements := seq(|elements|, i requires 0 <= i < |elements| => expressionToString(elements[i]));
              var elements := strFlatten_brackets(elements, ",");
              "SetValue(elements: " +elements + ")"
          case MultisetValue(elements) =>
              var elements := seq(|elements|, i requires 0 <= i < |elements| => expressionToString(elements[i]));
              var elements := strFlatten_brackets(elements, ",");
              "MultisetValue(elements: " +elements + ")"
          case MapValue(mapElems, _, _) =>
              var mapElems := seq(|mapElems|, i requires 0 <= i < |mapElems| => mapElemToString(mapElems[i]));
              var mapElems := strFlatten_brackets(mapElems, ",");
              "MapValue(mapElems: " + mapElems + ")"
          case MapBuilder(keyType, valueType) =>
              "MapBuilder(keyType: " + typeToString(keyType) + 
              ", valueType: " + typeToString(valueType) + ")"
          case SeqUpdate(expr, indexExpr, value, _, _) =>
              "SeqUpdate(expr: " + expressionToString(expr) +
              ", indexExpr: " + expressionToString(indexExpr) +
              ", value: " + expressionToString(value) + ")"
          case MapUpdate(expr, indexExpr, value, _, _) =>
              "MapUpdate(expr: " + expressionToString(expr) +
              ", indexExpr: " + expressionToString(indexExpr) + 
              ", value: " + expressionToString(value) + ")"
          case SetBuilder(elemType) =>
              "SetBuilder(elemType: " + typeToString(elemType) + ")"
          case ToMultiset(expr) =>
              "ToMultiset(expr: " + expressionToString(expr) + ")"
          case This() =>
              "this"
          case Ite(cond, thn, els) =>
              "if " + expressionToString(cond) + " then\n" 
              + indent(expressionToString(thn)) + "\nelse\n" + indent(expressionToString(els))
            //   "Ite(cond: " + expressionToString(cond) + 
            //   ", thn: " + expressionToString(thn) + 
            //   ", els: " + expressionToString(els) + ")"
          case UnOp(unOp, expr, format1) =>
              "(" + unaryOpToString(unOp) + expressionToString(expr) + ")"
            //   "UnOp(unOp: " + unaryOpToString(unOp) + 
            //   ", expr: " + expressionToString(expr) + 
            //   ", format1: " + unaryOpFormatToString(format1) + ")"
          case BinOp(op, left, right, format2) =>
             "(" + expressionToString(left) + " " + binOpToString(op.op) + " " + expressionToString(right) + ")"
            //   "BinOp(op: " + binOpToString(op) + 
            //   ", left: " + expressionToString(left) + 
            //   ", right: " + expressionToString(right) + 
            //   ", format2: " + binaryOpFormatToString(format2) + ")"
          case ArrayLen(expr, exprType, dim, native) =>
              "ArrayLen(expr: " + expressionToString(expr) + 
              ", exprType: " + typeToString(exprType) + 
              ", dim: " + natToString(dim) + 
              ", native: " + boolToString(native) + ")"
          case MapKeys(expr) =>
              "MapKeys(expr: " + expressionToString(expr) + ")"
          case MapValues(expr) =>
              "MapValues(expr: " + expressionToString(expr) + ")"
          case Select(expr, field, isConstant, onDatatype, fieldType) =>
              expressionToString(expr) + "." + varNameToString(field)
            //   "Select(expr: " + expressionToString(expr) + 
            //   ", field: " + nameToString(field) + 
            //   ", isConstant: " + boolToString(isConstant) + 
            //   ", onDatatype: " + boolToString(onDatatype) + 
            //   ", fieldType: " + typeToString(fieldType) + ")"
          case SelectFn(expr, field, onDatatype, isStatic, isConstant, arguments) =>
              expressionToString(expr) + "." + varNameToString(field)
            //   "SelectFn(expr: " + expressionToString(expr) + 
            //   ", field: " + nameToString(field) + 
            //   ", onDatatype: " + boolToString(onDatatype) + 
            //   ", isStatic: " + boolToString(isStatic) + 
            //   ", arity: " + natToString(arity) + ")"
          case Index(expr, collKind, indices) =>
              var indices := seq(|indices|, i requires 0 <= i < |indices| => expressionToString(indices[i]));
              expressionToString(expr) + "[" + strFlatten(indices, ",") + "]"
            //   "Index(expr: " + expressionToString(expr) + 
            //   ", collKind: " + collKindToString(collKind) + 
            //   ", indices: " + strFlatten_brackets(indices, ",") + ")"
          case IndexRange(expr, isArray, low, high) =>
              var low := match low
                  case None => "None"
                  case Some(low) => expressionToString(low);
              var high := match high
                  case None => "None"
                  case Some(high) => expressionToString(high);
              "IndexRange(expr: " + expressionToString(expr) + 
              ", isArray: " + boolToString(isArray) + 
              ", low: " + low + 
              ", high: " + high + ")"
          case TupleSelect(expr, index, fieldType) =>
              expressionToString(expr) + "." + natToString(index)
            //   "TupleSelect(expr: " + expressionToString(expr) + 
            //   ", index: " + natToString(index) + 
            //   ", fieldType: " + typeToString(fieldType) + ")"
          case Call(on, callName, typeArgs, args) =>
              var argsStrs := seq(|args|, i requires 0 <= i < |args| => expressionToString(args[i]));
              expressionToString(on) + "." + callNameToString(callName) + "<"
                + seqToStringInner(typeArgs, typeToString) + ">("
                + strFlatten_inner(argsStrs, ",") + ")"
            //   var args := seq(|args|, i requires 0 <= i < |args| => expressionToString(args[i]));
            //   var args := strFlatten_brackets(args, ",");
            //   "Call(on: " + expressionToString(on) + 
            //   ", callName: " + callNameToString(callName) + 
            //   ", typeArgs: " + seqToString(typeArgs, typeToString) + 
            //   ", args: " + args + ")"
          case Lambda(params, retType, body) =>
              var params := seq(|params|, i requires 0 <= i < |params| => formalToString(params[i]));
              var params := strFlatten_brackets(params, ",");
              var body := seq(|body|, i requires 0 <= i < |body| => statementToString(body[i]));
              var body := strFlatten_brackets(body, ",");
              "Lambda(params: " +params + 
              ", retType: " + typeToString(retType) + 
              ", body: " + body + ")"
          case BetaRedex(values, retType, expr) =>
              var values := seq(|values|, i requires 0 <= i < |values| => valueElemToString(values[i]));
              var values := strFlatten_brackets(values, ",");
              "BetaRedex(values: " + values + 
              ", retType: " + typeToString(retType) + 
              ", expr: " + expressionToString(expr) + ")"
          case IIFE(ident, typ, value, iifeBody) =>
              "IIFE(ident: " + varNameToString(ident) +
              ", typ: " + typeToString(typ) + 
              ", value: " + expressionToString(value) + 
              ", iifeBody: " + expressionToString(iifeBody) + ")"
          case Apply(expr, args) =>
              var args := seq(|args|, i requires 0 <= i < |args| => expressionToString(args[i]));
              var args := strFlatten_brackets(args, ",");
              "Apply(expr: " + expressionToString(expr) + 
              ", args: " + args + ")"
          case TypeTest(on, dType, variant) =>
              "TypeTest(on: " + expressionToString(on) + 
              ", dType: " + seqToString(dType, identToString) + 
              ", variant: " + nameToString(variant) + ")"
          case InitializationValue(typ) =>
              "InitializationValue(typ: " + typeToString(typ) + ")"
          case BoolBoundedPool() =>
              "BoolBoundedPool()"
          case SetBoundedPool(of) =>
              "SetBoundedPool(of: " + expressionToString(of) + ")"
          case MapBoundedPool(of) =>
              "MapBoundedPool(of: " + expressionToString(of) + ")"
          case SeqBoundedPool(of, includeDuplicates) =>
              "SeqBoundedPool(of: " + expressionToString(of) + 
              ", includeDuplicates: " + boolToString(includeDuplicates) + ")"
          case IntRange(_, lo, hi, up) =>
              "IntRange(lo: " + expressionToString(lo) +
              ", hi: " + expressionToString(hi) + 
              ", up: " + boolToString(up) + ")"
          case UnboundedIntRange(start, up) =>
              "UnboundedIntRange(start: " + expressionToString(start) + 
              ", up: " + boolToString(up) + ")"
          case Quantifier(elemType, collection, is_forall, lambda) =>
              "Quantifier(elemType: " + typeToString(elemType) + 
              ", collection: " + expressionToString(collection) + 
              ", is_forall: " + boolToString(is_forall) + 
              ", lambda: " + expressionToString(lambda) + ")"
      }
  }


  function  unaryOpFormatToString(format: UnaryOpFormat) : string
  {
      match format
      {
          case NoFormat => "NoFormat"
          case CombineFormat => "CombineFormat"
      }
  }
  function  binaryOpFormatToString(format: BinaryOpFormat) : string
  {
      match format
      {
          case NoFormat => "NoFormat"
          case ImpliesFormat => "ImpliesFormat"
          case EquivalenceFormat => "EquivalenceFormat"
          case ReverseFormat => "ReverseFormat"
      }
  }


    
  function  unaryOpToString(op: UnaryOp) : string
  {
      match op
      {
          case Not => "Not"
          case BitwiseNot => "BitwiseNot"
          case Cardinality => "Cardinality"
      }
  }

  function  literalToString(lit: Literal) : string
  {
      match lit
      {
          case BoolLiteral(value) => boolToString(value)
            //   "BoolLiteral(value: " + boolToString(value) + ")"
          case IntLiteral(value, typ) => value 
            //   "IntLiteral(value: " + value + ", type: " + typeToString(typ) + ")"
          case DecLiteral(intPart, fracPart, typ) =>
              "DecLiteral(intPart: " + intPart + ", fracPart: " + fracPart + ", type: " + typeToString(typ) + ")"
          case StringLiteral(value, verbatim) =>
              "StringLiteral(value: " + value + ", verbatim: " + boolToString(verbatim) + ")"
          case CharLiteral(value) =>
              "CharLiteral(value: " + [value] + ")"
          case CharLiteralUTF16(value) =>
              "CharLiteralUTF16(value: " + "??" + ")"
          case Null(typ) =>
              "Null<" + typeToString(typ) + ">"
      }
  }


}

