/* this pass eliminates all the "Dafny" nodes from the lucid AST */
/* Nodes: 
    TDafnyGenerateCmd
    DafnyDiv
    DafnyMod
    EDafnyThis
    EDafnyGenerateCmd
    DafnyCall
    DafnyDeclare
    DDafnyMethod
*/

include "LAST.dfy"
include "PPrintAst.dfy"

module LucidCollector {
    import opened LAST
    import opened Std.Wrappers

    datatype AstNode = 
        | IdNode(id)
        | ValNode(val)
        | TyNode(ty)
        | ExpNode(exp)
        | StmtNode(stmt)
        | DeclNode(decl)
    
    function astNodeStr(n : AstNode) : string {
        match n {
            case IdNode(id) => id
            case ValNode(v) => LAST.valStr(v)
            case TyNode(ty) => LAST.tyStr(ty)
            case ExpNode(e) => LAST.expStr(e)
            case StmtNode(s) => LAST.stmtStr(s)
            case DeclNode(d) => LAST.declStr(d)
        }
    }

    // at every AST node, 
    // apply a function that maps the 
    // node wrapped in an Arg to a 
    // sequence of 't' values.
    type F<!t> = AstNode -> seq<t>

    method visitId<t>(id: id, f:F<t>) returns (rv : seq<t>) {
        rv := f(IdNode(id));
    }
    method visitTy<t>(ty: ty, f:F<t>) returns (rv : seq<t>) {
        rv := f(TyNode(ty));
    }
    method visitParam<t>(param: param, f:F<t>) returns (rv : seq<t>) {
        var id := param.0;
        var ty := param.1;
        var rvId := visitId(id, f);
        var rvTy := visitTy(ty, f);
        rv := rvId + rvTy;
    }
    method visitVal<t>(val: val, f:F<t>) returns (rv : seq<t>) {
        rv := f(ValNode(val));
    }
    method visitExp<t>(exp: exp, f:F<t>) returns (rv : seq<t>) {
        match exp {
            case EVar(id) => {
                var rvId := visitId(id, f);
                rv := rvId;
            }
            case EVal(val) => {
                var rvVal := visitVal(val, f);
                rv := rvVal;
            }
            case ECall(id, args) => {
                var rvId := visitId(id, f);
                var rvArgs := [];
                for i := 0 to |args| {
                    var rvArg := visitExp(args[i], f);
                    rvArgs := rvArgs + rvArg;
                }
                rv := rvId + rvArgs;
            }
            case EEvent(id, args) => {
                var rvId := visitId(id, f);
                var rvArgs := [];
                for i := 0 to |args| {
                    var rvArg := visitExp(args[i], f);
                    rvArgs := rvArgs + rvArg;
                }
                rv := rvId + rvArgs;
            }
            case EHash(width, args) => {
                var rvArgs := [];
                for i := 0 to |args| {
                    var rvArg := visitExp(args[i], f);
                    rvArgs := rvArgs + rvArg;
                }
                rv := rvArgs;
            }
            case EProject(record, field) => {
                var rvRecord := visitExp(record, f);
                var rvField := visitId(field, f);
                rv := rvRecord + rvField;
            }
            case ERecord(fields) => {
                rv := [];
                for i := 0 to |fields| {
                    var rvId := visitId(fields[i].0, f);
                    var rvExp := visitExp(fields[i].1, f);
                    rv := rv + rvId + rvExp;
                }
            }
            case EIndex(vec, idx) => {
                var rvVec := visitExp(vec, f);
                var rvIdx := visitExp(idx, f);
                rv := rvVec + rvIdx;
            }
            case EComp(body, ivar, bound) => {
                var rvBody := visitExp(body, f);
                var rvIvar := visitId(ivar, f);
                rv := rvBody + rvIvar;
            }
            case EVecLit(elems) => {
                rv := [];
                for i := 0 to |elems| {
                    var rvElem := visitExp(elems[i], f);
                    rv := rv + rvElem;
                }
            }
            case EOp(op, args) => {
                var rvArgs := [];
                for i := 0 to |args| {
                    var rvArg := visitExp(args[i], f);
                    rvArgs := rvArgs + rvArg;
                }
                rv := rvArgs;
            }
            case EDafnyGenerateCmd(doit, e) => {
                var rvDoit := visitExp(doit, f);
                var rvE := visitExp(e, f);
                rv := rvDoit + rvE;
            }
        }
        var rvOuter := f(ExpNode(exp));
        rv := rv + rvOuter;
        // if (|rv| > 0) {
        //     print("[visitExp] there is more")
        // }
    }

    method visitStmt<t>(stmt: stmt, f:F<t>) returns (rv : seq<t>) {
        match stmt {
            case SNoop => {
                rv := [];
            }
            case SIf(e, strue, sfalse) => {
                var rvE := visitExp(e, f);
                var rvStrue := [];
                for i := 0 to |strue| {
                    var rvStmt := visitStmt(strue[i], f);
                    rvStrue := rvStrue + rvStmt;
                }
                var rvSfalse := [];
                for i := 0 to |sfalse| {
                    var rvStmt := visitStmt(sfalse[i], f);
                    rvSfalse := rvSfalse + rvStmt;
                }
                rv := rvE + rvStrue + rvSfalse;
            }
            case SLocal(id, ty, e) => {
                var rvId := visitId(id, f);
                var rvTy := visitTy(ty, f);
                var rvE := visitExp(e, f);
                rv := rvId + rvTy + rvE;
            }
            case SAssign(id, e) => {
                var rvId := visitId(id, f);
                var rvE := visitExp(e, f);
                rv := rvId + rvE;
            }
            case SUnit(e) => {
                var rvE := visitExp(e, f);
                rv := rvE;
            }
            case SRet(None) => {
                rv := [];
            }
            case SRet(Some(e)) => {
                var rvE := visitExp(e, f);
                rv := rvE;
            }
            case SGenerate(e) => {
                var rvE := visitExp(e, f);
                rv := rvE;
            }
            case SGeneratePort(port, e) => {
                var rvPort := visitExp(port, f);
                var rvE := visitExp(e, f);
                rv := rvPort + rvE;
            }
            case SGeneratePorts(ports, e) => {
                var rvPorts := visitExp(ports, f);
                var rvE := visitExp(e, f);
                rv := rvPorts + rvE;
            }
            case SFor(ivar, bound, body) => {
                var rvIvar := visitId(ivar, f);
                var rvBody := [];
                for i := 0 to |body| {
                    var rvStmt := visitStmt(body[i], f);
                    rvBody := rvBody + rvStmt;
                }
                rv := rvIvar + rvBody;
            }
            case SPrint(s) => {
                rv := [];
            }
            case SComment(s) => {
                rv := [];
            }
            case DafnyCall(id, args, outs) => {
                var rvId := visitId(id, f);
                var rvArgs := [];
                for i := 0 to |args| {
                    var rvArg := visitExp(args[i], f);
                    rvArgs := rvArgs + rvArg;
                }
                var rvOuts := [];
                for i := 0 to |outs| {
                    var rvOut := visitId(outs[i], f);
                    rvOuts := rvOuts + rvOut;
                }
                rv := rvId + rvArgs + rvOuts;
            }
            case DafnyDeclare(id, ty) => {
                var rvId := visitId(id, f);
                var rvTy := visitTy(ty, f);
                rv := rvId + rvTy;
            }
        }

        var rvStmt := f(StmtNode(stmt));
        rv := rv + rvStmt;
    }

    method visitDecl<t>(decl: decl, f:F<t>) returns (rv : seq<t>) {
        match decl {
            case DEvent(id, params) => {
                var rvId := visitId(id, f);
                var rvParams := [];
                for i := 0 to |params| {
                    var rvParam := visitParam(params[i], f);
                    rvParams := rvParams + rvParam;
                }
                rv := rvId + rvParams;
            }
            case DGlobal(id, ty, ctor) => {
                var rvId := visitId(id, f);
                var rvTy := visitTy(ty, f);
                var rvCtor := visitExp(ctor, f);
                rv := rvId + rvTy + rvCtor;
            }
            case DComment(s) => {
                rv := [];
            }
            case DRaw(s) => {
                rv := [];
            }
            case DDafnyFieldOrder(_) => {
                rv := [];
            }
            case DDafnyMethod(id, rtys, params, body, outvars) => {
                var rvId := visitId(id, f);
                var rvRtys := [];
                for i := 0 to |rtys| {
                    var rvTy := visitTy(rtys[i], f);
                    rvRtys := rvRtys + rvTy;
                }
                var rvParams := [];
                for i := 0 to |params| {
                    var rvParam := visitParam(params[i], f);
                    rvParams := rvParams + rvParam;
                }
                var rvBody := [];
                for i := 0 to |body| {
                    var rvStmt := visitStmt(body[i], f);
                    rvBody := rvBody + rvStmt;
                }
                var rvOutvars := [];
                for i := 0 to |outvars| {
                    var rvOutvar := visitId(outvars[i], f);
                    rvOutvars := rvOutvars + rvOutvar;
                }
                rv := rvId + rvRtys + rvParams + rvBody + rvOutvars;
            }
            case DConst(id, ty, v) => {
                var rvId := visitId(id, f);
                var rvTy := visitTy(ty, f);
                var rvVal := visitExp(v, f);
                rv := rvId + rvTy + rvVal;
            }
            case DSymbolic(id, ty) => {
                var rvId := visitId(id, f);
                var rvTy := visitTy(ty, f);
                rv := rvId + rvTy;
            }
            case DHandler(id, params, body) => {
                var rvId := visitId(id, f);
                var rvParams := [];
                for i := 0 to |params| {
                    var rvParam := visitParam(params[i], f);
                    rvParams := rvParams + rvParam;
                }
                var rvBody := [];
                for i := 0 to |body| {
                    var rvStmt := visitStmt(body[i], f);
                    rvBody := rvBody + rvStmt;
                }
                rv := rvId + rvParams + rvBody;
            }
            case DFunction(id, rty, params, body) => {
                var rvId := visitId(id, f);
                var rvRty := visitTy(rty, f);
                var rvParams := [];
                for i := 0 to |params| {
                    var rvParam := visitParam(params[i], f);
                    rvParams := rvParams + rvParam;
                }
                var rvBody := [];
                for i := 0 to |body| {
                    var rvStmt := visitStmt(body[i], f);
                    rvBody := rvBody + rvStmt;
                }
                rv := rvId + rvRty + rvParams + rvBody;
            }
            case DMemop(id, rty, params, body) => {
                var rvId := visitId(id, f);
                var rvRty := visitTy(rty, f);
                var rvParams := [];
                for i := 0 to |params| {
                    var rvParam := visitParam(params[i], f);
                    rvParams := rvParams + rvParam;
                }
                var rvBody := [];
                for i := 0 to |body| {
                    var rvStmt := visitStmt(body[i], f);
                    rvBody := rvBody + rvStmt;
                }
                rv := rvId + rvRty + rvParams + rvBody;
            }
            case DRecord(id, fields) => {
                var rvId := visitId(id, f);
                var rvFields := [];
                for i := 0 to |fields| {
                    var rvField := visitParam(fields[i], f);
                    rvFields := rvFields + rvField;
                }
                rv := rvId + rvFields;
            }
            case DModule(id, members) => {
                var rvId := visitId(id, f);
                var rvMembers := [];
                for i := 0 to |members| {
                    var rvMember := visitDecl(members[i], f);
                    rvMembers := rvMembers + rvMember;
                }
                rv := rvId + rvMembers;
            }
            case DConstr(rty, name, params, inits) => {
                var rvRty := visitId(rty, f);
                var rvName := visitId(name, f);
                var rvParams := [];
                for i := 0 to |params| {
                    var rvParam := visitParam(params[i], f);
                    rvParams := rvParams + rvParam;
                }
                var rvInits := [];
                for i := 0 to |inits| {
                    var rvFid := visitId(inits[i].0, f);
                    var rvExp := visitExp(inits[i].1, f);
                    rvInits := rvInits + rvFid + rvExp;
                }
                rv := rvRty + rvName + rvParams + rvInits;
            }
        }

        var rvDecl := f(DeclNode(decl));
        rv := rv + rvDecl;
    }

    method visitDecls<t>(ds : seq<decl>, f:F<t>) returns (rv : seq<t>) {
        var rv_list := [];
        for i := 0 to |ds| {
            var acc := visitDecl(ds[i], f);
            rv_list := rv_list + acc;
        }
        rv := rv_list;
    }
}



module LucidMapper {
    import opened LAST
    import opened Std.Wrappers


    datatype F = 
        | UpdateId(id -> id)
        | UpdateTy(ty -> ty)
        | UpdateParam(param -> param)
        | UpdateVal(val -> val)
        | UpdateOp(op -> op)
        | UpdateExp(exp -> exp)
        | UpdateStmt(stmt -> stmt)
        | UpdateStmts(seq<stmt> -> seq<stmt>) // applied to each straight-line block
        | UpdateDecl(decl -> decl)

    method visitId(id: id, f : F) returns (rv: id) {
        match f {
            case UpdateId(g) => {rv:= g(id);}
            case _ => {rv:= id;}
        }
    }

    method visitTy(ty: ty, f : F) returns (rv: ty) {
        var newTy := ty;
        match ty {
            case TGlobal(id, sizes) => {
                var newId := visitId(id, f);
                newTy :=TGlobal(newId, sizes);}
            case TVec(elem, len) => {
                var newElem := visitTy(elem, f);
                newTy := TVec(newElem, len);}
            case _ => {}
        }
        match f {
            case UpdateTy(g) => {rv:= g(newTy);}
            case _ => {rv:= newTy;}
        }
    }

    method visitParam(param: param, f : F) returns (rv: param) {
        // recurse on param components first (id, ty)
        var newId := visitId(param.0, f);
        var newTy := visitTy(param.1, f);
        match f {
            case UpdateParam(g) => {rv:= g((newId, newTy));}
            case _ => {rv:= (newId, newTy);}
        }
    }

    method visitVal(val: val, f : F) returns (rv: val) {
        match f {
            case UpdateVal(g) => {rv:= g(val);}
            case _ => {rv:= val;}
        }
    }
    method visitOp(op: op, f : F) returns (rv: op) {
        match f {
            case UpdateOp(g) => {rv:= g(op);}
            case _ => {rv:= op;}
        }
    }
    method visitExp(exp: exp, f : F) returns (rv: exp) {
        // visit inner, then apply f
        match exp {
            case EVar(id) => {
                var newId := visitId(id, f);
                rv:= EVar(newId);
            }
            case EVal(val) => {
                var newVal := visitVal(val, f);
                rv:= EVal(newVal);
            }
            case ECall(id, args) => {
                var newId := visitId(id, f);
                var newArgs := [];
                for i := 0 to |args| {
                    var  newArg := visitExp(args[i], f);
                    newArgs := newArgs + [newArg];
                }
                rv:= ECall(newId, newArgs);
            }
            case EEvent(id, args) => {
                var newId := visitId(id, f);
                var newArgs := [];
                for i := 0 to |args| {
                    var  newArg := visitExp(args[i], f);
                    newArgs := newArgs + [newArg];
                }
                rv:= EEvent(newId, newArgs);
            }
            case EHash(width, args) => {
                var newArgs := [];
                for i := 0 to |args| {
                    var  newArg := visitExp(args[i], f);
                    newArgs := newArgs + [newArg];
                }
                rv:= EHash(width, newArgs);
            }
            case EProject(record, field) => {
                var newRecord := visitExp(record, f);
                var newField := visitId(field, f);
                rv:= EProject(newRecord, newField);
            }
            case ERecord(fields) => {
                var newFields := [];
                for i := 0 to |fields| {
                    var newId := visitId(fields[i].0, f);
                    var newExp := visitExp(fields[i].1, f);
                    newFields := newFields + [(newId, newExp)];
                }
                rv:= ERecord(newFields);
            }
            case EIndex(vec, idx) => {
                var newVec := visitExp(vec, f);
                var newIdx := visitExp(idx, f);
                rv:= EIndex(newVec, newIdx);
            }
            case EComp(body, ivar, bound) => {
                var newBody := visitExp(body, f);
                var newIvar := visitId(ivar, f);
                rv:= EComp(newBody, newIvar, bound);
            }
            case EVecLit(elems) => {
                var newElems := [];
                for i := 0 to |elems| {
                    var newElem := visitExp(elems[i], f);
                    newElems := newElems + [newElem];
                }
                rv:= EVecLit(newElems);
            }
            case EOp(op, args) => {
                var newOp := visitOp(op, f);
                var newArgs := [];
                for i := 0 to |args| {
                    var  newArg := visitExp(args[i], f);
                    newArgs := newArgs + [newArg];
                }
                rv:= EOp(newOp, newArgs);
            }
            case EDafnyGenerateCmd(doit, e) => {
                var newDoit := visitExp(doit, f);
                var newE := visitExp(e, f);
                rv:= EDafnyGenerateCmd(newDoit, newE);
            }
        }
        match f {
            case UpdateExp(g) => {rv:= g(rv);}
            case _ => {}
        }
    }

  
    method visitStmt(stmt:stmt, f:F) returns (rv : stmt) {
        match stmt {
            case SNoop => {
                rv:= SNoop;
            }
            case SIf(e, strue, sfalse) => {
                var newE := visitExp(e, f);
                var newStrue := visitStmts(strue, f);
                var newSfalse := visitStmts(sfalse, f);
                rv:= SIf(newE, newStrue, newSfalse);
            }
            case SLocal(id, ty, e) => {
                var newId := visitId(id, f);
                var newTy := visitTy(ty, f);
                var newE := visitExp(e, f);
                rv:= SLocal(newId, newTy, newE);
            }
            case SAssign(id, e) => {
                var newId := visitId(id, f);
                var newE := visitExp(e, f);
                rv:= SAssign(newId, newE);
            }
            case SUnit(exp) => {
                var newExp := visitExp(exp, f);
                rv:= SUnit(newExp);
            }
            case SRet(None) => {
                rv:= SRet(None);
            }
            case SRet(Some(e)) => {
                var newE := visitExp(e, f);
                rv:= SRet(Some(newE));
            }
            case SGenerate(e) => {
                var newE := visitExp(e, f);
                rv:= SGenerate(newE);
            }
            case SGeneratePort(port, e) => {
                var newPort := visitExp(port, f);
                var newE := visitExp(e, f);
                rv:= SGeneratePort(newPort, newE);
            }
            case SGeneratePorts(ports, e) => {
                var newPorts := visitExp(ports, f);
                var newE := visitExp(e, f);
                rv:= SGeneratePorts(newPorts, newE);
            }
            case SFor(ivar, bound, body) => {
                var newIvar := visitId(ivar, f);
                var newBody := [];
                for i := 0 to |body| {
                    var newStmt := visitStmt(body[i], f);
                    newBody := newBody + [newStmt];
                }
                rv:= SFor(newIvar, bound, newBody);
            }
            case SPrint(s) => {
                rv:= SPrint(s);
            }
            case SComment(s) => {
                rv:= SComment(s);
            }
            case DafnyCall(id, args, outs) => {
                var newId := visitId(id, f);
                var newArgs := [];
                for i := 0 to |args| {
                    var newArg := visitExp(args[i], f);
                    newArgs := newArgs + [newArg];
                }
                var newOuts := [];
                for i := 0 to |outs| {
                    var newOut := visitId(outs[i], f);
                    newOuts := newOuts + [newOut];
                }
                rv:= DafnyCall(newId, newArgs, newOuts);
            }
            case DafnyDeclare(id, ty) => {
                var newId := visitId(id, f);
                var newTy := visitTy(ty, f);
                rv:= DafnyDeclare(newId, newTy);
            }
        }
        match f {
            case UpdateStmt(g) => {rv:= g(rv);}
            case _ => {}
        }
    }

    // Visit each statement in a straight-line block, then apply an UpdateStmts
    // block transform (if any) to the whole block. Used for method bodies and
    // if-branches so a block-level rewrite reaches every nesting level.
    method visitStmts(stmts:seq<stmt>, f:F) returns (rv:seq<stmt>) {
        rv := [];
        for i := 0 to |stmts| {
            var s := visitStmt(stmts[i], f);
            rv := rv + [s];
        }
        match f {
            case UpdateStmts(g) => {rv:= g(rv);}
            case _ => {}
        }
    }

    method visitDecl(decl:decl, f:F) returns (rv:decl) {
        match decl {
            case DEvent(id, params) => {
                var newId := visitId(id, f);
                var newParams := [];
                for i := 0 to |params| {
                    var newParam := visitParam(params[i], f);
                    newParams := newParams + [newParam];
                }
                rv:= DEvent(newId, newParams);
            }
            case DGlobal(id, ty, ctor) => {
                var newId := visitId(id, f);
                var newTy := visitTy(ty, f);
                var newCtor := visitExp(ctor, f);
                rv:= DGlobal(newId, newTy, newCtor);
            }
            case DComment(s) => {
                rv:= DComment(s);
            }
            case DRaw(s) => {
                rv:= DRaw(s);
            }
            case DDafnyFieldOrder(fs) => {
                rv:= DDafnyFieldOrder(fs);
            }
            case DDafnyMethod(id, rtys, params, body, outvars) => {
                var newId := visitId(id, f);
                var newRtys := [];
                for i := 0 to |rtys| {
                    var newTy := visitTy(rtys[i], f);
                    newRtys := newRtys + [newTy];
                }
                var newParams := [];
                for i := 0 to |params| {
                    var newParam := visitParam(params[i], f);
                    newParams := newParams + [newParam];
                }
                var newBody := visitStmts(body, f);
                var newOutvars := [];
                for i := 0 to |outvars| {
                    var newOutvar := visitId(outvars[i], f);
                    newOutvars := newOutvars + [newOutvar];
                }
                rv:= DDafnyMethod(newId, newRtys, newParams, newBody, newOutvars);
            }
            case DConst(id, ty, v) => {
                var newId := visitId(id, f);
                var newTy := visitTy(ty, f);
                var newVal := visitExp(v, f);
                rv:= DConst(newId, newTy, newVal);
            }
            case DSymbolic(id, ty) => {
                var newId := visitId(id, f);
                var newTy := visitTy(ty, f);
                rv:= DSymbolic(newId, newTy);
            }
            case DHandler(id, params, body) => {
                var newId := visitId(id, f);
                var newParams := [];
                for i := 0 to |params| {
                    var newParam := visitParam(params[i], f);
                    newParams := newParams + [newParam];
                }
                var newBody := visitStmts(body, f);
                rv:= DHandler(newId, newParams, newBody);
            }
            case DFunction(id, rty, params, body) => {
                var newId := visitId(id, f);
                var newRty := visitTy(rty, f);
                var newParams := [];
                for i := 0 to |params| {
                    var newParam := visitParam(params[i], f);
                    newParams := newParams + [newParam];
                }
                var newBody := visitStmts(body, f);
                rv:= DFunction(newId, newRty, newParams, newBody);
            }
            case DMemop(id, rty, params, body) => {
                var newId := visitId(id, f);
                var newRty := visitTy(rty, f);
                var newParams := [];
                for i := 0 to |params| {
                    var newParam := visitParam(params[i], f);
                    newParams := newParams + [newParam];
                }
                var newBody := visitStmts(body, f);
                rv:= DMemop(newId, newRty, newParams, newBody);
            }
            case DRecord(id, fields) => {
                var newId := visitId(id, f);
                var newFields := [];
                for i := 0 to |fields| {
                    var newField := visitParam(fields[i], f);
                    newFields := newFields + [newField];
                }
                rv:= DRecord(newId, newFields);
            }
            case DModule(id, members) => {
                var newId := visitId(id, f);
                var newMembers := [];
                for i := 0 to |members| {
                    var newMember := visitDecl(members[i], f);
                    newMembers := newMembers + [newMember];
                }
                rv:= DModule(newId, newMembers);
            }
            case DConstr(rty, name, params, inits) => {
                var newRty := visitId(rty, f);
                var newName := visitId(name, f);
                var newParams := [];
                for i := 0 to |params| {
                    var newParam := visitParam(params[i], f);
                    newParams := newParams + [newParam];
                }
                var newInits := [];
                for i := 0 to |inits| {
                    var newFid := visitId(inits[i].0, f);
                    var newExp := visitExp(inits[i].1, f);
                    newInits := newInits + [(newFid, newExp)];
                }
                rv:= DConstr(newRty, newName, newParams, newInits);
            }
        }
        match f {
            case UpdateDecl(g) => {rv:= g(rv);}
            case _ => {}
        }
    }
    method visitDecls(ds : seq<decl>, f : F) returns (rv : seq<decl>) {
        rv := [];
        for i:=0 to |ds| {
            var d := visitDecl(ds[i], f);
            rv := rv + [d];
        }
    }

}





module Normalizer {
    import opened LAST
    import opened Std.Wrappers
    import opened LucidCollector
    import LucidMapper
    import opened NatPrinter
    import opened Std.Arithmetic.Logarithm


    /***** helpers ******/
    const charToUpper := map [
        'a' := 'A',
        'b' := 'B',
        'c' := 'C',
        'd' := 'D',
        'e' := 'E',
        'f' := 'F',
        'g' := 'G',
        'h' := 'H',
        'i' := 'I',
        'j' := 'J',
        'k' := 'K',
        'l' := 'L',
        'm' := 'M',
        'n' := 'N',
        'o' := 'O',
        'p' := 'P',
        'q' := 'Q',
        'r' := 'R',
        's' := 'S',
        't' := 'T',
        'u' := 'U',
        'v' := 'V',
        'w' := 'W',
        'x' := 'X',
        'y' := 'Y',
        'z' := 'Z'
    ]

    function capitalize(s : string) : string {
        if |s| > 0 && (s[0] in charToUpper) 
            then [charToUpper[s[0]]] + s[1..]
            else s
    }

    function eval_exp(exp:exp) : val {
        match exp {
            case EVal(VInt(intstr, sz)) => VInt(intstr, sz)
            case EVal(VBool(b)) => VBool(b)
            case _ => VInvalid("not int or bool")
        }
    }
    function defaultTyVal(ty : ty) : val {
        match ty {
            case TBool => VBool(false)
            case TInt(sz) => VInt("0", sz)
            case _ => VInvalid("defaultTyVal: no default value for " + LAST.tyStr(ty))
        }
    }



    function getEventId (node : AstNode) : seq<id> {
        match node {
            case DeclNode(DEvent(id, _)) => [id]
            case _ => []
        }
    }
    method getEventIds(decls : seq<decl>) returns (rv_set : set<id>) {
        var rv : seq<id> := [];
        rv_set := {};
        for i := 0 to |decls| {
            var accEventIds := getEventId(DeclNode(decls[i]));
            rv := rv + accEventIds;
        }
        for i := 0 to |rv| {
            rv_set := rv_set + {rv[i]};
        }
    }


    // get the names of all the variables used in EVars in the program
    function getVarId(node : AstNode) : seq<id> {
        match node {
            case ExpNode(EVar(id)) => [id]
            case _ => []
        }
    }
    method getVarIds(ds : seq<decl>) returns (rv : set<id>) {
        var rv_list := [];
        for i := 0 to |ds| {
            var accIds := LucidCollector.visitDecl(ds[i], getVarId);
            rv_list := rv_list + accIds;
        }
        rv := {};
        for i := 0 to |rv_list| {
            // print ("getVarIds: " + rv_list[i] + "\n");
            rv := rv + {rv_list[i]};
        }
    }

    // find all the calls to Array methods and 
    // extract the ids of the memop function arguments. 
    function getMemopEvar(node : AstNode) : (seq<exp>) {
        match node {
            case ExpNode(exp) => 
                match exp {
                    case EVar(id) => ([])
                    case ECall(fcnid, args) => 
                        if fcnid == "ArrayMemops.Get" && |args| == 4 then [args[2]]
                        else if fcnid == "ArrayMemops.Set" && |args| == 4 then [args[2]]
                        else if fcnid == "ArrayMemops.GetSet" && |args| == 6 then [args[2], args[4]]
                        else []
                    case _ => []
                }
            case _ => []
        }
    }
    
    method getMemopIds(ds : seq<decl>) returns (rv : set<id>) {
        var exps := LucidCollector.visitDecls(ds, getMemopEvar);
        rv := {};
        for i := 0 to |exps| {
            match exps[i] {
                case EVar(id) => {
                    // print("getMemopArgs: found memop var = " + id + "\n");
                    rv := rv + {id};
                }
                case _ => {
                    print("getMemopArgs: expected EVar, got " + LAST.expStr(exps[i]) + "\n");
                }
            }
        }
    }

    class GenerateCmdEliminator {
        // first, we have to get the ids of all the variables that are
        // declared with type TDafnyGenerateCmd, so that we can 
        // delete them wherever they appear. 
        constructor () {}

        function getGenerateCmdVar(node : AstNode) : seq<id> {
            match node {
                case StmtNode(DafnyDeclare(id, TDafnyGenerateCmd)) => [id]
                case _ => []
            }
        }
        method getGenerateCmdVars(ds : seq<decl>) returns (generateCmdVars : set<id>)
        {
            generateCmdVars := {};
            var accIds := LucidCollector.visitDecls(ds, getGenerateCmdVar);
            for i := 0 to |accIds| {
                generateCmdVars := generateCmdVars + {accIds[i]};
            }
        }


        function skipGenerateCmdVars(generatevars : set<id>, ids : seq<id>) : seq<id> 
        {
            if |ids| == 0 then []
            else if ids[0] in generatevars then skipGenerateCmdVars(generatevars, ids[1..])
            else [ids[0]] + skipGenerateCmdVars(generatevars, ids[1..])
        }

        /*
            - Values:
                1. a statement with EDafnyGenerateCmd(true, e) is replaced with a generate statement
                2. a statement with rhs of EDafnyGenerateCmd(false, ...) is replaced with a no-op
            - Variables: 
                3. a variable declaration of type TDafnyGenerateCmd gets replaced with a no-op
                4. an assignment to a variable of type TDafnyGenerateCmd gets replaced with a no-op
                5. a return statement with a variable of type TDafnyGenerateCmd gets replaced with a no-op
                6. a DafnyCall with a return variable of type TDafnyGenerateCmd gets its return variable deleted
        */
        function mkReplaceGenerateCmd(generatevars : set<id>) : stmt -> stmt {
            (s : stmt) => 
                match s {
                    case DafnyDeclare(_, TDafnyGenerateCmd) => SNoop // (3)
                    case SAssign(_, exp) => 
                        match exp {
                            case EDafnyGenerateCmd(doit, ev) => 
                                match eval_exp(doit) {
                                    case VBool(true) => SGenerate(ev) // (1)
                                    case VBool(false) => SNoop // (2)
                                    case _ => s // error case -- leave the command expr for the wellformed checker
                                }
                            case EVar(id) => 
                                if id in generatevars then SNoop // (4)
                                else s
                            case _ => s // unrelated expression
                        }
                    case SRet(Some(exp)) => 
                        match exp {
                            case EDafnyGenerateCmd(doit, ev) => 
                                match eval_exp(doit) {
                                    case VBool(true) => SGenerate(ev) // (1)
                                    case VBool(false) => SNoop // (2)
                                    case _ => s // error case
                                }
                            case EVar(id) =>
                                if id in generatevars then SNoop // (5)
                                else s // unrelated expression
                            case _ => s // unrelated expression
                        }
                    case DafnyCall(id, args, outs) => 
                        var newOuts := skipGenerateCmdVars(generatevars, outs);
                        DafnyCall(id, args, newOuts) // (6)
                    case _ => s            
            }
        }

        function delete_generate_args(rtys : seq<ty>, ids : seq<id>) : (seq<ty>, seq<id>) {
            if |ids| == 0 then
                if |rtys| == 0 then ([], [])
                else
                    var rest := delete_generate_args(rtys[1..], ids);
                    if rtys[0] == TDafnyGenerateCmd 
                        then rest
                        else (([rtys[0]] + rest.0), rest.1)
            else // |ids| > 0
                if |rtys| == 0 then ([], [])
                else
                    var rest := delete_generate_args(rtys[1..], ids[1..]);
                    if rtys[0] == TDafnyGenerateCmd 
                        then rest
                        else (([rtys[0]] + rest.0),([ids[0]] + rest.1))                
        }

        // - a return variable of type TDafnyGenerateCmd gets deleted
        function deleteGenerateParams(d : decl) : decl 
        {
            match d {
                case DDafnyMethod(id, rtys, params, body, outvars) => 
                    var (new_rtys, new_outvars) := delete_generate_args(rtys, outvars);
                    DDafnyMethod(id, new_rtys, params, body, new_outvars)
                case _ => d            
            }
        }

        method process(ds : seq<decl>) returns (ds_out : seq<decl>) 
        modifies this
        {
            var cmdvars := getGenerateCmdVars(ds);
            var f := mkReplaceGenerateCmd(cmdvars);
            ds_out := [];
            for i := 0 to |ds| {
                var d := LucidMapper.visitDecl(ds[i], LucidMapper.UpdateStmt(f));
                d := deleteGenerateParams(d);
                ds_out := ds_out + [d];
            }
        }


    }

    class DafnyCallEliminator {
        // this must be run after elimDafnyGenerateOutParams
        static function elimDafnyCall(s : stmt) : stmt {
            match s {
                case DafnyCall(id, args, outvars) => 
                    if (id == "ArrayMemops.Get") && |outvars| == 1 then 
                        SAssign(outvars[0], ECall(id, args))
                    else if (id == "ArrayMemops.Set") && |outvars| == 1 then
                        SUnit(ECall(id, args))
                    else if (id == "ArrayMemops.GetSet") && |outvars| == 2 then 
                        SAssign(outvars[0], ECall(id, args))
                    // calls to user functions are allowed if they have 
                    // 0 or 1 outvars
                    else if |outvars| == 1 then 
                        SAssign(outvars[0], ECall(id, args))
                    else if |outvars| == 0 then 
                        SUnit(ECall(id, args))
                    else s
                case _ => s
            }
        }

        static method process(ds : seq<decl>) returns (ds_out : seq<decl>) {
            ds_out := [];
            for i := 0 to |ds| {
                var d := LucidMapper.visitDecl(ds[i], LucidMapper.UpdateStmt(elimDafnyCall));
                ds_out := ds_out + [d];
            }
        }
    }

    class DafnyDeclareEliminator {
        // eliminate DafnyDeclare statements (declarations without initializations)
        // - delete global typed (globals are never modified directly in user code)
        // - for other types, replace with local variable declaration with default value
        static function elimDafnyDeclare(s : stmt) : stmt {
            match s {
                case DafnyDeclare(id, TGlobal(_, _)) => SNoop 
                case DafnyDeclare(id, ty) => 
                    SLocal(id, ty, EVal(defaultTyVal(ty)))
                case _ => s
            }
        }
        static method process(ds : seq<decl>) returns (ds_out : seq<decl>) {
            ds_out := [];
            for i := 0 to |ds| {
                var d := LucidMapper.visitDecl(ds[i], LucidMapper.UpdateStmt(elimDafnyDeclare));
                ds_out := ds_out + [d];
            }
        }
    }

    class RecordInitMerger {
        // A local of a type with no default value (e.g. a record) is lowered by
        // Dafny to an uninitialized declare + a following assignment. The declare
        // gets an invalid default; merge the pair back into one initialized local.
        // Only fires on invalid defaults, so int/bool locals are untouched.
        // Applied to every straight-line block (method bodies and if-branches) via
        // the mapper's UpdateStmts, so nested record constructions are covered too.
        static function mergeInits(stmts : seq<stmt>) : seq<stmt> {
            if |stmts| < 2 then stmts
            else
                match (stmts[0], stmts[1]) {
                    case (SLocal(x, ty, EVal(VInvalid(_))), SAssign(y, e)) =>
                        if x == y then [SLocal(x, ty, e)] + mergeInits(stmts[2..])
                        else [stmts[0]] + mergeInits(stmts[1..])
                    case _ => [stmts[0]] + mergeInits(stmts[1..])
                }
        }
        static method process(ds : seq<decl>) returns (ds_out : seq<decl>) {
            ds_out := LucidMapper.visitDecls(ds, LucidMapper.UpdateStmts(mergeInits));
        }
    }

    class ModuleSelfRewrite {
        // Inside a module method, add a `t self` first parameter and rewrite each
        // field reference `field` to `self#field`. The field names come from the
        // module's `type t` record member.
        static function fieldNamesOf(members : seq<decl>) : set<id> {
            if |members| == 0 then {}
            else match members[0] {
                case DRecord(tn, fs) => if tn == "t" then (set i | 0 <= i < |fs| :: fs[i].0) else fieldNamesOf(members[1..])
                case _ => fieldNamesOf(members[1..])
            }
        }
        static function selfRewrite(fields : set<id>) : exp -> exp {
            (e : exp) =>
                match e {
                    case EVar(x) => if x in fields then EProject(EVar("self"), x) else e
                    case _ => e
                }
        }
        static method rewriteMember(m : decl, fields : set<id>) returns (rv : decl) {
            var rw := LucidMapper.visitDecl(m, LucidMapper.UpdateExp(selfRewrite(fields)));
            // Only funs that actually reference a field take a `self` param (the
            // rewrite changed the body); pure helpers keep their plain signature.
            if rw != m {
                match rw {
                    case DFunction(id, rty, params, body) =>
                        rv := DFunction(id, rty, [("self", TRecord("t"))] + params, body);
                    case _ => rv := rw;
                }
            } else {
                rv := m;
            }
        }
        static method process(ds : seq<decl>) returns (ds_out : seq<decl>) {
            ds_out := [];
            for i := 0 to |ds| {
                match ds[i] {
                    case DModule(id, members) => {
                        var fields := fieldNamesOf(members);
                        var newMembers := [];
                        for j := 0 to |members| {
                            var nm := rewriteMember(members[j], fields);
                            newMembers := newMembers + [nm];
                        }
                        ds_out := ds_out + [DModule(id, newMembers)];
                    }
                    case _ => ds_out := ds_out + [ds[i]];
                }
            }
        }
    }

    class DafnyMethodEliminator {
        // DafnyMethod elimination:
        //  if it is used as a memopid variable, it is a memop
        // 	- else if it is used as a non-memop variable, it is a constant or symbolic
        // 		- a constant if the method returns a value
        // 		- a symbolic if it returns an EVar
        // 	- else if its capitalized id is an event's id, it is a handler
        // 	- else it is a plain function

        var memopIds : set<id>
        var varIds : set<id>
        var eventIds : set<id>
        constructor Create() {
            memopIds := {};
            varIds := {};
            eventIds := {};
        }
        // A method with a single out-var lowers to a fun that must `return` it;
        // the implicit `return;` returns nothing otherwise.
        static function mapRetsInStmts(stmts : seq<stmt>, ov : id) : seq<stmt> {
            if |stmts| == 0 then []
            else
                var h := mapRetInStmt(stmts[0], ov);
                // drop dead code following a return in the same block
                if h.SRet? then [h]
                else [h] + mapRetsInStmts(stmts[1..], ov)
        }
        static function mapRetInStmt(s : stmt, ov : id) : stmt {
            match s {
                case SRet(None) => SRet(Some(EVar(ov)))
                case SIf(c, t, e) => SIf(c, mapRetsInStmts(t, ov), mapRetsInStmts(e, ov))
                // early `return` inside a for-loop maps too; the loop itself is
                // not a return, so it never truncates the enclosing block.
                case SFor(iv, b, body) => SFor(iv, b, mapRetsInStmts(body, ov))
                case _ => s
            }
        }
        static function fixFnReturns(d : decl, ov : id) : decl {
            match d {
                case DFunction(id, rty, params, body) =>
                    var mapped := mapRetsInStmts(body, ov);
                    var finalBody := if |mapped| > 0 && mapped[|mapped| - 1].SRet? then mapped
                                     else mapped + [SRet(Some(EVar(ov)))];
                    DFunction(id, rty, params, finalBody)
                case _ => d
            }
        }
        method elimDafnyMethod(d : decl) returns (d_out : decl)
        {
            match d {
                case DDafnyMethod(id, rtys, params, body, outvars) => {
                    if |rtys| == 1 {
                        if (id in memopIds) { 
                            d_out := DMemop(id, rtys[0], params, body);
                        }
                        else {
                            if (id in varIds) { 
                                if |body| == 1 { 
                                    match body[0] {
                                        case SRet(Some(EVal(v))) => {d_out := DConst(id, rtys[0], EVal(v));}
                                        case SRet(Some(EVar(_))) =>{d_out := DSymbolic(id, rtys[0]);}
                                        case _ => {
                                            print("elimDafnyMethod: id = " + id + " id in varIds, but body is not a return statement with a value or variable.\n");    
                                            d_out := d;
                                        }
                                    }
                                }
                                else {
                                    print("elimDafnyMethod: id = " + id + " id in varIds, but body is not a single statement.\n");    
                                    d_out := d;
                                }
                            }
                            else {
                                if |params| == 0 && |body| == 1 {
                                    match body[0] {
                                        case SRet(Some(EVal(v))) => {d_out := DConst(id, rtys[0], EVal(v));}
                                        case SRet(Some(EVar(_))) => {d_out := DSymbolic(id, rtys[0]);}
                                        case _ => {d_out := DFunction(id, rtys[0], params, body);}
                                    }
                                }
                                else {
                                    d_out := DFunction(id, rtys[0], params, body);
                                }
                            }
                        }
                    }
                    else {
                        if |rtys| == 0 { // if it has no return values,
                                         // it could either be a handler or a function
                            // A method is a handler if its name matches an event
                            // up to first-letter case. This covers both the old
                            // convention (event `IpPkt`, handler `ipPkt`) and the
                            // new one (event `pkt`, handler `Pkt`). Emit the
                            // event's actual id.
                            var matched : Option<id> := None;
                            var pending := eventIds;
                            while pending != {}
                                decreases |pending|
                            {
                                var e :| e in pending;
                                if capitalize(e) == capitalize(id) { matched := Some(e); }
                                pending := pending - {e};
                            }
                            if matched.Some? {
                                d_out := DHandler(matched.value, params, body);
                            }
                            else {
                                d_out := DFunction(id, TVoid, params, body);
                            }
                        }
                        else { // if it has multiple return values, we can't support it
                               // (and most likely an earlier pass should've eliminated these cases)
                            print ("elimDafnyMethod: id = " + id + " has 0 or multiple return values and is not a handler.\n");
                            d_out := d;
                        }
                    }
                    // a fun built from a method with one out-var must return it.
                    // (Dafny appends an implicit fall-through `return;` after an
                    // explicit `return e`, so fixFnReturns also drops that dead
                    // trailing return.)
                    if |outvars| == 1 {
                        d_out := fixFnReturns(d_out, outvars[0]);
                    }
                }
                case DModule(id, members) => {
                    // classify the module's methods (funs) too.
                    var newMembers := [];
                    for i := 0 to |members| {
                        var nm := elimDafnyMethod(members[i]);
                        newMembers := newMembers + [nm];
                    }
                    d_out := DModule(id, newMembers);
                }
                case _ => {d_out := d;}
            }
        }

        method process(ds : seq<decl>) returns (ds_out : seq<decl>)
            modifies this
        {
            memopIds := getMemopIds(ds);
            varIds := getVarIds(ds);
            eventIds := getEventIds(ds);
            ds_out := [];
            for i := 0 to |ds| {
                var d := elimDafnyMethod(ds[i]);
                ds_out := ds_out + [d];
            }
        }


    }

    class CmpSimplifier {
        // The dafny compiler reduces all comparisons to "<". We 
        // want to simplify these comparisons back to their original
        // forms. This pass is a work in progress. Currently it just 
        // converts !(x < y) to x >= y.

        static function simplifyCmp(exp : exp) : exp {
            match exp {
                case EOp(Not, args) => 
                    match |args| {
                        case 1 => 
                            match args[0] {
                                case EOp(Lt, lt_args) => 
                                    if |lt_args| == 2 
                                        then EOp(Gt, lt_args) // TODO: make this Gte once we fix the lucid compiler's wellformedness checker to allow it
                                        else exp
                                case _ => exp
                            }
                        case _ => exp
                    }
                case _ => exp
            }
        }

        static method process(ds : seq<decl>) returns (ds_out : seq<decl>) {
            ds_out := LucidMapper.visitDecls(ds, LucidMapper.UpdateExp(simplifyCmp));
        }
    }


    class DafnyArithEliminator {
        constructor Create() {}

        static function getConstVal(node : AstNode) : seq<(id, val)> {
            match node {
                // only scalar consts feed the modulo->mask arithmetic pass;
                // value-vector consts (comprehension/enumeration inits) are skipped.
                case DeclNode(DConst(id, _, EVal(v))) => [(id, v)]
                case _ => []
            }
        }
        static method getConstVals(ds : seq<decl>) returns (constVals : map<id, val>)
        {
            constVals := map[];
            var constValList := LucidCollector.visitDecls(ds, getConstVal);
            for i := 0 to |constValList| {
                constVals := constVals[constValList[i].0 := constValList[i].1];
            }
        }

        static function lookup(constVals : map<id, val>, id : id) : val
        {
            if id in constVals then constVals[id]
            else VInvalid("id not found in constVals")
        }
        static predicate isDigitc(c : char) { '0' <= c <= '9' }
        static predicate allDigitsc(s : string) { forall i :: 0 <= i < |s| ==> isDigitc(s[i]) }
        // the library `maxN` consts (`max8`, `max32`, ...) = 2^N. A `% maxN`
        // reduces mod the full width, which is a no-op when the operand is N bits
        // (the convention -- narrowing uses `to_uintN` casts), so it's dropped.
        static predicate isMaxName(id : id) { |id| > 3 && id[..3] == "max" && allDigitsc(id[3..]) }
        static predicate isPow2(n : nat) decreases n
        { if n == 0 then false else if n == 1 then true else n % 2 == 0 && isPow2(n / 2) }
        // 1. DafnyDiv elimination: 
        // 	- given `e / N`, if `N=2^x`, replace with `e >> x`
        // 2. DafnyMod elimination:
        // 	- given e mod N, if `N == (sizeof(e)^2)`, replace with `e`
        // For now, we assume that N is the right value to perform the elimination.
        static function {:axiom} mkElimDafnyArith(constVals : map<id, val>) : exp -> exp {
            (exp : exp) => match exp {
                case EOp(DafnyDiv, args) => 
                    if |args| == 2 then 
                        match args[1] {
                            case EVar(id) => 
                                match lookup(constVals, id) {
                                    case VInt(intstr, sz) => 
                                        var n := stringToNat(intstr);
                                        var logn := Log(2, n);
                                        EOp(BitShiftR, [args[0], EVal(VInt(natToString(logn), sz))])
                                    case _ => exp
                                }
                            case EVal(VInt(intstr, sz)) => 
                                var n := stringToNat(intstr);
                                var logn := Log(2, n);
                                EOp(BitShiftR, [args[0], EVal(VInt(natToString(logn), sz))])
                            case _ => exp
                        }
                    else
                        exp
                case EOp(DafnyMod, args) =>
                    // `e % N`, N a power of two: `maxN` (a full-width wrap) is a
                    // no-op and dropped; any other power-of-two `& (N-1)`. A
                    // non-power-of-two / unresolved divisor is left as `%`, which
                    // Lucid rejects -- rather than silently dropping a real modulo.
                    if |args| == 2 then
                        match args[1] {
                            case EVar(id) =>
                                if isMaxName(id) then args[0]
                                else
                                    match lookup(constVals, id) {
                                        case VInt(intstr, sz) =>
                                            var n := stringToNat(intstr);
                                            if isPow2(n) then EOp(BitAnd, [args[0], EVal(VInt(natToString(n - 1), sz))])
                                            else exp
                                        case _ => exp
                                    }
                            case EVal(VInt(intstr, sz)) =>
                                var n := stringToNat(intstr);
                                if isPow2(n) then EOp(BitAnd, [args[0], EVal(VInt(natToString(n - 1), sz))])
                                else exp
                            case _ => exp
                        }
                    else exp
                case _ => exp
            }
        }

        static method process(ds : seq<decl>) returns (ds_out : seq<decl>) 
        {
            var constVals := getConstVals(ds);
            var elimF := mkElimDafnyArith(constVals);
            ds_out := [];
            for i := 0 to |ds| {
                var d := LucidMapper.visitDecl(ds[i], LucidMapper.UpdateExp(elimF));
                ds_out := ds_out + [d];
            }
        }
    }

    function splitStrFst(c : char, str : string) : (string, string) {
        if |str| == 0 then ([], [])
        else 
            if str[0] == c then ([], str[1..]) // found, put the rest into snd
            else // not found, recurse and prepend to fst
                var rest := splitStrFst(c, str[1..]);
                ([str[0]] + rest.0, rest.1)               
    }


    class ArrayModuleRenaming {
        // 1. Replace "Array.t" with "IntArray.t"
        // 2. In calls to ArrayMemops functions, replace the module 
        // name ArrayMemops with either "IntArray" or "BoolArray" 
        // depending on the type of the global variable passed 
        // as the first argument to the function. 
        static function getGlobalTy(node : AstNode) : seq<(string, string)> {
            match node {
                case DeclNode(DGlobal(id, ty, _)) =>
                    match ty {
                        case TGlobal(tyid, _) => [(id,tyid)]
                        // a vector of arrays: element type carries the array kind
                        case TVec(TGlobal(tyid, _), _) => [(id,tyid)]
                        case _ => []
                    }
                case _ => []
            }
        }
        static method getGlobalTys(ds : seq<decl>) returns (tyMap : map<id, id>)
        {
            tyMap := map[];
            var tyList := LucidCollector.visitDecls(ds, getGlobalTy);
            for i := 0 to |tyList| {
                tyMap := tyMap[tyList[i].0 := tyList[i].1];
            }
        }

        static function arrayToIntArray(ty : ty) : ty {
            match ty {
                case TGlobal(tname, args) => 
                    if (tname == "Array.t") then 
                        TGlobal("IntArray.t", args)
                    else ty
                case _ => ty                        
            }
        }
        static method arraysToIntArrays(ds : seq<decl>) returns (rv : seq<decl>) {
            rv := [];
            for i:=0 to |ds| {
                var d := LucidMapper.visitDecl(ds[i], LucidMapper.UpdateTy(arrayToIntArray));
                rv := rv + [d];
            }
        }

        static function mkRenameArrayMemopCall(tymap : map<id, id>) : exp -> exp {
            (exp : exp) => 
                match exp {
                    case ECall(id, args) => 
                        if |args| > 0 then 
                            match args[0] {
                                case EVar(globalId) => 
                                    var names := splitStrFst('.', id);
                                    var modName := names.0;
                                    var fnName := names.1;
                                    var newModName := 
                                        if (modName == "ArrayMemops") then
                                            if globalId in tymap then 
                                                var tyname := tymap[globalId];
                                                if tyname == "IntArray.t" then
                                                    "IntArray."
                                                else if tyname == "BoolArray.t" then 
                                                    "BoolArray."
                                                else "ArrayMemops."
                                            else "ArrayMemops."
                                        else modName;
                                    ECall(newModName + fnName, args)
                                // module array method: the array is `self#field`
                                // (an EProject). Module arrays are always int.
                                case EProject(_, _) =>
                                    var names := splitStrFst('.', id);
                                    if names.0 == "ArrayMemops" then ECall("IntArray." + names.1, args) else exp
                                // module vector element: `self#field[i]` (EIndex
                                // over EProject). Module arrays are always int.
                                case EIndex(EProject(_, _), _) =>
                                    var names := splitStrFst('.', id);
                                    if names.0 == "ArrayMemops" then ECall("IntArray." + names.1, args) else exp
                                // vector element: the array is `vec[i]` (EIndex).
                                // Resolve the module from the vector global's type.
                                case EIndex(EVar(globalId), _) =>
                                    var names := splitStrFst('.', id);
                                    var modName := names.0;
                                    var fnName := names.1;
                                    var newModName :=
                                        if (modName == "ArrayMemops") then
                                            if globalId in tymap then
                                                var tyname := tymap[globalId];
                                                if tyname == "IntArray.t" then "IntArray."
                                                else if tyname == "BoolArray.t" then "BoolArray."
                                                else "ArrayMemops."
                                            else "ArrayMemops."
                                        else modName;
                                    ECall(newModName + fnName, args)
                                case _ => exp
                            }
                        else exp
                    case _ => exp
                }
        }
        static function renameCreateExp(e : exp) : exp {
            // module ctors are all int arrays; recurse into vector ctors so a
            // module's `field = [Array.create(..) for ..]` renames too.
            match e {
                case ECall(id, args) => if id == "ArrayMemops.Create" then ECall("IntArray.Create", args) else e
                case EComp(body, iv, n) => EComp(renameCreateExp(body), iv, n)
                case EVecLit(elems) => EVecLit(seq(|elems|, i requires 0 <= i < |elems| => renameCreateExp(elems[i])))
                case _ => e
            }
        }
        // rename an `ArrayMemops.Create(...)` call to the given array module.
        static function renameCreateTo(mod : string, e : exp) : exp {
            match e {
                case ECall("ArrayMemops.Create", args) => ECall(mod + ".Create", args)
                case _ => e
            }
        }
        // rename Create calls inside a vector constructor (comprehension body or
        // each enumerated element).
        static function renameCreateInVec(mod : string, ctor : exp) : exp {
            match ctor {
                case EComp(body, iv, n) => EComp(renameCreateTo(mod, body), iv, n)
                case EVecLit(elems) => EVecLit(seq(|elems|, i requires 0 <= i < |elems| => renameCreateTo(mod, elems[i])))
                case _ => ctor
            }
        }
        static function renameCreateModule(d : decl) : decl {
            match d {
                case DGlobal(id, gty, ctor) =>
                    match (gty, ctor) {
                        case (TGlobal(tyid, _), ECall(_, args)) =>
                            if (tyid == "IntArray.t") then
                                DGlobal(id, gty, ECall("IntArray.Create", args))
                            else if (tyid == "BoolArray.t") then
                                DGlobal(id, gty, ECall("BoolArray.Create", args))
                            else d
                        // a vector of arrays: rename Create inside the ctor
                        case (TVec(TGlobal(tyid, _), _), _) =>
                            if (tyid == "IntArray.t") then
                                DGlobal(id, gty, renameCreateInVec("IntArray", ctor))
                            else if (tyid == "BoolArray.t") then
                                DGlobal(id, gty, renameCreateInVec("BoolArray", ctor))
                            else d
                        case _ => d
                    }
                case DModule(id, members) =>
                    DModule(id, seq(|members|, i requires 0 <= i < |members| => renameCreateModule(members[i])))
                case DConstr(tyname, cname, params, inits) =>
                    DConstr(tyname, cname, params,
                        seq(|inits|, i requires 0 <= i < |inits| => (inits[i].0, renameCreateExp(inits[i].1))))
                case _ => d
            }
        }

        static method process(ds : seq<decl>) returns (rv : seq<decl>) {
            var ds_new := arraysToIntArrays(ds);
            var tyMap := getGlobalTys(ds_new);
            var f := mkRenameArrayMemopCall(tyMap);
            rv := [];
            for i:=0 to |ds_new| {
                var d := LucidMapper.visitDecl(ds_new[i], LucidMapper.UpdateExp(f));
                d := renameCreateModule(d);
                rv := rv + [d];
            }
        }
        
    }

    class IdPrefixRenaming {
        // don't let ids start with an underscore
        static function renameId(id : id) : id {
            if |id| > 0 && id[0] == '_' then 
                "var" + id
            else 
                id
        }
        static method process(ds : seq<decl>) returns (rv : seq<decl>) {
            rv := [];
            for i:=0 to |ds| {
                var d := LucidMapper.visitDecl(ds[i], LucidMapper.UpdateId(renameId));
                rv := rv + [d];
            }
        }
    }
    
    class EventNormalizer {
        // An event with no handler is deleted, UNLESS it is generated as output
        // (e.g. an egress-only event): Lucid still needs its declaration, so we
        // keep it and give it a `{skip;}` handler.

        static function getHandlerId(d : decl) : Option<id> {
            match d {
                case DHandler(id, _, _) => Some(id)
                case _ => None
            }
        }
        static method getHandlerIds(ds : seq<decl>) returns (rv : set<id>) {
            rv := {};
            for i:=0 to |ds| {
                var id_opt := getHandlerId(ds[i]);
                match id_opt {
                    case Some(id) => {
                        rv := rv + {id};
                    }
                    case None => {}
                }
            }
        }
        // event ids referenced in a generate statement (an EEvent expression).
        static function getGeneratedId(node : AstNode) : seq<id> {
            match node {
                case ExpNode(EEvent(id, _)) => [id]
                case _ => []
            }
        }
        static method getGeneratedIds(ds : seq<decl>) returns (rv : set<id>) {
            rv := {};
            var idList := LucidCollector.visitDecls(ds, getGeneratedId);
            for i := 0 to |idList| {
                rv := rv + {idList[i]};
            }
        }
        static method process(ds : seq<decl>) returns (rv : seq<decl>) {
            var handlerIds := getHandlerIds(ds);
            var generatedIds := getGeneratedIds(ds);
            rv := [];
            for i := 0 to |ds| {
                var d := ds[i];
                match d {
                    case DEvent(id, params) => {
                        if (id in handlerIds) {
                            rv := rv + [DEvent(id, params)];
                        } else if (id in generatedIds) {
                            // output-only event: keep it and add a skip handler.
                            rv := rv + [DEvent(id, params), DHandler(id, params, [SNoop])];
                        }
                        // else: drop truly-unused events.
                    }
                    case _ => {
                        rv := rv + [d];
                    }
                }
            }
        }
    }

    class TimestampAutoInit {
        // turn the "timestamp" argument of a handler 
        // into a local variable initialized with the current time.
        static function getEventSig(node : AstNode) : seq<(id, seq<param>)> {
            match node {
                case DeclNode(DEvent(id, params)) => [(id, params)]
                case _ => []
            }
        }
        static method getEventSigs(ds : seq<decl>) returns (eventSigs : map<id, seq<param>>) {
            eventSigs := map[];
            var sigList := LucidCollector.visitDecls(ds, getEventSig);
            for i := 0 to |sigList| {
                eventSigs := eventSigs[sigList[i].0 := sigList[i].1];
            }
        }

        static function updateHandler(eventSigs : map<id, seq<param>>) : decl -> decl {
            (d : decl) => 
                match d {
                    case DHandler(id, params, body) => 
                        if id in eventSigs then 
                            var eventParams := eventSigs[id];
                            if |params| > 0 && (|params| > |eventParams|) then 
                                var ts_id := params[|params|-1].0;
                                var ts_ty := params[|params|-1].1;
                                var ts_size := match ts_ty {
                                    case TInt(sz) => sz
                                    case _ => 0
                                };
                                var newParams := params[..|params|-1];
                                var newBody := [SLocal(
                                                        ts_id, 
                                                        ts_ty, 
                                                        EOp(IntCast(ts_size), [ECall("Sys.time", [])])
                                                       )
                                                ] 
                                                + body;
                                DHandler(id, newParams, newBody)
                            else d
                        else d
                    case _ => d
                }
        }

        static method process(ds : seq<decl>) returns (rv : seq<decl>) {
            var eventSigs := getEventSigs(ds);
            var f := updateHandler(eventSigs);
            rv := LucidMapper.visitDecls(ds, LucidMapper.UpdateDecl(f));
        }

    }

    method constDeclsFirst(ds : seq<decl>) returns (ds_ordered : seq<decl>) {
        var const_decls := [];
        var other_decls := [];
        for i:= 0 to |ds| {
            match ds[i] {
                case DConst(_, _, _) => const_decls := const_decls + [ds[i]];
                case DSymbolic(_, _) => const_decls := const_decls + [ds[i]];
                case _ => other_decls := other_decls + [ds[i]];
            }
        }
        ds_ordered := const_decls + other_decls;
    }

    // Lucid requires a module to be declared before any other module that
    // references it. Topologically sort DModule decls so a referenced module
    // (`OtherMod.op(..)` in a body, or `OtherMod.t` in a type) precedes its
    // user, keeping non-module decls in place.
    class ModuleOrdering {
        static function getModuleRef(node : AstNode) : seq<string> {
            match node {
                case ExpNode(ECall(id, _)) => [splitStrFst('.', id).0]
                case TyNode(TGlobal(id, _)) => [splitStrFst('.', id).0]
                case _ => []
            }
        }
        static method process(ds : seq<decl>) returns (rv : seq<decl>) {
            var modIds : set<id> := {};
            for i := 0 to |ds| {
                match ds[i] { case DModule(id, _) => modIds := modIds + {id}; case _ => {} }
            }
            if |modIds| <= 1 { return ds; }
            // deps[m] = other modules m references
            var deps : map<id, set<id>> := map[];
            for i := 0 to |ds| {
                match ds[i] {
                    case DModule(id, members) => {
                        var refs := LucidCollector.visitDecls(members, getModuleRef);
                        var d : set<id> := {};
                        for k := 0 to |refs| {
                            if refs[k] in modIds && refs[k] != id { d := d + {refs[k]}; }
                        }
                        deps := deps[id := d];
                    }
                    case _ => {}
                }
            }
            // greedy topological order (deterministic by ds order); a cycle or
            // missing dep falls back to placing the rest in original order.
            var ordered : seq<id> := [];
            var placed : set<id> := {};
            while placed < modIds
                decreases |modIds| - |placed|
            {
                var progress := false;
                for i := 0 to |ds| {
                    match ds[i] {
                        case DModule(id, _) =>
                            if id !in placed && deps[id] * placed == deps[id] {
                                ordered := ordered + [id]; placed := placed + {id}; progress := true;
                            }
                        case _ => {}
                    }
                }
                if !progress {
                    for i := 0 to |ds| {
                        match ds[i] {
                            case DModule(id, _) => if id !in placed { ordered := ordered + [id]; placed := placed + {id}; }
                            case _ => {}
                        }
                    }
                }
            }
            // rebuild, filling each module slot from the sorted order
            var modByPos : map<id, decl> := map[];
            for i := 0 to |ds| {
                match ds[i] { case DModule(id, _) => modByPos := modByPos[id := ds[i]]; case _ => {} }
            }
            rv := [];
            var mi := 0;
            for i := 0 to |ds| {
                match ds[i] {
                    case DModule(_, _) =>
                        if mi < |ordered| && ordered[mi] in modByPos {
                            rv := rv + [modByPos[ordered[mi]]]; mi := mi + 1;
                        } else { rv := rv + [ds[i]]; }
                    case _ => rv := rv + [ds[i]];
                }
            }
        }
    }

    class NoArrayCreateDefault {
        static function noArrayCreateDefault(exp : exp) : exp {
            match exp {
                case ECall("ArrayMemops.Create", args) => 
                    if |args| == 2 then 
                        ECall("ArrayMemops.Create", [args[0]])
                    else exp
                case _ => exp
            }
        }
        static method process(ds : seq<decl>) returns (rv : seq<decl>) {
            rv := LucidMapper.visitDecls(ds, LucidMapper.UpdateExp(noArrayCreateDefault));
        }
    }

    class ConvertBoolArrayNames {
        static const CalcFuns := {
            "ArrayMemops.nocalc", 
            "ArrayMemops.swapcalc"
        }
        static const BoolFuns := {
            "BoolArray.Get",
            "BoolArray.Set",
            "BoolArray.GetSet"
        }
        static function DeleteNoCalcSwapCalc(exps : seq<exp>) : seq<exp> {
            if |exps| == 0 then exps
            else 
                match exps[0] {
                    case EVar(id) => 
                        if id in CalcFuns then 
                            DeleteNoCalcSwapCalc(exps[1..])
                        else
                            [exps[0]] + DeleteNoCalcSwapCalc(exps[1..])
                    case _ => 
                            [exps[0]] + DeleteNoCalcSwapCalc(exps[1..])
                }
        }
        static function DeleteBoolArrayArgs(exp : exp) : exp {
            match exp {
                case ECall(fcnid, args) => 
                    if (fcnid in BoolFuns) then 
                        ECall(fcnid, DeleteNoCalcSwapCalc(args))
                    else exp
                case _ => exp
            }
        }
        static method process(ds : seq<decl>) returns (rv : seq<decl>) {
            rv := LucidMapper.visitDecls(ds, LucidMapper.UpdateExp(DeleteBoolArrayArgs));
        }
    }

    class ConvertIntArrayNames {
        static const nameMap := map[
            "IntArray.t":="Array.t",
            "IntArray.Get":="Array.getm",
            "IntArray.Set":="Array.setm",
            "IntArray.Create":="Array.create",
            "IntArray.GetSet":="Array.update",
            "ArrayMemops.nocalc":="nocalc",
            "ArrayMemops.swapcalc":="swapcalc"

        ]
        static function renameIntArrayId(id : id) : id {
            if id in nameMap then nameMap[id]
            else id
        }
        static method process(ds : seq<decl>) returns (rv : seq<decl>) {
            // rv := [];
            // for i := 0 to |ds| {
            //     var d := LucidMapper.visitDecl(ds[i], LucidMapper.UpdateId(renameIntArrayId));
            //     match ds[i] {
            //         case DGlobal(_, TGlobal(tname, _), _) => {
            //             print ("ConvertIntArrayNames: old_ty_str = " + tname + "\n");
            //         }
            //         case _ => {}
            //     }
            //     match d {
            //         case DGlobal(_, TGlobal(tname, _), _) => {
            //             print ("ConvertIntArrayNames: new_ty_str = " + tname + "\n");
            //         }
            //         case _ => {}
            //     }
            //     rv := rv + [d];
            // }
            rv := LucidMapper.visitDecls(ds, LucidMapper.UpdateId(renameIntArrayId));
        }
    }

    class DeleteHandlerReturns {
        // Delete return statements from handler bodies
        static function deleteHandlerReturns(s : stmt) : stmt {
            match s {
                case SRet(_) => SNoop
                case _ => s
            }
        }
        static method processDecl(d : decl) returns (d_out : decl) {
            match d {
                case DHandler(id, params, body) => {
                    var newBody := []; 
                    for i := 0 to |body| {
                        var s := LucidMapper.visitStmt(body[i], LucidMapper.UpdateStmt(deleteHandlerReturns));
                        newBody := newBody + [s];
                    }
                    d_out := DHandler(id, params, newBody);
                }
                case _ => d_out := d;
            }
        }
        static method process(ds : seq<decl>) returns (rv : seq<decl>) {
            rv := [];
            for i := 0 to |ds| {
                var d := processDecl(ds[i]);
                rv := rv + [d];
            }
        }
    }

    class OrderGlobalDecls {
        // order the global declarations according to the sequence 
        // defined in the "DDafnyFieldOrder" decl.
        static method getGlobalOrder(ds : seq<decl>) returns (fieldOrder : seq<id>) {
            fieldOrder := [];
            for i := 0 to |ds| {
                match ds[i] {
                    case DDafnyFieldOrder(ids) => fieldOrder := ids;
                    case _ => {}
                }
            }
        }
        static method getGlobalDecl(ds : seq<decl>, id : id) returns (d : seq<decl>) {
            d := [];
            for i := 0 to |ds| {
                match ds[i] {
                    case DGlobal(gid, _, _) => {
                        if gid == id {
                            d := [ds[i]];
                        }
                    }
                    case _ => {}
                }
            }
        }
        static method process(ds : seq<decl>) returns (rv : seq<decl>) {
            var fieldOrder := getGlobalOrder(ds);
            var orderedGlobalDecls := [];
            for i := 0 to |fieldOrder| {
                var d := getGlobalDecl(ds, fieldOrder[i]);
                orderedGlobalDecls := orderedGlobalDecls + d;
            }
            var globalIds : set<id> := {};
            for i := 0 to |ds| {
                match ds[i] {
                    case DGlobal(gid, _, _) => globalIds := globalIds + {gid};
                    // a constructor-initialized value-vector field is a DConst;
                    // it too supersedes the field's uninitialized DSymbolic getter.
                    case DConst(gid, _, _) => globalIds := globalIds + {gid};
                    case _ => {}
                }
            }
            var nonGlobalDecls := [];
            for i := 0 to |ds| {
                match ds[i] {
                    case DGlobal(_, _, _) => {}
                    // A `const` array field generates both a getter (→ DSymbolic)
                    // and a constructor global; drop the redundant symbolic.
                    case DSymbolic(sid, _) =>
                        if sid !in globalIds { nonGlobalDecls := nonGlobalDecls + [ds[i]]; }
                    case _ => nonGlobalDecls := nonGlobalDecls + [ds[i]];
                }
            }
            rv := orderedGlobalDecls + nonGlobalDecls;
        }
    }

    class PadEventParams {
        // after each event parameter that is a boolean, 
        // add an 7-bit uint parameter to pad it to 8 bits.
        static function padEventParams(params : seq<param>) : seq<param> {
            if |params| == 0 then params
            else 
                match params[0] {
                    case (id, TBool) => 
                        [(id, TBool)] + [("pad_" + id, TInt(7))] + padEventParams(params[1..])
                    case _ => [params[0]] + padEventParams(params[1..])
                }
        }
        static function padEvent(d : decl) : decl {
            match d {
                case DEvent(id, params) => DEvent(id, padEventParams(params))
                case DHandler(id, params, body) => DHandler(id, padEventParams(params), body)
                case _ => d
            }
        }
        static function getParamTys(params : seq<param>) : seq<ty> {
            if |params| == 0 then []
            else 
                [params[0].1] + getParamTys(params[1..])
        }
        static function getEventParamTys(n : LucidCollector.AstNode) : seq<(id, seq<ty>)> {
            match n {
                case DeclNode(d) => 
                    match d {
                        case DEvent(id, params) => [(id, getParamTys(params))]
                        case _ => []
                    }
                case _ => []
            }
        }
        static method getEventsParamTys(ds : seq<decl>) returns (rv : map<id, seq<ty>>) {
            rv := map[];
            var boolParamIds := LucidCollector.visitDecls(ds, getEventParamTys);
            for i := 0 to |boolParamIds| {
                rv := rv[boolParamIds[i].0 := boolParamIds[i].1];
            }
        }

        // recursive function, add a pad argument after each boolean argument. 
        // types of the arguments are given by first seq.
        static function padArgs(argTys : seq<ty>, args : seq<exp>) : seq<exp> {
            if |args| != |argTys| then args
            else 
                if |args| == 0 then args
                else 
                    match argTys[0] {
                        case TBool => 
                            [args[0], EVal(VInt("0", 7))] + padArgs(argTys[1..], args[1..])
                        case _ => [args[0]] + padArgs(argTys[1..], args[1..])
                    }
        }

        static function padEventArgs(eventBoolArgs : map<id, seq<ty>>) : exp -> exp {
            (exp : exp) => 
                match exp {
                    case EEvent(id, args) => 
                        if id in eventBoolArgs then 
                            var boolParamTys := eventBoolArgs[id];
                            EEvent(id, padArgs(boolParamTys, args))
                        else exp
                    case _ => exp
                }
        }

        static method process(ds : seq<decl>) returns (rv : seq<decl>) {
            // 1. get event parameter types
            var eventParamTys := getEventsParamTys(ds);
            // 2. pad event declarations
            var ds_new := LucidMapper.visitDecls(ds, LucidMapper.UpdateDecl(padEvent));
            // 3. pad event arguments
            var f := padEventArgs(eventParamTys);
            rv := LucidMapper.visitDecls(ds_new, LucidMapper.UpdateExp(f));
        }
    }


    // No preamble includes: the planned ArrayHelpers.dpt (builtin memcalcs +
    // BoolArray) was dropped from the library.
    const includes : seq<decl> := []

    method ProcessProg(ds : seq<decl>) returns (ds_out : seq<decl>) {
        // 1. Dafny generate command values turn into noops or generate commands, 
        //    all other generate command expressions and values are deleted.
        var GenerateCmdElim := new GenerateCmdEliminator();
        ds_out := GenerateCmdElim.process(ds);
        // 2. Dafny call statements (which may have had multiple return values) prior to 
        // generate command elimination are replaced with plain call expressions.
        ds_out := DafnyCallEliminator.process(ds_out);
        // 3. declarations without initializations are replaced with 
        // local variable declarations with default values.
        ds_out := DafnyDeclareEliminator.process(ds_out);
        ds_out := RecordInitMerger.process(ds_out);
        // 4. The dafny compiler uses "methods" to represent memops, 
        //    constants, symbolic variables, handlers, and functions.
        //    This pass eliminates the Dafny methods and replaces them
        //    with the appropriate construct. It infers the kind of construct 
        //    for each method based on its usage in the program.
        var MethodEliminator := new DafnyMethodEliminator.Create();
        ds_out := MethodEliminator.process(ds_out);
        ds_out := ModuleSelfRewrite.process(ds_out);
        // 6. We permit a certain subset of division and modulo operations, 
        //    those which can be transformed into bitshifts and no-ops.
        //    This pass simplifies those operations and transforms other 
        //    division and modulo op expressions into invalid values that 
        //    will halt compilation. 
        ds_out := DafnyArithEliminator.process(ds_out);
        // 7. The Dafny compiler reduces all comparisons to "<". This makes 
        //    some comparisons too complicated for the Lucid compiler to fit 
        //    into a memop, even though they are valid. This pass undoes the 
        //    comparison reduction, i.e., turning "!(x < y)" back into "x >= y".
        ds_out := CmpSimplifier.process(ds_out);
        // 6. The dafny source program orders global declarations according to 
        //    their usage order, as required by the Lucid compiler. However, 
        //    the Dafny compiler mangles the order of the global declarations.
        //    This pass retrieves the original order of the global declarations
        //    and reorders them accordingly.
        ds_out := OrderGlobalDecls.process(ds_out);
        // 7. The dafny compiler puts constant declarations at the end of the 
        //    program because order is not important, but the Lucid compiler
        //    cares about order. This pass moves the constant declarations to
        //    the beginning of the program.
        ds_out := constDeclsFirst(ds_out);
        // 8. This is a temporary pass that deletes the default argument
        //    of array constructors, which is not yet supported by the Lucid compiler.
        ds_out := NoArrayCreateDefault.process(ds_out);
        // 9. The Dafny-Lucid library uses the same "ArrayMemops" module 
        //    for both int and bool arrays. But in lucid, they are two different 
        //    modules. This pass renames identifiers from "ArrayMemops" to
        //    either "IntArray" or "BoolArray" depending on the array type. 
        ds_out := ArrayModuleRenaming.process(ds_out);
        // 10. The dafny compiler creates intermediates with names that begin 
        //     with "_", which is not a legal first character for a lucid id.
        //     This pass deletes the "_" from the beginning of the id.
        ds_out := IdPrefixRenaming.process(ds_out);
        // 11. The dafny-lucid library allows users to declare "ghost" events 
        //     that should not be executed, by declaring the event's handler as 
        //     a ghost method. However, there is no way to declare the _event_
        //     as a ghost datatype constructor. So, ghost events, at this point of 
        //     the code, will be events with no handlers. This pass deletes such events. 
        //     Note that, as an alternative, we could instead create no-op handlers
        //     for ghost events. 
        ds_out := EventNormalizer.process(ds_out);
        // 12. The tofino does not work well with boolean packet fields that 
        //     are not padded to 8 bits. The lucid compiler does not perform 
        //     such padding automatically. So, this pass pads boolean event
        //     parameters to 8 bits by adding an extra 7-bit uint parameter 
        //     after every boolean parameter.
        ds_out := PadEventParams.process(ds_out);
        // 13. The dafny-lucid library represents timestamps as a parameter 
        //     carried by the event. In lucid, timestamps are obtained 
        //     by calling the "Sys.time" function. This pass deletes 
        //     the timestamp parameter from the event and adds a local
        //     variable with the same name to the start of the handler body,
        //     initialized with a call to Sys.time cast to the appropriate 
        //     bitwidth.
        ds_out := TimestampAutoInit.process(ds_out);
        // 14. The dafny-lucid library generates events by having event
        //     handlers return a recircCmd expression. In Lucid, 
        //     events are generated with the "generate" statement and 
        //     event handlers may not return. This pass deletes the 
        //     return statements from event handlers. Note that 
        //     by this point, event handler return statements 
        //     should have had their return values eliminated by the 
        //     pass that eliminated RecircCmds.
        ds_out := DeleteHandlerReturns.process(ds_out);
        // 15. The following two passes are minor adjustments that 
        //     should be rolled into the "ArrayModuleRenaming" pass.
        ds_out := ConvertBoolArrayNames.process(ds_out);
        ds_out := ConvertIntArrayNames.process(ds_out);
        // Order modules so a referenced module precedes its user.
        ds_out := ModuleOrdering.process(ds_out);
        // 16. Finally, add an include statement for the ArrayHelpers module,
        //     which implements the BoolArray module and builtin memcalcs.
        ds_out := includes + ds_out;
    }



    // collect all the AST nodes that are not allowed to be in 
    // the final Lucid program
    function accCompatErrors(node : AstNode) : seq<AstNode> {
        match node {
            case TyNode(TDafnyGenerateCmd) => [node]
            case ValNode(VInvalid(_)) => [node]
            case ExpNode(EDafnyGenerateCmd(_, _)) => [node]
            case ExpNode(EOp(DafnyDiv, _)) => [node]
            case ExpNode(EOp(DafnyMod, _)) => [node]
            case StmtNode(DafnyCall(_, _, _)) => [node]
            case StmtNode(DafnyDeclare(_, _)) => [node]
            case DeclNode(DDafnyMethod(id, rtys, params, body, outvars)) => 
                var methodWithoutBody := DeclNode(DDafnyMethod(id, rtys, params, [], outvars));
                [methodWithoutBody]
            case _ => []
        }
    }


    method wellformedCheck(ds : seq<decl>) returns (pass : bool) {
        var errors := [];
        for i := 0 to |ds| {
            var accErrors := LucidCollector.visitDecl(ds[i], accCompatErrors);
            errors := errors + accErrors;
        }
        if (|errors| > 0) {
            var n_errs_str := PPrint.natToString(|errors|);
            print("-----" + n_errs_str + " Incompatible AST nodes found in Lucid program -----\n");
            for i := 0 to |errors| {
                print(astNodeStr(errors[i]));
                print ("\n");
            }
            print("\n----------------------------------------------------\n");
            return false;
        } else {
            print("\n----- Lucid program is well-formed -----\n");
            return true;
        }
    }
}