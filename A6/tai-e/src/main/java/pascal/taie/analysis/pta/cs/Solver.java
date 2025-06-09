/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if(!callGraph.contains(csMethod)) {
            callGraph.addReachableMethod(csMethod);
            StmtProcessor processor = new StmtProcessor(csMethod);
            for(Stmt stmt:csMethod.getMethod().getIR().getStmts()) {
                stmt.accept(processor);
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        //x = new XXX()
        @Override
        public Void visit(New stmt) {
            Pointer left = csManager.getCSVar(this.context, stmt.getLValue());
            Obj obj = heapModel.getObj(stmt);
            Context ctx = contextSelector.selectHeapContext(this.csMethod, obj);
            workList.addEntry(left, PointsToSetFactory.make(csManager.getCSObj(ctx, obj)));
            return null;
        }

        //y = x
        @Override
        public Void visit(Copy stmt) {
            Pointer left = csManager.getCSVar(this.context, stmt.getLValue());
            Pointer right = csManager.getCSVar(this.context, stmt.getRValue());
            addPFGEdge(right, left);
            return null;
        }

        //y = T.f
        @Override
        public Void visit(LoadField stmt) {
            if(stmt.isStatic()) {
                Pointer left = csManager.getCSVar(this.context, stmt.getLValue());
                Pointer right = csManager.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(right, left);
            }
            return null;
        }

        //T.f = y
        @Override
        public Void visit(StoreField stmt) {
            if(stmt.isStatic()) {
                Pointer left = csManager.getStaticField(stmt.getFieldRef().resolve());
                Pointer right = csManager.getCSVar(this.context, stmt.getRValue());
                addPFGEdge(right, left);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if(stmt.isStatic()) {
                System.out.println(stmt);
                JMethod callee = resolveCallee(null, stmt);
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                Context calleeCtx = contextSelector.selectContext(csCallSite, callee);
                CSMethod csCallee = csManager.getCSMethod(calleeCtx, callee);
                __processCall(csCallSite, csCallee);
            }
            return null;
        }

    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finished
        if(pointerFlowGraph.addEdge(source, target)) {
            if(!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()) {
            WorkList.Entry workSet = workList.pollEntry();
            Pointer n = workSet.pointer();
            PointsToSet pts = workSet.pointsToSet();
            PointsToSet delta = propagate(n, pts);

            if(n instanceof CSVar csVar) {
                Context ctx = csVar.getContext();
                Var var = csVar.getVar();

                for(CSObj csObj:delta) {
                    // store field
                    // x.f=y
                    for(StoreField storeField : var.getStoreFields()) {
                        Pointer left = csManager.getInstanceField(csObj, storeField.getFieldRef().resolve());
                        Pointer right = csManager.getCSVar(ctx, storeField.getRValue());
                        addPFGEdge(right, left);
                    }

                    // load field
                    // y=x.f
                    for(LoadField loadField : var.getLoadFields()) {
                        Pointer left = csManager.getCSVar(ctx, loadField.getLValue());
                        Pointer right = csManager.getInstanceField(csObj, loadField.getFieldRef().resolve());
                        addPFGEdge(right, left);
                    }

                    // store array
                    // x[*]=y
                    for(StoreArray storeArray : var.getStoreArrays()) {
                        Pointer left = csManager.getArrayIndex(csObj);
                        Pointer right = csManager.getCSVar(ctx, storeArray.getRValue());
                        addPFGEdge(right, left);
                    }

                    // load array
                    // y=x[*]
                    for(LoadArray loadArray : var.getLoadArrays()) {
                        Pointer left = csManager.getCSVar(ctx, loadArray.getLValue());
                        Pointer right = csManager.getArrayIndex(csObj);
                        addPFGEdge(right, left);
                    }

                    processCall(csVar, csObj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finished
        PointsToSet delta = PointsToSetFactory.make();
        PointsToSet target = pointer.getPointsToSet();

        for(CSObj obj:pointsToSet) {
            if(!target.contains(obj)) {
                delta.addObject(obj);
                target.addObject(obj);
            }
        }

        if(!delta.isEmpty()) {
            for(Pointer n:pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(n, delta);
            }
        }

        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        Var var = recv.getVar();
        Context ctx = recv.getContext();

        for(Invoke invoke:var.getInvokes()) {
            JMethod callee = resolveCallee(recvObj, invoke);
            CSCallSite csCallSite = csManager.getCSCallSite(ctx, invoke);
            Context ctxNew = contextSelector.selectContext(csCallSite, recvObj, callee);
            workList.addEntry(csManager.getCSVar(ctxNew, callee.getIR().getThis()), PointsToSetFactory.make(recvObj));
            __processCall(csCallSite, csManager.getCSMethod(ctxNew, callee));
        }
    }

    private void __processCall(CSCallSite csCallSite, CSMethod csMethod) {
        CallKind kind = null;
        Invoke callSite = csCallSite.getCallSite();
        if (callSite.isInterface()) kind = CallKind.INTERFACE;
        else if (callSite.isStatic()) kind = CallKind.STATIC;
        else if (callSite.isSpecial()) kind = CallKind.SPECIAL;
        else if (callSite.isVirtual()) kind = CallKind.VIRTUAL;
        else if (callSite.isDynamic()) kind = CallKind.DYNAMIC;
        if(kind == null) {return;}
        if (!callGraph.getCalleesOf(csCallSite).contains(csMethod)) {
            callGraph.addEdge(new Edge<>(kind, csCallSite, csMethod));
            addReachable(csMethod);
            List<Var> params = csMethod.getMethod().getIR().getParams();
            List<Var> args = callSite.getInvokeExp().getArgs();
            assert args.size() == params.size();
            Context callerCtx = csCallSite.getContext();
            Context calleeCtx = csMethod.getContext();

            for (int i = 0; i < args.size(); i++) {
                addPFGEdge(csManager.getCSVar(callerCtx, args.get(i)), csManager.getCSVar(calleeCtx, params.get(i)));
            }
            Var receiver = callSite.getLValue();
            if(receiver != null) {
                List<Var> rets = csMethod.getMethod().getIR().getReturnVars();
                for(Var ret:rets) {
                    addPFGEdge(csManager.getCSVar(calleeCtx, ret), csManager.getCSVar(callerCtx, receiver));
                }
            }

        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
