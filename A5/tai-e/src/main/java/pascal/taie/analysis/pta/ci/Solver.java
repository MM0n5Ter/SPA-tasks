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

package pascal.taie.analysis.pta.ci;

import fj.P;
import jdk.jshell.VarSnippet;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finished
        if(callGraph.addReachableMethod(method)) {
            for(Stmt stmt:method.getIR().getStmts()) {
                // System.out.println(stmt);
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            Pointer x = pointerFlowGraph.getVarPtr(stmt.getLValue());
            workList.addEntry(x, new PointsToSet(heapModel.getObj(stmt)));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Pointer left = pointerFlowGraph.getVarPtr(stmt.getLValue());
            Pointer right = pointerFlowGraph.getVarPtr(stmt.getRValue());
            addPFGEdge(right, left);
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if(stmt.isStatic()) {
                Pointer left = pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
                Pointer right = pointerFlowGraph.getVarPtr(stmt.getRValue());
                addPFGEdge(right, left);
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if(stmt.isStatic()) {
                Pointer left = pointerFlowGraph.getVarPtr(stmt.getLValue());
                Pointer right = pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(right, left);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod callee = resolveCallee(null, stmt);
                __processCall(stmt, callee);
            }
            return null;
        }
    }

    // r=x.m(a1, a2, a3)
    private void __processCall(Invoke callSite, JMethod callee) {
        if (!callGraph.getCalleesOf(callSite).contains(callee)) {
            CallKind kind = null;
            if (callSite.isInterface()) kind = CallKind.INTERFACE;
            else if (callSite.isStatic()) kind = CallKind.STATIC;
            else if (callSite.isSpecial()) kind = CallKind.SPECIAL;
            else if (callSite.isVirtual()) kind = CallKind.VIRTUAL;
            else if (callSite.isDynamic()) kind = CallKind.DYNAMIC;
            if (kind != null) {
                callGraph.addEdge(new Edge<>(kind, callSite,callee));
                addReachable(callee);
                List<Var> params = callee.getIR().getParams();
                List<Var> args = callSite.getInvokeExp().getArgs();
                assert args.size() == params.size();
                for (int i = 0; i < args.size(); i++) {
                    addPFGEdge(pointerFlowGraph.getVarPtr(args.get(i)), pointerFlowGraph.getVarPtr(params.get(i)));
                }
                Var receiver = callSite.getLValue();
                if(receiver != null) {
                    List<Var> rets = callee.getIR().getReturnVars();
                    for(Var ret:rets) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(receiver));
                    }
                }
            }
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

            if(n instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();
                for(Obj obj:delta) {
                    // store field
                    // x.f=y
                    for(StoreField storeField : var.getStoreFields()) {
                        Pointer left = pointerFlowGraph.getInstanceField(obj, storeField.getFieldRef().resolve());
                        Pointer right = pointerFlowGraph.getVarPtr(storeField.getRValue());
                        addPFGEdge(right, left);
                    }

                    // load field
                    // y=x.f
                    for(LoadField loadField : var.getLoadFields()) {
                        Pointer left = pointerFlowGraph.getVarPtr(loadField.getLValue());
                        Pointer right = pointerFlowGraph.getInstanceField(obj, loadField.getFieldRef().resolve());
                        addPFGEdge(right, left);
                    }

                    // store array
                    // x[*]=y
                    for(StoreArray storeArray : var.getStoreArrays()) {
                        Pointer left = pointerFlowGraph.getArrayIndex(obj);
                        Pointer right = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                        addPFGEdge(right, left);
                    }

                    // load array
                    // y=x[*]
                    for(LoadArray loadArray : var.getLoadArrays()) {
                        Pointer left = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                        Pointer right = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(right, left);
                    }

                    processCall(var, obj);
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
        PointsToSet delta = new PointsToSet();

        for(Obj obj:pointsToSet) {
            if(!pointer.getPointsToSet().contains(obj)) {
                pointer.getPointsToSet().addObject(obj);
                delta.addObject(obj);
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
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finished
        for(Invoke invoke:var.getInvokes()) {
            JMethod callee = resolveCallee(recv, invoke);
            workList.addEntry(pointerFlowGraph.getVarPtr(callee.getIR().getThis()), new PointsToSet(recv));
            __processCall(invoke, callee);
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
