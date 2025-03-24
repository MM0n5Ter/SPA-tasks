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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finished
        // Your task is to recognize dead code in ir and add it to deadCode

        LinkedList<Stmt> stmts = new LinkedList<>();
        Set<Stmt> reachableStmts = new HashSet<>();
        Set<Stmt> visitedStmts = new HashSet<>();
        stmts.add(cfg.getEntry());

        reachableStmts.add(cfg.getEntry());
        reachableStmts.add(cfg.getExit());

        while (!stmts.isEmpty()) {
            Stmt stmt = stmts.pop();
            if (!visitedStmts.contains(stmt)) {
                visitedStmts.add(stmt);
                if (stmt instanceof AssignStmt assignStmt) {
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                        stmts.add(edge.getTarget());
                    }

                    if (!(assignStmt.getLValue() instanceof Var var && !liveVars.getResult(assignStmt).contains(var) && hasNoSideEffect(assignStmt.getRValue())))
                        reachableStmts.add(stmt);

                } else if (stmt instanceof If ifStmt) {
                    reachableStmts.add(stmt);
                    ConditionExp conditionStmt = ifStmt.getCondition();
                    Value eval = ConstantPropagation.evaluate(conditionStmt, constants.getResult(ifStmt));
                    if (eval.isConstant()) {
                        Edge.Kind targetKind = eval.getConstant() == 1 ? Edge.Kind.IF_TRUE : Edge.Kind.IF_FALSE;
                        for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                            if (edge.getKind() == targetKind)
                                stmts.add(edge.getTarget());
                        }
                    } else {
                        for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                            stmts.add(edge.getTarget());
                        }
                    }
                } else if (stmt instanceof SwitchStmt switchStmt) {
                    reachableStmts.add(stmt);
                    Value eval = ConstantPropagation.evaluate(switchStmt.getVar(), constants.getResult(switchStmt));
                    if (eval.isConstant()) {
                        boolean matched = false;
                        for (Edge<Stmt> edge : cfg.getOutEdgesOf(switchStmt)) {
                            if (edge.getKind() == Edge.Kind.SWITCH_CASE && edge.getCaseValue() == eval.getConstant()) {
                                matched = true;
                                stmts.add(edge.getTarget());
                            }
                        }
                        if (!matched) {
                            Stmt defaultStmt = switchStmt.getDefaultTarget();
                            stmts.add(defaultStmt);
                        }
                    } else {
                        for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                            stmts.add(edge.getTarget());
                        }
                    }
                } else {
                    reachableStmts.add(stmt);
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                        stmts.add(edge.getTarget());
                    }
                }
            }
        }

        for (Stmt stmt : cfg.getNodes()) {
            if (!reachableStmts.contains(stmt)) {
                deadCode.add(stmt);
            }
        }
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
