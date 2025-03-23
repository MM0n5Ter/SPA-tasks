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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;
import java.util.Optional;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finished
        CPFact boundary =  new CPFact();
        for(Var var : cfg.getIR().getParams()) {
            if(canHoldInt(var)) {
                boundary.update(var, Value.getNAC());
            }
        }
        return boundary;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finished
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for(Var var: fact.keySet()) {
            target.update(var, meetValue(target.get(var), fact.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finished
        if(v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if(v1.isUndef()) {
            return v2;
        } else if(v2.isUndef()) {
            return v1;
        } else if(v1.equals(v2)){
            return v1;
        } else {
            return Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finished
        if(stmt instanceof DefinitionStmt<?,?> definitionStmt) {
           LValue lValue = definitionStmt.getLValue();
           if(lValue instanceof Var gen && canHoldInt(gen)) {
               Value res = evaluate(definitionStmt.getRValue(), in);
               CPFact newFact = in.copy();
               newFact.update(gen, res);
               return out.copyFrom(newFact);
           }
        }

        return out.copyFrom(in);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finished
        if(exp instanceof Var var) {
            return in.get(var);
        }
        if(exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }
        if(exp instanceof BinaryExp binaryExp) {
            Value v1 = in.get(binaryExp.getOperand1());
            Value v2 = in.get(binaryExp.getOperand2());

            if ((binaryExp.getOperator() == ArithmeticExp.Op.DIV ||
                    binaryExp.getOperator() == ArithmeticExp.Op.REM) &&
                    v2.isConstant() && v2.getConstant() == 0)
                return Value.getUndef();

            if (v1.isNAC() || v2.isNAC())
                return Value.getNAC();

            if (v1.isConstant() && v2.isConstant()) {
                return BinaryEvaluate(v1, v2, binaryExp.getOperator());
            }

            return Value.getUndef();
        }

        return Value.getNAC();
    }

    public static Value BinaryEvaluate(Value v1, Value v2, BinaryExp.Op op) {
        int para1 = v1.getConstant();
        int para2 = v2.getConstant();

        if (op instanceof ArithmeticExp.Op op1) {
            return switch (op1) {
                case ADD -> Value.makeConstant(para1 + para2);
                case SUB -> Value.makeConstant(para1 - para2);
                case MUL -> Value.makeConstant(para1 * para2);
                case DIV -> Value.makeConstant(para1 / para2);
                case REM -> Value.makeConstant(para1 % para2);
            };
        }

        if (op instanceof BitwiseExp.Op op1) {
            return switch (op1) {
                case AND -> Value.makeConstant(para1 & para2);
                case OR -> Value.makeConstant(para1 | para2);
                case XOR -> Value.makeConstant(para1 ^ para2);
            };
        }

        if (op instanceof ConditionExp.Op op1) {
            return switch (op1) {
                case EQ -> Value.makeConstant(para1 == para2 ? 1 : 0);
                case NE -> Value.makeConstant(para1 != para2 ? 1 : 0);
                case GE -> Value.makeConstant(para1 >= para2 ? 1 : 0);
                case GT -> Value.makeConstant(para1 > para2 ? 1 : 0);
                case LE -> Value.makeConstant(para1 <= para2 ? 1 : 0);
                case LT -> Value.makeConstant(para1 < para2 ? 1 : 0);
            };
        }

        if (op instanceof ShiftExp.Op op1) {
            return switch (op1) {
                case SHL -> Value.makeConstant(para1 << para2);
                case SHR -> Value.makeConstant(para1 >> para2);
                case USHR -> Value.makeConstant(para1 >>> para2);
            };
        }

        return Value.getNAC();
    }
}
