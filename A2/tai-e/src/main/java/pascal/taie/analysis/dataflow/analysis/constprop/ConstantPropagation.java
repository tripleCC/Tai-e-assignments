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

import pascal.taie.Assignment;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

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
        // must analysis
        // 除了参数，其他都是 undef
        CPFact fact = new CPFact();
        for (Var var : cfg.getIR().getParams()) {
            if (canHoldInt(var)) {
                // 参数未知，保守 NAC
                fact.update(var, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // undef -> nac or con
        CPFact fact = new CPFact();
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // 这里应用用 fact 来索引，而不是 target
        for (Var var : fact.keySet()) {
            Value tv = target.get(var);
            Value fv = fact.get(var);
            target.update(var, meetValue(tv, fv));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isUndef() || v2.isUndef()) {
            return v1.isUndef() ? v2 : v1;
        } else if (v1.isConstant() && v2.isConstant()) {
            if (v1.getConstant() == v2.getConstant()) {
                return Value.makeConstant(v1.getConstant());
            } else {
                return Value.getNAC();
            }
        }
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact newIn = in.copy();

        if (stmt instanceof DefinitionStmt) {
            DefinitionStmt ds = (DefinitionStmt)stmt;
            if (ds.getDef().isPresent()) {
                LValue lval = ds.getDef().get();
                if (lval instanceof Var) {
                    Var var = (Var)lval;
                    if (canHoldInt(var)) {
                        RValue rval = ds.getRValue();
                        if (rval instanceof Exp) {
                            Exp e = (Exp)rval;
                            // var 为 y 时，in 不应该为空 （meet 出了问题？）
                            Value val = evaluate(e, newIn);
                            // 这里的 update 已经有 (IN[s] – {(x, _)} 中 kill 的含义
                            newIn.update(var, val);
                        } else {
                            newIn.update(var, Value.getNAC());
                        }
                    }
                }
            }
        }

        if (newIn.equals(out)) {
            return false;
        } else {
            out.copyFrom(newIn);
            return true;
        }
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
        if (exp instanceof IntLiteral) {
            IntLiteral il = (IntLiteral)exp;
            return Value.makeConstant(il.getValue());
        } else if (exp instanceof Var) {
            Var var = (Var)exp;
            Value value = in.get(var);
            return value;
        } else if (exp instanceof BinaryExp) {
            BinaryExp be = (BinaryExp)exp;
            Value v1 = in.get(be.getOperand1());
            Value v2 = in.get(be.getOperand2());
            if (v1.isNAC() || v2.isNAC()) {
                return Value.getNAC();
            }

            if (v1.isConstant() && v2.isConstant()) {
                int i1 = v1.getConstant();
                int i2 = v2.getConstant();
                if (exp instanceof ArithmeticExp) {
                    ArithmeticExp e = (ArithmeticExp)be;
                    switch (e.getOperator()) {
                        case ADD -> {
                            return Value.makeConstant(i1 + i2);
                        }
                        case SUB -> {
                            return Value.makeConstant(i1 - i2);
                        }
                        case MUL -> {
                            return Value.makeConstant(i1 * i2);
                        }
                        case DIV -> {
                            if (v2.getConstant() == 0) {
                                return Value.getUndef();
                            }
                            return Value.makeConstant(i1 / i2);
                        }
                        case REM -> {
                            if (v2.getConstant() == 0) {
                                return Value.getUndef();
                            }
                            return Value.makeConstant(i1 % i2);
                        }
                    }
                } else if (exp instanceof ConditionExp) {
                    ConditionExp e = (ConditionExp)exp;
                    switch (e.getOperator()) {
                        case EQ -> {
                            return Value.makeConstant(i1 == i2 ? 1 : 0);
                        }
                        case GE -> {
                            return Value.makeConstant(i1 >= i2 ? 1 : 0);
                        }
                        case GT -> {
                            return Value.makeConstant(i1 > i2 ? 1 : 0);
                        }
                        case LE ->
                        {
                            return Value.makeConstant(i1 <= i2 ? 1 : 0);
                        }
                        case LT -> {
                            return Value.makeConstant(i1 < i2 ? 1 : 0);
                        }
                        case NE -> {
                            return Value.makeConstant(i1 != i2 ? 1 : 0);
                        }
                    }
                } else if (exp instanceof ShiftExp) {
                    ShiftExp e = (ShiftExp)exp;
                    switch (e.getOperator()) {
                        case SHL -> {
                            return Value.makeConstant(i1 << i2);
                        }
                        case SHR -> {
                            return Value.makeConstant(i1 >> i2);
                        }
                        case USHR -> {
                            return Value.makeConstant(i1 >>> i2);
                        }
                    }
                } else if (exp instanceof BitwiseExp) {
                    BitwiseExp e = (BitwiseExp)exp;
                    switch (e.getOperator()) {
                        case OR -> {
                            return Value.makeConstant(i1 | i2);
                        }
                        case AND -> {
                            return Value.makeConstant(i1 & i2);
                        }
                        case XOR -> {
                            return Value.makeConstant(i1 ^ i2);
                        }
                    }
                }
            }

            return Value.getUndef();
        }

        return Value.getNAC();
    }
}
