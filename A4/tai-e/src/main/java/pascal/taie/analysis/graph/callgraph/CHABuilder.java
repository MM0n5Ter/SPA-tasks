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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallKind getCallKind(Invoke callSite) {
        if (callSite.isVirtual()) {
            return CallKind.VIRTUAL;
        } else if (callSite.isStatic()) {
            return CallKind.STATIC;
        } else if (callSite.isInterface()) {
            return CallKind.INTERFACE;
        } else if (callSite.isSpecial()) {
            return CallKind.SPECIAL;
        } else if (callSite.isDynamic()) {
            return CallKind.DYNAMIC;
        }
        return null;
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finished
        ArrayDeque<JMethod> workList = new ArrayDeque<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod current = workList.removeFirst();
            if (!callGraph.contains(current)) {
                callGraph.addReachableMethod(current);
                for(Invoke callSite : callGraph.getCallSitesIn(current)) {
                    CallKind kind = getCallKind(callSite);
                    if (kind == null) { continue; }
                    for(JMethod jMethod : resolve(callSite)) {
                        if(jMethod == null) { continue; }
                        callGraph.addEdge(new Edge<>(kind, callSite, jMethod));
                        workList.add(jMethod);
                    }
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finished
        Set<JMethod> methods = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        Subsignature subsignature = methodRef.getSubsignature();
        if(callSite.isStatic()){
            methods.add(methodRef.getDeclaringClass().getDeclaredMethod(subsignature));

        } else if (callSite.isSpecial()) {
            JMethod res = dispatch(methodRef.getDeclaringClass(), subsignature);
            if(res != null){ methods.add(res); }

        } else if (callSite.isVirtual() || callSite.isInterface()) {
            ArrayDeque<JClass> classes = new ArrayDeque<>();
            classes.add(methodRef.getDeclaringClass());
            while(!classes.isEmpty()){
                JClass clazz = classes.removeFirst();
                JMethod method = dispatch(clazz, subsignature);
                if(method != null){ methods.add(method); }

                if (clazz.isInterface()) {
                    classes.addAll(hierarchy.getDirectImplementorsOf(clazz));
                    classes.addAll(hierarchy.getDirectSubinterfacesOf(clazz));
                } else {
                    classes.addAll(hierarchy.getDirectSubclassesOf(clazz));
                }
            }

        }
        return methods;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finished
        JMethod result = jclass.getDeclaredMethod(subsignature);
        if(result != null && !result.isAbstract()){
            return result;
        } else {
            if(jclass.getSuperClass() != null){ return dispatch(jclass.getSuperClass(), subsignature); }
            return null;
        }
    }
}
