/**************************************************************************************************
 Copyright 2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.smt;

import charlie.smt.*;
import cora.smt.*;
import java.lang.Iterable;
import java.util.Iterator;
import java.util.ArrayList;
import java.util.List;
import java.util.HashSet;
import java.util.Set;
import java.util.Arrays;

public class InternalSolver implements SmtSolver {


  ArrayList<QVar> basis = new ArrayList<>();
  /**
   * TODO: this is the place where all the work needs to be done.
   * Figure out if we should return YES(Valuation val), NO(), or MAYBE(String reason).
   */
  public SmtSolver.Answer checkSatisfiability(SmtProblem problem){
    Constraint constraints = problem.queryCombinedConstraint();
    System.out.println(constraints);
    ArrayList<Constraint> children = getConstraints(constraints);
    ArrayList<IntegerExpression> expressions = getExpressions(children);
    System.out.println("expressions: " +expressions);
    ArrayList<QExpression> Qexpressions = convertToQExpressions(expressions);
    System.out.println (Qexpressions.toString());
    Qexpressions = simplexMethod(problem, Qexpressions);
    System.out.println ("we are done, no positive factors in obj func: " + Qexpressions.get(0));
    System.out.println ("basis: " + basis);
    
    ArrayList<QValue> solution = collectSolution(Qexpressions);
    System.out.println ("values of basis variables: " + solution);
    // if (maximalValue(constantsFinal).compareTo(new QValue(0,1)) < 0){
    //   System.out.println ("No solution since maximum value of z is: " + maximalValue(constantsFinal));
    //   return new Answer.NO();
    // }
    if (zSmallerThanZero(solution)){
      if (integerSolution(solution)){
        Valuation val = makeValuation(problem, solution); 
        return new Answer.YES(val);
        // if (extraCheck(val, expressions)){
        //   System.out.println ("valuation: " + val);
        //   return new Answer.YES(val);
        // }

      }
      else {

        // for (int i = 0; i < solution.size(); i++){
        //   if (solution.get(i).queryDenominator() != 1){
        //     System.out.println ("fraction in answer: " + q);
        //     double value = (double) solution.get(i).queryNumerator() / solution.get(i).queryDenominator();
        //     QValue roundedDown = new QValue ((int) Math.floor(value), 1);
        //     System.out.println (roundedDown);
        //     Valuation newVal = val;
        //     newVal.setInt(i, roundedDown);
        //     if (extraCheck(newVal, expressions)){
        //       System.out.println ("it now holds, val is: " + newVal);
        //     }


        //   }
        // }
        return new Answer.MAYBE("no integer solution");
      }
    }
    return new Answer.NO();

  }

  /**
   * TODO: this should return true if we can prove that the given problem is valid, and false if
   * we cannot prove validity.  Note that if we let phi be the negation of the problem (use:
   * problem.queryCombinedConstraint().negate()), then we have validity exactly if we can show that
   * phi is NOT satisfiabile.
   */
  public boolean checkValidity(SmtProblem problem) {
    return !checkSatisfiability(problem).isYes();
  }


  public ArrayList<Constraint> getConstraints (Constraint constraints){
    ArrayList<Constraint> children = new ArrayList<>();
    switch (constraints) {
      case Conjunction c: 
        for (int i = 1; i <= c.numChildren(); i++){
          children.add(c.queryChild(i));
        }
        return children;
      case Is0 i:
        children.add(i);
        return children;
      case Geq0 q:
        children.add(q);
        return children;
      default: 
        throw new Error("Expression of the form " + constraints + " not supported!");

    }
  }

  public ArrayList<IntegerExpression> getExpressions (ArrayList<Constraint> children){
    ArrayList<IntegerExpression> expressions = new ArrayList<>();
    for (int i =0; i < children.size(); i++){
      //aanpassen naar switch
      switch (children.get(i)){
        case Is0 is0: expressions.add(is0.queryExpression().simplify()); expressions.add(is0.queryExpression().negate().simplify()); break;
        case Geq0 geq0: expressions.add(geq0.queryExpression().simplify()); break;
        default: throw new Error("Expression of the form " + children.get(i).toString() + " not supported!");
      }
    }
    return expressions;
  }

  public boolean extraCheck (Valuation val, ArrayList<IntegerExpression> expressions){
    for (IntegerExpression expr : expressions){
      if (expr.evaluate(val) < 0) System.out.println (val.toString() + " does not hold for " + expr + " valuation is " + expr.evaluate(val)); return false; 
    }
    return true;
  }

  public ArrayList<QValue> collectSolution(ArrayList<QExpression> Qexpressions){
    ArrayList<QValue> constantsFinal = new ArrayList<>();
    for (int i =1; i < Qexpressions.size(); i++){
      ArrayList<QValue> constants = new ArrayList<>();
      collectConstants(constants, Qexpressions.get(i));
      constantsFinal.addAll(constants);
      if (constants.isEmpty()) constantsFinal.add(new QValue(0,1));
    }
    return constantsFinal;
  }

  public boolean zSmallerThanZero(ArrayList<QValue> constants){
    for (int i =0; i < basis.size(); i++){
      if (basis.get(i).queryName().equals("[z]")) {
        return constants.get(i).compareTo(new QValue(0,1)) < 0;
      }
    }
    return true;
  }

  public boolean integerSolution (ArrayList<QValue> solution){
    for (QValue q : solution){
      if (q.queryDenominator() != 1) return false;
    }
    return true;
  }

  public Valuation makeValuation (SmtProblem problem, ArrayList<QValue> constants){
    
    Valuation val = new Valuation();
    //first we set all variables to zero
    for (int i =0; i <= problem.numberIntegerVariables(); i++){
      val.setInt(i, 0);
    }
    //then we set basis variables to their corresponding values
    for (int i =0; i < basis.size(); i++){
      if (basis.get(i).queryIndex() <= problem.numberIntegerVariables()){
        System.out.println ("setting variable " + (basis.get(i).queryIndex())+ " to " + constants.get(i).queryNumerator() + " in valuation");
        val.setInt(basis.get(i).queryIndex()-1, constants.get(i).queryNumerator());
      }
    }
    return val;
  }


  public ArrayList<QExpression> simplexMethod (SmtProblem problem, ArrayList<QExpression> Qexpressions){
    Qexpressions = addIndividualSlackVariables(problem, Qexpressions);
    System.out.println (Qexpressions);

    QVar slackVariable = new QVar(problem.numberIntegerVariables()+ Qexpressions.size()+1, "z");
    QExpression objFunc = new QMult (new QValue(-1, 1), slackVariable);
    Qexpressions = addUniversalSlackVariable(slackVariable, Qexpressions);
    System.out.println (Qexpressions);

    //System.out.println("basis variables: " + basis);
    Qexpressions.add(0,objFunc);
    System.out.println("final expr: " +Qexpressions);
    if (!basicSolution(Qexpressions)){
      System.out.println("there is no basic solution");
      Qexpressions = findBasicSolution(Qexpressions, slackVariable);
      Qexpressions = removingZeroExpressions(Qexpressions);
      System.out.println("new expr: " + Qexpressions);
    }
    else{
      return Qexpressions;
    }
    if (basicSolution(Qexpressions)){
      System.out.println ("we have a basic solution");
      //for (int i =0; i < 10; i++){
      while (positiveFactor(Qexpressions.get(0))){
        System.out.println("positive factor present");
        QVar swap = findPositiveFactor(Qexpressions.get(0), problem);
        if (!(swap.queryName()=="temp")){
          System.out.println("we found a variable with positive factor: " + swap);
          QExpression newExpr = findMinBound(Qexpressions, swap);
          System.out.println ("expr with min bound: "+newExpr);
          Qexpressions = pivot(swap, newExpr, Qexpressions);
          Qexpressions = removingZeroExpressions(Qexpressions);
          System.out.println("removed zero expressions: " + Qexpressions);
        }
      }
    }
    return Qexpressions;
  }

  public ArrayList<QValue> removeZeros (ArrayList<QValue> list){
    for (int i =0; i < list.size(); i++){
      if (list.get(i).queryNumerator() == 0){
        list.remove(i);
        i--;
      }
    }
    return list;
  }

  public ArrayList<QExpression> convertToQExpressions (ArrayList<IntegerExpression> expressions){
    ArrayList<QExpression> Qexpressions = new ArrayList<>();
    for (IntegerExpression expr : expressions){
      Qexpressions.add(convert(expr));
    }
    return Qexpressions;
  }


  public QValue convertIntToQ(int i){
    return new QValue(i, 1);
  }

  public QExpression convert(IntegerExpression expr) {
    switch (expr) {
      case IVar x: return new QVar(x.queryIndex(), x.queryName());
      case IValue v: return new QValue(v.queryValue(), 1);
      case CMult cm:
        return new QMult(convertIntToQ(cm.queryConstant()), convert(cm.queryChild()));
      case Addition a:
        List<QExpression> list = new ArrayList<>();
        for (int i = 1; i <= a.numChildren(); i++) list.add(convert(a.queryChild(i)));
        return new QAddition(list);
      default:
        throw new Error("Expression of the form " + expr.toString() + " not supported!");
    }
  } 

  public QExpression findMinBound (ArrayList<QExpression> expressions, QVar swap){
    //return expr in which variable swap is most bound by so has to be the lowest for
    ArrayList<QValue> constants = new ArrayList<>();
    collectConstants(constants, expressions.get(1));
    QValue total = new QValue(0,1);
    for (QValue constant: constants){
      total = total.add(constant);
    }
    int boundedIndex = 1;
    while (getCount(swap, expressions.get(boundedIndex)).queryNumerator()==0 || divide(total, getCount(swap, expressions.get(boundedIndex))).compareTo(new QValue(0,1)) > 0){
      boundedIndex++;
    }
    QExpression minBound = divide(total, getCount(swap, expressions.get(boundedIndex)));
    System.out.println ("bound found for " + expressions.get(1) + " is " + minBound + ", minbound of class" + minBound.getClass());
    QExpression bounded = expressions.get(boundedIndex);
    for (int i = 2; i < expressions.size(); i++){
      constants.clear();
      collectConstants(constants, expressions.get(i));
      total = new QValue(0,1);
      for (QValue constant: constants){
        total = total.add(constant);      
      }
      if (getCount(swap, expressions.get(i)).queryNumerator() != 0){
        //System.out.println ("bound found for " + expressions.get(i) + " is " + divide(total, getCount(swap, expressions.get(i))));
        if (divide(total, getCount(swap, expressions.get(i))) instanceof QValue q){
          System.out.println ("minbound for " + swap + " in " + expressions.get(i) + " is " + divide(total, getCount(swap, expressions.get(i))));
          if (q.compareTo(minBound) > 0 && q.compareTo(new QValue(0,1))< 0) {
            minBound = q;
            bounded = expressions.get(i);
            boundedIndex = i-2;
            //System.out.println("found new minBound " + q + " setting basis min bound index to " + boundedIndex);
          }
        }
      }
    }
    System.out.println ("setting index " + boundedIndex+" in basis to "+swap.queryName() );
    //basis.set(boundedIndex, swap.queryName());

    return bounded;
  }

  public boolean positiveFactor (QExpression objFunc){
    switch (objFunc) {
      case QVar x: return true;
      case QValue v: return false;
      case QMult cm: return cm.queryConstant().queryNumerator() > 0;
      case QAddition a: return positiveFactor(a.queryChild(1)) || positiveFactor(new QAddition(a, a.queryChild(1).negate()).simplify());
      default: return false;     
    }
  }

  public QVar findPositiveFactor (QExpression expression, SmtProblem problem) {
    switch (expression){
      case QVar x: return x;
      case QMult cm: 
        if (cm.queryConstant().queryNumerator() > 0) {
          return findPositiveFactor(cm.queryChild(), problem);
        }
        return new QVar (100, "temp");
      case QAddition a: 
        if (positiveFactor(a.queryChild(1))){
          return findPositiveFactor(a.queryChild(1), problem);
        }
        return findPositiveFactor(new QAddition(a, a.queryChild(1).negate()).simplify(), problem);
      default: return new QVar (100, "temp");
    }
  }

  public ArrayList<QExpression> findBasicSolution (ArrayList<QExpression> expressions, QVar slackVariable){
    ArrayList<QValue> list = new ArrayList<>();
    System.out.println ("finding constants in expressions: "+ expressions);
    for (int i =1; i < expressions.size(); i++){
      collectConstants(list, expressions.get(i));
    }
    System.out.println ("constants: " + list);
    QValue lowestConstant = list.get(0);
    int lowestConstantIndex = 0;
    for (int i =1; i < list.size(); i++){
      if (list.get(i).compareTo(lowestConstant)<0){
        lowestConstant = list.get(i);
        lowestConstantIndex = i;
      }
    }  
    System.out.println ("expression with lowest constant: " + expressions.get(lowestConstantIndex+1));
    System.out.println ("basis: " + basis);
    return pivot (slackVariable, expressions.get(lowestConstantIndex+1), expressions);
  }

  public ArrayList<QExpression> pivot (QVar swap, QExpression newExpr, ArrayList<QExpression> expressions){
    // find variable in newExpr and swap with that  
    QValue count = getCount(swap, newExpr);
    System.out.println ("found count " + count + "of " + swap + " in " + newExpr);
    QExpression remove = new QMult(count, swap);
    newExpr = new QAddition (remove.negate(), newExpr).negate().simplify();
    System.out.println(newExpr);
    newExpr = divide(newExpr, count).simplify();
    //FIX LATER WHY SIMPLIFY AGAIN AFTER DIVIDE
    System.out.println("we are swapping " + swap + " with " + newExpr.toString());
    for (int i =0; i < expressions.size(); i++){
      QExpression newExpression = replace (expressions.get(i), swap, newExpr);
      if (newExpression instanceof QValue q){
        System.out.println ("found qvalue in expressions: " + q + "removing basis value: " + basis.get(i-1));
        basis.remove(i-1);
      }
      expressions.set(i,newExpression);
    }
    newExpr = addTerms(newExpr, new QMult(new QValue(-1,1), swap));
    expressions.add(1, newExpr);
    basis.add(0, swap);
    System.out.println("basis: " + basis);
    return expressions;

  }


  public QExpression divide (QExpression expr, QValue count){
    if (count.queryNumerator()==0){
      throw new IllegalArgumentException("We cannot divide by zero.");
    }
    switch (expr) {
      case QVar x: 
      if (getCount(x,expr).queryNumerator() == getCount(x,expr).queryDenominator()){
        return new QMult(count.simplify(new QValue(1,1),count), x);
      }
      return x; 
      case QValue v: 
        return count.simplify(v,count);
      case QMult cm: return new QMult((QValue)divide(cm.queryConstant(), count),cm.queryChild());
      case QAddition a:
        QAddition divided = new QAddition(new QValue(0,1), new QValue(0,1));
        for (int i = 1; i <= a.numChildren(); i++) divided = addTerms(divided, divide(a.queryChild(i), count));
        return divided;
      default:
        throw new Error("Expression of the form " + expr.toString() + " not supported!");
    }

  }

  public QAddition addTerms(QExpression expr1, QExpression expr2) {
    return new QAddition (expr1, expr2);
  }

  public ArrayList<QExpression> removingZeroExpressions (ArrayList<QExpression> expressions){
    for (int i =0; i < expressions.size(); i++){
      if (expressions.get(i) instanceof QValue q){
        if (q.queryNumerator()==0){
          expressions.remove(i);
          i--;
        }
      }
    }
    return expressions;
  }

  public QExpression replace (QExpression expr, QVar oldVar, QExpression newExpr){
    //replace oldVar in expr for newExpr
    switch (expr) {
      case QVar x: if (x == oldVar){
        return newExpr; 
      } else {
        return x;
      }
      case QValue v: return v;
      case QMult cm: return new QMult(cm.queryConstant(), replace(cm.queryChild(), oldVar, newExpr)).simplify();
      case QAddition a:
        return new QAddition (replace(a.queryChild(1), oldVar, newExpr), replace(new QAddition(a, a.queryChild(1).negate().simplify()).simplify(), oldVar, newExpr)).simplify();
      default:
        throw new Error("Expression of the form " + expr.toString() + " not supported!");
    }
  }

  public boolean basicSolution (ArrayList<QExpression> expressions){
    //returns true if there is a basic solution
    ArrayList<QValue> list = new ArrayList<>();
    for (int i =1; i < expressions.size(); i++){
      collectConstants(list, expressions.get(i));
    }
    for (QValue constant : list){
      if (constant.queryNumerator() < 0){
        System.out.println("i have found constant < 0 : " + constant);
        return false;
      }
    }
    return true;
  }

  public ArrayList<QExpression> addUniversalSlackVariable (QVar slackVariable, ArrayList<QExpression> expressions){
    for (int i =0; i < expressions.size(); i++){
      expressions.set(i ,new QAddition (slackVariable, expressions.get(i)));
    }
    //expressions.add(SmtFactory.createMultiplication(SmtFactory.createValue(-1), slackVariable).simplify());

    return expressions;
  }



  public ArrayList<QExpression> addIndividualSlackVariables (SmtProblem problem, ArrayList<QExpression> expressions){
    //with coefficient -1, not sure if thats correct
    int index = problem.numberIntegerVariables()+1;
    //ArrayList<QVar> slackVariables = new ArrayList<>();
    for (int i =0; i < expressions.size(); i++){
      QVar slackVariable = new QVar(index, "y"+(i+1));
      index++;
      basis.add(slackVariable);
      expressions.set(i, new QAddition(expressions.get(i), new QMult(new QValue(-1,1), slackVariable)));
      //slackVariables.add(slackVariable);
    }
    //for (QVar v : slackVariables) expressions.add(v);
    return expressions;
  }

  public void collectVariables(Set<IVar> vars, IntegerExpression expr) {
    switch (expr) {
      case IVar x: vars.add(x); return;
      case IValue v: return;
      case CMult cm:
        if (cm.queryChild() instanceof IVar x) vars.add(x);
        else throw new Error("This won't work if we mutliply constants by things other than variables!");
        return;
      case Addition a:
        for (int i = 1; i <= a.numChildren(); i++) collectVariables(vars, a.queryChild(i));
        return;
      default:
        throw new Error("Expression of the form " + expr.toString() + " not supported!");
    }
  }

  QValue getCount(QVar x, QExpression expr) {
    switch(expr) {
      case QVar y: if (x.equals(y)) return new QValue(1,1); else return new QValue(0,1);
      case QValue v: return new QValue(0,1);
      case QMult cm: if (cm.queryChild().equals(x)) return cm.queryConstant(); else return new QValue(0,1);
      case QAddition a:
        for (int i = 1; i <= a.numChildren(); i++) {
          QValue tmp = getCount(x, a.queryChild(i));
          if (tmp.queryNumerator() != 0) return tmp;
        }
        return new QValue(0,1);
      default: throw new Error("expression does not have the expected shape!");
    }
  }

  public void collectConstants(ArrayList<QValue> list, QExpression expr){
    switch (expr) {
      case QVar x: return;
      case QValue v: list.add(v);return;
      case QMult cm: return;
      case QAddition a:
        for (int i = 1; i <= a.numChildren(); i++) collectConstants(list, a.queryChild(i));
        return;
      default:
        throw new Error("Expression of the form " + expr.toString() + " not supported!");
    }
  }

}