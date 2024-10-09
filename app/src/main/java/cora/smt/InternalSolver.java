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
    QVar slackVariable = new QVar(problem.numberIntegerVariables()+ Qexpressions.size()+1, "z");
    Qexpressions = addSlackVariables(slackVariable, problem, Qexpressions);
    Qexpressions = simplexMethod(Qexpressions, slackVariable);
    System.out.println ("we are done, no positive factors in obj func: " + Qexpressions.get(0));
    System.out.println ("basis: " + basis);
    
    ArrayList<QValue> solution = collectSolution(Qexpressions);
    System.out.println ("values of basis variables: " + solution);
    if (zSmallerThanZero(solution)){
      if (integerSolution(solution)){
        Valuation val = makeValuation(problem, solution); 
        //return new Answer.YES(val);
        if (extraCheck(val, expressions)){
          System.out.println ("valuation: " + val);
          return new Answer.YES(val);
        }
        return new Answer.MAYBE("something went wrong in simplex method.");
      }
      else {
        // Qexpressions.add(addExpression(solution, slackVariable));
        // System.out.println ("no int solution, so added expr: " + Qexpressions);
        // Qexpressions = simplexMethod(Qexpressions);
        // System.out.println ("basis: " + basis);
        // solution = collectSolution(Qexpressions);
        // System.out.println ("values of basis variables: " + solution);

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

  public QExpression addExpression (ArrayList<QValue> solution, QVar slackVariable){
    int index = 0;
    while (solution.get(index).queryDenominator() == 1){
      index++;
    }
    QValue fraction = solution.get(index);
    double fractionDouble = (double) fraction.queryNumerator()/fraction.queryDenominator();
    int roundedUp = (int) Math.ceil(fractionDouble);
    System.out.println (fraction + " rounded up is " + roundedUp);
    QVar x = basis.get(index);
    return new QAddition(new ArrayList<QExpression>(Arrays.asList(new QValue(roundedUp, 1).multiply(new QValue(-1,1)), basis.get(index), slackVariable)));
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

  public ArrayList<QExpression> addSlackVariables (QVar slackVariable, SmtProblem problem, ArrayList<QExpression> Qexpressions){
    Qexpressions = addIndividualSlackVariables(problem, Qexpressions);
    System.out.println (Qexpressions);
    QExpression objFunc = new QMult (new QValue(-1, 1), slackVariable);
    Qexpressions = addUniversalSlackVariable(slackVariable, Qexpressions);
    System.out.println (Qexpressions);

    //System.out.println("basis variables: " + basis);
    Qexpressions.add(0,objFunc);
    return Qexpressions;
  }

  public boolean extraCheck (Valuation val, ArrayList<IntegerExpression> expressions){
    for (IntegerExpression expr : expressions){
      if (expr.evaluate(val) < 0){
        System.out.println (val.toString() + " does not hold for " + expr + " valuation is " + expr.evaluate(val)); 
        return false; 
      }
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
        val.setInt(basis.get(i).queryIndex(), constants.get(i).queryNumerator());
      }
    }
    return val;
  }

  public ArrayList<QExpression> simplexMethod (ArrayList<QExpression> Qexpressions, QVar slackVariable){
    System.out.println("final expr: " +Qexpressions);
    while (!basicSolution(Qexpressions)){
      System.out.println("there is no basic solution");
      Qexpressions = pivot (slackVariable, exprWithLowestConstant(Qexpressions), Qexpressions);
      Qexpressions = removingZeroExpressions(Qexpressions);
      System.out.println("new expr: " + Qexpressions);
      while (positiveFactor(Qexpressions.get(0))){
        System.out.println("positive factor present");
        QVar swap = findPositiveFactor(Qexpressions.get(0));
        System.out.println("we found a variable with positive factor: " + swap);
        QExpression newExpr = findMinBound(Qexpressions, swap);
        System.out.println ("expr with min bound: "+newExpr);
        Qexpressions = pivot(swap, newExpr, Qexpressions);
        Qexpressions = removingZeroExpressions(Qexpressions);
        System.out.println("removed zero expressions: " + Qexpressions);
      }
    }
    return Qexpressions;
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
    int index = 1;
    QValue count = getCount(swap, expressions.get(index));
    ArrayList<QValue> constants = new ArrayList<>();
    collectConstants(constants, expressions.get(index));
    System.out.println (expressions);
    while (count.compareTo(new QValue(0,1)) >= 0 || constants.size()==0 || constants.get(0).compareTo(new QValue(0,1))<0 ){
      constants.clear();
      index++;
      if (index >= expressions.size()){
        throw new Error("No minimum bound for "+ swap);
      }
      count = getCount(swap, expressions.get(index));
      collectConstants(constants, expressions.get(index));
    }
    System.out.println ("first expr with negative coefficient: " + expressions.get(index));
    collectConstants(constants, expressions.get(index));
    System.out.println ("dividing "+ constants.get(0)+ " and " + count);
    QValue minBound = (QValue)divide(constants.get(0),count).multiply(new QValue(-1,1));
    System.out.println ("min bound for " + expressions.get(index)+ " is " + minBound);
    for (int i = index+1; i <expressions.size(); i++){
      System.out.println ("looking at expr: " + expressions.get(i));

      count = getCount(swap, expressions.get(i));
      System.out.println (swap + " count is: " + count);
      if (count.compareTo(new QValue(0,1)) < 0){
        System.out.println ("count is smaller than 0");
        constants.clear();
        collectConstants(constants, expressions.get(i));
        if (constants.size() > 0 && constants.get(0).compareTo(new QValue(0,1))>0 && divide(constants.get(0),count).multiply(new QValue(-1,1)).compareTo(minBound)<0){
          minBound = (QValue)divide(constants.get(0),count).multiply(new QValue(-1,1));
          System.out.println ("min bound for " + expressions.get(i)+ " is " + minBound);
          index = i;
        }
      }
    }
    System.out.println ("expression with min bound: " + expressions.get(index));
    return expressions.get(index);
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

  public QVar findPositiveFactor (QExpression expression) {
    switch (expression){
      case QVar x: return x;
      case QMult cm: 
        if (cm.queryConstant().queryNumerator() > 0) {
          return findPositiveFactor(cm.queryChild());
        }
        return new QVar (100, "temp");
      case QAddition a: 
        if (positiveFactor(a.queryChild(1))){
          return findPositiveFactor(a.queryChild(1));
        }
        return findPositiveFactor(new QAddition(a, a.queryChild(1).negate()).simplify());
      default: throw new Error("There is no positive factor in " + expression);
    }
  }

  public QExpression exprWithLowestConstant (ArrayList<QExpression> expressions){
    //you can assume there exists an expression in expressions with a constant < 0, because we do not have a basic solution
    ArrayList<QValue> list = new ArrayList<>();
    QValue lowestConstant = new QValue (0,1);
    QExpression expression = expressions.get(0);
    for (int i =1; i < expressions.size(); i++){
      collectConstants(list, expressions.get(i));
      if (!list.isEmpty() && list.get(0).compareTo(lowestConstant) < 0){
        lowestConstant = list.get(0);
        expression = expressions.get(i);
      }
      list.clear();
    }
    return expression;
  }

  public ArrayList<QExpression> pivot (QVar swap, QExpression newExpr, ArrayList<QExpression> expressions){
    // find variable in newExpr and swap with that  
    QValue count = getCount(swap, newExpr);
    System.out.println ("found count " + count + "of " + swap + " in " + newExpr);
    QExpression remove = new QMult(count, swap);
    System.out.println (remove.negate());
    newExpr = new QAddition (remove.negate(), newExpr).negate().simplify();
    System.out.println(newExpr);
    newExpr = divide(newExpr, count).simplify();
    //FIX LATER WHY SIMPLIFY AGAIN AFTER DIVIDE
    System.out.println("we are swapping " + swap + " with " + newExpr.toString());
    for (int i =0; i < expressions.size(); i++){
      System.out.println("replacing for: " + expressions.get(i));
      QExpression newExpression = replace (expressions.get(i), swap, newExpr);
      if (newExpression instanceof QValue q){
        System.out.println ("found qvalue in expressions: " + q + "removing basis value: " + basis.get(i-1));
        basis.remove(i-1);
      }
      expressions.set(i,newExpression);
    }
    System.out.println ("done replacing");
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

  public void collectVariables(Set<QVar> vars, QExpression expr) {
    switch (expr) {
      case QVar x: vars.add(x); return;
      case QValue v: return;
      case QMult cm:
        if (cm.queryChild() instanceof QVar x) vars.add(x);
        else throw new Error("This won't work if we mutliply constants by things other than variables!");
        return;
      case QAddition a:
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
      case QMult cm: 
      if (cm.queryChild() instanceof QVar v){
        if (v.queryIndex()==x.queryIndex()) return cm.queryConstant(); else return new QValue(0,1);
      }
      throw new Error("expression does not have the expected shape!");
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