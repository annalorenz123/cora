
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
import java.math.BigInteger;

public class SimplexMethod {


  ArrayList<QVar> basis = new ArrayList<>();


  public SmtSolver.Answer checkSatisfiability(SmtProblem problem, ArrayList<IntegerExpression> expressions, boolean negative){
    if (expressions.size()==0) return new SmtSolver.Answer.YES(new Valuation());
    System.out.println("Expressions: " +expressions);
    ArrayList<QExpression> Qexpressions = convertToQExpressions(expressions);
    Set<ArrayList<QExpression>> problems = new HashSet<>();
    problems.add(Qexpressions);
    boolean firstTime = true;
    int iterations = 0;
    while (problems.size() > 0){
      iterations++;
      System.out.println ("Problems: ");
      Iterator<ArrayList<QExpression>> it = problems.iterator();
      while (it.hasNext()){
        System.out.println (it.next());
      }
      it = problems.iterator();
      final ArrayList<QExpression> currentProblem = new ArrayList<>(it.next());
      System.out.println ("Current problem: " + currentProblem);
      it = problems.iterator();
      final ArrayList<QExpression> originalProblem = new ArrayList<>(it.next());
      ArrayList<QValue> solution = getSolution(problem.numberIntegerVariables(), currentProblem);
      SmtSolver.Answer answer = checkSolution(solution, problem.numberIntegerVariables(), expressions, negative);
      problems.remove(originalProblem);
      if (answer instanceof SmtSolver.Answer.YES) {
        System.out.println ("Iterations: " + iterations);
        return answer;
      }
      if (answer instanceof SmtSolver.Answer.NO){
        if (problems.size()==0){
          return answer;
        }
        else System.out.println ("Removed first problem but we have more options.");
      }
      if (answer instanceof SmtSolver.Answer.MAYBE){
        QValuation qVal = makeQValuation(problem.numberIntegerVariables(), solution);
        ArrayList<QValuation> roundedValuations = getRoundedValuations(problem.numberIntegerVariables(), qVal);
        for (QValuation q : roundedValuations){
          Valuation v = convertQValToVal(q, problem.numberIntegerVariables());
          if (extraCheck(v, expressions)) {
            System.out.println ("Iterations: " + iterations);
            return new SmtSolver.Answer.YES(v);
          }
        }
        System.out.println ("There is no integer solution so we add an expression.");
        if (firstTime) {
          problems.addAll(getNewProblems(convertToQExpressions(expressions), solution)); 
          firstTime = false;
        }
        else {
          ArrayList<ArrayList<QExpression>> adjustedProblems = adjustProblems(convertToQExpressions(expressions),originalProblem);
          if (adjustedProblems.isEmpty()) {
            adjustedProblems = getNewProblems(originalProblem, solution);
          }
          problems.addAll(adjustedProblems);
        }
      }
    }
    throw new Error("Simplex error. Should have returned yes or no answer.");
  }

  public ArrayList<IntegerExpression> convertToNegative (SmtProblem problem, ArrayList<IntegerExpression> expressions){
    final int numVariables = problem.numberIntegerVariables();
    for (int i =1; i <= numVariables; i++){
      IntegerExpression newexpr = SmtFactory.createAddition(problem.createIntegerVariable(), SmtFactory.createMultiplication(-1, problem.createIntegerVariable()));
      for (int j=0; j < expressions.size(); j++){
        expressions.set(j, replace(expressions.get(j), i, newexpr));
      }

    }
    return expressions;
  } 

  public IntegerExpression replace (IntegerExpression expr, int varIndex, IntegerExpression newExpr){
    switch (expr) {
      case IVar x: 
        if (x.queryIndex() == varIndex){
          return newExpr;
        } else {
          return x;
        }
      case IValue v: return v;
      case CMult cm: return SmtFactory.createMultiplication(cm.queryConstant(), replace(cm.queryChild(), varIndex, newExpr)).simplify();
      case Addition a:
        ArrayList <IntegerExpression> newChildren = new ArrayList<>();
        for (int i =1; i <= a.numChildren(); i++){
          newChildren.add(replace(a.queryChild(i), varIndex, newExpr).simplify());
        }
        return SmtFactory.createAddition(newChildren).simplify();
      default:
        throw new Error("Expression of the form " + expr.toString() + " not supported!");
    }
  }

  public Valuation convertQValToVal (QValuation qVal, int numberOfVariables){
    Valuation v = new Valuation();
    for (int i =0; i <= numberOfVariables; i++){
      v.setInt(i, qVal.queryQValueAssignment(i).queryNumerator().intValue());
    }
    return v;
  }
  
  public ArrayList<ArrayList<QExpression>> adjustProblems (ArrayList<QExpression> Qexpressions, ArrayList<QExpression> currentProblem){
    ArrayList<ArrayList<QExpression>> adjustedProblems = new ArrayList<>();
    if (currentProblem.get(currentProblem.size()-1).equals(currentProblem.get(currentProblem.size()-2).negate())){
      return adjustedProblems; 
    }
    currentProblem.add(currentProblem.get(currentProblem.size()-1).negate());
    adjustedProblems.add(new ArrayList<>(currentProblem));
    currentProblem.remove(currentProblem.size()-1);
    Set <QVar> variables = new HashSet<>();
    collectVariables(variables, currentProblem.get(currentProblem.size()-1));
    Iterator<QVar> it = variables.iterator();
    if (variables.isEmpty()) return adjustedProblems;
    QVar variable = it.next();
    if (variables.size() != 1){
      throw new Error(currentProblem.get(currentProblem.size()-1) + " should only contain one variable.");
    }
    if (getCount(variable, currentProblem.get(currentProblem.size()-1)).queryNumerator().compareTo(BigInteger.valueOf(0)) < 0){
      currentProblem.set(currentProblem.size()-1, new QAddition (currentProblem.get(currentProblem.size()-1), new QValue(BigInteger.valueOf(-1),BigInteger.valueOf(1))).simplify());
    }
    else if (getCount(variable, currentProblem.get(currentProblem.size()-1)).queryNumerator().compareTo(BigInteger.valueOf(0)) > 0){
      currentProblem.set(currentProblem.size()-1, new QAddition (currentProblem.get(currentProblem.size()-1), new QValue(BigInteger.valueOf(-1),BigInteger.valueOf(1))).simplify());
    }
    adjustedProblems.add(currentProblem);
    return adjustedProblems;
  }

  public ArrayList<QValuation> getRoundedValuations (int numberOfVariables, QValuation qVal){
    ArrayList<QValuation> roundedSolutions = new ArrayList<>();
    for (int i =1; i <= numberOfVariables; i++){
      QValue value = qVal.queryQValueAssignment(i);
      if (value.queryDenominator() != BigInteger.valueOf(1)){
        double qDouble = value.queryNumerator().divide(value.queryDenominator()).doubleValue();
        int roundedUp = (int) Math.ceil(qDouble);
        int roundedDown = (int) Math.floor(qDouble);
        if (roundedSolutions.size() == 0){
          qVal.setQValue(i, new QValue(BigInteger.valueOf(roundedUp),BigInteger.valueOf(1)));
          roundedSolutions.add(qVal);
          QValuation copiedVal = new QValuation();
          for (int j =0; j <= numberOfVariables; j++){
            copiedVal.setQValue(j, qVal.queryQValueAssignment(j));
          }
          copiedVal.setQValue(i, new QValue(BigInteger.valueOf(roundedDown),BigInteger.valueOf(1)));
          roundedSolutions.add(copiedVal);
        }
        else{
          final int solutionSize = roundedSolutions.size();
          for (int k = 0; k < solutionSize; k++){
            roundedSolutions.get(k).setQValue(i, new QValue(BigInteger.valueOf(roundedUp),BigInteger.valueOf(1)));
            QValuation copiedVal = new QValuation();
            for (int j =0; j <= numberOfVariables; j++){
              copiedVal.setQValue(j, roundedSolutions.get(k).queryQValueAssignment(j));
            }
            roundedSolutions.add(copiedVal);
            roundedSolutions.get(roundedSolutions.size()-1).setQValue(i, new QValue(BigInteger.valueOf(roundedDown),BigInteger.valueOf(1)));
          }
        }
      }
    }
    return roundedSolutions;
  }


  public SmtSolver.Answer checkSolution (ArrayList<QValue> solution, int numberIntegerVariables, ArrayList<IntegerExpression> expressions, boolean negative){
    System.out.println ("Checking solution: " + solution);
    if (zLargerThanZero(solution)){
      return new SmtSolver.Answer.NO();
    }
    if (!integerSolution(solution)){
      return new SmtSolver.Answer.MAYBE("no integer solution");
    }
    Valuation val = makeValuation(numberIntegerVariables, solution, negative); 
    if (extraCheck(val, expressions)){
      return new SmtSolver.Answer.YES(val);
    }
    return new SmtSolver.Answer.MAYBE("something went wrong in simplex method.");
  }

  public boolean isSlackVar (QVar var){
    return var.queryName().contains("y");
  }

  public ArrayList<ArrayList<QExpression>> getNewProblems (ArrayList<QExpression> Qexpressions, ArrayList<QValue> solution){
    int index = 0;
    ArrayList<ArrayList<QExpression>> newProblems = new ArrayList<>();
    while (solution.get(index).queryDenominator().equals(BigInteger.valueOf(1)) || isSlackVar(basis.get(index))){
      index++;
      if (index == solution.size() || index == basis.size()) return newProblems;
    }
    QValue fraction = solution.get(index);
    double fractionDouble = fraction.queryNumerator().divide(fraction.queryDenominator()).doubleValue();
    int roundedUp = (int) Math.ceil(fractionDouble)+1;
    int roundedDown = (int) Math.floor(fractionDouble);
    QExpression constraintUp = new QAddition(new QValue(BigInteger.valueOf(roundedUp), BigInteger.valueOf(1)).multiply(new QValue(BigInteger.valueOf(-1),BigInteger.valueOf(1))), basis.get(index));
    QExpression constraintDown = new QAddition(new QValue(BigInteger.valueOf(roundedDown), BigInteger.valueOf(1)), new QMult(new QValue(BigInteger.valueOf(-1),BigInteger.valueOf(1)), basis.get(index)));
    Qexpressions.add(constraintUp);
    newProblems.add(new ArrayList<>(Qexpressions));
    if (roundedDown >= 0){
      Qexpressions.remove(Qexpressions.size() - 1);
      Qexpressions.add(constraintDown);
      newProblems.add(new ArrayList<>(Qexpressions));
    }
    return newProblems;
  }

  public ArrayList<QExpression> addSlackVariables (QVar slackVariable, int numberIntegerVariables, ArrayList<QExpression> Qexpressions){
    Qexpressions = addIndividualSlackVariables(numberIntegerVariables, Qexpressions);
    QExpression objFunc = new QMult (new QValue(BigInteger.valueOf(-1), BigInteger.valueOf(1)), slackVariable);
    Qexpressions = addUniversalSlackVariable(slackVariable, Qexpressions);
    Qexpressions.add(0,objFunc);
    return Qexpressions;
  }

  public boolean extraCheck (Valuation val, ArrayList<IntegerExpression> expressions){
    for (IntegerExpression expr : expressions){
      if (expr.evaluate(val) < 0){
        return false; 
      }
    }
    return true;
  }

  public ArrayList<QValue> collectSolution(ArrayList<QExpression> Qexpressions){
    if (basis.size() != Qexpressions.size()-1) throw new Error ("Basis and number of expr do not have the same length.");
    ArrayList<QValue> constantsFinal = new ArrayList<>();
    for (int i =1; i < Qexpressions.size(); i++){
      ArrayList<QValue> constants = new ArrayList<>();
      collectConstants(constants, Qexpressions.get(i));
      constantsFinal.addAll(constants);
      if (constants.isEmpty()){
        constantsFinal.add(new QValue(BigInteger.valueOf(0),BigInteger.valueOf(1)));
      } 
    }
    return constantsFinal;
  }

  public boolean zLargerThanZero(ArrayList<QValue> constants){
    for (int i =0; i < basis.size(); i++){
      if (basis.get(i).queryName().equals("[z]")) {
        return constants.get(i).compareTo(new QValue(BigInteger.valueOf(0),BigInteger.valueOf(1))) > 0;
      }
    }
    return false;
  }

  public boolean integerSolution (ArrayList<QValue> solution){
    for (QValue q : solution){
      if (!(q.queryDenominator().equals(BigInteger.valueOf(1)))) return false;
    }
    return true;
  }

  public QValuation makeQValuation (int numberIntegerVariables, ArrayList<QValue> constants){
    QValuation val = new QValuation();
    for (int i =0; i <= numberIntegerVariables; i++){
      val.setQValue(i, new QValue(BigInteger.valueOf(0),BigInteger.valueOf(1)));
    }
    for (int i =0; i < basis.size(); i++){
      if (basis.get(i).queryIndex() <= numberIntegerVariables){
        val.setQValue(basis.get(i).queryIndex(), constants.get(i));
      }
    }
    return val;
  }


  public Valuation makeValuation (int numberIntegerVariables, ArrayList<QValue> constants, boolean negative){
    Valuation val = new Valuation();
    for (int i =0; i <= numberIntegerVariables; i++){
      val.setInt(i, 0);
    }
    for (int i =0; i < basis.size(); i++){
      if (basis.get(i).queryIndex() <= numberIntegerVariables){
        val.setInt(basis.get(i).queryIndex(), constants.get(i).queryNumerator().intValue());
      }
    }
    return val;
  }

  public ArrayList<QValue> getSolution (int numberIntegerVariables, ArrayList<QExpression> Qexpressions){
    QVar slackVariable = new QVar(numberIntegerVariables + Qexpressions.size()+1, "z");
    basis.clear();
    Qexpressions = addSlackVariables(slackVariable, numberIntegerVariables, Qexpressions);
    Qexpressions = simplexMethod(numberIntegerVariables, Qexpressions, slackVariable);
    
    ArrayList<QValue> solution = collectSolution(Qexpressions);
    return solution;
  } 

  public ArrayList<QExpression> simplexMethod (int numberIntegerVariables, ArrayList<QExpression> Qexpressions, QVar slackVariable){
    if (!basicSolution(Qexpressions)){
      Qexpressions = pivot (slackVariable, exprWithLowestConstant(Qexpressions, slackVariable), Qexpressions);
      Qexpressions = removingZeroExpressions(Qexpressions);
      while (positiveFactor(Qexpressions.get(0)) ){
        if (basicSolution(Qexpressions)){
          QVar swap = findPositiveFactor(Qexpressions.get(0));
          QExpression newExpr = findMinBound(Qexpressions, swap);
          if (newExpr == Qexpressions.get(0)) return Qexpressions;
          Qexpressions = pivot(swap, newExpr, Qexpressions);
          Qexpressions = removingZeroExpressions(Qexpressions);
          if (basis.size() != Qexpressions.size()-1) throw new Error ("Basis and expr do not have same length.");
        }
        else throw new Error ("Simplex method has taken wrong step.");
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
    return new QValue(BigInteger.valueOf(i), BigInteger.valueOf(1));
  }

  public QExpression convert(IntegerExpression expr) {
    switch (expr) {
      case IVar x: return new QVar(x.queryIndex(), x.queryName());
      case IValue v: return new QValue(BigInteger.valueOf(v.queryValue()), BigInteger.valueOf(1));
      case CMult cm:
        return new QMult(convertIntToQ(cm.queryConstant()), convert(cm.queryChild()));
      case Addition a:
        List<QExpression> list = new ArrayList<>();
        for (int i = 1; i <= a.numChildren(); i++) list.add(convert(a.queryChild(i)));
        return new QAddition(list);
      default:
        throw new Error("Expression of the form " + expr + " not supported!");
    }
  } 

  public static QExpression findMinBound (ArrayList<QExpression> expressions, QVar swap){
    int index = 1;
    QValue count = getCount(swap, expressions.get(index));
    ArrayList<QValue> constants = new ArrayList<>();
    collectConstants(constants, expressions.get(index));
    if (constants.size()==0){
      constants.add(new QValue(BigInteger.valueOf(0),BigInteger.valueOf(1)));
    }
    while (count.compareTo(new QValue(BigInteger.valueOf(0),BigInteger.valueOf(1))) >= 0 || constants.get(0).compareTo(new QValue(BigInteger.valueOf(0),BigInteger.valueOf(1)))<0 ){
      constants.clear();
      index++;
      if (index >= expressions.size()){
        throw new Error("No minimum bound for "+ swap + ". Unbounded solution.");

      }
      count = getCount(swap, expressions.get(index));
      collectConstants(constants, expressions.get(index));
      if (constants.size()==0){
        constants.add(new QValue(BigInteger.valueOf(0),BigInteger.valueOf(1)));
      }
    }
    collectConstants(constants, expressions.get(index));
    QValue minBound = (QValue)divide(constants.get(0),count).multiply(new QValue(BigInteger.valueOf(-1),BigInteger.valueOf(1)));
    for (int i = index+1; i <expressions.size(); i++){
      count = getCount(swap, expressions.get(i));
      if (count.compareTo(new QValue(BigInteger.valueOf(0),BigInteger.valueOf(1))) < 0){
        constants.clear();
        collectConstants(constants, expressions.get(i));
        if (constants.size()==0){
          constants.add(new QValue(BigInteger.valueOf(0),BigInteger.valueOf(1)));
        }
        if (constants.get(0).compareTo(new QValue(BigInteger.valueOf(0),BigInteger.valueOf(1)))>=0){
          if (divide(constants.get(0),count).multiply(new QValue(BigInteger.valueOf(-1),BigInteger.valueOf(1))).compareTo(minBound)<0){
            minBound = (QValue)divide(constants.get(0),count).multiply(new QValue(BigInteger.valueOf(-1),BigInteger.valueOf(1)));
            index = i;
          }
          
        }
      }
    }
    return expressions.get(index);
  }

  public ArrayList<Double> getTimes (){
    ArrayList<Double> list = new ArrayList<>();
    list.add(0.0);
    list.add(0.0);
    list.add(0.0);
    list.add(0.0);
    return list;
  }

  public static boolean positiveFactor (QExpression objFunc){
    switch (objFunc) {
      case QVar x: return true;
      case QValue v: return false;
      case QMult cm: return cm.queryConstant().queryNumerator().compareTo(BigInteger.valueOf(0)) > 0;
      case QAddition a: return positiveFactor(a.queryChild(1)) || positiveFactor(new QAddition(a, a.queryChild(1).negate()).simplify());
      default: return false;     
    }
  }

  public QVar findPositiveFactor (QExpression expression) {
    switch (expression){
      case QVar x: return x;
      case QMult cm: 
        if (cm.queryConstant().queryNumerator().compareTo(BigInteger.valueOf(0)) > 0) {
          return findPositiveFactor(cm.queryChild());
        }
        throw new Error ("No positive factor in " + expression);
      case QAddition a: 
        if (positiveFactor(a.queryChild(1))){
          return findPositiveFactor(a.queryChild(1));
        }
        return findPositiveFactor(new QAddition(a, a.queryChild(1).negate()).simplify());
      default: throw new Error("There is no positive factor in " + expression);
    }
  }

  public QExpression exprWithLowestConstant (ArrayList<QExpression> expressions, QVar slackVariable){
    int index = 1;
    while (getCount(slackVariable, expressions.get(index)).queryNumerator().equals(BigInteger.valueOf(0))){
      index++;
      if (index == expressions.size()) throw new Error ("z does not occur in any expression.");
    }
    ArrayList<QValue> list = new ArrayList<>();
    collectConstants(list, expressions.get(index));
    if (list.isEmpty()) list.add(new QValue(BigInteger.valueOf(0),BigInteger.valueOf(1)));
    QExpression lowestDivision = divide(list.get(0), getCount(slackVariable, expressions.get(index)));
    QExpression expression = expressions.get(index);
    for (int i =index+1; i < expressions.size(); i++){
      if (getCount(slackVariable, expressions.get(i)).queryNumerator() != BigInteger.valueOf(0)){
        list.clear();
        collectConstants(list, expressions.get(i));
        if (list.isEmpty()) list.add(new QValue(BigInteger.valueOf(0),BigInteger.valueOf(1)));
        QExpression currentDivision = divide(list.get(0), getCount(slackVariable, expressions.get(i)));
        if (currentDivision.compareTo(lowestDivision) < 0) {
          lowestDivision = currentDivision;
          expression = expressions.get(i);
        }
      }
    }
    return expression;
  }

  public ArrayList<QExpression> pivot (QVar swap, QExpression newExpr, ArrayList<QExpression> expressions){
    QValue count = getCount(swap, newExpr);
    QExpression remove = new QMult(count, swap);
    newExpr = new QAddition (remove.negate(), newExpr).negate().simplify();
    newExpr = divide(newExpr, count).simplify();
    for (int i =0; i < expressions.size(); i++){
      QExpression newExpression = replace (expressions.get(i), swap, newExpr).simplify();
      if (newExpression instanceof QValue q && i != 0){
        int basisIndex = i-1;
        while (basisIndex >= basis.size() && basisIndex > 0) basisIndex--;
        basis.remove(basisIndex);
      }
      expressions.set(i,newExpression);
    }
    newExpr = addTerms(newExpr, new QMult(new QValue(BigInteger.valueOf(-1),BigInteger.valueOf(1)), swap)).simplify();
    expressions.add(1, newExpr);
    basis.add(0, swap);
    return expressions;
  }


  public static QExpression divide (QExpression expr, QValue count){
    if (count.queryNumerator().equals(BigInteger.valueOf(0))){
      throw new IllegalArgumentException("We cannot divide by zero.");
    }
    switch (expr) {
      case QVar x: 
      if (getCount(x,expr).queryNumerator().equals(getCount(x,expr).queryDenominator())){
        return new QMult(count.simplify(new QValue(BigInteger.valueOf(1),BigInteger.valueOf(1)),count), x);
      }
      return x; 
      case QValue v: 
        return count.simplify(v,count);
      case QMult cm: return new QMult((QValue)divide(cm.queryConstant(), count),cm.queryChild());
      case QAddition a:
        QAddition divided = new QAddition(new QValue(BigInteger.valueOf(0),BigInteger.valueOf(1)), new QValue(BigInteger.valueOf(0),BigInteger.valueOf(1)));
        for (int i = 1; i <= a.numChildren(); i++) divided = addTerms(divided, divide(a.queryChild(i), count));
        return divided;
      default:
        throw new Error("Expression of the form " + expr.toString() + " not supported!");
    }

  }

  public static QAddition addTerms(QExpression expr1, QExpression expr2) {
    return new QAddition (expr1, expr2);
  }

  public ArrayList<QExpression> removingZeroExpressions (ArrayList<QExpression> expressions){
    for (int i =1; i < expressions.size(); i++){
      if (expressions.get(i) instanceof QValue q){
          expressions.remove(i);
          i--;
      }
    }
    return expressions;
  }

  public QExpression replace (QExpression expr, QVar oldVar, QExpression newExpr){
    switch (expr) {
      case QVar x: 
        if (x.queryIndex() == oldVar.queryIndex()){
          return newExpr;
        } else {
          return x;
        }
      case QValue v: return v;
      case QMult cm: return new QMult(cm.queryConstant(), replace(cm.queryChild(), oldVar, newExpr)).simplify();
      case QAddition a:
        ArrayList <QExpression> newChildren = new ArrayList<>();
        for (int i =1; i <= a.numChildren(); i++){
          newChildren.add(replace(a.queryChild(i), oldVar, newExpr).simplify());
        }
        return new QAddition(newChildren).simplify();
      default:
        throw new Error("Expression of the form " + expr.toString() + " not supported!");
    }
  }

  public boolean basicSolution (ArrayList<QExpression> expressions){
    ArrayList<QValue> list = new ArrayList<>();
    for (int i =1; i < expressions.size(); i++){
      collectConstants(list, expressions.get(i));
    }
    for (QValue constant : list){
      if (constant.queryNumerator().compareTo(BigInteger.valueOf(0))<0){
        return false;
      }
    }
    return true;
  }

  public ArrayList<QExpression> addUniversalSlackVariable (QVar slackVariable, ArrayList<QExpression> expressions){
    for (int i =0; i < expressions.size(); i++){
      expressions.set(i ,new QAddition (slackVariable, expressions.get(i)));
    }
    return expressions;
  }

  public ArrayList<QExpression> addIndividualSlackVariables (int numberIntegerVariables, ArrayList<QExpression> expressions){
    int index = numberIntegerVariables+1;
    for (int i =0; i < expressions.size(); i++){
      QVar slackVariable = new QVar(index, "y"+(i+1));
      index++;
      basis.add(slackVariable);
      expressions.set(i, new QAddition(expressions.get(i), new QMult(new QValue(BigInteger.valueOf(-1),BigInteger.valueOf(1)), slackVariable)));
    }
    return expressions;
  }

  public void collectVariables(Set<QVar> vars, QExpression expr) {
    switch (expr) {
      case QVar x: vars.add(x); return;
      case QValue v: return;
      case QMult cm:
        if (cm.queryChild() instanceof QVar x) vars.add(x);
        else throw new Error("This won't work if we multiply constants by things other than variables!");
        return;
      case QAddition a:
        for (int i = 1; i <= a.numChildren(); i++) collectVariables(vars, a.queryChild(i));
        return;
      default:
        throw new Error("Expression of the form " + expr.toString() + " not supported!");
    }
  }

  public static QValue getCount(QVar x, QExpression expr) {
    switch(expr) {
      case QVar y: if (x.queryIndex()==y.queryIndex()) return new QValue(BigInteger.valueOf(1),BigInteger.valueOf(1)); else return new QValue(BigInteger.valueOf(0),BigInteger.valueOf(1));
      case QValue v: return new QValue(BigInteger.valueOf(0),BigInteger.valueOf(1));
      case QMult cm: 
      if (cm.queryChild() instanceof QVar v){
        if (v.queryIndex()==x.queryIndex()) return cm.queryConstant(); else return new QValue(BigInteger.valueOf(0),BigInteger.valueOf(1));
      }
      throw new Error("expression does not have the expected shape!");
      case QAddition a:
        for (int i = 1; i <= a.numChildren(); i++) {
          QValue tmp = getCount(x, a.queryChild(i));
          if (tmp.queryNumerator() != BigInteger.valueOf(0)) return tmp;
        }
        return new QValue(BigInteger.valueOf(0),BigInteger.valueOf(1));
      default: throw new Error("expression does not have the expected shape!");
    }
  }

  public static void collectConstants(ArrayList<QValue> list, QExpression expr){
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