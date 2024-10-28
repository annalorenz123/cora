
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

public class SimplexMethod {


  ArrayList<QVar> basis = new ArrayList<>();


  public SmtSolver.Answer checkSatisfiability(SmtProblem problem, ArrayList<IntegerExpression> expressions){
    System.out.println("expressions: " +expressions);

    
    
    ArrayList<QExpression> Qexpressions = convertToQExpressions(expressions);
    Set<ArrayList<QExpression>> problems = new HashSet<>();
    problems.add(Qexpressions);
    //Iterator<ArrayList<QExpression>> it = problems.iterator();
    boolean firstTime = true;
    int iterations = 0;
    while (problems.size() > 0){
      iterations++;

      System.out.println ("problems: ");
      Iterator<ArrayList<QExpression>> it = problems.iterator();
      while (it.hasNext()){
        System.out.println (it.next());
      }
      it = problems.iterator();
      final ArrayList<QExpression> currentProblem = new ArrayList<>(it.next());
      
      System.out.println ("CURRENT PROBLEM: " + currentProblem);
      it = problems.iterator();
      final ArrayList<QExpression> originalProblem = new ArrayList<>(it.next());
      ArrayList<QValue> solution = getSolution(problem.numberIntegerVariables(), currentProblem);
      SmtSolver.Answer answer = checkSolution(solution, problem.numberIntegerVariables(), expressions);
      problems.remove(originalProblem);
      
      if (answer instanceof SmtSolver.Answer.YES) return answer;
      if (answer instanceof SmtSolver.Answer.NO){
        if (problems.size()==0) return answer;
        else System.out.println ("removed first problem but we have more options");
      }
      if (answer instanceof SmtSolver.Answer.MAYBE){
        Qexpressions = convertToQExpressions(expressions);
        QValuation qVal = makeQValuation(problem.numberIntegerVariables(), solution);
        System.out.println ("qvaluation: " + qVal);
      
        ArrayList<QValuation> roundedValuations = getRoundedValuations(problem.numberIntegerVariables(), qVal);
        System.out.println ("rounded valuations: " + roundedValuations);

        for (QValuation q : roundedValuations){
          Valuation v = convertQValToVal(q, problem.numberIntegerVariables());
          if (extraCheck(v, expressions)) return new SmtSolver.Answer.YES(v);
        }
        System.out.println ("there is no integer solution so we add an expression");
        if (firstTime) {
          problems.addAll(getNewProblems(convertToQExpressions(expressions), solution)); 
          firstTime = false;
        }
        else {
          //answer = tryExactValue(convertToQExpressions(expressions),currentProblem);
          problems.addAll(adjustProblems(convertToQExpressions(expressions),originalProblem));
          problems.addAll(getNewProblems(convertToQExpressions(expressions), solution)); 
          problems = new HashSet<>(removeDuplicates(new ArrayList<>(problems)));
        }
      }
    }
    return new SmtSolver.Answer.MAYBE("not implemented yet.");
  }

  public ArrayList<ArrayList<QExpression>> removeDuplicates (ArrayList<ArrayList<QExpression>> problems){
    System.out.println ("going to remove duplicates from: " + problems);
    ArrayList<ArrayList<QExpression>> list = new ArrayList<>();
    boolean alreadyPresent = false;
    for (int i =0; i < problems.size(); i++){
      for (int j=0; j < list.size(); j++){
        if (problems.get(i).equals(list.get(j))){
          alreadyPresent = true;
        }
      }
      System.out.println ("going to add: " + problems.get(i));
      if (!alreadyPresent) list.add(problems.get(i));
    }
    System.out.println ("removed duplicates: " + list);
    return list;
  }

  public Valuation convertQValToVal (QValuation qVal, int numberOfVariables){
    Valuation v = new Valuation();
    for (int i =0; i <=numberOfVariables; i++){
      v.setInt(i, (int)qVal.queryQValueAssignment(i).queryNumerator());
    }
    return v;
  }
  
  public ArrayList<ArrayList<QExpression>> adjustProblems (ArrayList<QExpression> Qexpressions, ArrayList<QExpression> currentProblem){
    System.out.println ("current problem: " + currentProblem);
    ArrayList<ArrayList<QExpression>> adjustedProblems = new ArrayList<>();

    currentProblem.add(currentProblem.get(currentProblem.size()-1).negate());
    adjustedProblems.add(new ArrayList<>(currentProblem));
    
    System.out.println ("added: " +adjustedProblems);
    currentProblem.remove(currentProblem.size()-1);
    Set <QVar> variables = new HashSet<>();
    
    
    collectVariables(variables, currentProblem.get(currentProblem.size()-1));
    Iterator<QVar> it = variables.iterator();
    if (variables.isEmpty()) return adjustedProblems;
    QVar variable = it.next();
    if (variables.size() != 1){
      throw new Error(currentProblem.get(currentProblem.size()-1) + " should only contain one variable: ");
    }
    if (getCount(variable, currentProblem.get(currentProblem.size()-1)).queryNumerator() < 0){
      currentProblem.set(currentProblem.size()-1, new QAddition (currentProblem.get(currentProblem.size()-1), new QValue(1,1)).simplify());
    }
    else if (getCount(variable, currentProblem.get(currentProblem.size()-1)).queryNumerator() > 0){
      currentProblem.set(currentProblem.size()-1, new QAddition (currentProblem.get(currentProblem.size()-1), new QValue(-1,1)).simplify());
    }
    adjustedProblems.add(currentProblem);
    System.out.println ("adjusted problems: "+adjustedProblems);
    return adjustedProblems;
  }

  public ArrayList<QValuation> getRoundedValuations (int numberOfVariables, QValuation qVal){
    ArrayList<QValuation> roundedSolutions = new ArrayList<>();
    for (int i =1; i <= numberOfVariables; i++){
      QValue value = qVal.queryQValueAssignment(i);
      if (value.queryDenominator() != 1){
        double qDouble = (double) value.queryNumerator()/value.queryDenominator();
        int roundedUp = (int) Math.ceil(qDouble);
        int roundedDown = (int) Math.floor(qDouble);
        if (roundedSolutions.size() == 0){
          qVal.setQValue(i, new QValue(roundedUp,1));
          roundedSolutions.add(qVal);
          QValuation copiedVal = new QValuation();
          for (int j =0; j <= numberOfVariables; j++){
            copiedVal.setQValue(j, qVal.queryQValueAssignment(j));
          }
          copiedVal.setQValue(i, new QValue(roundedDown,1));

          roundedSolutions.add(copiedVal);
        }
        else{
          final int solutionSize = roundedSolutions.size();
          for (int k = 0; k < solutionSize; k++){
            roundedSolutions.get(k).setQValue(i, new QValue(roundedUp,1));
            QValuation copiedVal = new QValuation();
            for (int j =0; j <= numberOfVariables; j++){
              copiedVal.setQValue(j, roundedSolutions.get(k).queryQValueAssignment(j));
            }
            roundedSolutions.add(copiedVal);
            roundedSolutions.get(roundedSolutions.size()-1).setQValue(i, new QValue(roundedDown,1));
          }
        }
      }
    }
    return roundedSolutions;
  }


  public SmtSolver.Answer checkSolution (ArrayList<QValue> solution, int numberIntegerVariables, ArrayList<IntegerExpression> expressions){
    if (zLargerThanZero(solution)){
      System.out.println ("z is larger than zero");
      return new SmtSolver.Answer.NO();
    }
    if (!integerSolution(solution)){
      System.out.println ("there is no integer solution");
      return new SmtSolver.Answer.MAYBE("no integer solution");

      
    }
    Valuation val = makeValuation(numberIntegerVariables, solution); 
    if (extraCheck(val, expressions)){
      System.out.println ("valuation: " + val);
      return new SmtSolver.Answer.YES(val);
    }
    System.out.println ("SOMETHING WENT WRONG, SIMPLEX RETURNED SOLUTION THAT DOES NOT HOLD");
    return new SmtSolver.Answer.MAYBE("something went wrong in simplex method.");
  }

  public ArrayList<ArrayList<QExpression>> getNewProblems (ArrayList<QExpression> Qexpressions, ArrayList<QValue> solution){
    int index = 0;
    while (solution.get(index).queryDenominator() == 1){
      index++;
    }
    QValue fraction = solution.get(index);
    double fractionDouble = (double) fraction.queryNumerator()/fraction.queryDenominator();
    int roundedUp = (int) Math.ceil(fractionDouble);
    int roundedDown = (int) Math.floor(fractionDouble);
    System.out.println (fraction + " rounded up is " + roundedUp);
    System.out.println (fraction + " rounded down is " + roundedDown);
    QExpression constraintUp = new QAddition(new QValue(roundedUp, 1).multiply(new QValue(-1,1)), basis.get(index));
    QExpression constraintDown = new QAddition(new QValue(roundedDown, 1), new QMult(new QValue(-1,1), basis.get(index)));

    Qexpressions.add(constraintUp);
    ArrayList<ArrayList<QExpression>> newProblems = new ArrayList<>();
    newProblems.add(new ArrayList<>(Qexpressions));
    if (roundedDown >= 0){
          
      // Remove constraintUp and add constraintDown
      Qexpressions.remove(Qexpressions.size() - 1);
      Qexpressions.add(constraintDown);
          
      // Add a copy of Qexpressions with constraintDown
      newProblems.add(new ArrayList<>(Qexpressions));
    }

    return newProblems;

  }

  public ArrayList<QExpression> addSlackVariables (QVar slackVariable, int numberIntegerVariables, ArrayList<QExpression> Qexpressions){
    Qexpressions = addIndividualSlackVariables(numberIntegerVariables, Qexpressions);
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
      if (constants.isEmpty()){
        constantsFinal.add(new QValue(0,1));
        System.out.println ("added a 0: " + constantsFinal);

      } 
    }
    return constantsFinal;
  }

  public boolean zLargerThanZero(ArrayList<QValue> constants){
    for (int i =0; i < basis.size(); i++){
      if (basis.get(i).queryName().equals("[z]")) {
        return constants.get(i).compareTo(new QValue(0,1)) > 0;
      }
    }
    return false;
  }

  public boolean integerSolution (ArrayList<QValue> solution){
    for (QValue q : solution){
      if (q.queryDenominator() != 1) return false;
    }
    return true;
  }

  public QValuation makeQValuation (int numberIntegerVariables, ArrayList<QValue> constants){
    QValuation val = new QValuation();
    //first we set all variables to zero
    for (int i =0; i <= numberIntegerVariables; i++){
      val.setQValue(i, new QValue(0,1));
    }
    //then we set basis variables to their corresponding values
    for (int i =0; i < basis.size(); i++){
      if (basis.get(i).queryIndex() <= numberIntegerVariables){
        System.out.println ("setting variable " + (basis.get(i).queryIndex())+ " to " + constants.get(i) + " in valuation");
        val.setQValue(basis.get(i).queryIndex(), constants.get(i));
      }
    }
    return val;
  }


  public Valuation makeValuation (int numberIntegerVariables, ArrayList<QValue> constants){
    Valuation val = new Valuation();
    //first we set all variables to zero
    for (int i =0; i <= numberIntegerVariables; i++){
      val.setInt(i, 0);
    }
    //then we set basis variables to their corresponding values
    for (int i =0; i < basis.size(); i++){
      if (basis.get(i).queryIndex() <= numberIntegerVariables){
        System.out.println ("setting variable " + (basis.get(i).queryIndex())+ " to " + constants.get(i).queryNumerator() + " in valuation");
        val.setInt(basis.get(i).queryIndex(), (int)constants.get(i).queryNumerator());
      }
    }
    return val;
  }

  public ArrayList<QValue> getSolution (int numberIntegerVariables, ArrayList<QExpression> Qexpressions){
    QVar slackVariable = new QVar(numberIntegerVariables + Qexpressions.size()+1, "z");
    basis.clear();
    Qexpressions = addSlackVariables(slackVariable, numberIntegerVariables, Qexpressions);
    Qexpressions = simplexMethod(numberIntegerVariables, Qexpressions, slackVariable);
    System.out.println ("we are done, no positive factors in obj func: " + Qexpressions.get(0));
    System.out.println ("basis: " + basis);
    
    ArrayList<QValue> solution = collectSolution(Qexpressions);
    System.out.println ("values of basis variables: " + solution);
    return solution;
  } 

  public ArrayList<QExpression> simplexMethod (int numberIntegerVariables, ArrayList<QExpression> Qexpressions, QVar slackVariable){
    System.out.println("final expr: " +Qexpressions);
    int iterations = 0;
    while (!(basicSolution(Qexpressions)) && iterations <10){
      iterations++;
      System.out.println("there is no basic solution");
      Qexpressions = pivot (slackVariable, exprWithLowestConstantAlternative(Qexpressions, slackVariable), Qexpressions);
      Qexpressions = removingZeroExpressions(Qexpressions);
      System.out.println("new expr: " + Qexpressions);
      
      while (positiveFactor(Qexpressions.get(0)) ){
        
        System.out.println("positive factor present");
        QVar swap = findPositiveFactor(Qexpressions.get(0));
        System.out.println("we found a variable with positive factor: " + swap);
        QExpression newExpr = findMinBound(Qexpressions, swap);
        System.out.println ("expr with min bound: "+newExpr);
        Qexpressions = pivot(swap, newExpr, Qexpressions);
        Qexpressions = removingZeroExpressions(Qexpressions);
        ArrayList<QValue> solution = collectSolution(Qexpressions);
        System.out.println ("values of basis variables: " + solution);
        System.out.println("removed zero expressions: " + Qexpressions);
      }
      //???
      // ArrayList<QValue> solution = collectSolution(Qexpressions);
      // System.out.println ("values of basis variables: " + solution);
      // if (zLargerThanZero(solution)) return Qexpressions;
    }
    return Qexpressions;
    // if (basicSolution(Qexpressions)) return Qexpressions;
    // else {
    //   basis.clear();
    //   Qexpressions = addSlackVariables(slackVariable, numberIntegerVariables, Qexpressions);
    //   return simplexMethod(numberIntegerVariables, Qexpressions, slackVariable);
    // }
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
        throw new Error("Expression of the form " + expr + " not supported!");
    }
  } 

  public ArrayList<QExpression> getSwapAndConstant (ArrayList<QExpression> expressions, QVar swap){
    ArrayList<QExpression> newExpressions = new ArrayList<>();
    for (int i =1; i < expressions.size(); i++){
      ArrayList<QValue> constants = new ArrayList<>();
      collectConstants(constants, expressions.get(i));
      if (constants.size()==0) constants.add(new QValue(0,1));
      QValue count = getCount(swap, expressions.get(i));
      newExpressions.add(new QAddition(new QMult(count, swap), constants.get(0)).simplify());
    }
    System.out.println ("new expressions: " + newExpressions);
    return newExpressions;
  }

  public QExpression findMinBoundAlternative (ArrayList<QExpression> expressions, QVar swap){
    System.out.println("in findminboundlalternative");
    ArrayList<QExpression> newExpressions = getSwapAndConstant(expressions, swap);
    int index =0;
    while (getCount(swap, newExpressions.get(index)).queryNumerator() == 0){
      index++;
      if (index==newExpressions.size()) throw new Error(swap + " does not occur in any expressions.");
    }
    ArrayList<QValue> constants = new ArrayList<>();
    collectConstants(constants, newExpressions.get(index));
    //System.out.println (expressions);
    if (constants.size()==0) constants.add(new QValue(0,1));
    System.out.println ("dividing " + constants.get(0).multiply(new QValue(-1,1)) + " and " + getCount(swap, newExpressions.get(index)));
    QExpression whenZero = divide (constants.get(0).multiply(new QValue(-1,1)), getCount(swap, newExpressions.get(index)));
    QValuation qval = new QValuation();
    qval.setQValue(swap.queryIndex(), (QValue) whenZero);
    boolean biggerOrEqualToZero = true;
    for (int i =0; i < newExpressions.size(); i++){
    System.out.println ("hi");
      if (newExpressions.get(i).evaluate(qval).compareTo(new QValue(0,1)) < 0){
        System.out.println (newExpressions.get(i) + " is smaller than zero for " + qval);
        biggerOrEqualToZero = false;
      }
    }
    ArrayList<QExpression> options = new ArrayList<>();
    if (biggerOrEqualToZero){
      System.out.println (expressions.get(index+1) + " is an option");
      options.add(expressions.get(index+1));
    }
    for (int i = index+1; i < newExpressions.size(); i++){
      if (getCount(swap, newExpressions.get(i)).queryNumerator() != 0){
        constants.clear();
        collectConstants(constants, newExpressions.get(i));
        if (constants.size()==0) constants.add(new QValue(0,1));
        whenZero = divide (constants.get(0).multiply(new QValue(-1,1)), getCount(swap, newExpressions.get(i)));
        qval = new QValuation();
        qval.setQValue(swap.queryIndex(), (QValue) whenZero);
        biggerOrEqualToZero = true;
        for (int j =0; j < newExpressions.size(); j++){
          if (newExpressions.get(j).evaluate(qval).compareTo(new QValue(0,1)) < 0){
            biggerOrEqualToZero = false;
          }
        } 
        if (biggerOrEqualToZero && (options.size()==0 || whenZero.compareTo(options.get(0)) > 0)){
          System.out.println ("found better option");
          options.set(0,expressions.get(i));
        }
      }
    }
    if (options.size()==0) throw new Error("No minimum bound for " + swap);
    else return options.get(0);
  }

  public QExpression findMinBound (ArrayList<QExpression> expressions, QVar swap){
    int index = 1;
    QValue count = getCount(swap, expressions.get(index));
    ArrayList<QValue> constants = new ArrayList<>();
    collectConstants(constants, expressions.get(index));
    //System.out.println (expressions);
    if (constants.size()==0){
      constants.add(new QValue(0,1));
    }
    while (count.compareTo(new QValue(0,1)) >= 0 || constants.get(0).compareTo(new QValue(0,1))<0 ){
      constants.clear();
      index++;
      if (index >= expressions.size()){
        return findMinBoundAlternative(expressions, swap);
        //throw new Error("No minimum bound for "+ swap);
      }
      count = getCount(swap, expressions.get(index));
      collectConstants(constants, expressions.get(index));
      if (constants.size()==0){
        constants.add(new QValue(0,1));
      }
    }
    //System.out.println ("first expr with negative coefficient: " + expressions.get(index));
    collectConstants(constants, expressions.get(index));
    //System.out.println ("dividing "+ constants.get(0)+ " and " + count);
    QValue minBound = (QValue)divide(constants.get(0),count).multiply(new QValue(-1,1));
    System.out.println ("first valid min bound for " + expressions.get(index)+ " is " + minBound);
    for (int i = index+1; i <expressions.size(); i++){
      //System.out.println ("looking at expr: " + expressions.get(i));

      count = getCount(swap, expressions.get(i));
      //System.out.println (swap + " count is: " + count);
      if (count.compareTo(new QValue(0,1)) < 0){
        //System.out.println ("count is smaller than 0");
        constants.clear();
        collectConstants(constants, expressions.get(i));
        if (constants.size()==0){
          constants.add(new QValue(0,1));
        }
        if (constants.get(0).compareTo(new QValue(0,1))>=0 && divide(constants.get(0),count).multiply(new QValue(-1,1)).compareTo(minBound)<0){
          minBound = (QValue)divide(constants.get(0),count).multiply(new QValue(-1,1));
          //System.out.println ("min bound for " + expressions.get(i)+ " is " + minBound);
          index = i;
        }
      }
    }
    //System.out.println ("expression with min bound: " + expressions.get(index));
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

  public QExpression exprWithLowestConstant (ArrayList<QExpression> expressions, QVar slackVariable){
    //you can assume there exists an expression in expressions with a constant < 0, because we do not have a basic solution
    ArrayList<QValue> list = new ArrayList<>();
    QValue lowestConstant = new QValue (0,1);
    QExpression expression = expressions.get(0);
    for (int i =1; i < expressions.size(); i++){
      collectConstants(list, expressions.get(i));
      if (!list.isEmpty() && list.get(0).compareTo(lowestConstant) < 0 && getCount(slackVariable, expressions.get(i)).queryNumerator() != 0){
        lowestConstant = list.get(0);
        expression = expressions.get(i);
      }
      list.clear();
    }
    return expression;
  }

  public QExpression exprWithLowestConstantAlternative (ArrayList<QExpression> expressions, QVar slackVariable){
    //you can assume there exists an expression in expressions with a constant < 0, because we do not have a basic solution
    int index = 1;
    while (getCount(slackVariable, expressions.get(index)).queryNumerator()==0){
      index++;
      if (index == expressions.size()) throw new Error ("z does not occur in any expression");
    }
    ArrayList<QValue> list = new ArrayList<>();
    collectConstants(list, expressions.get(index));
    if (list.isEmpty()) list.add(new QValue(0,1));
    QExpression lowestDivision = divide(list.get(0), getCount(slackVariable, expressions.get(index)));
    QExpression expression = expressions.get(index);
    for (int i =index+1; i < expressions.size(); i++){
      if (getCount(slackVariable, expressions.get(i)).queryNumerator() != 0){
        list.clear();
        collectConstants(list, expressions.get(i));
        if (list.isEmpty()) list.add(new QValue(0,1));
        QExpression currentDivision = divide(list.get(0), getCount(slackVariable, expressions.get(i)));
        if (currentDivision.compareTo(lowestDivision) < 0) {
          lowestDivision = currentDivision;
          expression = expressions.get(i);
        }
      }
    }
    System.out.println ("going to swap " + slackVariable + " with " + expression);
    return expression;
  }

  public ArrayList<QExpression> pivot (QVar swap, QExpression newExpr, ArrayList<QExpression> expressions){
    // find variable in newExpr and swap with that  
    QValue count = getCount(swap, newExpr);
    //System.out.println ("found count " + count + "of " + swap + " in " + newExpr);
    QExpression remove = new QMult(count, swap);
    System.out.println (remove.negate());
    newExpr = new QAddition (remove.negate(), newExpr).negate().simplify();
    System.out.println(newExpr);
    newExpr = divide(newExpr, count).simplify();
    System.out.println("we are swapping " + swap + " with " + newExpr.toString());
    //System.out.println ("expressions: " + expressions);
    for (int i =0; i < expressions.size(); i++){
      System.out.println("we are swapping " + swap + " with " + newExpr.toString() + " in " + expressions.get(i));
      QExpression newExpression = replace (expressions.get(i), swap, newExpr);
      //System.out.println ("result is " + newExpression);
      if (newExpression instanceof QValue q){
        //System.out.println ("found qvalue in expressions: " + q + "removing basis value: " + basis.get(i-1));
        System.out.println ("removing basis value: " + (i-1) + " from basis " + basis);
        int basisIndex = i-1;
        while (basisIndex >= basis.size() && basisIndex > 0) basisIndex--;
        basis.remove(basisIndex);
      }
      expressions.set(i,newExpression);
    }
    //System.out.println ("done replacing");
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
        //if (q.queryNumerator()==0){
          expressions.remove(i);
          i--;
        //}
      }
    }
    return expressions;
  }

  public QExpression replace (QExpression expr, QVar oldVar, QExpression newExpr){
    //System.out.println ("in replace for " + expr);
    //replace oldVar in expr for newExpr
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
          System.out.println ("replacing for: " + a.queryChild(i)+" result is " + replace(a.queryChild(i), oldVar, newExpr));
          newChildren.add(replace(a.queryChild(i), oldVar, newExpr).simplify());
        }
        //System.out.println ("final result is: " + new QAddition(newChildren).simplify());
        return new QAddition(newChildren).simplify();

        //System.out.println ("replacing in " + a.queryChild(1) + " and in " + new QAddition(a, a.queryChild(1).negate().simplify()));
        //System.out.println ("result 1: " + replace(a.queryChild(1), oldVar, newExpr));
        //System.out.println ("result 2: " + replace(a.queryChild(2), oldVar, newExpr).simplify());
        //return new QAddition (replace(a.queryChild(1), oldVar, newExpr), replace(new QAddition(a, a.queryChild(1).negate().simplify()).simplify(), oldVar, newExpr)).simplify();
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
        //System.out.println("i have found constant < 0 : " + constant);
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
      expressions.set(i, new QAddition(expressions.get(i), new QMult(new QValue(-1,1), slackVariable)));
    }
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