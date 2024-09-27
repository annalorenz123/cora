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
import java.lang.Iterable;
import java.util.Iterator;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import java.util.Arrays;

public class InternalSolver implements SmtSolver {

  /**
   * TODO: this is the place where all the work needs to be done.
   * Figure out if we should return YES(Valuation val), NO(), or MAYBE(String reason).
   */
  public SmtSolver.Answer checkSatisfiability(SmtProblem problem) {
    //return new Answer.YES(new Valuation());
    Constraint constraints = problem.queryCombinedConstraint();
    System.out.println(constraints);
    ArrayList<Constraint> children = new ArrayList<>();
    if (constraints instanceof Conjunction) {
      Conjunction conjunction = (Conjunction) constraints;
      for (int i = 1; i <= conjunction.numChildren(); i++){
        children.add(conjunction.queryChild(i));
      }
    }
    ArrayList<IntegerExpression> expressions = new ArrayList<IntegerExpression>();
    for (int i =0; i < children.size(); i++){
      //aanpassen naar switch
      Constraint child = children.get(i);
      if (child instanceof Is0){
        System.out.println("instance of is0" + child.toString());
        Is0 func = (Is0) child;
        expressions.add(func.queryExpression().simplify());
      }
      else if (child instanceof Geq0){
        Geq0 func = (Geq0) child;
        expressions.add(func.queryExpression().simplify());
      }
    }
    System.out.println("expressions: " +expressions);
    //for every expression except the objective function we add a slack variable
    
    expressions = addIndividualSlackVariables(problem, expressions);
    expressions = addUniversalSlackVariable(problem, expressions);
    System.out.println("final expr: " +expressions);
    //ArrayList<ArrayList<Double>> simpTab = makeSimplexTableau (problem, expressions);
    ArrayList<ArrayList<Double>> simpTab = new ArrayList<>();
    printSimplexTableau(simpTab);
    simplexMethod(simpTab);
    return new Answer.MAYBE("not implemented yet");

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


  public ArrayList<IntegerExpression> addUniversalSlackVariable (SmtProblem problem, ArrayList<IntegerExpression> expressions){
    IVar slackVariable = problem.createIntegerVariable("z");
    for (int i =0; i < expressions.size(); i++){
      expressions.set(i ,SmtFactory.createAddition(slackVariable, expressions.get(i)));
    }
    expressions.add(SmtFactory.createMultiplication(SmtFactory.createValue(-1), slackVariable).simplify());

    return expressions;
  }



  public ArrayList<IntegerExpression> addIndividualSlackVariables (SmtProblem problem, ArrayList<IntegerExpression> expressions){
    //with coefficient -1, not sure if thats correct
    for (int i =0; i < expressions.size(); i++){
      System.out.println(expressions.get(i).toString() + " " + expressions.get(i).getClass());
      expressions.set(i, SmtFactory.createAddition(SmtFactory.createMultiplication(-1,problem.createIntegerVariable()).simplify(), expressions.get(i)));
    }
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

  int getCount(IVar x, IntegerExpression expr) {
    switch(expr) {
      case IVar y: if (x.equals(y)) return 1; else return 0;
      case IValue v: return 0;
      case CMult cm: if (cm.queryChild().equals(x)) return cm.queryConstant(); else return 0;
      case Addition a:
        for (int i = 1; i <= a.numChildren(); i++) {
          int tmp = getCount(x, a.queryChild(i));
          if (tmp != 0) return tmp;
        }
        return 0;
      default: throw new Error("expression does not have the expected shape!");
    }
  }

  public void collectConstants(ArrayList<Double> list, IntegerExpression expr){
    switch (expr) {
      case IVar x: return;
      case IValue v: list.add((double)v.queryValue());return;
      case CMult cm: return;
      case Addition a:
        for (int i = 1; i <= a.numChildren(); i++) collectConstants(list, a.queryChild(i));
        return;
      default:
        throw new Error("Expression of the form " + expr.toString() + " not supported!");
    }
  }
  
  public ArrayList<ArrayList<Double>> makeSimplexTableau (SmtProblem problem, ArrayList<IntegerExpression> expressions){
    ArrayList<ArrayList<Double>> simplexTableau = new ArrayList<>();
    System.out.println(expressions);
    Set<IVar> vars = new HashSet<IVar>();
    for (IntegerExpression expr : expressions){
      collectVariables(vars, expr);
    }
    for (IntegerExpression expr : expressions){
      ArrayList<Double> row = new ArrayList<>();
      for (IVar var : vars){
        row.add( (double)getCount(var, expr));
      }
      ArrayList<Double> list = new ArrayList<>();
      collectConstants(list, expr);
      
      for (Double d : list){
        row.add(d);
      }
      
      simplexTableau.add(row);
    }
    simplexTableau.get(simplexTableau.size()-1).add(0.0);
    // ArrayList<Double> objFuncRow = new ArrayList<>();
    // for (int i =0; i < simplexTableau.get(0).size(); i++){
    //   objFuncRow.add(0.0);
    // }
    // objFuncRow.add(-1.0);
    // objFuncRow.add(0.0);

    // for (IVar var: vars){
    //   objFuncRow.add((double)getCount(var, obj_func));
    // }
    // objFuncRow.add(0.0);
    //simplexTableau.add(objFuncRow);

    return simplexTableau;
  }

  public Boolean pivotFound (ArrayList<ArrayList<Double>> matrix){
    //returns true if there is a negative number in the objective row
    for (double i : matrix.get(matrix.size()-1)){
      if (i < 0){
        return true;
      }
    }
    return false;
  }

  public int pivotColumn(ArrayList<ArrayList<Double>> matrix){
    //returns index of lowest value in objective row
    int lowestElementIndex = 0;
    for (int i = 1; i < matrix.get(matrix.size()-1).size()-1; i++){
      if (matrix.get(matrix.size()-1).get(i) < matrix.get(matrix.size()-1).get(lowestElementIndex)){
        lowestElementIndex = i;
      }
    }
    return lowestElementIndex;
  }

  public int pivotRow (int pivotColumn, ArrayList<ArrayList<Double>> matrix){
    //use only non negative entries
    int startIndex =0;
    while (matrix.get(startIndex).get(matrix.get(startIndex).size()-1) <= 0 || matrix.get(startIndex).get(pivotColumn) <= 0){
      startIndex++;
      System.out.println("increasing start index " + startIndex);
    } 
    System.out.println("size: " + matrix.get(0).size());
    if (startIndex== matrix.get(0).size()){
      System.out.println("unbounded solution");
      return 0;
    }
    else {
      double lowestQuotient = matrix.get(startIndex).get(matrix.get(startIndex).size()-1) / matrix.get(startIndex).get(pivotColumn);
      for (int i =startIndex; i < matrix.size()-1; i++){
        if (matrix.get(i).get(pivotColumn) > 0 && matrix.get(i).get(matrix.get(i).size()-1) > 0){
          System.out.println("dividing " + matrix.get(i).get(matrix.get(i).size()-1) + " and " + matrix.get(i).get(pivotColumn));
          if (matrix.get(i).get(matrix.get(i).size()-1) / matrix.get(i).get(pivotColumn) < lowestQuotient){
            System.out.println (matrix.get(i).get(matrix.get(i).size()-1) / matrix.get(i).get(pivotColumn) + " is smaller than " + lowestQuotient);
            lowestQuotient = matrix.get(i).get(matrix.get(i).size()-1) / matrix.get(i).get(pivotColumn);
            startIndex = i;
          }
        }
      }
      return startIndex;
    }

  }


  public int allNegative(int pivotColumn, ArrayList<ArrayList<Double>> matrix){
    int lowestIndex = 0;
    double lowestQuotient = matrix.get(0).get(matrix.get(0).size()-1) / matrix.get(0).get(pivotColumn);
    for (int i =0; i < matrix.size()-1; i++){
      if (matrix.get(i).get(matrix.get(i).size()-1) / matrix.get(i).get(pivotColumn) < lowestQuotient){
        lowestQuotient = matrix.get(i).get(matrix.get(i).size()-1) / matrix.get(i).get(pivotColumn);
        lowestIndex = i;
      }
    }
    return lowestIndex;

  }

  public void printSimplexTableau (ArrayList<ArrayList<Double>> simpTab){
    for (int i =0; i < simpTab.size(); i++){
      System.out.print("[ ");
      for (int j =0; j < simpTab.get(i).size(); j++){
        System.out.print(simpTab.get(i).get(j) + ", ");
      }
      System.out.println("] ");
    }
  }
  public ArrayList<ArrayList<Double>> step (ArrayList<ArrayList<Double>> matrix, int pivotColumn, int pivotRow){
    //set pivot element to 1
    double factor = matrix.get(pivotRow).get(pivotColumn);
    for (int j =0; j < matrix.get(pivotRow).size(); j++){
      double newValue = matrix.get(pivotRow).get(j)/factor;
      matrix.get(pivotRow).set(j, newValue);
    }
    //find first row that is not the pivot row
    //gaat fout, could get i-i in row
    //doe multiple of pivot row eraf
    
    for (int j =0; j < matrix.size(); j++){
      if (j != pivotRow){
        factor = matrix.get(pivotRow).get(pivotColumn)/matrix.get(j).get(pivotColumn);
        System.out.println ("subtracting " + factor + " times row " + pivotRow + " from row " + j );
        for (int k =0; k < matrix.get(j).size(); k++){
          matrix.get(j).set(k,matrix.get(j).get(k)-factor*matrix.get(pivotRow).get(k));
        }
      }
    }
    printSimplexTableau(matrix);
    return matrix;
  }
    // }
    // factor = matrix.get(i).get(pivotColumn);
    // System.out.println ("subtracting " + factor + " times, row " + pivotRow + " from row " + i);
    // for (int j =0; j < matrix.get(i).size(); j++){
    //   double newValue = matrix.get(i).get(j)-(factor*matrix.get(pivotRow).get(j));
    //   matrix.get(i).set(j,newValue);
    // }
    


  public void simplexMethod(ArrayList<ArrayList<Double>> simpTab){
    ArrayList<Double> row1 = new ArrayList<>(Arrays.asList(1.0, 3.0, 1.0, 1.0, 0.0, 0.0, 12.0));
    ArrayList<Double> row2 = new ArrayList<>(Arrays.asList(1.0, 1.0, -1.0, 0.0, 1.0, 0.0, 10.0));
    ArrayList<Double> row3 = new ArrayList<>(Arrays.asList(1.0, -1.0, 1.0, 0.0, 0.0, 1.0, 7.0));
    ArrayList<Double> row4 = new ArrayList<>(Arrays.asList(0.0, 0.0, -1.0, 0.0, 0.0, 0.0, 0.0));
    simpTab.add(row1);
    simpTab.add(row2);
    simpTab.add(row3);
    simpTab.add(row4);
    ArrayList<Integer> baseVariables = new ArrayList<>();
    simpTab.get(1).set(1,-1.0);

    for (int i=0; i < simpTab.size(); i++){
      baseVariables.add(0);
    }
    System.out.println("base:" + baseVariables);
    printSimplexTableau(simpTab);
    while (pivotFound(simpTab)){
      printSimplexTableau (simpTab);
      int pivotColumn= pivotColumn(simpTab);
      int pivotRow = pivotRow(pivotColumn, simpTab);

      System.out.println("pivot row and column: " + pivotRow + " " + pivotColumn);
      simpTab = step(simpTab, pivotColumn, pivotRow);
      baseVariables.set(pivotRow, pivotRow);
      System.out.println(baseVariables);
    }


  }
}