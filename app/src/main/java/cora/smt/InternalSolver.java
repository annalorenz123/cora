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
import java.math.BigInteger;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

public class InternalSolver implements SmtSolver {


  ArrayList<QVar> basis = new ArrayList<>();
  /**
   * TODO: this is the place where all the work needs to be done.
   * Figure out if we should return YES(Valuation val), NO(), or MAYBE(String reason).
   */
  public SmtSolver.Answer checkSatisfiability(SmtProblem problem){
    
    Constraint constraint = problem.queryCombinedConstraint();
    ArrayList<Constraint> children = getConstraints(constraint);
    ArrayList<IntegerExpression> expressions = getExpressions(children);
    long startTime = System.nanoTime();
    //SimplexMethod bb = new SimplexMethod();
    BitBlasting bb = new BitBlasting();
    //BitBlastingLimitedBitWidth bb = new BitBlastingLimitedBitWidth();
    SmtSolver.Answer answer = bb.checkSatisfiability(problem, expressions, false);
    long endTime = System.nanoTime();
    long duration = endTime - startTime; // Time in nanoseconds
    double executionTime = duration / 1_000_000.0;

    File file = new File("bitblastingmeasurements.csv");
    try (BufferedWriter writer = new BufferedWriter(new FileWriter(file, true))) {
        // Append the line and a newline character

        writer.write(Double.toString(executionTime));
        ArrayList<Double> times = bb.getTimes();
        double percentageBitblasting = times.get(0)/executionTime;
        double percentageTT = times.get(1)/executionTime;
        double percentageDIMACS = times.get(2)/executionTime;
        double percentageMinisat = times.get(3)/executionTime;
        writer.write (", " + Double.toString(percentageBitblasting));
        writer.write (", " + Double.toString(percentageTT));
        writer.write (", " + Double.toString(percentageDIMACS));
        writer.write (", " + Double.toString(percentageMinisat));
        writer.write (", " + Double.toString(times.get(0)));
        writer.write (", " + Double.toString(times.get(1)));
        writer.write (", " + Double.toString(times.get(2)));
        writer.write (", " + Double.toString(times.get(3)));
        if (answer instanceof SmtSolver.Answer.NO){
          writer.write(", NO");
        }
        writer.newLine();
        //System.out.println("Line added successfully to: " + filePath);
    } catch (IOException e) {
        System.err.println("An error occurred while writing to the file: " + e.getMessage());
    }
    return answer;
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

}