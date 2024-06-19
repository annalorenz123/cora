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

package cora.reduction;

import java.util.List;
import charlie.util.Pair;
import charlie.terms.Term;
import charlie.terms.Renaming;
import cora.io.ProofObject;
import cora.io.OutputModule;

/**
 * A ReductionObject holds a reduction, and knows how to print itself to an OutputModule.
 */
class Reduction implements ProofObject {
  private List<Term> _steps;

  /**
   * The constructor is package-private, since this is only meant to be constructed from withing
   * the reduction package.  Note that the given list becomes the property of the Reduction; it
   * should not be changed afterwards, and that it should be non-empty as it contains at least the
   * starting term of the reduction.
   */
  Reduction(List<Term> steps) { _steps = steps; }

  /**
   * As answer, we always return YES, because if a Reduction is returned, reducing to normal form
   * succeeded.
   */
  public Answer queryAnswer() {
    return Answer.YES;
  }

  /** This returns a default string representation of the normal form in the reduction. */
  public String printAnswer() {
    return "Normalised input term to: " + _steps.get(_steps.size()-1).toString();
  }

  /** The main functionality of any proof object is to print itself to an OutputModule. */
  public void justify(OutputModule out) {
    Renaming naming = out.queryTermPrinter().generateUniqueNaming(_steps);
    out.startTable();
    boolean first = true;
    for (Term t : _steps) {
      out.nextColumn(first ? "" : "%{ruleArrow}");
      out.println("%a", new Pair<Term,Renaming>(t, naming));
      first = false;
    }
    out.endTable();
  }
}

