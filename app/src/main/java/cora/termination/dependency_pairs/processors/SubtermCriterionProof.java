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

package cora.termination.dependency_pairs.processors;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.Map;

import charlie.util.Pair;
import cora.terms.*;
import cora.terms.TermPrinter.Renaming;
import cora.io.OutputModule;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;

/** The proof object generated by the Subterm Criterion Processor. */
class SubtermCriterionProof extends ProcessorProofObject {
  private Set<Integer> _oriented;                       // indexes of oriented DPs
  private Map<FunctionSymbol,Integer> _proj;            // projection per symbol

  /** A failed proof: nothing could be removed */
  SubtermCriterionProof(Problem inp) {
    super(inp);
    _oriented = null;
    _proj = null;
  }

  /**
   * A successful proof: the given set of DPs could be removed, using the given integer
   * function.  The set of indexes considers the 0-based index in inp.getDPList().
   */
  SubtermCriterionProof(Problem inp, Set<Integer> oriented, Map<FunctionSymbol,Integer> proj) {
    super(inp, removeDPs(oriented, inp));
    _oriented = oriented;
    _proj = proj;
  }

  /** Helper function for the constructor */
  private static List<Problem> removeDPs(Set<Integer> oriented, Problem original) {
    List<DP> originalDPs = original.getDPList();
    List<DP> remainingDPs = new ArrayList<DP>();
    for (int index = 0; index < originalDPs.size(); index++) {
      if (!oriented.contains(index)) remainingDPs.add(originalDPs.get(index));
    }
    if (remainingDPs.size() == 0) return List.of();
    else return List.of(new Problem(remainingDPs, original.getTRS()));
  }
 
  public String queryProcessorName() { return "Subterm Criterion"; }
    
  public void justify(OutputModule module) {
    if (_proj == null) {
      module.println("No suitable projection could be found");
      return;
    }
    printProjection(module);
    module.println("We thus have:");
    printOriented(module);

    if (_oriented.size() == _input.getDPList().size()) {
      module.println("All DPs are strictly oriented, and may be removed.  " +
                     "Hence, this DP problem is finite.");
    }
    else module.println("We may remove the strictly oriented DPs, which yields:");
  }

  /** Helper function for justify: prints the interpretation function we found. */
  private void printProjection(OutputModule module) {
    module.println("We use the following projection function:");
    module.startTable();
    _proj.forEach(
      (f, num) -> {
        module.nextColumn("%{nu}(%a)", f.toString());
        module.nextColumn("=");
        module.println("%a", num);
      }
    );
    module.endTable();
  }


  /** Helper function for justify: prints which DPs are oriented (and why). */
  private void printOriented(OutputModule module) {
    module.startTable();
    List<DP> originalDPs = _input.getDPList();
    for (int index = 0; index < originalDPs.size(); index++) {
      DP dp = originalDPs.get(index);
      FunctionSymbol f = dp.lhs().queryRoot();
      FunctionSymbol g = dp.rhs().queryRoot();
      if (!_proj.containsKey(f) || !_proj.containsKey(g)) {
        throw new Error("Illegal proof: no projection given for " + dp + ".");
      }
      Term left = dp.lhs().queryArgument(_proj.get(f));
      Term right = dp.rhs().queryArgument(_proj.get(g));
      Renaming renaming = module.queryTermPrinter().generateUniqueNaming(left, right);
      boolean oriented = _oriented.contains(index);
      module.nextColumn("(" + (index+1) + ")");
      module.nextColumn("%a", new Pair<Term,Renaming>(left, renaming));
      module.nextColumn(oriented ? "%{supterm}" : "%{suptermeq}");
      module.nextColumn("%a", new Pair<Term,Renaming>(right, renaming));
      module.println();
    }
    module.endTable();
  }
}

