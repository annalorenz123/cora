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
import charlie.terms.*;
import cora.io.OutputModule;
import cora.termination.dependency_pairs.DP;
import cora.termination.dependency_pairs.Problem;

/** The proof object generated by the Integer Function Processor. */
class IntegerMappingProof extends ProcessorProofObject {
  private Set<Integer> _oriented;                       // indexes of oriented DPs
  private Map<FunctionSymbol,List<Variable>> _argvars;  // argument variables per symbol
  private Map<FunctionSymbol,Term> _intp;               // interpretation per symbol

  /** A failed proof: nothing could be removed */
  IntegerMappingProof(Problem inp) {
    super(inp);
    _oriented = null;
    _intp = null;
  }

  /**
   * A successful proof: the given set of DPs could be removed, using the given integer
   * function.  The set of indexes considers the 0-based index in inp.getDPList().
   */
  IntegerMappingProof(Problem inp, Set<Integer> oriented,
                      Map<FunctionSymbol,List<Variable>> argvars, Map<FunctionSymbol,Term> intp) {
    super(inp, removeDPs(oriented, inp));
    _oriented = oriented;
    _argvars = argvars;
    _intp = intp;
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
 
  public String queryProcessorName() { return "Integer Function"; }
    
  public void justify(OutputModule module) {
    if (_intp == null) {
      module.println("No suitable integer maping could be found");
      return;
    }
    printFunction(module);
    module.println("We thus have:");
    printOriented(module);

    if (_oriented.size() == _input.getDPList().size()) {
      module.println("All DPs are strictly oriented, and may be removed.  " +
                     "Hence, this DP problem is finite.");
    }
    else module.println("We may remove the strictly oriented DPs, which yields:");
  }

  /** Helper function for justify: prints the interpretation function we found. */
  private void printFunction(OutputModule module) {
    module.println("We use the following integer mapping:");
    module.startTable();
    _intp.forEach(
      (f, t) -> {
        module.nextColumn("J(%a)", f.toString());
        module.nextColumn("=");
        module.println("%a", t);
      }
    );
    module.endTable();
  }

  /**
   * Given a candidate term t over variables {x_1^f,...,x_n^f}, and a term of the form f(s1,...,sn),
   * this returns t[x_1^f:=s1,...,x_n^f:=sn].
   */
  private Term instantiateCandidate(Term candidate, Term term) {
    Substitution subst = TermFactory.createEmptySubstitution();
    FunctionSymbol f = term.queryRoot();
    for (int varL = 0; varL < f.queryArity(); varL ++) {
      subst.extend(_argvars.get(f).get(varL), term.queryArgument(varL + 1));
    }
    return candidate.substitute(subst);
  }

  /** Helper function for justify: prints which DPs are oriented (and why). */
  private void printOriented(OutputModule module) {
    module.startTable();
    List<DP> originalDPs = _input.getDPList();
    for (int index = 0; index < originalDPs.size(); index++) {
      DP dp = originalDPs.get(index);
      Term left = instantiateCandidate(_intp.get(dp.lhs().queryRoot()), dp.lhs());
      Term right = instantiateCandidate(_intp.get(dp.rhs().queryRoot()), dp.rhs());
      Renaming renaming =
        module.queryTermPrinter().generateUniqueNaming(left, right, dp.constraint());
      boolean oriented = _oriented.contains(index);
      module.nextColumn("(" + (index+1) + ")");
      module.nextColumn("%a", new Pair<Term,Renaming>(dp.constraint(), renaming));
      module.nextColumn("%{Vdash}");
      module.nextColumn("%a", new Pair<Term,Renaming>(left, renaming));
      module.nextColumn(oriented ? "%{greater}" : "%{geq}");
      module.nextColumn("%a", new Pair<Term,Renaming>(right, renaming));
      if (oriented) {
        module.nextColumn("(and %a %{geq} 0)", new Pair<Term,Renaming>(left, renaming));
      }
      module.println();
    }
    module.endTable();
  }
}

