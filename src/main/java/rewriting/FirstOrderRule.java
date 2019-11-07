/**************************************************************************************************
 Copyright 2019 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.rewriting;

import cora.exceptions.IllegalRuleError;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.TypingError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.Term;
import cora.interfaces.terms.Substitution;
import cora.interfaces.terms.Variable;
import cora.interfaces.rewriting.Rule;

/**
 * A FirstOrderRule is a rule l -> r where l and r are first-order terms of the same sort, l is not a
 * variable, and vars(r) ⊆ vars(l).
 */
public class FirstOrderRule extends RuleInherit implements Rule {
  /**
   * Creates a rule with the given left- and right-hand side.
   * If the types don't match, a TypingError is thrown.
   */
  public FirstOrderRule(Term left, Term right) {
    super(left, right);
    // both sides need to be first-order
    if (!left.isFirstOrder() || !right.isFirstOrder()) {
      throw new IllegalRuleError("FirstOrderRule", "terms in rule [" + left.toString() + " → " +
        right.toString() + "] are not first-order.");
    }
    // the left-hand side should have the form f(...)
    if (!left.isFunctionalTerm()) {
        throw new IllegalRuleError("FirstOrderRule", "illegal rule [" + left.toString() + " → " +
          right.toString() + "] with a variable as the left-hand side.");
    }
  }

  public boolean applicable(Term t) {
    return _left.match(t) != null;
  }

  public Term apply(Term t) {
    Substitution subst = _left.match(t);
    if (subst == null) return null;
    return _right.substitute(subst);
  }
}

