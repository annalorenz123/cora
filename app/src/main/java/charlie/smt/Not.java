/**************************************************************************************************
 Copyright 2023--2024 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package charlie.smt;

public final class Not extends Constraint {
  private Constraint _negated;

  /** The constructor is hidden, since Constraints should be made through the SmtFactory. */
  Not(Constraint e) {
    _negated = e;
    _negated.simplify();
  }

  public Constraint queryChild() {
    return _negated;
  }

  public boolean evaluate(Valuation val) {
    return !(_negated.evaluate(val));
  }

  public Constraint negate() {
    return _negated;
  }

  public void addToSmtString(StringBuilder builder) {
    builder.append("(not ");
    _negated.addToSmtString(builder);
    builder.append(")");
  }

  public boolean equals(Constraint other) {
    return (other instanceof Not) && (_negated.equals(((Not)other).queryChild()));
  }

  public Constraint simplify(){
    if (_negated instanceof BVar b1 && b1.queryIndex()==1) return new BVar(2);;
    if (_negated instanceof BVar b2 && b2.queryIndex()==2) return new BVar(1);;
    // if (_negated instanceof Falsehood) return SmtFactory.createTrue();
    // if ( _negated instanceof Truth) return SmtFactory.createFalse();
    if (_negated instanceof Not n) return n.queryChild();
    return this;
  }
}

