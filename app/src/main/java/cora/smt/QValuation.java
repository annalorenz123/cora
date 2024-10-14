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

package cora.smt;

import java.util.TreeSet;
import java.util.TreeMap;
import charlie.smt.*;

/**
 * A valuation is an assignment of booleans to BVars, and integers to IVars.
 * A Valuation is in principle mutable, so be careful how you use it! (It needs to be mutual to
 * support gradual creation.)
 */
public class QValuation {
  private TreeSet<Integer> _trueBVars;
  private TreeMap<Integer,QValue> _QVarValues;

  /** Creates a new valuation with all booleans set to false, and no integer values set. */
  public QValuation() {
    _trueBVars = new TreeSet<Integer>();
    _QVarValues = new TreeMap<Integer,QValue>();
  }

  /** Returns the valuation for the boolean variable with the given index */
  public boolean queryBoolAssignment(int index) {
    return _trueBVars.contains(index);
  }

  /** Returns the valuation for the integer variable with the given index */
  public QValue queryQValueAssignment(int index) {
    if (_QVarValues.containsKey(index)) return _QVarValues.get(index);
    else return new QValue(4242,1);
  }

  /** Returns the valuation for the given boolean variable */
  public boolean queryAssignment(BVar x) {
    return queryBoolAssignment(x.queryIndex());
  }

  /** Returns the valuation for the given integer variable */
  public QValue queryAssignment(QVar x) {
    return queryQValueAssignment(x.queryIndex());
  }

  /** Set a boolean variable to the given value. */
  public void setBool(int index, boolean value) {
    if (value) _trueBVars.add(index);
    else _trueBVars.remove(index);
  }

  /** Set an integer variable to the given value. */
  public void setQValue(int index, QValue value) {
    _QVarValues.put(index, value);
  }

  /** Give a human-readable representation of the valuation, for use in debugging. */
  public String toString() {
    StringBuilder ret = new StringBuilder();
    ret.append("True boolean variables:\n");
    for (Integer i : _trueBVars) ret.append("  b" + i.toString() + "\n");
    ret.append("QValue variables:\n");
    for (Integer i : _QVarValues.keySet()) {
      ret.append("  i" + i.toString() + " : " + _QVarValues.get(i).toString() + "\n");
    }
    return ret.toString();
  }
}

