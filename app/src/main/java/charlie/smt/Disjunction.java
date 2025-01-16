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

import java.util.List;
import java.util.ArrayList;
import java.util.HashSet;


public final class Disjunction extends Junction {
  Disjunction(Constraint a, Constraint b) {
    super(a, b);
  }

  Disjunction(List<Constraint> args) {
    super(args);
  }

  protected String symbol() { return "or"; }

  public boolean evaluate(Valuation val) {
    for (int i = 0; i < _children.size(); i++) {
      if (_children.get(i).evaluate(val)) return true;
    }
    return false;
  }

  public Conjunction negate() {
    ArrayList<Constraint> arr = new ArrayList<Constraint>();
    for (Constraint c : _children) arr.add(c.negate());
    return new Conjunction(arr);
  }

  public Constraint simplify(){
    //return this;
    final Constraint before = SmtFactory.createDisjunction(this.queryChildren());
    HashSet<Constraint> argsSet = new HashSet<>();
    for (int i = 0; i < _children.size(); i++) {
      if (_children.get(i) instanceof BVar b && b.queryIndex()==2) {
        //System.out.println ("returning true for " +this);
        return b;
      }
      if (!(_children.get(i) instanceof BVar b2 && b2.queryIndex()==1)) {
        argsSet.add(_children.get(i));
      }
    }

    if (argsSet.isEmpty()) {
      return new BVar(1);
    }
    ArrayList<Constraint> list = new ArrayList<>(argsSet);
    return SmtFactory.createDisjunction(list);
  }

    // // Convert HashSet to ArrayList to maintain expected return type
    // List<Constraint> resultChildren = new ArrayList<>(argsSet);
    // //if (!((this.queryChildren()).equals(resultChildren))) System.out.println(before + " simplified is " + this);
    // //System.out.println ("simplified " + this);
    // return SmtFactory.createDisjunction(resultChildren);
    // ArrayList<Constraint> argsSimplified = new ArrayList<>();
    // final Constraint before = SmtFactory.createDisjunction(this.queryChildren());
    // // for (int i = 0; i < _children.size(); i++) {
    // //   if (_children.get(i) instanceof Truth ) return SmtFactory.createTrue();
    // //   if (_children.get(i) instanceof Falsehood ) {
    // //     _children.remove(i);
    // //     i--;
    // //     if (_children.size()==1) return _children.get(0);
    // //   }
    // //   if (i > 0){
    // //     if (_children.get(i).equals(_children.get(i-1))) {
    // //       _children.remove(i);
    // //       i--; // Decrement `i` to adjust for the shift after removal
    // //       if (_children.size() == 1) {
    // //         return _children.get(0);
    // //       }
    // //     }
    // //     if (_children.get(i) instanceof Not n){
    // //       if (n.queryChild().equals(_children.get(i-1))) return SmtFactory.createTrue();
    // //     }
      
    // //   }
    
    // // }
    // for (int i = 0; i < _children.size(); i++) {
    //   if (_children.get(i) instanceof Truth ) {
    //     //System.out.println ("returning true");
    //     return SmtFactory.createTrue();
    //   }
    //   if (!(_children.get(i) instanceof Falsehood)) {
    //     boolean alreadyPresent = false;
    //     for (int j =0; j < argsSimplified.size(); j++){
    //       if (argsSimplified.get(j).equals(_children.get(i))) alreadyPresent=true;
    //     }
    //     if (!alreadyPresent) argsSimplified.add(_children.get(i));      
    //   }
    // }
    // if (argsSimplified.size()==0) {
    //   //System.out.println ("returning false");
    //   return SmtFactory.createFalse();
    // }
    // //this._children = argsSimplified;

    // if (!(before.equals(this))) System.out.println (before + " simplified is " + this);
    // List<Constraint> resultChildren = new ArrayList<>(argsSimplified);
    // return SmtFactory.createDisjunction(resultChildren);
}
