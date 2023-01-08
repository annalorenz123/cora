/**************************************************************************************************
 Copyright 2023 Cynthia Kop

 Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 in compliance with the License.
 You may obtain a copy of the License at

     http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software distributed under the
 License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 express or implied.
 See the License for the specific language governing permissions and limitations under the License.
 *************************************************************************************************/

package cora.terms;

import cora.exceptions.NullInitialisationError;

/**
 * An ArgumentPath is a position of the form i.pos, where i indicates the index of an argument
 * in the corresponding term and pos a position within that argument.  Since it is a path, it
 * keeps track of the terms on the way from the top of the term to the referenced subterm.
 */
class ArgumentPath implements Path {
  private int _argPos;
  private Path _tail;
  private Term _topterm;
  private Term _subterm;

  /** Should only be called by Terms; nothing outside the package. */
  ArgumentPath(Term myterm, int argumentIndex, Path tail) {
    _argPos = argumentIndex;
    _tail = tail;
    if (tail == null) throw new NullInitialisationError("ArgumentPath", "tail");
    _topterm = myterm;
    if (myterm == null) throw new NullInitialisationError("ArgumentPath", "myterm");
    _subterm = tail.queryCorrespondingSubterm();
  }

  public boolean isEmpty() {
    return false;
  }

  public boolean isArgument() {
    return true;
  }

  public Term queryAssociatedTerm() {
    return _topterm;
  }

  public Term queryCorrespondingSubterm() {
    return _subterm;
  }

  public int queryArgumentPosition() {
    return _argPos;
  }

  public Path queryTail() {
    return _tail;
  }

  public boolean equals(Position other) {
    return other.isArgument() &&
           other.queryArgumentPosition() == _argPos &&
           _tail.equals(other.queryTail());
  }

  public String toString() {
    return "" + _argPos + "." + _tail.toString();
  }
}
