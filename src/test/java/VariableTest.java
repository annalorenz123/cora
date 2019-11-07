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

import org.junit.Test;
import static org.junit.Assert.*;
import java.util.List;
import cora.exceptions.ArityError;
import cora.exceptions.IndexingError;
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.NullCallError;
import cora.exceptions.TypingError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.*;
import cora.types.*;
import cora.terms.*;
import cora.terms.positions.*;

public class VariableTest {
  private Type baseType(String name) {
    return new Sort(name);
  }

  private Type arrowType(String name1, String name2) {
    return new ArrowType(baseType(name1), baseType(name2));
  }

  private Term constantTerm(String name, Type type) {
    return new Constant(name, type);
  }

  private Term unaryTerm(String name, Type output, Term arg) {
    Type arrtype = new ArrowType(arg.queryType(), output);
    FunctionSymbol f = new Constant(name, arrtype);
    return new FunctionalTerm(f, arg);
  }

  private Term twoArgTerm() {
    Type type = new ArrowType(baseType("a"), arrowType("b", "a"));
    FunctionSymbol f = new Constant("f", type);
    Term arg1 = constantTerm("c", baseType("a"));
    Term arg2 = unaryTerm("g", baseType("b"), constantTerm("d", baseType("b")));
    return new FunctionalTerm(f, arg1, arg2);
  }

  @Test(expected = NullInitialisationError.class)
  public void testVarNullName() {
    Variable x = new Var(null, baseType("o"));
  }

  @Test(expected = NullInitialisationError.class)
  public void testVarNullType() {
    Variable x = new Var("x", null);
  }

  @Test(expected = NullInitialisationError.class)
  public void testVarNullTypeWithoutName() {
    Variable x = new Var(null);
  }

  @Test(expected = NullInitialisationError.class)
  public void testBinderVariableNullName() {
    Variable x = new BinderVariable(null, baseType("o"));
  }

  @Test(expected = NullInitialisationError.class)
  public void testBinderVariableNullType() {
    Variable x = new BinderVariable("x", null);
  }

  @Test(expected = NullInitialisationError.class)
  public void testBinderVariableNullTypeWithoutName() {
    Variable x = new BinderVariable(null);
  }

  @Test(expected = NullInitialisationError.class)
  public void testUnitVariableNullName() {
    Variable x = new UnitVariable(null);
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testRootRequest() {
    Variable x = new Var("x", baseType("o"));
    x.queryRoot();
  }

  @Test(expected = IndexingError.class)
  public void testSubtermRequest() {
    Variable x = new UnitVariable("x");
    x.queryImmediateSubterm(1);
  }

  @Test(expected = NullCallError.class)
  public void testNullSubstitution() {
    Term t = new BinderVariable("x", baseType("Int"));
    t.substitute(null);
  }

  @Test(expected = NullCallError.class)
  public void testNullMatch1() {
    Term t = new Var("x", baseType("Int"));
    t.match(constantTerm("37", baseType("Int")), null);
  }

  @Test(expected = NullCallError.class)
  public void testNullMatch2() {
    Term t = new Var("x", baseType("Int"));
    Substitution subst = new Subst();
    t.match(null, subst);
  }

  @Test(expected = ArityError.class)
  public void testBaseVariableApplication() {
    Term t = new Var("x", baseType("Int"));
    t.apply(t);
  }

  @Test(expected = TypingError.class)
  public void testIllegalTypeApplication() {
    Term t = new Var("x", arrowType("a", "b"));
    Term q = constantTerm("c", baseType("b"));
    t.apply(q);
  }

  @Test(expected = TypingError.class)
  public void testMatchWithBadType() {
    Term t = new UnitVariable();
    Term q = twoArgTerm();
    t.match(q);
  }

  @Test
  public void testTermVarBasics() {
    Variable x = new Var("x", baseType("o"));
    Term s = x;
    assertTrue(s.isVariable());
    assertTrue(s.isVarTerm());
    assertFalse(s.isConstant());
    assertFalse(s.isFunctionalTerm());
    assertFalse(x.isBinderVariable());
    assertTrue(s.queryVariable().equals(x));
    assertTrue(s.toString().equals("x"));
    assertTrue(s.numberImmediateSubterms() == 0);
    assertTrue(s.isPattern());
    assertTrue(s.isFirstOrder());
    Variable y = new Var("x", baseType("o"));
    assertTrue(x.queryVariableIndex() != y.queryVariableIndex());
    Variable z = new Var("z", arrowType("o", "o"));
    assertFalse(z.isFirstOrder());
    assertTrue(z.isPattern());
    assertTrue(z.apply(y).equals(new VarTerm(z, y)));
  }

  @Test
  public void testBinderVarBasics() {
    Variable x = new BinderVariable(arrowType("a", "b"));
    Variable y = new BinderVariable(arrowType("a", "b"));
    Variable z = new BinderVariable(Sort.unitSort);
    assertTrue(x.isVariable());
    assertTrue(x.isBinderVariable());
    assertFalse(x.equals(y));
    assertFalse(x.toString().equals(y.toString()));
    assertFalse(x.isFirstOrder());
    assertFalse(z.isFirstOrder());    // binders are never first order
  }

  @Test
  public void testUnitVarBasics() {
    Variable x = new UnitVariable("x");
    Variable y = new UnitVariable();
    assertFalse(x.equals(y));
    assertTrue(x.queryType().equals(Sort.unitSort));
    assertTrue(y.isFirstOrder());
    assertTrue(x.queryVariableIndex() != y.queryVariableIndex());
  }

  @Test
  public void testTermVarVars() {
    Variable x = new Var("x", baseType("oo"));
    Environment env = x.vars();
    assertTrue(env.size() == 1);
    assertTrue(env.contains(x));
    Environment other = new Env();
    other.add(new BinderVariable("y", baseType("aa")));
    x.updateVars(other);
    assertTrue(other.size() == 2);
    assertTrue(other.contains(x));
    x.updateVars(other);
    assertTrue(other.size() == 2);
  }

  @Test
  public void testTermVarEquality() {
    Term s1 = new Var("x", Sort.unitSort);
    Term s2 = new Var("x", Sort.unitSort);
    Term s3 = new UnitVariable("x");
    Term s4 = new UnitVariable("x");
    Term s5 = new BinderVariable("x", Sort.unitSort);
    Term s6 = new BinderVariable("x", Sort.unitSort);
    assertTrue(s1.equals(s1));
    assertTrue(s3.equals(s3));
    assertTrue(s5.equals(s5));
    assertFalse(s1.equals(s2));
    assertFalse(s3.equals(s4));
    assertFalse(s5.equals(s6));
    assertFalse(s1.equals(s3));
    assertFalse(s3.equals(s5));
    assertFalse(s6.equals(s2));
  }

  @Test
  public void testVarOrFunctionalTerm() {
    Term s1 = new Var("x", baseType("o"));
    Term s2 = constantTerm("x", baseType("o"));
    assertFalse(s1.equals(s2));
    assertTrue(s1.toString().equals(s2.toString()));
  }

  @Test
  public void testPositions() {
    Term s = new UnitVariable("x");
    List<Position> lst = s.queryAllPositions();
    assertTrue(lst.size() == 1);
    assertTrue(lst.get(0).toString().equals("ε"));
  }

  @Test
  public void testSubtermGood() {
    Term s = new BinderVariable("x", baseType("o"));
    Position p = new EmptyPosition();
    assertTrue(s.querySubterm(p).equals(s));
  }

  @Test(expected = IndexingError.class)
  public void testSubtermBad() {
    Term s = new Var("x", baseType("o"));
    Position p = new ArgumentPosition(1, new EmptyPosition());
    Term t = s.querySubterm(p);
  }

  @Test
  public void testSubtermReplacementGood() {
    Term s = new Var("x", baseType("a"));
    Term t = twoArgTerm();
    Position p = new EmptyPosition();
    assertTrue(s.replaceSubterm(p, t).equals(t));
    assertTrue(s.toString().equals("x"));
  }

  @Test(expected = IndexingError.class)
  public void testVarSubtermReplacementBad() {
    Term s = new Var("x", baseType("o"));
    Position p = new ArgumentPosition(1, new EmptyPosition());
    Term t = s.replaceSubterm(p, twoArgTerm());
  }

  @Test(expected = IndexingError.class)
  public void testBinderVariableSubtermReplacementBad() {
    Term s = new BinderVariable("x", baseType("o"));
    Position p = new ArgumentPosition(1, new EmptyPosition());
    Term t = s.replaceSubterm(p, twoArgTerm());
  }

  @Test(expected = IndexingError.class)
  public void testUnitVariableSubtermReplacementBad() {
    Term s = new UnitVariable();
    Position p = new ArgumentPosition(1, new EmptyPosition());
    Term t = s.replaceSubterm(p, twoArgTerm());
  }

  @Test
  public void testSubstituting() {
    Variable x = new Var("x", baseType("Int"));
    Variable y = new BinderVariable("y", baseType("Int"));
    Variable z = new UnitVariable("z");
    Term xterm = constantTerm("37", baseType("Int"));
    Substitution gamma = new Subst(x, xterm);
    gamma.extend(y, x); 
    assertTrue(x.substitute(gamma).equals(xterm));
    assertTrue(y.substitute(gamma).equals(x));
    assertTrue(z.substitute(gamma).equals(z));
    gamma.replace(y, xterm);
    gamma.extend(z, constantTerm("bing", Sort.unitSort));
    assertTrue(y.substitute(gamma).equals(xterm));
    assertTrue(z.substitute(gamma).equals(constantTerm("bing", Sort.unitSort)));
  }

  @Test
  public void testVarMatchingNoMapping() {
    Variable x = new Var(baseType("a"));
    Term t = twoArgTerm();
    Subst gamma = new Subst();
    assertTrue(x.match(t, gamma) == null);
    assertTrue(gamma.get(x).equals(t));
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testVarMatchingExistingMapping() {
    Variable x = new Var("x", baseType("a"));
    Term t = twoArgTerm();
    Subst gamma = new Subst(x, t);
    assertTrue(x.match(t, gamma) == null);
    assertTrue(gamma.get(x).equals(t));
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testVarMatchingConflictingMapping() {
    Variable x = new Var("x", baseType("a"));
    Term t = twoArgTerm();
    Term q = new Var("y", baseType("a"));
    Subst gamma = new Subst(x, q);
    assertTrue(x.match(t, gamma) != null);
    assertTrue(gamma.get(x).equals(q));
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testUnitVarMatchingNoMapping() {
    Variable x = new UnitVariable("x");
    Term t = constantTerm("bing", Sort.unitSort);
    Subst gamma = new Subst();
    assertTrue(x.match(t, gamma) == null);
    assertTrue(gamma.get(x).equals(t));
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testUnitVarMatchingExistingMapping() {
    Variable x = new UnitVariable();
    Term t = constantTerm("bing", Sort.unitSort);
    Subst gamma = new Subst(x, t);
    assertTrue(x.match(t, gamma) == null);
    assertTrue(gamma.get(x).equals(t));
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testUnitVarMatchingConflictingMapping() {
    Variable x = new UnitVariable("x");
    Term t = constantTerm("bing", Sort.unitSort);
    Term q = new Var("y", Sort.unitSort);
    Subst gamma = new Subst(x, q);
    assertTrue(x.match(t, gamma) != null);
    assertTrue(gamma.get(x).equals(q));
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testBinderVarMatchingFailure() {
    Variable x = new BinderVariable("x", baseType("a"));
    Term t = twoArgTerm();
    Subst gamma = new Subst();
    assertFalse(x.match(t, gamma) == null);
    assertTrue(gamma.domain().size() == 0);
  }

  @Test
  public void testMatchBinderVarToOtherBinder() {
    Variable x = new BinderVariable("x", baseType("a"));
    Variable y = new BinderVariable("y", baseType("a"));
    Subst gamma = new Subst();
    assertTrue(x.match(y, gamma) == null);
    assertTrue(gamma.get(x).equals(y));
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testMatchBinderVarToNonBinderVariable() {
    Variable x = new BinderVariable("x", baseType("a"));
    Variable y = new Var("y", baseType("a"));
    Subst gamma = new Subst();
    assertFalse(x.match(y, gamma) == null);
  }

  @Test
  public void testBinderVarMatchingExistingMapping() {
    Variable x = new BinderVariable("x", baseType("a"));
    Variable y = new BinderVariable("y", baseType("a"));
    Subst gamma = new Subst(x, y);
    assertTrue(x.match(y, gamma) == null);
    assertTrue(gamma.get(x).equals(y));
    assertTrue(gamma.domain().size() == 1);
  }

  @Test
  public void testBinderVarMatchingConflictingMapping() {
    Variable x = new Var("x", baseType("a"));
    Variable y = new BinderVariable("y", baseType("a"));
    Variable z = new BinderVariable("y", baseType("a"));
    Subst gamma = new Subst(x, y);
    assertTrue(x.match(z, gamma) != null);
    assertTrue(gamma.get(x).equals(y));
    assertTrue(gamma.domain().size() == 1);
  }
}
