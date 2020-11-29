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
import java.lang.Error;
import java.util.ArrayList;
import cora.exceptions.InappropriatePatternDataError;
import cora.exceptions.IndexingError;
import cora.exceptions.NullInitialisationError;
import cora.exceptions.ArityError;
import cora.exceptions.TypingError;
import cora.interfaces.types.Type;
import cora.interfaces.terms.FunctionSymbol;
import cora.interfaces.terms.Term;
import cora.types.*;
import cora.terms.positions.*;
import cora.terms.Constant;
import cora.terms.Var;
import cora.terms.FunctionalTerm;
import cora.terms.Subst;

public class ConstantTest {
  private Type baseType(String name) {
    return new Sort(name);
  }

  @Test(expected = NullInitialisationError.class)
  public void testConstantNullName() {
    FunctionSymbol f = new Constant(null, baseType("o"));
  }

  @Test(expected = java.lang.Error.class)
  public void testConstantEmptyName() {
    FunctionSymbol f = new Constant("", baseType("o"));
  }

  @Test(expected = NullInitialisationError.class)
  public void testConstantNullType() {
    FunctionSymbol f = new Constant("bing", null);
  }

  @Test(expected = ArityError.class)
  public void testBaseConstantApply() {
    FunctionSymbol c = new Constant("c", baseType("o"));
    c.apply(new Constant("a", baseType("o")));
  }

  @Test(expected = TypingError.class)
  public void testIllTypedApply() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type c = baseType("c3");
    Type combi = new ArrowType(a, new ArrowType(b, c));
    FunctionSymbol f = new Constant("ff", combi);
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(new Constant("aa", a));
    args.add(new Constant("bb", a));
    f.apply(args);
  }

  @Test
  public void testFunctionSymbolBasics() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type c = baseType("c3");
    Type combi = new ArrowType(a, new ArrowType(b, c));
    FunctionSymbol f = new Constant("ff", combi);
    assertTrue(f.queryName().equals("ff"));
    assertTrue(f.toString().equals("ff"));
    assertTrue(f.queryType().equals(combi));
    ArrayList<Term> args = new ArrayList<Term>();
    args.add(new Constant("aa", a));
    args.add(new Constant("bb", b));
    assertTrue(f.apply(args).toString().equals("ff(aa, bb)"));
  }

  @Test
  public void testFunctionSymbolEquality() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type c = baseType("c3");
    Type combi = new ArrowType(a, new ArrowType(b, c));
    FunctionSymbol f = new Constant("ff", combi);
    FunctionSymbol g = new Constant("ff", combi);
    FunctionSymbol h = new Constant("f", combi);
    FunctionSymbol i = new Constant("f", new ArrowType(a,c));

    assertTrue(f.equals(g));
    assertFalse(f.equals(h));
    assertFalse(f.equals(i));
    assertFalse(f.equals(null));
  }

  @Test(expected = InappropriatePatternDataError.class)
  public void testVariableRequest() {
    Term f = new Constant("f", baseType("a"));
    Term x = f.queryVariable();
  }

  @Test(expected = IndexingError.class)
  public void testBadPositionRequest() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type combi = new ArrowType(a, b);
    Constant f = new Constant("f", combi);
    Term tmp = f.querySubterm(SubPosition.makeFunctionalPos(1, new RootPosition()));
  }

  @Test(expected = IndexingError.class)
  public void testBadPositionReplacement() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type combi = new ArrowType(a, b);
    Constant f = new Constant("f", combi);
    Term tmp = f.replaceSubterm(SubPosition.makeFunctionalPos(1, new RootPosition()),
                                new Constant("a", a));
  }

  @Test
  public void testTermBasics() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type c = baseType("c3");
    Type combi = new ArrowType(a, new ArrowType(b, c));
    Term f = new Constant("ff", combi);
    Var x = new Var("ff", combi);

    assertTrue(f.queryType().equals(combi));
    assertTrue(f.isConstant());
    assertTrue(f.isFunctionalTerm());
    assertFalse(f.isVariable());
    assertFalse(f.isVarTerm());
    assertFalse(f.isAbstraction());
    assertTrue(f.numberImmediateSubterms() == 0);
    assertTrue(f.queryRoot().equals(f));
    assertTrue(f.queryAllPositions().size() == 1);
    assertTrue(f.queryAllPositions().get(0).isEmpty());
    assertTrue(f.querySubterm(new RootPosition()).equals(f));
    assertTrue(f.replaceSubterm(new RootPosition(), x).equals(x));
    assertFalse(f.isFirstOrder());
    assertTrue(f.isPattern());
    Subst gamma = new Subst(x, new Constant("gg", combi));
    assertTrue(f.substitute(gamma).equals(f));
    assertTrue(f.freeVars().size() == 0);
    assertTrue(f.boundVars().size() == 0);
    Term aa = new Constant("g", a);
    assertTrue(aa.isFirstOrder());
    assertTrue(aa.isPattern());
  }

  @Test
  public void testTermEquality() {
    Type a = baseType("a");
    Type b = baseType("b");
    Type combi = new ArrowType(a, b);
    Constant f = new Constant("f", combi);
    Constant g = new Constant("f", combi);
    Constant h = new Constant("h", combi);

    assertTrue(f.equals((Term)f));
    assertTrue(f.equals((Term)g));
    assertFalse(f.equals((Term)h));

    ArrayList<Term> args = new ArrayList<Term>();
    Term ff = new FunctionalTerm(f, args);
    Term gg = new FunctionalTerm(g, args);
    args.add(new Constant("aa", a));
    Term fa = new FunctionalTerm(f, args);

    assertTrue(f.equals(ff));
    assertTrue(f.equals(gg));
    assertFalse(f.equals(a));

    assertTrue(f.match(ff) != null);
  }
}
