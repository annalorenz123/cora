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

package charlie.terms;

import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.Set;
import charlie.types.*;

/**
 * Not too many tests here, because most testing is actually done through the toString() functions
 * of the various kinds of terms.
 */
public class TermPrinterTest {
  @Test
  public void testRenamingWithoutAvoidance() {
    Type a = TypeFactory.createSort("a");
    Type b = TypeFactory.createSort("b");
    Type ab = TypeFactory.createArrow(a, b);
    Variable x1 = new Var("x", a);
    Variable x2 = new Var("x", a);
    Variable x3 = new Binder("x", b);
    MetaVariable mvar = TermFactory.createMetaVar("x", TypeFactory.createArrow(a, a), 1);
    Term x4 = TermFactory.createMeta(mvar, TermFactory.createConstant("A", a));
    Variable y = new Binder("y", b);
    Variable z1 = new Binder("z", ab);
    Variable z2 = new Var("z", ab);
    TermPrinter printer = new TermPrinter(Set.of());
    Renaming naming = printer.generateUniqueNaming(x1, x2, x3, x4, y, z1, z2);
    assertTrue(naming.getName(x1).equals("x__2"));
    assertTrue(naming.getName(x2).equals("x__3"));
    assertTrue(naming.getName(x3).equals("x__4"));
    assertTrue(naming.getName(mvar).equals("x__1"));  // meta-variables come before variables
    assertTrue(naming.getName(y).equals("y"));
    assertTrue(naming.getName(z1).equals("z__2"));  // binders come after non-binders
    assertTrue(naming.getName(z2).equals("z__1"));
  }

  @Test
  public void testBannedOverlap() {
    TermPrinter printer = new TermPrinter(Set.of("x", "y__1", "z", "z__1", "u", "v__1"));
    Type o = TypeFactory.defaultSort;
    Variable x = new Var("x", o);
    Variable y1 = new Var("y", o);
    Variable y2 = new Var("y", o);
    Variable z = new Binder("z", o);
    Variable u1 = new Var("u", o);
    Variable u2 = new Var("u", o);
    Variable v = new Var("v", o);
    Variable w = new Var("", o);
    Variable a = new Var("17", o);
    Variable b1 = new Var("b", o);
    Variable b2 = new Var("b", o);
    Variable b3 = new Var("b__1", o);
    Renaming naming = printer.generateUniqueNaming(x, y1, y2, z, u1, u2, v, w, a, b1, b2, b3);
    assertTrue(naming.getName(x).equals("x__1"));
    assertTrue(naming.getName(y1).equals("y__3"));
    assertTrue(naming.getName(y2).equals("y__2"));
    assertTrue(naming.getName(z).equals("z__2"));
    assertTrue(naming.getName(u1).equals("u__1"));
    assertTrue(naming.getName(u2).equals("u__2"));
    assertTrue(naming.getName(v).equals("v"));
    assertTrue(naming.getName(w).equals("VAR"));
    assertTrue(naming.getName(a).equals("_17"));
    assertTrue(naming.getName(b1).equals("b__3"));
    assertTrue(naming.getName(b2).equals("b__2"));
    assertTrue(naming.getName(b3).equals("b__1"));
  }

  @Test
  public void testBoundVariableRenaming() {
    Type o = TypeFactory.defaultSort;
    Variable x = new Binder("x", o);
    Variable y = new Binder("y", o);
    Term abs1 = new Abstraction(x, x);
    Term abs2 = new Abstraction(y, y);
    Type oo = TypeFactory.createArrow(o, o);
    Term f =
      TermFactory.createConstant("f", TypeFactory.createArrow(oo, TypeFactory.createArrow(oo, o)));
    Term term = TermFactory.createApp(f, abs1, abs2); // f(λx.x, λy.y)

    TermPrinter printer = new TermPrinter(Set.of());
    Renaming naming = printer.generateUniqueNaming(term, x);
    assertTrue(naming.getName(x).equals("x"));
    assertTrue(naming.getName(y) == null);
    assertFalse(naming.isAvailable("x"));
    assertTrue(naming.isAvailable("y"));
    StringBuilder builder = new StringBuilder();
    printer.print(term, naming, builder);
    assertTrue(naming.getName(x).equals("x"));
    assertTrue(naming.getName(y) == null);
    assertFalse(naming.isAvailable("x"));
    assertTrue(naming.isAvailable("y"));
    assertTrue(builder.toString().equals("f(λx1.x1, λy.y)"));
  }

  @Test
  public void testIncompleteRenamingUsedWithAbstraction() {
    Type o = TypeFactory.createSort("o");
    // λx.λy.λu.f(g(z2,u),z1,x) where x and u have the same name, and z1 and z2 too
    Variable x = new Binder("x", o);
    Variable y = new Binder("y", o);
    Variable z1 = new Binder("z", o);
    Variable z2 = new Binder("z", o);
    Variable u = new Binder("x", o);
    Constant f = new Constant("f", TypeFactory.createArrow(o, TypeFactory.createArrow(o,
      TypeFactory.createArrow(o, o))));
    Constant g = new Constant("g", TypeFactory.createArrow(o, TypeFactory.createArrow(o, o)));
    Term main = (new Application(f, new Application(g, z2, u), z1)).apply(x);
    Term abs = new Abstraction(x, new Abstraction(y, new Abstraction(u, main)));

    TermPrinter printer = new TermPrinter(Set.of());
    Renaming naming = printer.generateUniqueNaming(abs);

    StringBuilder builder = new StringBuilder();
    printer.print(abs, naming, builder);
    assertTrue(builder.toString().equals("λx.λy.λx1.f(g(z__2, x1), z__1, x)"));

    builder.setLength(0);
    naming = new Renaming(Set.of());
    printer.print(abs, naming, builder);
    assertEquals("λx.λy.λx1.f(g(z, x1), z, x)", builder.toString());

    builder.setLength(0);
    naming = printer.generateUniqueNaming(new Var("x", o));
    printer.print(abs, naming, builder);
    assertEquals("λx1.λy.λx2.f(g(z, x2), z, x1)", builder.toString());
  }

  @Test
  public void testAvoidName() {
    // create f(x, y) and a loose variable z
    Type o = TypeFactory.createSort("o");
    Variable x = new Var("x", o);
    Variable y = new Var("y", o);
    Variable z = new Var("z", o);
    Constant f = new Constant("f", TypeFactory.createArrow(o, TypeFactory.createArrow(o, o)));
    Term term = f.apply(x).apply(y);

    TermPrinter printer = new TermPrinter(Set.of());
    Renaming a = printer.generateUniqueNaming(term);
    printer.avoidAdditional(Set.of("x", "z"));
    Renaming b = printer.generateUniqueNaming(term);

    assertTrue(printer.print(term, a).equals("f(x, y)"));
    assertTrue(printer.print(term, b).equals("f(x__1, y)"));
    assertTrue(printer.print(z, a).equals("z"));
    assertTrue(printer.print(z, b).equals("z"));

    printer.avoidAdditional("y");
    assertTrue(printer.print(term, b).equals("f(x__1, y)"));
    Renaming c = printer.generateUniqueNaming(term);
    assertTrue(printer.print(term, c).equals("f(x__1, y__1)"));
  }
}

