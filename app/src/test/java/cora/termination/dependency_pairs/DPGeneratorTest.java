package cora.termination.dependency_pairs;

import cora.parsing.CoraInputReader;
import cora.rewriting.Rule;
import cora.rewriting.RuleFactory;
import cora.terms.FunctionSymbol;
import cora.terms.TermFactory;
import cora.types.Type;
import cora.types.TypeFactory;
import org.junit.jupiter.api.Test;
import cora.terms.Term;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.junit.jupiter.api.Assumptions.assumingThat;

class DPGeneratorTest {

  @Test
  void testGenerateVarsNotArrowTypeGivesEmptyList() {
    Type ty = TypeFactory.createSort("a");
    assertTrue(DPGenerator.generateVars(ty).isEmpty());
  }

  @Test
  void testGenerateVarsArrow() {
    // (int => int) => int => int
    Type ty = TypeFactory.createArrow(
      TypeFactory.createArrow(
        TypeFactory.intSort,
        TypeFactory.intSort
      ),
      TypeFactory.createArrow(
        TypeFactory.boolSort,
        TypeFactory.boolSort
      )
    );

    List<Term> dpVars = DPGenerator.generateVars(ty);

    assertEquals(2,dpVars.size());

    //generateVars correctly creates variables of arrow types
    assertEquals(
      dpVars.get(0).queryType(),
      TypeFactory.createArrow(
        TypeFactory.intSort,
        TypeFactory.intSort
      )
    );
    //and of other types
    assertEquals(
      dpVars.get(1).queryType(),
      TypeFactory.boolSort
    );
  }

  @Test
  void testGenerateDpType() {
    Type ty =
      CoraInputReader.readTypeFromString("Bool");
    Type depTy = DPGenerator.generateDpType(ty);

    assumingThat(ty.isBaseType() || ty.isProdType(),  () -> {
      assertTrue(DPGenerator.dpSort.equals(depTy));
    });

    assumingThat(ty.isArrowType(), () -> {
      assertSame(DPGenerator.generateDpType(ty).queryOutputType(), DPGenerator.dpSort);
    });
  }

  @Test
  void testGenerateSharpFn() {
    FunctionSymbol f = TermFactory.
      createConstant("f", CoraInputReader.readTypeFromString("Bool -> Int"));
    FunctionSymbol fSharp = DPGenerator.generateSharpFn(f);

    // the fsharp symbol is named correctly.
    assertEquals(fSharp.toString(), f.toString() + "#");

    // the fsharp symbol has the correct type, which is generated by generateDpType.
    assertTrue(DPGenerator.generateDpType(f.queryType()).equals(fSharp.queryType()));
  }

  @Test
  void testFakeEta(){
    Type arr =
      CoraInputReader.readTypeFromString("Bool -> b -> c -> d -> e");
    Term f = TermFactory.createConstant("f",arr);
    Term x = TermFactory.createVar(TypeFactory.boolSort);

    System.out.println(f + ":" + f.queryType());

    System.out.println("fake eta result");

    System.out.println(DPGenerator.fakeEta(f.apply(x)));
  }

  @Test
  void testGenLeftSharpRule() {
    Type arr =
      CoraInputReader.readTypeFromString(
        "Bool -> b -> c -> d -> e"
      );
    Term f = TermFactory.createConstant("f",arr);
    System.out.println("Normal lhs: " + f + ":" + f.queryType());
    System.out.println("DP lhs: " + DPGenerator.generateSharpEta(f));
    System.out.println("With f : " + DPGenerator.generateSharpEta(f).queryRoot().queryType());
  }

  @Test
  void testGenRightCandidates() {
    Term f = TermFactory.createConstant("f",
        CoraInputReader.readTypeFromString("a -> b -> c"));
    Type a = CoraInputReader.readTypeFromString("a");
    Term c = TermFactory.createConstant("c", a);
    Term g = TermFactory.createConstant("g",
        CoraInputReader.readTypeFromString("a -> a"));
    Term gc = TermFactory.createApp(g,c);
    Term lhs = TermFactory.createApp(f, c);
    Term rhs = TermFactory.createApp(f, List.of(gc));
    Term eta = DPGenerator.fakeEta(rhs);

    // Printing part
    System.out.println("Original lhs: " + lhs + " : " + lhs.queryType());
    System.out.println("Original rhs: " + rhs + " : " + rhs.queryType());
//    System.out.println("Fake eta expanded form: " + eta + " : " + eta.queryType());
//    System.out.println(DPGenerator.genRightCandidates(eta));

    DP t = new DP(f, f, f);

//    System.out.println(t);
//    Rule r = RuleFactory.createRule(lhs, rhs);
//    System.out.println (
//        DPGenerator.generateProblemFromRule(r)
//    );

  }
}
