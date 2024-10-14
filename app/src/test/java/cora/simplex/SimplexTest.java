package cora.smt;

import charlie.smt.*;
import cora.smt.*;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;

public class SimplexTest{
    
    static Logger logger = Logger.getLogger(SimplexTest.class.getName());

    @Test
    public void testQValue(){
        assertThrows(IllegalArgumentException.class, () -> new QValue(1,0));
        assertThrows(IllegalArgumentException.class, () -> new QValue(0,0));
        assertThrows(IllegalArgumentException.class, () -> new QValue(-4,0));
        assertThrows(IllegalArgumentException.class, () -> new QValue(-4,-0));


    }

    @Test
    public void testQValueSimplify(){
        QValue q = new QValue(1,3);
        QValue q2 = new QValue(2,6);
        QValue q3 = new QValue(1,6);
        QValue q4 = new QValue(4,9);
        assertEquals(q.compareTo(q2), 0);
        assertEquals(q3.compareTo(q.simplify(q, new QValue(2,1))),0);
        assertEquals(q4.compareTo(q.simplify(new QValue(1,3), new QValue(3,4))),0);

    }



    @Test
    public void testPositiveFactor(){
        InternalSolver internalSolver = new InternalSolver();
        assertFalse(internalSolver.positiveFactor(new QMult(new QValue(-1,1), new QVar(1))));
        assertTrue(internalSolver.positiveFactor(new QMult(new QValue(1,1), new QVar(1))));
        assertFalse(internalSolver.positiveFactor(new QValue(-1,1)));
        assertFalse(internalSolver.positiveFactor(new QValue(1,1)));
        assertTrue(internalSolver.positiveFactor(new QVar(1)));
        assertFalse(internalSolver.positiveFactor(new QAddition (new QValue(-1,1), new QMult(new QValue(-3,1), new QVar(2)))));
        assertTrue(internalSolver.positiveFactor(new QAddition (new QValue(-1,1), new QMult(new QValue(5,1), new QVar(3)))));
        assertFalse(internalSolver.positiveFactor(new QAddition (new QValue(-1,1), new QMult(new QValue(0,1), new QVar(4)))));
        assertFalse(internalSolver.positiveFactor(new QAddition (new QMult(new QValue(0,1), new QVar(4)), new QValue(-1,1))));
    }

    @Test
    public void testBasicSolution (){
        InternalSolver internalSolver = new InternalSolver();
        ArrayList<QExpression> test1 = new ArrayList<>(Arrays.asList(new QVar(1), new QValue (-1,1)));
        assertFalse(internalSolver.basicSolution(test1));

    }

    @Test
    public void testReplace(){
        //expr, oldvar, newexpr
        InternalSolver internalSolver = new InternalSolver();
        QVar x = new QVar(1);
        QVar y = new QVar(2);
        logger.log(Level.INFO, internalSolver.replace(x, x, y).toString());
        assertEquals(internalSolver.replace(x, x, y).compareTo(y), 0);


    }

    @Test
    public void testFindMinBound(){
        //test1
        InternalSolver internalSolver = new InternalSolver();
        QVar x = new QVar(1);
        QExpression expr1 = new QAddition(new ArrayList<QExpression>(Arrays.asList(new QValue(7,1), new QMult(new QValue(-3,1), x),new QMult(new QValue(2,1), new QVar(2)),new QMult(new QValue(-1,1), new QVar(3)))));
        QExpression expr2 = new QAddition(new ArrayList<QExpression>(Arrays.asList(new QValue(12,1), new QMult(new QValue(-5,1), x),new QMult(new QValue(4,1), new QVar(2)),new QMult(new QValue(6,1), new QVar(3)))));
        QExpression expr3 = new QValue (7,1);
        QExpression expr4 = new QMult (new QValue(7,1), x);
        ArrayList <QExpression> qexpressions = new ArrayList<>();
        qexpressions.add(x);
        qexpressions.add(expr1);
        qexpressions.add(expr2);
        qexpressions.add(expr3);
        qexpressions.add(expr4);
        System.out.println (internalSolver.findMinBound(qexpressions,x));
        assertEquals(internalSolver.findMinBound(qexpressions, x), expr1);
        
        //test2
        qexpressions.clear();
        QExpression expr5 = new QAddition (new ArrayList<QExpression>(Arrays.asList(new QValue(-12,1), new QMult(new QValue(-1,1), x))));
        qexpressions.add(x);
        qexpressions.add(expr5);
        assertThrows(Error.class, () -> internalSolver.findMinBound(qexpressions, x));

        //test3
        qexpressions.clear();
        qexpressions.add(x);
        qexpressions.add(new QAddition (new ArrayList<QExpression>(Arrays.asList(new QValue(-12,1), new QMult(new QValue(1,1), x)))));
        assertThrows(Error.class, () -> internalSolver.findMinBound(qexpressions, x));

        //test4
        qexpressions.add(expr1);
        assertEquals(internalSolver.findMinBound(qexpressions, x), expr1);
    }

    @Test
    public void testExprWithLowestConstant(){
        InternalSolver internalSolver = new InternalSolver();
        QVar x = new QVar(1);
        QExpression expr1 = new QAddition(new ArrayList<QExpression>(Arrays.asList(new QValue(7,1), new QMult(new QValue(-3,1), x),new QMult(new QValue(2,1), new QVar(2)),new QMult(new QValue(-1,1), new QVar(3)))));
        QExpression expr2 = new QAddition(new ArrayList<QExpression>(Arrays.asList(new QValue(-13,1), new QMult(new QValue(-3,1), x),new QMult(new QValue(2,1), new QVar(2)),new QMult(new QValue(-1,1), new QVar(3)))));
        QExpression expr3 = new QAddition(new ArrayList<QExpression>(Arrays.asList(new QValue(-2,1), new QMult(new QValue(-3,1), x),new QMult(new QValue(2,1), new QVar(2)),new QMult(new QValue(-1,1), new QVar(3)))));
        QExpression expr4 = new QMult(new QValue(-15,1), new QVar(2));
        ArrayList <QExpression> qexpressions = new ArrayList<>();
        qexpressions.add(expr1);
        qexpressions.add(expr2);
        qexpressions.add(expr3);
        qexpressions.add(expr4);
        assertEquals(internalSolver.exprWithLowestConstant(qexpressions), expr2);
    }

    @Test
    public void testgetRoundedValuations(){

    
    }



}