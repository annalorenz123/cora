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
}