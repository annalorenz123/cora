package cora.smt;

import charlie.smt.*;
import cora.smt.*;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;

public class SimplexTest{
    
    @Test
    public void testQValue(){
        assertThrows(IllegalArgumentException.class, () -> new QValue(1,0));
        assertThrows(IllegalArgumentException.class, () -> new QValue(0,0));
        assertThrows(IllegalArgumentException.class, () -> new QValue(-4,0));
        assertThrows(IllegalArgumentException.class, () -> new QValue(-4,-0));


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
        //assertFalse(internalSolver.positiveFactor(new QAddition (new QValue(-1,1), new QMult(new QValue(0,1), new QVar(4)))));



    }

    @Test
    public void testPositiveFactor2(){
        assertEquals(true, true);
    }
}