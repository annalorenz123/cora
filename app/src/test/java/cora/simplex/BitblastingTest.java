package cora.smt;

import charlie.smt.*;
import cora.smt.*;
import org.junit.jupiter.api.Test;
import static org.junit.jupiter.api.Assertions.*;
import java.util.*;
import java.util.logging.Logger;
import java.util.logging.Level;

public class BitblastingTest{

    @Test
    public void testGreaterOrEqual(){
        //public static Constraint subtract(ArrayList<Constraint> minuend, ArrayList<Constraint> subtrahend) {
        //return SmtFactory.createNegation(subtract(leftSide, rightSide));
        ArrayList<Constraint> i = BitBlasting.convert((IValue)SmtFactory.createValue(1));
        ArrayList<Constraint> j = BitBlasting.convert((IValue)SmtFactory.createValue(0));
        assertEquals(BitBlasting.greaterOrEqual(i,j).evaluate(), true);

    }

}