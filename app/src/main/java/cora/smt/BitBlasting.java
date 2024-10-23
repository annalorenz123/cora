package cora.smt;

import charlie.smt.*;
import cora.smt.*;
import java.util.ArrayList;
import java.util.List;

public class BitBlasting{
    static int bidWidth = 4;
    static ArrayList<ArrayList<Constraint>> allVariables = new ArrayList<>();


    public static SmtSolver.Answer checkSatisfiability(SmtProblem problem, ArrayList<IntegerExpression> expressions){
        
        for (int i =0; i < problem.numberIntegerVariables(); i++){
            allVariables.add(new ArrayList<>());
        }
        if (expressions.size()==0) return new SmtSolver.Answer.YES(new Valuation());
        ArrayList<IntegerExpression> c = new ArrayList<>();
        //multiple expressions add later
        ArrayList<Constraint> args = new ArrayList<>();
        System.out.println ("number of expressions: " + expressions.size());
        for (int i =0; i < expressions.size(); i++){
            //make switch
            if (expressions.get(i) instanceof Addition a){
                c = makeSides(a);
            }
            else if (expressions.get(i) instanceof CMult cm){
                c = makeSides(cm);
            }
            else if (expressions.get(i) instanceof IVar v){
                c.add(v);
                c.add(SmtFactory.createValue(0));
            }
            // else if (expressions.get(i) instanceof IValue v){
            //     if (v.queryValue() >= 0) c = SmtFactory.createTrue();
            //     else c = SmtFactory.createFalse();
            // }
            else throw new Error("expression of form: " + expressions.get(i) + " not supported yet.");
            System.out.println (c);
            ArrayList<Constraint> leftSide = convert(problem, c.get(0));
            ArrayList<Constraint> rightSide = convert(problem, c.get(1));
            System.out.println ("left side converted: " + leftSide);
            // for (int a =0; a < leftSide.size(); a++){
            //     System.out.println ("s" + a + ": " + leftSide.get(a));
            // }
            // System.out.println ("right side converted: " );
            // for (int a =0; a < rightSide.size(); a++){
            //     System.out.println ("s" + a + ": " + rightSide.get(a));
            // }
            Constraint end = greaterOrEqual(leftSide, rightSide);
            //System.out.println ("end: " + end);
            args.add(end);
            // if (expressions.get(i) instanceof IVar v){
            //     System.out.println ("found variable");
            //     c = convert(problem, v);
            // }
            
            // else if (expressions.get(i) instanceof CMult mult){
            //     c = multiply(convert((IValue)SmtFactory.createValue(mult.queryConstant())), convert(problem, (IVar)mult.queryChild()));
            // }

        }
        Constraint endConjunction = SmtFactory.createConjunction(args);
        // Constraint endConjunction = args.get(0);
        // for (int i =1; i < args.size(); i++){
        //     endConjunction = SmtFactory.createConjunction(endConjunction, args.get(i));
        // }
        
        //System.out.println ("end conjunction: " + endConjunction);
        ArrayList<Valuation> valuations = test(problem, endConjunction);
        if (valuations.size()==0) return new SmtSolver.Answer.NO();
        else {

            Valuation v =  makeValuation (problem, valuations.get(0));
            InternalSolver is = new InternalSolver();
            if (is.extraCheck(v, expressions)){
                return new SmtSolver.Answer.YES(v);
            }
            else throw new Error ("bitblasting gave answer that does not hold: " + v);
        }
        
         
        // for (int i =0; i < c.size(); i++){
        //     System.out.println ("s" + i + ": " + c.get(i));
        // }
        
        //System.out.println ("FINAL FORMULA:" + greaterOrEqual(c));
        
        // if (expressions.size()==1){
        //     System.out.println ("expression size is 1");
        //     if (expressions.get(0) instanceof Addition a){
        //         System.out.println ("expression is addition");
        //         if (a.queryChild(1) instanceof IVar x && a.queryChild(2) instanceof IVar y){
        //             System.out.println ("expression is addition");
        //             Constraint addition = add(problem, x, y);
        //             test(problem, addition);
        //         }  
        //     }
        // }
       
        //return new SmtSolver.Answer.MAYBE("not implemented yet.");



    }

    public static Valuation makeValuation (SmtProblem problem, Valuation v){
        Valuation finalVal = new Valuation();
        System.out.println (allVariables);
        for (int i = 1; i <= problem.numberIntegerVariables(); i++){
            if (allVariables.get(i-1).size() > bidWidth){
                allVariables.set(i-1, removeFalses(allVariables.get(i-1)));
            }
            System.out.println ("int var with index: " + i + " and valuation: " + allVariables.get(i-1));
            int decimal = convertBinToDec (allVariables.get(i-1), v);
            finalVal.setInt(i, decimal);
        }
        return finalVal;
    }

    public static int convertBinToDec (ArrayList<Constraint> binary, Valuation v){
        int power = 0;
        int finalInt = 0;
        for (int i =0; i < binary.size(); i++){
            if (!(binary.get(i) instanceof Falsehood) && v.queryBoolAssignment(((BVar)binary.get(i)).queryIndex())){
                finalInt += Math.pow(2,power);
            }
            power++;
        }
        return finalInt;
    }

    public static int convertBinToDec (ArrayList<Constraint> binary){
        int power = 0;
        int finalInt = 0;
        for (int i =0; i < binary.size(); i++){
            if (! (binary.get(i) instanceof Falsehood) ||  ! (binary.get(i) instanceof Truth) ){
                throw new Error ("not truth and falsehood");
            }
            if (binary.get(i) instanceof Truth){
                finalInt += Math.pow(2,power);
            }
            power++;
        }
        return finalInt;

    }



    public static ArrayList<Constraint> convert (SmtProblem problem, IntegerExpression expression){
        ArrayList<Constraint> constraint = new ArrayList<>();
        switch (expression){
            case IVar v: constraint = convert(problem, v); break;
            case IValue v : constraint = convert(v); break;
            case Addition a : constraint = add(problem, a); break;
            case CMult cm : constraint = multiply(convert((IValue) SmtFactory.createValue(cm.queryConstant())), convert(problem,(IVar) cm.queryChild())); break;
            default : throw new Error (expression + " not supported yet.");
        }
        return constraint;
    }

    // public static Constraint equals (SmtProblem problem, IntegerExpression expression){
    //     switch (expression){
    //         case Addition a : 
    //             return add(problem, a);
    //         case IVar x : //make boolean variables?
    //         case IValue v : //convert to bvar constraint
    //         default : return SmtFactory.createTrue();
             
            
    //     }
        
    // }

    public static IntegerExpression addTerms(IntegerExpression expr1, IntegerExpression expr2) {
        return SmtFactory.createAddition (expr1, expr2);
  }


    public static ArrayList<IntegerExpression> makeSides (CMult cm){
        IntegerExpression leftSide = SmtFactory.createValue(0);
        IntegerExpression rightSide = SmtFactory.createValue(0);
        if (cm.queryConstant() < 0) rightSide= addTerms(rightSide, SmtFactory.createMultiplication(cm.queryConstant()*-1, cm.queryChild()));
        else leftSide = addTerms(cm,leftSide);
        ArrayList<IntegerExpression> result = new ArrayList<>();
        result.add(leftSide.simplify());
        result.add(rightSide.simplify());
        return result;
    }

    public static ArrayList<IntegerExpression> makeSides (Addition a){
        IntegerExpression leftSide = SmtFactory.createValue(0);
        IntegerExpression rightSide = SmtFactory.createValue(0);
        for (int i =1; i <= a.numChildren(); i++){
            switch (a.queryChild(i)){
                case IVar v : leftSide = addTerms(v, leftSide); break;
                case IValue v : 
                    if (v.queryValue() < 0) rightSide= addTerms(rightSide, SmtFactory.createValue(v.queryValue()*-1)); 
                    else leftSide = addTerms(v, leftSide); break;
                case CMult cm : 
                    if (cm.queryConstant() < 0) rightSide= addTerms(rightSide, SmtFactory.createMultiplication(cm.queryConstant()*-1, cm.queryChild()));
                    else leftSide = addTerms(cm,leftSide); break;
                default : throw new Error (a.queryChild(i) + " not supported.");

            }
        }
        ArrayList<IntegerExpression> result = new ArrayList<>();
        result.add(leftSide.simplify());
        result.add(rightSide.simplify());
        return result;
    }


    public static void main(String[] args) {
        int binaryNumber = 0b11111111111111111111111111110110; // Binary for decimal 10
        System.out.println("Binary 0b1010 as decimal: " + binaryNumber);

    }

    public static ArrayList<Constraint> add(SmtProblem problem, Addition a ){
        ArrayList<Constraint> con = new ArrayList<>();
        switch (a.queryChild(1)){
            case IVar v : con = convert(problem, v); break;
            case IValue val : con = convert(val); break;
            case CMult c : con = multiply(convert((IValue)SmtFactory.createValue(c.queryConstant())), convert(problem, (IVar)c.queryChild())); break;
            default: throw new Error(a.queryChild(1).getClass() + " not supported yet.");
        }
        System.out.println (a.queryChild(1) + " converted is " + con);
        for (int j =2; j <= a.numChildren(); j++){
            
            switch (a.queryChild(j)){
                //case IValue val: con = add(problem, con, convert(val)); break;
                case IVar var: con = add(con, convert(problem, var)); break;
                case IValue v : con = add(con, convert(v)); break;
                case CMult c : con = add(con, multiply(convert((IValue)SmtFactory.createValue(c.queryConstant())), convert(problem, (IVar)c.queryChild()))); break;
                default: throw new Error(a.queryChild(j).getClass() + " not supported yet.");
            }
        }
        System.out.println ("result of addition: " + con);
        return con;

    }

    public static ArrayList<Constraint> leftShift(ArrayList<Constraint> formula, int i){
        ArrayList<Constraint> constraints = new ArrayList<>();
        System.out.println ("formula before shifing: " + formula);
        for (int j = 0; j < i; j++){
            formula.add(0, SmtFactory.createFalse());
            //formula.remove(formula.size()-1);
        }
        System.out.println ("formula after shifing: " + formula);
        return formula;
    }

    public static ArrayList<Constraint> multiply(ArrayList<Constraint> lhs, ArrayList<Constraint> rhs) {
        System.out.println ("going to multiply " + lhs + " and " + rhs);

        ArrayList<Constraint> result = new ArrayList<>();

        // Initialize result with zeros
        for (int i = 0; i < bidWidth; i++) {
            result.add(SmtFactory.createFalse()); // Placeholder for zero constraint
        }

        for (int i = 0; i < bidWidth; i++) {
            Constraint left = lhs.get(i);
            if (left.evaluate()){
                ArrayList<Constraint> shifted = leftShift(rhs, i);
                System.out.println ("going to add " + shifted + " AND " + result);
                result = add(shifted, result);
                System.out.println ("result is: " + result);
            }
            //Constraint partialProduct = lhs.get(i).and(rhs);
            //partialProduct = partialProduct.leftShift(i); // Shift left according to the bit position

            // Add partial products to the result
            // for (int j = 0; j < result.size(); j++) {
            //     if (j < partialProduct.size()) { // Ensure we stay within bounds
            //         result.set(j, result.get(j).add(partialProduct)); // Assuming add handles constraints
            //     }
            // }
        }
        System.out.println ("final result is: " + result);
        return result; // This represents the product
    }

    public static ArrayList<Constraint> removeFalses (ArrayList<Constraint> formula){
        System.out.println ("before:" + formula);
        for (int i =0; i < formula.size(); i++){
            if (formula.get(i) instanceof Falsehood) formula.remove(i); i--;
        }
        System.out.println ("after:" + formula);
        return formula;
    }

    public static ArrayList<Constraint> convert (SmtProblem problem, IVar v){
        ArrayList<Constraint> constraints = new ArrayList<>();
        if (!allVariables.get(v.queryIndex()-1).isEmpty()){
            if (allVariables.get(v.queryIndex()-1).size() > bidWidth){
                allVariables.set(v.queryIndex()-1, removeFalses(allVariables.get(v.queryIndex()-1)));
            }
            System.out.println ("i already know " + v.queryName()+ " returning: "+ allVariables.get(v.queryIndex()-1));
            return allVariables.get(v.queryIndex()-1);
        } 
        for (int i =0; i < bidWidth; i++){
            constraints.add(problem.createBooleanVariable());
        }
        System.out.println ("converted " + v + " to " + constraints);
        //return SmtFactory.createConjunction(constraints);
        final ArrayList<Constraint> end =new ArrayList<>(constraints);
        allVariables.set(v.queryIndex()-1, end);
        return constraints;
    }

    public static ArrayList<Constraint> convert (IValue v){
        String value = Integer.toBinaryString(v.queryValue());
        System.out.println (value + " with length " + value.length());
        if (value.length() > bidWidth){
            throw new Error ("Value " + v.queryValue() + " too big for bidwidth.");
        } 
        if (value.length() < bidWidth) {
            value = addZeros(value);
            System.out.println ("added zeros: " + value);
        }
        ArrayList<Constraint> constraints = new ArrayList<>();
        for (int i =bidWidth-1; i >= 0; i--){
            if (value.charAt(i)=='1'){
                constraints.add(SmtFactory.createTrue());
            } 
            else constraints.add(SmtFactory.createFalse());
        }
        //return SmtFactory.createConjunction(constraints);
        return constraints;
    }

    public static String addZeros (String value){
        for (int i = value.length(); i < bidWidth; i++){
            value = "0" + value;
        }
        return value;
    }



    // public static Constraint add (SmtProblem problem, Constraint c, IValue v){
    //     String value = Integer.toBinaryString(v.queryValue());
    //     System.out.println (value);

    //     return SmtFactory.createTrue();

    // }
    
    // public static Constraint add (SmtProblem problem, IVar w, IVar v){
    //     Constraint carry = SmtFactory.createFalse();
    //     Constraint endFormula = SmtFactory.createTrue();
    //     for (int i =0; i < bidWidth; i++){
    //         BVar x_i = SmtFactory.createBooleanVariable(problem);
    //         BVar y_i = SmtFactory.createBooleanVariable(problem);
    //         Constraint x_xor_y = SmtFactory.createConjunction(SmtFactory.createDisjunction(x_i, y_i), SmtFactory.createNegation(SmtFactory.createConjunction(x_i, y_i)));
    //         Constraint sum = SmtFactory.createConjunction(SmtFactory.createDisjunction(x_xor_y, carry), SmtFactory.createNegation(SmtFactory.createConjunction(x_xor_y, carry)));

            
    //         endFormula = SmtFactory.createConjunction(endFormula, sum);
    //         carry = SmtFactory.createDisjunction(SmtFactory.createConjunction(x_i,y_i), SmtFactory.createConjunction(carry, x_xor_y));

    //     }
    //     System.out.println (endFormula);
    //     return endFormula;

    public static Constraint xor (Constraint a, Constraint b){
        //System.out.println ("result of xor: " + SmtFactory.createConjunction(SmtFactory.createDisjunction(a,b).simplify(), SmtFactory.createNegation(SmtFactory.createConjunction(a,b).simplify()).simplify()).simplify());
        return SmtFactory.createConjunction(SmtFactory.createDisjunction(a,b).simplify(), SmtFactory.createNegation(SmtFactory.createConjunction(a,b).simplify()).simplify()).simplify();
        //return SmtFactory.createConjunction(SmtFactory.createDisjunction(a,b), SmtFactory.createNegation(SmtFactory.createConjunction(a,b)));

    }



    public static ArrayList<Constraint> addFalses (ArrayList<Constraint> adding, int size){
        //System.out.println ("going to make " + adding + " the size " + size);
        for (int i = adding.size(); i < size; i++){
            adding.add(SmtFactory.createFalse());
        }
        return adding;

    }
    public static Constraint subtract(ArrayList<Constraint> minuend, ArrayList<Constraint> subtrahend) {
        //System.out.println ("going to subtract "+ minuend + " and " + subtrahend);
        // Ensure both binary numbers are of the same length
        if (minuend.size()!= subtrahend.size()) {
            
            if (minuend.size() < subtrahend.size()){
                minuend = addFalses(minuend, subtrahend.size());
            }
            else subtrahend = addFalses(subtrahend, minuend.size());
            //System.out.println ("not of same size, converted: " + minuend + " and " + subtrahend);
            //throw new Error (minuend + " and " + subtrahend + " not of same size");
        }
        int n = minuend.size();
        //System.out.println ("size of " + minuend + " is " + n);
        ArrayList<Constraint> result = new ArrayList<>();
        Constraint borrow = SmtFactory.createFalse(); // Initial borrow is false (no borrow)
        
        for (int i = 0; i < n; i++) {
            // Get the bits from minuend and subtrahend at position i
            Constraint a = minuend.get(i);  // Bit from the minuend
            Constraint b = subtrahend.get(i); // Bit from the subtrahend
            //System.out.println ("a: " + a);
            //System.out.println ("b: " + b);
            // Perform the subtraction at this bit position:
            // result[i] = a XOR b XOR borrow
            Constraint diff = xor(xor(a,b),borrow);
            //System.out.println ("hallo");
            result.add(diff);
            //System.out.println ("hello");
            // Calculate the new borrow:
            // borrow = (NOT a AND b) OR (borrow AND (NOT a XOR b))
            Constraint newBorrow = SmtFactory.createDisjunction(SmtFactory.createConjunction(SmtFactory.createNegation(a).simplify(), b).simplify(), SmtFactory.createConjunction(borrow, xor(SmtFactory.createNegation(a),b)).simplify()).simplify();
            // Update the borrow for the next bit position
            //System.out.println ("wow");
            borrow = newBorrow;
        }
        //System.out.println ("end borrow: " + borrow);
        return borrow;
    }

    public static ArrayList<Constraint> add (ArrayList<Constraint> c, ArrayList<Constraint> d){
        //change
        // if (!(c instanceof Conjunction) || !(d instanceof Conjunction)) throw new Error (c + " or " + d + " not in proper type");
        // if (c instanceof Conjunction c1) if (c1.numChildren() != bidWidth) throw new Error (c + " does not have enough children.");
        // if (d instanceof Conjunction d1) if (d1.numChildren() != bidWidth) throw new Error (d + " does not have enough children.");
        // Conjunction c1 = (Conjunction) c;
        // Conjunction d1 = (Conjunction) d;
        

        Constraint carry = SmtFactory.createFalse();
        ArrayList <Constraint> constraints = new ArrayList<>();
        if (c.size() > d.size()){
            d = addFalses(d, c.size());
        }
        else if (d.size() > c.size()){
            c = addFalses(c, d.size());
        }
        System.out.println ("going to add: " + c + " and "+d);
        for (int i =0; i < c.size() ; i++){
            Constraint c_i = c.get(i);
            Constraint d_i = d.get(i);
            Constraint c_xor_d= xor(c_i, d_i);
            Constraint sum = xor(c_xor_d, carry);
            //Constraint sum = SmtFactory.createConjunction(SmtFactory.createDisjunction(c_xor_d, carry).simplify(), SmtFactory.createNegation(SmtFactory.createConjunction(c_xor_d, carry).simplify()).simplify()).simplify();

            
            constraints.add(sum);
            carry = SmtFactory.createDisjunction(SmtFactory.createConjunction(c_i,d_i).simplify(), SmtFactory.createConjunction(carry, c_xor_d).simplify()).simplify();
            //if (i == bidWidth-1) constraints.add(SmtFactory.createConjunction(sum, SmtFactory.createNegation(carry)));
        }
        constraints.add(carry);
        //constraints.set(constraints.size()-1, SmtFactory.createConjunction(constraints.get(constraints.size()-1), carry).simplify());
        //two negative numbers -> negative outcome 
        //two positive numbers -> positive outcome

        return constraints;
        //return SmtFactory.createConjunction(constraints);

        
    }


        public static Constraint addReturnCarry (ArrayList<Constraint> c, ArrayList<Constraint> d){
        //change
        // if (!(c instanceof Conjunction) || !(d instanceof Conjunction)) throw new Error (c + " or " + d + " not in proper type");
        // if (c instanceof Conjunction c1) if (c1.numChildren() != bidWidth) throw new Error (c + " does not have enough children.");
        // if (d instanceof Conjunction d1) if (d1.numChildren() != bidWidth) throw new Error (d + " does not have enough children.");
        // Conjunction c1 = (Conjunction) c;
        // Conjunction d1 = (Conjunction) d;
        

        Constraint carry = SmtFactory.createFalse();
        ArrayList <Constraint> constraints = new ArrayList<>();
        for (int i =0; i < bidWidth ; i++){
            Constraint c_i = c.get(i);
            Constraint d_i = d.get(i);
            Constraint c_xor_d= SmtFactory.createConjunction(SmtFactory.createDisjunction(c_i, d_i).simplify(), SmtFactory.createNegation(SmtFactory.createConjunction(c_i, d_i).simplify()).simplify()).simplify();
            Constraint sum = SmtFactory.createConjunction(SmtFactory.createDisjunction(c_xor_d, carry).simplify(), SmtFactory.createNegation(SmtFactory.createConjunction(c_xor_d, carry).simplify()).simplify()).simplify();

            
            constraints.add(sum);
            carry = SmtFactory.createDisjunction(SmtFactory.createConjunction(c_i,d_i).simplify(), SmtFactory.createConjunction(carry, c_xor_d).simplify()).simplify();
            //if (i == bidWidth-1) constraints.add(SmtFactory.createConjunction(sum, SmtFactory.createNegation(carry)));
        }
        //two negative numbers -> negative outcome 
        //two positive numbers -> positive outcome

        return carry;
        //return SmtFactory.createConjunction(constraints);

        
    }

    public static ArrayList<Constraint> negate (ArrayList<Constraint> formula){
        for (int i =0; i < formula.size(); i++){
            formula.set(i, formula.get(i).negate());
        }
        return add(formula, convert((IValue)SmtFactory.createValue(1)));
    }


    public static Constraint greaterOrEqual (ArrayList<Constraint> leftSide, ArrayList<Constraint> rightSide){
        // if (formula.get(formula.size()-1) instanceof Conjunction c){
        //     return SmtFactory.createConjunction(c.queryChild(1).negate(), c.queryChild(2));    
        // }
        // rightSide = negate(rightSide);
        // System.out.println ("rightside negated: " + rightSide);
        // return addReturnCarry(leftSide, rightSide);
        // Constraint end = SmtFactory.createImplication(leftSide.get(leftSide.size()-1))
        // for (int i = bidWidth-1; i >= 0; i--){  
        //     end = SmtFactory.createDisjunction(SmtFactory.createConjunction(leftSide.get(i), SmtFactory.createNegation(rightSide.get(i))), SmtFactory.createConjunction(SmtFactory.createIff(leftSide.get(i), rightSide.get(i)), ));
        // }
        return SmtFactory.createNegation(subtract(leftSide, rightSide));
        

    }


    // public static negate (IValue value){

    // }

    public static ArrayList<Valuation> generateAllValuations(int numVariables) {
        ArrayList<Valuation> valuations = new ArrayList<>();
        
        // Total number of valuations is 2^numVariables
        int totalValuations = 1 << numVariables; // Same as 2^numVariables
        
        // Iterate through all possible valuations
        for (int i = 0; i < totalValuations; i++) {
            Valuation val = new Valuation();
            for (int j = 0; j < numVariables; j++) {
                // Check if the j-th bit in i is set (1)
                boolean value = (i & (1 << j)) != 0;
                val.setBool(j+1, value);
            }
            valuations.add(val);
        }
        
        return valuations;
    }

    public static ArrayList<Valuation> test(SmtProblem problem, Constraint formula){
        


        ArrayList<Valuation> valuations = generateAllValuations(problem.numberBooleanVariables());
        //System.out.println (valuations);
        ArrayList<Valuation> trueValuations = new ArrayList<>();
        for (Valuation val : valuations){
            if (formula.evaluate(val)){
                trueValuations.add(val);
            }
        }
        if (trueValuations.size() <= 5 ) System.out.println (trueValuations);
        else {
            for (int i =0; i < 5; i++) System.out.println (trueValuations.get(i));
        }
        //if (trueValuations.size() > 0 ) System.out.println ("holds for: " + trueValuations.get(0));
        return trueValuations;
        //ArrayList<Valuation> valuations = new ArrayList<>();
        // Valuation val1 = new Valuation();
        // val1.setBool(1, true);
        // Valuation val2 = new Valuation();
        // val2.setBool(1, false);
        // valuations.add(val1);
        // valuations.add(val2);
        // System.out.println ("number of bool vars: " + problem.numberBooleanVariables());
        // ArrayList<Valuation> willAdd = new ArrayList<>();
        // for (int i =2; i <= problem.numberBooleanVariables(); i++){
        //     for (Valuation val: valuations){
        //         val.setBool(i, false);
        //         Valuation val3 = new Valuation();
        //         for (int j=1; j <= problem.numberBooleanVariables(); j++){
        //             if (val.queryBoolAssignment(j)) val3.setBool(j, true);
        //         }
        //         val3.setBool(i, true);
        //         willAdd.add(val3);
        //     }
        //     valuations.addAll(willAdd);
        // }
        // System.out.println (valuations);
        // int value = 0;
        // ArrayList<Constraint> c = convert((IValue)SmtFactory.createValue(value));
        // System.out.println (value +" converted is " + c);
        // Constraint answer = SmtFactory.createTrue();
        // ArrayList<Valuation> trueValuations= new ArrayList<>();
        // if (formula.size() != c.size()) throw new Error ("f has different bitwidth as c");
        // for (int j =0; j < valuations.size(); j++){
        //     boolean doesithold = true;
        //     for (int i =0; i < formula.size(); i++){
        //         //System.out.println ("testing valuation: " + valuations.get(j) + " on " + formula.get(i-1) + " resulting in " +formula.get(i-1).evaluate(valuations.get(j)) +" and cc value: " + cc.queryChild(i));
        //         if (c.get(i).evaluate() != formula.get(i).evaluate(valuations.get(j))){
        //             //System.out.println ("removing: " + valuations.get(j));
        //             doesithold = false;
                    
        //         }
        //     }
        //     if (doesithold) trueValuations.add(valuations.get(j));
            
        // }
        // System.out.println (trueValuations);
        // for (Valuation val : valuations){
        //     if (formula.evaluate(val)) System.out.println (" holds for " + val);
        //     else System.out.println (" does not hold for " + val);
        // }

    }
    // public static void add(IVar x, IValue y){
    //     String value = Integer.toBinaryString(y.queryValue());
    //     System.out.println (value);
    //     BVar carry = SmtFactory.createBooleanVariable();

    //     Conjunction endFormula = SmtFactory.createConjunction();
    //     for (int i =0; i < bidWidth; i++){
    //         BVar yi = SmtFactory.createBooleanVariable();
    //         if (value.charAt(i) == 1) {
    //             Constraint sum = SmtFactory.createConjunction(SmtFactory.createNegation(yi, SmtFactory.createNegation(carry)));
    //         }
    //         else{
    //             Constraint sum = SmtFactory.createConjunction(SmtFactory.createDisjunction(y1, carry), SmtFactory.createNegation(SmtFactory.createConjunction(y1, carry))); 
    //         }
    //         carry = 
    //         endFormula = SmtFactory.createConjunction(endFormula, sum);

    //     }

    // }
  
}