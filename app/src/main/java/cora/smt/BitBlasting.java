package cora.smt;

import charlie.smt.*;
import cora.smt.*;
import java.util.ArrayList;
import java.util.List;

public class BitBlasting{
    static int bidWidth = 4;



    public static SmtSolver.Answer checkSatisfiability(SmtProblem problem, ArrayList<IntegerExpression> expressions){
        if (expressions.size()==0) return new SmtSolver.Answer.YES(new Valuation());
        ArrayList<Constraint> c = new ArrayList<>();
        //multiple expressions add later
        for (int i =0; i < expressions.size(); i++){
            if (expressions.get(i) instanceof Addition a){
                c = add(problem, a);
            }
        }
        System.out.println (c);
        for (int i =0; i < c.size(); i++){
            System.out.println ("s" + i + ": " + c.get(i));
        }
        test(problem,c);
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
       
        return new SmtSolver.Answer.MAYBE("not implemented yet.");



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




    public static void main(String[] args) {
        int binaryNumber = 0b11111111111111111111111111110110; // Binary for decimal 10
        System.out.println("Binary 0b1010 as decimal: " + binaryNumber);

    }

    public static ArrayList<Constraint> add(SmtProblem problem, Addition a ){
        ArrayList<Constraint> con = new ArrayList<>();
        switch (a.queryChild(1)){
            case IVar v : con = convert(problem, v); break;
            case IValue val : con = convert(val); break;
            default: throw new Error(a.queryChild(1).getClass() + " not supported yet.");
        }
        System.out.println (a.queryChild(1) + " converted is " + con);
        for (int j =2; j <= a.numChildren(); j++){
            
            switch (a.queryChild(j)){
                //case IValue val: con = add(problem, con, convert(val)); break;
                case IVar var: con = add(problem, con, convert(problem, var)); break;
                case IValue v : con = add(problem, con, convert(v)); break;
                default: throw new Error(a.queryChild(j).getClass() + " not supported yet.");
            }
        }
        return con;

    }


    public static ArrayList<Constraint> convert (SmtProblem problem, IVar v){
        ArrayList<Constraint> constraints = new ArrayList<>();
        for (int i =0; i < bidWidth; i++){
            constraints.add(problem.createBooleanVariable());
        }
        System.out.println ("converted " + v + " to " + constraints);
        //return SmtFactory.createConjunction(constraints);
        return constraints;
    }

    public static ArrayList<Constraint> convert (IValue v){
        String value = Integer.toBinaryString(v.queryValue());
        System.out.println (value + " with length " + value.length());
        if (value.length() > bidWidth){
            if (canBeShortened(value)){
                System.out.println (value + " can be shortened to " + value.substring(0, bidWidth));
                value = value.substring(0, bidWidth);
            }
            else throw new Error ("Value " + v.queryValue() + " too big for bidwidth.");
        } 
        ArrayList<Constraint> constraints = new ArrayList<>();
        for (int i =0; i < bidWidth; i++){
            if (i >= value.length()){
                constraints.add(SmtFactory.createFalse());
            }
            else if (value.charAt(i)=='1'){
                constraints.add(SmtFactory.createTrue());
            } 
            else constraints.add(SmtFactory.createFalse());
        }
        //return SmtFactory.createConjunction(constraints);
        return constraints;
    }

    public static boolean canBeShortened (String binaryNumber){
        boolean allZeros = true;
        for (int i = bidWidth; i < binaryNumber.length(); i++){
            if (binaryNumber.charAt(i) != '0') allZeros = false;
        }
        if (allZeros) return true;
        boolean allOnes = true;
        for (int i = bidWidth; i < binaryNumber.length(); i++){
            if (binaryNumber.charAt(i) != '1') allOnes = false;
        }
        return allOnes;
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

        
    // }

    public static ArrayList<Constraint> add (SmtProblem problem, ArrayList<Constraint> c, ArrayList<Constraint> d){
        //change
        // if (!(c instanceof Conjunction) || !(d instanceof Conjunction)) throw new Error (c + " or " + d + " not in proper type");
        // if (c instanceof Conjunction c1) if (c1.numChildren() != bidWidth) throw new Error (c + " does not have enough children.");
        // if (d instanceof Conjunction d1) if (d1.numChildren() != bidWidth) throw new Error (d + " does not have enough children.");
        // Conjunction c1 = (Conjunction) c;
        // Conjunction d1 = (Conjunction) d;


        Constraint carry = SmtFactory.createFalse();
        ArrayList <Constraint> constraints = new ArrayList<>();
        for (int i =0; i < bidWidth; i++){
            Constraint c_i = c.get(i);
            Constraint d_i = d.get(i);
            Constraint c_xor_d= SmtFactory.createConjunction(SmtFactory.createDisjunction(c_i, d_i), SmtFactory.createNegation(SmtFactory.createConjunction(c_i, d_i)));
            Constraint sum = SmtFactory.createConjunction(SmtFactory.createDisjunction(c_xor_d, carry), SmtFactory.createNegation(SmtFactory.createConjunction(c_xor_d, carry)));

            
            constraints.add(sum);
            carry = SmtFactory.createDisjunction(SmtFactory.createConjunction(c_i,d_i), SmtFactory.createConjunction(carry, c_xor_d));
            
        }
        return constraints;
        //return SmtFactory.createConjunction(constraints);

        
    }

    public static void test(SmtProblem problem, ArrayList<Constraint> formula){
        



        ArrayList<Valuation> valuations = new ArrayList<>();
        Valuation val1 = new Valuation();
        val1.setBool(1, true);
        Valuation val2 = new Valuation();
        val2.setBool(1, false);
        valuations.add(val1);
        valuations.add(val2);
        System.out.println ("number of bool vars: " + problem.numberBooleanVariables());
        ArrayList<Valuation> willAdd = new ArrayList<>();
        for (int i =2; i <= problem.numberBooleanVariables(); i++){
            for (Valuation val: valuations){
                val.setBool(i, false);
                Valuation val3 = new Valuation();
                for (int j=1; j <= problem.numberBooleanVariables(); j++){
                    if (val.queryBoolAssignment(j)) val3.setBool(j, true);
                }
                val3.setBool(i, true);
                willAdd.add(val3);
            }
            valuations.addAll(willAdd);
        }
        //System.out.println (valuations);
        int value = 0;
        ArrayList<Constraint> c = convert((IValue)SmtFactory.createValue(value));
        System.out.println (value +" converted is " + c);
        Constraint answer = SmtFactory.createTrue();
        ArrayList<Valuation> trueValuations= new ArrayList<>();
        if (formula.size() != c.size()) throw new Error ("f has different bitwidth as c");
        for (int j =0; j < valuations.size(); j++){
            boolean doesithold = true;
            for (int i =0; i < formula.size(); i++){
                //System.out.println ("testing valuation: " + valuations.get(j) + " on " + formula.get(i-1) + " resulting in " +formula.get(i-1).evaluate(valuations.get(j)) +" and cc value: " + cc.queryChild(i));
                if (c.get(i).evaluate() != formula.get(i).evaluate(valuations.get(j))){
                    //System.out.println ("removing: " + valuations.get(j));
                    doesithold = false;
                    
                }
            }
            if (doesithold) trueValuations.add(valuations.get(j));
            
        }
        System.out.println (trueValuations);
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