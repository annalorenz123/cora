package cora.smt;

import charlie.smt.*;
import cora.smt.*;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.BufferedReader;
import java.io.FileReader;

public class BitBlastingFaster{
    double timeBitBlasting = 0;
    double timeTseitinTransformation = 0;
    double timeMiniSat = 0;

    static int bidWidth = 20;
    ArrayList<Constraint> allCarrys = new ArrayList<>();
    static ArrayList<ArrayList<Constraint>> allVariables = new ArrayList<>();
    static ArrayList<BVar> originalVars = new ArrayList<>();
    int startIndex = 0;

    public SmtSolver.Answer checkSatisfiability(SmtProblem problem, ArrayList<IntegerExpression> expressions, boolean negative){
        if (expressions.size()==0) return new SmtSolver.Answer.YES(new Valuation());
        long startTime = System.nanoTime();
        for (int i =0; i < problem.numberIntegerVariables(); i++){
            allVariables.add(new ArrayList<>());
        }
        
        ArrayList<IntegerExpression> c = new ArrayList<>();
        ArrayList<Constraint> args = new ArrayList<>();
        //System.out.println ("number of expressions: " + expressions.size());
        for (int i =0; i < expressions.size(); i++){
            //make switch
            switch(expressions.get(i)){
                case Addition a: c.addAll(makeSides(a)); break;
                case CMult cm: c.addAll(makeSides(cm)); break;
                case IVar v : c.add(v); c.add(SmtFactory.createValue(0)); break;
                default: throw new Error("expression of form: " + expressions.get(i) + " not supported.");
            }
        }
        int maxBidWidth =0;         
        for (int i =0; i < c.size(); i+=2){
            int currentBidWidth = determineBidWidth(c.get(i), c.get(i+1));
            if ( currentBidWidth > maxBidWidth){
                maxBidWidth = currentBidWidth;
            }
        }
        
        bidWidth = getConstantBidWidth(c);
        //bidWidth =1;
        System.out.println ("minimal bidwidth for constants is: " + bidWidth);
        while (bidWidth <= maxBidWidth){
            System.out.println ("setting bidwidth to: " + bidWidth);
            System.out.println ("c: " + c);
            for (int i =0; i < c.size(); i+=2){
                ArrayList<Constraint> leftSide = convert(problem, c.get(i));
                ArrayList<Constraint> rightSide = convert(problem, c.get(i+1));
                Constraint end = greaterOrEqual(leftSide, rightSide);
                args.add(end);
                for (Constraint cons : allCarrys){
                    args.add(SmtFactory.createNegation(cons).simplify());
                }
                allCarrys.clear();
            }
            Constraint endConjunction = SmtFactory.createConjunction(args).simplify();
            
            
            System.out.println (allVariables);
            if (endConjunction instanceof Truth) {
                System.out.println ("true");
                return new SmtSolver.Answer.YES(BitBlasting.makeZeroValuation(allVariables,problem, new Valuation()));
            }
            long endTime = System.nanoTime();
            timeBitBlasting = (endTime - startTime) / 1_000_000.0;
            //System.out.println (endConjunction);
            //System.out.println (endConjunction.toString().length());
            startTime = System.nanoTime();
            //endConjunction = AdjustedTTransformation.tseitinTransformation(endConjunction, problem);
            
            endConjunction = TseitinTransformation.tseitinTransformation(endConjunction, problem);
            endTime = System.nanoTime();
            timeTseitinTransformation =(endTime - startTime) / 1_000_000.0;
            //timeTseitinTransformation = (endTime - startTime) / 1_000_000.0;
            //endConjunction = ToCNF.toCNF(problem, endConjunction);
            //System.out.println ("end conjunction num vars: " + problem.numberBooleanVariables());
            //System.out.println (endConjunction);
            //return new SmtSolver.Answer.MAYBE("not implemented yet.");
            startTime = System.nanoTime();
            try{
                CnfToDimacs.convertToDimacs(endConjunction, problem.numberBooleanVariables(), "output.cnf");
            }
            catch (IOException e){
                System.out.println (e);
            }
            
            SatCaller.callMiniSat("output.cnf", "output.txt");
            
            SmtSolver.Answer answer = readOutput(problem, expressions, negative);
            endTime = System.nanoTime();
            timeMiniSat = (endTime - startTime) / 1_000_000.0;
            if (answer instanceof SmtSolver.Answer.YES) return answer;
            bidWidth++;
        }
        return new SmtSolver.Answer.NO();
 
            //System.out.println ("left side converted: " + leftSide);
            // for (int a =0; a < leftSide.size(); a++){
            //     System.out.println ("s" + a + ": " + leftSide.get(a));
            // }
            //System.out.println ("right side: " +rightSide);
            // for (int a =0; a < rightSide.size(); a++){
            //     System.out.println ("s" + a + ": " + rightSide.get(a));
            // }
            // if (leftSide.size() > bidWidth){
            //     leftSide = new ArrayList<>(leftSide.subList(0, bidWidth));
            // }
            // if (rightSide.size() > bidWidth){
            //     rightSide = new ArrayList<>(rightSide.subList(0, bidWidth));
            // }
            
            //System.out.println ("end arg: " + end);
            //System.out.println ("end: " + end);
            
            // if (expressions.get(i) instanceof IVar v){
            //     System.out.println ("found variable");
            //     c = convert(problem, v);
            // }
            
            // else if (expressions.get(i) instanceof CMult mult){
            //     c = multiply(convert((IValue)SmtFactory.createValue(mult.queryConstant())), convert(problem, (IVar)mult.queryChild()));
            // }

        
 

        // ArrayList<Valuation> valuations = test(problem, endConjunction);
        // if (valuations.size()==0) return new SmtSolver.Answer.NO();
        // else {
        //     for (int f =0; f < valuations.size(); f++){
        //         Valuation v =  makeValuation (problem, valuations.get(f));
        //         SimplexMethod sm = new SimplexMethod();
        //         if (!sm.extraCheck(v, expressions)){
        //             throw new Error ("bitblasting gave answer that does not hold: " + v);
        //         }
        //     }
        //     return new SmtSolver.Answer.YES(makeValuation (problem, valuations.get(0)));

        // }
        // System.out.println (endConjunction.toString().length());

        
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
       
        



    }

    public ArrayList<Double> getTimes (){
        ArrayList<Double> list = new ArrayList<>();
        list.add(timeBitBlasting);
        list.add(timeTseitinTransformation);
        list.add(timeMiniSat);
        return list;
    }

    public SmtSolver.Answer readOutput (SmtProblem problem, ArrayList<IntegerExpression> expressions, boolean negative){
        //System.out.println ("numintvars: " + problem.numberIntegerVariables());
        String filePath = "output.txt"; // Adjust path if needed
        Valuation v = new Valuation();
        SimplexMethod sm = new SimplexMethod();
        try (BufferedReader reader = new BufferedReader(new FileReader(filePath))) {
            String firstLine = reader.readLine();
            if (firstLine.equals("SAT")) {
                String valuation = reader.readLine();
                //System.out.println (valuation);
                ArrayList<String> numbersList = new ArrayList<>(Arrays.asList(valuation.split(" ")));
                //System.out.println(problem.numberIntegerVariables());
                if (!negative){
                    for (int i =1; i <= problem.numberIntegerVariables(); i++){
                        //System.out.println ("at variable " + i);
                        ArrayList<Constraint> binary = new ArrayList<>();
                        for (int j =1; j <= bidWidth; j++){
                            //System.out.println ("looking at: " + ((i-1)*bidWidth+(j-1)));
                            if (numbersList.get((i-1)*bidWidth+(j-1)).startsWith("-")){
                                //System.out.println("setting " + ((i-1)*bidWidth+(j-1)) + " to false");
                                binary.add(SmtFactory.createFalse());
                            }
                            else {
                                binary.add(SmtFactory.createTrue());
                                //System.out.println("setting " + ((i-1)*bidWidth+(j-1)) + " to true");
                            }
                        }
                        
                        //System.out.println (allVariables);
                        
                        for (int a =0; a < allVariables.size(); a++){
                            while (allVariables.get(a).isEmpty()) {
                                v.setInt(a+1, 0); 
                                a++;
                            }
                            int index = ((BVar)(removeFalses(allVariables.get(a))).get(0)).queryIndex();
                            if (((i-1)*bidWidth+1) == index){
                                //System.out.println ("setting variable "+ (a+1) + " with starting index " + index);
                                v.setInt(a+1, convertBinToDec(binary));
                                break;
                            }
                        }
                        
                    }          
                    if (!sm.extraCheck(v, expressions)){
                        throw new Error ("bitblasting gave answer that does not hold: " + v);
                    }
                    return new SmtSolver.Answer.YES(v);
                }
                // else{
                //     for (int i =0; i <= problem.numberIntegerVariables()/3; i++){
                //         v.setInt(i,0);
                //     }
                //     int it = 0;
                //     System.out.println ("startindex: " + startIndex);
                //     for (int i =problem.numberIntegerVariables()/3+1; i <= problem.numberIntegerVariables(); i++){
                        
                //         ArrayList<Constraint> binary = new ArrayList<>();
                //         for (int j =1; j <= bidWidth; j++){
                //             System.out.println ("index is : " + (it*bidWidth+(j-1)+startIndex));
                //             if (numbersList.get((it*bidWidth+(j-1)+startIndex)).startsWith("-")){
                //                 //System.out.println("setting " + ((i-1)*bidWidth+(j-1)) + " to false");
                //                 System.out.println ("looking at: " + (it*bidWidth+(j-1)+startIndex));
                //                 binary.add(SmtFactory.createFalse());
                //             }
                //             else binary.add(SmtFactory.createTrue());
                //         }
                //         System.out.println (binary);
                //         System.out.println ("num int vars: " + problem.numberIntegerVariables());
                //         System.out.println ("all variables: " + allVariables);
                //         for (int a =problem.numberIntegerVariables()/3; a < allVariables.size(); a++){
                //             int index = ((BVar)(removeFalses(allVariables.get(a)).get(0))).queryIndex();
                //             if ((it*bidWidth+startIndex) == index){
                //                 System.out.println ("setting variable "+ (a+1) + " with starting index " + index);
                //                 v.setInt(a+1, convertBinToDec(binary));
                //                 break;
                //             }
                //         }
                //         it++;
                //     } 
                //     System.out.println(v);
                //     if (!sm.extraCheck(v, expressions)){
                //         throw new Error ("bitblasting returned valuation that does not hold.");
                //     }
                //     //else return sm.adjustedValuation(problem.numberIntegerVariables(), v);
                //     return new SmtSolver.Answer.YES(v);
                // }


            }
        } catch (IOException e) {
            System.err.println("An error occurred while reading the file: " + e.getMessage());
        }
        return new SmtSolver.Answer.NO();
        // if (negative) return new SmtSolver.Answer.NO();
        // startIndex = problem.numberBooleanVariables()+1;
        // ArrayList<IntegerExpression> negativeexpr =  sm.convertToNegative(problem, expressions);
        // System.out.println ("NEGATIVE EXPR: " + negativeexpr); 
        
        // return checkSatisfiability (problem,negativeexpr, true);
    }



    // Method to write DIMACS string to a file
    public static void writeDimacsToFile(String dimacsContent, String outputFilePath) throws IOException {
        try (FileWriter writer = new FileWriter(outputFilePath)) {
            writer.write(dimacsContent);
        }
    }

    // public Valuation makeValuation2 (SmtProblem problem, Valuation v){
    //     Valuation finalVal = new Valuation();
    //     for (int i = 1; i <= problem.numberIntegerVariables(); i++){
    //         for (int j =1; j <= bidWidth;)
    //         if (allVariables.get(i-1).size() > bidWidth){
    //             allVariables.set(i-1, removeFalses(allVariables.get(i-1)));
    //         }
    //         System.out.println ("int var with index: " + i + " and valuation: " + allVariables.get(i-1));
    //         int decimal = convertBinToDec (allVariables.get(i-1), v);
    //         finalVal.setInt(i, decimal);
    //     }
    //     return finalVal;
    // }



    public Valuation makeValuation (SmtProblem problem, Valuation v){
        Valuation finalVal = new Valuation();
        //System.out.println (allVariables);
        for (int i = 1; i <= problem.numberIntegerVariables(); i++){
            if (allVariables.get(i-1).size() > bidWidth){
                allVariables.set(i-1, removeFalses(allVariables.get(i-1)));
            }
            //System.out.println ("int var with index: " + i + " and valuation: " + allVariables.get(i-1));
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

    public int convertBinToDec (ArrayList<Constraint> binary){
        int power = 0;
        int finalInt = 0;
        for (int i =0; i < binary.size(); i++){
            if (! ((binary.get(i) instanceof Falsehood) ||  (binary.get(i) instanceof Truth)) ){
                throw new Error ("not truth and falsehood");
            }
            if (binary.get(i) instanceof Truth){
                finalInt += Math.pow(2,power);
            }
            power++;
        }
        return finalInt;

    }



    public ArrayList<Constraint> convert (SmtProblem problem, IntegerExpression expression){
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

    public IntegerExpression addTerms(IntegerExpression expr1, IntegerExpression expr2) {
        return SmtFactory.createAddition (expr1, expr2);
  }


    public ArrayList<IntegerExpression> makeSides (CMult cm){
        IntegerExpression leftSide = SmtFactory.createValue(0);
        IntegerExpression rightSide = SmtFactory.createValue(0);
        if (cm.queryConstant() < 0) rightSide= addTerms(rightSide, SmtFactory.createMultiplication(cm.queryConstant()*-1, cm.queryChild()));
        else leftSide = addTerms(cm,leftSide);
        ArrayList<IntegerExpression> result = new ArrayList<>();
        result.add(leftSide.simplify());
        result.add(rightSide.simplify());
        return result;
    }

    public ArrayList<IntegerExpression> makeSides (Addition a){
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

    public ArrayList<Constraint> add(SmtProblem problem, Addition a ){
        ArrayList<Constraint> con = new ArrayList<>();
        switch (a.queryChild(1)){
            case IVar v : con = convert(problem, v); break;
            case IValue val : con = convert(val); break;
            case CMult c : con = multiply(convert((IValue)SmtFactory.createValue(c.queryConstant())), convert(problem, (IVar)c.queryChild())); break;
            default: throw new Error(a.queryChild(1).getClass() + " not supported yet.");
        }
        //System.out.println (a.queryChild(1) + " converted is " + con);
        for (int j =2; j <= a.numChildren(); j++){
            
            switch (a.queryChild(j)){
                //case IValue val: con = add(problem, con, convert(val)); break;
                case IVar var: con = add(con, convert(problem, var)); break;
                case IValue v : con = add(con, convert(v)); break;
                case CMult c : con = add(con, multiply(convert((IValue)SmtFactory.createValue(c.queryConstant())), convert(problem, (IVar)c.queryChild()))); break;
                default: throw new Error(a.queryChild(j).getClass() + " not supported yet.");
            }
        }
        //System.out.println ("result of addition: " + con);
        //return con;
        if (con.size() > bidWidth) return new ArrayList<>(con.subList(0, bidWidth));
        else return con;

    }

    public ArrayList<Constraint> add (ArrayList<Constraint> c, ArrayList<Constraint> d){
        //change
        // if (!(c instanceof Conjunction) || !(d instanceof Conjunction)) throw new Error (c + " or " + d + " not in proper type");
        // if (c instanceof Conjunction c1) if (c1.numChildren() != bidWidth) throw new Error (c + " does not have enough children.");
        // if (d instanceof Conjunction d1) if (d1.numChildren() != bidWidth) throw new Error (d + " does not have enough children.");
        // Conjunction c1 = (Conjunction) c;
        // Conjunction d1 = (Conjunction) d;
        
        if (isZero(c)) return d;
        if (isZero(d)) return c;
        Constraint carry = SmtFactory.createFalse();
        ArrayList <Constraint> constraints = new ArrayList<>();
        if (c.size() > d.size()){
            d = addFalses(d, c.size());
        }
        else if (d.size() > c.size()){
            c = addFalses(c, d.size());
        }
        //System.out.println ("going to add: " + c + " and "+d);
        
        for (int i =0; i < c.size() ; i++){
            Constraint c_i = c.get(i);
            Constraint d_i = d.get(i);
            Constraint c_xor_d= xor(c_i, d_i);
            Constraint sum = xor(c_xor_d, carry);
            //Constraint sum = SmtFactory.createConjunction(SmtFactory.createDisjunction(c_xor_d, carry).simplify(), SmtFactory.createNegation(SmtFactory.createConjunction(c_xor_d, carry).simplify()).simplify()).simplify();

            
            constraints.add(sum);
            carry = SmtFactory.createDisjunction(SmtFactory.createConjunction(c_i,d_i).simplify(), SmtFactory.createConjunction(carry, c_xor_d).simplify()).simplify();
            //carry = SmtFactory.createDisjunction(SmtFactory.createConjunction(c_i,d_i).simplify(), SmtFactory.createConjunction(carry, c_xor_d).simplify()).simplify();

            //if (i == bidWidth-1) constraints.add(SmtFactory.createConjunction(sum, SmtFactory.createNegation(carry)));
            if (i >= bidWidth) {
                //System.out.println (i+" geq than " + bidWidth);
                allCarrys.add(carry);  
                allCarrys.add(sum);  
                //System.out.println ("added: not" + allCarrys.get(allCarrys.size()-2) + " and not" + allCarrys.get(allCarrys.size()-1));
            }    
        }
        //constraints.add(carry);
        //System.out.println ("added : not " + carry);
        allCarrys.add(carry);
        //constraints.set(constraints.size()-1, SmtFactory.createConjunction(constraints.get(constraints.size()-1), carry).simplify());
        //two negative numbers -> negative outcome 
        //two positive numbers -> positive outcome

        //return constraints;
        //System.out.println ("result of adding " + c + " and " + d + " is " + new ArrayList<>(constraints.subList(0, bidWidth)));
        if (constraints.size() > bidWidth) return new ArrayList<>(constraints.subList(0, bidWidth));
        else return constraints;
        //return constraints;

        
    }

    public ArrayList<Constraint> leftShift(ArrayList<Constraint> formula, int i){
        ArrayList<Constraint> constraints = new ArrayList<>();
        //System.out.println ("formula before shifing: " + formula);
        for (int j = 0; j < i; j++){
            formula.add(0, SmtFactory.createFalse());
            //formula.remove(formula.size()-1);
        }
        //System.out.println ("formula after shifing: " + formula);
        return formula;
    }

    public ArrayList<Constraint> multiply(ArrayList<Constraint> lhs, ArrayList<Constraint> rhs) {
        //System.out.println ("going to multiply " + lhs + " and " + rhs + " bitwidth before: " + rhs.size());
        

        ArrayList<Constraint> result = new ArrayList<>();

        // Initialize result with zeros
        for (int i = 0; i < bidWidth; i++) {
            result.add(SmtFactory.createFalse()); // Placeholder for zero constraint
        }

        for (int i = 0; i < bidWidth; i++) {
            Constraint left = lhs.get(i);
            if (left.evaluate()){
                //System.out.println ("going to shift " + i);
                ArrayList<Constraint> shifted = new ArrayList<>();
                ArrayList<Constraint> rhscopy = new ArrayList<>(rhs); 
                shifted = leftShift(rhscopy, i);
                //System.out.println ("going to add " + shifted + " AND " + result);
                result = new ArrayList<>(add(shifted, result));
                //System.out.println ("result is: " + result);
            }
        }
        //System.out.println ("final result is: " + result + " with size: " + result.size());
        return result; // This represents the product
        //return new ArrayList<>(result.subList(0, bidWidth));

    }

    public ArrayList<Constraint> removeFalses (ArrayList<Constraint> formula){
        //System.out.println ("before:" + formula);
        ArrayList<Constraint> newFormula = new ArrayList<>();
        for (int i =0; i < formula.size(); i++){
            if (!(formula.get(i) instanceof Falsehood)) newFormula.add(formula.get(i));
        }
        return newFormula;
    }

    public ArrayList<Constraint> convert (SmtProblem problem, IVar v){
        ArrayList<Constraint> constraints = new ArrayList<>();
        if (!allVariables.get(v.queryIndex()-1).isEmpty()){
            if (allVariables.get(v.queryIndex()-1).size() > bidWidth){
                allVariables.set(v.queryIndex()-1, new ArrayList<>(removeFalses(allVariables.get(v.queryIndex()-1))));
            }
            //System.out.println ("i already know " + v.queryName()+ " returning: "+ allVariables.get(v.queryIndex()-1));
            return allVariables.get(v.queryIndex()-1);
        } 
        for (int i =0; i < bidWidth; i++){
            constraints.add(problem.createBooleanVariable());
        }
        //System.out.println ("converted " + v + " to " + constraints);
        //return SmtFactory.createConjunction(constraints);
        //final ArrayList<Constraint> end =new ArrayList<>(constraints);
        allVariables.set(v.queryIndex()-1, new ArrayList<>(constraints));
        return constraints;
    }

    public ArrayList<Constraint> convert (IValue v){
        String value = Integer.toBinaryString(v.queryValue());
        //System.out.println (value + " with length " + value.length());
        if (value.length() > bidWidth){
            throw new Error ("Value " + v.queryValue() + " too big for bidwidth.");
        } 
        if (value.length() < bidWidth) {
            value = addZeros(value);
            //System.out.println ("added zeros: " + value);
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

    public String addZeros (String value){
        for (int i = value.length(); i < bidWidth; i++){
            value = "0" + value;
        }
        return value;
    }

    public Constraint xor (Constraint a, Constraint b){
        //System.out.println ("result of xor: " + SmtFactory.createConjunction(SmtFactory.createDisjunction(a,b).simplify(), SmtFactory.createNegation(SmtFactory.createConjunction(a,b).simplify()).simplify()).simplify());
        return SmtFactory.createConjunction(SmtFactory.createDisjunction(a,b).simplify(), SmtFactory.createNegation(SmtFactory.createConjunction(a,b).simplify()).simplify()).simplify();
        //return SmtFactory.createConjunction(SmtFactory.createDisjunction(a,b), SmtFactory.createNegation(SmtFactory.createConjunction(a,b)));

    }



    public ArrayList<Constraint> addFalses (ArrayList<Constraint> adding, int size){
        //System.out.println ("going to make " + adding + " the size " + size);
        for (int i = adding.size(); i < size; i++){
            adding.add(SmtFactory.createFalse());
        }
        //if (adding.size() != size) throw new Error ("addfalses does not work");
        return adding;

    }

    public Constraint subtract(ArrayList<Constraint> minuend, ArrayList<Constraint> subtrahend) {
        //calculate minuend-subtrahend
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
            Constraint newBorrow = SmtFactory.createDisjunction(SmtFactory.createConjunction(SmtFactory.createNegation(a).simplify(), b).simplify(), SmtFactory.createConjunction(borrow, xor(SmtFactory.createNegation(a).simplify(),b)).simplify()).simplify();
            // Update the borrow for the next bit position
            //System.out.println ("wow");
            borrow = newBorrow;
        }
        //System.out.println ("end borrow: " + borrow);
        return borrow;
    }

    public boolean isZero (ArrayList<Constraint> check){
        for (Constraint c : check){
            if (!(c instanceof Falsehood)) return false;
        }
        return true;
    }

    public ArrayList<Constraint> negate (ArrayList<Constraint> formula){
        for (int i =0; i < formula.size(); i++){
            formula.set(i, formula.get(i).negate());
        }
        return add(formula, convert((IValue)SmtFactory.createValue(1)));
    }


    public Constraint greaterOrEqual (ArrayList<Constraint> leftSide, ArrayList<Constraint> rightSide){
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
        return SmtFactory.createNegation(subtract(leftSide, rightSide)).simplify();
        

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
        System.out.println (trueValuations);
        // if (trueValuations.size() <= 5 ) System.out.println (trueValuations);
        // else {
        //     for (int i =0; i < 5; i++) System.out.println (trueValuations.get(i));
        // }
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

    public static int determineBidWidth (IntegerExpression leftSide, IntegerExpression rightSide){
        if (maxValue(leftSide) >= maxValue(rightSide)){
            return findExponent(maxValue(leftSide));
        }
        return findExponent(maxValue(rightSide));
        
    }

    public static int maxValue (IntegerExpression expr){
        switch (expr){
            case IValue b: return b.queryValue();
            case IVar b : return ((int)Math.pow(2,bidWidth))-1;
            case CMult cm : return cm.queryConstant()*maxValue(cm.queryChild());
            case Addition a: 
                int total = maxValue(a.queryChild(1));
                for (int i =2; i <= a.numChildren(); i++){
                    total += maxValue(a.queryChild(i));
                }
                return total;
            default: throw new Error (expr + " not supported in maxvalue");
        }
    }

    public static int findExponent(int number) {
        if (number <= 0) {
            throw new IllegalArgumentException("Number must be greater than 0");
        }
        int exponent = 0;
        while ((1 << exponent) < number) {
            exponent++;
        }
        System.out.println ("exponent for "+number+ " is " + (exponent));
        return exponent+1; // Add 1 to align with your example
    }

    public static int getConstantBidWidth(ArrayList<IntegerExpression> c){
        int maxvalue =1;
        for (int i =0; i < c.size(); i++){
            if (c.get(i) instanceof IValue v && v.queryValue() > maxvalue){
                maxvalue = v.queryValue();
            }
            else if (c.get(i) instanceof CMult cm && cm.queryConstant() > maxvalue){
                maxvalue = cm.queryConstant();
            }
            else if (c.get(i) instanceof Addition a){
                for (int j =1; j <= a.numChildren(); j++){
                    if (a.queryChild(j) instanceof IValue v2 && v2.queryValue() > maxvalue){
                        maxvalue = v2.queryValue();
                    }
                    if (a.queryChild(j) instanceof CMult cm && cm.queryConstant() > maxvalue){
                        maxvalue = cm.queryConstant();
                    }
                }
            }
        }
        System.out.println ("bidwidth for "+ c + " is " + maxvalue);
        return findExponent(maxvalue);
    }
  
}