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

public class BitBlastingNEW{
    ArrayList<Constraint> constraints = new ArrayList<>();
    double timeBitBlasting = 0;
    double timeTseitinTransformation = 0;
    double timeMiniSat = 0;
    static int bidWidth = 10;
    ArrayList<Constraint> allCarrys = new ArrayList<>();
    static ArrayList<ArrayList<BVar>> allVariables = new ArrayList<>();
    static ArrayList<BVar> originalVars = new ArrayList<>();
    int startIndex = 0;
    SmtProblem problem1;
    public static BVar falseVar;
    public static BVar trueVar;


    public SmtSolver.Answer checkSatisfiability(SmtProblem problem, ArrayList<IntegerExpression> expressions, boolean negative){
        System.out.println (expressions);
        if (expressions.size()==0) return new SmtSolver.Answer.YES(new Valuation());
        long startTime = System.nanoTime();
        falseVar = problem.createBooleanVariable();
        trueVar = problem.createBooleanVariable();
        for (int i =0; i < problem.numberIntegerVariables(); i++){
            allVariables.add(new ArrayList<>());
        }
        problem1=problem;


        // constraints.add(SmtFactory.createIff(falseVar, SmtFactory.createFalse()));
        // constraints.add(SmtFactory.createIff(trueVar, SmtFactory.createTrue()));
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
            int currentBidWidth = BitBlastingFaster.determineBidWidth(c.get(i), c.get(i+1));
            if ( currentBidWidth > maxBidWidth){
                maxBidWidth = currentBidWidth;
            }
        }
        System.out.println ("BITWIDTH GOING TO BE: " + maxBidWidth);
        for (int i =0; i < c.size(); i+=2){
            System.out.println ("sides: " + c.get(i) + " and " + c.get(i+1));
            ArrayList<BVar> leftSide = convert(problem, c.get(i));
            ArrayList<BVar> rightSide = convert(problem, c.get(i+1));
            Constraint end = greaterOrEqual(leftSide, rightSide);
            args.add(end);
        }
        Constraint endConjunction = SmtFactory.createConjunction(args);
        
        //System.out.println ("end: " + endConjunction);
        endConjunction = addConstraints(endConjunction);
        if (endConjunction instanceof Conjunction){
            ((Conjunction)endConjunction).addChild(SmtFactory.createConjunction(SmtFactory.createNegation(falseVar),trueVar));
        }
        else {
            endConjunction = SmtFactory.createConjunction(endConjunction, SmtFactory.createConjunction(SmtFactory.createNegation(falseVar),trueVar));
        }
        //System.out.println ("end2: " + endConjunction);
        //System.out.println ("end constraints: "+ constraints);
        // if (endConjunction instanceof Truth) {
        //     System.out.println ("formula is true");
            
        //     SmtSolver.Answer answer = new SmtSolver.Answer.YES(makeZeroValuation(allVariables, problem, new Valuation()));
        //     long endTime = System.nanoTime();
        //     timeBitBlasting = (endTime - startTime) / 1_000_000.0;
        //     return answer;
        // }
        long endTime = System.nanoTime();
        timeBitBlasting = (endTime - startTime) / 1_000_000.0;
        //System.out.println (endConjunction.toString().length());
        startTime = System.nanoTime();
        int numberofobjectsbefore = ToCNF.countNumberOfObjects(endConjunction,0);
        //endConjunction = TseitinTransformation.tseitinTransformation(endConjunction, problem);
        endConjunction = AdjustedTTransformation.tseitinTransformation(endConjunction, problem);

        int numberofobjectsafter = ToCNF.countNumberOfObjects(endConjunction,0);
        
        //System.out.println ("number of objects before: " + numberofobjectsbefore + " and after: " + numberofobjectsafter);
        System.out.println ("BITWIDTH was: " + maxBidWidth);
        double ratiott = (double)numberofobjectsafter / numberofobjectsbefore;
        File file = new File("ratiott.csv");
        try (BufferedWriter writer = new BufferedWriter(new FileWriter(file, true))) {
        // Append the line and a newline character
            writer.write(Double.toString(ratiott)+ ", ");
            writer.newLine();
        }
        catch (IOException e) {
            System.err.println("An error occurred while writing to the file: " + e.getMessage());
        }
        //System.out.println ("ratio tt: " + Double.toString(ratiott));
        endTime = System.nanoTime();
        timeTseitinTransformation = (endTime - startTime) / 1_000_000.0;
        startTime = System.nanoTime();
        try{
            CnfToDimacs.convertToDimacs(endConjunction, problem.numberBooleanVariables(), "output.cnf");
        }
        catch (IOException e){
            System.out.println (e);
        }
        
        SatCaller.callKissat("output.cnf", "output.txt");
        //SatCaller.callMiniSat("output.cnf", "output.txt");
        SmtSolver.Answer answer=  readOutput(problem, expressions, negative);
        endTime = System.nanoTime();
        timeMiniSat = (endTime - startTime) / 1_000_000.0;
        return answer;
        // ArrayList<Valuation> valuations = test(problem, endConjunction);
        // if (valuations.size()==0) {
        //     endTime = System.nanoTime();
        //     timeMiniSat = (endTime - startTime) / 1_000_000.0;
        //     return new SmtSolver.Answer.NO();
        // }
        // else {
        //     for (int f =0; f < valuations.size(); f++){
        //         Valuation v =  makeValuation (problem, valuations.get(f));
        //         SimplexMethod sm = new SimplexMethod();
        //         if (!sm.extraCheck(v, expressions)){
        //             throw new Error ("bitblasting gave answer that does not hold: " + v);
        //         }
        //     }
        //     endTime = System.nanoTime();
        //     timeMiniSat = (endTime - startTime) / 1_000_000.0;
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

    public ArrayList<BVar> add(SmtProblem problem, Addition a ){
        ArrayList<BVar> con = new ArrayList<>();

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
        return con;
        //return new ArrayList<>(con.subList(0, bidWidth));
    }

    public boolean notConstant(ArrayList<BVar> var){
        for (BVar b : var){
            if (b.queryIndex() != 1 && b.queryIndex() != 2){
                return true;
            }
        }
        return false;
    }

    public ArrayList<BVar> add (ArrayList<BVar> c, ArrayList<BVar> d){
        if (isZero(c)) return d;
        if (isZero(d)) return c;

        Constraint carry = SmtFactory.createFalse();
        if (c.size() > d.size()){
            d = addFalses(d, c.size());
        }
        else if (d.size() > c.size()){
            c = addFalses(c, d.size());
        }
        //System.out.println ("going to add: " + c + " and "+d);
        ArrayList<BVar> result = new ArrayList<>();
        for (int i =0; i < c.size() ; i++){
            BVar c_i = c.get(i);
            BVar d_i = d.get(i);
            Constraint c_xor_d= xor(c_i, d_i);
            BVar sumvar = problem1.createBooleanVariable();
            result.add(sumvar);
            if (i==0){
                constraints.add(SmtFactory.createIff(sumvar, c_xor_d));
            }
            else constraints.add(SmtFactory.createIff(sumvar, xor(c_xor_d, carry)));           
            Constraint newcarry = SmtFactory.createFalse();
            if (i==0){
                newcarry = SmtFactory.createConjunction(c_i, d_i);
            }
            else{
                newcarry = SmtFactory.createDisjunction(SmtFactory.createConjunction(c_i,d_i), SmtFactory.createConjunction(carry, SmtFactory.createDisjunction(c_i, d_i)));
            }
            carry = problem1.createBooleanVariable();
            constraints.add(SmtFactory.createIff(carry, newcarry));
        }
        //BVar growVar = problem1.createBooleanVariable();
        result.add((BVar)carry);
        //constraints.add(SmtFactory.createIff(growVar, carry));
        //System.out.println ("constraints: " + constraints);
        return result;        
    }

    public Constraint subtract(ArrayList<BVar> minuend, ArrayList<BVar> subtrahend) {
        //calculate minuend-subtrahend
        System.out.println ("going to subtract "+ minuend + " and " + subtrahend);
        if (isZero(subtrahend)) return falseVar;
        if (isZero(minuend)) return SmtFactory.createDisjunction(convertList(subtrahend));
        
        // Ensure both binary numbers are of the same length
        if (minuend.size()!= subtrahend.size()) {
            
            if (minuend.size() < subtrahend.size()){
                minuend = addFalses(minuend, subtrahend.size());
            }
            else subtrahend = addFalses(subtrahend, minuend.size());
            System.out.println ("not of same size, converted: " + minuend + " and " + subtrahend);
            //throw new Error (minuend + " and " + subtrahend + " not of same size");
        }
        int n = minuend.size();
        //System.out.println ("size of " + minuend + " is " + n);
        //ArrayList<Constraint> result = new ArrayList<>();
        Constraint borrow = SmtFactory.createFalse(); // Initial borrow is false (no borrow)
        ArrayList<BVar> result = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            // Get the bits from minuend and subtrahend at position i
            BVar a = minuend.get(i);  // Bit from the minuend
            BVar b = subtrahend.get(i); // Bit from the subtrahend
            //System.out.println ("a: " + a);
            //System.out.println ("b: " + b);
            // Perform the subtraction at this bit position:
            // result[i] = a XOR b XOR borrow

            // BVar diffvar = problem1.createBooleanVariable();
            // if (i==0){
            //     Constraint diff = xor(a,b);
            //     //constraints.add(SmtFactory.createIff(diffvar, diff));
            //     System.out.println ("diff: " + SmtFactory.createIff(diffvar, diff));
            // }
            // else{
            //     Constraint diff = xor(xor(a,b),borrow);
            //     //constraints.add(SmtFactory.createIff(diffvar, diff));
            //     System.out.println ("diff: " + SmtFactory.createIff(diffvar, diff));
            // }

            // Calculate the new borrow:
            // borrow = (NOT a AND b) OR (borrow AND (NOT a XOR b))
            //BVar borrowvar = problem1.createBooleanVariable();
            Constraint newBorrow = SmtFactory.createFalse();
            if (i == 0){
                newBorrow = SmtFactory.createConjunction(SmtFactory.createNegation(a), b);
                //System.out.println ("borrow: " + SmtFactory.createIff(borrow, newBorrow));
            }
            else{
                newBorrow = SmtFactory.createDisjunction(SmtFactory.createConjunction(SmtFactory.createNegation(a), b), SmtFactory.createConjunction(borrow, xor(SmtFactory.createNegation(a),b)));
            }
            // Update the borrow for the next bit position
            borrow = problem1.createBooleanVariable();
            constraints.add(SmtFactory.createIff(borrow, newBorrow));
            //System.out.println ("borrow: " + SmtFactory.createIff(borrow, newBorrow));

            //result.add(diffvar);
            //borrow = borrowvar;
        }
        //System.out.println ("adding: " + SmtFactory.createIff(trueVar, SmtFactory.createNegation(borrow)));
        //constraints.add(SmtFactory.createIff(trueVar, SmtFactory.createNegation(borrow)));
        //System.out.println ("end borrow: " + borrow);
        //System.out.println ("result is : " + result);
        //return result;
        return borrow;
    }

    public ArrayList<BVar> leftShift(ArrayList<BVar> formula, int i){
        //ArrayList<Constraint> constraints = new ArrayList<>();
        //System.out.println ("formula before shifing: " + formula);
        for (int j = 0; j < i; j++){
            formula.add(0, falseVar);
            //formula.remove(formula.size()-1);
        }
        //System.out.println ("formula after shifing: " + formula);
        return formula;
    }

    public ArrayList<BVar> multiply(ArrayList<BVar> lhs, ArrayList<BVar> rhs) {
        //System.out.println ("going to multiply " + lhs + " and " + rhs);

        ArrayList<BVar> result = new ArrayList<>();

        // Initialize result with zeros
        // for (int i = 0; i < bidWidth; i++) {
        //     result.add(SmtFactory.createFalse()); // Placeholder for zero constraint
        // }

        for (int i = 0; i < bidWidth; i++) {
            BVar left = lhs.get(i);
            if (left.queryIndex()==2){
                //System.out.println ("going to shift " + i);
                ArrayList<BVar> shifted = new ArrayList<>();
                ArrayList<BVar> rhscopy = new ArrayList<>(rhs); 
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

    public static ArrayList<Constraint> removeFalses (ArrayList<Constraint> formula){
        //System.out.println ("before:" + formula);
        ArrayList<Constraint> newFormula = new ArrayList<>();
        for (int i =0; i < formula.size(); i++){
            if (!(((BVar)(formula.get(i))).queryName().contains("extra"))) newFormula.add(formula.get(i));
        }
        return newFormula;
    }

    public ArrayList<BVar> convert (SmtProblem problem, IVar v){
        
        if (!allVariables.get(v.queryIndex()-1).isEmpty()){
            // if (allVariables.get(v.queryIndex()-1).size() > bidWidth){
            //     allVariables.set(v.queryIndex()-1, new ArrayList<>(removeFalses(allVariables.get(v.queryIndex()-1))));
            // }
            //System.out.println ("i already know " + v.queryName()+ " returning: "+ allVariables.get(v.queryIndex()-1));
            if (allVariables.get(v.queryIndex()-1).size() != bidWidth) throw new Error (allVariables.get(v.queryIndex()-1) + " in allvariables");
            return allVariables.get(v.queryIndex()-1);
        } 
        ArrayList<BVar> newvar = new ArrayList<>();
        for (int i =0; i < bidWidth; i++){
            newvar.add(problem.createBooleanVariable());
        }
        //System.out.println ("VAR converted " + v + " to " + newvar);
        //return SmtFactory.createConjunction(constraints);
        //final ArrayList<Constraint> end =new ArrayList<>(constraints);
        allVariables.set(v.queryIndex()-1, new ArrayList<>(newvar));
        return newvar;
    }

    public ArrayList<BVar> convert (IValue v){
        String value = Integer.toBinaryString(v.queryValue());
        //System.out.println (value + " with length " + value.length());
        if (value.length() > bidWidth){
            throw new Error ("Value " + v.queryValue() + " too big for bidwidth.");
        } 
        if (value.length() < bidWidth) {
            value = addZeros(value);
            //System.out.println ("added zeros: " + value);
        }
        ArrayList<BVar> valuev = new ArrayList<>();
        for (int i =bidWidth-1; i >= 0; i--){
            if (value.charAt(i)=='1'){
                valuev.add(trueVar);
            } 
            else valuev.add(falseVar);
        }
        //return SmtFactory.createConjunction(constraints);
        //System.out.println ("converted " +v+ " to " + valuev);
        return valuev;
    }

    public String addZeros (String value){
        for (int i = value.length(); i < bidWidth; i++){
            value = "0" + value;
        }
        return value;
    }

    public Constraint xor (Constraint a, Constraint b){
        //System.out.println ("result of xor: " + SmtFactory.createConjunction(SmtFactory.createDisjunction(a,b).simplify(), SmtFactory.createNegation(SmtFactory.createConjunction(a,b).simplify()).simplify()).simplify());
        //return SmtFactory.createConjunction(SmtFactory.createDisjunction(a,b).simplify(), SmtFactory.createNegation(SmtFactory.createConjunction(a,b).simplify()).simplify()).simplify();
        return SmtFactory.createConjunction(SmtFactory.createDisjunction(a,b), SmtFactory.createNegation(SmtFactory.createConjunction(a,b)));

    }



    public ArrayList<BVar> addFalses (ArrayList<BVar> adding, int size){
        //System.out.println ("going to make " + adding + " the size " + size);
        ArrayList<BVar> newvar = new ArrayList<>(adding);
        for (int i = adding.size(); i < size; i++){
            newvar.add(falseVar);
        }
        //if (adding.size() != size) throw new Error ("addfalses does not work");
        return newvar;

    }

    public boolean isZero (ArrayList<BVar> check){
        for (BVar c : check){
            if (!(c.queryIndex() ==1)) return false;
        }
        return true;
    }

    // public ArrayList<BVar> negate (ArrayList<BVar> formula){
    //     for (int i =0; i < formula.size(); i++){
    //         formula.set(i, formula.get(i).negate());
    //     }
    //     return add(formula, convert((IValue)SmtFactory.createValue(1)));
    // }


    public Constraint greaterOrEqual (ArrayList<BVar> leftSide, ArrayList<BVar> rightSide){
        //System.out.println ("result is: " + SmtFactory.createDisjunction(convertList(subtract(leftSide, rightSide))));
        //return SmtFactory.createDisjunction(convertList(subtract(leftSide, rightSide)));
        return SmtFactory.createNegation(subtract(leftSide, rightSide));
        // ArrayList<Constraint> children = new ArrayList<>();

        // if (leftSide.size() < rightSide.size()){
        //     leftSide = addFalses(leftSide, rightSide.size());
        // }
        // else if (rightSide.size() < leftSide.size()){
        //     rightSide = addFalses(rightSide, leftSide.size());
        // }
        // System.out.println ("leftside: " + leftSide);
        // System.out.println ("rightside: " + rightSide);
        // for (int i =leftSide.size()-1; i >=0; i--){
        //     ArrayList<Constraint> conjunction = new ArrayList<>();
        //     conjunction.add(SmtFactory.createDisjunction(leftSide.get(i), SmtFactory.createNegation(rightSide.get(i))));
        //     for (int j = i+1 ;j < leftSide.size(); j++){
        //         //conjunction.add(SmtFactory.createNegation(xor(leftSide.get(j), rightSide.get(j))));
        //         conjunction.add(SmtFactory.createDisjunction(SmtFactory.createConjunction(leftSide.get(j), rightSide.get(j)),SmtFactory.createConjunction(SmtFactory.createNegation(leftSide.get(j)), SmtFactory.createNegation(rightSide.get(j))) ));
        //     }
        //     children.add(SmtFactory.createConjunction(conjunction));
        // }

        // return SmtFactory.createDisjunction(children);
    }

    public Constraint addConstraints (Constraint endConjunction){
        if (constraints.isEmpty()) return endConjunction;
        if (endConjunction instanceof Conjunction conjunction){
            for (int i =0; i < constraints.size(); i++){
                
                Constraint c = constraints.get(i);
                //System.out.println ("adding" + c);
                conjunction.addChild(SmtFactory.createImplication(((Iff)c).queryLeft(), ((Iff)c).queryRight()));
                conjunction.addChild(SmtFactory.createImplication(((Iff)c).queryRight(), ((Iff)c).queryLeft()));
            }

            return conjunction;
        }
        else{
            Iff first = (Iff) constraints.get(0);
            Constraint conjunction = SmtFactory.createConjunction(endConjunction, SmtFactory.createImplication(first.queryLeft(), first.queryRight()));
            ((Conjunction)conjunction).addChild(SmtFactory.createImplication(first.queryRight(), first.queryLeft()));
            for (int i =1; i < constraints.size(); i++){
                //System.out.println ("adding" + constraints.get(i) + " to " + endConjunction);
                ((Conjunction)conjunction).addChild(SmtFactory.createImplication(((Iff)constraints.get(i)).queryLeft(), ((Iff)constraints.get(i)).queryRight()));
                ((Conjunction)conjunction).addChild(SmtFactory.createImplication(((Iff)constraints.get(i)).queryRight(), ((Iff)constraints.get(i)).queryLeft()));
            }
            return conjunction;
        }

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
            if (firstLine.equals("SAT") || firstLine.equals("SATISFIABLE")) {
                StringBuilder content = new StringBuilder();
                String line;
                while ((line = reader.readLine()) != null) {
                    content.append(line).append(" ");
                }

                // Split by any whitespace (space, newline, tab, etc.)
                ArrayList<String> numbersList = new ArrayList<>(Arrays.asList(content.toString().trim().split("\\s+")));
                
                //System.out.println ("SIZE NUMBERLIST: " + numbersList.size());
                //System.out.println ("all:" + allVariables);
                
                for (int a =0; a < allVariables.size(); a++){
                    //System.out.println ("variable: " + allVariables.get(a));
                    ArrayList<Constraint> binary = new ArrayList<>();
                    for (int i =0; i < bidWidth; i++){
                        int index = ((BVar)allVariables.get(a).get(i)).queryIndex();
                        //System.out.println ("at index: " + index);
                        if (index <= numbersList.size()){
                            if (numbersList.get(index-1).startsWith("-")){
                                binary.add(SmtFactory.createFalse());
                            }
                            else{
                                binary.add(SmtFactory.createTrue());
                            }
                        }
                        else binary.add(SmtFactory.createFalse());


                    }
                    v.setInt(a+1, convertBinToDec(binary));       
                }
                if (!sm.extraCheck(v, expressions)){
                    throw new Error ("bitblasting gave answer that does not hold: " + v);
                }
                return new SmtSolver.Answer.YES(v);
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
        //System.out.println ("allvariables:" + allVariables);
        for (int i = 1; i <= problem.numberIntegerVariables(); i++){
            if (allVariables.get(i-1).size() > bidWidth){
                throw new Error (allVariables.get(i-1) + "in all variables");
                //allVariables.set(i-1, removeFalses(allVariables.get(i-1)));
            }
            //System.out.println ("int var with index: " + i + " and valuation: " + allVariables.get(i-1));
            int decimal = convertBinToDec (allVariables.get(i-1), v);
            finalVal.setInt(i, decimal);
        }
        return finalVal;
    }


    public static Valuation makeZeroValuation (ArrayList<ArrayList<BVar>> allVariables , SmtProblem problem, Valuation v){
        Valuation finalVal = new Valuation();
        //System.out.println (allVariables);
        //System.out.println ("num variables: " + problem.numberIntegerVariables());
        for (int i = 1; i <= problem.numberIntegerVariables(); i++){
            if (allVariables.get(i-1).size() > bidWidth){
                //allVariables.set(i-1, removeFalses(allVariables.get(i-1)));
                throw new Error (allVariables.get(i-1) + "in all variables");
            }
            //System.out.println ("int var with index: " + i + " and valuation: " + allVariables.get(i-1));
            //int decimal = convertBinToDec (allVariables.get(i-1), v);
            finalVal.setInt(i, 0);
        }
        return finalVal;
    }

    public static int convertBinToDec (ArrayList<BVar> binary, Valuation v){
        int power = 0;
        int finalInt = 0;
        for (int i =0; i < binary.size(); i++){
            if (!(((BVar)(binary.get(i))).queryIndex() ==1) && v.queryBoolAssignment(((BVar)binary.get(i)).queryIndex())){
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
    
    public ArrayList<Constraint> convertList (ArrayList<BVar> list){
        ArrayList<Constraint> result = new ArrayList<>();
        for (Constraint c : list){
            result.add(c);
        }
        return result;
    }


    public ArrayList<BVar> convert (SmtProblem problem, IntegerExpression expression){
        ArrayList<BVar> constraint = new ArrayList<>();
        switch (expression){
            case IVar v: constraint = convert(problem, v); break;
            case IValue v : constraint = convert(v); break;
            case Addition a : constraint = add(problem, a); break;
            case CMult cm : constraint = multiply(convert((IValue) SmtFactory.createValue(cm.queryConstant())), convert(problem, (IVar) cm.queryChild())); break;
            default : throw new Error (expression + " not supported yet.");
        }
        System.out.println (expression + " is converted " + constraint);
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


    // public static negate (IValue value){

    // }

    public ArrayList<Valuation> generateAllValuations(int numVariables) {
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

    public ArrayList<Valuation> test(SmtProblem problem, Constraint formula){
        


        ArrayList<Valuation> valuations = generateAllValuations(problem.numberBooleanVariables());
        //System.out.println (valuations);
        ArrayList<Valuation> trueValuations = new ArrayList<>();
        for (Valuation val : valuations){
            if (formula.evaluate(val)){
                trueValuations.add(val);
                System.out.println ("true val: " + val);
            }
        }
        //System.out.println (trueValuations);
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
        return exponent + 1; // Add 1 to align with your example
    }
  
}