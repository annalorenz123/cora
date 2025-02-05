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

public class BitBlastingLimitedBitWidth{
    static int bitWidth = 3;

    ArrayList<Constraint> constraints = new ArrayList<>();
    double timeBitBlasting = 0;
    double timeTseitinTransformation = 0;
    double timeMiniSat = 0;
    
    ArrayList<Constraint> allCarrys = new ArrayList<>();
    static ArrayList<ArrayList<BVar>> allVariables = new ArrayList<>();
    SmtProblem problem1;
    public static BVar falseVar;
    public static BVar trueVar;
    

    public SmtSolver.Answer checkSatisfiability(SmtProblem problem, ArrayList<IntegerExpression> expressions, boolean negative){
        if (expressions.size()==0) return new SmtSolver.Answer.YES(new Valuation());
        long startTime = System.nanoTime();
        falseVar = problem.createBooleanVariable();
        trueVar = problem.createBooleanVariable();
        for (int i =0; i < problem.numberIntegerVariables(); i++){
            allVariables.add(new ArrayList<>());
        }
        problem1=problem;
        ArrayList<IntegerExpression> c = new ArrayList<>();
        ArrayList<Constraint> args = new ArrayList<>();
        for (int i =0; i < expressions.size(); i++){
            switch(expressions.get(i)){
                case Addition a: c.addAll(makeSides(a)); break;
                case CMult cm: c.addAll(makeSides(cm)); break;
                case IVar v : c.add(v); c.add(SmtFactory.createValue(0)); break;
                default: throw new Error("expression of form: " + expressions.get(i) + " not supported.");
            }
        }
        int maxBitWidth =0;         
        for (int i =0; i < c.size(); i+=2){
            int currentBitWidth = determineBitWidth(c.get(i), c.get(i+1));
            if ( currentBitWidth > maxBitWidth){
                maxBitWidth = currentBitWidth;
            }
        }
        bitWidth = getConstantBitWidth(c);
        while (bitWidth <= maxBitWidth){
            for (int i =0; i < c.size(); i+=2){
                ArrayList<BVar> leftSide = convert(problem, c.get(i));
                ArrayList<BVar> rightSide = convert(problem, c.get(i+1));
                Constraint end = greaterOrEqual(leftSide, rightSide);
                args.add(end);
            }
            Constraint endConjunction = SmtFactory.createConjunction(args);
            endConjunction = addConstraints(endConjunction);
            if (endConjunction instanceof Conjunction){
                ((Conjunction)endConjunction).addChild(SmtFactory.createConjunction(SmtFactory.createNegation(falseVar),trueVar));
            }
            else {
                endConjunction = SmtFactory.createConjunction(endConjunction, SmtFactory.createConjunction(SmtFactory.createNegation(falseVar),trueVar));
            }
            long endTime = System.nanoTime();
            timeBitBlasting = (endTime - startTime) / 1_000_000.0;
            startTime = System.nanoTime();
            endConjunction = PlaistedGreenbaumTransformation.plaistedGreenbaumTransformation(endConjunction, problem);
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
            if (answer instanceof SmtSolver.Answer.YES) return answer;
                bitWidth++;
        }
        return new SmtSolver.Answer.NO();
    }

    public static int determineBitWidth (IntegerExpression leftSide, IntegerExpression rightSide){
        if (maxValue(leftSide) >= maxValue(rightSide)){
            return findExponent(maxValue(leftSide));
        }
        return findExponent(maxValue(rightSide));
        
    }

    public static int getConstantBitWidth(ArrayList<IntegerExpression> c){
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
        return findExponent(maxvalue);
    }

    public static int maxValue (IntegerExpression expr){
        switch (expr){
            case IValue b: return b.queryValue();
            case IVar b : return ((int)Math.pow(2,bitWidth))-1;
            case CMult cm : return cm.queryConstant()*maxValue(cm.queryChild());
            case Addition a: 
                int total = maxValue(a.queryChild(1));
                for (int i =2; i <= a.numChildren(); i++){
                    total += maxValue(a.queryChild(i));
                }
                return total;
            default: throw new Error (expr + " not supported in maxValue.");
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

    public ArrayList<BVar> add(SmtProblem problem, Addition a){
        ArrayList<BVar> con = new ArrayList<>();
        switch (a.queryChild(1)){
            case IVar v : con = convert(problem, v); break;
            case IValue val : con = convert(val); break;
            case CMult c : con = multiply(convert((IValue)SmtFactory.createValue(c.queryConstant())), convert(problem, (IVar)c.queryChild())); break;
            default: throw new Error(a.queryChild(1).getClass() + " not supported yet.");
        }
        for (int j =2; j <= a.numChildren(); j++){
            switch (a.queryChild(j)){
                case IVar var: con = add(con, convert(problem, var)); break;
                case IValue v : con = add(con, convert(v)); break;
                case CMult c : con = add(con, multiply(convert((IValue)SmtFactory.createValue(c.queryConstant())), convert(problem, (IVar)c.queryChild()))); break;
                default: throw new Error(a.queryChild(j).getClass() + " not supported yet.");
            }
        }
        return con;
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
        result.add((BVar)carry);
        return result;        
    }

    public Constraint subtract(ArrayList<BVar> minuend, ArrayList<BVar> subtrahend) {
        if (isZero(subtrahend)) return falseVar;
        if (isZero(minuend)) return SmtFactory.createDisjunction(convertList(subtrahend));
        
        if (minuend.size()!= subtrahend.size()) {
            
            if (minuend.size() < subtrahend.size()){
                minuend = addFalses(minuend, subtrahend.size());
            }
            else subtrahend = addFalses(subtrahend, minuend.size());
        }
        int n = minuend.size();
        Constraint borrow = SmtFactory.createFalse();
        ArrayList<BVar> result = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            BVar a = minuend.get(i);
            BVar b = subtrahend.get(i);
            System.out.println ("a: " + a);
            System.out.println ("b: " + b);
            Constraint newBorrow = SmtFactory.createFalse();
            if (i == 0){
                newBorrow = SmtFactory.createConjunction(SmtFactory.createNegation(a), b);
            }
            else{
                newBorrow = SmtFactory.createDisjunction(SmtFactory.createConjunction(SmtFactory.createNegation(a), b), SmtFactory.createConjunction(borrow, SmtFactory.createNegation(xor(a,b))));
            }
            borrow = problem1.createBooleanVariable();
            constraints.add(SmtFactory.createIff(borrow, newBorrow));
            System.out.println ("borrow: " + SmtFactory.createIff(borrow, newBorrow));
        }
        return borrow;
    }

    public ArrayList<BVar> leftShift(ArrayList<BVar> formula, int i){
        for (int j = 0; j < i; j++){
            formula.add(0, falseVar);
        }
        return formula;
    }

    public ArrayList<BVar> multiply(ArrayList<BVar> lhs, ArrayList<BVar> rhs) {
        ArrayList<BVar> result = new ArrayList<>();

        for (int i = 0; i < bitWidth; i++) {
            BVar left = lhs.get(i);
            if (left.queryIndex()==2){
                ArrayList<BVar> shifted = new ArrayList<>();
                ArrayList<BVar> rhscopy = new ArrayList<>(rhs); 
                shifted = leftShift(rhscopy, i);
                result = new ArrayList<>(add(shifted, result));
            }
        }
        return result;

    }

    public static ArrayList<BVar> removeFalses (ArrayList<BVar> formula){
        ArrayList<BVar> newFormula = new ArrayList<>();
        for (int i =0; i < formula.size(); i++){
            if (!(((BVar)(formula.get(i))).queryName().contains("false"))) newFormula.add(formula.get(i));
        }
        return newFormula;
    }

    public ArrayList<BVar> convert (SmtProblem problem, IVar v){
        if (!allVariables.get(v.queryIndex()-1).isEmpty()){
            if (allVariables.get(v.queryIndex()-1).size() != bitWidth) allVariables.set(v.queryIndex()-1, removeFalses(allVariables.get(v.queryIndex()-1)));
            return allVariables.get(v.queryIndex()-1);
        } 
        ArrayList<BVar> newvar = new ArrayList<>();
        for (int i =0; i < bitWidth; i++){
            newvar.add(problem.createBooleanVariable());
        }
        allVariables.set(v.queryIndex()-1, new ArrayList<>(newvar));
        return newvar;
    }

    public ArrayList<BVar> convert (IValue v){
        String value = Integer.toBinaryString(v.queryValue());
        if (value.length() > bitWidth){
            throw new Error ("Value " + v.queryValue() + " too big for bitwidth.");
        } 
        if (value.length() < bitWidth) {
            value = addZeros(value);
        }
        ArrayList<BVar> valuev = new ArrayList<>();
        for (int i =bitWidth-1; i >= 0; i--){
            if (value.charAt(i)=='1'){
                valuev.add(trueVar);
            } 
            else valuev.add(falseVar);
        }
        return valuev;
    }

    public String addZeros (String value){
        for (int i = value.length(); i < bitWidth; i++){
            value = "0" + value;
        }
        return value;
    }

    public Constraint xor (Constraint a, Constraint b){
        return SmtFactory.createConjunction(SmtFactory.createDisjunction(a,b), SmtFactory.createNegation(SmtFactory.createConjunction(a,b)));

    }

    public ArrayList<BVar> addFalses (ArrayList<BVar> adding, int size){
        ArrayList<BVar> newvar = new ArrayList<>(adding);
        for (int i = adding.size(); i < size; i++){
            newvar.add(falseVar);
        }
        return newvar;
    }

    public boolean isZero (ArrayList<BVar> check){
        for (BVar c : check){
            if (!(c.queryIndex() ==1)) return false;
        }
        return true;
    }

    public Constraint greaterOrEqual (ArrayList<BVar> leftSide, ArrayList<BVar> rightSide){
        return SmtFactory.createNegation(subtract(leftSide, rightSide));
    }

    public Constraint addConstraints (Constraint endConjunction){
        if (constraints.isEmpty()) return endConjunction;
        if (endConjunction instanceof Conjunction conjunction){
            for (int i =0; i < constraints.size(); i++){
                Constraint c = constraints.get(i);
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
        String filePath = "output.txt"; // Adjust path if needed
        Valuation v = new Valuation();
        SimplexMethod sm = new SimplexMethod();
        try (BufferedReader reader = new BufferedReader(new FileReader(filePath))) {
            String firstLine = reader.readLine();
            if (firstLine.equals("SAT") || firstLine.equals("SATISFIABLE")) {
                String valuation = reader.readLine();
                ArrayList<String> numbersList = new ArrayList<>(Arrays.asList(valuation.split(" ")));
                for (int a =0; a < allVariables.size(); a++){
                    ArrayList<Constraint> binary = new ArrayList<>();
                    for (int i =0; i < bitWidth; i++){
                        int index = ((BVar)allVariables.get(a).get(i)).queryIndex();
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
                    throw new Error ("Bitblasting gave answer that does not hold: " + v);
                }
                return new SmtSolver.Answer.YES(v);
            }
        } catch (IOException e) {
            System.err.println("An error occurred while reading the file: " + e.getMessage());
        }
        return new SmtSolver.Answer.NO();
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
                throw new Error ("Truth and Falsehood not allowed.");
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

}