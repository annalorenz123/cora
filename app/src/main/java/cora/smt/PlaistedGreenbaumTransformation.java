package cora.smt;
import charlie.smt.*;
import cora.smt.*;
import java.util.ArrayList;

public class PlaistedGreenbaumTransformation{

     public static Constraint plaistedGreenbaumTransformation (Constraint formula, SmtProblem problem){
        if (ToCNF.inCNF(formula)) {
            return formula;
        }
        formula = ToCNF.convertNots(formula);
        if (ToCNF.inCNF(formula)) {
            return formula;
        }
        BVar full = problem.createBooleanVariable();
        ArrayList<Constraint> implications = replaceSubFormulaForVar(problem, full , formula);
        for (int i =0; i < implications.size(); i++){
            if (!(ToCNF.inCNF(implications.get(i)))){
                implications.set(i, ToCNF.distributiveLaw(implications.get(i)));
            }
        }
        for (int i =0; i < implications.size(); i++){
            if (!ToCNF.inCNF(implications.get(i))){
                throw new Error ("Not in CNF: " + implications.get(i));
            }
        }
        implications.add(full);
        return SmtFactory.createConjunction(implications);
    }

    public static boolean onlyVariables (Constraint c){
        if (c instanceof Conjunction con){
            for (int i =1; i <= con.numChildren(); i++){
                if (!(con.queryChild(i) instanceof BVar || con.queryChild(i) instanceof Not)){
                    return false;
                }
            }
            return true;
        }
        if (c instanceof Disjunction d){
            for (int i =1; i <= d.numChildren(); i++){
                if (!(d.queryChild(i) instanceof BVar || d.queryChild(i) instanceof Not)){
                    return false;
                }
            }
            return true;
        }
        else throw new Error (c + " not supported in onlyVariables.");
    }

    public static ArrayList<Constraint> replaceSubFormulaForVar (SmtProblem problem, BVar previousVar, Constraint c){
        ArrayList<Constraint> list = new ArrayList<>();
        if (c instanceof BVar || c instanceof Not) return list;
        else if (c instanceof Conjunction con){
            if (onlyVariables(c)) {list.add(SmtFactory.createImplication(previousVar, c)); return list;};
            ArrayList<Constraint> args = new ArrayList<>();
            for (int i = 1; i <= con.numChildren(); i++){
                if (con.queryChild(i) instanceof BVar || con.queryChild(i) instanceof Not) args.add(con.queryChild(i));
                else if (con.queryChild(i) instanceof Conjunction || con.queryChild(i) instanceof Disjunction){
                    BVar newvar = problem.createBooleanVariable();
                    args.add(newvar);
                    list.addAll(replaceSubFormulaForVar(problem, newvar, con.queryChild(i)));
                }
                else throw new Error (con.queryChild(i) + " not supported.");
            }
            list.add(SmtFactory.createImplication(previousVar, SmtFactory.createConjunction(args)));
        } 
        else if (c instanceof Disjunction d){
            if (onlyVariables(c)) {list.add(SmtFactory.createImplication(previousVar, c)); return list;};
            ArrayList<Constraint> args = new ArrayList<>();
            for (int i = 1; i <= d.numChildren(); i++){
                if (d.queryChild(i) instanceof BVar || d.queryChild(i) instanceof Not) args.add(d.queryChild(i));
                else if (d.queryChild(i) instanceof Conjunction || d.queryChild(i) instanceof Disjunction){
                    BVar newvar = problem.createBooleanVariable();
                    args.add(newvar);
                    list.addAll(replaceSubFormulaForVar(problem, newvar, d.queryChild(i)));
                }
                else throw new Error (d.queryChild(i) + " not supported.");
            }
            list.add(SmtFactory.createImplication(previousVar, SmtFactory.createDisjunction(args)));
        } 
        else throw new Error (c + " not supported.");
        return list;
    }

}