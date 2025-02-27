package cora.smt;
import charlie.smt.*;
import cora.smt.*;
import java.util.ArrayList;

public class TseitinTransformation{

     public static Constraint tseitinTransformation (Constraint formula, SmtProblem problem){
        if (ToCNF.inCNF(formula)) {
            return formula;
        }
        BVar full = problem.createBooleanVariable();
        ArrayList<Constraint> biimplications = replaceSubFormulaForVar(problem, full, formula);
        for (int i =0; i < biimplications.size(); i++){
            if (!(ToCNF.inCNF(biimplications.get(i)))){
                biimplications.set(i, ToCNF.convertNots(biimplications.get(i)));
            }
        }
        for (int i =0; i < biimplications.size(); i++){
            if (!(ToCNF.inCNF(biimplications.get(i)))){
                biimplications.set(i, ToCNF.distributiveLaw(biimplications.get(i)));
            }
        }
        for (int i =0; i < biimplications.size(); i++){
            if (!ToCNF.inCNF(biimplications.get(i))){
                throw new Error ("Not in CNF: " + biimplications.get(i));
            }
        }
        biimplications.add(full);
        return SmtFactory.createConjunction(biimplications);
    }

    public static boolean onlyVariables (Constraint c){
        if (c instanceof Conjunction con){
            for (int i =1; i <= con.numChildren(); i++){
                if (!(con.queryChild(i) instanceof BVar || (con.queryChild(i) instanceof Not n && n.queryChild() instanceof BVar))){
                    return false;
                }
            }
            return true;
        }
        if (c instanceof Disjunction d){
            for (int i =1; i <= d.numChildren(); i++){
                if (!(d.queryChild(i) instanceof BVar || (d.queryChild(i) instanceof Not n2 && n2.queryChild() instanceof BVar))){
                    return false;
                }
            }
            return true;
        }
        else throw new Error (c + " not supported in onlyVariables.");
    }

    public static ArrayList<Constraint> replaceSubFormulaForVar (SmtProblem problem, BVar previousVar, Constraint c){
        ArrayList<Constraint> list = new ArrayList<>();
        if (c instanceof BVar) return list;
        else if (c instanceof Not n){
            if (n.queryChild() instanceof BVar) {
                list.add(SmtFactory.createImplication(previousVar, n)); 
                list.add(SmtFactory.createImplication(n, previousVar));
                return list; 
            }
            else if (n.queryChild() instanceof Not n2){
                return replaceSubFormulaForVar(problem, previousVar, n2.queryChild());
            }
            else {
                BVar newvar = problem.createBooleanVariable();
                list.add(SmtFactory.createImplication(previousVar, SmtFactory.createNegation(newvar)));
                list.add(SmtFactory.createImplication(SmtFactory.createNegation(newvar), previousVar));
                list.addAll(replaceSubFormulaForVar(problem, newvar, n.queryChild()));
            }
        }
        else if (c instanceof Conjunction con){
            if (onlyVariables(c)) {
                list.add(SmtFactory.createImplication(previousVar, c));
                list.add(SmtFactory.createImplication(c, previousVar)); 
                return list;
            }
            ArrayList<Constraint> args = new ArrayList<>();
            for (int i = 1; i <= con.numChildren(); i++){
                if (con.queryChild(i) instanceof BVar) args.add(con.queryChild(i));
                else if (con.queryChild(i)  instanceof Conjunction || con.queryChild(i) instanceof Disjunction || con.queryChild(i)  instanceof Not){
                    BVar newvar = problem.createBooleanVariable();
                    args.add(newvar);

                    list.addAll(replaceSubFormulaForVar(problem, newvar, con.queryChild(i) ));
                }
                else throw new Error (con.queryChild(i) + " not supported.");
            }
            list.add(SmtFactory.createImplication(previousVar, SmtFactory.createConjunction(args)));
            list.add(SmtFactory.createImplication(SmtFactory.createConjunction(args), previousVar));
        } 
        else if (c instanceof Disjunction d){
            if (onlyVariables(c)) {
                list.add(SmtFactory.createImplication(previousVar, c));
                list.add(SmtFactory.createImplication(c, previousVar)); 
                return list;
            }
            ArrayList<Constraint> args = new ArrayList<>();
            for (int i = 1; i <= d.numChildren(); i++){
                if (d.queryChild(i) instanceof BVar) args.add(d.queryChild(i));
                else if (d.queryChild(i) instanceof Conjunction || d.queryChild(i) instanceof Disjunction || d.queryChild(i) instanceof Not){
                    BVar newvar = problem.createBooleanVariable();
                    args.add(newvar);
                    list.addAll(replaceSubFormulaForVar(problem, newvar, d.queryChild(i)));
                }
                else throw new Error (d.queryChild(i) + " not supported.");
            }
            list.add(SmtFactory.createImplication(previousVar, SmtFactory.createDisjunction(args)));
            list.add(SmtFactory.createImplication(SmtFactory.createDisjunction(args), previousVar));
        } 
        else throw new Error (c + " not supported.");
        return list;
    }

}