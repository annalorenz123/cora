package cora.smt;
import charlie.smt.*;
import cora.smt.*;
import java.util.ArrayList;

public class TseitinTransformation{

     public static Constraint tseitinTransformation (Constraint formula, SmtProblem problem){
        if (TseitinTransformationOLD.inCNF(formula)) {
            return formula;
        }
        BVar full = problem.createBooleanVariable();
        ArrayList<Constraint> biimplications = replaceSubFormulaForVar(problem, full, formula);
        System.out.println ("subformulas made");
        System.out.println ("full: " + full);
        //biImplications = biImplicationsToImplications(biImplications);
        System.out.println (biimplications);
        System.out.println ("length before converted nots: " + ToCNF.countNumberOfObjects(SmtFactory.createConjunction(biimplications), 0));
        for (int i =0; i < biimplications.size(); i++){
            if (!(TseitinTransformationOLD.inCNF(biimplications.get(i)))){
                biimplications.set(i, ToCNF.convertNots(biimplications.get(i)));
            }
        }
        System.out.println ("length after converted nots: " + ToCNF.countNumberOfObjects(SmtFactory.createConjunction(biimplications), 0));
        for (int i =0; i < biimplications.size(); i++){
            if (!(TseitinTransformationOLD.inCNF(biimplications.get(i)))){
                biimplications.set(i, ToCNF.distributiveLaw(biimplications.get(i)));
            }
        }
        System.out.println ("length after dislaw: " + ToCNF.countNumberOfObjects(SmtFactory.createConjunction(biimplications), 0));

        System.out.println ("in cnf");
        //System.out.println (biImplications);
        for (int i =0; i < biimplications.size(); i++){
            if (!TseitinTransformationOLD.inCNF(biimplications.get(i))){
                //System.out.println ("NOT IN CNF: " + biimplications.get(i));
                throw new Error ("not in cnf: " + biimplications.get(i));
            }
        }
        biimplications.add(full);
        if (!(full instanceof BVar)) throw new Error ("full not instance of bvar: " + full);
        System.out.println ("added: " + full);
        System.out.println ("end: " + SmtFactory.createConjunction(biimplications));
        return SmtFactory.createConjunction(biimplications);
        //return formula;
    }

    public static boolean onlyVariables (Constraint c){
        if (c instanceof Conjunction con){
            for (int i =1; i <= con.numChildren(); i++){
                if (!(con.queryChild(i) instanceof BVar)){
                    return false;
                }
            }
            return true;
        }
        if (c instanceof Disjunction d){
            for (int i =1; i <= d.numChildren(); i++){
                if (!(d.queryChild(i) instanceof BVar)){
                    return false;
                }
            }
            return true;
        }
        else throw new Error (c + " not supported in onlyvariables");
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
                if (con.queryChild(i) instanceof BVar) args.add(con.queryChild(i) );
                else if (con.queryChild(i)  instanceof Conjunction || con.queryChild(i) instanceof Disjunction || con.queryChild(i)  instanceof Not){
                    BVar newvar = problem.createBooleanVariable();
                    args.add(newvar);

                    list.addAll(replaceSubFormulaForVar(problem, newvar, con.queryChild(i) ));
                    //list.add(previousVar, con.queryChild(i)); //??
                }
                else throw new Error (con.queryChild(i) + " not supported in replacesubformulaforvar");
            }
            list.add(SmtFactory.createImplication(previousVar, SmtFactory.createConjunction(args)));
            list.add(SmtFactory.createImplication(SmtFactory.createConjunction(args), previousVar));
            //list.add(SmtFactory.createImplication(previousVar, SmtFactory.createConjunction(args)));

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
                else throw new Error (d.queryChild(i) + " not supported in replacesubformulaforvar");
            }
            list.add(SmtFactory.createImplication(previousVar, SmtFactory.createDisjunction(args)));
            list.add(SmtFactory.createImplication(SmtFactory.createDisjunction(args), previousVar));
        } 
        else throw new Error (c + " not supported in replacesubformulaforvar");

        //return simplify(list);
        return list;
    }

    public static ArrayList<Constraint> simplify (ArrayList<Constraint> list){
        System.out.println (list);
        for (int i =0; i < list.size(); i+=2){
            Constraint c = ((Disjunction)list.get(i)).queryChild(2);
            for (int j =0; j < list.size(); j+=2){
                if (i!=j){
                    if ((((Disjunction)list.get(j)).queryChild(2)).equals(c)){
                        Constraint newimplication = SmtFactory.createImplication(((Not)(((Disjunction)list.get(j)).queryChild(1))).queryChild(), ((Not)(((Disjunction)list.get(i)).queryChild(1))).queryChild());
                        Constraint otherwayaround = SmtFactory.createImplication(((Not)(((Disjunction)list.get(i)).queryChild(1))).queryChild(), ((Not)(((Disjunction)list.get(j)).queryChild(1))).queryChild());
                        list.set(j, newimplication);
                        list.set(j+1, otherwayaround);
                    }
                }
            }
        }
        return list;
    }


    public static Constraint replace (Constraint expr, Constraint old, Constraint newExpr){
        //System.out.println ("in replace for " + expr);
        //replace oldVar in expr for newExpr
        if (expr.equals(old)) return newExpr;
        switch (expr) {
            case Not n : return SmtFactory.createNegation(replace (n.queryChild(), old, newExpr));
            case Conjunction c: 
                ArrayList<Constraint> newargs = new ArrayList<>();
                for (int i =1; i <= c.numChildren(); i++){
                    newargs.add(replace(c.queryChild(i), old, newExpr));
                }
                return SmtFactory.createConjunction(newargs);
            case Disjunction d: 
                ArrayList<Constraint> newargs2 = new ArrayList<>();
                for (int i =1; i <= d.numChildren(); i++){
                    newargs2.add(replace(d.queryChild(i), old, newExpr));
                }
                return SmtFactory.createDisjunction(newargs2);
            default: return expr;
        }
  }
}