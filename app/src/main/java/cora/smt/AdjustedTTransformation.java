package cora.smt;
import charlie.smt.*;
import cora.smt.*;
import java.util.ArrayList;

public class AdjustedTTransformation{

     public static Constraint tseitinTransformation (Constraint formula, SmtProblem problem){
        if (TseitinTransformationOLD.inCNF(formula)) {
            return formula;
        }
        System.out.println ("going to convert nots");
        formula = ToCNF.convertNots(formula);
        if (TseitinTransformationOLD.inCNF(formula)) {
            return formula;
        }
        System.out.println ("converted nots");
        System.out.println (formula);
        //return formula;
        // System.out.println ("not in cnf: " + formula);
        BVar full = problem.createBooleanVariable();
        ArrayList<Constraint> implications = replaceSubFormulaForVar(problem, full , formula);
        System.out.println ("subformulas made");
        System.out.println (implications);
        // ArrayList<Constraint> biImplications = new ArrayList<>();
        // for (Constraint f : subFormulas){
        //     biImplications.add(SmtFactory.createImplication(problem.createBooleanVariable(), f));
        // }
        // System.out.println ("before replacing ");
        // biImplications = replaceFormulaForVariable(biImplications);
        // System.out.println ("after replacing ");
        //final Constraint full = ((Not)(((Disjunction)implications.get(implications.size()-1)).queryChild(1))).queryChild();
        System.out.println ("full: " + full);
        //biImplications = biImplicationsToImplications(biImplications);
        //System.out.println (biImplications);
        for (int i =0; i < implications.size(); i++){
            // if (!(TseitinTransformationOLD.inCNF(biImplications.get(i)))){
            //     biImplications.set(i, ToCNF.convertNots(biImplications.get(i)));
            // }
            if (!(TseitinTransformationOLD.inCNF(implications.get(i)))){
                implications.set(i, ToCNF.distributiveLaw(implications.get(i)));
            }
        }

        System.out.println ("in cnf");
        //System.out.println (biImplications);
        for (int i =0; i < implications.size(); i++){
            if (!TseitinTransformationOLD.inCNF(implications.get(i))){
                System.out.println ("NOT IN CNF: " + implications.get(i));
                throw new Error ("not in cnf: " + implications.get(i));
            }
        }
        implications.add(full);
        System.out.println ("added: " + full);
        // System.out.println ("end: " + SmtFactory.createConjunction(biImplications));
        return SmtFactory.createConjunction(implications);
        //return formula;
    }

    public static ArrayList<Constraint> replaceFormulaForVariable (ArrayList<Constraint> biImplications){
        for (int i =0; i < biImplications.size(); i++){
        //System.out.println ("going to check for replacements for " + biImplications.get(i));
        //for (int j =i+1; j < biImplications.size(); j++){
            switch (((Not)((Disjunction)biImplications.get(i)).queryChild(1)).queryChild()){
                case BVar b : break;
                case Conjunction c:
                    ArrayList<Constraint> newargs = new ArrayList<>();
                    for (int k=1; k <= c.numChildren(); k++){
                        if (!(c.queryChild(k) instanceof BVar b)){
                            boolean foundReplacement = false;
                            for (int r = i+1; r < biImplications.size(); r++){
                                if (c.queryChild(k).equals(((Iff)biImplications.get(r)).queryRight())){
                                    newargs.add(((Iff)biImplications.get(r)).queryLeft());
                                    foundReplacement = true;
                                }
                            }
                            if (!foundReplacement) newargs.add(c.queryChild(k));
                        }
                        else newargs.add(b);
                    }
                    biImplications.set(i, SmtFactory.createIff(((Iff)biImplications.get(i)).queryLeft(), SmtFactory.createConjunction(newargs)));
                    break;
                case Disjunction d:
                    ArrayList<Constraint> newargs2 = new ArrayList<>();
                    for (int k=1; k <= d.numChildren(); k++){
                        if (!(d.queryChild(k) instanceof BVar b)){
                            boolean foundReplacement = false;
                            for (int r = i+1; r < biImplications.size(); r++){
                                if (d.queryChild(k).equals(((Iff)biImplications.get(r)).queryRight())){
                                    newargs2.add(((Iff)biImplications.get(r)).queryLeft());
                                    foundReplacement = true;
                                    //System.out.println ("swapping " + d.queryChild(k) + " for "+((Iff)biImplications.get(r)).queryLeft());
                                }
                            }
                            if (!foundReplacement) newargs2.add(d.queryChild(k));
                        }
                        else newargs2.add(b);
                    }
                    biImplications.set(i, SmtFactory.createIff(((Iff)biImplications.get(i)).queryLeft(), SmtFactory.createDisjunction(newargs2)));
                    break;
                case Not n:
                    if (n.queryChild() instanceof Falsehood) biImplications.set(i, SmtFactory.createIff(((Iff)biImplications.get(i)).queryLeft(), SmtFactory.createTrue()));
                    for (int j = i+1; j < biImplications.size(); j++){
                        if (n.queryChild().equals(((Iff)biImplications.get(j)).queryRight())){
                            biImplications.set(i, SmtFactory.createIff(((Iff)biImplications.get(i)).queryLeft(), SmtFactory.createNegation(((Iff)biImplications.get(j)).queryLeft())));
                        }                  
                    }
                    
                    break;    
                default: throw new Error ("expression of form " + biImplications.get(i) + " not supported.");

            }

            //}
            //System.out.println ("result is " + biImplications.get(i));
        }
        
        return biImplications;
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
        else throw new Error (c + " not supported in onlyvariables");
    }

    // public static ArrayList<Constraint> makeSubFormulas (SmtProblem problem, Constraint c){
    //     ArrayList<Constraint> subFormulas = new ArrayList<>();
    //     switch (c){
    //         case BVar b : return new ArrayList<>();
    //         case Falsehood f: return new ArrayList<>();
    //         case Truth t : return new ArrayList<>();
    //         case Conjunction con: 
    //             BVar x = problem.createBooleanVariable();
    //             ArrayList<Constraint> args = new ArrayList<>();
    //             for (int i = 1; i <= con.numChildren(); i++){
    //                 if (con.queryChild(i) instanceof Conjunction || con.queryChild(i) instanceof Disjunction){
    //                     BVar newbvar = problem.createBooleanVariable();
    //                     subFormulas.add(SmtFactory.createImplication(newbvar, con.queryChild(i)));
    //                     args.add(newbvar);
    //                     if (!(onlyVariables(con.queryChild(i)))) subFormulas.addAll(problem, con.queryChild(i));
    //                 }
    //                 else args.add(con.queryChild(i));
    //                 subFormulas.add(SmtFactory.createImplication(x,SmtFactory.createConjunction(args)));
    //                 for (Constraint arg : args){
    //                     subFormulas.add(x, arg);
    //                 }
                    
    //             }
    //             break;
    //         case Disjunction d: 
    //             BVar x1 = problem.createBooleanVariable();
    //             if (onlyVariables(d)) subFormulas.add(SmtFactory.createImplication(x1,d)); 
    //             else{
    //                 ArrayList<Constraint> args2 = new ArrayList<>();
    //                 for (int i = 1; i <= d.numChildren(); i++){
    //                     if (d.queryChild(i) instanceof Conjunction || d.queryChild(i) instanceof Disjunction){
    //                         BVar newbvar = problem.createBooleanVariable();
    //                         subFormulas.add(SmtFactory.createImplication(newbvar, con.queryChild(i)));
    //                         args.add(newbvar);
    //                         if (!(onlyVariables(con.queryChild(i)))) subFormulas.addAll(problem, con.queryChild(i))
    //                 }
    //             }
    //             break;
    //         case Not n : if (!(n.queryChild() instanceof BVar) ) throw new Error ("nested not: " + n); break;
    //         // case Iff i:
    //         //     subFormulas.add(i);
    //         //     subFormulas.addAll(makeSubFormulas(problem, i.queryLeft()));
    //         //     subFormulas.addAll(makeSubFormulas(problem, i.queryRight()));
    //         //     break;
    //         default: throw new Error (c + " not supported yet.");

    //     }
    //     //System.out.println (subFormulas);
    //     return subFormulas;
    // }}

    // public static ArrayList<Constraint> subFormulas (SmtProblem problem, Constraint c){
    //     BVar x1 = problem.createBooleanVariable();
    //     while (!(onlyVariables(c))){
    //         if (c instanceof Conjunction con){
    //             for (int i = 1; i <= con.numChildren(); i++){
    //                 if (con.queryChild(i) instanceof Conjunction || con.queryChild(i) instanceof Disjunction){
    //                     BVar newbvar = problem.createBooleanVariable();
    //                     subFormulas.add(SmtFactory.createImplication(newbvar, replaceNestedFormulas(con.queryChild(i))));
    //                     args.add(newbvar);
    //                     if (!(onlyVariables(con.queryChild(i)))) subFormulas.addAll(problem, con.queryChild(i));
    //                 }
    //             }
    //         }
    //     }
    // }

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
                    //list.add(previousVar, con.queryChild(i)); //??
                }
                else throw new Error (con.queryChild(i) + " not supported in replacesubformulaforvar");
            }
            // for (Constraint cons : args){
            //     list.add(SmtFactory.createImplication(previousVar, cons));
            // }
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
                else throw new Error (d.queryChild(i) + " not supported in replacesubformulaforvar");
            }
            list.add(SmtFactory.createImplication(previousVar, SmtFactory.createDisjunction(args)));
        } 
        else throw new Error (c + " not supported in replacesubformulaforvar");

        return list;
    }

    // public ArrayList<Constraint> replaceNestedFormulas (SmtProblem problem, Constraint c){
    //     ArrayList<Constraint> implications = new ArrayList<>();
    //     if (c instanceof BVar || c instanceof Not) return c;
    //     if (c instanceof Conjunction con){
    //         implications.add(SmtFactory,createImplication(problem.createBooleanVariable(), replaceSubFormulaForVar(con)));

    //         // for (int i = 1; i <= con.numChildren(); i++){
    //         //     while (con.queryChild(i) instanceof Conjunction || con.queryChild(i) instanceof Disjunction){
    //         //         BVar newbvar = problem.createBooleanVariable();
    //         //         subFormulas.add(SmtFactory.createImplication(newbvar, replaceNestedFormulas(con.queryChild(i))));
    //         //         args.add(newbvar);
    //         //         if (!(onlyVariables(con.queryChild(i)))) subFormulas.addAll(problem, con.queryChild(i));
    //         //     }
    //         // }    
    //     }

    // }
}