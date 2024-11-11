
package cora.smt;
import charlie.smt.*;
import cora.smt.*;
import java.util.*;




public class TseitinTransformation{
    static ArrayList<BVar> auxVariables = new ArrayList<>();
    private static HashMap<Constraint, BVar> auxVars = new HashMap<>();

    public static void main(String[] args) {
        SmtProblem problem = new SmtProblem();
        Constraint test = SmtFactory.createImplication(SmtFactory.createConjunction(SmtFactory.createBooleanVariable(problem), SmtFactory.createDisjunction(SmtFactory.createBooleanVariable(problem), SmtFactory.createBooleanVariable(problem))), SmtFactory.createNegation(SmtFactory.createBooleanVariable(problem)));
        //Constraint test = SmtFactory.createNegation(SmtFactory.createDisjunction(SmtFactory.createImplication(problem.createBooleanVariable(), problem.createBooleanVariable()),SmtFactory.createImplication(problem.createBooleanVariable(), problem.createBooleanVariable()) ));
        Constraint end = tseitinTransformation(test, problem);
        //System.out.println (end);
    }


    public static Constraint tseitinTransformation (Constraint formula, SmtProblem problem){
        System.out.println ("converting: " + formula);

        if (inCNF(formula)) return formula;
        else{
            if (formula instanceof Disjunction d){
                formula = distributiveLaw(formula);
            }
            else{
                formula = deMorgan(formula);
            }
        }
        if (inCNF(formula)) {
            System.out.println ("in cnf: " + formula);
            return formula;
        }
        if (formula instanceof Disjunction d){
            formula = distributiveLaw(formula);
        }
        else{
            formula = deMorgan(formula);
        }
        System.out.println ("not in cnf: " + formula);
        ArrayList<Constraint> subFormulas = makeSubFormulas(problem, formula);
        System.out.println ("subformulas: " + subFormulas);
        ArrayList<Constraint> biImplications = new ArrayList<>();
        for (Constraint f : subFormulas){
            biImplications.add(SmtFactory.createIff(problem.createBooleanVariable(), f));
        }
        
        biImplications = replaceFormulaForVariable(biImplications);
        System.out.println ("after replacing: " +biImplications);
        Constraint full = ((Iff)biImplications.get(0)).queryLeft();
        biImplications = biImplicationsToImplications(biImplications);
        //System.out.println (biImplications);
        for (int i =0; i < biImplications.size(); i++){
            if (inCNF(biImplications.get(i))){
                System.out.println ("IN CNF: " + biImplications.get(i));
            }
            else {
                System.out.println (biImplications.get(i) + " is not in cnf");
                // for (int j =0; j < biImplications.size(); j++){
                //     biImplications.set(j, convertNots(biImplications.get(j)));
                // }
                if (biImplications.get(i) instanceof Conjunction || biImplications.get(i) instanceof Not){
                    biImplications.set(i, deMorgan(biImplications.get(i)));
                }
                else if (biImplications.get(i) instanceof Disjunction) biImplications.set(i, distributiveLaw(biImplications.get(i)));
                else throw new Error ("what law to apply on " + biImplications.get(i));
                System.out.println ("converted it to: " + biImplications.get(i));
            }
        }
        System.out.println ("second try:");
        for (int i =0; i < biImplications.size(); i++){
            if (inCNF(biImplications.get(i))){
                System.out.println ("IN CNF: " + biImplications.get(i));
            }
            else {
                System.out.println (biImplications.get(i) + " is not in cnf");
                if (biImplications.get(i) instanceof Conjunction || biImplications.get(i) instanceof Not){
                    biImplications.set(i, deMorgan(biImplications.get(i)));
                }
                else if (biImplications.get(i) instanceof Disjunction) biImplications.set(i, distributiveLaw(biImplications.get(i)));
                else throw new Error ("what law to apply on " + biImplications.get(i));
                System.out.println ("converted it to: " + biImplications.get(i));
            }
        }
        System.out.println (biImplications);
        for (int i =0; i < biImplications.size(); i++){
            if (!inCNF(biImplications.get(i))){
                System.out.println ("NOT IN CNF: " + biImplications.get(i));
                throw new Error ("not in cnf: " + biImplications.get(i));
            }
        }
        biImplications.add(full);
        System.out.println ("end: " + SmtFactory.createConjunction(biImplications));
        return SmtFactory.createConjunction(biImplications);
        //return formula;
    }

    public static ArrayList<Constraint> makeSubFormulas (SmtProblem problem, Constraint c){
        ArrayList<Constraint> subFormulas = new ArrayList<>();
        switch (c){
            case BVar b : return new ArrayList<>();
            case Falsehood f: return new ArrayList<>();
            case Truth t : return new ArrayList<>();
            case Conjunction con: 
                subFormulas.add(con);
                for (int i = 1; i <= con.numChildren(); i++){
                    subFormulas.addAll(makeSubFormulas(problem, con.queryChild(i)));
                }
                break;
            case Disjunction d: 
                subFormulas.add(d);
                for (int i = 1; i <= d.numChildren(); i++){
                    subFormulas.addAll(makeSubFormulas(problem, d.queryChild(i)));
                }
                break;
            case Not n:
                if (n.queryChild() instanceof BVar) break;
                subFormulas.add(n);
                subFormulas.addAll(makeSubFormulas(problem, n.queryChild()));
                break;
            case Iff i:
                subFormulas.add(i);
                subFormulas.addAll(makeSubFormulas(problem, i.queryLeft()));
                subFormulas.addAll(makeSubFormulas(problem, i.queryRight()));
                break;
            default: throw new Error (c + " not supported yet.");

        }
        //System.out.println (subFormulas);
        return subFormulas;
    }

    public static ArrayList<Constraint> replaceFormulaForVariable (ArrayList<Constraint> biImplications){
        for (int i =0; i < biImplications.size(); i++){
            //System.out.println ("going to check for replacements for " + biImplications.get(i));
            //for (int j =i+1; j < biImplications.size(); j++){
                switch (((Iff)biImplications.get(i)).queryRight()){
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
            System.out.println ("result is " + biImplications.get(i));
        }
        
        return biImplications;
    }

    // public static ArrayList<Constraint> makeBiImplications (SmtProblem problem, Constraint formula){
    //     ArrayList<Constraint> biImplications = new ArrayList<>();
    //     System.out.println ("in makebiimplications for " + formula);
    //     switch (formula){
    //         case Falsehood f: break;
    //         case Truth t: break;
    //         case BVar b: break;
    //         case Conjunction c:
    //             if (allChildrenAreVars(c)) break;
    //             ArrayList<Constraint> args = new ArrayList<>();
                
    //             for (int i =1; i <= c.numChildren(); i++){
    //                 if (c.queryChild(i) instanceof BVar b){
    //                     args.add(b);
    //                 }
    //                 else {
    //                     BVar newVar = problem.createBooleanVariable();
    //                     args.add(newVar);
    //                     biImplications.add(SmtFactory.createIff(newVar, c.queryChild(i)));
    //                     formula = replace(formula, c.queryChild(i), newVar);
    //                     biImplications.addAll(makeBiImplications(problem, c.queryChild(i)));
    //                 }
    //             }
    //             biImplications.add(SmtFactory.createIff(problem.createBooleanVariable(), SmtFactory.createConjunction(args))); break;
    //         case Disjunction d:
    //             if (allChildrenAreVars(d)) break;
    //             ArrayList<Constraint> args2 = new ArrayList<>();
    //             for (int i =1; i <= d.numChildren(); i++){
    //                 if (d.queryChild(i) instanceof BVar b){
    //                     args2.add(b);
    //                 }
    //                 else {
    //                     BVar newVar = problem.createBooleanVariable();
    //                     args2.add(newVar);
    //                     biImplications.add(SmtFactory.createIff(newVar, d.queryChild(i)));
    //                     formula = replace(formula, d.queryChild(i), newVar);
    //                     biImplications.addAll(makeBiImplications(problem, d.queryChild(i)));
    //                 }
    //             }
    //             biImplications.add(SmtFactory.createIff(problem.createBooleanVariable(), SmtFactory.createDisjunction(args2))); break;
    //         case Not n:
    //             System.out.println ("in the not case: " + n);
    //             if (n.queryChild() instanceof BVar b) {
    //                 if (biImplications.size()!=0) biImplications.add(SmtFactory.createIff(problem.createBooleanVariable(), n));
    //             }
    //             else{
    //                 biImplications.add(SmtFactory.createIff(problem.createBooleanVariable(), n));
    //                 BVar newVar = problem.createBooleanVariable();
    //                 biImplications.add(SmtFactory.createIff(newVar, n.queryChild()));
    //                 System.out.println ("added: " + biImplications.get(biImplications.size()-1));
    //                 formula = replace(formula, n.queryChild(), newVar); 
    //                 biImplications.addAll(makeBiImplications(problem, n.queryChild()));
    //                 System.out.println ("added: " + biImplications.get(biImplications.size()-1));
    //             } break;
    //         default: throw new Error ("expression of format: " + formula + " from class " + formula.getClass() + " not supported.");
    //     }
    //     return biImplications;
    // }

    public static ArrayList<Constraint> biImplicationsToImplications (ArrayList<Constraint> biImplications ){
        for (int i =0; i < biImplications.size(); i++){
            Constraint left = ((Iff)biImplications.get(i)).queryLeft();
            Constraint right = ((Iff)biImplications.get(i)).queryRight();
            biImplications.set(i, SmtFactory.createConjunction(SmtFactory.createImplication(left, right), SmtFactory.createImplication(right, left))); 
        }
        System.out.println ("hey:" + SmtFactory.createConjunction(biImplications));
        return biImplications;
    }

    // public static ArrayList<Constraint> makeImplications (ArrayList<Constraint> subformulas){
    //     ArrayList<BVar> auxVariables = new ArrayList<>();
    //     ArrayList<Constraint> implications = new ArrayList<>();
    //     for (Constraint c : subFormulas){
    //         BVar newVar = SmtFactory.createBooleanVariable();
    //         auxVariables.add(newVar);
    //         implications.add(SmtFactory.createImplication(newVar, c));
            
    //         if (c instanceof Conjunction || c instanceof Disjunction){
    //             Constraint converted = deMorgan (SmtFactory.createNegation(c));
    //             if (inCNF(SmtFactory.createDisjunction(converted, newVar))){
    //                 implications.add(SmtFactory.createDisjunction(converted, newVar));

    //             }
    //             //else //try distributive law
    //         }
    //         else implications.add(SmtFactory.createImplication(c, newVar));
    //     }
        

   // }

    // public static Constraint convertNots (Constraint c){
    //     switch (c){
    //         case BVar b: return b;
    //         case Not n:
    //             if (n.queryChild() instanceof BVar) return n;
    //             else if (n.queryChild() instanceof Conjunction con){

    //             } 
    //     }
    // }


    public static Constraint deMorgan (Constraint c){
        if (c instanceof BVar) return c;
        if (c instanceof Conjunction con){
            ArrayList<Constraint> args = new ArrayList<>();
            for (int i =1; i <= con.numChildren(); i++){
                if (con.queryChild(i) instanceof Disjunction d){
                    args.add(distributiveLaw(con.queryChild(i).simplify()));
                }
                else args.add(deMorgan(con.queryChild(i).simplify()));
            }
            return SmtFactory.createConjunction(args).simplify();
        }
        if (c instanceof Not n){
            if (n.queryChild() instanceof Not){
                n.simplify();
            }
            Constraint child = n.queryChild();
            if (child instanceof Conjunction con){
                ArrayList<Constraint> args = new ArrayList<>();
                for (int i =1; i <= con.numChildren(); i++){
                    args.add(SmtFactory.createNegation(con.queryChild(i)).simplify());
                }
                return SmtFactory.createDisjunction(args);
            }
            else if (child instanceof Disjunction d){
                ArrayList<Constraint> args = new ArrayList<>();
                for (int i =1; i <= d.numChildren(); i++){
                    args.add(SmtFactory.createNegation(d.queryChild(i)).simplify());
                }
                return SmtFactory.createConjunction(args).simplify();
            }
            else if (child instanceof BVar) return n;
            else throw new Error("cannot apply demorgan laws on " + n);
        }
        else throw new Error("cannot apply demorgan laws on " + c);

    }

    public static Constraint distributiveLaw (Constraint c){
        ArrayList<Constraint> args = new ArrayList<>();
        if (c instanceof Disjunction d){
            for (int i =1; i < d.numChildren(); i++){
                Constraint firstChild = d.queryChild(i);
                Constraint secondChild = d.queryChild(i+1);
                if (inCNF(c)) return c;
                else if (firstChild instanceof BVar && secondChild instanceof BVar){
                    args.add(firstChild);
                    args.add(secondChild);
                }
                else if ((firstChild instanceof Not|| firstChild instanceof BVar )&& secondChild instanceof Conjunction con){
                    args.add(distributiveWithOneAnd(deMorgan(firstChild.simplify()), con));
                }
                else if ((secondChild instanceof Not || secondChild instanceof BVar) && firstChild instanceof Conjunction con){
                    args.add( distributiveWithOneAnd (deMorgan(secondChild.simplify()), con));
                }
                else if (firstChild instanceof Conjunction con1 && secondChild instanceof Conjunction con2){
                    args.add( distributiveWithTwoAnds (con1, con2));
                }
                else if (firstChild instanceof Not n && secondChild instanceof BVar b){
                    args.add(SmtFactory.createDisjunction(deMorgan(n.simplify()), b));
                }
                else if (secondChild instanceof Not n && firstChild instanceof BVar b){
                    args.add(SmtFactory.createDisjunction(deMorgan(n.simplify()), b));
                }
                else throw new Error (firstChild + " or " + secondChild + " not supported in dislaw.");
            }
        }
        return SmtFactory.createConjunction(args);
    }

    public static Constraint distributiveWithOneAnd (Constraint n, Conjunction c){
        ArrayList<Constraint> args = new ArrayList<>();
        for (int i =1; i <= c.numChildren(); i++){ 
            args.add( SmtFactory.createDisjunction(n, c.queryChild(i)));
        }
        return SmtFactory.createConjunction(args);
    }

    public static Constraint distributiveWithTwoAnds (Conjunction c1, Conjunction c2){
        ArrayList<Constraint> args = new ArrayList<>();
        for (int i =1; i <= c1.numChildren(); i++){
            for (int j=1; j<= c2.numChildren(); j++){
                args.add(SmtFactory.createDisjunction(c1.queryChild(i), c2.queryChild(j)));
            }
        }
        return SmtFactory.createConjunction(args);
    }


    public static boolean inCNF (ArrayList<Constraint> args){
        for (Constraint arg : args){
            if (!inCNF(arg)) return false;
        }
        return true;
    }

    public static boolean inCNF (Constraint arg){
        switch (arg){
            case Falsehood f: return true;
            case Truth t: return true;
            case BVar b : return true;
            case NBVar b : return true;
            case Not n: if (n.queryChild() instanceof BVar) return true; else return false;
            case Conjunction c : 
                for (int i =1; i <= c.numChildren(); i++){
                    if (c.queryChild(i) instanceof Conjunction || !inCNF(c.queryChild(i))) return false;
                }
                return true;
            case Disjunction d: 
                for (int i =1; i <= d.numChildren(); i++){
                    if (!(d.queryChild(i) instanceof BVar || d.queryChild(i) instanceof NBVar || (d.queryChild(i) instanceof Not n && n.queryChild() instanceof BVar))){
                        return false;
                    }
                }
                return true;
            
            default: throw new Error(arg + " not supported in inCNF");
        }
    }

    




    // public static Constraint replace (Constraint expr, Constraint oldCon, Constraint newCon){
    //     //System.out.println ("in replace for " + expr);
    //     //replace oldCon in expr for newCon
    //     if (expr.equals(oldCon)) return newCon;
    //     switch (expr) {
    //         case BVar x: return x;
    //         case Conjunction c: 
    //             ArrayList<Constraint> newArgs = new ArrayList<>();
    //             for (int i =1; i <= c.numChildren(); i++) newArgs.add(replace (c.queryChild(i),oldCon, newCon)); 
    //             return SmtFactory.createConjunction(newArgs);
    //         case Disjunction d:
    //             ArrayList<Constraint> newArgs2 = new ArrayList<>();
    //             for (int i =1; i <= d.numChildren(); i++) newArgs2.add(replace (d.queryChild(i), oldCon, newCon)); 
    //             return SmtFactory.createDisjunction(newArgs2);
    //         case Iff i:
    //             return SmtFactory.createIff(replace(i.queryLeft(), oldCon, newCon), replace(i.queryRight(), oldCon, newCon));
    //         case Not n: 
    //             return SmtFactory.createNegation(replace(n.queryChild(), oldCon, newCon));
    //         case Falsehood f : return f;
    //         case Truth t : return t;
    //         default:
    //             throw new Error("Expression of the form " + expr.toString() + " not supported!");
    //     }
    // }

    // public static Constraint convertToCNF(Constraint c){
    //     //to be implemented
    //     return c;
    // }

    // public static void convert (Constraint c, SmtProblem problem){
    //     if (c instanceof BVar b) return;
    //     if (!(auxVars.containsKey(c))) {
    //         //auxVars.put(c, problem.createBooleanVariable()); 
    //         if (c instanceof Conjunction con) {
    //             ArrayList<Constraint> args = new ArrayList<>();
    //             for (int i =1; i <= con.numChildren(); i++){
    //                 if (con.queryChild(i) instanceof BVar b) args.add(b); 
    //                 else if (auxVars.containsKey(con.queryChild(i))) args.add(auxVars.get(con.queryChild(i)));
    //                 else {
    //                     auxVars.put(con.queryChild(i), problem.createBooleanVariable()); 
    //                     args.add(auxVars.get(con.queryChild(i)));
    //                 }
    //             }
    //             auxVars.put(SmtFactory.createConjunction(args), problem.createBooleanVariable());
    //         } 
    //         else if (c instanceof Disjunction d) {
    //             ArrayList<Constraint> args = new ArrayList<>();
    //             for (int i =1; i <= d.numChildren(); i++){
    //                 if (d.queryChild(i) instanceof BVar b) args.add(b); 
    //                 else if (auxVars.containsKey(d.queryChild(i))) args.add(auxVars.get(d.queryChild(i)));
    //                 else {
    //                     auxVars.put(d.queryChild(i), problem.createBooleanVariable()); 
    //                     args.add(auxVars.get(d.queryChild(i)));
    //                 }
    //             }
    //             auxVars.put(SmtFactory.createDisjunction(args), problem.createBooleanVariable());
    //         } 
    //         else if (c instanceof Not n) {
    //             auxVars.put(n, problem.createBooleanVariable()); 
    //             if (!(n.queryChild() instanceof BVar)){
    //                 if (!(auxVars.containsKey(n.queryChild()))) auxVars.put(n.queryChild(), problem.createBooleanVariable()); 
    //             }
    //         }
    //     }

    //     else throw new Error("expression of form " + c + " not supported.");
    // }

    // public static Constraint replace (Constraint formula){
    //     //if (auxVars.containsKey(formula)) return auxVars.get(formula);
    //     switch (formula){
    //         case BVar b : return b;
    //         case Conjunction c: 
    //             ArrayList<Constraint> args = new ArrayList<>();
                
    //             for (int i =1; i <= c.numChildren(); i++){
    //                 if (c.queryChild(i) instanceof BVar b) args.add(b);
    //                 else if (auxVars.containsKey(c.queryChild(i)) ) args.add(auxVars.get(c.queryChild(i)));
    //             }
    //             return SmtFactory.createConjunction(args);
    //         case Disjunction d: 
    //             ArrayList<Constraint> args2 = new ArrayList<>();
                
    //             for (int i =1; i <= d.numChildren(); i++){
    //                 if (d.queryChild(i) instanceof BVar b) args2.add(b);
    //                 else if (auxVars.containsKey(d.queryChild(i)) ) args2.add(auxVars.get(d.queryChild(i)));
    //             }
    //             return SmtFactory.createDisjunction(args2);
    //         case Not n:
    //             if (n.queryChild() instanceof BVar) return n;
    //             else if (auxVars.containsKey(n.queryChild())) return SmtFactory.createNegation(auxVars.get(n.queryChild()));
    //         default: throw new Error ("expression of form: " + formula + " not supported.");
    //     }
    // }

    // public static boolean allChildrenAreVars (Constraint c){
    //     if (c instanceof Conjunction con){
    //         for (int i =1; i <= con.numChildren(); i++){
    //             if (!(con.queryChild(i) instanceof BVar)) return false;
    //         }
    //         return true;
    //     }
    //     else if (c instanceof Disjunction d){
    //         for (int i =1; i <= d.numChildren(); i++){
    //             if (!(d.queryChild(i) instanceof BVar)) return false;
    //         }
    //         return true;
    //     }
    //     else throw new Error ("expression of form " + c + " not supported.");
    // }

   
}