
package cora.smt;
import charlie.smt.*;
import cora.smt.*;
import java.util.ArrayList;

public class TseitinTransformation{

    public ArrayList<Constraint> tseitinTransformation (ArrayList<Constraint> args){
        if (inCNF(args)) return args;
        System.out.println ("not in cnf");
        ArrayList<Constraint> subFormulas = new ArrayList<>();
        for (Constraint arg : args){
            
            subFormulas.addAll(returnSubFormulas(arg));
        }
        System.out.println ("subformulas: " + subFormulas);
        ArrayList<Constraint> implications = makeImplications(subFormulas);
        
        return subFormulas;
    }

    public ArrayList<Constraint> makeImplications (ArrayList<Constraint> subformulas){
        ArrayList<BVar> auxVariables = new ArrayList<>();
        ArrayList<Constraint> implications = new ArrayList<>();
        for (Constraint c : subFormulas){
            BVar newVar = SmtFactory.createBooleanVariable();
            auxVariables.add(newVar);
            implications.add(SmtFactory.createImplication(newVar, c));
            
            if (c instanceof Conjunction || c instanceof Disjunction){
                Constraint converted = deMorgan (SmtFactory.createNegation(c));
                if (inCNF(SmtFactory.createDisjunction(converted, newVar))){
                    implications.add(SmtFactory.createDisjunction(converted, newVar));

                }
                else //try distributive law
            }
            else implications.add(SmtFactory.createImplication(c, newVar));
        }
        

    }

    public Constraint deMorgan (Constraint c){
        if (c instanceof Not n){
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
                for (int i =1; i <= con.numChildren(); i++){
                    args.add(SmtFactory.createNegation(con.queryChild(i)).simplify());
                }
                return SmtFactory.createConjunction(args);
            }
            else throw new Error("cannot apply demorgan laws on " + n);
        }
        else throw new Error("cannot apply demorgan laws on " + c);

    }


    public boolean inCNF (ArrayList<Constraint> args){
        for (Constraint arg : args){
            if (!inCNF(arg)) return false;
        }
        return true;
    }

    public boolean inCNF (Constraint arg){
        switch (arg){
            case BVar b : return true;
            case NBVar b : return true;
            case Not n: return false;
            case Conjunction c : 
                for (int i =1; i <= c.numChildren(); i++){
                    if (c.queryChild(i) instanceof Conjunction || !inCNF(c.queryChild(i))) return false;
                }
                return true;
            case Disjunction d: 
                for (int i =1; i <= d.numChildren(); i++){
                    if (!(d.queryChild(i) instanceof BVar || d.queryChild(i) instanceof NBVar)){
                        return false;
                    }
                }
                return true;
            
            default throw new Error(arg + " not supported in inCNF");
        }
    }

    


    public ArrayList<Constraint> returnSubFormulas (Constraint c){
        ArrayList<Constraint> subFormulas = new ArrayList<>();
        switch (c){
            case BVar b : return new ArrayList<>();
            case Falsehood f: return new ArrayList<>();
            case Truth t : return new ArrayList<>();
            case Conjunction con: 
                subFormulas.add(con);
                for (int i = 1; i <= con.numChildren(); i++){
                    subFormulas.addAll(returnSubFormulas(con.queryChild(i)));
                }
                return subFormulas;
            case Disjunction d: 
                subFormulas.add(d);
                for (int i = 1; i <= d.numChildren(); i++){
                    subFormulas.addAll(returnSubFormulas(d.queryChild(i)));
                }
                return subFormulas;
            case Not n:
                subFormulas.add(n);
                subFormulas.addAll(returnSubFormulas(n.queryChild()));
                return subFormulas;
            case Iff i:
                subFormulas.add(i);
                subFormulas.addAll(returnSubFormulas(i.queryLeft()));
                subFormulas.addAll(returnSubFormulas(i.queryRight()));
                return subFormulas;
            default: throw new Error (c + " not supported yet.");

        }
    }



}