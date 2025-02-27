package cora.smt;

import charlie.smt.*;
import cora.smt.*;
import java.util.ArrayList;

public class ToCNF {

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

    public static Constraint convertNots (Constraint formula){
        switch (formula){
            case BVar b : return b;
            case Not n : 
                if (n.queryChild() instanceof BVar b) return n;
                if (n.queryChild() instanceof Not n2) return convertNots(n2.queryChild());
                if (n.queryChild() instanceof Conjunction c){
                    ArrayList<Constraint> children1 = new ArrayList<>();
                    for (int i =1; i <= c.numChildren(); i++){
                        children1.add(convertNots(SmtFactory.createNegation(c.queryChild(i))));
                    }
                    return SmtFactory.createDisjunction(children1);
                }
                if (n.queryChild() instanceof Disjunction d){
                    ArrayList<Constraint> children2 = new ArrayList<>();
                    for (int i =1; i <= d.numChildren(); i++){
                        children2.add(convertNots(SmtFactory.createNegation(d.queryChild(i))));
                    }
                    return SmtFactory.createConjunction(children2);
                }
                throw new Error ("Expression of form: " + n + " not supported.");
            case Conjunction c: 
                ArrayList<Constraint> convertedChildren1 = new ArrayList<>();
                for (int i =1; i <= c.numChildren(); i++) {
                    convertedChildren1.add(convertNots(c.queryChild(i)));
                }
                return SmtFactory.createConjunction(convertedChildren1);
            case Disjunction d: 
                ArrayList<Constraint> convertedChildren2 = new ArrayList<>();
                for (int i =1; i <= d.numChildren(); i++) {
                    convertedChildren2.add(convertNots(d.queryChild(i)));
                }
                return SmtFactory.createDisjunction(convertedChildren2);
            default: throw new Error ("Expression of form: " + formula + " not supported.");
        }
    }

    public static Constraint distributiveLaw (Constraint c){
        if (inCNF(c)) return c;
        ArrayList<Constraint> args = new ArrayList<>();
        if (c instanceof Conjunction con){
            ArrayList<Constraint> converted = new ArrayList<>();
            for (int i =1; i <= con.numChildren(); i++){
                converted.add(distributiveLaw(con.queryChild(i)));
            }
            return SmtFactory.createConjunction(converted);
        }
        if (c instanceof Disjunction d){
            for (int i =1; i < d.numChildren(); i+=2){
                
                Constraint firstChild = distributiveLaw(d.queryChild(i));
                Constraint secondChild = distributiveLaw(d.queryChild(i+1));
                if ((i+2) == d.numChildren()) {
                    args.add(distributiveLaw( d.queryChild(i+2)));
                }
                if (firstChild instanceof Conjunction c1 && secondChild instanceof Conjunction c2){
                    args.add(distributiveWithTwoAnds(c1,c2));
                }
                else if (firstChild instanceof Conjunction c1){
                    args.add(distributiveWithOneAnd(secondChild, c1));
                }
                else if (secondChild instanceof Conjunction c2){
                    args.add(distributiveWithOneAnd(firstChild, c2));
                }
                else if (firstChild instanceof BVar b1){
                    args.add(b1);
                }
                else if (secondChild instanceof BVar b2){
                    args.add(b2);
                }
                else if (firstChild instanceof Not n1){
                    args.add(n1);
                }
                else if (secondChild instanceof Not n2){
                    args.add(n2);
                }
            }
            return SmtFactory.createConjunction(args);
        }
        throw new Error ("In distributive law for " + c);
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

    public static int countNumberOfObjects (Constraint c, int count){
        switch (c){
            case BVar b : count++; break;
            case Not n : 
                if (n.queryChild() instanceof BVar){
                    count ++; 
                    break;
                } 
                else {
                    count ++; 
                    count += countNumberOfObjects (n.queryChild(),0); break;
                }
            case Conjunction con :
                count ++;
                for (int i =1; i <= con.numChildren(); i++){
                    count += countNumberOfObjects (con.queryChild(i), 0);
                }
                break;
            case Disjunction d :
                count ++;
                for (int i =1; i <= d.numChildren(); i++){
                    count += countNumberOfObjects (d.queryChild(i), 0);
                }
                break;
            default : throw new Error (c + " not supported.");
        }
        return count;
    }

}




