package cora.smt;

import charlie.smt.*;
import cora.smt.*;
import java.util.ArrayList;

public class ToCNF {

    public static Constraint toCNF (SmtProblem problem, Constraint formula){
        //System.out.println ("converting: " + formula);
        if (TseitinTransformationOLD.inCNF(formula)) return formula;

        //if (formula instanceof Conjunction c ) System.out.println ("length before converted nots: " + c.numChildren());
        System.out.println ("length before converted nots: " + countNumberOfObjects(formula, 0));
        formula = convertNots(formula);
        System.out.println ("length after converted nots: " + countNumberOfObjects(formula, 0));
        //if (formula instanceof Conjunction c2 ) System.out.println ("length after converted nots: " + c2.numChildren());

        // System.out.println("all nots inside:");
        // if (TseitinTransformationOLD.inCNF(formula)) return formula;
        // //if (BitBlastingFaster.test(problem, formula).isEmpty()) throw new Error ("convert not already mistake");
        // System.out.println("applying dislaw:");
        
        // formula = distributiveLaw(formula);
        // System.out.println ("length after dislaw: " + formula.toString().length());
        // if (formula instanceof Conjunction c3 ) System.out.println ("length after dislaw: " + c3.numChildren());
        // if (TseitinTransformationOLD.inCNF(formula)) return formula;
        // else throw new Error (formula + " not in cnf");
        return formula;
    }

    public static Constraint convertNots (Constraint formula){
        switch (formula){
            case BVar b : return b;
            case Not n : 
                if (n.queryChild() instanceof BVar b) return n;
                if (n.queryChild() instanceof Not n2) return convertNots(n2.queryChild());
                if (n.queryChild() instanceof Conjunction c){
                    //System.out.println ("in not case conjunction for "+c);
                    ArrayList<Constraint> children1 = new ArrayList<>();
                    for (int i =1; i <= c.numChildren(); i++){
                        children1.add(convertNots(SmtFactory.createNegation(c.queryChild(i))));
                    }
                    //System.out.println ("returning: " + SmtFactory.createDisjunction(children1));
                    return SmtFactory.createDisjunction(children1);
                }
                if (n.queryChild() instanceof Disjunction d){
                    //System.out.println ("in not case disjunction for "+d);
                    ArrayList<Constraint> children2 = new ArrayList<>();
                    for (int i =1; i <= d.numChildren(); i++){
                        children2.add(convertNots(SmtFactory.createNegation(d.queryChild(i))));
                    }
                    //System.out.println ("returning: "+ SmtFactory.createConjunction(children2));
                    return SmtFactory.createConjunction(children2);
                }
                throw new Error ("what do i return in convertnots for: " + n);
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
            default: throw new Error ("expression of form: " + formula + " not supported in convertnots");
        }
    }

    public static Constraint distributiveLaw (Constraint c){
        //System.out.println ("in dislaw for " + c);
        if (TseitinTransformationOLD.inCNF(c)) return c;
        ArrayList<Constraint> args = new ArrayList<>();
        if (c instanceof Conjunction con){
            //System.out.println ("in dislaw for conjunction " + c);
            ArrayList<Constraint> converted = new ArrayList<>();
            for (int i =1; i <= con.numChildren(); i++){
                converted.add(distributiveLaw(con.queryChild(i)));
            }
            //System.out.println ("result is " + SmtFactory.createConjunction(converted));
            return SmtFactory.createConjunction(converted);
        }
        if (c instanceof Disjunction d){
            for (int i =1; i < d.numChildren(); i+=2){
                
                Constraint firstChild = distributiveLaw(d.queryChild(i));
                Constraint secondChild = distributiveLaw(d.queryChild(i+1));
                if ((i+2) == d.numChildren()) {
                    if (d.numChildren()%2 ==0){
                        throw new Error("in here with even number of children");
                    }
                    args.add(distributiveLaw(d.queryChild(i+2)));
                }
               
                //System.out.println("first child: " + firstChild);
                //System.out.println("second child: " + secondChild);
                //System.out.println ("first child instanceof " + firstChild.getClass()+ " and second child " + secondChild.getClass());
                if (firstChild instanceof Conjunction c1 && secondChild instanceof Conjunction c2){
                    args.add(TseitinTransformationOLD.distributiveWithTwoAnds(c1,c2));
                }
                else if (firstChild instanceof Conjunction c1){
                    args.add(TseitinTransformationOLD.distributiveWithOneAnd(secondChild, c1));
                }
                else if (secondChild instanceof Conjunction c2){
                    args.add(TseitinTransformationOLD.distributiveWithOneAnd(firstChild, c2));
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
            //System.out.println ("result is " + SmtFactory.createConjunction(args).simplify());
            return SmtFactory.createConjunction(args).simplify();
        }
        throw new Error ("in dislaw for " + c);
    }


    public static int countNumberOfObjects (Constraint c, int count){
        switch (c){
            case BVar b : return count++;
            case Not n : return countNumberOfObjects (n.queryChild(), count+1);
            case Conjunction con :
                count ++;
                for (int i =1; i <= con.numChildren(); i++){
                    count =+ countNumberOfObjects (con.queryChild(i), count);
                }
                return count;
            case Disjunction d :
                count ++;
                for (int i =1; i <= d.numChildren(); i++){
                    count =+ countNumberOfObjects (d.queryChild(i), count);
                }
                return count;
            default : throw new Error (c + " not supported in countnumberofobjects");
        }
    }
}




