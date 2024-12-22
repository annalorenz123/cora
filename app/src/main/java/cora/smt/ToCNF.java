package cora.smt;

import charlie.smt.*;
import cora.smt.*;
import java.util.ArrayList;

public class ToCNF {

    public static Constraint toCNF (SmtProblem problem, Constraint formula){
        //System.out.println ("converting: " + formula);
        if (TseitinTransformationOLD.inCNF(formula)) return formula;

        //if (formula instanceof Conjunction c ) System.out.println ("length before converted nots: " + c.numChildren());
        //System.out.println ("length before converted nots: " + countNumberOfObjects(formula, 0));
        formula = convertNotstToCnf(problem, formula);
        //System.out.println ("converted nots: " + formula);
        //BitBlasting b = new BitBlasting();
        //if (b.test(problem, formula).isEmpty()) System.out.println ("unsat after convertnots");
        //System.out.println ("length after converted nots: " + countNumberOfObjects(formula, 0));
        //if (formula instanceof Conjunction c2 ) System.out.println ("length after converted nots: " + c2.numChildren());

        // System.out.println("all nots inside:");
        if (TseitinTransformationOLD.inCNF(formula)) return formula;
        // //if (BitBlastingFaster.test(problem, formula).isEmpty()) throw new Error ("convert not already mistake");
        // System.out.println("applying dislaw:");
        formula = dislawtocnf(formula);
        //formula = distributiveLaw(problem, formula);
        //if (b.test(problem, formula).isEmpty()) System.out.println ("unsat after dislaw");
        // System.out.println ("length after dislaw: " + formula.toString().length());
        // if (formula instanceof Conjunction c3 ) System.out.println ("length after dislaw: " + c3.numChildren());
        if (TseitinTransformationOLD.inCNF(formula)) return formula;
        else throw new Error (formula + " not in cnf");
        //return formula;
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

    // public static Constraint distributiveLaw (SmtProblem problem, Constraint c){
    //     BitBlasting b = new BitBlasting();
    //     if (c instanceof BVar) return c;
    //     if (TseitinTransformationOLD.inCNF(c)) return c.simplify();
        
    //     if (c instanceof Conjunction con){
            
    //         ArrayList<Constraint> converted = new ArrayList<>();
    //         for (int i =1; i <= con.numChildren(); i++){
    //             converted.add(distributiveLaw(problem, con.queryChild(i).simplify()).simplify());
    //         }
    //         System.out.println ("in dislaw for conjunction " + c);
    //         System.out.println ("result is " + SmtFactory.createConjunction(converted).simplify());
    //         if (b.test(problem, c).size() != b.test(problem, SmtFactory.createConjunction(converted).simplify()).size()){
    //             throw new Error(" and case it goes wrong for " + c + " AND " + SmtFactory.createConjunction(converted).simplify());

    //         }
    //         return SmtFactory.createConjunction(converted).simplify();
    //     }
    //     if (c instanceof Disjunction d){
    //         ArrayList<Constraint> args = new ArrayList<>();
    //         System.out.println ("in dis case dislaw for " + d + " num children: " + d.numChildren());
    //         for (int i =1; i < d.numChildren(); i+=2){
                
    //             Constraint firstChild = distributiveLaw(problem, d.queryChild(i).simplify()).simplify();
    //             if (!(d.queryChild(i).equals(firstChild))){
    //                 System.out.println ("converted lol " + d.queryChild(i) + " to " + firstChild);
    //             }
                
    //             Constraint secondChild = distributiveLaw(problem, d.queryChild(i+1).simplify()).simplify();
    //             if (!(d.queryChild(i+1).equals(secondChild))){
    //                 System.out.println ("converted lol " + d.queryChild(i+1).simplify() + " to " + secondChild.simplify());
    //             }
               
    //             System.out.println("first child: " + firstChild);
    //             System.out.println("second child: " + secondChild);
    //             //System.out.println ("first child instanceof " + firstChild.getClass()+ " and second child " + secondChild.getClass());
    //             if (firstChild instanceof Conjunction c1 && secondChild instanceof Conjunction c2){
    //                 args.add(TseitinTransformationOLD.distributiveWithTwoAnds(c1,c2).simplify());
    //             }
    //             else if (firstChild instanceof Conjunction c1){
    //                 args.add(TseitinTransformationOLD.distributiveWithOneAnd(secondChild, c1).simplify());
    //             }
    //             else if (secondChild instanceof Conjunction c2){
    //                 args.add(TseitinTransformationOLD.distributiveWithOneAnd(firstChild, c2).simplify());
    //                 //System.out.println ("converted " + )
    //             }
    //             else if (firstChild instanceof BVar b1){
    //                 args.add(b1);
    //                 if (secondChild instanceof BVar || secondChild instanceof Not){
    //                     args.add(secondChild);
    //                 }
    //             }
    //             // if (secondChild instanceof BVar b2){
    //             //     args.add(b2);
    //             // }
    //             else if (firstChild instanceof Not n1){
    //                 args.add(n1);
    //                 if (secondChild instanceof BVar || secondChild instanceof Not){
    //                     args.add(secondChild);
    //                 }
    //             }
    //             // if (secondChild instanceof Not n2){
    //             //     args.add(n2);
    //             // }
    //             System.out.println (args.get(args.size()-1));
    //             // if (b.test(problem, args.get(args.size()-1)).size() != b.test(problem, SmtFactory.createDisjunction(firstChild, secondChild)).size()){
    //             //     throw new Error ("dis case it goes wrong for " + args.get(args.size()-1) + " AND " + SmtFactory.createDisjunction(args).simplify());
    //             // }
    //             if ((i+2) == d.numChildren()) {
    //                 if (d.numChildren()%2 ==0){
    //                     throw new Error("in here with even number of children");
    //                 }
    //                 if (args.size()==1){
    //                     return distributiveLaw(problem, SmtFactory.createDisjunction(args.get(args.size()-1), d.queryChild(i+2)));
    //                 }
    //                 else return distributiveLaw (problem, SmtFactory.createDisjunction(SmtFactory.createConjunction(args), d.queryChild(i+2)));
    //                 //i--;
    //                 // Constraint thirdchild = distributiveLaw(problem, d.queryChild(i+2).simplify()).simplify();
    //                 // return addThirdChild(thirdchild, SmtFactory.createConjunction(args));
    //             }
    //         }
            
    //         if (b.test(problem, d).size() != b.test(problem, SmtFactory.createConjunction(args).simplify()).size()){
    //             throw new Error("dis case it goes wrong for " + d + " with class " + d.getClass() + "AND " + SmtFactory.createConjunction(args).simplify());

    //         }
    //         System.out.println ("in dislaw for " + c);
    //         System.out.println ("result is " + SmtFactory.createConjunction(args).simplify());
    //         return SmtFactory.createConjunction(args).simplify();
    //     }
    //     throw new Error ("in dislaw for " + c);
    // }

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
                    args.add(distributiveLaw( d.queryChild(i+2)));
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
            return SmtFactory.createConjunction(args);
        }
        throw new Error ("in dislaw for " + c);
    }

    // public static Constraint addThirdChild (Constraint thirdchild, Conjunction conjunction){
    //     if (TseitinTransformation.onlyVariables(conjunction)) {
    //         conjunction.addChild(thirdchild);
    //         return conjunction;
    //     }
    //     ArrayList<Constraint> children = conjunction.queryChildren();
    //     ArrayList<Constraint> newargs = new ArrayList<>();
    //     for (int i =1; i <= conjunction.numChildren(); i++){
    //         if (conjunction.queryChild(i) instanceof Disjunction d){
    //             d.addChild(thirdchild);
    //         }
    //         else if (conjunction.queryChild(i) instanceof Conjunction c){
    //             newargs.add(TseitinTransformationOLD.distributiveWithOneAnd(thirdchild, c));
    //         }
    //     }
    //                 for (Constraint child : args){
    //                     while (child instanceof Conjunction || child instanceof Disjunction){
    //                         if (TseitinTransformation.onlyVariables(child)) {
    //                             if (child instanceof Conjunction c1){
    //                                 c1.addChild(thirdchild);
    //                             }
    //                             else if (child instanceof Disjunction d1){
    //                                 d1.addChild(thirdchild);
    //                             }
    //                         }
    //                         else {
    //                             c1 = child;
    //                         }
    //                     }
    //                     if (child instanceof Disjunction d1){
    //                         System.out.println ("in here for adding: " + thirdchild + " to " + d1);
    //                         d1.addChild(thirdchild);
    //                     }
    //                 }    
    //                 if (TseitinTransformation.onlyVariables(SmtFactory.createConjunction(args))) args.add(thirdchild);
    // }


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
            default : throw new Error (c + " not supported in countnumberofobjects");
        }
        //System.out.println ("count for " + c + " is " + count);
        return count;
    }
  
    public static Constraint dislawtocnf(Constraint formula) {
        if (formula instanceof BVar || formula instanceof Not) {
            // Base case: already in CNF
            return formula;
        } else if (formula instanceof Conjunction and ) {
            // CNF: (A ∧ B) is already in CNF
            ArrayList<Constraint> newargs = new ArrayList<>();
            for (int i =1; i <= and.numChildren(); i++){
                newargs.add(dislawtocnf(and.queryChild(i)));
            }
            return SmtFactory.createConjunction(newargs);
        } else if (formula instanceof Disjunction or) {
            // Apply distributive law: (A ∨ (B ∧ C)) -> ((A ∨ B) ∧ (A ∨ C))
            ArrayList<Constraint> orargs = new ArrayList<>();
            for (int i =1; i <= or.numChildren(); i++){
                orargs.add(dislawtocnf(or.queryChild(i)));
            }
            ArrayList<Constraint> andArgs = new ArrayList<>();
            for (Constraint arg : orargs){
                if (arg instanceof Conjunction c){
                    andArgs = c.queryChildren();
                    break;
                }
            }
            if (!andArgs.isEmpty()){
                ArrayList<Constraint> distributed = new ArrayList<>();
                // Distribute OR over AND
                for (Constraint andOperand : andArgs) {
                    ArrayList<Constraint> newOrOperands = new ArrayList<>();
                    for (Constraint cnfOperand : orargs) {
                        if (cnfOperand instanceof Conjunction) { // Check if this is the AND being distributed
                            newOrOperands.add(andOperand); // Replace the AND with its operand
                        } else {
                            newOrOperands.add(cnfOperand); // Add other operands unchanged
                        }
                    }
                    distributed.add(dislawtocnf(SmtFactory.createDisjunction(newOrOperands))); // Recursively convert to CNF
                }
                return SmtFactory.createConjunction(distributed);
            }

            // Return the OR if no AND was found
            return SmtFactory.createDisjunction(orargs);
        }

        throw new Error ("Unsupported formula type: " + formula);
    }

    public static Constraint convertNotstToCnf (SmtProblem problem, Constraint formula){
        BitBlasting b1 = new BitBlasting();
        switch (formula){
            case BVar b : return b;
            case Not n : 
                if (n.queryChild() instanceof BVar b) return n;
                if (n.queryChild() instanceof Not n2) {
                    Constraint result = convertNotstToCnf(problem, n2.queryChild());
                    if (b1.test(problem, result).size() != b1.test(problem, n).size()){
                        throw new Error (result + " not equivalent to " + n);
                    }
                    return result;
                }
                if (n.queryChild() instanceof Conjunction c){
                    //System.out.println ("in not case conjunction for "+c);
                    ArrayList<Constraint> children1 = new ArrayList<>();
                    for (int i =1; i <= c.numChildren(); i++){
                        children1.add(convertNotstToCnf(problem, SmtFactory.createNegation(c.queryChild(i))));
                    }
                    if (b1.test(problem, SmtFactory.createDisjunction(children1)).size() != b1.test(problem, n).size()){
                        throw new Error (SmtFactory.createDisjunction(children1) + " not equivalent to " + n);
                    }
                    //System.out.println ("returning: " + SmtFactory.createDisjunction(children1));
                    return SmtFactory.createDisjunction(children1);
                }
                if (n.queryChild() instanceof Disjunction d){
                    //System.out.println ("in not case disjunction for "+d);
                    ArrayList<Constraint> children2 = new ArrayList<>();
                    for (int i =1; i <= d.numChildren(); i++){
                        children2.add(convertNotstToCnf(problem,SmtFactory.createNegation(d.queryChild(i))));
                    }
                    if (b1.test(problem, SmtFactory.createConjunction(children2)).size() != b1.test(problem, n).size()){
                        throw new Error (SmtFactory.createConjunction(children2) + " not equivalent to " + n);
                    }
                    //System.out.println ("returning: "+ SmtFactory.createConjunction(children2));
                    return SmtFactory.createConjunction(children2);
                }
                throw new Error ("what do i return in convertnots for: " + n);
            case Conjunction c: 
                ArrayList<Constraint> convertedChildren1 = new ArrayList<>();
                for (int i =1; i <= c.numChildren(); i++) {
                    convertedChildren1.add(convertNotstToCnf(problem, c.queryChild(i)));
                }
                if (b1.test(problem, SmtFactory.createConjunction(convertedChildren1)).size() != b1.test(problem, c).size()){
                        throw new Error (SmtFactory.createConjunction(convertedChildren1) + " not equivalent to " + c);
                }
                return SmtFactory.createConjunction(convertedChildren1);
            case Disjunction d: 
                ArrayList<Constraint> convertedChildren2 = new ArrayList<>();
                for (int i =1; i <= d.numChildren(); i++) {
                    convertedChildren2.add(convertNotstToCnf(problem, d.queryChild(i)));
                }
                if (b1.test(problem, SmtFactory.createDisjunction(convertedChildren2)).size() != b1.test(problem, d).size()){
                    throw new Error (SmtFactory.createDisjunction(convertedChildren2) + " not equivalent to " + d);
                }
                return SmtFactory.createDisjunction(convertedChildren2);
            default: throw new Error ("expression of form: " + formula + " not supported in convertnots");
        }
    }
}




