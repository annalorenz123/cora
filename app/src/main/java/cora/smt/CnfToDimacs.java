package cora.smt;
import charlie.smt.*;
import cora.smt.*;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;
import java.util.regex.*;

public class CnfToDimacs {

    // Method to convert a formula string to DIMACS format
    public static void convertToDimacs(Constraint formula, int numVariables, String filename) throws IOException {
        // List to store clauses, where each clause is a list of integers (literals)
        List<List<Integer>> clauses = new ArrayList<>();

        // Split the formula into clauses based on "and" (ignoring case)
        String[] rawClauses = formula.toString().split("and");

        // Parse each clause
        for (String rawClause : rawClauses) {
            // Clean the clause (trim spaces and remove unnecessary parentheses)
            String cleanedClause = rawClause.trim().replaceAll("[()]", "");

            // List to store literals for this clause
            List<Integer> clause = new ArrayList<>();

            // Find all variables and their negations in the clause
            Matcher matcher = Pattern.compile("not\\s*(b\\d+)|b\\d+").matcher(cleanedClause);
            while (matcher.find()) {
                String var = matcher.group();
                if (var.startsWith("not")) {
                    // Negation: Add as negative integer (e.g., "not b11" -> -11)
                    clause.add(-getVariableIndex(var.substring(4).trim()));
                } else {
                    if (var.equals("false") || var.equals("true")) throw new Error ("false seen as variable");
                    // Regular variable: Add as positive integer (e.g., "b11" -> 11)
                    clause.add(getVariableIndex(var.trim()));
                }
            }

            // Add the clause to the list of clauses
            clauses.add(clause);
        }

        // Write the CNF in DIMACS format to the file
        try (FileWriter writer = new FileWriter(filename)) {
            // Write the problem line
            writer.write("p cnf " + numVariables + " " + clauses.size() + "\n");

            // Write each clause
            for (List<Integer> clause : clauses) {
                for (Integer literal : clause) {
                    writer.write(literal + " ");
                }
                writer.write("0\n");
            }
        }

        System.out.println("Conversion to DIMACS format completed successfully.");
    }

    // Helper method to map variables like b1, b11, b92 to their integer indices
    private static int getVariableIndex(String varName) {
        // Extract the number from the variable name (e.g., "b11" -> 11)
        return Integer.parseInt(varName.substring(1));
    }

    // public static void main(String[] args) {
    //     // Example formula input (as a string)
    //     String formula = "((not b11) or b12) and ((not b11) or b92) and ((not b12) or (not b92) or b11)";
    //     // Example: There are 92 variables in the formula, so pass 92 as the number of variables
    //     int numVariables = 92;

    //     try {
    //         // Convert the formula to DIMACS format and write to a file
    //         convertToDimacs(formula, numVariables, "output.dimacs");
    //     } catch (IOException e) {
    //         e.printStackTrace();
    //     }
    // }

    // public static void convertToDimacs(Constraint formula, int numVariables, String filename) throws IOException {
    //     // List to store clauses, where each clause is a list of integers (literals)
    //     List<List<Integer>> clausesstring = new ArrayList<>();
    //     ArrayList<Constraint> clauses = new ArrayList<>();

    //     // Split the formula into clauses based on "and" (ignoring case)
    //     //String[] rawClauses = ((Conjunction)formula).query;
    //     if (formula instanceof Conjunction c){
    //         clauses.addAll(c.queryChildren());
    //     }
    //     else if (formula instanceof Disjunction d){
    //         clauses.add(d);
    //     }
    //     else throw new Error ("implement this in cnftodimancs");
    //     // Parse each clause
    //     for (Constraint rawClause : clauses) {
    //         // Clean the clause (trim spaces and remove unnecessary parentheses)
    //         //String cleanedClause = rawClause.trim().replaceAll("[()]", "");

    //         // List to store literals for this clause
    //         List<Integer> clausestring = new ArrayList<>();
    //         ArrayList<Constraint> clause = new ArrayList<>();
    //         if (rawClause instanceof Disjunction d){
    //             clause.addAll(d.queryChildren());
    //         }
    //         else if (rawClause instanceof Not n){
    //             clause.add(n);
    //         }
    //         else if (rawClause instanceof BVar b){
    //             clause.add(b);
    //         }
    //         for (Constraint c : clause){
    //             if (c instanceof Not n){
    //                 BVar var = (BVar) n.queryChild();
    //                 clausestring.add(-var.queryIndex());
    //             }
    //             else{
    //                 BVar var = (BVar) c;
    //                 clausestring.add(var.queryIndex());
    //             }
    //         }
    //         clausesstring.add(clausestring);
    //         // Find all variables and their negations in the clause
    //         // Add the clause to the list of clauses
    //     }

    //     // Write the CNF in DIMACS format to the file
    //     try (FileWriter writer = new FileWriter(filename)) {
    //         // Write the problem line
    //         writer.write("p cnf " + numVariables + " " + clauses.size() + "\n");

    //         // Write each clause
    //         for (List<Integer> clausestring : clausesstring) {
    //             for (Integer literal : clausestring) {
    //                 writer.write(literal + " ");
    //             }
    //             writer.write("0\n");
    //         }
    //     }

    //     System.out.println("Conversion to DIMACS format completed successfully.");
    // }

    // // Helper method to map variables like b1, b11, b92 to their integer indices
    // private static int getVariableIndex(String varName) {
    //     // Extract the number from the variable name (e.g., "b11" -> 11)
    //     return Integer.parseInt(varName.substring(1));
    // }
}
