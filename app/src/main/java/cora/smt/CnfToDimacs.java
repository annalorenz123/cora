package cora.smt;
import charlie.smt.*;
import cora.smt.*;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;
import java.util.regex.*;
import java.io.BufferedReader;
import java.io.FileReader;
import java.io.BufferedWriter;


public class CnfToDimacs {

    // Helper method to map variables like b1, b11, b92 to their integer indices
    private static int getVariableIndex(String varName) {
        // Extract the number from the variable name (e.g., "b11" -> 11)
        return Integer.parseInt(varName.substring(1));
    }

   
    public static void convertToDimacs(Constraint formula, int numVariables, String filename) throws IOException {
        StringBuilder content = new StringBuilder();
        int clauseCount = 0;

        // Determine the type of the formula and write clauses directly
        if (formula instanceof Conjunction c) {
            for (Constraint rawClause : c.queryChildren()) {
                processClause(content, rawClause);
                clauseCount++;
            }
        } else if (formula instanceof Disjunction d) {
            processClause(content, d);
            clauseCount++;
        } else {
            throw new Error("Formula must be in CNF to convert to DIMACS.");
        }

        // Write the DIMACS content to the file
        try (BufferedWriter writer = new BufferedWriter(new FileWriter(filename))) {
            // Write the problem line at the beginning
            writer.write("p cnf " + numVariables + " " + clauseCount);
            writer.newLine();
            
            // Write the clauses
            writer.write("-1 0");
            writer.newLine();
            writer.write("2 0");
            writer.newLine();
            
            // Write the rest of the clauses from content
            writer.write(content.toString());
        } catch (IOException e) {
            System.err.println("An error occurred while writing to the file: " + e.getMessage());
        }


        System.out.println("Conversion to DIMACS format completed successfully.");
    }

    private static void processClause(StringBuilder builder, Constraint clause) {
        if (clause instanceof Disjunction d) {
            for (Constraint literal : d.queryChildren()) {
                appendLiteral(builder, literal);
            }
        } else {
            appendLiteral(builder, clause);
        }
        builder.append("0\n"); // End of clause
    }

    private static void appendLiteral(StringBuilder builder, Constraint literal) {
        if (literal instanceof Not n) {
            BVar var = (BVar) n.queryChild();
            builder.append(-var.queryIndex()).append(" "); // Negative literal
        } else if (literal instanceof BVar b) {
            builder.append(b.queryIndex()).append(" "); // Positive literal
        } else {
            throw new Error("Unexpected literal type: " + literal.getClass().getName());
        }
    }

    public static String extractProcessTimeKissat(String filePath) throws IOException {
        String processTime = null;
        BufferedReader reader = null;

        try {
            // Open the file reader
            reader = new BufferedReader(new FileReader(filePath));
            String line;
            while ((line = reader.readLine()) != null) {
                // Check if the line contains "process-time"
                if (line.trim().startsWith("c process-time:")) {
                    // Extract the value after the colon
                    String[] parts = line.split(":");
                    if (parts.length > 1) {
                        processTime = parts[1].trim().replace("seconds", "").trim() + ", ";
                        break;
                    }
                }
            }
        } finally {
            if (reader != null) {
                reader.close();
            }
        }

        if (processTime == null) {
            throw new IOException("Process time not found in the file.");
        }

        return processTime;
    }

} 

