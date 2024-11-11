package cora.smt;
import java.io.*;

public class MiniSatCaller {
    public static void callMiniSat(String dimacsFilePath, String outputFilePath) {
        try {
            // Command to run MiniSat with the CNF formula file as argument and redirect output to a file
            String command = "minisat " + dimacsFilePath + " " + outputFilePath;
            
            // Start the process
            Process process = new ProcessBuilder(command.split(" ")).start();
            
            // Get the output from the process (for example, SAT/UNSAT status)
            BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
            String line;
            while ((line = reader.readLine()) != null) {
                System.out.println(line);  // Print SAT/UNSAT status
            }
            
            // Wait for the process to finish and capture the exit code
            int exitCode = process.waitFor();
            if (exitCode == 0) {
                System.out.println("MiniSat finished successfully.");
            } else {
                System.out.println("MiniSat failed with exit code: " + exitCode);
            }
        } catch (IOException | InterruptedException e) {
            e.printStackTrace();
        }
    }


    public static void main(String[] args) {
        // Example usage: Replace "formula.cnf" with the path to your CNF file
        // and specify an output file like "minisat_output.txt"
        callMiniSat("formula.cnf", "minisat_output.txt");
    }
}
