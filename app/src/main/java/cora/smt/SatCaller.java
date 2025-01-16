package cora.smt;
import java.io.*;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class SatCaller {
       public static void callMiniSat(String dimacsFilePath, String outputFilePath) {
        try {
            // Command to run MiniSat with the CNF formula file as argument and redirect output to a file
            String command = "minisat " + dimacsFilePath + " " + outputFilePath;
            
            // Start the process
            Process process = new ProcessBuilder(command.split(" ")).start();
            
            // Get the output from the process (for example, SAT/UNSAT status)
            BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
            String line;
            String cpuTime = null;  // Variable to hold the extracted CPU time
            
            // Prepare the file and writer to append CPU time
            File file = new File("timeminisat.csv");
            try (BufferedWriter writer = new BufferedWriter(new FileWriter(file, true))) {
                while ((line = reader.readLine()) != null) {
                    System.out.println(line);  // Print SAT/UNSAT status

                    // Check for the line containing CPU time
                    if (line.contains("CPU time")) {
                        cpuTime = extractCpuTime(line); // Extract CPU time
                        if (cpuTime != null) {
                            writer.write(cpuTime); // Append CPU time to the file
                            writer.newLine(); // Add a newline after each CPU time entry
                        }
                    }
                }
            } catch (IOException e) {
                System.err.println("An error occurred while writing to the file: " + e.getMessage());
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
    
    private static String extractCpuTime(String line) {
        // Updated regular expression to capture both integer and floating-point CPU time
        String regex = "CPU time\\s+:\\s+([0-9]*\\.?[0-9]+)\\s+s";
        Pattern pattern = Pattern.compile(regex);
        Matcher matcher = pattern.matcher(line);

        // If a match is found, return the CPU time formatted as requested
        if (matcher.find()) {
            String cpuTime = matcher.group(1);
            return cpuTime + ", ";  // Return the CPU time with a comma and space
        }

        return null;  // Return null if no match is found
    }



    public static void callKissat(String dimacsFilePath, String outputFilePath) {
        outputFilePath = "outputRobust.txt";
        try {
            // Log current working directory and file paths
            System.out.println("Current working directory: " + System.getProperty("user.dir"));
            System.out.println("DIMACS file: " + dimacsFilePath);
            System.out.println("Output file: " + outputFilePath);

            // Build the command as a list of arguments
            ProcessBuilder processBuilder = new ProcessBuilder("kissat", "--relaxed", dimacsFilePath);

            // Redirect output to the specified file
            processBuilder.redirectOutput(new File(outputFilePath));
            processBuilder.redirectError(ProcessBuilder.Redirect.INHERIT); // Redirect error output to console

            // Start the process
            Process process = processBuilder.start();

            // Wait for the process to finish
            int exitCode = process.waitFor();
            if (exitCode == 0) {
                System.out.println("Kissat finished successfully.");
            } else {
                System.out.println("Kissat failed with exit code: " + exitCode);
            }
            extractResultAndValuation("outputRobust.txt", "output.txt");
        } catch (IOException | InterruptedException e) {
            e.printStackTrace();
        }
        try {
            String filePath = "outputRobust.txt";
            String processTime = CnfToDimacs.extractProcessTimeKissat(filePath);
            File file = new File("timekissat.csv");
            try (BufferedWriter writer = new BufferedWriter(new FileWriter(file, true))) {
                // Append the line and a newline character
                writer.write(processTime);
            }
            catch (IOException e) {
                System.err.println("An error occurred while writing to the file: " + e.getMessage());
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public static void extractResultAndValuation(String inputFilePath, String outputFilePath) {
        try (BufferedReader reader = new BufferedReader(new FileReader(inputFilePath));
             BufferedWriter writer = new BufferedWriter(new FileWriter(outputFilePath))) {

            String line;
            boolean inResultSection = false;

            while ((line = reader.readLine()) != null) {
                // Detect the result section
                if (line.contains("[ result ]")) {
                    inResultSection = true;
                    continue; // Skip the section header line
                }

                if (inResultSection) {
                    // Extract and write the satisfiability result (after "s ")
                    if (line.startsWith("s ")) {
                        String result = line.substring(2); // Remove "s " prefix
                        writer.write(result);
                        writer.newLine();
                        continue;
                    }

                    // Write the valuation lines, removing the "v " prefix
                    if (line.startsWith("v ")) {
                        String valuation = line.substring(2); // Remove "v " prefix
                        writer.write(valuation);
                        writer.newLine();
                    }

                    // Stop after finishing the result section
                    if (line.startsWith("c ---- ")) {
                        break;
                    }
                }
            }

            System.out.println("Result and valuation extracted successfully to: " + outputFilePath);
        } catch (IOException e) {
            e.printStackTrace();
        }
    }
}