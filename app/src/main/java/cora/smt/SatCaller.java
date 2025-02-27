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

    public static String getFifthToLastLine(String filePath) throws IOException {
        try (BufferedReader reader = new BufferedReader(new FileReader(filePath))) {
            String line = null;
            int lineCount = 0;

            // First pass: Count the total number of lines
            while (reader.readLine() != null) {
                lineCount++;
            }

            // Second pass: Skip (lineCount - 5) lines and read the 5th-to-last line
            reader.close();
            try (BufferedReader reader2 = new BufferedReader(new FileReader(filePath))) {
                for (int i = 0; i < lineCount - 5; i++) {
                    reader2.readLine();
                }
                return extractNumber(reader2.readLine()); // Return the 5th-to-last line
            }
        }

    }
    private static String extractNumber(String line) {
        // Regular expression to match the number in the format we want (e.g., 0.52)
        Pattern pattern = Pattern.compile("\\s([0-9]+\\.[0-9]+)\\s");
        Matcher matcher = pattern.matcher(line);

        if (matcher.find()) {
            return matcher.group(1); // Return the matched number
        }
        return null; // Return null if no number is found
    }
}