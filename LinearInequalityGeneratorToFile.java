import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Random;

public class LinearInequalityGeneratorToFile {

    public static void main(String[] args) {
        // Set the ranges for the number of variables and inequalities
        int minVariables = 5;
        int maxVariables = 5;
        int minInequalities = 5;
        int maxInequalities = 5;

        // Define the range for coefficients and right-hand side values
        int minValue = -50;
        int maxValue = 50;

        // Number of files to generate
        int numFiles = 50;
        String folderName = "testing/exactly5var5inequal50coeff";

        // Create the folder if it does not exist
        File folder = new File(folderName);
        if (!folder.exists()) {
            folder.mkdir();
            System.out.println("Created folder: " + folderName);
        }

        // Create a random object for generating random numbers
        Random random = new Random();

        // Generate multiple files with inequalities
        for (int fileIndex = 1; fileIndex <= numFiles; fileIndex++) {
            // Define the file name for the output file
            String fileName = folderName + "/linear_inequalities_" + fileIndex + ".smt";

            // Randomly determine the number of variables and inequalities
            int numVariables = random.nextInt(maxVariables - minVariables + 1) + minVariables;
            int numInequalities = random.nextInt(maxInequalities - minInequalities + 1) + minInequalities;

            try (FileWriter writer = new FileWriter(fileName)) {
                StringBuilder inequalities = new StringBuilder();

                // Generate inequalities
                for (int i = 0; i < numInequalities; i++) {
                    StringBuilder inequality = new StringBuilder();

                    // Create the left-hand side of the inequality
                    for (int j = 1; j <= numVariables; j++) {
                        int coefficient = random.nextInt(maxValue - minValue + 1) + minValue; // Random integer coefficient between -1000 and 1000
                        while (coefficient ==0) coefficient = random.nextInt(maxValue - minValue + 1) + minValue;
                        inequality.append(coefficient).append("*x").append(j);
                        if (j < numVariables) {
                            inequality.append(" + ");
                        }
                    }

                    // Determine the inequality sign and add a random right-hand side value
                    String sign = random.nextBoolean() ? ">=" : "<=";
                    
                    int rhs = random.nextInt(maxValue - minValue + 1) + minValue; // Random integer for the right-hand side between -1000 and 1000
                    // Append the sign and rhs to the inequality
                    inequality.append(" ").append(sign).append(" ").append(rhs);

                    // Append the inequality to the set of inequalities
                    inequalities.append(inequality.toString());

                    // Add /\ if this is not the last inequality
                    if (i < numInequalities - 1) {
                        inequalities.append(" /\\ ");
                    }
                }
                
                // Write the generated inequalities to the file
                writer.write(inequalities.toString());
                System.out.println("Inequalities written to file: " + fileName);

            } catch (IOException e) {
                System.err.println("Error writing to file: " + e.getMessage());
            }
        }

        System.out.println("All files generated successfully in the folder: " + folderName);
    }
}
