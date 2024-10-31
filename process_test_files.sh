#!/bin/bash

# Directory containing the files
FOLDER_PATH="linear_inequalities_files"  # Replace with your actual folder path

# The script or program you want to run on each file
PROGRAM="./run.sh"  # Replace with the name of the script/program to run

# Check if the folder exists
if [ ! -d "$FOLDER_PATH" ]; then
  echo "Directory $FOLDER_PATH does not exist."
  exit 1
fi

# Iterate over each file in the folder
for file in "$FOLDER_PATH"/*; do
  # Check if it is a file
  if [ -f "$file" ]; then
    echo "Processing file: $file"
    
    # Run the program in the required format
    $PROGRAM "$file"
    
    # Check if the program ran successfully
    if [ $? -ne 0 ]; then
      echo "Error processing: $file. Stopping execution."
      exit 1  # Stop the script on error
    else
      echo "Successfully processed: $file"
    fi
  fi
done

echo "All files processed successfully."
