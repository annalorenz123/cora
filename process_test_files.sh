#!/bin/bash

# Directory containing the files
FOLDER_PATH="testing/bitblasting_moresimple"  # Replace with your actual folder path

# The script or program you want to run on each file
PROGRAM="./run.sh"  # Replace with the name of the script/program to run

# Check if the folder exists
if [ ! -d "$FOLDER_PATH" ]; then
  echo "Directory $FOLDER_PATH does not exist."
  exit 1
fi

# Specify the file path where execution time will be written
file="executionTimesBitBlasting.txt"

# Specify the directory where you want to save the file (adjust this as needed)
directory_path="app"
mkdir -p "$directory_path"  # This will create the directory if it doesn't exist

# Full path to the file
full_file_path="$directory_path/$file"

# Check if the file exists, if not, create it
if [ ! -f "$full_file_path" ]; then
    touch "$full_file_path"
fi

# Iterate over each file in the folder
for file in "$FOLDER_PATH"/*; do
  # Check if it is a file
  if [ -f "$file" ]; then
    echo "Processing file: $file"
    #echo "$file" >> "$full_file_path"
    
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
