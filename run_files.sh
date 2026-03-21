#!/bin/bash

DIR="$1"

if [ -z "$DIR" ]; then
    echo "Usage: $0 <root-directory>"
    exit 1
fi

# Colours
RED="\e[31m"
GREEN="\e[32m"
RESET="\e[0m"

# Recursively find all .lean files
find "$DIR" -type f -name "*.lean" | while read -r file; do
    # Convert to absolute path
    fullpath="$(realpath "$file")"

    echo "Checking: $fullpath"
    time_initial=$(date +%s%N | cut -b1-13)
    # Run the command and capture stdout + stderr
    output=$(lake lean "$fullpath" 2>&1)
    time_final=$(date +%s%N | cut -b1-13)
    time_diff=$((time_final - time_initial))
    # Check for "error" in the output (case-insensitive)
    if echo "$output" | grep -qi "error"; then
        echo -e "${RED}FAILED${RESET}"
    else
        echo -e "${GREEN}SUCCESS${RESET}"
    fi
    echo "Time Taken = $time_diff"
    echo "----------------------------------------------------"
done

