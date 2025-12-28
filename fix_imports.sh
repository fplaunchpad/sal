#!/bin/bash

# Script to fix imports in Lean files within a subdirectory
# Usage: ./fix_imports.sh <directory>
# Example: ./fix_imports.sh CaseStudies/Pramaana/SaraStatutesV3/cases

if [ -z "$1" ]; then
    echo "Usage: $0 <directory>"
    echo "Example: $0 CaseStudies/Pramaana/SaraStatutesV3/cases"
    exit 1
fi

TARGET_DIR="$1"

if [ ! -d "$TARGET_DIR" ]; then
    echo "Error: Directory '$TARGET_DIR' does not exist"
    exit 1
fi

# Find all .lean files in the target directory
find "$TARGET_DIR" -name "*.lean" -type f | while read -r file; do
    echo "Processing: $file"
    
    # Create a temp file
    temp_file=$(mktemp)
    
    # Track if we need to add import Blaster
    has_blaster=false
    if grep -q "^import Blaster" "$file"; then
        has_blaster=true
    fi
    
    # Process the file line by line
    first_import_seen=false
    blaster_added=false
    
    while IFS= read -r line || [[ -n "$line" ]]; do
        # Check if this is an import line
        if [[ "$line" =~ ^import[[:space:]]+ ]]; then
            # Extract the module name after "import "
            module_name=$(echo "$line" | sed 's/^import[[:space:]]*//')
            
            # Mark that we've seen the first import
            if [ "$first_import_seen" = false ]; then
                first_import_seen=true
                # Add import Blaster before the first import if not present
                if [ "$has_blaster" = false ] && [ "$blaster_added" = false ]; then
                    echo "import Blaster" >> "$temp_file"
                    blaster_added=true
                fi
            fi
            
            # Skip if it's already import Blaster or import Bls
            if [[ "$module_name" == "Blaster" ]] || [[ "$module_name" == "Bls" ]]; then
                # Replace Bls with Blaster
                echo "import Blaster" >> "$temp_file"
                continue
            fi
            
            # Skip if it already starts with CaseStudies.Pramaana or is an external lib
            if [[ "$module_name" =~ ^CaseStudies\.Pramaana\. ]] || \
               [[ "$module_name" =~ ^Mathlib\. ]] || \
               [[ "$module_name" =~ ^Std\. ]] || \
               [[ "$module_name" =~ ^Init\. ]] || \
               [[ "$module_name" =~ ^Lean\. ]] || \
               [[ "$module_name" =~ ^Blaster ]]; then
                echo "$line" >> "$temp_file"
            else
                # Add the CaseStudies.Pramaana. prefix
                echo "import CaseStudies.Pramaana.$module_name" >> "$temp_file"
            fi
        else
            echo "$line" >> "$temp_file"
        fi
    done < "$file"
    
    # Replace original file with processed file
    mv "$temp_file" "$file"
    
    echo "  Done: $file"
done

echo ""
echo "All files processed!"





