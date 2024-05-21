#!/usr/bin/env bash


cp ./scripts/copilot_lakefile.txt lakefile.lean

lake update LeanCopilot 

lake exe LeanCopilot/download

lake build 

echo ".........................................................................."
echo "Please do not push changes to the following files: 
     - lakefile.lean
     - .lake/lakefile.olean
     - .lake/lakefile.olean.trace
     - lake-manifest.json
Please ensure that there are no 'import LeanCopilot' statements in the lean files."
