#!/usr/bin/env bash

python3 ./scripts/check-file-import.py

echo "Running linter for Lean files"

./scripts/lint-style.sh

echo "Building HepLean"

lake build HepLean

echo "Run linter"

lake exe runLinter HepLean

echo "Run shake"

lake exe shake HepLean