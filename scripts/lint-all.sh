#!/usr/bin/env bash

echo "Running linter for Lean files"

./scripts/lint-style.sh

echo "Building HepLean"

lake build HepLean

echo "Run linter"

lake exe runLinter HepLean