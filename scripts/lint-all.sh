#!/usr/bin/env bash


echo "Running linter for Lean files"

./scripts/lint-style.sh

echo "Building PhysLean"

lake build PhysLean

echo "Run linter"

lake exe runLinter PhysLean

echo "Run shake"

lake exe shake PhysLean
