
# Scripts associated with HepLean 

## lint-style.py and lint-style.sh

Taken from Mathlib's linters. These perform text-based linting of the code. 

These are to be slowly replaced with code written in Lean.

## hepLean_style_lint

Checks the following in HepLean 
- There are no double empty lines. 
- There are no non-initial double spaces.  
Passing this linter is currently not required to pass CI on github.

Run using 
```
lake exe hepLean_style_lint
```

## check_file_imports.lean 

Checks all files are correctly imported into `HepLean.lean`. 

Run using 
```
lake exe check_file_imports
```

## type_former_lint.lean

Checks whether the name of definitions which form a type or prop starts with a capital letter. 

Run using 
```
lake exe type_former_lint
```

## lint-all.sh 

Performs all linting checks on HepLean. 

Run using 
```
./scripts/lint-all.sh
```

## Other useful commands

- To build HepLean use 
```
lake exe cache get 
lake build
```

- To update HepLean's dependencies use 
```
lake update
```