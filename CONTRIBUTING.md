# Contributing 

## Adding results to HepLean

This assumes you have already installed Lean and setup HepLean. 

To add a result to HepLean:

- Create a new branch of HepLean.
- Name the branch something which tells people what sort of things you are adding e.g., "StandardModel-HiggsPotential"
- On pushing to a branch GitHub will run a number of continuous integration checks on your code.
- Once you are happy, and your branch has passed the continuous integration checks, make a pull-request to the main branch of HepLean.

## Naming commits 

It is useful to prefix commits with one of the following. 
- `feat:` When you add one or more new lemma, definition, or theorems. 
- `refactor:` When you are improving the layout and structure of the code. 
- `fix:` When fixing a mistake in a definition or other Lean code. 
- `docs:` When adding a comment or updating documentation. 
- `style:` When adding e.g., white space, a semicolon etc. But does not change the overall
    structure of the code.
- `chore:` Updating e.g., workflows.