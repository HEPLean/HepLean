# High Energy Physics in Lean

[![](https://img.shields.io/badge/Read_The-Docs-green)](https://heplean.github.io/HepLean/)
[![](https://img.shields.io/badge/PRs-Welcome-green)](https://github.com/HEPLean/HepLean/pulls)
[![](https://img.shields.io/badge/Lean-Zulip-green)](https://leanprover.zulipchat.com)
![](https://img.shields.io/badge/Lean-v4.8.0_rc1-blue)

A project to digitalize high energy physics.

## Aims of this project

- Use Lean to create an exhaustive database of definitions, theorems, proofs, and calculations in high energy physics.
- Make a library that is easy to use by the high energy physics community.
- Keep the database up-to date with developments in MathLib4. 
- Create gitHub workflows of relevance to the high energy physics community. 

## Where to learn more 

- Read the associated paper:

  https://arxiv.org/abs/2405.08863

- The documentation for this project is at: 

  https://heplean.github.io/HepLean/

- Watch this overview of HepLean:

  https://www.youtube.com/watch?v=W2cObnopqas
- A list of 'Frequently asked questions' can be found on the Wiki for this project: 

  https://github.com/HEPLean/HepLean/wiki/The-answers-to-some-questions
- Feel free to connect on the Lean Zulip channel: 

  https://leanprover.zulipchat.com

- A small example script relating to the three fermion anomaly cancellation condition can be found [here](https://live.lean-lang.org/#code=import%20Mathlib.Tactic.Polyrith%20%0A%0Atheorem%20threeFamily%20(a%20b%20c%20%3A%20ℚ)%20(h%20%3A%20a%20%2B%20b%20%2B%20c%20%3D%200)%20(h3%20%3A%20a%20%5E%203%20%2B%20b%20%5E%203%20%2B%20c%20%5E%203%20%3D%200)%20%3A%20%0A%20%20%20%20a%20%3D%200%20∨%20b%20%3D%200%20∨%20c%20%3D%200%20%20%3A%3D%20by%20%0A%20%20have%20h1%20%3A%20c%20%3D%20-%20(a%20%2B%20b)%20%3A%3D%20by%20%0A%20%20%20%20linear_combination%20h%20%0A%20%20have%20h4%20%3A%20%203%20*%20a%20*%20b%20*%20c%20%3D%200%20%3A%3D%20by%20%0A%20%20%20%20rw%20%5B←%20h3%2C%20h1%5D%0A%20%20%20%20ring%20%0A%20%20simp%20at%20h4%20%0A%20%20exact%20or_assoc.mp%20h4%0A%20%20%0A)


## Contributing 

We follow here roughly the same contribution policies as MathLib4 (which can be found [here](https://leanprover-community.github.io/contribute/index.html)). 

A guide to contributing can be found [here](https://github.com/HEPLean/HepLean/blob/master/CONTRIBUTING.md).

If you want permission to create a pull-request for this repository contact Joseph Tooby-Smith on the lean Zulip, or email.  

## Installation

### Installing Lean 4 

The installation instructions for Lean 4 are given here: https://leanprover-community.github.io/get_started.html. 

### Installing HepLean 

- Clone this repository (or download the repository as a Zip file) 
- Open a terminal at the top-level in the corresponding directory.
- Run `lake exe cache get`. The command `lake` should have been installed when you installed Lean.
- Run `lake build`.
- Open the directory (not a single file) in Visual Studio Code (or another Lean compatible code editor).

### Adding Lean Copilot (optional)

[Lean Copilot](https://github.com/lean-dojo/LeanCopilot) allows the use of large language models in Lean. Using Lean Copilot with HepLean can be done in the following way:

Either: 

- Run the script `./scripts/add-copilot.sh` 

Or: 

- Copy the file `./scripts/copilot_lakefile.txt` over to `lakefile.lean`,
- Run `lake update LeanCopilot`,
- Run `lake exe LeanCopilot/download`,
- Run `lake build`.

To use LeanCopilot add `import LeanCopilot` to the top of the lean file you are working in. 
The following commands should then become available to you:
- `suggest_tactics`,
- `search_proofs`,
- `select_premises`.

Adding Lean Copilot will modify a number of files. If you have added Lean Copilot, please do not push changes to the following files:

- `lakefile.lean`,
- `.lake/lakefile.olean`,
- `.lake/lakefile.olean.trace`,
- `lake-manifest.json`.

Please also ensure that there are not any `import LeanCopilot` statements in the lean files.
