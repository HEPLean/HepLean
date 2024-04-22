# High Energy Physics in Lean

## Aims of this project

- Use Lean to create a exhaustive database of definitions, theorems, proofs and calculations in high energy physics.
- Keep the database up-to date with developments in MathLib4. 
- Create github workflows of relevence to the high energy physics community. 

## Where to learn more 

- The documentation for this project is at: 

  https://heplean.github.io/HepLean/
- Feel free to connect on the Lean Zulip channel: 

  https://leanprover.zulipchat.com

- A small example script relating to the three fermion anomaly cancellation condition can be found [here](https://live.lean-lang.org/#code=import%20Mathlib.Tactic.Polyrith%20%0A%0Atheorem%20threeFamily%20(a%20b%20c%20%3A%20ℚ)%20(h%20%3A%20a%20%2B%20b%20%2B%20c%20%3D%200)%20(h3%20%3A%20a%20%5E%203%20%2B%20b%20%5E%203%20%2B%20c%20%5E%203%20%3D%200)%20%3A%20%0A%20%20%20%20a%20%3D%200%20∨%20b%20%3D%200%20∨%20c%20%3D%200%20%20%3A%3D%20by%20%0A%20%20have%20h1%20%3A%20c%20%3D%20-%20(a%20%2B%20b)%20%3A%3D%20by%20%0A%20%20%20%20linear_combination%20h%20%0A%20%20have%20h4%20%3A%20%203%20*%20a%20*%20b%20*%20c%20%3D%200%20%3A%3D%20by%20%0A%20%20%20%20rw%20%5B←%20h3%2C%20h1%5D%0A%20%20%20%20ring%20%0A%20%20simp%20at%20h4%20%0A%20%20exact%20or_assoc.mp%20h4%0A%20%20%0A)

  

## Contributing 

We follow here roughly the same contribution policies as MathLib4 (which can be found [here](https://leanprover-community.github.io/contribute/index.html)). With the exception that we allow some `sorry` statements, if a theorem is widly expected to be true by the community. 

If you want permission to create a pull-request for this repository contact Joseph Tooby-Smith on the lean Zulip, or email. 

## Installation

### Installing Lean 4 

See: https://leanprover-community.github.io/get_started.html

### Quick installation 

1. Clone this repository. 
2. Open a terminal in the cloned directory. 
2. Run `lake -Kenv=dev update`.

Depending on how up to date this directory is compared to MathLib4 this may lead to errors.
