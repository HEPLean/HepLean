
![HepLean](./docs/HepLeanLogo_white.jpeg)
[![](https://img.shields.io/badge/Read_The-Docs-green)](https://heplean.github.io/HepLean/)
[![](https://img.shields.io/badge/Get-Involved-green)](https://heplean.github.io/HepLean/#how-to-get-involved)
[![](https://img.shields.io/badge/Lean-Zulip-green)](https://leanprover.zulipchat.com)
[![](https://img.shields.io/badge/TODO-List-green)](https://heplean.github.io/HepLean/TODOList)
[![](https://img.shields.io/badge/Informal_dependencies-Graph-green)](https://heplean.github.io/HepLean/InformalGraph)
[![](https://img.shields.io/badge/Lean-v4.12.0-blue)](https://github.com/leanprover/lean4/releases/tag/v4.12.0)

A project to digitalize high energy physics.

## Aims of this project

1. Digitalize results (meaning calculations, definitions, and theorems) from high energy physics
into Lean 4.
2. Develop structures to aid the creation of new results in high energy physics using Lean,
  with the potential future use of AI.
3. Create good documentation so that the project can be used for pedagogical purposes.


## Areas of high energy physics with some coverage in HepLean


[![](https://img.shields.io/badge/The_CKM_Matrix-blue)](https://heplean.github.io/HepLean/docs/HepLean/FlavorPhysics/CKMMatrix/Basic.html)
[![](https://img.shields.io/badge/Higgs_Field-blue)](https://heplean.github.io/HepLean/docs/HepLean/StandardModel/HiggsBoson/Basic.html)
[![](https://img.shields.io/badge/2HDM-blue)](https://heplean.github.io/HepLean/docs/HepLean/BeyondTheStandardModel/TwoHDM/Basic.html)
[![](https://img.shields.io/badge/Lorentz_Group-blue)](https://heplean.github.io/HepLean/docs/HepLean/SpaceTime/LorentzGroup/Basic.html)
[![](https://img.shields.io/badge/Anomaly_Cancellation-blue)](https://heplean.github.io/HepLean/docs/HepLean/AnomalyCancellation/Basic.html)
[![](https://img.shields.io/badge/Feynman_diagrams-blue)](https://heplean.github.io/HepLean/docs/HepLean/FeynmanDiagrams/PhiFour/Basic.html)
## Associated media and publications
| | Description |
|----|------|
| [Paper](https://arxiv.org/abs/2405.08863) | HepLean: Digitalising high energy physics |
| [Code](https://live.lean-lang.org/#code=import%20Mathlib.Tactic.Polyrith%20%0A%0Atheorem%20threeFamily%20(a%20b%20c%20%3A%20ℚ)%20(h%20%3A%20a%20%2B%20b%20%2B%20c%20%3D%200)%20(h3%20%3A%20a%20%5E%203%20%2B%20b%20%5E%203%20%2B%20c%20%5E%203%20%3D%200)%20%3A%20%0A%20%20%20%20a%20%3D%200%20∨%20b%20%3D%200%20∨%20c%20%3D%200%20%20%3A%3D%20by%20%0A%20%20have%20h1%20%3A%20c%20%3D%20-%20(a%20%2B%20b)%20%3A%3D%20by%20%0A%20%20%20%20linear_combination%20h%20%0A%20%20have%20h4%20%3A%20%203%20*%20a%20*%20b%20*%20c%20%3D%200%20%3A%3D%20by%20%0A%20%20%20%20rw%20%5B←%20h3%2C%20h1%5D%0A%20%20%20%20ring%20%0A%20%20simp%20at%20h4%20%0A%20%20exact%20or_assoc.mp%20h4%0A%20%20%0A) | Example code snippet |
| [Video](https://www.youtube.com/watch?v=W2cObnopqas) | HepLean: Lean and high energy physics |
| [Video](https://www.youtube.com/watch?v=IjodVUawTjM) | Index notation in Lean 4 |

### Papers referencing HepLean
- Hu, Jiewen, Thomas Zhu, and Sean Welleck. "miniCTX: Neural Theorem Proving with (Long-) Contexts." arXiv preprint [arXiv:2408.03350](https://www.arxiv.org/abs/2408.03350) (2024). [Project page]( https://cmu-l3.github.io/minictx/)

How HepLean was used: *Theorems from the space-time files of HepLean were included in a data set used to evaluate the ability of models to prove theorems from real-world repositories, which requires working with definitions, theorems, and other context not seen in training.*

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

### Optional extras

- [Lean Copilot](https://github.com/lean-dojo/LeanCopilot) and [LLMLean](https://github.com/cmu-l3/llmlean) allow for the use of large language models in Lean
- [tryAtEachStep](https://github.com/dwrensha/tryAtEachStep) allows one to apply a tactic, e.g. `exact?` at each step of a lemma in a file to see if it completes the goal. This is useful for golfing proofs.
