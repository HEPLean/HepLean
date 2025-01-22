---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults
# To see the site locally:
# Run
# To view changes run: bundle exec jekyll serve
#layout: home
---

# What is HepLean?

HepLean is an open-source project to digitalise definitions, theorems, proofs, and calculations in physics using the interactive theorem prover Lean 4.

## Scope of HepLean

Currently the scope of HepLean includes the results and foundations of the following arXiv categories:

*hep-th, hep-ph, hep-ex, hep-lat, gr-qc, and math-ph.*

In particular, the current scope of HepLean includes (but is not limited to) the following foundational areas:

*special and general relativity, quantum mechanics, quantum field theory, particle physics, classical mechanics and field theory, cosmology, thermodynamics*

Once the foundations are in place, and HepLean has a large enough active community behind it, the scope of HepLean will naturally increase to include other areas of physics (and it most likely will undergo a name change).

# Why formalize physics?

HepLean has the potential to benefit the physics community in four ways:
- Make it easier to find results.
- Make it easier to automate the creation of new results using e.g. machine learning methods.
- Make it easier to check papers and results for mathematical correctness.
- Create new avenues through which physics can be taught.
- Opens up new ways to interface between theory and computer programs.

# How to get involved?

There are a number of different ways to get involved in HepLean depending on your background.

## Physicists
Physicists, who are not so familiar with Lean, can contribute by adding `informal_definition` and `informal_lemma` to HepLean. These are English written statements of results which can latter be formalised. Informal definitions and lemmas already in HepLean can be found (here)[https://heplean.github.io/HepLean/InformalGraph.html].

Here are some tips when writing informal results:
- For big theorems, break it down into lots of smaller lemmas.
- Place the informal result in HepLean in the appropriate file.
- Add dependencies to the `informal_definition` or  `informal_lemma`.
- Write the `math` field of the informal result in sufficient detail that it can be understood by someone with little other context.

Physicists can also help by improving documentation on existing results in HepLean.

## Mathematicians with a Lean background
Mathematicians and people with a Lean background can contribute in a number of ways:
- Help by formalising `informal_definition` and `informal_lemma` which are currently in HepLean.
- Help by golfing and refactoring code.

## Computer scientists with a Lean background
There are a number of metaprograms and infrastructure projects which would improve HepLean. If you need help in this direction, please get in touch.
