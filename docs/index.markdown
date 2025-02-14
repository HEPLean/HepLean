---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults
# To see the site locally:
# Run
# To view changes run: bundle exec jekyll serve
#layout: home
---



<div class="example-container" style="border: 2px solid #ddd; border-radius: 8px; padding: 20px; margin: 20px 0; box-shadow: 0 2px 4px rgba(0,0,0,0.1);">
  <div style="text-align: center;">
    <img src="/assets/WicksTheoremScreenShot.png"
         alt="Screenshot of Wick's theorem implementation in PhysLean"
         style="width: 100%; height: auto; border-radius: 4px;">
    <p style="margin-top: 10px; font-style: italic; color: #666;">
      The above screenshot demonstrates how theorems are formalized in PhysLean.
    </p>
  </div>
</div>

**PhysLean was formally called HepLean**
# 1. Mission of PhysLean

The mission of PhysLean is to digitalize results, meaning definitions, theorems and calculations, from physics into Lean 4 with an initial focus on high energy physics and in a way which is useful to the broad physics community.


# 2. Vision of PhysLean

**Statement**: PhysLean aspires to be the definitive formal repository for physics in Lean, akin to Mathlib for mathematics, with both the Lean and physics communities behind it and a potential formal collaboration.

**Detailed Vision**:
- A comprehensive repository for containing fundamental definitions, theorems, and calculations from physics.
- A interface between experimental data, simulations, and formal theoretical frameworks.
- Extensive, physics-focused documentation to support adoption.
- Accessibility for physicists at all levels, including and especially to those new to formal methods.
- An intuitive set-up that aligns with the way physicists think and work.
- A large and active team, with the potential for structured, high-energy physics-style collaborations.

# 3. Values of PhysLean
The three core values of PhysLean are:

- *Welcoming*:  PhysLean strives to foster an environment where contributors of all academic backgrounds and experience levels feel valued, supported, and empowered to make meaningful contributions.
- *Open and Transparent*: PhysLean and its outputs will always be openly accessible, freely available, and developed with transparency to benefit the broader physics and Lean communities.
- *Accessibility and Practicality*: PhysLean is designed to be intuitive, well-documented, and directly useful to physicists, regardless of their familiarity with formal methods.

# 4. Potential impact of the PhysLean

PhysLean has the potential to have the following impact on the physics community:
- Make it easier to find results.
- Make it easier to automate the creation of new results using e.g. machine learning methods.
- Make it easier to check papers and results for mathematical correctness.
- Create new avenues through which physics can be taught.
- Open up new ways to interface between theory and computer programs.

# 5. Where to learn more

You can learn more about PhysLean by reading: [2405.08863](https://inspirehep.net/literature/2787050), or contacting Joseph Tooby-Smith at: joseph at heplean dot com.

# 6. How to get involved

There are a number of different ways to get involved in PhysLean depending on your background.

## 6.1 Physicists
Physicists, who are not so familiar with Lean, can contribute by adding `informal_definition` and `informal_lemma` to PhysLean. These are English written statements of results which can latter be formalised. Informal definitions and lemmas already in PhysLean can be found (here)[https://heplean.github.io/HepLean/InformalGraph.html].

Here are some tips when writing informal results:
- For big theorems, break it down into lots of smaller lemmas.
- Place the informal result in PhysLean in the appropriate file.
- Add dependencies to the `informal_definition` or  `informal_lemma`.
- Write the `math` field of the informal result in sufficient detail that it can be understood by someone with little other context.

Physicists can also help by improving documentation on existing results in PhysLean.

## 6.2 Mathematicians with a Lean background
Mathematicians and people with a Lean background can contribute in a number of ways:
- Help by formalising `informal_definition` and `informal_lemma` which are currently in PhysLean.
- Help by golfing and refactoring code.

## 6.3 Computer scientists with a Lean background
There are a number of metaprograms and infrastructure projects which would improve PhysLean. If you need help in this direction, please get in touch.
