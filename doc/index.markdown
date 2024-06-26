---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults
# To see the site locally:
# Run 
# To view changes run: bundle exec jekyll serve
#layout: home
---
# Content 

- [What is HepLean?](https://heplean.github.io/HepLean/#what-is-heplean)
- [How to get involved?](https://heplean.github.io/HepLean/#how-to-get-involved)
- [Coverage](https://heplean.github.io/HepLean/#coverage)

# What is HepLean

HepLean is an open-source project to digitalise definitions, theorems, proofs, and calculations in high energy physics using the interactive theorem prover Lean 4.

HepLean has the potential to benefit the high energy physics community in four ways: 
- Make it easier to find results. 
- Make it easier to automate the creation of new results using e.g. machine learning methods. 
- Make it easier to check papers and results for mathematical correctness. 
- Create new avenues through which high energy physics can be taught. 

HepLean is a connection between high energy physics (both formal and pheno), 
computer science, and mathematics.
# How to get involved? 

There are a number of ways to get involved in HepLean. 

- <b>Improve documentation</b>: If you have never worked on Lean before but have a background 
in high-energy physics, a good place to start contributing is to improve documentation 
on existing code in HepLean. If you need any pointers, please get in touch. 
- <b>Golfing and improving proofs</b>: Many of the proofs in HepLean are not as concise, 
or as short as they could be. Golfing (making shorter) existing proofs is useful benefit 
to HepLean. 
- <b>Improving current areas</b>: There are a number of areas of high energy physics currently in HepLean.
 These are by no means complete, and we would love to see new lemmas, theorems and 
definitions added.  
- <b>Add a new area</b>: We want HepLean to expand into a new areas of high energy physics. 
If you have expertise in any area and would like to see it digitalised, either get in touch or 
make a relavent pull-request on GitHub. 
- <b>Develop new tactics</b>: A benifit of Lean is the ability to automate proofs. This 
is often done through proof tactics. The development of such tactics specific to high-energy physics 
will make it easier for the high-energy physics to use and adapt to Lean. 
- <b>Coding aspects</b>: Improvements to GitHub workflows, and other structural aspects of this
project are greatly appreciated. 

# Coverage 

Any area not appearing in the below table has zero coverage in HepLean. 

| Area | Low Coverage | Medium | High | How to Help? |
| --- | --- | --- | --- | --- |
| [Anomaly cancellation](https://heplean.github.io/HepLean/docs/HepLean/AnomalyCancellation/Basic.html)| ✔️ | ✔️ | ✔️ | Docs, golf |
| [CKM Matrix](https://heplean.github.io/HepLean/docs/HepLean/FlavorPhysics/CKMMatrix/Basic.html) | ✔️ | ✔️ | ✔️ | Docs, golf |
| [Higgs potential](https://heplean.github.io/HepLean/docs/HepLean/StandardModel/HiggsBoson/Basic.html) | ✔️ |  ✘ |  ✘ | Docs, golf, new lemmas etc. |
| [Feynman diagrams](https://heplean.github.io/HepLean/docs/HepLean/FeynmanDiagrams/Basic.html) | ✔️ | ✘  | ✘  |  |
| [Lorentz Group](https://heplean.github.io/HepLean/docs/HepLean/SpaceTime/LorentzGroup/Basic.html) | ✔️ | ✘  | ✘  | New lemmas etc.|
| [2HDM](https://heplean.github.io/HepLean/docs/HepLean/SpaceTime/LorentzGroup/Basic.html) | ✔️ | ✘  | ✘  | New lemmas etc. |
| All other areas |  ✘ | ✘  | ✘  | New lemmas etc.|

