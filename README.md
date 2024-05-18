# Formalising Large Corner-free Sets

For my third year project, I formalised Ben Green's 2021 result ["Lower bounds for corner-free sets"](https://arxiv.org/abs/2102.11702). It was a new construction that significantly improved on the previous best results by [Linial & Shraibman (2021)](https://arxiv.org/pdf/2102.00421) and [Behrend (1946)](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC1078964/).

This project is organised as follows:

- `BenGreenCornerFree` contains the (almost finished) formalised Lean project. It is split into ABCD parts:
    - [ ] `Asymptotics{1,2,3}.lean`: Simplifying asymptotics of the construction size after parameter choice
    - [ ] `Bridge.lean`: Computing upper bound of construction size via PHP (Pigeon-Hole Principle)
    - [ ] `Construction.lean`: Defining the construction
    - [ ] `Defs.lean`: Definition of `AddCornerFree`
    - [ ] Missing: Proving a single statement that says "there exists a corner-free set of size xxx"
- `details` contains a scratchpad-blueprint
- `essay/main-submitted.pdf`: My submitted essay (32 pages, commit: `cd1252f6`)
- `presentation/main.pdf` contains my presentation
