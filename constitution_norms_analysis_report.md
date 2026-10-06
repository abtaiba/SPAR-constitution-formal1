# Analysis: `constitution_norms_p10-17.json`

As of 2026-10-01 · *Claude's Constitution (Jan 2026)*, pages 10–17

## Key findings

- **90 norms**, all with the same 21 fields. There are no duplicates, and all the text is verbatim.
- **80 of the 90 bind Claude.** 64 are regulative and 26 are constitutive.
- **Labels:** Obligation 27 · Definition 18 · Permission 10 · Disposition 9 · Prohibition 6 · Priority 6 · Evaluation 5 · Default 4 · Exception 4 · Scope 1.
- **Strength:** Strong 34 · Presumptive 11 · Permissive 9 · Advisory 4 · Absolute 4 · null 28. "Should" appears 28 times and "must" only once. Most norms are firm but not absolute.
- **38% are defeasible**, but only 8 entries have explicit exception clauses. Most of the flexibility comes from wording like "typically" or from Priority rules, not from "unless" clauses.
- **Two sections hold 84% of the norms.** *Three types of principals* (45) is mostly about Trust and Classification. *Genuine helpfulness* (31) is mostly about Care and Interpretation.

## Issues to fix

1. **7 one-way `related` links:** N012→N051, N055a→N056a, N057b→N057a, N057c→N057a, N073b→N055b, N074→N073a, N075→N074.
2. **N069** has an exception clause but is marked `defeasible: false`.
3. **N017 and N065b** are Obligations with no deontic marker, so they may be missing a tag.

## Caveat

This covers only 8 pages and a single annotator, so the proportions may not hold for the whole constitution.