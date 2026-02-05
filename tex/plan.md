# IJCAR 2026 Paper Plan

## Deadlines
- **Abstract submission**: February 6, 2026 (AoE) — Friday
- **Paper submission**: February 13, 2026 (AoE) — Friday
- **Format**: LNCS, up to 15 pages (excl. references and appendices)

## Current status
- Paper is 13 pages, ~3000 words across sections.
- The tool now translates all 21 CPC-MINI modules with full
  `lambdapi check` + SR verification (133 unit tests pass).
- ~200 QF_UF proof files exist in `proofs/QF_UF/`.
- The `--proofs` flag crashes on a missing file; needs a fix
  before we can report proof benchmark numbers.
- `elaborate.ml` (491 lines) exists as a separate elaboration
  phase but is not described in the paper.
- The paper's Section 4 and conclusion understate what has
  been achieved and need rewriting.

---

## Day-by-day plan

### Tuesday 4 Feb — Audit and abstract draft
_Priority: get the abstract right before Friday._

- [ ] Re-read entire paper end-to-end, make a detailed list
      of every factual claim that is now wrong or understated.
- [ ] Draft updated abstract (concrete numbers: 21 modules,
      ~5000 LOC, 200 QF_UF proofs, full type-checking).
- [ ] Draft updated title if needed (current title is fine,
      but consider whether "Automatically" is accurate).
- [ ] Send abstract draft to Guillaume for review.

### Wednesday 5 Feb — Fix proof benchmark, gather numbers
- [ ] Fix the `--proofs` crash (missing file in QF_UF dir).
- [ ] Run full proof translation, record success/failure counts.
- [ ] Collect quantitative data for the results table:
  - Per-module: symbol count, rule count, lines of .lp output,
    encoding time, checking time.
  - Proof benchmark: number of proofs, proof steps, success rate.
  - Implementation: LOC breakdown by file.
- [ ] Finalise abstract text; submit by end of day (AoE Fri = Sat morning Paris).

### Thursday 6 Feb — Abstract submission day (AoE)
- [ ] Submit abstract on HotCRP.
- [ ] Begin rewriting Section 4 (res.tex):
  - Add results table (modules x metrics).
  - Describe the 3-phase pipeline (parse, elaborate, encode).
  - Add a concrete translation example
    (side-by-side .eo source and .lp output).
  - Update proof benchmark description with real numbers.
  - Mention unit test infrastructure.

### Friday 7 Feb — Section 4 rewrite (continued)
- [ ] Finish Section 4 rewrite.
- [ ] Add implementation subsection: ~5000 LOC OCaml, Menhir
      parser, elaborate.ml as distinct phase, LambdaPi API
      usage, per-module timing.
- [ ] Add figure: pipeline diagram (parse → elaborate → encode → check).
- [ ] Review whether the formal definitions in res.tex
      (Definition 1–3) still match the implementation; update
      if not.

### Saturday 8 Feb — Conclusion + intro polish
- [ ] Rewrite Section 5 (conclusion):
  - CPC-MINI is fully translated — no longer future work.
  - Future work: full CPC (expert/ modules), larger proof
    benchmarks beyond QF_UF, efficiency for massive proofs,
    formal verification of CPC rules in LambdaPi, consistency
    checking, proof interoperability via Dedukti export.
  - Add acknowledgements (INRIA, CARMA, AWS, Haniel,
    Yoni Zohar, Hans-Jörg, Theo).
- [ ] Polish Section 1 (intro.tex):
  - Check all citations still make sense.
  - Ensure the contribution statement at the end of the
    intro accurately reflects updated results.
  - Minor consistency fixes.

### Sunday 9 Feb — Sections 2 & 3, examples
- [ ] Review Section 2 (eoas.tex):
  - Check Eunoia syntax presentation matches current spec.
  - Consider adding a brief subsection or paragraph on
    computational operators / builtins if space permits.
  - Verify the elaboration definition is accurate.
- [ ] Review Section 3 (lp.tex):
  - Ensure LambdaPi syntax presentation is complete enough
    for the translation section to be self-contained.
  - No major changes expected here.
- [ ] Add/improve concrete examples:
  - A small Eunoia signature snippet and its LambdaPi output.
  - A small proof step (assume/step) and its LambdaPi output.

### Monday 10 Feb — Full pass, page budget
- [ ] Full read-through of the assembled paper for coherence.
- [ ] Check page count. We have 15 pages max (excl. refs).
  - Currently 13 pages including refs. After adding the
    results table and examples, we may be tight.
  - If over: tighten prose, shrink figures, move details
    to appendix.
  - If under: expand examples or add related work discussion.
- [ ] Fix any LaTeX formatting issues (overfull hboxes,
      figure placement, table formatting).
- [ ] Verify all `\cite` references resolve; add any
      missing bib entries to `inria.bib`.

### Tuesday 11 Feb — Co-author review
- [ ] Send full draft to Guillaume.
- [ ] Address any feedback from Guillaume on the abstract
      (if received earlier).
- [ ] Proof-read: fix typos, grammar, notation consistency.
- [ ] Verify: every claim in the paper can be reproduced
      by running the tool (`dune exec eo2lp`, `dune test`).

### Wednesday 12 Feb — Final revisions
- [ ] Incorporate Guillaume's feedback.
- [ ] Final notation/macro consistency check across all sections.
- [ ] Verify PDF metadata (title, authors, affiliations).
- [ ] Check LNCS formatting compliance:
  - Author names and affiliations format.
  - No page numbers (LNCS adds them).
  - Correct `\documentclass{llncs}` usage.
- [ ] Generate final PDF; do one last visual inspection.

### Thursday 13 Feb — Submission day (AoE)
- [ ] Final proof-read (fresh eyes).
- [ ] Submit on HotCRP before AoE.
- [ ] Verify submission: correct PDF, all authors listed,
      correct track, all supplementary material attached.
- [ ] (Optional) prepare a supplementary archive:
      tool source, CPC-MINI, generated .lp files, proof
      benchmark scripts.

---

## Key changes needed (summary)

### Abstract — update
- Strengthen: "a subset" → "the full QF_UF fragment"
- Add numbers: 21 modules, ~200 proofs, 133 tests, ~5k LOC

### Section 4 (res.tex) — major rewrite
- Add results table with per-module metrics
- Describe 3-phase pipeline (parse, elaborate, encode)
- Add concrete translation example (side-by-side .eo/.lp)
- Update proof benchmark with real numbers
- Add implementation details (LOC, Menhir, LambdaPi API)

### Section 5 (conclusion) — rewrite
- Remove "translate all of CPC" as future work (done for CPC-MINI)
- Remove "fewer than 70 proof steps" (outdated)
- Reframe future work: full CPC, larger benchmarks, formal
  verification, interoperability

### Section 1 (intro.tex) — minor polish
- Update contribution statement
- Check citation accuracy

### Sections 2–3 — review only
- Verify accuracy, no major changes expected

---

## Old planning notes (archived)

<details>
<summary>Original section outline</summary>

- section 1:
  - Eunoia, SMT-LIB 3, cvc5, CPC, lambdapi/dedukti.
  - Alethe, LFSC, LambdaPi citations.
- section 2:
  - discussion of commands
  - definition of term elaboration wrt. attributes
  - builtin-commands, CPC as Eunoia signature
  - example of cvc5 proof using CPC rules
- section 4:
  - term/type-level translation
  - top-level translation (consts, define, program, declare-rule, include)
  - assume, step
  - rodin proof benchmarks, cpc-mini, eo2lp implementation
  - limitations (declare-consts for literals)
  - examples of translated signature and proofs
- section 5:
  - formal type-theoretic semantics for Eunoia
  - interoperability of SMT in LambdaPi ecosystem
  - larger benchmarks, full CPC, verify CPC rules
  - acknowledgements: INRIA, CARMA, AWS, Haniel, Yoni Zohar, Hans-Jörg, Theo

</details>
