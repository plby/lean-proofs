/-
Copyright (c) 2026 Elliot Glazer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Root module of the `Erdos501` development.  `Solution.lean` and `SolutionFlypitch.lean` import this.
See `docs/STATUS.md` for what each module proves and its state.

The forcing side of the independence proof (the first-order sentence
`Erdos501_f`, its semantics, the random algebra, and the theorem
`neg_Erdos501_f_unprovable : ¬ (ZFC ⊢ₛ' ∼Erdos501_f)`) lives in the vendored
Flypitch library, under `Flypitch4/Erdos501/` (namespace `Flypitch.Erdos501`).
-/
-- Second question (closed sets of measure < 1): NPS87, infinite free set.
import ErdosProblems.Erdos501.Closed
-- First question, negative direction: Hechler's counterexample under CH.
import ErdosProblems.Erdos501.Hechler
-- ZFC core of the random-reals argument (paper §2–3): certificate ⇒ free set
-- (Mathlib-level; the forcing tree has its own copy in `Flypitch4.Erdos501.ZFCCore`).
import ErdosProblems.Erdos501.ZFCCore
-- Assembly: `independent ZFC Erdos501_f` and the faithfulness bridge.
import ErdosProblems.Erdos501.Independence
-- Bridge to Mathlib's first-order logic (the Palomar-conformant `Challenge.lean`):
-- the shared statement, the translation to Flypitch, and the semantic independence
-- `¬ (ZFC ⊨ᵇ Erdos501)`, `¬ (ZFC ⊨ᵇ ∼Erdos501)`.
import ErdosProblems.Erdos501.FOL.Statement
import ErdosProblems.Erdos501.FOL.Translate
import ErdosProblems.Erdos501.FOL.FolLemmas
import ErdosProblems.Erdos501.FOL.Collection
import ErdosProblems.Erdos501.FOL.Axioms
import ErdosProblems.Erdos501.FOL.Sentence
import ErdosProblems.Erdos501.FOL.Independence
