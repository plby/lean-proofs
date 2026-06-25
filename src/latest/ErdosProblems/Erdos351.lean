/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 351.
https://www.erdosproblems.com/forum/thread/351

Informal authors:
- GPT-5.5 Pro
- Liam Price
- Kevin Barreto

Formal authors:
- Opus 4.7
- GPT-5.5 Pro
- Pawan Sasanka Ammanamanchi

URLs:
- https://www.erdosproblems.com/forum/thread/283#post-6290
- https://www.overleaf.com/read/gdmnffbshxsq#ef2000
- https://github.com/Shashi456/erdos-formalizations/blob/main/Erdos/P283/Proof_flat.lean
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/351.lean
- https://raw.githubusercontent.com/Shashi456/erdos-formalizations/refs/heads/main/Erdos/P283/Proof_flat.lean
-/
import ErdosProblems.Erdos283

/-! ## #351 wrapper -/

namespace Erdos351

open Polynomial

/-- FC-named alias for `imageSet`. -/
def imageSet (P : ℚ[X]) : Set ℚ := PolynomialEgyptianSums.imageSet P

/-- FC-named alias for `IsStronglyComplete (imageSet P)`. -/
def HasCompleteImage (P : ℚ[X]) : Prop :=
  PolynomialEgyptianSums.IsStronglyComplete (imageSet P)

/-- **`formal-conjectures` upstream form for #351** under `answer := True`.

Direct from `PolynomialEgyptianSums.corollary_7_pos_leading`. -/
theorem erdos_351 :
    True ↔ ∀ P : ℚ[X], 0 < P.natDegree → 0 < P.leadingCoeff →
      HasCompleteImage P := by
  refine ⟨fun _ P _ hlc => ?_, fun _ => trivial⟩
  exact PolynomialEgyptianSums.corollary_7_pos_leading P hlc

#print axioms erdos_351
-- 'Erdos351.erdos_351' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos351
