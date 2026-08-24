/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos863

/-- Representations of `n` as `a + b`, counted once by imposing `a ≤ b`. -/
def sumReps (A : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun x => x.1 ≤ x.2 ∧ x.1 + x.2 = n

/-- Representations of `n` as the natural-number difference `a - b`. -/
def diffReps (A : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ A).filter fun x => x.1 - x.2 = n

/-- The usual `B₂[r]` condition, with unordered summands. -/
def IsB2 (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ n : ℕ, (sumReps A n).card ≤ r

/-- At most `r` representations of every positive difference. -/
def IsDiffB2 (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ n : ℕ, 0 < n → (diffReps A n).card ≤ r

/-- Maximum cardinality of a `B₂[r]` subset of `{1, ..., N}`. -/
noncomputable def sumMax (r N : ℕ) : ℕ :=
  letI : DecidablePred (IsB2 r) := Classical.decPred _
  ((Finset.Icc 1 N).powerset.filter (IsB2 r)).sup Finset.card

/-- Maximum cardinality of a positive-difference `B₂[r]` subset of `{1, ..., N}`. -/
noncomputable def diffMax (r N : ℕ) : ℕ :=
  letI : DecidablePred (IsDiffB2 r) := Classical.decPred _
  ((Finset.Icc 1 N).powerset.filter (IsDiffB2 r)).sup Finset.card

/-- A sequence has the square-root asymptotic constant `c`. -/
def HasSqrtAsymptotic (f : ℕ → ℕ) (c : ℝ) : Prop :=
  Tendsto (fun N : ℕ => (f N : ℝ) / Real.sqrt N) atTop (nhds c)

theorem erdos_863 {r : ℕ} (hr : 2 ≤ r) {cSum cDiff : ℝ}
    (hsum : HasSqrtAsymptotic (sumMax r) cSum)
    (hdiff : HasSqrtAsymptotic (diffMax r) cDiff) :
    cDiff < cSum := by
  sorry

end Erdos863
