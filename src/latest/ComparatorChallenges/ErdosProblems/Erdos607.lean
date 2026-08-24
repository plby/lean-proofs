/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib
import Submission.IsAffineLine

open Filter

namespace Erdos607

noncomputable local instance instDecidableProp (p : Prop) : Decidable p :=
  Classical.propDecidable p

abbrev Point := EuclideanSpace ℝ (Fin 2)

abbrev Line := {ℓ : AffineSubspace ℝ Point // IsAffineLine ℓ}

noncomputable local instance : DecidableEq Line := Classical.decEq Line

noncomputable def pairLine (P : Finset Point) (pq : P.offDiag) : Line :=
  ⟨affineSpan ℝ ({pq.1.1, pq.1.2} : Set Point),
    ⟨⟨pq.1.1, subset_affineSpan ℝ _ (by simp)⟩, by
      rw [direction_affineSpan, vectorSpan_pair]
      exact finrank_span_singleton
        (vsub_ne_zero.2 (Finset.mem_offDiag.mp pq.2).2.2)⟩⟩

noncomputable def determinedLines (P : Finset Point) : Finset Line :=
  P.offDiag.attach.image (pairLine P)

noncomputable def pointsOn (P : Finset Point) (ℓ : Line) : Finset Point :=
  P.filter fun p ↦ p ∈ (ℓ.1 : Set Point)

noncomputable def richness (P : Finset Point) (ℓ : Line) : ℕ :=
  (pointsOn P ℓ).card

noncomputable def multiplicitySpectrum (P : Finset Point) : Finset ℕ :=
  (determinedLines P).image (richness P)

def IsRealizableSpectrum (n : ℕ) (A : Finset ℕ) : Prop :=
  ∃ P : Finset Point, P.card = n ∧ multiplicitySpectrum P = A

noncomputable def possibleSpectra (n : ℕ) : Finset (Finset ℕ) :=
  ((Finset.Icc 2 n).powerset).filter (IsRealizableSpectrum n)

noncomputable def F (n : ℕ) : ℕ :=
  (possibleSpectra n).card

theorem erdos_607 :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (F n : ℝ) ≤ Real.exp (C * Real.sqrt n) := by
  sorry

end Erdos607
