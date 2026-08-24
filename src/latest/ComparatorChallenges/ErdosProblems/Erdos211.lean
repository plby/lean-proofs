/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

def IsAffineLine (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
  (ℓ : Set (EuclideanSpace ℝ (Fin 2))).Nonempty ∧ Module.finrank ℝ ℓ.direction = 1

namespace Erdos211

abbrev Point := EuclideanSpace ℝ (Fin 2)

abbrev Line := {ℓ : AffineSubspace ℝ Point // IsAffineLine ℓ}

open scoped Classical in
noncomputable def richness (P : Finset Point) (ℓ : Line) : ℕ :=
  (P.filter fun p ↦ p ∈ (ℓ.1 : Set Point)).card

noncomputable def pairLine (P : Finset Point) (pq : P.offDiag) : Line :=
  ⟨affineSpan ℝ ({pq.1.1, pq.1.2} : Set Point),
    ⟨⟨pq.1.1, subset_affineSpan ℝ _ (by simp)⟩, by
      rw [direction_affineSpan, vectorSpan_pair]
      exact finrank_span_singleton
        (vsub_ne_zero.2 (Finset.mem_offDiag.mp pq.2).2.2)⟩⟩

open scoped Classical in
noncomputable def determinedLines (P : Finset Point) : Finset Line :=
  P.offDiag.attach.image (pairLine P)

theorem erdos_211 :
    ∃ C : ℕ, 0 < C ∧
      ∀ (n k : ℕ) (P : Finset Point),
        1 ≤ k → k < n → P.card = n →
        (∀ line : Line, richness P line ≤ n - k) →
        k * n ≤ C * (determinedLines P).card := by
  sorry

end Erdos211
