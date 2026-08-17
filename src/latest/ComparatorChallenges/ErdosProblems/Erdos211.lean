import Mathlib

open Classical
open scoped Real

noncomputable section

attribute [local instance] Classical.propDecidable

def IsAffineLine (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
  (ℓ : Set (EuclideanSpace ℝ (Fin 2))).Nonempty ∧ Module.finrank ℝ ℓ.direction = 1

namespace Erdos211

abbrev Point := EuclideanSpace ℝ (Fin 2)

end Erdos211

namespace Erdos211

abbrev Line := {ℓ : AffineSubspace ℝ Point // IsAffineLine ℓ}

end Erdos211

namespace Erdos211

noncomputable def richness (P : Finset Point) (ℓ : Line) : ℕ :=
  (P.filter fun p ↦ p ∈ (ℓ.1 : Set Point)).card

end Erdos211

namespace Erdos211

noncomputable def pairLine (P : Finset Point) (pq : P.offDiag) : Line :=
  ⟨affineSpan ℝ ({pq.1.1, pq.1.2} : Set Point),
    ⟨⟨pq.1.1, subset_affineSpan ℝ _ (by simp)⟩, by
      rw [direction_affineSpan, vectorSpan_pair]
      exact finrank_span_singleton
        (vsub_ne_zero.2 (Finset.mem_offDiag.mp pq.2).2.2)⟩⟩

end Erdos211

namespace Erdos211

noncomputable def determinedLines (P : Finset Point) : Finset Line :=
  P.offDiag.attach.image (pairLine P)

end Erdos211

namespace Erdos211

theorem erdos_211 :
    ∃ C : ℕ, 0 < C ∧
      ∀ (n k : ℕ) (P : Finset Point),
        1 ≤ k → k < n → P.card = n →
        (∀ line : Line, richness P line ≤ n - k) →
        k * n ≤ C * (determinedLines P).card := by
  sorry

end Erdos211

end
