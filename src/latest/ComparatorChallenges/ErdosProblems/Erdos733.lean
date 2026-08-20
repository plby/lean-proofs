import Mathlib

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos733

abbrev Point := EuclideanSpace ℝ (Fin 2)

end Erdos733

def IsAffineLine (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
-- BODY
  (ℓ : Set (EuclideanSpace ℝ (Fin 2))).Nonempty ∧ Module.finrank ℝ ℓ.direction = 1

namespace Erdos733

abbrev Line := {ℓ : AffineSubspace ℝ Point // IsAffineLine ℓ}

end Erdos733

namespace Erdos733

def lineCount (P : Finset Point) (ℓ : Line) : ℕ :=
  (P.filter fun p ↦ p ∈ (ℓ.1 : AffineSubspace ℝ Point)).card

end Erdos733

namespace Erdos733

def lineSizeMultiset (P : Finset Point) (L : Finset Line) : Multiset ℕ :=
  L.1.map (lineCount P)

end Erdos733

namespace Erdos733

def lineSizeSequence (P : Finset Point) (L : Finset Line) : List ℕ :=
  (lineSizeMultiset P L).sort (· ≤ ·)

end Erdos733

namespace Erdos733

def LineCompatible (n : ℕ) (X : List ℕ) : Prop :=
  ∃ P : Finset Point, P.card = n ∧
    ∃ L : Finset Line,
      (∀ ℓ ∈ L, 2 ≤ lineCount P ℓ) ∧
        X = lineSizeSequence P L

end Erdos733

namespace Erdos733

def compatibleSequences (n : ℕ) : Set (List ℕ) :=
  {X | LineCompatible n X}

end Erdos733

namespace Erdos733

theorem erdos_733 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (compatibleSequences n).Finite ∧
        ((compatibleSequences n).ncard : ℝ) ≤
          Real.exp (C * Real.sqrt n) := by
  sorry

end Erdos733

end
