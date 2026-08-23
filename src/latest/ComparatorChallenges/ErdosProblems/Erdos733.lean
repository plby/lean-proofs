/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

noncomputable section


namespace Erdos733

open scoped Classical in
abbrev Point := EuclideanSpace ℝ (Fin 2)

end Erdos733

open scoped Classical in
def IsAffineLine (ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
-- BODY
  (ℓ : Set (EuclideanSpace ℝ (Fin 2))).Nonempty ∧ Module.finrank ℝ ℓ.direction = 1

namespace Erdos733

open scoped Classical in
abbrev Line := {ℓ : AffineSubspace ℝ Point // IsAffineLine ℓ}

end Erdos733

namespace Erdos733

open scoped Classical in
def lineCount (P : Finset Point) (ℓ : Line) : ℕ :=
  (P.filter fun p ↦ p ∈ (ℓ.1 : AffineSubspace ℝ Point)).card

end Erdos733

namespace Erdos733

open scoped Classical in
def lineSizeMultiset (P : Finset Point) (L : Finset Line) : Multiset ℕ :=
  L.1.map (lineCount P)

end Erdos733

namespace Erdos733

open scoped Classical in
def lineSizeSequence (P : Finset Point) (L : Finset Line) : List ℕ :=
  (lineSizeMultiset P L).sort (· ≤ ·)

end Erdos733

namespace Erdos733

open scoped Classical in
def LineCompatible (n : ℕ) (X : List ℕ) : Prop :=
  ∃ P : Finset Point, P.card = n ∧
    ∃ L : Finset Line,
      (∀ ℓ ∈ L, 2 ≤ lineCount P ℓ) ∧
        X = lineSizeSequence P L

end Erdos733

namespace Erdos733

open scoped Classical in
def compatibleSequences (n : ℕ) : Set (List ℕ) :=
  {X | LineCompatible n X}

end Erdos733

namespace Erdos733

open scoped Classical in
theorem erdos_733 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (compatibleSequences n).Finite ∧
        ((compatibleSequences n).ncard : ℝ) ≤
          Real.exp (C * Real.sqrt n) := by
  sorry

end Erdos733

end
