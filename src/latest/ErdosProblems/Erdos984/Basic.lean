/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Basic predicates for Erdős Problem 984

This file contains only the exact public statement and the finite
off-diagonal-coloring interface used in Hunter's construction.
-/

open scoped Topology

namespace Erdos984

/-- The first `k` terms of the positive-step progression beginning at `a`
are monochromatic under `color`.  Positivity of the step is kept separate. -/
def IsMonochromaticAP (color : ℕ → Bool) (a d k : ℕ) : Prop :=
  ∃ b : Bool, ∀ i < k, color (a + i * d) = b

/-- The exact affirmative statement of Erdős Problem 984.  The bound is
written out rather than hidden behind asymptotic notation, so the constant
has the intended dependence on `ε` and on the single chosen coloring. -/
def Erdos984Statement : Prop :=
  ∃ color : ℕ → Bool, ∀ ε : ℝ, 0 < ε →
    ∃ A : ℝ, 0 < A ∧ ∀ a d k : ℕ,
      0 < a → 0 < d → IsMonochromaticAP color a d k →
        (k : ℝ) ≤ A * (a : ℝ) ^ ε

/-- `color` has no progression of length `k`, lying in `[0,N)`, whose
terms all have the prescribed Boolean color. -/
def AvoidsColorAP (color : ℕ → Bool) (b : Bool) (N k : ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → a + (k - 1) * d < N →
    ∃ i < k, color (a + i * d) ≠ b

/-- The orientation of Hunter's finite coloring used throughout the
development: `false` has no three-term progression and `true` has no
`h`-term progression. -/
def GoodOffDiagonal (color : ℕ → Bool) (N h : ℕ) : Prop :=
  AvoidsColorAP color false N 3 ∧ AvoidsColorAP color true N h

/-- The exact finite input needed by the geometric-block assembly.  The
field `coloring` selects one good coloring at every finite length. -/
structure OffDiagonalData where
  H : ℕ → ℕ
  three_le_H : ∀ N, 3 ≤ H N
  coloring : ℕ → ℕ → Bool
  good : ∀ N, GoodOffDiagonal (coloring N) N (H N)
  subpower : ∀ ε : ℝ, 0 < ε →
    ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ, 0 < N →
      (H N : ℝ) ≤ B * (N : ℝ) ^ ε

lemma IsMonochromaticAP.color_eq {color : ℕ → Bool} {a d k : ℕ}
    (h : IsMonochromaticAP color a d k) {i j : ℕ}
    (hi : i < k) (hj : j < k) :
    color (a + i * d) = color (a + j * d) := by
  obtain ⟨b, hb⟩ := h
  exact (hb i hi).trans (hb j hj).symm

lemma IsMonochromaticAP.take {color : ℕ → Bool} {a d k m : ℕ}
    (h : IsMonochromaticAP color a d k) (hm : m ≤ k) :
    IsMonochromaticAP color a d m := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun i hi => hb i (lt_of_lt_of_le hi hm)⟩

lemma IsMonochromaticAP.drop {color : ℕ → Bool} {a d k j m : ℕ}
    (h : IsMonochromaticAP color a d k) (hjm : j + m ≤ k) :
    IsMonochromaticAP color (a + j * d) d m := by
  obtain ⟨b, hb⟩ := h
  refine ⟨b, fun i hi => ?_⟩
  simpa [Nat.add_mul, add_assoc] using hb (j + i) (by omega)

lemma AvoidsColorAP.not_mono {color : ℕ → Bool} {b : Bool} {N k a d : ℕ}
    (havoid : AvoidsColorAP color b N k) (hd : 0 < d)
    (hend : a + (k - 1) * d < N)
    (hmono : ∀ i < k, color (a + i * d) = b) : False := by
  obtain ⟨i, hi, hne⟩ := havoid a d hd hend
  exact hne (hmono i hi)

end Erdos984
