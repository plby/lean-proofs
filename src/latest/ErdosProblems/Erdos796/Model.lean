import ErdosProblems.Erdos796.Core
import Mathlib.Data.Nat.Lattice

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The finite cofactor model

This file isolates the elementary order-theoretic part of the cofactor
model.  In particular, the maximum defining `G(n)` is an attained natural
number, despite being written as a supremum over infinite compatible
families: every score is bounded by a finite weighted sum.
-/

namespace Erdos796

open scoped BigOperators

/-- The empty cofactor family. -/
def emptyFamily : ℕ → Finset ℕ := fun _ => ∅

@[simp] theorem emptyFamily_apply (j : ℕ) : emptyFamily j = ∅ := rfl

theorem emptyFamily_compatible : Compatible emptyFamily := by
  constructor
  · intro j
    simp [emptyFamily]
  · intro i j m
    simp [productRepCount, emptyFamily]

/-- A compatible fibre at index `j` has at most `j` elements. -/
theorem compatible_card_le {U : ℕ → Finset ℕ} (hU : Compatible U) (j : ℕ) :
    (U j).card ≤ j := by
  calc
    (U j).card ≤ (positiveIcc j).card := Finset.card_le_card (hU.1 j)
    _ = j := by simp [positiveIcc]

/-- A crude finite upper bound for every model score. -/
def modelUpperBound (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 n.sqrt, bucketCount n j * j

theorem modelScore_le_upperBound {U : ℕ → Finset ℕ} (hU : Compatible U) (n : ℕ) :
    modelScore n U ≤ modelUpperBound n := by
  unfold modelScore modelUpperBound
  apply Finset.sum_le_sum
  intro j _
  exact Nat.mul_le_mul_left _ (compatible_card_le hU j)

/-- The set of values attained by compatible cofactor families. -/
def modelValues (n : ℕ) : Set ℕ :=
  {k | ∃ U : ℕ → Finset ℕ, Compatible U ∧ modelScore n U = k}

theorem modelValues_nonempty (n : ℕ) : (modelValues n).Nonempty := by
  refine ⟨0, emptyFamily, emptyFamily_compatible, ?_⟩
  simp [modelScore, emptyFamily]

theorem modelValues_bddAbove (n : ℕ) : BddAbove (modelValues n) := by
  refine ⟨modelUpperBound n, ?_⟩
  intro k hk
  rcases hk with ⟨U, hU, rfl⟩
  exact modelScore_le_upperBound hU n

/-- The maximum finite-model score `G(n)`. -/
noncomputable def G (n : ℕ) : ℕ := sSup (modelValues n)

theorem G_mem_modelValues (n : ℕ) : G n ∈ modelValues n := by
  exact Nat.sSup_mem (modelValues_nonempty n) (modelValues_bddAbove n)

/-- A compatible family attaining `G(n)` exists. -/
theorem G_attained (n : ℕ) :
    ∃ U : ℕ → Finset ℕ, Compatible U ∧ modelScore n U = G n := by
  exact G_mem_modelValues n

theorem modelScore_le_G {U : ℕ → Finset ℕ} (hU : Compatible U) (n : ℕ) :
    modelScore n U ≤ G n := by
  have hm : modelScore n U ∈ modelValues n := ⟨U, hU, rfl⟩
  exact le_csSup (modelValues_bddAbove n) hm

end Erdos796
