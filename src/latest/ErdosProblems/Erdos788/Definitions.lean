import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact finite formulation of Erdős Problem 788

The original paper defines `f(n)` as the largest *integer* with a universal
property.  We first maximize over natural numbers and then embed the result in
`ℤ`.  The final equivalence in this file proves that this is exactly the
integer maximum from the problem statement, including its quantifier order.
-/

namespace Erdos788

/-- The integer interval `I_n = (n, 2n) ∩ ℕ`. -/
def I (n : ℕ) : Finset ℕ :=
  Finset.Ioo n (2 * n)

/-- The integer interval `J_n = (2n, 4n) ∩ ℕ`. -/
def J (n : ℕ) : Finset ℕ :=
  Finset.Ioo (2 * n) (4 * n)

/-- `C` is `B`-admissible: it lies in `I n`, and no sum of two distinct
members of `C` belongs to `B`.  The assumption `B ⊆ J n` stays at the outer
quantifier, exactly as in the original definition. -/
def Admissible (n : ℕ) (B C : Finset ℕ) : Prop :=
  C ⊆ I n ∧
    ∀ ⦃c⦄, c ∈ C → ∀ ⦃c'⦄, c' ∈ C → c ≠ c' → c + c' ∉ B

/-- The natural-number form of the universal guarantee at threshold `t`. -/
def Guarantees (n t : ℕ) : Prop :=
  ∀ B : Finset ℕ, B ⊆ J n →
    ∃ C : Finset ℕ, Admissible n B C ∧ t ≤ B.card + C.card

/-- A uniform finite upper bound for every score `|B| + |C|`. -/
def scoreBound (n : ℕ) : ℕ :=
  (J n).card + (I n).card

theorem guarantees_zero (n : ℕ) : Guarantees n 0 := by
  intro B _hB
  refine ⟨∅, ?_, by simp⟩
  simp [Admissible]

theorem guarantees_le_scoreBound {n t : ℕ} (h : Guarantees n t) :
    t ≤ scoreBound n := by
  obtain ⟨C, hC, ht⟩ := h (J n) (by simp)
  exact ht.trans (Nat.add_le_add_left (Finset.card_le_card hC.1) _)

/-- The largest natural-number threshold with the universal property. -/
noncomputable def fNat (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (Guarantees n) (scoreBound n)

theorem fNat_guarantees (n : ℕ) : Guarantees n (fNat n) := by
  classical
  exact Nat.findGreatest_spec (Nat.zero_le _) (guarantees_zero n)

theorem le_fNat {n t : ℕ} (h : Guarantees n t) : t ≤ fNat n := by
  classical
  exact Nat.le_findGreatest (guarantees_le_scoreBound h) h

/-- The integer-valued function `f(n)` in the original problem. -/
noncomputable def f (n : ℕ) : ℤ :=
  (fNat n : ℤ)

/-- The paper's universal guarantee predicate for an arbitrary integer `t`. -/
def IntegerGuarantees (n : ℕ) (t : ℤ) : Prop :=
  ∀ B : Finset ℕ, B ⊆ J n →
    ∃ C : Finset ℕ, Admissible n B C ∧
      t ≤ ((B.card + C.card : ℕ) : ℤ)

theorem f_integerGuarantees (n : ℕ) : IntegerGuarantees n (f n) := by
  intro B hB
  obtain ⟨C, hC, hscore⟩ := fNat_guarantees n B hB
  refine ⟨C, hC, ?_⟩
  simpa [f] using! (Int.ofNat_le.mpr hscore)

theorem integerGuarantees_le_f {n : ℕ} {t : ℤ}
    (h : IntegerGuarantees n t) : t ≤ f n := by
  by_cases ht : t ≤ 0
  · exact ht.trans (by simp [f])
  · have ht0 : 0 ≤ t := le_of_lt (lt_of_not_ge ht)
    let u : ℕ := t.toNat
    have hu_cast : (u : ℤ) = t := Int.toNat_of_nonneg ht0
    have hu : Guarantees n u := by
      intro B hB
      obtain ⟨C, hC, hscore⟩ := h B hB
      refine ⟨C, hC, ?_⟩
      exact_mod_cast (hu_cast ▸ hscore)
    have huf : u ≤ fNat n := le_fNat hu
    simpa [f, hu_cast] using! (Int.ofNat_le.mpr huf)

/-- `f n` is the greatest integer having the universal guarantee. -/
theorem f_isGreatestIntegerGuarantee (n : ℕ) :
    IntegerGuarantees n (f n) ∧
      ∀ t : ℤ, IntegerGuarantees n t → t ≤ f n :=
  ⟨f_integerGuarantees n, fun _t ht ↦ integerGuarantees_le_f ht⟩

/-- An integer has the universal guarantee exactly when it is at most `f n`. -/
theorem integerGuarantees_iff_le_f {n : ℕ} {t : ℤ} :
    IntegerGuarantees n t ↔ t ≤ f n := by
  constructor
  · exact integerGuarantees_le_f
  · intro htf B hB
    obtain ⟨C, hC, hscore⟩ := f_integerGuarantees n B hB
    exact ⟨C, hC, htf.trans hscore⟩

end Erdos788
