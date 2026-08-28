import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Arithmetic of the support of an equivariant power series

These lemmas identify the permitted exponents of a primitive-root action
and rule out exponents below the least nonnegative permitted residue.
-/

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsPowerCoefficientsArithmetic

/-- A primitive-root power is nontrivial precisely off the divisible exponents. -/
theorem pow_add_ne_one_iff_not_dvd {M : Type*} [CommMonoid M] {ζ : M}
    {m n k : ℕ} (hζ : IsPrimitiveRoot ζ m) :
    ζ ^ (n + k) ≠ 1 ↔ ¬m ∣ n + k :=
  not_congr (hζ.pow_eq_one_iff_dvd (n + k))

/-- No smaller exponent lies in the same residue class as `r < m`. -/
theorem not_dvd_add_of_lt_residue {m n r k : ℕ} (hrm : r < m)
    (hr : m ∣ r + k) (hnr : n < r) : ¬m ∣ n + k := by
  intro hn
  have hsub : m ∣ r - n := by
    simpa only [Nat.add_sub_add_right] using Nat.dvd_sub hr hn
  have hle : m ≤ r - n := Nat.le_of_dvd (Nat.sub_pos_of_lt hnr) hsub
  exact (not_le_of_gt hrm) (hle.trans (Nat.sub_le r n))

/-- For `0 < k ≤ m`, the first permitted exponent is `m - k`. -/
theorem not_dvd_add_of_lt_sub {m n k : ℕ} (hk : 0 < k) (hkm : k ≤ m)
    (hn : n < m - k) : ¬m ∣ n + k := by
  apply not_dvd_add_of_lt_residue (Nat.sub_lt (hk.trans_le hkm) hk) ?_ hn
  simpa only [Nat.sub_add_cancel hkm] using (dvd_refl m)

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsPowerCoefficientsArithmetic
