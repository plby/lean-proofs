/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The order function in Romanoff's series

This file develops the elementary multiplicative-order interface used in the
Romanoff-series estimate for Erdős problem 851.  For an odd modulus `q`,
`twoOrder q` is the multiplicative order of `2` modulo `q`.
-/

namespace Erdos851

/-- The multiplicative order of `2` modulo `q`.  The intended domain is the
odd positive moduli; keeping the definition total makes finite sums easier to
state. -/
noncomputable def twoOrder (q : ℕ) : ℕ := orderOf (2 : ZMod q)

/-- Two is a unit modulo every odd modulus. -/
theorem isUnit_two_zmod {q : ℕ} (hq : Odd q) : IsUnit (2 : ZMod q) := by
  exact (ZMod.isUnit_iff_coprime 2 q).2 hq.coprime_two_left

/-- The order of two modulo an odd modulus is positive. -/
theorem twoOrder_pos {q : ℕ} (hq : Odd q) : 0 < twoOrder q := by
  rw [twoOrder, orderOf_pos_iff]
  exact (isUnit_two_zmod hq).isOfFinOrder

/-- Divisibility by `2^h - 1` is exactly periodicity of the powers of two
modulo `q`. -/
theorem dvd_two_pow_sub_one_iff_pow_eq_one {q h : ℕ} :
    q ∣ 2 ^ h - 1 ↔ (2 : ZMod q) ^ h = 1 := by
  have hle : 1 ≤ 2 ^ h := Nat.one_le_pow h 2 (by norm_num)
  constructor
  · intro hdvd
    have hmod : 2 ^ h ≡ 1 [MOD q] :=
      ((Nat.modEq_iff_dvd' hle).2 hdvd).symm
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using
      (ZMod.natCast_eq_natCast_iff (2 ^ h) 1 q).2 hmod
  · intro hpow
    have hmod : 2 ^ h ≡ 1 [MOD q] := by
      apply (ZMod.natCast_eq_natCast_iff (2 ^ h) 1 q).1
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hpow
    exact (Nat.modEq_iff_dvd' hle).1 hmod.symm

/-- The fundamental order/divisibility equivalence used to average the
singular factor. -/
theorem twoOrder_dvd_iff_dvd_two_pow_sub_one {q h : ℕ} :
    twoOrder q ∣ h ↔ q ∣ 2 ^ h - 1 := by
  rw [twoOrder, orderOf_dvd_iff_pow_eq_one,
    dvd_two_pow_sub_one_iff_pow_eq_one]

/-- Euler's theorem bounds the order of two by the totient of every odd
modulus. -/
theorem twoOrder_dvd_totient {q : ℕ} (hq : Odd q) :
    twoOrder q ∣ q.totient := by
  rw [twoOrder_dvd_iff_dvd_two_pow_sub_one]
  have hle : 1 ≤ 2 ^ q.totient := Nat.one_le_pow _ _ (by norm_num)
  apply (Nat.modEq_iff_dvd' hle).1
  exact (Nat.ModEq.pow_totient hq.coprime_two_left).symm

/-- An odd modulus is strictly smaller than `2` raised to the order of `2`
modulo that modulus. -/
theorem lt_two_pow_twoOrder {q : ℕ} (hq : Odd q) :
    q < 2 ^ twoOrder q := by
  have hord : 0 < twoOrder q := twoOrder_pos hq
  have hdvd : q ∣ 2 ^ twoOrder q - 1 :=
    twoOrder_dvd_iff_dvd_two_pow_sub_one.mp (dvd_refl _)
  have hpow : 1 < 2 ^ twoOrder q :=
    one_lt_pow₀ (by norm_num : (1 : ℕ) < 2) hord.ne'
  have hsub : 0 < 2 ^ twoOrder q - 1 := Nat.sub_pos_iff_lt.mpr hpow
  have hle : q ≤ 2 ^ twoOrder q - 1 := Nat.le_of_dvd hsub hdvd
  omega

/-- The moduli occurring in Romanoff's Euler-product expansion are odd and
squarefree. -/
def IsRomanoffModulus (q : ℕ) : Prop := Squarefree q ∧ Odd q

noncomputable local instance instDecidableIsRomanoffModulus (q : ℕ) :
    Decidable (IsRomanoffModulus q) := Classical.propDecidable _

/-- The unweighted coefficient in the Romanoff series.  It is extended by
zero away from odd squarefree moduli. -/
noncomputable def romanoffCoeff (q : ℕ) : ℝ :=
  if IsRomanoffModulus q then 1 / (q.totient : ℝ) else 0

/-- The summand in the Romanoff series. -/
noncomputable def romanoffTerm (q : ℕ) : ℝ :=
  romanoffCoeff q / (twoOrder q : ℝ)

theorem romanoffCoeff_nonneg (q : ℕ) : 0 ≤ romanoffCoeff q := by
  unfold romanoffCoeff
  split_ifs
  · positivity
  · exact le_rfl

theorem romanoffTerm_nonneg (q : ℕ) : 0 ≤ romanoffTerm q := by
  exact div_nonneg (romanoffCoeff_nonneg q) (by positivity)

theorem romanoffCoeff_eq_zero_of_not_modulus {q : ℕ}
    (hq : ¬ IsRomanoffModulus q) : romanoffCoeff q = 0 := by
  simp [romanoffCoeff, hq]

theorem romanoffTerm_eq_zero_of_not_modulus {q : ℕ}
    (hq : ¬ IsRomanoffModulus q) : romanoffTerm q = 0 := by
  simp [romanoffTerm, romanoffCoeff_eq_zero_of_not_modulus hq]

theorem romanoffCoeff_eq_inv_totient {q : ℕ}
    (hq : IsRomanoffModulus q) :
    romanoffCoeff q = 1 / (q.totient : ℝ) := by
  simp [romanoffCoeff, hq]

theorem romanoffTerm_eq_inv_mul {q : ℕ}
    (hq : IsRomanoffModulus q) :
    romanoffTerm q = 1 / ((q.totient : ℝ) * (twoOrder q : ℝ)) := by
  rw [romanoffTerm, romanoffCoeff_eq_inv_totient hq]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Odd moduli of order at most `X` form an explicitly finite set. -/
noncomputable def romanoffModuliUpToOrder (X : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ X)).filter fun q ↦
    IsRomanoffModulus q ∧ twoOrder q ≤ X

theorem mem_romanoffModuliUpToOrder_iff {X q : ℕ} :
    q ∈ romanoffModuliUpToOrder X ↔
      IsRomanoffModulus q ∧ twoOrder q ≤ X := by
  simp only [romanoffModuliUpToOrder, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun h ↦ h.2
  · intro h
    have hlt : q < 2 ^ twoOrder q := lt_two_pow_twoOrder h.1.2
    have hpow : 2 ^ twoOrder q ≤ 2 ^ X := Nat.pow_le_pow_right (by omega) h.2
    exact ⟨hlt.trans_le hpow, h⟩

end Erdos851
