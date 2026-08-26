/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedMultiplicity

/-!
# The finite literal pinned singular series

Residual coprimality proves that the pinned companion value is nonzero
modulo every prime in the finite product. All factors are positive once
the pre-sieve cutoff exceeds twice the number of unpinned coordinates.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem card_pinnedShiftIndex {K : ℕ} (h : Fin K) :
    Fintype.card (PinnedShiftIndex h) = K - 1 := by
  simpa only [Fintype.card_fin, Fintype.card_subtype_eq] using!
    Fintype.card_subtype_compl (fun i : Fin K ↦ i = h)

theorem pinnedResidual_not_dvd_prime
    {p₀ Y : ℕ} (hp₀ : p₀.Prime) (hYp₀ : Y < p₀) (p : Nat.Primes) (hpY : p.val ≤ Y) :
    ¬p.val ∣ p₀ := by
  intro hdiv
  have heq := (hp₀.dvd_iff_eq p.property.ne_one).mp hdiv
  omega

theorem pinnedResidual_companion_numerator_ne_zero
    {m p₀ Y : ℕ} (hm : 0 < m) (hp₀ : 0 < p₀)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) (p : Nat.Primes) (hpY : p.val ≤ Y) :
    (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0 := by
  have hdivP := p.property.dvd_primorial_iff.mpr hpY
  have hnot : ¬p.val ∣ m * p₀ - 1 :=
    (p.property.coprime_iff_not_dvd).mp (hcop.of_dvd_right hdivP).symm
  have hprod : 1 ≤ m * p₀ := Nat.succ_le_iff.mpr (Nat.mul_pos hm hp₀)
  intro hz
  apply hnot
  apply (ZMod.natCast_eq_zero_iff (m * p₀ - 1) p).mp
  rw [Nat.cast_sub hprod, Nat.cast_mul, Nat.cast_one]
  exact sub_eq_zero.mpr (sub_eq_zero.mp hz).symm

def pinnedSingularSeries {K : ℕ} (h : Fin K) (w m p₀ Y : ℕ) : ℝ :=
  ∏ p ∈ boundedFourierPrimes Y, pinnedLocalFactor h w m p₀ p

theorem pinnedLocalMultiplicity_le_two_card
    {K w m p₀ : ℕ} (h : Fin K) (p : Nat.Primes) (hKw : K ≤ w) (hwp : w < p)
    (hpp₀ : ¬p.val ∣ p₀) (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0) :
    pinnedLocalMultiplicity h w m p₀ p ≤ 2 * Fintype.card (PinnedShiftIndex h) := by
  have hc := pinnedLocalMultiplicity_add_FourierExceptionalCount h p hKw hwp hpp₀ hnum
  omega

theorem pinnedLocalFactor_pos_of_multiplicity_lt
    {K w m p₀ : ℕ} (h : Fin K) (p : Nat.Primes)
    (hcount : pinnedLocalMultiplicity h w m p₀ p < p.val) :
    0 < pinnedLocalFactor h w m p₀ p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
  unfold pinnedLocalFactor
  apply mul_pos
  · exact sub_pos.mpr ((div_lt_one hp0).mpr (by exact_mod_cast hcount))
  · apply pow_pos
    exact inv_pos.mpr (sub_pos.mpr ((div_lt_one hp0).mpr hp1))

theorem pinnedSingularSeries_pos
    {K w m p₀ Y : ℕ} (h : Fin K) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hYp₀ : Y < p₀) (hKw : K ≤ w) (hlarge : 2 * Fintype.card (PinnedShiftIndex h) ≤ w)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) :
    0 < pinnedSingularSeries h w m p₀ Y := by
  apply Finset.prod_pos
  intro p hp
  have hpY := (mem_boundedFourierPrimes Y p).mp hp
  have hnot := pinnedResidual_not_dvd_prime hp₀ hYp₀ p hpY
  have hnum := pinnedResidual_companion_numerator_ne_zero hm hp₀.pos hcop p hpY
  apply pinnedLocalFactor_pos_of_multiplicity_lt h p
  by_cases hpw : p.val ≤ w
  · rw [pinnedLocalMultiplicity, pinnedLocalForbiddenResidues_eq_empty_of_le_cutoff
      h p hpw hnot hnum, Finset.card_empty]
    exact p.property.pos
  · have hwp : w < p.val := Nat.lt_of_not_ge hpw
    exact (pinnedLocalMultiplicity_le_two_card h p hKw hwp hnot hnum).trans_lt
      (hlarge.trans_lt hwp)

end

end Erdos4b
