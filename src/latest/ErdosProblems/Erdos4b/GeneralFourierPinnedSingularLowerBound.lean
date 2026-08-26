/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedSingularSeries
import ErdosProblems.Erdos4b.GeneralFourierSingularLowerBound

/-!
# A uniform positive lower bound for the literal finite pinned series

Small-prime factors are at least one. Every rough factor dominates
the generic factor, whose finite product is uniformly close to one.
The resulting bound is uniform in the pin and residual parameters.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem one_le_pinnedLocalFactor_of_small_prime
    {K w m p₀ : ℕ} (h : Fin K) (p : Nat.Primes) (hpw : p.val ≤ w)
    (hpp₀ : ¬p.val ∣ p₀) (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0) :
    1 ≤ pinnedLocalFactor h w m p₀ p := by
  have hzero : pinnedLocalMultiplicity h w m p₀ p = 0 := by
    rw [pinnedLocalMultiplicity, pinnedLocalForbiddenResidues_eq_empty_of_le_cutoff
      h p hpw hpp₀ hnum, Finset.card_empty]
  have hp0 : (0 : ℝ) < p.val := by exact_mod_cast p.property.pos
  have hp1 : (1 : ℝ) < p.val := by exact_mod_cast p.property.one_lt
  have hbase0 : 0 < 1 - (1 : ℝ) / p.val := sub_pos.mpr ((div_lt_one hp0).mpr hp1)
  have hbase1 : 1 - (1 : ℝ) / p.val ≤ 1 := sub_le_self _ (by positivity)
  simp only [pinnedLocalFactor, hzero, Nat.cast_zero, zero_div, sub_zero, one_mul]
  exact one_le_pow₀ ((one_le_inv₀ hbase0).mpr hbase1)

theorem norm_roughPinnedSingularFactor_le_literal
    {K w m p₀ Y : ℕ} (h : Fin K) (p : Nat.Primes) (hKw : K ≤ w)
    (hlarge : 2 * Fintype.card (PinnedShiftIndex h) ≤ w) (hpY : p.val ≤ Y)
    (hpp₀ : ¬p.val ∣ p₀) (hnum : (1 : ZMod p) - (m : ZMod p) * p₀ ≠ 0) :
    ‖roughDoubledFourierSingularFactor w (roughPinnedFourierEdges h w m p₀ Y)
      (truncatedPinnedFourierCompanion m Y) p‖ ≤ pinnedLocalFactor h w m p₀ p := by
  by_cases hwp : w < p.val
  · rw [roughDoubledFourierSingularFactor, if_pos hwp,
      roughPinnedFourierSingularFactor_eq_pinnedLocalFactor h p hKw hwp hpY hpp₀ hnum,
      Complex.norm_real, Real.norm_eq_abs]
    have hpos := pinnedLocalFactor_pos_of_multiplicity_lt h p
      ((pinnedLocalMultiplicity_le_two_card h p hKw hwp hpp₀ hnum).trans_lt
        (hlarge.trans_lt hwp))
    exact (abs_of_nonneg hpos.le).le
  · rw [roughDoubledFourierSingularFactor, if_neg hwp, norm_one]
    exact one_le_pinnedLocalFactor_of_small_prime h p (Nat.le_of_not_gt hwp) hpp₀ hnum

theorem generic_bound_le_pinnedSingularSeries
    {K w m p₀ Y : ℕ} (h : Fin K) (hm : 0 < m) (hp₀ : p₀.Prime)
    (hw : 14 * K + 1 ≤ w) (hYp₀ : Y < p₀)
    (hcop : (m * p₀ - 1).Coprime (primorial Y)) :
    2 - Real.exp (genericFourierSingularErrorBound (2 * (K - 1)) w) ≤
      pinnedSingularSeries h w m p₀ Y := by
  have hKw : K ≤ w := by omega
  have hlarge : 2 * Fintype.card (PinnedShiftIndex h) ≤ w := by
    rw [card_pinnedShiftIndex]
    omega
  have hcard : Fintype.card (PinnedShiftIndex h ⊕ PinnedShiftIndex h) = 2 * (K - 1) := by
    rw [Fintype.card_sum, card_pinnedShiftIndex, two_mul]
  have hcut : 7 * (Fintype.card (PinnedShiftIndex h ⊕ PinnedShiftIndex h) : ℝ) ≤ w := by
    have hn : 7 * Fintype.card (PinnedShiftIndex h ⊕ PinnedShiftIndex h) ≤ w := by
      rw [hcard]
      omega
    exact_mod_cast hn
  have hbound := generic_bound_le_norm_prod_roughDoubledFourierSingularFactor
    (roughPinnedFourierEdges h w m p₀ Y) (truncatedPinnedFourierCompanion m Y)
    (by omega : 0 < w) hcut (boundedFourierPrimes Y)
  rw [hcard, norm_prod] at hbound
  apply hbound.trans
  apply Finset.prod_le_prod (fun p hp ↦ norm_nonneg _)
  intro p hp
  have hpY := (mem_boundedFourierPrimes Y p).mp hp
  exact norm_roughPinnedSingularFactor_le_literal h p hKw hlarge hpY
    (pinnedResidual_not_dvd_prime hp₀ hYp₀ p hpY)
    (pinnedResidual_companion_numerator_ne_zero hm hp₀.pos hcop p hpY)

theorem exists_uniform_half_le_pinnedSingularSeries (K : ℕ) :
    ∃ W : ℕ, ∀ w ≥ W, ∀ (h : Fin K) (m p₀ Y : ℕ),
      0 < m → p₀.Prime → Y < p₀ → (m * p₀ - 1).Coprime (primorial Y) →
        (1 : ℝ) / 2 ≤ pinnedSingularSeries h w m p₀ Y := by
  obtain ⟨W, hW⟩ := exists_genericFourierSingularErrorBound_cutoff (2 * (K - 1))
  refine ⟨max (14 * K + 1) W, ?_⟩
  intro w hw h m p₀ Y hm hp₀ hYp₀ hcop
  have hbound := generic_bound_le_pinnedSingularSeries h hm hp₀
    ((le_max_left _ _).trans hw) hYp₀ hcop
  have herror := (hW w ((le_max_right _ _).trans hw)).2.2
  linarith

end

end Erdos4b
