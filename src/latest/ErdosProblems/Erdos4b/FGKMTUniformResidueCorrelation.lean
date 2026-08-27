/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTResidueCorrelation

/-! # The uniform correlation estimate at the logarithmic sieve cutoff -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

def residueSieveCutoff (x : ℕ) : ℕ := ⌊Real.log (x : ℝ) ^ 20⌋₊

theorem eventually_residueSieveCutoff_bounds :
    ∀ᶠ x : ℕ in atTop,
      2 ≤ Real.log (x : ℝ) ∧ 0 < residueSieveCutoff x ∧
      Real.log (x : ℝ) ^ 20 / 2 ≤ (residueSieveCutoff x : ℝ) ∧
      2 * Real.log (x : ℝ) ≤ (residueSieveCutoff x : ℝ) := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (2 : ℝ))] with x hL
  have hL1 : 1 ≤ Real.log (x : ℝ) := by linarith
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hfloor : Real.log (x : ℝ) ^ 20 / 2 < (residueSieveCutoff x : ℝ) :=
    Nat.div_two_lt_floor (one_le_pow₀ hL1)
  have hpos : 0 < residueSieveCutoff x := by
    have hp : (0 : ℝ) < residueSieveCutoff x :=
      (by positivity : (0 : ℝ) < Real.log (x : ℝ) ^ 20 / 2).trans hfloor
    exact_mod_cast hp
  have hsquare := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hL 2
  norm_num at hsquare
  have hcubic : 4 * Real.log (x : ℝ) ≤ Real.log (x : ℝ) ^ 3 := by
    nlinarith [mul_le_mul_of_nonneg_right hsquare hLpos.le]
  have hpower : Real.log (x : ℝ) ^ 3 ≤ Real.log (x : ℝ) ^ 20 :=
    pow_le_pow_right₀ hL1 (by norm_num)
  exact ⟨hL, hpos, hfloor.le, by linarith⟩

theorem eventually_uniform_residue_correlation {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ x : ℕ in atTop, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      ∀ N : Finset ℤ, (N.card : ℝ) ≤ Real.log (x : ℝ) →
      (∀ n ∈ N, |(n : ℝ)| ≤ (x : ℝ) ^ A) →
      |residueAvoidanceMass S N / residueSieveDensity S ^ N.card - 1| ≤
        48 * (A + 1) / Real.log (x : ℝ) ^ 16 := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_residueSieveCutoff_bounds, eventually_ge_atTop (2 : ℕ),
    hlog.eventually (eventually_ge_atTop (24 * (A + 1)))] with x hcut hx hthreshold
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast (by omega : 1 ≤ x)
  have hxpos : (0 : ℝ) < x := by linarith
  have hL1 : 1 ≤ Real.log (x : ℝ) := by linarith [hcut.1]
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hheight : 1 ≤ (x : ℝ) ^ A := Real.one_le_rpow hxR hA
  have hlogH : Real.log (2 * (x : ℝ) ^ A) ≤ (A + 1) * Real.log (x : ℝ) := by
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hxpos A).ne', Real.log_rpow hxpos]
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hpow : 24 * (A + 1) ≤ Real.log (x : ℝ) ^ 16 := hthreshold.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 16))
  have hsmall : 24 * (A + 1) / Real.log (x : ℝ) ^ 16 ≤ 1 :=
    (div_le_one (by positivity : 0 < Real.log (x : ℝ) ^ 16)).mpr hpow
  intro S hS hSrough N ht hN
  by_cases hEmpty : N = ∅
  · subst N
    have hmass : residueAvoidanceMass S ∅ = 1 := by
      rw [residueAvoidanceMass_eq_prod (fun p hp => (hS p hp).pos)]
      simp [occupiedResidues]
    rw [hmass, Finset.card_empty, pow_zero, div_one, sub_self, abs_zero]
    positivity
  have hrough (p : ℕ) (hp : p ∈ S) : residueSieveCutoff x < p := by
    have hf : (residueSieveCutoff x : ℝ) ≤ Real.log (x : ℝ) ^ 20 :=
      Nat.floor_le (by positivity)
    exact_mod_cast hf.trans_lt (hSrough p hp)
  have hsize : 2 * N.card ≤ residueSieveCutoff x := by
    have hh := (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2)).trans hcut.2.2.2
    exact_mod_cast hh
  have hcard : 1 ≤ N.card := Nat.succ_le_iff.mpr
    (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hEmpty))
  have hE := residueCorrelationError_le_logSaving hA hL1 hcut.2.2.1 ht hheight hlogH
  have hcor := residueAvoidance_ratio_error hcut.2.1 hS hrough hcard hsize hheight hN
    (hE.trans hsmall)
  calc
    _ ≤ 2 * residueCorrelationError (residueSieveCutoff x) N.card ((x : ℝ) ^ A) := hcor
    _ ≤ 2 * (24 * (A + 1) / Real.log (x : ℝ) ^ 16) :=
      mul_le_mul_of_nonneg_left hE (by norm_num)
    _ = _ := by ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_residueSieveCutoff_bounds
#print axioms Erdos4b.FGKMT.eventually_uniform_residue_correlation
