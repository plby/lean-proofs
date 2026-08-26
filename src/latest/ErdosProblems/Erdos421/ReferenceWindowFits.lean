import ErdosProblems.Erdos421.ReferenceCutoffGeometry
import ErdosProblems.Erdos421.OuterPrimeReciprocalSaving

/-! # The actual parent and cofactor windows satisfy every reference hypothesis -/

namespace Erdos421

open Filter Topology

structure ReferenceWindowFits (X x : ℝ) (N z : ℕ) (δ : ℝ) : Prop where
  scale : X ^ (9 / 20 : ℝ) ≤ x
  cutoff : 2 ≤ z
  square : (z : ℝ) ^ 2 ≤ x
  power : (1 + δ) * x ≤ (z : ℝ) ^ 6
  support : (1 + δ) * x ≤ (N : ℝ) + 1

theorem eventually_reference_window_fits :
    ∀ᶠ X : ℕ in atTop, (intermediatePrimeCutoff X : ℝ) ≤ X ∧
      ∀ x : ℝ, (X : ℝ) ≤ x → x ≤ 2 * X → ∀ δ : ℝ, δ ≤ 1 / 2 →
        ReferenceWindowFits X x (3 * X) (intermediatePrimeCutoff X) δ ∧
        Real.log x / Real.log (intermediatePrimeCutoff X) ∈ Set.Icc (5 / 2 : ℝ) 6 ∧
        ∀ p ∈ sievePrimes (intermediatePrimeCutoff X) (outerPrimeCutoff X),
          ReferenceWindowFits X (x / p) (3 * X / p) (intermediatePrimeCutoff X) δ ∧
          2 ≤ Real.log (x / p) / Real.log (intermediatePrimeCutoff X) := by
  filter_upwards [eventually_intermediate_cutoff_bound, eventually_outer_cutoff_bound,
    eventually_intermediate_power_dominates, eventually_intermediate_cutoff_large 2,
    eventually_ge_atTop 2] with X hZ hQ hdom hlarge hX
  have hX1 : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hXp : (0 : ℝ) < X := by linarith
  have hz2 : 2 ≤ intermediatePrimeCutoff X := by exact_mod_cast hlarge.1
  have hZ1 : (1 : ℝ) < intermediatePrimeCutoff X :=
    by exact_mod_cast (show 1 < intermediatePrimeCutoff X by omega)
  have hZp : (0 : ℝ) < intermediatePrimeCutoff X := by linarith
  have hLZ := Real.log_pos hZ1
  have hZpow : (3 : ℝ) * X ≤ (intermediatePrimeCutoff X : ℝ) ^ 6 := by exact_mod_cast hdom.le
  have hZsq := intermediate_square_le_reference_scale hX1.le hZ
  have hscale : (X : ℝ) ^ (9 / 20 : ℝ) ≤ X :=
    Real.rpow_le_self_of_one_le hX1.le (by norm_num)
  refine ⟨hZ.trans (Real.rpow_le_self_of_one_le hX1.le (by norm_num)), ?_⟩
  intro x hXx hxX δ hδ
  have hxp : 0 < x := hXp.trans_le hXx
  have hparent := reference_parent_endpoint hxp.le hxX hδ
  have hsupport : (1 + δ) * x ≤ ((3 * X : ℕ) : ℝ) + 1 := by
    push_cast
    linarith
  refine ⟨⟨hscale.trans hXx, hz2, hZsq.trans (hscale.trans hXx),
    hparent.trans hZpow, hsupport⟩,
    reference_main_argument_range hX1 hXx hxX hz2 hZ hZpow, ?_⟩
  intro p hp
  obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, hpQ⟩ := Finset.mem_Ico.mp hpI
  have hpr : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
  have hpbound : (p : ℝ) ≤ (X : ℝ) ^ (51 / 100 : ℝ) :=
    (show (p : ℝ) ≤ outerPrimeCutoff X by exact_mod_cast hpQ.le).trans hQ
  have hcscale := reference_cofactor_scale_lower hX1.le hXx hpr hpbound
  have hcsq := hZsq.trans hcscale
  have hcend : (1 + δ) * (x / p) ≤ (3 * X : ℝ) / p := by
    calc
      _ = ((1 + δ) * x) / p := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hparent hpr.le
  have hcpow : (1 + δ) * (x / p) ≤ (intermediatePrimeCutoff X : ℝ) ^ 6 :=
    (hcend.trans (div_le_self (by positivity) hp1)).trans hZpow
  have hdiv := nat_div_real_lt_add_one (3 * X) hpp.pos
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hdiv
  have hcsupport : (1 + δ) * (x / p) ≤ ((3 * X / p : ℕ) : ℝ) + 1 := hcend.trans hdiv.le
  have hlog := Real.log_le_log (pow_pos hZp 2) hcsq
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  exact ⟨⟨hcscale, hz2, hcsq, hcpow, hcsupport⟩, (le_div_iff₀ hLZ).mpr hlog⟩

end Erdos421
