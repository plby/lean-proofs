/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.RadiusSixDerivative

/-!
# Splitting the radius-six reciprocal zero sum

This file combines the local disk, the dyadic annuli, and the remaining far
part of the radius-six divisor.  All identities are finite `Finsupp`
identities; no convergence argument is involved.
-/

namespace Erdos48

open Complex Metric

noncomputable section

/-- Choose the last dyadic multiple of `r` which does not exceed one. -/
theorem exists_dyadic_scale_le_one {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∃ N : ℕ,
      r * (2 : ℝ) ^ N ≤ 1 ∧
        (1 / 2 : ℝ) < r * (2 : ℝ) ^ N := by
  have H : ∃ n : ℕ, 1 < r * (2 : ℝ) ^ n := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr0
      (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, ?_⟩
    have hpow : 0 < (2 : ℝ) ^ n := by positivity
    have hrewrite : ((1 / 2 : ℝ) ^ n) * (2 : ℝ) ^ n = 1 := by
      rw [one_div_pow]
      field_simp
    nlinarith
  let n := Nat.find H
  have hnSpec : 1 < r * (2 : ℝ) ^ n := Nat.find_spec H
  have hn0 : n ≠ 0 := by
    intro hn
    have : 1 < r := by simpa only [hn, pow_zero, mul_one] using hnSpec
    exact (not_lt_of_ge hr1) this
  let N := n - 1
  have hNn : N < n := by
    dsimp [N]
    omega
  have hupper : r * (2 : ℝ) ^ N ≤ 1 := by
    exact le_of_not_gt (Nat.find_min H hNn)
  have hnEq : n = N + 1 := by
    dsimp [N]
    omega
  refine ⟨N, hupper, ?_⟩
  rw [hnEq, pow_succ] at hnSpec
  nlinarith

/-- A reciprocal-power sum over points farther than `R` is bounded by total
multiplicity divided by `R^j`. -/
theorem norm_sum_farTail_div_pow_le
    (Z : ℂ →₀ ℕ) (z : ℂ) {R : ℝ} (hR : 0 < R) (j : ℕ) :
    ‖∑ rho ∈ Z.support.filter (fun rho ↦ R < dist rho z),
        (Z rho : ℂ) / (z - rho) ^ j‖ ≤
      Z.sum (fun _ m ↦ (m : ℝ)) / R ^ j := by
  calc
    ‖∑ rho ∈ Z.support.filter (fun rho ↦ R < dist rho z),
        (Z rho : ℂ) / (z - rho) ^ j‖ ≤
        ∑ rho ∈ Z.support.filter (fun rho ↦ R < dist rho z),
          ‖(Z rho : ℂ) / (z - rho) ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ rho ∈ Z.support.filter (fun rho ↦ R < dist rho z),
          (Z rho : ℝ) / R ^ j := by
      apply Finset.sum_le_sum
      intro rho hrho
      rw [Finset.mem_filter] at hrho
      rw [norm_div, norm_pow, norm_natCast]
      have hdist : R ≤ ‖z - rho‖ := by
        simpa [dist_eq_norm, norm_sub_rev] using hrho.2.le
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        (pow_pos hR _) (pow_le_pow_left₀ hR.le hdist j)
    _ = (∑ rho ∈ Z.support.filter (fun rho ↦ R < dist rho z),
          (Z rho : ℝ)) / R ^ j := by rw [Finset.sum_div]
    _ ≤ Z.sum (fun _ m ↦ (m : ℝ)) / R ^ j := by
      apply div_le_div_of_nonneg_right
      · rw [Finsupp.sum]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun _ _ _ ↦ Nat.cast_nonneg _)
      · positivity

/-- The small-disk zero `Finsupp` is exactly the restriction of the
radius-six zero `Finsupp` to the radius-`4*eta` disk. -/
theorem smallDiskZeroFinsupp_eq_radiusSix_restrict
    {q : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t eta : ℝ) (heta0 : 0 < eta) (heta1 : eta ≤ 1) (rho : ℂ) :
    smallDiskZeroFinsupp hq chi hchi t eta rho =
      if dist rho (((1 + eta : ℝ) : ℂ) + t * I) ≤ 4 * eta then
        radiusSixZeroFinsupp hq chi hchi t rho
      else 0 := by
  rw [smallDiskZeroFinsupp_apply, smallDiskZeroMultiplicity]
  split
  next hsmall =>
    rw [radiusSixZeroFinsupp_apply, radiusSixZeroMultiplicity]
    have hcenters :
        dist (((1 + eta : ℝ) : ℂ) + t * I) ((2 : ℂ) + t * I) =
          1 - eta := by
      rw [Complex.dist_eq]
      have heq :
          (((1 + eta : ℝ) : ℂ) + t * I) - ((2 : ℂ) + t * I) =
            ((eta - 1 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonpos (by linarith)]
      ring
    have hfull : dist rho ((2 : ℂ) + t * I) ≤ 6 := by
      calc
        dist rho ((2 : ℂ) + t * I) ≤
            dist rho (((1 + eta : ℝ) : ℂ) + t * I) +
              dist (((1 + eta : ℝ) : ℂ) + t * I) ((2 : ℂ) + t * I) :=
          dist_triangle _ _ _
        _ ≤ 4 * eta + (1 - eta) := add_le_add hsmall hcenters.le
        _ ≤ 6 := by linarith
    rw [if_pos hfull]
  next hsmall => rfl

/-- Subtracting the local reciprocal-power sum from the radius-six sum
leaves exactly the points outside the local disk. -/
theorem radiusSix_sum_sub_smallDisk_sum_eq_outside
    {q j : ℕ} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter ℂ q) (hchi : chi.IsPrimitive)
    (t eta : ℝ) (heta0 : 0 < eta) (heta1 : eta ≤ 1) :
    let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
    let D := radiusSixZeroFinsupp hq chi hchi t
    let Z := smallDiskZeroFinsupp hq chi hchi t eta
    D.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j) -
        Z.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j) =
      ∑ rho ∈ D.support.filter (fun rho ↦ 4 * eta < dist rho z),
        (D rho : ℂ) / (z - rho) ^ j := by
  dsimp only
  let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let D := radiusSixZeroFinsupp hq chi hchi t
  let Z := smallDiskZeroFinsupp hq chi hchi t eta
  rw [Finsupp.sum, Finsupp.sum]
  have hZsub : Z.support ⊆ D.support := by
    intro rho hrho
    rw [Finsupp.mem_support_iff] at hrho ⊢
    have heq := smallDiskZeroFinsupp_eq_radiusSix_restrict
      hq chi hchi t eta heta0 heta1 rho
    by_cases hsmall : dist rho z ≤ 4 * eta
    · have hZD : Z rho = D rho := by
        simpa only [Z, D, z, hsmall, if_true] using heq
      intro hDzero
      exact hrho (hZD.trans hDzero)
    · have : Z rho = 0 := by
        simpa only [Z, D, z, hsmall, if_false] using heq
      exact False.elim (hrho this)
  have hZsum :
      (∑ rho ∈ Z.support, (Z rho : ℂ) / (z - rho) ^ j) =
        ∑ rho ∈ D.support, (Z rho : ℂ) / (z - rho) ^ j := by
    apply Finset.sum_subset hZsub
    intro rho hrhoD hrhoZ
    have hZzero : Z rho = 0 := by
      simpa only [Finsupp.mem_support_iff, not_not] using hrhoZ
    simp [hZzero]
  rw [hZsum]
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ rho ∈ D.support,
        ((D rho : ℂ) / (z - rho) ^ j -
          (Z rho : ℂ) / (z - rho) ^ j)) =
        ∑ rho ∈ D.support,
          if 4 * eta < dist rho z then
            (D rho : ℂ) / (z - rho) ^ j else 0 := by
      apply Finset.sum_congr rfl
      intro rho hrho
      have heq := smallDiskZeroFinsupp_eq_radiusSix_restrict
        hq chi hchi t eta heta0 heta1 rho
      by_cases hsmall : dist rho z ≤ 4 * eta
      · have hZD : Z rho = D rho := by
          simpa only [Z, D, z, hsmall, if_true] using heq
        rw [if_neg (not_lt.mpr hsmall), hZD]
        ring
      · have hZzero : Z rho = 0 := by
          simpa only [Z, D, z, hsmall, if_false] using heq
        rw [if_pos (lt_of_not_ge hsmall), hZzero]
        simp
    _ = ∑ rho ∈ D.support.filter (fun rho ↦ 4 * eta < dist rho z),
        (D rho : ℂ) / (z - rho) ^ j := by
      rw [Finset.sum_filter]

/-- Split the outside-local part at an arbitrary radius `R`. -/
theorem sum_outside_eq_annular_add_far
    (Z : ℂ →₀ ℕ) (z : ℂ) {r R : ℝ} (hrR : r ≤ R) (j : ℕ) :
    (∑ rho ∈ Z.support.filter (fun rho ↦ r < dist rho z),
        (Z rho : ℂ) / (z - rho) ^ j) =
      (∑ rho ∈ Z.support.filter (fun rho ↦
          r < dist rho z ∧ dist rho z ≤ R),
        (Z rho : ℂ) / (z - rho) ^ j) +
      ∑ rho ∈ Z.support.filter (fun rho ↦ R < dist rho z),
        (Z rho : ℂ) / (z - rho) ^ j := by
  classical
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hr : r < dist rho z
  · by_cases hR : dist rho z ≤ R
    · simp [hr, hR, not_lt.mpr hR]
    · simp [hr, hR, lt_of_not_ge hR]
  · by_cases hR : R < dist rho z
    · exact False.elim (hr (hrR.trans_lt hR))
    · simp [hr, hR]

/-- Uniform bound for the contribution of every radius-six zero outside the
detector disk.  The first two terms are the dyadic annuli and the last term
is the fixed-distance tail. -/
theorem exists_norm_radiusSix_sub_smallDisk_powerSum_le :
    ∃ Aₗ Aₑ : ℕ, 37 ≤ Aₗ ∧ 37 ≤ Aₑ ∧
      ∀ (q : ℕ) [NeZero q], ∀ (hq : 1 < q),
        ∀ (chi : DirichletCharacter ℂ q), ∀ (hchi : chi.IsPrimitive),
          ∀ (t eta : ℝ), 0 < eta → eta ≤ 1 / 8 →
            ∀ j : ℕ, 2 ≤ j →
              let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
              let D := radiusSixZeroFinsupp hq chi hchi t
              let Z := smallDiskZeroFinsupp hq chi hchi t eta
              ‖D.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j) -
                  Z.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j)‖ ≤
                64 * (Real.log 4 + 4) / (4 * eta) ^ j +
                  ((1024 * (Aₗ : ℝ) / 3) *
                    Real.log ((q : ℝ) * (|t| + 2))) /
                      (4 * eta) ^ (j - 1) +
                  (2 * (Aₑ : ℝ) *
                    Real.log ((q : ℝ) * (|t| + 2))) /
                      (1 / 2 : ℝ) ^ j := by
  obtain ⟨Aₗ, hAₗ, hlocal⟩ :=
    exists_dyadicAnnularShell_radiusSix_mass_bound
  obtain ⟨Aₑ, hAₑ, hfull⟩ := exists_radiusSixZeroFinsupp_mass_bound
  refine ⟨Aₗ, Aₑ, hAₗ, hAₑ, ?_⟩
  intro q _ hq chi hchi t eta heta0 heta8 j hj
  dsimp only
  let z : ℂ := ((1 + eta : ℝ) : ℂ) + t * I
  let D := radiusSixZeroFinsupp hq chi hchi t
  let Z := smallDiskZeroFinsupp hq chi hchi t eta
  let r : ℝ := 4 * eta
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by dsimp [r]; linarith
  obtain ⟨N, hRN, hRhalf⟩ := exists_dyadic_scale_le_one hr0 hr1
  let R : ℝ := r * (2 : ℝ) ^ N
  have hR0 : 0 < R := by positivity
  have hrR : r ≤ R := by
    dsimp [R]
    have hone : (1 : ℝ) ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
    simpa using mul_le_mul_of_nonneg_left hone hr0.le
  have hB4 : (4 : ℝ) ≤ (q : ℝ) * (|t| + 2) := by
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
    have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    nlinarith
  have hlog : 0 ≤ Real.log ((q : ℝ) * (|t| + 2)) :=
    Real.log_nonneg (by linarith)
  have hnear :
      ‖∑ rho ∈ D.support.filter (fun rho ↦
            r < dist rho z ∧ dist rho z ≤ R),
          (D rho : ℂ) / (z - rho) ^ j‖ ≤
        64 * (Real.log 4 + 4) / r ^ j +
          ((1024 * (Aₗ : ℝ) / 3) *
            Real.log ((q : ℝ) * (|t| + 2))) / r ^ (j - 1) := by
    have hann := norm_sum_annularTail_div_pow_le_of_affine_mass
      D z hr0 (by positivity : 0 ≤ 32 * (Real.log 4 + 4))
      (mul_nonneg (by positivity : 0 ≤ 256 * (Aₗ : ℝ) / 3) hlog)
      N j hj (by
        intro k hk
        apply hlocal q hq chi hchi t eta r heta0
          (by dsimp [r]; linarith) k
        have hkN : k + 1 ≤ N := by omega
        exact (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by norm_num) hkN) hr0.le).trans hRN)
    change ‖∑ rho ∈ D.support.filter (fun rho ↦
          r < dist rho z ∧ dist rho z ≤ r * (2 : ℝ) ^ N),
        (D rho : ℂ) / (z - rho) ^ j‖ ≤ _ at hann
    rw [show R = r * (2 : ℝ) ^ N by rfl]
    calc
      ‖∑ rho ∈ D.support.filter (fun rho ↦
            r < dist rho z ∧ dist rho z ≤ R),
          (D rho : ℂ) / (z - rho) ^ j‖ ≤
          2 * (32 * (Real.log 4 + 4)) / r ^ j +
            4 * ((256 * (Aₗ : ℝ) / 3) *
              Real.log ((q : ℝ) * (|t| + 2))) / r ^ (j - 1) := hann
      _ = _ := by ring
  have hfar :
      ‖∑ rho ∈ D.support.filter (fun rho ↦ R < dist rho z),
          (D rho : ℂ) / (z - rho) ^ j‖ ≤
        (2 * (Aₑ : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) /
          (1 / 2 : ℝ) ^ j := by
    have hraw := norm_sum_farTail_div_pow_le D z hR0 j
    have hmass := hfull q hq chi hchi t
    have hnum : 0 ≤
        2 * (Aₑ : ℝ) * Real.log ((q : ℝ) * (|t| + 2)) := by
      positivity
    calc
      ‖∑ rho ∈ D.support.filter (fun rho ↦ R < dist rho z),
          (D rho : ℂ) / (z - rho) ^ j‖ ≤
          D.sum (fun _ m ↦ (m : ℝ)) / R ^ j := hraw
      _ ≤ (2 * (Aₑ : ℝ) *
          Real.log ((q : ℝ) * (|t| + 2))) / R ^ j :=
        div_le_div_of_nonneg_right hmass (by positivity)
      _ ≤ (2 * (Aₑ : ℝ) *
          Real.log ((q : ℝ) * (|t| + 2))) / (1 / 2 : ℝ) ^ j := by
        exact div_le_div_of_nonneg_left hnum (by positivity)
          (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2)
            hRhalf.le j)
  have hdiff := radiusSix_sum_sub_smallDisk_sum_eq_outside
    hq chi hchi t eta heta0 (by linarith : eta ≤ 1) (j := j)
  have hsplit := sum_outside_eq_annular_add_far D z hrR j
  change D.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j) -
      Z.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j) =
        ∑ rho ∈ D.support.filter (fun rho ↦ r < dist rho z),
          (D rho : ℂ) / (z - rho) ^ j at hdiff
  rw [hdiff, hsplit]
  calc
    ‖(∑ rho ∈ D.support.filter (fun rho ↦
          r < dist rho z ∧ dist rho z ≤ R),
        (D rho : ℂ) / (z - rho) ^ j) +
      ∑ rho ∈ D.support.filter (fun rho ↦ R < dist rho z),
        (D rho : ℂ) / (z - rho) ^ j‖ ≤
        ‖∑ rho ∈ D.support.filter (fun rho ↦
          r < dist rho z ∧ dist rho z ≤ R),
            (D rho : ℂ) / (z - rho) ^ j‖ +
          ‖∑ rho ∈ D.support.filter (fun rho ↦ R < dist rho z),
            (D rho : ℂ) / (z - rho) ^ j‖ := norm_add_le _ _
    _ ≤ (64 * (Real.log 4 + 4) / r ^ j +
          ((1024 * (Aₗ : ℝ) / 3) *
            Real.log ((q : ℝ) * (|t| + 2))) / r ^ (j - 1)) +
        (2 * (Aₑ : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) /
          (1 / 2 : ℝ) ^ j := add_le_add hnear hfar
    _ = _ := by rfl

end

end Erdos48
