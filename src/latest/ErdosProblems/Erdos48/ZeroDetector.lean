/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.RegularizedDerivative
import ErdosProblems.Erdos48.TuranSecond

/-!
# Reciprocal zero detectors

This file turns the consecutive power-sum theorem into the form used for
zeros in a disk and records the exact high-derivative formula for a finite
sum of logarithmic poles.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

/-- Exact formula for a high derivative of a finite weighted sum of simple
poles. -/
theorem iteratedDeriv_weighted_inv_sub_sum
    {K k : ℕ} (b rho : Fin K → ℂ) {z : ℂ}
    (hne : ∀ j, z ≠ rho j) :
    iteratedDeriv k (fun s : ℂ ↦ ∑ j, b j / (s - rho j)) z =
      (-1 : ℂ) ^ k * k.factorial *
        ∑ j, b j / (z - rho j) ^ (k + 1) := by
  rw [iteratedDeriv_fun_sum]
  · simp_rw [div_eq_mul_inv, iteratedDeriv_const_mul_field]
    have hinv := iter_deriv_inv_linear_sub (𝕜 := ℂ) k 1
    simp only [one_mul, one_pow] at hinv
    have hterm (j : Fin K) :
        iteratedDeriv k (fun s : ℂ ↦ (s - rho j)⁻¹) z =
          (-1 : ℂ) ^ k * (k.factorial : ℂ) *
            (z - rho j) ^ (-1 - (k : ℤ)) := by
      simpa [iteratedDeriv_eq_iterate] using congrFun (hinv (rho j)) z
    simp_rw [hterm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hexp : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) := by omega
    rw [hexp, zpow_neg, zpow_natCast]
    push_cast
    ring
  · intro j hj
    exact (contDiffAt_const.mul
      ((contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr (hne j))))

/-- A disk-normalized, separation-free reciprocal power-sum detector.  The
weights may be arbitrary complex numbers; divisor multiplicities are the
important nonnegative-real specialization. -/
theorem exists_large_reciprocalPowerSum
    {K M : ℕ} (hK : 0 < K) (b rho : Fin K → ℂ)
    {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hinside : ∀ j, dist (rho j) z ≤ r)
    (hne : ∀ j, z ≠ rho j) :
    ∃ ν ∈ Finset.Icc (M + 1) (M + K),
      ‖∑ j, b j‖ ≤
        (K : ℝ) *
          (2 * ((2 : ℝ) ^ (M + K) *
            ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K))) *
          r ^ ν * ‖∑ j, b j / (z - rho j) ^ ν‖ := by
  let w : Fin K → ℂ := fun j ↦ (r : ℂ) / (z - rho j)
  have hw : ∀ j, 1 ≤ ‖w j‖ := by
    intro j
    rw [show ‖w j‖ = r / ‖z - rho j‖ by
      simp only [w, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]]
    have hdenpos : 0 < ‖z - rho j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hne j))
    rw [one_le_div hdenpos]
    simpa [dist_eq_norm, norm_sub_rev] using hinside j
  obtain ⟨ν, hν, hlarge⟩ :=
    exists_large_consecutive_powerSum_of_one_le_norm hK w b hw
  refine ⟨ν, hν, ?_⟩
  calc
    ‖∑ j, b j‖ ≤
        (K : ℝ) *
          (2 * ((2 : ℝ) ^ (M + K) *
            ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K))) *
          ‖∑ j, b j * w j ^ ν‖ := hlarge
    _ = (K : ℝ) *
          (2 * ((2 : ℝ) ^ (M + K) *
            ((K + 1 : ℝ) * (2 : ℝ) ^ K * (2 : ℝ) ^ K))) *
          r ^ ν * ‖∑ j, b j / (z - rho j) ^ ν‖ := by
      have hsum : (∑ j, b j * w j ^ ν) =
          (r : ℂ) ^ ν * ∑ j, b j / (z - rho j) ^ ν := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [w]
        rw [div_pow]
        ring
      rw [hsum, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr]
      ring

/-- Finset-indexed form of `exists_large_reciprocalPowerSum`. -/
theorem exists_large_reciprocalPowerSum_finset
    {M : ℕ} {S : Finset ℂ} (hS : S.Nonempty) (b : ℂ → ℂ)
    {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hinside : ∀ rho ∈ S, dist rho z ≤ r)
    (hne : ∀ rho ∈ S, z ≠ rho) :
    ∃ ν ∈ Finset.Icc (M + 1) (M + S.card),
      ‖∑ rho ∈ S, b rho‖ ≤
        (S.card : ℝ) *
          (2 * ((2 : ℝ) ^ (M + S.card) *
            ((S.card + 1 : ℝ) * (2 : ℝ) ^ S.card *
              (2 : ℝ) ^ S.card))) *
          r ^ ν * ‖∑ rho ∈ S, b rho / (z - rho) ^ ν‖ := by
  let e : S ≃ Fin S.card := S.equivFin
  let rho' : Fin S.card → ℂ := fun j ↦ (e.symm j : ℂ)
  let b' : Fin S.card → ℂ := fun j ↦ b (e.symm j : ℂ)
  have hcard : 0 < S.card := Finset.card_pos.mpr hS
  have hinside' : ∀ j, dist (rho' j) z ≤ r := by
    intro j
    exact hinside (e.symm j) (e.symm j).2
  have hne' : ∀ j, z ≠ rho' j := by
    intro j
    exact hne (e.symm j) (e.symm j).2
  obtain ⟨ν, hν, hlarge⟩ :=
    exists_large_reciprocalPowerSum hcard b' rho' hr hinside' hne'
  refine ⟨ν, hν, ?_⟩
  have hsum_b : (∑ j, b' j) = ∑ rho ∈ S, b rho := by
    calc
      (∑ j, b' j) = ∑ rho : S, b (rho : ℂ) := by
        simpa only [b'] using e.symm.sum_comp (fun rho : S ↦ b (rho : ℂ))
      _ = ∑ rho ∈ S, b rho := by
        exact (Finset.sum_subtype S (by simp) b).symm
  have hsum_power : (∑ j, b' j / (z - rho' j) ^ ν) =
      ∑ rho ∈ S, b rho / (z - rho) ^ ν := by
    calc
      (∑ j, b' j / (z - rho' j) ^ ν) =
          ∑ rho : S, b (rho : ℂ) / (z - (rho : ℂ)) ^ ν := by
        simpa only [b', rho'] using e.symm.sum_comp
          (fun rho : S ↦ b (rho : ℂ) / (z - (rho : ℂ)) ^ ν)
      _ = ∑ rho ∈ S, b rho / (z - rho) ^ ν := by
        exact (Finset.sum_subtype S (by simp)
          (fun rho ↦ b rho / (z - rho) ^ ν)).symm
  simpa only [hsum_b, hsum_power] using hlarge

/-- A finite-support version of the high-derivative pole identity. -/
theorem iteratedDeriv_weighted_inv_sub_finsum
    {k : ℕ} (b : ℂ → ℂ) (hb : (Function.support b).Finite)
    {z : ℂ} (hne : ∀ rho ∈ Function.support b, z ≠ rho) :
    iteratedDeriv k (fun s : ℂ ↦ ∑ᶠ rho : ℂ, b rho / (s - rho)) z =
      (-1 : ℂ) ^ k * k.factorial *
        ∑ᶠ rho : ℂ, b rho / (z - rho) ^ (k + 1) := by
  let S : Finset ℂ := hb.toFinset
  have hsupport : Function.support b ⊆ (S : Set ℂ) := by
    simpa only [S, hb.coe_toFinset] using (Set.Subset.rfl :
      Function.support b ⊆ Function.support b)
  have hfun : (fun s : ℂ ↦ ∑ᶠ rho : ℂ, b rho / (s - rho)) =
      (fun s : ℂ ↦ ∑ rho ∈ S, b rho / (s - rho)) := by
    funext s
    apply finsum_eq_sum_of_support_subset
    intro rho hrho
    apply hsupport
    intro hbzero
    simp [hbzero] at hrho
  have hright : (∑ᶠ rho : ℂ, b rho / (z - rho) ^ (k + 1)) =
      ∑ rho ∈ S, b rho / (z - rho) ^ (k + 1) := by
    apply finsum_eq_sum_of_support_subset
    intro rho hrho
    apply hsupport
    intro hbzero
    simp [hbzero] at hrho
  rw [hfun, hright]
  rw [iteratedDeriv_fun_sum]
  · simp_rw [div_eq_mul_inv, iteratedDeriv_const_mul_field]
    have hinv := iter_deriv_inv_linear_sub (𝕜 := ℂ) k 1
    simp only [one_mul, one_pow] at hinv
    have hterm (rho : ℂ) :
        iteratedDeriv k (fun s : ℂ ↦ (s - rho)⁻¹) z =
          (-1 : ℂ) ^ k * (k.factorial : ℂ) *
            (z - rho) ^ (-1 - (k : ℤ)) := by
      simpa [iteratedDeriv_eq_iterate] using congrFun (hinv rho) z
    simp_rw [hterm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rho hrho
    have hexp : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) := by omega
    rw [hexp, zpow_neg, zpow_natCast]
    ring
  · intro rho hrho
    have hrhoSupport : rho ∈ Function.support b := by
      simpa only [S, hb.mem_toFinset] using hrho
    exact (contDiffAt_const.mul
      ((contDiffAt_id.sub contDiffAt_const).inv
        (sub_ne_zero.mpr (hne rho hrhoSupport))))

/-- High consecutive reciprocal-power detector for natural multiplicities.
The normalization uses a closest support point, so every normalized root is
in the closed unit disk and one lies on its boundary. -/
theorem exists_weightedReciprocalPowerSum_second
    (Z : ℂ →₀ ℕ) {rho₀ z : ℂ} (hrho₀ : Z rho₀ ≠ 0)
    (hne : ∀ rho ∈ Z.support, z ≠ rho)
    {M : ℕ} {R : ℝ} (_hR : 0 < R) (hrho₀R : dist rho₀ z ≤ R) :
    let K := Z.support.card
    ∃ j ∈ Finset.Icc (M + 1) (M + K),
      1 ≤ (K : ℝ) *
          (((17 / 16 : ℝ) ^ M *
            ((K + 1 : ℝ) * (2 : ℝ) ^ K) /
              (2 * (68 : ℝ)⁻¹ ^ K))) *
          R ^ j *
          ‖Z.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j)‖ := by
  dsimp only
  let S := Z.support
  have hS : S.Nonempty := ⟨rho₀, Finsupp.mem_support_iff.mpr hrho₀⟩
  obtain ⟨rhoMin, hrhoMin, hmin⟩ :=
    Finset.exists_min_image S (fun rho ↦ dist rho z) hS
  let e : S ≃ Fin S.card := S.equivFin
  let rho : Fin S.card → ℂ := fun i ↦ (e.symm i : ℂ)
  let b : Fin S.card → ℝ := fun i ↦ Z (e.symm i : ℂ)
  let d : ℝ := dist rhoMin z
  let w : Fin S.card → ℂ := fun i ↦ (d : ℂ) / (z - rho i)
  let i₀ : Fin S.card := e ⟨rhoMin, hrhoMin⟩
  have hcard : 0 < S.card := Finset.card_pos.mpr hS
  have hd : 0 < d := by
    dsimp [d]
    exact dist_pos.mpr (Ne.symm (hne rhoMin hrhoMin))
  have hdist : ∀ i, d ≤ dist (rho i) z := by
    intro i
    exact hmin (e.symm i) (e.symm i).2
  have hrho0 : rho i₀ = rhoMin := by simp [rho, i₀]
  have hw0 : ∀ i, w i ≠ 0 := by
    intro i
    apply div_ne_zero
    · exact_mod_cast hd.ne'
    · exact sub_ne_zero.mpr (hne (rho i) (e.symm i).2)
  have hw : ∀ i, ‖w i‖ ≤ 1 := by
    intro i
    rw [show ‖w i‖ = d / ‖z - rho i‖ by
      simp only [w, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]]
    have hden : 0 < ‖z - rho i‖ := norm_pos_iff.mpr
      (sub_ne_zero.mpr (hne (rho i) (e.symm i).2))
    rw [div_le_one hden]
    simpa [dist_eq_norm, norm_sub_rev] using hdist i
  have hwi₀ : ‖w i₀‖ = 1 := by
    rw [show ‖w i₀‖ = d / ‖z - rho i₀‖ by
      simp only [w, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]]
    rw [hrho0]
    have : ‖z - rhoMin‖ = d := by simp [d, dist_eq_norm, norm_sub_rev]
    rw [this, div_self hd.ne']
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    dsimp [b]
    positivity
  have hbi₀ : 1 ≤ b i₀ := by
    dsimp [b, i₀]
    simp only [Equiv.symm_apply_apply]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Finsupp.mem_support_iff.mp hrhoMin)
  obtain ⟨j, hj, hlarge⟩ :=
    exists_large_consecutive_weighted_powerSum_second
      hcard w b hw0 hw hb i₀ hwi₀ hbi₀
  refine ⟨j, ?_, ?_⟩
  · simpa only [S] using hj
  · have hdR : d ≤ R := by
      calc
        d ≤ dist rho₀ z := hmin rho₀ (Finsupp.mem_support_iff.mpr hrho₀)
        _ ≤ R := hrho₀R
    have hsum : (∑ i, (b i : ℂ) * w i ^ j) =
        (d : ℂ) ^ j *
          Z.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j) := by
      rw [Finsupp.sum]
      rw [Finset.mul_sum]
      calc
        (∑ i, (b i : ℂ) * w i ^ j) =
            ∑ rho : S, ((Z (rho : ℂ) : ℝ) : ℂ) *
              ((d : ℂ) / (z - (rho : ℂ))) ^ j := by
          simpa only [b, w, rho] using e.symm.sum_comp
            (fun rho : S ↦ ((Z (rho : ℂ) : ℝ) : ℂ) *
              ((d : ℂ) / (z - (rho : ℂ))) ^ j)
        _ = ∑ rho ∈ S, ((Z rho : ℝ) : ℂ) *
              ((d : ℂ) / (z - rho)) ^ j := by
          exact (Finset.sum_subtype S (fun _ ↦ Iff.rfl)
            (fun rho ↦ ((Z rho : ℝ) : ℂ) *
              ((d : ℂ) / (z - rho)) ^ j)).symm
        _ = ∑ rho ∈ S, (d : ℂ) ^ j *
              ((Z rho : ℂ) / (z - rho) ^ j) := by
          apply Finset.sum_congr rfl
          intro rho hrho
          rw [div_pow]
          norm_cast
          ring
        _ = _ := by rfl
    have hnorm : ‖∑ i, (b i : ℂ) * w i ^ j‖ =
        d ^ j * ‖Z.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j)‖ := by
      rw [hsum, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hd]
    rw [hnorm] at hlarge
    have hpow : d ^ j ≤ R ^ j := pow_le_pow_left₀ hd.le hdR j
    have hnormNonneg :
        0 ≤ ‖Z.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j)‖ := norm_nonneg _
    have hinner : d ^ j *
          ‖Z.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j)‖ ≤
        R ^ j * ‖Z.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j)‖ :=
      mul_le_mul_of_nonneg_right hpow hnormNonneg
    have hcoef : 0 ≤ (S.card : ℝ) *
        (((17 / 16 : ℝ) ^ M *
          ((S.card + 1 : ℝ) * (2 : ℝ) ^ S.card) /
            (2 * (68 : ℝ)⁻¹ ^ S.card))) := by positivity
    calc
      (1 : ℝ) ≤ (S.card : ℝ) *
          (((17 / 16 : ℝ) ^ M *
            ((S.card + 1 : ℝ) * (2 : ℝ) ^ S.card) /
              (2 * (68 : ℝ)⁻¹ ^ S.card))) *
          (d ^ j *
            ‖Z.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j)‖) := hlarge
      _ ≤ (S.card : ℝ) *
          (((17 / 16 : ℝ) ^ M *
            ((S.card + 1 : ℝ) * (2 : ℝ) ^ S.card) /
              (2 * (68 : ℝ)⁻¹ ^ S.card))) *
          R ^ j *
          ‖Z.sum (fun rho m ↦ (m : ℂ) / (z - rho) ^ j)‖ := by
        calc
          (S.card : ℝ) *
              (((17 / 16 : ℝ) ^ M *
                ((S.card + 1 : ℝ) * (2 : ℝ) ^ S.card) /
                  (2 * (68 : ℝ)⁻¹ ^ S.card))) *
              (d ^ j * ‖Z.sum (fun rho m ↦
                (m : ℂ) / (z - rho) ^ j)‖) ≤
            (S.card : ℝ) *
              (((17 / 16 : ℝ) ^ M *
                ((S.card + 1 : ℝ) * (2 : ℝ) ^ S.card) /
                  (2 * (68 : ℝ)⁻¹ ^ S.card))) *
              (R ^ j * ‖Z.sum (fun rho m ↦
                (m : ℂ) / (z - rho) ^ j)‖) :=
            mul_le_mul_of_nonneg_left hinner hcoef
          _ = _ := by ring

/-- A multiplicity-weighted reciprocal detector with one distinguished
root.  Expanding the natural-valued `Finsupp` into a finite sigma type turns
the weighted pole sum into the pure power sum controlled by Atkinson's
theorem.  Choosing exponents divisible by `L` supplies any fixed minimum
derivative order required by the zero-density argument. -/
theorem exists_norm_sparseWeightedReciprocalPowerSum_gt_distinguished
    (Z : ℂ →₀ ℕ) {rho₀ z : ℂ} (hrho₀ : Z rho₀ ≠ 0)
    (hzrho₀ : z ≠ rho₀) {L : ℕ} (hL : 0 < L) :
    ∃ j : ℕ, L ≤ j ∧ j ≤ L * Z.sum (fun _ m => m) ∧
      (1 / 6 : ℝ) * ‖(z - rho₀)⁻¹‖ ^ j <
        ‖Z.sum (fun rho m => (m : ℂ) / (z - rho) ^ j)‖ := by
  let α := Σ rho : Z.support, Fin (Z rho)
  have hsupport₀ : rho₀ ∈ Z.support := Finsupp.mem_support_iff.mpr hrho₀
  let a₀ : α := ⟨⟨rho₀, hsupport₀⟩, ⟨0, Nat.pos_of_ne_zero hrho₀⟩⟩
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let w : Fin (Fintype.card α) → ℂ := fun i =>
    (z - ((e.symm i).1 : ℂ))⁻¹
  let i₀ : Fin (Fintype.card α) := e a₀
  have hcard : Fintype.card α = Z.sum (fun _ m => m) := by
    change Fintype.card (Σ rho : Z.support, Fin (Z rho)) = _
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [Finsupp.sum]
    exact (Finset.sum_subtype Z.support (by simp) (fun rho => Z rho)).symm
  have hn : 0 < Fintype.card α := by
    rw [hcard]
    apply Finsupp.sum_pos
    · intro rho hrho
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hrho)
    · exact Finsupp.ne_iff.mpr ⟨rho₀, hrho₀⟩
  have hwi₀ : w i₀ ≠ 0 := by
    simp only [w, i₀, Equiv.symm_apply_apply, a₀]
    exact inv_ne_zero (sub_ne_zero.mpr hzrho₀)
  obtain ⟨j, hjL, hjupper, hj⟩ :=
    exists_norm_sparsePowerSum_gt_distinguished hn w i₀ hwi₀ hL
  refine ⟨j, hjL, ?_, ?_⟩
  · simpa [hcard] using hjupper
  · have hleft : ‖w i₀‖ = ‖(z - rho₀)⁻¹‖ := by
      simp [w, i₀, a₀]
    rw [hleft] at hj
    have hsum : (∑ i, w i ^ j) =
        Z.sum (fun rho m => (m : ℂ) / (z - rho) ^ j) := by
      calc
        (∑ i, w i ^ j) = ∑ a : α, w (e a) ^ j := by
          exact (e.sum_comp (fun i => w i ^ j)).symm
        _ = ∑ rho : Z.support, ∑ _k : Fin (Z rho),
            (z - (rho : ℂ))⁻¹ ^ j := by
          rw [Fintype.sum_sigma]
          simp only [w, Equiv.symm_apply_apply]
        _ = ∑ rho : Z.support,
            (Z rho : ℂ) / (z - (rho : ℂ)) ^ j := by
          apply Finset.sum_congr rfl
          intro rho _hrho
          rw [Fin.sum_const, nsmul_eq_mul, inv_pow]
          ring
        _ = Z.sum (fun rho m => (m : ℂ) / (z - rho) ^ j) := by
          rw [Finsupp.sum]
          exact (Finset.sum_subtype Z.support (by simp)
            (fun rho => (Z rho : ℂ) / (z - rho) ^ j)).symm
    simpa [hsum] using hj

end

end Erdos48
