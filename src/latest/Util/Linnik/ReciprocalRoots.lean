import Util.Linnik.ExceptionalPair
import Util.Linnik.PowerSum

/-!
# Reciprocal-square root multisets

The four local zero divisors are mapped to reciprocal squares.  Equal
images retain their combined multiplicities, so the positive-power-sum
theorem applies without any separation of zeros.
-/

namespace Linnik

open Complex
open scoped BigOperators Classical

noncomputable def reciprocalSquareRoots (D : ℂ →₀ ℕ) (c : ℂ) : ℂ →₀ ℕ :=
  D.mapDomain (fun rho ↦ ((c - rho) ^ 2)⁻¹)

theorem reciprocalSquareRoots_mass (D : ℂ →₀ ℕ) (c : ℂ) :
    (reciprocalSquareRoots D c).sum (fun _ m ↦ (m : ℝ)) =
      D.sum (fun _ m ↦ (m : ℝ)) := by
  exact Finsupp.sum_mapDomain_index (by intro; simp) (by intros; push_cast; rfl)

theorem reciprocalSquareRoots_powerSum (D : ℂ →₀ ℕ) (c : ℂ) (k : ℕ) :
    (reciprocalSquareRoots D c).sum (fun w m ↦ (m : ℂ) * w ^ k) =
      D.sum (fun rho m ↦ (m : ℂ) / (c - rho) ^ (2 * k)) := by
  rw [reciprocalSquareRoots, Finsupp.sum_mapDomain_index
    (by intro; simp) (by intros; push_cast; ring)]
  apply Finsupp.sum_congr
  intro rho _
  rw [← inv_pow, ← pow_mul, div_eq_mul_inv, inv_pow]

theorem reciprocalSquareRoots_support (D : ℂ →₀ ℕ) (c : ℂ) :
    (reciprocalSquareRoots D c).support =
      D.support.image (fun rho ↦ ((c - rho) ^ 2)⁻¹) :=
  Finsupp.mapDomain_support_of_subsingletonAddUnits _ _

theorem reciprocalSquareRoots_norm_le_one (D : ℂ →₀ ℕ) (c : ℂ)
    (hc : c.re = 2) (hD : ∀ rho ∈ D.support, rho.re < 1)
    {w : ℂ} (hw : w ∈ (reciprocalSquareRoots D c).support) : ‖w‖ ≤ 1 := by
  rw [reciprocalSquareRoots_support] at hw
  obtain ⟨rho, hrho, rfl⟩ := Finset.mem_image.mp hw
  have hnorm : 1 ≤ ‖c - rho‖ := by
    have hre := (le_abs_self (c - rho).re).trans (Complex.abs_re_le_norm (c - rho))
    rw [Complex.sub_re, hc] at hre
    linarith [hD rho hrho]
  rw [norm_inv, norm_pow]
  exact (inv_le_one₀ (by positivity : 0 < ‖c - rho‖ ^ 2)).mpr (one_le_pow₀ hnorm)

theorem natFinsupp_mass_add (D E : ℂ →₀ ℕ) :
    (D + E).sum (fun _ m ↦ (m : ℝ)) =
      D.sum (fun _ m ↦ (m : ℝ)) + E.sum (fun _ m ↦ (m : ℝ)) :=
  Finsupp.sum_add_index' (by intro; simp) (by intros; push_cast; rfl)

theorem natFinsupp_powerSum_add (D E : ℂ →₀ ℕ) (k : ℕ) :
    (D + E).sum (fun w m ↦ (m : ℂ) * w ^ k) =
      D.sum (fun w m ↦ (m : ℂ) * w ^ k) + E.sum (fun w m ↦ (m : ℂ) * w ^ k) :=
  Finsupp.sum_add_index' (by intro; simp) (by intros; push_cast; ring)

theorem natFinsupp_mass_mono {D E : ℂ →₀ ℕ} (h : D ≤ E) :
    D.sum (fun _ m ↦ (m : ℝ)) ≤ E.sum (fun _ m ↦ (m : ℝ)) := by
  apply Finsupp.sum_le_sum_index h
  · intro _ _ a b hab
    change (a : ℝ) ≤ (b : ℝ)
    exact_mod_cast hab
  · intro _ _
    simp

noncomputable def fourRemainingRoots {q : ℕ} [NeZero q]
    (chi1 chi : DirichletCharacter ℂ q) (beta t : ℝ) : ℂ →₀ ℕ :=
  reciprocalSquareRoots (remainingCharacterZeros chi1 1 beta 0) 2 +
    reciprocalSquareRoots (remainingCharacterZeros chi1 chi1 beta 0) 2 +
    reciprocalSquareRoots (remainingCharacterZeros chi1 chi beta t) ((2 : ℂ) + t * I) +
    reciprocalSquareRoots (remainingCharacterZeros chi1 (chi * chi1) beta t) ((2 : ℂ) + t * I)

theorem fourRemainingRoots_powerSum {q : ℕ} [NeZero q]
    (chi1 chi : DirichletCharacter ℂ q) (beta t : ℝ) (k : ℕ) :
    (fourRemainingRoots chi1 chi beta t).sum (fun w m ↦ (m : ℂ) * w ^ k) =
      remainingZeroPowerSum chi1 1 beta 0 (2 * k) +
        remainingZeroPowerSum chi1 chi1 beta 0 (2 * k) +
        remainingZeroPowerSum chi1 chi beta t (2 * k) +
        remainingZeroPowerSum chi1 (chi * chi1) beta t (2 * k) := by
  simp only [fourRemainingRoots, natFinsupp_powerSum_add,
    reciprocalSquareRoots_powerSum, remainingZeroPowerSum, Complex.ofReal_zero, zero_mul, add_zero]

theorem remainingCharacterZeros_re_lt_one {q : ℕ} [NeZero q]
    (chi1 chi : DirichletCharacter ℂ q) (beta t : ℝ)
    {rho : ℂ} (hrho : rho ∈ (remainingCharacterZeros chi1 chi beta t).support) : rho.re < 1 := by
  apply characterDiskZeros_re_lt_one chi t
  apply Finsupp.mem_support_iff.mpr
  intro hzero
  have hle := remainingCharacterZeros_le chi1 chi beta t rho
  rw [hzero] at hle
  exact (Finsupp.mem_support_iff.mp hrho) (Nat.eq_zero_of_le_zero hle)

theorem fourRemainingRoots_norm_le_one {q : ℕ} [NeZero q]
    (chi1 chi : DirichletCharacter ℂ q) (beta t : ℝ)
    {w : ℂ} (hw : w ∈ (fourRemainingRoots chi1 chi beta t).support) : ‖w‖ ≤ 1 := by
  have hnorm (psi : DirichletCharacter ℂ q) (u : ℝ) :
      ∀ z ∈ (reciprocalSquareRoots (remainingCharacterZeros chi1 psi beta u)
        ((2 : ℂ) + u * I)).support, ‖z‖ ≤ 1 := by
    intro z hz
    exact reciprocalSquareRoots_norm_le_one _ _ (by simp)
      (fun rho hrho ↦ remainingCharacterZeros_re_lt_one chi1 psi beta u hrho) hz
  simp only [fourRemainingRoots, Finsupp.support_add_eq_union, Finset.mem_union] at hw
  rcases hw with ((hw | hw) | hw) | hw
  · simpa using hnorm 1 0 w (by simpa using hw)
  · simpa using hnorm chi1 0 w (by simpa using hw)
  · exact hnorm chi t w hw
  · exact hnorm (chi * chi1) t w hw

theorem exists_fourRemainingRoots_mass_bound :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi1 chi : DirichletCharacter ℂ q) (beta t : ℝ),
          (fourRemainingRoots chi1 chi beta t).sum (fun _ m ↦ (m : ℝ)) ≤
            8 * ((A : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) := by
  obtain ⟨A, hA, hbound⟩ := exists_characterDiskZeros_bounds
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi1 chi beta t
  have hmass (psi : DirichletCharacter ℂ q) (u : ℝ) (hu : |u| ≤ |t|) :
      (remainingCharacterZeros chi1 psi beta u).sum (fun _ m ↦ (m : ℝ)) ≤
        2 * ((A : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) := by
    have hfirst := (natFinsupp_mass_mono (remainingCharacterZeros_le chi1 psi beta u)).trans
      (hbound q hq psi u).1
    apply hfirst.trans
    have hq₀ : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    have hlog : Real.log ((q : ℝ) * (|u| + 2)) ≤
        Real.log ((q : ℝ) * (|t| + 2)) := by
      apply Real.log_le_log (by positivity)
      exact mul_le_mul_of_nonneg_left (by linarith : |u| + 2 ≤ |t| + 2) hq₀.le
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg A))
      (by norm_num)
  have h₀ := hmass 1 0 (by simpa using abs_nonneg t)
  have h₁ := hmass chi1 0 (by simpa using abs_nonneg t)
  have h₂ := hmass chi t le_rfl
  have h₃ := hmass (chi * chi1) t le_rfl
  simp only [fourRemainingRoots, natFinsupp_mass_add, reciprocalSquareRoots_mass]
  linarith

theorem exists_fourRemainingRoots_powerSum_bound :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi1 chi : DirichletCharacter ℂ q), chi1 ≠ 1 → chi1 ^ 2 = 1 →
          ∀ beta : ℝ, 0 < beta → beta < 1 →
            DirichletCharacter.LFunction chi1 (beta : ℂ) = 0 →
            ∀ (t : ℝ) (k : ℕ), 1 ≤ k →
              ((fourRemainingRoots chi1 chi beta t).sum (fun w m ↦ (m : ℂ) * w ^ k)).re ≤
                4 * k * (1 - beta) +
                  (64 * ((A : ℝ) * Real.log ((q : ℝ) * (|t| + 2))) + 2) * (1 / 9 : ℝ) ^ k := by
  obtain ⟨A, hA, hbound⟩ := exists_remaining_four_zeroPowerSum_bound
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi1 chi hchi1 hsquare beta hbeta₀ hbeta₁ hzero t k hk
  have h := hbound q hq chi1 chi hchi1 hsquare beta hbeta₀ hbeta₁ hzero t (2 * k) (by omega)
  rw [← fourRemainingRoots_powerSum] at h
  have hp : (3 : ℝ) ^ (2 * k) = (9 : ℝ) ^ k := by rw [pow_mul]; norm_num
  rw [hp, div_eq_mul_inv, ← inv_pow] at h
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, inv_eq_one_div] at h
  convert h using 1
  ring

theorem center_sub_zero_eq_real (rho : ℂ) :
    (2 : ℂ) + rho.im * I - rho = ((2 - rho.re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp

theorem nontrivial_zero_mem_characterDiskZeros {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {rho : ℂ}
    (hrho₀ : 0 < rho.re) (hrho₁ : rho.re < 1)
    (hzero : DirichletCharacter.LFunction chi rho = 0) :
    rho ∈ (characterDiskZeros chi rho.im).support := by
  have hrho : rho ≠ 1 := by intro h; simp [h] at hrho₁
  have hreal : 0 ≤ 2 - rho.re := by linarith
  have hdist : dist rho ((2 : ℂ) + rho.im * I) ≤ 6 := by
    rw [dist_comm, dist_eq_norm, center_sub_zero_eq_real,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hreal]
    linarith
  have hreg : regularizedLFunction chi rho = 0 := by
    rw [regularizedLFunction_eq_mul chi hrho, hzero, mul_zero]
  rw [Finsupp.mem_support_iff]
  intro h
  exact (diskZeros_zero_iff (differentiable_regularizedLFunction chi)
    (regularizedLFunction_ne_zero_of_one_le_re chi
      (s := (2 : ℂ) + rho.im * I) (by simp)) hdist).mp h hreg

theorem remainingCharacterZeros_mem_of_ne_exceptional {q : ℕ} [NeZero q]
    (chi1 chi : DirichletCharacter ℂ q) (beta t : ℝ) {rho : ℂ}
    (hrho : rho ∈ (characterDiskZeros chi t).support)
    (hne : chi ≠ chi1 ∨ rho ≠ (beta : ℂ)) :
    rho ∈ (remainingCharacterZeros chi1 chi beta t).support := by
  unfold remainingCharacterZeros
  split_ifs with h
  · have hrhoBeta : rho ≠ (beta : ℂ) := hne.resolve_left (not_ne_iff.mpr h.1)
    rw [Finsupp.mem_support_iff, Finsupp.tsub_apply]
    simpa [Finsupp.single_apply, hrhoBeta, hrhoBeta.symm] using
      (Finsupp.mem_support_iff.mp hrho)
  · exact hrho

theorem target_mem_fourRemainingRoots {q : ℕ} [NeZero q]
    (chi1 chi : DirichletCharacter ℂ q) (beta : ℝ) {rho : ℂ}
    (hrho₀ : 0 < rho.re) (hrho₁ : rho.re < 1)
    (hzero : DirichletCharacter.LFunction chi rho = 0)
    (hne : chi ≠ chi1 ∨ rho ≠ (beta : ℂ)) :
    (((2 : ℂ) + rho.im * I - rho) ^ 2)⁻¹ ∈
      (fourRemainingRoots chi1 chi beta rho.im).support := by
  have hmem := remainingCharacterZeros_mem_of_ne_exceptional chi1 chi beta rho.im
    (nontrivial_zero_mem_characterDiskZeros chi hrho₀ hrho₁ hzero) hne
  simp only [fourRemainingRoots, Finsupp.support_add_eq_union, Finset.mem_union]
  apply Or.inl
  apply Or.inr
  rw [reciprocalSquareRoots_support]
  exact Finset.mem_image.mpr ⟨rho, hmem, rfl⟩

theorem target_root_norm {rho : ℂ} (hrho : rho.re < 1) :
    ‖(((2 : ℂ) + rho.im * I - rho) ^ 2)⁻¹‖ = ((2 - rho.re) ^ 2)⁻¹ := by
  rw [norm_inv, norm_pow, center_sub_zero_eq_real, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]

theorem target_root_norm_ge_quarter {rho : ℂ}
    (hrho₀ : 0 < rho.re) (hrho₁ : rho.re < 1) :
    (1 : ℝ) / 4 ≤ ‖(((2 : ℂ) + rho.im * I - rho) ^ 2)⁻¹‖ := by
  rw [target_root_norm hrho₁, inv_eq_one_div]
  apply one_div_le_one_div_of_le (sq_pos_of_pos (by linarith))
  nlinarith

end Linnik
