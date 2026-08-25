import Util.Linnik.CharacterGrowth
import ErdosProblems.Erdos48.RegularizedDerivative
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Finite zero divisors on the fixed disk

Natural multiplicities and high logarithmic derivatives on a fixed disk
are packaged here for the four-character zero-repulsion argument.
-/

namespace Linnik

open Complex Metric Set Filter BoundedGaps.Maynard
open scoped BigOperators Topology Classical

theorem entire_analyticOrderAt_ne_top {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {c : ℂ} (hc : f c ≠ 0) (rho : ℂ) :
    analyticOrderAt f rho ≠ ⊤ := by
  rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero rho
    (fun z ↦ hf.analyticAt z)]
  intro h
  exact hc (congrFun h c)

noncomputable def diskZeroMultiplicity (f : ℂ → ℂ) (c : ℂ) : ℂ → ℕ :=
  fun rho ↦ if dist rho c ≤ 6 then analyticOrderNatAt f rho else 0

theorem diskZeroMultiplicity_eq_divisor {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {c : ℂ} (hc : f c ≠ 0) (rho : ℂ) :
    (diskZeroMultiplicity f c rho : ℤ) =
      MeromorphicOn.divisor f (closedBall c 6) rho := by
  unfold diskZeroMultiplicity
  by_cases hrho : dist rho c ≤ 6
  · rw [if_pos hrho, MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun z _ ↦ hf.analyticAt z) (mem_closedBall.mpr hrho),
      ← Nat.cast_analyticOrderNatAt (entire_analyticOrderAt_ne_top hf hc rho),
      ENat.map_natCast, WithTop.untop₀_coe]
  · rw [if_neg hrho, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _
      (by simpa only [mem_closedBall] using hrho)]
    norm_cast

theorem diskZeroMultiplicity_hasFiniteSupport {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {c : ℂ} (hc : f c ≠ 0) :
    Function.HasFiniteSupport (diskZeroMultiplicity f c) := by
  apply ((MeromorphicOn.divisor f (closedBall c 6)).finiteSupport
    (isCompact_closedBall c 6)).subset
  intro rho hrho
  rw [Function.mem_support] at hrho ⊢
  rw [← diskZeroMultiplicity_eq_divisor hf hc]
  exact_mod_cast hrho

noncomputable def diskZeros {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {c : ℂ} (hc : f c ≠ 0) : ℂ →₀ ℕ :=
  Finsupp.ofSupportFinite (diskZeroMultiplicity f c)
    (diskZeroMultiplicity_hasFiniteSupport hf hc)

@[simp] theorem diskZeros_apply {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {c : ℂ} (hc : f c ≠ 0) (rho : ℂ) :
    diskZeros hf hc rho = diskZeroMultiplicity f c rho := rfl

theorem diskZeros_zero_iff {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {c : ℂ} (hc : f c ≠ 0) {rho : ℂ}
    (hrho : dist rho c ≤ 6) : diskZeros hf hc rho = 0 ↔ f rho ≠ 0 := by
  rw [diskZeros_apply, diskZeroMultiplicity, if_pos hrho]
  rw [← (hf.analyticAt rho).analyticOrderAt_eq_zero,
    ← Nat.cast_analyticOrderNatAt (entire_analyticOrderAt_ne_top hf hc rho)]
  simp

theorem diskZeros_sum_eq_divisor_finsum {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {c : ℂ} (hc : f c ≠ 0)
    (g : ℂ → ℂ) :
    (diskZeros hf hc).sum (fun rho m ↦ (m : ℂ) * g rho) =
      ∑ᶠ rho : ℂ, ((MeromorphicOn.divisor f (closedBall c 6) rho : ℤ) : ℂ) * g rho := by
  rw [Finsupp.sum]
  symm
  calc
    (∑ᶠ rho : ℂ, ((MeromorphicOn.divisor f (closedBall c 6) rho : ℤ) : ℂ) * g rho) =
        ∑ rho ∈ (diskZeros hf hc).support,
          ((MeromorphicOn.divisor f (closedBall c 6) rho : ℤ) : ℂ) * g rho := by
      apply finsum_eq_sum_of_support_subset
      intro rho hrho
      rw [Function.mem_support] at hrho
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro hzero
      apply hrho
      rw [← diskZeroMultiplicity_eq_divisor hf hc, ← diskZeros_apply hf hc,
        hzero]
      simp
    _ = ∑ rho ∈ (diskZeros hf hc).support, ((diskZeros hf hc rho : ℕ) : ℂ) * g rho := by
      apply Finset.sum_congr rfl
      intro rho _
      rw [← diskZeroMultiplicity_eq_divisor hf hc, ← diskZeros_apply hf hc]
      norm_cast

theorem diskZeros_mass_eq_divisor_finsum {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {c : ℂ} (hc : f c ≠ 0) :
    (diskZeros hf hc).sum (fun _ m ↦ (m : ℝ)) =
      ((∑ᶠ rho : ℂ, MeromorphicOn.divisor f (closedBall c 6) rho : ℤ) : ℝ) := by
  have h := diskZeros_sum_eq_divisor_finsum hf hc (fun _ ↦ 1)
  simp only [mul_one] at h
  have hfinite := (MeromorphicOn.divisor f (closedBall c 6)).finiteSupport
    (isCompact_closedBall c 6)
  have hcast :
      (∑ᶠ rho : ℂ, ((MeromorphicOn.divisor f (closedBall c 6) rho : ℤ) : ℂ)) =
        ((∑ᶠ rho : ℂ, MeromorphicOn.divisor f (closedBall c 6) rho : ℤ) : ℂ) := by
    exact (map_finsum (Int.castRingHom ℂ) hfinite).symm
  have hre := congrArg Complex.re (h.trans hcast)
  simpa only [Finsupp.sum, Complex.re_sum, Complex.natCast_re, Complex.intCast_re,
    Int.cast_sum] using hre

/-- Jensen's inequality bounds the total number of zeros, counted with
multiplicity, by twice the relative logarithmic growth. -/
theorem diskZeros_mass_le {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {c : ℂ} (hc : f c ≠ 0)
    {M : ℝ} (hM : 0 ≤ M)
    (hsize : 1 ≤ Real.exp M * ‖f c‖)
    (hbound : ∀ z ∈ sphere c 12, ‖f z‖ ≤ Real.exp M * ‖f c‖) :
    (diskZeros hf hc).sum (fun _ m ↦ (m : ℝ)) ≤ 2 * M := by
  have han : AnalyticOnNhd ℂ f (closedBall c |(12 : ℝ)|) :=
    fun z _ ↦ hf.analyticAt z
  have hjensen := han.sum_divisor_le (r := (6 : ℝ)) (R := (12 : ℝ))
    (M := Real.exp M * ‖f c‖) (by norm_num) (by norm_num) hsize hc
    (by simpa using hbound)
  rw [show |(6 : ℝ)| = 6 by norm_num] at hjensen
  norm_num at hjensen
  have hratio : Real.exp M * ‖f c‖ / ‖f c‖ = Real.exp M :=
    mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hc)
  rw [hratio, Real.log_exp] at hjensen
  rw [diskZeros_mass_eq_divisor_finsum]
  apply hjensen.trans
  have hlog : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
  nlinarith

theorem iteratedDeriv_finsupp_poles (D : ℂ →₀ ℕ) {c : ℂ}
    (hne : ∀ rho ∈ D.support, c ≠ rho) (k : ℕ) :
    iteratedDeriv k (fun s : ℂ ↦ D.sum (fun rho m ↦ (m : ℂ) / (s - rho))) c =
      (-1 : ℂ) ^ k * k.factorial *
        D.sum (fun rho m ↦ (m : ℂ) / (c - rho) ^ (k + 1)) := by
  simp only [Finsupp.sum]
  rw [iteratedDeriv_fun_sum]
  · simp_rw [div_eq_mul_inv, iteratedDeriv_const_mul_field]
    have hinv := iter_deriv_inv_linear_sub (𝕜 := ℂ) k 1
    simp only [one_mul, one_pow] at hinv
    have hterm (rho : ℂ) :
        iteratedDeriv k (fun s : ℂ ↦ (s - rho)⁻¹) c =
          (-1 : ℂ) ^ k * (k.factorial : ℂ) *
            (c - rho) ^ (-1 - (k : ℤ)) := by
      simpa [iteratedDeriv_eq_iterate] using congrFun (hinv rho) c
    simp_rw [hterm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rho _
    have hexp : (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) := by omega
    rw [hexp, zpow_neg, zpow_natCast]
    ring
  · intro rho hrho
    exact contDiffAt_const.mul
      ((contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr (hne rho hrho)))

/-- At the center, the error in the reciprocal-power expansion decays as
`3⁻ᵏ`; retaining this decay is important in the positive-power-sum argument. -/
theorem norm_iteratedDeriv_sub_diskZeros_le {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {c : ℂ} (hc : f c ≠ 0)
    {M : ℝ} (hM : 0 < M)
    (hbound : ∀ z ∈ sphere c 12, ‖f z‖ ≤ Real.exp M * ‖f c‖) (k : ℕ) :
    ‖iteratedDeriv k (logDeriv f) c -
        (-1 : ℂ) ^ k * k.factorial *
          (diskZeros hf hc).sum (fun rho m ↦ (m : ℂ) / (c - rho) ^ (k + 1))‖ ≤
      k.factorial * (16 * M / 3) / (3 : ℝ) ^ k := by
  obtain ⟨G, hG, hGne, hidentity, hGbound⟩ :=
    exists_regularizedLogDeriv_data_erdos48 (f := f) (c := c) (R := (3 : ℝ))
      (by norm_num) hM (fun z _ ↦ hf.analyticAt z) hc
      (by convert hbound using 1; norm_num)
  let D := diskZeros hf hc
  let P : ℂ → ℂ := fun s ↦ D.sum (fun rho m ↦ (m : ℂ) / (s - rho))
  let U : Set ℂ := {s | f s ≠ 0} ∩ ball c 3
  have hUopen : IsOpen U := (isOpen_ne.preimage hf.continuous).inter isOpen_ball
  have hcU : c ∈ U := ⟨hc, by simp⟩
  have heqOn : Set.EqOn (logDeriv G) (fun s ↦ logDeriv f s - P s) U := by
    intro s hs
    have hid := hidentity s (ball_subset_closedBall hs.2) hs.1
    rw [show (2 : ℝ) * 3 = 6 by norm_num] at hid
    rw [hid]
    congr 1
    symm
    simpa only [P, D, div_eq_mul_inv] using
      diskZeros_sum_eq_divisor_finsum hf hc (fun rho ↦ (s - rho)⁻¹)
  have hDne : ∀ rho ∈ D.support, c ≠ rho := by
    intro rho hrho hcr
    subst rho
    have hzero : D c = 0 :=
      (diskZeros_zero_iff hf hc (by simp)).mpr hc
    exact (Finsupp.mem_support_iff.mp hrho) hzero
  have hlogAnalytic : AnalyticAt ℂ (logDeriv f) c := by
    simpa only [logDeriv] using (hf.analyticAt c).deriv.div (hf.analyticAt c) hc
  have hPAnalytic : AnalyticAt ℂ P c := by
    have han : AnalyticAt ℂ
        (∑ rho ∈ D.support, (fun s : ℂ ↦ (D rho : ℂ) / (s - rho))) c := by
      apply Finset.analyticAt_sum D.support
      intro rho hrho
      exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr (hDne rho hrho))
    convert han using 1
    funext s
    simp [P, Finsupp.sum]
  have hGP : iteratedDeriv k (logDeriv G) c =
      iteratedDeriv k (logDeriv f) c - iteratedDeriv k P c := by
    rw [heqOn.iteratedDeriv_of_isOpen hUopen k hcU]
    exact iteratedDeriv_sub hlogAnalytic.contDiffAt hPAnalytic.contDiffAt
  have hPderiv := iteratedDeriv_finsupp_poles D hDne k
  have hGderiv := norm_iteratedDeriv_logDeriv_le_of_regularized_data
    (G := G) (c := c) (z := c) (R := (3 : ℝ)) (r := (3 : ℝ))
    (C := 16 * M / 3) (by norm_num) (by norm_num) hG hGne
    (by intro z hz; exact hz) hGbound k
  rw [hGP, show iteratedDeriv k P c = _ from hPderiv] at hGderiv
  exact hGderiv

/-- The full natural-valued zero divisor of a regularized character in the
radius-six disk centered at `2+it`. -/
noncomputable def characterDiskZeros {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) : ℂ →₀ ℕ :=
  diskZeros (differentiable_regularizedLFunction chi)
    (regularizedLFunction_ne_zero_of_one_le_re chi
      (s := (2 : ℂ) + t * I) (by simp))

theorem characterDiskZeros_mem_support {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) {rho : ℂ}
    (hrho : rho ∈ (characterDiskZeros chi t).support) :
    dist rho ((2 : ℂ) + t * I) ≤ 6 ∧ regularizedLFunction chi rho = 0 := by
  have hne := Finsupp.mem_support_iff.mp hrho
  change diskZeroMultiplicity (regularizedLFunction chi) ((2 : ℂ) + t * I) rho ≠ 0 at hne
  unfold diskZeroMultiplicity at hne
  split_ifs at hne with hdist
  · exact ⟨hdist, apply_eq_zero_of_analyticOrderNatAt_ne_zero hne⟩
  · exact (hne rfl).elim

theorem characterDiskZeros_re_lt_one {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (t : ℝ) {rho : ℂ}
    (hrho : rho ∈ (characterDiskZeros chi t).support) : rho.re < 1 :=
  regularizedLFunction_zero_re_lt_one chi
    (characterDiskZeros_mem_support chi t hrho).2

/-- Uniform finite zero counts and all high logarithmic-derivative
approximations, valid for principal and imprimitive characters as well. -/
theorem exists_characterDiskZeros_bounds :
    ∃ A : ℕ, 37 ≤ A ∧
      ∀ (q : ℕ) [NeZero q], 1 < q →
        ∀ (chi : DirichletCharacter ℂ q) (t : ℝ),
          let M := (A : ℝ) * Real.log ((q : ℝ) * (|t| + 2))
          (characterDiskZeros chi t).sum (fun _ m ↦ (m : ℝ)) ≤ 2 * M ∧
          ∀ k : ℕ,
            ‖iteratedDeriv k (logDeriv (regularizedLFunction chi)) ((2 : ℂ) + t * I) -
                (-1 : ℂ) ^ k * k.factorial *
                  (characterDiskZeros chi t).sum
                    (fun rho m ↦ (m : ℂ) / ((2 : ℂ) + t * I - rho) ^ (k + 1))‖ ≤
              k.factorial * (16 * M / 3) / (3 : ℝ) ^ k := by
  obtain ⟨A, hA, hbound⟩ := exists_regularized_radiusTwelve_relative_bound
  refine ⟨A, hA, ?_⟩
  intro q _ hq chi t
  let c : ℂ := (2 : ℂ) + t * I
  let B : ℝ := (q : ℝ) * (|t| + 2)
  let M : ℝ := (A : ℝ) * Real.log B
  have hq₂ : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hB₄ : 4 ≤ B := by dsimp [B]; nlinarith [abs_nonneg t]
  have hA₁ : 1 ≤ A := by omega
  have hM : 0 < M := mul_pos (by exact_mod_cast (show 0 < A by omega))
    (Real.log_pos (by linarith))
  have hexp : Real.exp M = B ^ A := by
    dsimp [M]
    rw [Real.exp_nat_mul, Real.exp_log (by linarith : 0 < B)]
  have hexp₃ : 3 ≤ Real.exp M := by
    rw [hexp]
    calc
      (3 : ℝ) ≤ B := by linarith
      _ = B ^ 1 := (pow_one _).symm
      _ ≤ B ^ A := pow_le_pow_right₀ (by linarith) hA₁
  have hsize : 1 ≤ Real.exp M * ‖regularizedLFunction chi c‖ :=
    (one_le_three_mul_norm_regularized_center chi t).trans
      (mul_le_mul_of_nonneg_right hexp₃ (norm_nonneg _))
  have hc : regularizedLFunction chi c ≠ 0 :=
    regularizedLFunction_ne_zero_of_one_le_re chi (by simp [c])
  have hgrowth : ∀ s ∈ sphere c 12,
      ‖regularizedLFunction chi s‖ ≤ Real.exp M * ‖regularizedLFunction chi c‖ :=
    hbound q hq chi t
  constructor
  · exact diskZeros_mass_le (differentiable_regularizedLFunction chi) hc hM.le hsize hgrowth
  · intro k
    exact norm_iteratedDeriv_sub_diskZeros_le
      (differentiable_regularizedLFunction chi) hc hM hgrowth k

end Linnik
