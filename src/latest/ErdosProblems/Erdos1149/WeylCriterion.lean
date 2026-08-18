/-
Copyright (c) 2026 Ralf Stephan, in collaboration with Claude Code.
Released under CC0 1.0 Universal (public-domain dedication).

This file is a self-contained adaptation of the CC0 development in
`ForMathlib/Analysis/Equidistribution/{ModOne,AddCircleWeyl}.lean`.  It keeps only the
converse direction of Weyl's criterion needed for Erdős problem 1149.
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace Erdos1149

open MeasureTheory Filter Topology AddCircle

/-! ### Continuous-test-function form of Weyl's criterion -/

/-- If the empirical averages of every character of the additive circle converge to its Haar
integral, then the same is true for every continuous complex-valued function. -/
private theorem tendsto_average_of_tendsto_fourier {T : ℝ} [Fact (0 < T)]
    (Y : ℕ → AddCircle T)
    (hfou : ∀ k : ℤ, Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, fourier k (Y n)) / N) atTop
      (nhds (∫ b, fourier k b ∂(haarAddCircle (T := T))))) :
    ∀ F : C(AddCircle T, ℂ), Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, F (Y n)) / N) atTop
      (nhds (∫ b, F b ∂(haarAddCircle (T := T)))) := by
  set μ : Measure (AddCircle T) := haarAddCircle with hμ
  have hint : ∀ g : C(AddCircle T, ℂ), Integrable g μ := fun g =>
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hspan : ∀ g ∈ Submodule.span ℂ (Set.range (fourier (T := T))),
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, g (Y n)) / N) atTop
        (nhds (∫ b, g b ∂μ)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hgmem =>
        obtain ⟨k, rfl⟩ := hgmem
        exact hfou k
    | zero =>
        simp only [ContinuousMap.zero_apply, Finset.sum_const_zero, zero_div, integral_zero]
        exact tendsto_const_nhds
    | add g₁ g₂ _ _ ih₁ ih₂ =>
        simp only [ContinuousMap.add_apply, Finset.sum_add_distrib, add_div,
          integral_add (hint g₁) (hint g₂)]
        exact ih₁.add ih₂
    | smul c g _ ih =>
        simp only [ContinuousMap.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_div_assoc,
          integral_const_mul]
        exact ih.const_mul c
  intro F
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hF : F ∈ closure (Submodule.span ℂ (Set.range (fourier (T := T))) : Set _) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top, Submodule.top_coe]
    exact Set.mem_univ F
  obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hF (ε / 3) (by positivity)
  rw [dist_eq_norm] at hdist
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp (hspan p hp)) (ε / 3) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have hbound : ∀ z : AddCircle T, ‖F z - p z‖ ≤ ‖F - p‖ := fun z => by
    simpa using (F - p).norm_coe_le_norm z
  have h1 : ‖(∑ n ∈ Finset.range N, F (Y n)) / N - (∑ n ∈ Finset.range N, p (Y n)) / N‖
      ≤ ‖F - p‖ := by
    rw [div_sub_div_same, ← Finset.sum_sub_distrib, norm_div, Complex.norm_natCast]
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · rw [div_le_iff₀ (by exact_mod_cast h)]
      calc ‖∑ n ∈ Finset.range N, (F (Y n) - p (Y n))‖
          ≤ ∑ n ∈ Finset.range N, ‖F (Y n) - p (Y n)‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.range N, ‖F - p‖ := Finset.sum_le_sum (fun n _ => hbound _)
        _ = ‖F - p‖ * N := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  have h2 : ‖(∫ b, p b ∂μ) - ∫ b, F b ∂μ‖ ≤ ‖F - p‖ := by
    rw [← integral_sub (hint p) (hint F)]
    calc ‖∫ b, (p b - F b) ∂μ‖ ≤ ∫ b, ‖p b - F b‖ ∂μ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ _b, ‖F - p‖ ∂μ := by
          refine integral_mono_of_nonneg (by filter_upwards with z using norm_nonneg _)
            (integrable_const _) ?_
          filter_upwards with z
          rw [norm_sub_rev]
          exact hbound z
      _ = ‖F - p‖ := by simp
  have hN0' := hN₀ N hN
  rw [dist_eq_norm] at hN0' ⊢
  have htri : ‖(∑ n ∈ Finset.range N, F (Y n)) / N - ∫ b, F b ∂μ‖
      ≤ ‖(∑ n ∈ Finset.range N, F (Y n)) / N -
          (∑ n ∈ Finset.range N, p (Y n)) / N‖
        + ‖(∑ n ∈ Finset.range N, p (Y n)) / N - ∫ b, p b ∂μ‖
        + ‖(∫ b, p b ∂μ) - ∫ b, F b ∂μ‖ := by
    have heq : (∑ n ∈ Finset.range N, F (Y n)) / N - ∫ b, F b ∂μ
        = ((∑ n ∈ Finset.range N, F (Y n)) / N -
            (∑ n ∈ Finset.range N, p (Y n)) / N)
          + ((∑ n ∈ Finset.range N, p (Y n)) / N - ∫ b, p b ∂μ)
          + ((∫ b, p b ∂μ) - ∫ b, F b ∂μ) := by ring
    rw [heq]
    exact norm_add₃_le
  linarith [htri, h1, h2, hN0', hdist]

/-- Real-valued form of the continuous-test-function criterion. -/
private theorem tendsto_average_real_of_tendsto_fourier {T : ℝ} [Fact (0 < T)]
    (Y : ℕ → AddCircle T)
    (hfou : ∀ k : ℤ, Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, fourier k (Y n)) / N) atTop
      (nhds (∫ b, fourier k b ∂(haarAddCircle (T := T)))))
    (G : C(AddCircle T, ℝ)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, G (Y n)) / N) atTop
      (nhds (∫ b, G b ∂(haarAddCircle (T := T)))) := by
  have hC := tendsto_average_of_tendsto_fourier Y hfou
    ⟨fun z => ((G z : ℝ) : ℂ), Complex.continuous_ofReal.comp G.continuous⟩
  simp only [ContinuousMap.coe_mk, integral_complex_ofReal] at hC
  have hpush : ∀ N : ℕ, (∑ n ∈ Finset.range N, ((G (Y n) : ℝ) : ℂ)) / (N : ℂ)
      = (((∑ n ∈ Finset.range N, G (Y n)) / N : ℝ) : ℂ) := by
    intro N
    push_cast
    ring
  simp only [hpush] at hC
  have h2 := (Complex.continuous_re.tendsto _).comp hC
  simpa [Function.comp_def] using h2

/-! ### A continuous approximation to a circle arc -/

private theorem haarAddCircle_eq_volume :
    (haarAddCircle : Measure (AddCircle (1 : ℝ))) = volume := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

private theorem measureReal_closedBall (c : AddCircle (1 : ℝ)) {s : ℝ} (hs : 0 ≤ s) :
    (haarAddCircle : Measure (AddCircle (1 : ℝ))).real (Metric.closedBall c s)
      = min 1 (2 * s) := by
  rw [measureReal_def, haarAddCircle_eq_volume, AddCircle.volume_closedBall,
    ENNReal.toReal_ofReal (le_min zero_le_one (by linarith))]

/-- A continuous plateau bump: it is one on the inner closed ball of radius `s - η`, zero
outside the closed ball of radius `s`, and between zero and one everywhere. -/
private noncomputable def circBump (c : AddCircle (1 : ℝ)) (s η : ℝ) :
    C(AddCircle (1 : ℝ), ℝ) :=
  ⟨fun z => max 0 (min 1 ((s - ‖z - c‖) / η)), by fun_prop⟩

private theorem circBump_nonneg {c : AddCircle (1 : ℝ)} {s η : ℝ} {z : AddCircle (1 : ℝ)} :
    0 ≤ circBump c s η z := le_max_left _ _

private theorem circBump_le_one {c : AddCircle (1 : ℝ)} {s η : ℝ}
    {z : AddCircle (1 : ℝ)} : circBump c s η z ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

private theorem circBump_eq_one {c : AddCircle (1 : ℝ)} {s η : ℝ}
    {z : AddCircle (1 : ℝ)} (hη : 0 < η) (hz : ‖z - c‖ ≤ s - η) :
    circBump c s η z = 1 := by
  have h1 : (1 : ℝ) ≤ (s - ‖z - c‖) / η := by
    rw [le_div_iff₀ hη]
    linarith
  simp only [circBump, ContinuousMap.coe_mk, min_eq_left h1, max_eq_right zero_le_one]

private theorem circBump_eq_zero {c : AddCircle (1 : ℝ)} {s η : ℝ}
    {z : AddCircle (1 : ℝ)} (hη : 0 < η) (hz : s ≤ ‖z - c‖) :
    circBump c s η z = 0 := by
  have h1 : (s - ‖z - c‖) / η ≤ 0 := by
    rw [div_le_iff₀ hη]
    linarith
  simp only [circBump, ContinuousMap.coe_mk]
  exact max_eq_left (le_trans (min_le_right _ _) h1)

private theorem integrable_circBump (c : AddCircle (1 : ℝ)) (s η : ℝ) :
    Integrable (circBump c s η) (haarAddCircle : Measure (AddCircle (1 : ℝ))) :=
  (circBump c s η).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem integral_circBump_le (c : AddCircle (1 : ℝ)) {s η : ℝ}
    (hs : 0 ≤ s) (hη : 0 < η) :
    ∫ z, circBump c s η z ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))) ≤ min 1 (2 * s) := by
  have hle : ∀ z, circBump c s η z
      ≤ (Metric.closedBall c s).indicator (1 : AddCircle (1 : ℝ) → ℝ) z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall c s
    · rw [Set.indicator_of_mem hz]
      exact circBump_le_one
    · rw [Set.indicator_of_notMem hz, circBump_eq_zero hη]
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      exact le_of_not_ge hz
  calc ∫ z, circBump c s η z ∂(haarAddCircle : Measure (AddCircle (1 : ℝ)))
      ≤ ∫ z, (Metric.closedBall c s).indicator (1 : AddCircle (1 : ℝ) → ℝ) z
          ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))) :=
        integral_mono (integrable_circBump c s η)
          ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall) hle
    _ = min 1 (2 * s) := by
      rw [integral_indicator_one measurableSet_closedBall, measureReal_closedBall c hs]

private theorem le_integral_circBump (c : AddCircle (1 : ℝ)) {s η : ℝ}
    (hη : 0 < η) (hs : 0 ≤ s - η) :
    min 1 (2 * (s - η)) ≤
      ∫ z, circBump c s η z ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))) := by
  have hle : ∀ z, (Metric.closedBall c (s - η)).indicator
      (1 : AddCircle (1 : ℝ) → ℝ) z ≤ circBump c s η z := by
    intro z
    by_cases hz : z ∈ Metric.closedBall c (s - η)
    · have hz' : ‖z - c‖ ≤ s - η := by
        rwa [Metric.mem_closedBall, dist_eq_norm] at hz
      rw [Set.indicator_of_mem hz, circBump_eq_one hη hz']
      simp
    · rw [Set.indicator_of_notMem hz]
      exact circBump_nonneg
  calc min 1 (2 * (s - η))
      = ∫ z, (Metric.closedBall c (s - η)).indicator (1 : AddCircle (1 : ℝ) → ℝ) z
          ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))) := by
        rw [integral_indicator_one measurableSet_closedBall, measureReal_closedBall c hs]
    _ ≤ _ := integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall)
      (integrable_circBump c s η) hle

/-! ### Exponential sums supply the character limits -/

private theorem integral_fourier_eq_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ z, fourier k z ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))) = 0 := by
  have hc : (2 * (Real.pi : ℂ) * Complex.I * k) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
      (Int.cast_ne_zero.mpr hk)
  have hpre := AddCircle.intervalIntegral_preimage (1 : ℝ) 0 (fun z => fourier k z)
  rw [haarAddCircle_eq_volume, ← hpre]
  have hfun : ∀ t : ℝ, fourier k ((t : ℝ) : AddCircle (1 : ℝ))
      = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * k) * t) := by
    intro t
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  simp only [hfun]
  rw [integral_exp_mul_complex hc]
  have h1 : (2 * (Real.pi : ℂ) * Complex.I * k) * ((0 : ℝ) + 1 : ℝ)
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  have h0 : (2 * (Real.pi : ℂ) * Complex.I * k) * ((0 : ℝ) : ℂ) = 0 := by
    push_cast
    ring
  rw [h1, h0, Complex.exp_int_mul_two_pi_mul_I, Complex.exp_zero, sub_self, zero_div]

private theorem tendsto_fourier_of_weylSums {x : ℕ → ℝ}
    (hw : ∀ k : ℤ, k ≠ 0 → Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * x n)) / N)
        atTop (nhds 0))
    (k : ℤ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, fourier k ((x n : ℝ) : AddCircle (1 : ℝ))) / N) atTop
      (nhds (∫ b, fourier k b ∂(haarAddCircle (T := (1 : ℝ))))) := by
  rcases eq_or_ne k 0 with rfl | hk
  · have hint : ∫ z, fourier (0 : ℤ) z ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))) = 1 := by
      simp
    rw [hint]
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℂ)))
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    simp [Finset.sum_const, Finset.card_range, div_self hN']
  · rw [integral_fourier_eq_zero hk]
    refine (hw k hk).congr fun N => ?_
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring

private theorem tendsto_average_of_weylSums {x : ℕ → ℝ}
    (hw : ∀ k : ℤ, k ≠ 0 → Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * k * x n)) / N)
        atTop (nhds 0))
    (G : C(AddCircle (1 : ℝ), ℝ)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, G ((x n : ℝ) : AddCircle (1 : ℝ))) / N)
      atTop (nhds (∫ z, G z ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))))) :=
  tendsto_average_real_of_tendsto_fourier (fun n => ((x n : ℝ) : AddCircle (1 : ℝ)))
    (tendsto_fourier_of_weylSums hw) G

/-! ### Passing from continuous functions to interval counts -/

/-- The norm of a real number modulo one is no greater than its distance to any integer. -/
private theorem norm_coe_le_abs_sub_int (y : ℝ) (k : ℤ) :
    ‖((y : ℝ) : AddCircle (1 : ℝ))‖ ≤ |y - (k : ℝ)| := by
  rw [UnitAddCircle.norm_eq]
  exact round_le y k

private theorem circ_dist_le_of_fract_mem {c d y : ℝ}
    (hy : Int.fract y ∈ Set.Ico c d) :
    ‖((y : ℝ) : AddCircle (1 : ℝ)) -
        (((c + d) / 2 : ℝ) : AddCircle (1 : ℝ))‖ ≤ (d - c) / 2 := by
  rw [← QuotientAddGroup.mk_sub]
  refine le_trans (norm_coe_le_abs_sub_int (y - (c + d) / 2) ⌊y⌋) ?_
  have he : y - (c + d) / 2 - (⌊y⌋ : ℝ) = Int.fract y - (c + d) / 2 := by
    rw [Int.fract]
    ring
  rw [Set.mem_Ico] at hy
  rw [he, abs_le]
  constructor <;> linarith [hy.1, hy.2]

private theorem fract_mem_of_circ_dist_lt {c d y : ℝ} (hc : 0 ≤ c) (hd : d ≤ 1)
    (h : ‖((y : ℝ) : AddCircle (1 : ℝ)) -
        (((c + d) / 2 : ℝ) : AddCircle (1 : ℝ))‖ < (d - c) / 2) :
    Int.fract y ∈ Set.Ico c d := by
  rw [← QuotientAddGroup.mk_sub, UnitAddCircle.norm_eq] at h
  have h2 := abs_lt.mp h
  let k : ℤ := round (y - (c + d) / 2)
  have hk0 : (k : ℝ) ≤ y := by
    dsimp [k]
    linarith [h2.1]
  have hk1 : y < (k : ℝ) + 1 := by
    dsimp [k]
    linarith [h2.2]
  have hfloor : ⌊y⌋ = k := Int.floor_eq_iff.mpr ⟨hk0, hk1⟩
  rw [Set.mem_Ico, Int.fract, hfloor]
  dsimp [k] at ⊢
  constructor <;> linarith [h2.1, h2.2]

/-- Qualitative Weyl criterion in the exact half-open interval-counting form used below.

If every nonzero integral-frequency normalized exponential sum tends to zero, then the proportion
of `n < N` with fractional part in `[c,d)` tends to the interval length `d-c`. -/
theorem tendsto_count_fract_Ico_of_weyl {x : ℕ → ℝ}
    (hw : ∀ h : ℤ, h ≠ 0 → Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * h * x n)) / N)
        atTop (nhds 0))
    {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1) :
    Tendsto (fun N : ℕ =>
      (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico c d).card : ℝ) / N)
      atTop (nhds (d - c)) := by
  classical
  rcases hcd.eq_or_lt with rfl | hcd
  · simp only [Set.Ico_self, Set.mem_empty_iff_false, Finset.filter_false, Finset.card_empty,
      Nat.cast_zero, zero_div, sub_self]
    exact tendsto_const_nhds
  refine Metric.tendsto_atTop.2 fun δ hδ => ?_
  set η : ℝ := min (δ / 8) ((d - c) / 4) with hηdef
  have hη0 : 0 < η := lt_min (by linarith) (by linarith)
  have hη1 : η ≤ δ / 8 := min_le_left _ _
  have hη2 : η ≤ (d - c) / 4 := min_le_right _ _
  set z : AddCircle (1 : ℝ) := (((c + d) / 2 : ℝ) : AddCircle (1 : ℝ)) with hz
  have hup := tendsto_average_of_weylSums hw (circBump z ((d - c) / 2 + η) η)
  have hlo := tendsto_average_of_weylSums hw (circBump z ((d - c) / 2) η)
  have hIup : (∫ w, circBump z ((d - c) / 2 + η) η w
        ∂(haarAddCircle : Measure (AddCircle (1 : ℝ)))) ≤ (d - c) + 2 * η :=
    le_trans (integral_circBump_le z (by linarith) hη0)
      (le_trans (min_le_right _ _) (by linarith))
  have hIlo : (d - c) - 2 * η ≤
      ∫ w, circBump z ((d - c) / 2) η w
        ∂(haarAddCircle : Measure (AddCircle (1 : ℝ))) :=
    le_trans (le_min (by linarith) (by linarith))
      (le_integral_circBump z hη0 (by linarith))
  let count : ℕ → ℕ := fun N =>
    ((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico c d).card
  have hcount : ∀ N : ℕ, (count N : ℝ) =
      ∑ n ∈ Finset.range N, (if Int.fract (x n) ∈ Set.Ico c d then (1 : ℝ) else 0) := by
    intro N
    dsimp [count]
    rw [Finset.sum_boole]
  have hupper : ∀ N : ℕ, (count N : ℝ) ≤
      ∑ n ∈ Finset.range N,
        circBump z ((d - c) / 2 + η) η ((x n : ℝ) : AddCircle (1 : ℝ)) := by
    intro N
    rw [hcount N]
    refine Finset.sum_le_sum fun n _ => ?_
    by_cases hmem : Int.fract (x n) ∈ Set.Ico c d
    · have hdist := circ_dist_le_of_fract_mem (c := c) (d := d) hmem
      rw [if_pos hmem, circBump_eq_one hη0 (by rw [hz]; linarith)]
    · rw [if_neg hmem]
      exact circBump_nonneg
  have hlower : ∀ N : ℕ,
      (∑ n ∈ Finset.range N,
        circBump z ((d - c) / 2) η ((x n : ℝ) : AddCircle (1 : ℝ))) ≤ (count N : ℝ) := by
    intro N
    rw [hcount N]
    refine Finset.sum_le_sum fun n _ => ?_
    by_cases hmem : Int.fract (x n) ∈ Set.Ico c d
    · rw [if_pos hmem]
      exact circBump_le_one
    · rw [if_neg hmem]
      refine le_of_eq (circBump_eq_zero hη0 ?_)
      by_contra hlt
      refine hmem (fract_mem_of_circ_dist_lt hc hd ?_)
      rw [← hz]
      exact not_le.mp hlt
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hup (δ / 8) (by linarith)
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hlo (δ / 8) (by linarith)
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have h1 := hN₁ N (le_trans (le_max_left _ _) hN)
  have h2 := hN₂ N (le_trans (le_max_right _ _) hN)
  have hNn : (0 : ℝ) ≤ 1 / N := by positivity
  have key : ∀ u v : ℝ, u ≤ v → u / N ≤ v / N := by
    intro u v huv
    rw [div_eq_mul_one_div u, div_eq_mul_one_div v]
    exact mul_le_mul_of_nonneg_right huv hNn
  have hdiv1 := key _ _ (hupper N)
  have hdiv2 := key _ _ (hlower N)
  rw [Real.dist_eq, abs_lt] at h1 h2 ⊢
  dsimp [count] at hdiv1 hdiv2
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end Erdos1149
