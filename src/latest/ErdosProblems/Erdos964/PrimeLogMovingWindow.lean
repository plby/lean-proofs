import ErdosProblems.Erdos964.PrimeLogScaleError
import ErdosProblems.Erdos964.IntervalIntegralEndpointLimit
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Prime quadrature with moving logarithmic endpoints
-/

namespace Erdos964

open Filter MeasureTheory
open scoped Topology

theorem exists_prime_log_scale_compact_error (a b : ℝ) (hab : a ≤ b) (g : ℝ → ℝ)
    (hg : ∀ z ∈ Set.Icc a b, DifferentiableAt ℝ g z)
    (hg' : ContinuousOn (deriv g) (Set.Icc a b)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L x y : ℝ, 0 < L → 1 ≤ x → x ≤ y →
      Real.log x / L ∈ Set.Icc a b → Real.log y / L ∈ Set.Icc a b →
      |primeLogScaleSum L x y g -
        (∫ z in (Real.log x / L)..(Real.log y / L), g z)| ≤ C / L := by
  obtain ⟨E, hE, herror⟩ := exists_prime_log_scale_error
  have hgcont : ContinuousOn g (Set.Icc a b) :=
    fun z hz => (hg z hz).continuousAt.continuousWithinAt
  obtain ⟨G, hG⟩ := isCompact_Icc.exists_bound_of_continuousOn hgcont
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hg'
  let C := E * (2 * |G| + |D| * (b - a))
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro L x y hL hx hxy hqx hqy
  have hqxy : Real.log x / L ≤ Real.log y / L :=
    div_le_div_of_nonneg_right (Real.log_le_log (by linarith) hxy) hL.le
  have hsub : Set.Icc (Real.log x / L) (Real.log y / L) ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc hqx.1 hqy.2
  have hgsmall := fun z hz => hg z (hsub hz)
  have hg'small := hg'.mono hsub
  have hnormint := intervalIntegrable_of_continuousOn_Icc
    (fun z => |deriv g z|) a b _ _ hg'.abs hqx hqy
  have hint : (∫ z in (Real.log x / L)..(Real.log y / L), |deriv g z|) ≤
      |D| * (b - a) := by
    calc
      _ ≤ ∫ _ in (Real.log x / L)..(Real.log y / L), |D| := by
        apply intervalIntegral.integral_mono_on hqxy hnormint (by
          apply Continuous.intervalIntegrable
          exact continuous_const)
        intro z hz
        exact (show |deriv g z| ≤ D by simpa only [Real.norm_eq_abs] using hD z (hsub hz)).trans
          (le_abs_self D)
      _ = |D| * (Real.log y / L - Real.log x / L) := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hqx.1, hqy.2]) (abs_nonneg _)
  have hxg : |g (Real.log x / L)| ≤ |G| := by
    exact (show |g (Real.log x / L)| ≤ G by
      simpa only [Real.norm_eq_abs] using hG _ hqx).trans (le_abs_self G)
  have hyg : |g (Real.log y / L)| ≤ |G| := by
    exact (show |g (Real.log y / L)| ≤ G by
      simpa only [Real.norm_eq_abs] using hG _ hqy).trans (le_abs_self G)
  calc
    _ ≤ (E / L) * (|g (Real.log x / L)| + |g (Real.log y / L)| +
        ∫ z in (Real.log x / L)..(Real.log y / L), |deriv g z|) :=
      herror L x y g hL hx hxy hgsmall hg'small
    _ ≤ (E / L) * (2 * |G| + |D| * (b - a)) :=
      mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hE hL.le)
    _ = C / L := by dsimp only [C]; ring

theorem tendsto_primeLogScaleSum_moving_window {ι : Type*} {l : Filter ι}
    (a b u v : ℝ) (hab : a ≤ b) (g : ℝ → ℝ) (L x y : ι → ℝ)
    (hg : ∀ z ∈ Set.Icc a b, DifferentiableAt ℝ g z)
    (hg' : ContinuousOn (deriv g) (Set.Icc a b))
    (hu : u ∈ Set.Icc a b) (hv : v ∈ Set.Icc a b)
    (hL : Tendsto L l atTop)
    (hx : Tendsto (fun i => Real.log (x i) / L i) l (𝓝 u))
    (hy : Tendsto (fun i => Real.log (y i) / L i) l (𝓝 v))
    (hwindow : ∀ᶠ i in l, 1 ≤ x i ∧ x i ≤ y i ∧
      Real.log (x i) / L i ∈ Set.Icc a b ∧ Real.log (y i) / L i ∈ Set.Icc a b) :
    Tendsto (fun i => primeLogScaleSum (L i) (x i) (y i) g) l (𝓝 (∫ z in u..v, g z)) := by
  obtain ⟨C, hC, herror⟩ := exists_prime_log_scale_compact_error a b hab g hg hg'
  have hgcont : ContinuousOn g (Set.Icc a b) :=
    fun z hz => (hg z hz).continuousAt.continuousWithinAt
  have hmain := tendsto_intervalIntegral_endpoints g a b u v
    (fun i => Real.log (x i) / L i) (fun i => Real.log (y i) / L i) hgcont hu hv hx hy
    (hwindow.mono (fun i hi => hi.2.2.1)) (hwindow.mono (fun i hi => hi.2.2.2))
  have he : Tendsto (fun i => primeLogScaleSum (L i) (x i) (y i) g -
      (∫ z in (Real.log (x i) / L i)..(Real.log (y i) / L i), g z)) l (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun i => norm_nonneg _)) _ (hL.const_div_atTop C)
    filter_upwards [hwindow, hL.eventually (eventually_gt_atTop 0)] with i hi hLi
    simpa only [sub_zero, Real.norm_eq_abs] using
      herror (L i) (x i) (y i) hLi hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have h := he.add hmain
  simp only [zero_add] at h
  apply h.congr'
  exact Eventually.of_forall (fun i => by ring)

end Erdos964
