import Wikipedia.HopfProblem.OrbitPairTimeProfileDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniformly positive small scalar clocks on a compact time slab

The time derivative of a native smooth scalar family is native smooth.
If the scalar family vanishes outside a bounded time interval and the
spatial source is compact, this derivative is globally bounded. Hence
`t + delta * kappa(t,x)` has positive time derivative for every sufficiently
small delta, uniformly over the entire source.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem smooth_time_derivative {κ : ℝ × M → ℝ}
    (hκ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ κ) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => deriv (fun t => κ (t, q.2)) q.1) := by
  let f : (ℝ × M) → ℝ → ℝ := fun q t => κ (t, q.2)
  have hf : ContMDiff ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (Function.uncurry f) :=
    hκ.comp (contMDiff_snd.prodMk (contMDiff_snd.comp contMDiff_fst))
  intro q
  have hd := (hf.contMDiffAt (x := (q, q.1))).mfderiv f Prod.fst
    (contMDiffAt_fst (n := ∞)) (m := ∞) (by simp)
  let d : (ℝ × M) → (ℝ →L[ℝ] ℝ) := fun z => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (f z) z.1
  have hcoords : inTangentCoordinates 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      Prod.fst (fun z => f z z.1) d q = d :=
    inTangentCoordinates_model_space _ _ _ _
  change ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ →L[ℝ] ℝ) ∞
    (inTangentCoordinates 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) Prod.fst (fun z => f z z.1) d q) q at hd
  rw [hcoords] at hd
  have heval := hd.clm_apply (contMDiffAt_const (c := (1 : ℝ)))
  simpa only [d, f, mfderiv_eq_fderiv, fderiv_apply_one_eq_deriv] using heval

variable [CompactSpace M]

theorem bounded_time_derivative_of_fixed_exterior {κ : ℝ × M → ℝ}
    (hκ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ κ)
    {a b : ℝ} (hfix : ∀ t x, t ∉ Ioo a b → κ (t, x) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ × M, ‖deriv (fun t => κ (t, q.2)) q.1‖ ≤ C := by
  let d : ℝ × M → ℝ := fun q => deriv (fun t => κ (t, q.2)) q.1
  have hd : Continuous d := (smooth_time_derivative hκ).continuous
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_univ (X := M))).exists_bound_of_continuousOn
    hd.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro q
  by_cases hq : q.1 ∈ Icc a b
  · exact (hC q ⟨hq, mem_univ _⟩).trans (le_max_left _ _)
  · have heq : (fun t => κ (t, q.2)) =ᶠ[𝓝 q.1] (fun _ => (0 : ℝ)) := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hq] with t ht
      exact hfix t q.2 (fun h => ht ⟨h.1.le, h.2.le⟩)
    have hzero : deriv (fun t => κ (t, q.2)) q.1 = 0 :=
      heq.deriv_eq.trans (deriv_const _ _)
    rw [hzero, norm_zero]
    exact le_max_right _ _

theorem exists_radius_positive_scalar_clock {κ : ℝ × M → ℝ}
    (hκ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ κ)
    {a b : ℝ} (hfix : ∀ t x, t ∉ Ioo a b → κ (t, x) = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, ‖δ‖ < ε →
      ∀ x t, 0 < deriv (fun s => s + δ * κ (s, x)) t := by
  obtain ⟨C, hC, hbound⟩ := bounded_time_derivative_of_fixed_exterior hκ hfix
  have hCp : 0 < C + 1 := by linarith
  refine ⟨1 / (C + 1), one_div_pos.mpr hCp, ?_⟩
  intro δ hδ x t
  have hδC : ‖δ‖ * (C + 1) < 1 := (lt_div_iff₀ hCp).mp hδ
  have hnorm : ‖δ * deriv (fun s => κ (s, x)) t‖ < 1 := by
    rw [norm_mul]
    calc
      ‖δ‖ * ‖deriv (fun s => κ (s, x)) t‖ ≤ ‖δ‖ * C :=
        mul_le_mul_of_nonneg_left (hbound (t, x)) (norm_nonneg δ)
      _ ≤ ‖δ‖ * (C + 1) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg δ)
      _ < 1 := hδC
  have hs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => κ (s, x)) :=
    hκ.comp (contMDiff_id.prodMk contMDiff_const)
  have hsd := (hs.mdifferentiableAt (x := t) (by simp)).differentiableAt.hasDerivAt
  have hderiv := ((hasDerivAt_id t).add (hsd.const_mul δ)).deriv
  change deriv (fun s => s + δ * κ (s, x)) t =
    1 + δ * deriv (fun s => κ (s, x)) t at hderiv
  rw [hderiv]
  have hlow := (abs_lt.mp (show |δ * deriv (fun s => κ (s, x)) t| < 1 from hnorm)).1
  linarith

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
