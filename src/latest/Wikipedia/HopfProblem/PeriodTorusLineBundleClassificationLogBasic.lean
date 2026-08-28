import Wikipedia.HopfProblem.PeriodTori
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Topology.Homotopy.Lifting

/-!
# Actual entire logarithms on the covering plane

The exponential covering map supplies a normalized continuous lift on the
contractible space `ℂ²`. Near each point that lift is a principal logarithm
of the normalized original function, up to an additive constant, so it is
analytic. No global logarithm is an assumption.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

open Complex Filter Set
open scoped Topology ContDiff

theorem exists_normalized_continuous_logarithm (f : ComplexPlane₂ → ℂ)
    (hf : Continuous f) (hne : ∀ z, f z ≠ 0) :
    ∃ b : ComplexPlane₂ → ℂ, Continuous b ∧ (∀ z, Complex.exp (b z) = f z) ∧
      b 0 = Complex.log (f 0) := by
  let fc : C(ComplexPlane₂, ℂ) := ⟨f, hf⟩
  have hs : ∀ z, fc z ∈ ({0} : Set ℂ)ᶜ := by
    intro z
    change f z ≠ 0
    exact hne z
  obtain ⟨b, hb, _⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    fc (a₀ := 0) (e₀ := Complex.log (f 0)) (Complex.exp_log (hne 0)) hs
  refine ⟨b, b.continuous, ?_, hb.1⟩
  intro z
  exact congrFun hb.2 z

/-- Continuous exponential lifts with the same initial value agree globally. -/
theorem continuous_exp_lift_eq (b c : ComplexPlane₂ → ℂ)
    (hb : Continuous b) (hc : Continuous c)
    (he : ∀ z, Complex.exp (b z) = Complex.exp (c z)) (h0 : b 0 = c 0) : b = c := by
  apply Complex.isCoveringMap_exp.eq_of_comp_eq hb hc ?_ 0 h0
  funext z
  exact Subtype.ext (he z)

theorem continuous_exp_eq_one_constant (b : ComplexPlane₂ → ℂ)
    (hb : Continuous b) (he : ∀ z, Complex.exp (b z) = 1) (z : ComplexPlane₂) :
    b z = b 0 := by
  have h := continuous_exp_lift_eq b (fun _ => b 0) hb continuous_const
    (fun w => (he w).trans (he 0).symm) rfl
  exact congrFun h z

/-- A continuous logarithmic lift of an analytic function is itself analytic. -/
theorem analyticAt_continuous_exp_lift (f b : ComplexPlane₂ → ℂ) (x : ComplexPlane₂)
    (hf : AnalyticAt ℂ f x) (hb : ContinuousAt b x)
    (he : ∀ z, Complex.exp (b z) = f z) : AnalyticAt ℂ b x := by
  have hne : f x ≠ 0 := by
    rw [← he x]
    exact Complex.exp_ne_zero _
  have hlim : Tendsto (fun z => (b z - b x).im) (𝓝 x) (𝓝 (0 : ℝ)) := by
    have hsub : ContinuousAt (fun z => b z - b x) x := hb.sub continuousAt_const
    simpa only [ContinuousAt, Function.comp_def, sub_self, Complex.zero_im] using
      Complex.continuous_im.continuousAt.comp hsub
  have hstrip : ∀ᶠ z in 𝓝 x, -Real.pi < (b z - b x).im ∧
      (b z - b x).im < Real.pi :=
    hlim.eventually (Ioo_mem_nhds (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos)
  have hlocal : (fun z => b x + Complex.log (f z / f x)) =ᶠ[𝓝 x] b := by
    filter_upwards [hstrip] with z hz
    rw [← he z, ← he x, ← Complex.exp_sub, Complex.log_exp hz.1 hz.2.le]
    ring
  have hratio : AnalyticAt ℂ (fun z => f z / f x) x := hf.div analyticAt_const hne
  have hslit : f x / f x ∈ Complex.slitPlane := by simp [hne]
  exact (analyticAt_const.add (hratio.clog hslit)).congr hlocal

/-- A nowhere-zero entire function on `ℂ²` has an actual normalized entire logarithm. -/
theorem exists_normalized_entire_logarithm (f : ComplexPlane₂ → ℂ)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hne : ∀ z, f z ≠ 0) :
    ∃ b : ComplexPlane₂ → ℂ, AnalyticOnNhd ℂ b Set.univ ∧
      (∀ z, Complex.exp (b z) = f z) ∧ b 0 = Complex.log (f 0) := by
  have hfc : Continuous f := by simpa only [continuousOn_univ] using hf.continuousOn
  obtain ⟨b, hb, he, h0⟩ := exists_normalized_continuous_logarithm f hfc hne
  refine ⟨b, ?_, he, h0⟩
  intro x _
  exact analyticAt_continuous_exp_lift f b x (hf x (Set.mem_univ x)) hb.continuousAt he

theorem existsUnique_normalized_entire_logarithm (f : ComplexPlane₂ → ℂ)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hne : ∀ z, f z ≠ 0) :
    ∃! b : ComplexPlane₂ → ℂ, AnalyticOnNhd ℂ b Set.univ ∧
      (∀ z, Complex.exp (b z) = f z) ∧ b 0 = Complex.log (f 0) := by
  obtain ⟨b, hb, he, h0⟩ := exists_normalized_entire_logarithm f hf hne
  refine ⟨b, ⟨hb, he, h0⟩, ?_⟩
  rintro c ⟨hc, hce, hc0⟩
  apply continuous_exp_lift_eq c b
    (by simpa only [continuousOn_univ] using hc.continuousOn)
    (by simpa only [continuousOn_univ] using hb.continuousOn)
  · intro z
    exact (hce z).trans (he z).symm
  · exact hc0.trans h0.symm

/-- The normalized logarithm selected from the actual existence theorem. -/
def normalizedEntireLog (f : ComplexPlane₂ → ℂ)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hne : ∀ z, f z ≠ 0) : ComplexPlane₂ → ℂ :=
  (exists_normalized_entire_logarithm f hf hne).choose

theorem normalizedEntireLog_analytic (f : ComplexPlane₂ → ℂ)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hne : ∀ z, f z ≠ 0) :
    AnalyticOnNhd ℂ (normalizedEntireLog f hf hne) Set.univ :=
  (exists_normalized_entire_logarithm f hf hne).choose_spec.1

theorem normalizedEntireLog_exp (f : ComplexPlane₂ → ℂ)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hne : ∀ z, f z ≠ 0) (z : ComplexPlane₂) :
    Complex.exp (normalizedEntireLog f hf hne z) = f z :=
  (exists_normalized_entire_logarithm f hf hne).choose_spec.2.1 z

theorem normalizedEntireLog_zero (f : ComplexPlane₂ → ℂ)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hne : ∀ z, f z ≠ 0) :
    normalizedEntireLog f hf hne 0 = Complex.log (f 0) :=
  (exists_normalized_entire_logarithm f hf hne).choose_spec.2.2

theorem normalizedEntireLog_holomorphic (f : ComplexPlane₂ → ℂ)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hne : ∀ z, f z ≠ 0) :
    ContDiff ℂ ω (normalizedEntireLog f hf hne) :=
  (normalizedEntireLog_analytic f hf hne).contDiff

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
