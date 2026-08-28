import Wikipedia.HopfProblem.SmoothMorseLemmaResult
import Wikipedia.HopfProblem.SmoothMorseLemmaLocalization
import Wikipedia.HopfProblem.SmoothMorseLemmaCharts

/-!
# The smooth Morse lemma at an arbitrary point of an open domain

Translation gives the theorem at any critical point. A genuine smooth
compactly supported representative then removes global smoothness from
the hypotheses. Restricting the resulting native partial diffeomorphism
inside the original domain preserves its literal forward and inverse
normal-form identities for the original function.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SmoothMorseLemma

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The smooth Morse lemma at any actual nondegenerate critical point. -/
theorem exists_morse_chart {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (a : E)
    (hc : fderiv ℝ f a = 0)
    (hn : Function.Bijective (fderiv ℝ (fderiv ℝ f) a)) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      a ∈ e.source ∧ e a = 0 ∧
      HasFDerivAt e (ContinuousLinearMap.id ℝ E) a ∧
      (∀ x ∈ e.source,
        f x = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a (e x) (e x)) ∧
      (∀ y ∈ e.target,
        f (e.symm y) = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a y y) := by
  let g : E → ℝ := fun x => f (a + x)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_const.add contDiff_id)
  have hgc : fderiv ℝ g 0 = 0 := by
    simpa only [g, fderiv_comp_add_left, add_zero] using hc
  have hgn : Function.Bijective (fderiv ℝ (fderiv ℝ g) 0) := by
    simpa only [g, hessian_comp_add_left, add_zero] using hn
  obtain ⟨e, he0, hezero, hederiv, hnormal, _⟩ := exists_morse_chart_zero hg hgc hgn
  let φ := translateChart a e
  have haφ : a ∈ φ.source := by
    change a ∈ (translateChart a e).source
    rw [mem_translateChart_source, sub_self]
    exact he0
  have hφzero : φ a = 0 := by
    change e (a - a) = 0
    rw [sub_self, hezero]
  have hφderiv : HasFDerivAt φ (ContinuousLinearMap.id ℝ E) a := by
    have hφfun : (φ : E → E) = fun x => e (x - a) :=
      funext (translateChart_apply a e)
    rw [hφfun]
    have hdshift : HasFDerivAt (fun x : E => x - a) (ContinuousLinearMap.id ℝ E) a :=
      (hasFDerivAt_id a).sub_const a
    have hdouter : HasFDerivAt e (ContinuousLinearMap.id ℝ E) (a - a) := by
      simpa only [sub_self] using hederiv
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      hdouter.comp (f := fun x : E => x - a) a hdshift
  have hφnormal (x : E) (hx : x ∈ φ.source) :
      f x = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a (φ x) (φ x) := by
    have hx' : x - a ∈ e.source := (mem_translateChart_source a e x).mp hx
    have hpoint : a + (x - a) = x := by simp [sub_eq_add_neg]
    simpa only [g, hessian_comp_add_left, add_zero, hpoint, φ, translateChart_apply] using
      hnormal (x - a) hx'
  refine ⟨φ, haφ, hφzero, hφderiv, hφnormal, ?_⟩
  intro y hy
  have hr : φ (φ.symm y) = y := φ.right_inv hy
  simpa only [hr] using hφnormal (φ.symm y) (φ.map_target hy)

/-- The genuine local smooth Morse lemma. Smoothness is required only on
the original open set, and the actual chart source lies inside that set. -/
theorem exists_morse_chart_of_contDiffOn {f : E → ℝ} {U : Set E}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (a : E) (ha : a ∈ U)
    (hc : fderiv ℝ f a = 0)
    (hn : Function.Bijective (fderiv ℝ (fderiv ℝ f) a)) :
    ∃ e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
      a ∈ e.source ∧ e.source ⊆ U ∧ e a = 0 ∧
      HasFDerivAt e (ContinuousLinearMap.id ℝ E) a ∧
      (∀ x ∈ e.source,
        f x = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a (e x) (e x)) ∧
      (∀ y ∈ e.target,
        f (e.symm y) = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a y y) := by
  obtain ⟨g, hg, heq, hga, hdf, hH, _⟩ :=
    exists_contDiff_extension_preserving_derivatives hf hU ha
  have hgc : fderiv ℝ g a = 0 := hdf.trans hc
  have hgn : Function.Bijective (fderiv ℝ (fderiv ℝ g) a) := by
    rw [hH]
    exact hn
  obtain ⟨e, hea, hezero, hederiv, hnormal, _⟩ := exists_morse_chart hg a hgc hgn
  obtain ⟨W, hWsub, hWopen, haW⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds ha) heq)
  let φ := restrictChart e W hWopen
  have haφ : a ∈ φ.source := ⟨hea, haW⟩
  have hφU : φ.source ⊆ U := fun _ hx => (hWsub hx.2).1
  have hφnormal (x : E) (hx : x ∈ φ.source) :
      f x = f a + (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) a (φ x) (φ x) := by
    have hxeq : g x = f x := (hWsub hx.2).2
    simpa only [φ, restrictChart_apply, hxeq, hga, hH] using hnormal x hx.1
  refine ⟨φ, haφ, hφU, hezero, hederiv, hφnormal, ?_⟩
  intro y hy
  have hr : φ (φ.symm y) = y := φ.right_inv hy
  simpa only [hr] using hφnormal (φ.symm y) (φ.map_target hy)

end Wikipedia.HopfProblem.SmoothMorseLemma
