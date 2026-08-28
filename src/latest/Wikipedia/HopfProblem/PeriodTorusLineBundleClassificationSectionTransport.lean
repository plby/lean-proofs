import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIso
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Transport of actual holomorphic sections under native bundle isomorphisms

The map uses the actual fibre equivalences, and its regularity follows by
composing the original section with the actual analytic total-space map.
No scalar presentation or preselected factor is needed.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNative

variable {M E H : Type*} [TopologicalSpace M] [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [ChartedSpace H M]
    {I : ModelWithCorners ℂ E H}
    {V W : M → Type*}
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, TopologicalSpace (W x)]
    [TopologicalSpace (TotalSpace ℂ V)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ V] [FiberBundle ℂ W]

namespace AnalyticBundleIso

def mapSection (e : AnalyticBundleIso I V W) (s : ContMDiffSection I ℂ ω V) :
    ContMDiffSection I ℂ ω W where
  toFun x := e.fiberEquiv x (s x)
  contMDiff_toFun := by
    simpa only [Function.comp_def, e.map_fiber] using e.diffeomorph.contMDiff.comp s.contMDiff

@[simp]
theorem mapSection_apply (e : AnalyticBundleIso I V W)
    (s : ContMDiffSection I ℂ ω V) (x : M) : e.mapSection s x = e.fiberEquiv x (s x) := rfl

/-- Native analytic isomorphisms give an actual bijection of holomorphic sections. -/
def sectionEquiv (e : AnalyticBundleIso I V W) :
    ContMDiffSection I ℂ ω V ≃ ContMDiffSection I ℂ ω W where
  toFun := e.mapSection
  invFun := e.symm.mapSection
  left_inv s := by
    ext x
    exact (e.fiberEquiv x).symm_apply_apply (s x)
  right_inv s := by
    ext x
    exact (e.fiberEquiv x).apply_symm_apply (s x)

@[simp]
theorem sectionEquiv_apply (e : AnalyticBundleIso I V W)
    (s : ContMDiffSection I ℂ ω V) (x : M) : e.sectionEquiv s x = e.fiberEquiv x (s x) := rfl

theorem sectionEquiv_value_ne_zero_iff (e : AnalyticBundleIso I V W)
    (s : ContMDiffSection I ℂ ω V) (x : M) : e.sectionEquiv s x ≠ 0 ↔ s x ≠ 0 := by
  rw [sectionEquiv_apply]
  constructor
  · intro h hs
    exact h (by rw [hs, map_zero])
  · intro h hs
    apply h
    exact (e.fiberEquiv x).injective (hs.trans (map_zero _).symm)

/-- Pointwise scalar proportionality is preserved in both directions;
the statement does not replace sections by formal ratios. -/
theorem sectionEquiv_eq_smul_iff (e : AnalyticBundleIso I V W)
    (s t : ContMDiffSection I ℂ ω V) (c : ℂ) :
    (∀ x, e.sectionEquiv t x = c • e.sectionEquiv s x) ↔ ∀ x, t x = c • s x := by
  constructor
  · intro h x
    apply (e.fiberEquiv x).injective
    simpa only [sectionEquiv_apply, map_smul] using h x
  · intro h x
    simp only [sectionEquiv_apply, h x, map_smul]

end AnalyticBundleIso

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNative
