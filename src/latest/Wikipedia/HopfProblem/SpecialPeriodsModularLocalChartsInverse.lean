import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Analytic local coordinates from the inverse function theorem

The inverse function theorem initially gives an open partial homeomorphism
and analyticity at the distinguished points.  Restricting its source and
target to the open analytic loci gives an actual biholomorphic coordinate
map, analytic on every point of its declared source and target.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- A nonzero complex derivative gives an actual analytic local coordinate
map, with the original function as its forward map everywhere. -/
theorem exists_analytic_openPartialHomeomorph {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hderiv : deriv f x ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      x ∈ e.source ∧ (∀ z, e z = f z) ∧
      AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target := by
  let e₀ : OpenPartialHomeomorph ℂ ℂ :=
    (hf.hasStrictDerivAt.hasStrictFDerivAt_equiv hderiv).toOpenPartialHomeomorph f
  have hx : x ∈ e₀.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  have hi : AnalyticAt ℂ e₀.symm (f x) := hf.analyticAt_localInverse hderiv
  let e₁ := e₀.restrOpen {z | AnalyticAt ℂ f z} (isOpen_analyticAt ℂ f)
  let e := (e₁.symm.restrOpen {z | AnalyticAt ℂ e₀.symm z}
    (isOpen_analyticAt ℂ e₀.symm)).symm
  refine ⟨e, ?_, ?_, ?_, ?_⟩
  · change (x ∈ e₀.source ∧ AnalyticAt ℂ f x) ∧ AnalyticAt ℂ e₀.symm (f x)
    exact ⟨⟨hx, hf⟩, hi⟩
  · intro z
    rfl
  · intro z hz
    change AnalyticAt ℂ f z
    exact hz.1.2
  · intro z hz
    change AnalyticAt ℂ e₀.symm z
    exact hz.2

end Wikipedia.HopfProblem.SpecialPeriods
