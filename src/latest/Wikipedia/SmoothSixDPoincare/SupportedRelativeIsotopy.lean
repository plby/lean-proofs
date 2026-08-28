import Wikipedia.SmoothSixDPoincare.AmbientIsotopy

/-! # Native isotopies with a common support and a fixed subset -/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- Keep the supported relative motion itself, not only an unqualified isotopy witness. -/
structure SupportedRelativeIsotopy (e : Diffeomorph J J M M ∞) (K S : Set M) where
  family : ℝ × M → M
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ family
  zero : ∀ x, family (0, x) = x
  one : ∀ x, family (1, x) = e x
  slices : ∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ x, d x = family (t, x)
  fixedOutside : ∀ t x, x ∉ K → family (t, x) = x
  fixedOn : ∀ t x, x ∈ S → family (t, x) = x

namespace SupportedRelativeIsotopy

variable {e : Diffeomorph J J M M ∞} {K S : Set M}
  (A : SupportedRelativeIsotopy e K S)

include A

theorem isotopicToIdentity : IsotopicToIdentity e := by
  refine ⟨A.family, A.smooth, A.zero, A.one, ?_⟩
  intro t
  obtain ⟨d, hd⟩ := A.slices t
  exact ⟨d, fun x => (hd x).symm⟩

theorem endpoint_fixed_outside (x : M) (hx : x ∉ K) : e x = x :=
  (A.one x).symm.trans (A.fixedOutside 1 x hx)

theorem endpoint_fixed_on (x : M) (hx : x ∈ S) : e x = x :=
  (A.one x).symm.trans (A.fixedOn 1 x hx)

end SupportedRelativeIsotopy

end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph
