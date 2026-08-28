import Wikipedia.HopfProblem.EllipticFiniteQuotient

/-!
# Descending invariant fibrations through the finite orbit quotient

An invariant map from the covering manifold descends to the actual orbit
quotient.  Continuity, surjectivity, properness, and holomorphicity are
proved for this descended map.  In particular, properness is inherited
from the map upstairs and is not supplied as additional quotient data.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic.FiniteQuotient

variable {G M B : Type*} [Group G] [MulAction G M]
    (f : M → B) (hf : ∀ (g : G) (x : M), f (g • x) = f x)

/-- The actual quotient lift of a map constant on the group orbits. -/
def descend : Space G M → B :=
  Quotient.lift f (by
    rintro x y ⟨g, hg⟩
    rw [← hg]
    exact hf g y)

@[simp] theorem descend_project (x : M) : descend f hf (project G M x) = f x := rfl

@[simp] theorem descend_comp_project : descend f hf ∘ project G M = f := rfl

theorem descend_surjective (hs : Function.Surjective f) :
    Function.Surjective (descend f hf) := by
  intro b
  obtain ⟨x, hx⟩ := hs b
  exact ⟨project G M x, hx⟩

/-- Inverse images downstairs are the images of the corresponding inverse
images upstairs. -/
theorem descend_preimage_eq_image (K : Set B) :
    descend f hf ⁻¹' K = project G M '' (f ⁻¹' K) := by
  ext q
  obtain ⟨x, rfl⟩ := project_surjective G M q
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hxy⟩
    change descend f hf (project G M x) ∈ K
    rw [← hxy, descend_project]
    exact hy

section Topology

variable [TopologicalSpace M] [TopologicalSpace B]

theorem descend_continuous (hc : Continuous f) : Continuous (descend f hf) :=
  (project_isQuotientMap G M).continuous_iff.mpr hc

theorem descend_continuous_iff : Continuous (descend f hf) ↔ Continuous f :=
  (project_isQuotientMap G M).continuous_iff

/-- Proper maps upstairs give proper maps from the quotient, with no
extra separation or local-compactness hypothesis on the base. -/
theorem descend_isProperMap (hp : IsProperMap f) : IsProperMap (descend f hf) :=
  isProperMap_of_comp_of_surj (project_continuous G M)
    (descend_continuous f hf hp.continuous) hp (project_surjective G M)

theorem descend_isCompact_preimage (hp : IsProperMap f) {K : Set B} (hK : IsCompact K) :
    IsCompact (descend f hf ⁻¹' K) := by
  rw [descend_preimage_eq_image]
  exact (hp.isCompact_preimage hK).image (project_continuous G M)

end Topology

section ComplexStructure

variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace B] [ChartedSpace H B]
    [IsManifold (modelWithCornersSelf ℂ E) ω M]
    [Finite G] [LocallyCompactSpace M] [T2Space M]
    [ContinuousConstSMul G M] [IsCancelSMul G M]

/-- Holomorphicity descends in the complex atlas constructed from the
quotient covering map. -/
theorem descend_holomorphic (I : ModelWithCorners ℂ F H)
    (hh : ContMDiff (modelWithCornersSelf ℂ E) I ω f) :
    letI := chartedSpace (E := E) G M
    ContMDiff (modelWithCornersSelf ℂ E) I ω (descend f hf) :=
  CoveringQuotient.contMDiff_of_comp (project_isQuotientCoveringMap G M) I ω hh

end ComplexStructure

end Wikipedia.HopfProblem.Elliptic.FiniteQuotient
