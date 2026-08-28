import Wikipedia.HopfProblem.TriangleClosedDomainBasic
import Wikipedia.HopfProblem.TriangleRiemannIdealComparison
import Wikipedia.HopfProblem.RiemannBoundaryCompactification

/-!
# Boundary-limit filters for the actual closed triangle

The dense open part of the actual triangle closure is exactly its finite
one-point image.  We identify these two subspaces and their approach
filters, including at the ideal point.  Consequently the previously
constructed forward and inverse boundary limits transfer to the compact
source without any additional boundary-continuity assumption.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

open RiemannBoundary RiemannMapping

/-- Flattening the two actual subtypes identifies the open interior of
the closed source with its finite one-point image. -/
def triangleClosedInteriorToOnePoint :
    triangleClosedInterior ≃ₜ onePointDomain triangleInterior where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, subset_closure x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp] theorem triangleClosedInteriorToOnePoint_val (x : triangleClosedInterior) :
    (triangleClosedInteriorToOnePoint x : OnePoint ℂ) = x.val.val := rfl

@[simp] theorem triangleClosedInteriorToOnePoint_symm_val
    (x : onePointDomain triangleInterior) :
    (triangleClosedInteriorToOnePoint.symm x).val.val = x.val := rfl

/-- The two actual disc maps agree under the natural identification. -/
@[simp] theorem triangleClosedInteriorDiscHomeomorph_onePoint
    (x : triangleClosedInterior) :
    triangleDiscOnOnePointDomain (triangleClosedInteriorToOnePoint x) =
      triangleClosedInteriorDiscHomeomorph x := rfl

theorem triangleClosedInteriorDiscHomeomorph_onePoint_symm
    (w : ball (0 : ℂ) 1) :
    triangleClosedInteriorToOnePoint (triangleClosedInteriorDiscHomeomorph.symm w) =
      triangleDiscOnOnePointDomain.symm w := by
  apply triangleDiscOnOnePointDomain.injective
  rw [triangleClosedInteriorDiscHomeomorph_onePoint,
    triangleClosedInteriorDiscHomeomorph.apply_symm_apply,
    triangleDiscOnOnePointDomain.apply_symm_apply]

/-- Approach to a point of the closed source has exactly the ambient
one-point filter after flattening the actual interior subtypes. -/
theorem triangleClosedInterior_comap_onePoint_filter (x : TriangleClosedDomain) :
    comap triangleClosedInteriorToOnePoint
        (comap (Subtype.val : onePointDomain triangleInterior → OnePoint ℂ) (𝓝 x.val)) =
      comap (Subtype.val : triangleClosedInterior → TriangleClosedDomain) (𝓝 x) := by
  rw [nhds_subtype_eq_comap, comap_comap, comap_comap]
  rfl

theorem triangleClosedInterior_map_onePoint_filter (x : TriangleClosedDomain) :
    map triangleClosedInteriorToOnePoint
        (comap (Subtype.val : triangleClosedInterior → TriangleClosedDomain) (𝓝 x)) =
      comap (Subtype.val : onePointDomain triangleInterior → OnePoint ℂ) (𝓝 x.val) := by
  rw [← triangleClosedInterior_comap_onePoint_filter x,
    map_comap_of_surjective triangleClosedInteriorToOnePoint.surjective]

/-- Forward convergence for the dense open part is unchanged by its
exact identification with the finite one-point domain. -/
theorem triangleClosedInterior_forward_tendsto_iff (x : TriangleClosedDomain)
    {l : Filter ℂ} :
    Tendsto (fun z : triangleClosedInterior => (triangleClosedInteriorDiscHomeomorph z : ℂ))
        (comap (Subtype.val : triangleClosedInterior → TriangleClosedDomain) (𝓝 x)) l ↔
      Tendsto (fun z : onePointDomain triangleInterior => (triangleDiscOnOnePointDomain z : ℂ))
        (comap (Subtype.val : onePointDomain triangleInterior → OnePoint ℂ) (𝓝 x.val)) l := by
  rw [← triangleClosedInterior_map_onePoint_filter x, tendsto_map'_iff]
  rfl

/-- The ambient representative is only read on the original interior,
so its arbitrary value at infinity plays no role in forward limits. -/
theorem triangleClosedInterior_forward_representative_tendsto_iff
    (x : TriangleClosedDomain) {l : Filter ℂ} :
    Tendsto (fun z : triangleClosedInterior => (triangleClosedInteriorDiscHomeomorph z : ℂ))
        (comap (Subtype.val : triangleClosedInterior → TriangleClosedDomain) (𝓝 x)) l ↔
      Tendsto triangleOnePointRepresentative
        (𝓝[onePointDomain triangleInterior] x.val) l := by
  rw [triangleClosedInterior_forward_tendsto_iff]
  have he : (fun z : onePointDomain triangleInterior => (triangleDiscOnOnePointDomain z : ℂ)) =
      triangleOnePointRepresentative ∘
        (Subtype.val : onePointDomain triangleInterior → OnePoint ℂ) := by
    funext z
    exact (triangleOnePointRepresentative_homeomorph z).symm
  rw [he, ← tendsto_map'_iff, map_comap_setCoe_val]
  rfl

/-- The total inverse representatives agree after the actual inclusion
of the closed source, even at their irrelevant outside-disc values. -/
theorem triangleClosedInteriorDiscHomeomorph_inverse_coe (z : ℂ) :
    ((discHomeomorphInverse triangleClosedInteriorDiscHomeomorph z : TriangleClosedDomain) :
        OnePoint ℂ) =
      discHomeomorphInverse triangleDiscOnOnePointDomain z := by
  classical
  unfold discHomeomorphInverse
  split_ifs <;> rfl

/-- Inverse convergence in the actual closed source is precisely
inverse convergence in its inherited one-point topology. -/
theorem triangleClosedInterior_inverse_tendsto_iff (x : TriangleClosedDomain)
    {l : Filter ℂ} :
    Tendsto (discHomeomorphInverse triangleClosedInteriorDiscHomeomorph) l (𝓝 x) ↔
      Tendsto (discHomeomorphInverse triangleDiscOnOnePointDomain) l (𝓝 x.val) := by
  rw [tendsto_subtype_rng]
  simp only [triangleClosedInteriorDiscHomeomorph_inverse_coe]

/-- At finite points, the one-point approach filter is exactly the
image of the original complex approach filter. -/
theorem triangleOnePointRepresentative_finite_tendsto_iff {a : ℂ} {l : Filter ℂ} :
    Tendsto triangleOnePointRepresentative
        (𝓝[onePointDomain triangleInterior] (a : OnePoint ℂ)) l ↔
      Tendsto triangleMap (𝓝[triangleInterior] a) l := by
  change Tendsto triangleOnePointRepresentative
    (𝓝[((↑) : ℂ → OnePoint ℂ) '' triangleInterior] (a : OnePoint ℂ)) l ↔ _
  rw [OnePoint.nhdsWithin_coe_image, tendsto_map'_iff]
  rfl

/-- The actual inverse disc map on the one-point image is the finite
inclusion of the original complex inverse. -/
theorem triangleDiscOnOnePointDomain_inverse_coe (z : ℂ) :
    discHomeomorphInverse triangleDiscOnOnePointDomain z =
      ((discHomeomorphInverse triangleBiholomorph.toHomeomorph z : ℂ) : OnePoint ℂ) := by
  classical
  unfold discHomeomorphInverse
  split_ifs <;> rfl

theorem triangleDiscOnOnePointDomain_finite_inverse_tendsto_iff
    {a : ℂ} {l : Filter ℂ} :
    Tendsto (discHomeomorphInverse triangleDiscOnOnePointDomain) l
        (𝓝 (a : OnePoint ℂ)) ↔
      Tendsto (discHomeomorphInverse triangleBiholomorph.toHomeomorph) l (𝓝 a) := by
  have h := (OnePoint.isOpenEmbedding_coe (X := ℂ)).isEmbedding.tendsto_nhds_iff
    (f := discHomeomorphInverse triangleBiholomorph.toHomeomorph) (l := l) (y := a)
  simpa only [Function.comp_def, ← triangleDiscOnOnePointDomain_inverse_coe] using h.symm

/-- Actual ambient forward and inverse limits supply exactly the
boundary data required to compactify the actual closed source. -/
theorem triangleClosedDiscBoundaryLimits_of_ambient
    (h : ∀ p ∈ triangleClosedSet, p ∉ onePointDomain triangleInterior →
      ∃ w : ℂ, ‖w‖ = 1 ∧
        Tendsto triangleOnePointRepresentative (𝓝[onePointDomain triangleInterior] p) (𝓝 w) ∧
        Tendsto (discHomeomorphInverse triangleDiscOnOnePointDomain)
          (𝓝[ball (0 : ℂ) 1] w) (𝓝 p)) :
    DiscBoundaryLimits triangleClosedInteriorDiscHomeomorph := by
  intro x hx
  obtain ⟨w, hw, hf, hi⟩ := h x.val x.property hx
  exact ⟨w, hw, (triangleClosedInterior_forward_representative_tendsto_iff x).mpr hf,
    (triangleClosedInterior_inverse_tendsto_iff x).mpr hi⟩

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
