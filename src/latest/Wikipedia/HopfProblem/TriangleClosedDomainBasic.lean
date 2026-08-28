import Wikipedia.HopfProblem.TriangleClosedDomainGeometry
import Wikipedia.HopfProblem.TriangleClosedDomainInfinity
import Wikipedia.HopfProblem.RiemannMappingTriangle

/-!
# The actual compact closure of the source triangle

The closed source is the closure of the finite image of the actual triangle
in `OnePoint ℂ`, with the inherited topology.  Its original interior is an
open dense subspace and is homeomorphic to the actual `triangleDomain`.
Compactness and separation come from this concrete compactification, not
from an assumed homeomorphism to a closed disc.
-/

noncomputable section

open Set Filter Topology
open scoped OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

open RiemannBoundary RiemannMapping

/-- The literal closure of the finite source image in the one-point plane. -/
def triangleClosedSet : Set (OnePoint ℂ) :=
  closure (onePointDomain triangleInterior)

/-- The actual closed source, with its inherited subspace topology. -/
abbrev TriangleClosedDomain := triangleClosedSet

theorem triangleClosedSet_isClosed : IsClosed triangleClosedSet := isClosed_closure

theorem triangleClosedSet_isCompact : IsCompact triangleClosedSet :=
  triangleClosedSet_isClosed.isCompact

instance triangleClosedDomain_compactSpace : CompactSpace TriangleClosedDomain :=
  isCompact_iff_compactSpace.mp triangleClosedSet_isCompact

instance triangleClosedDomain_t2Space : T2Space TriangleClosedDomain := inferInstance

/-- Finite closure membership is exactly ordinary complex closure membership. -/
theorem coe_mem_triangleClosedSet_iff_closure (z : ℂ) :
    (z : OnePoint ℂ) ∈ triangleClosedSet ↔ z ∈ closure triangleInterior := by
  change z ∈ ((↑) : ℂ → OnePoint ℂ) ⁻¹'
    closure (((↑) : ℂ → OnePoint ℂ) '' triangleInterior) ↔ _
  rw [← OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image]

/-- The finite part consists of the actual closed half-Ford inequalities. -/
theorem coe_mem_triangleClosedSet_iff (z : ℂ) :
    (z : OnePoint ℂ) ∈ triangleClosedSet ↔
      stripLeft ≤ z.re ∧ z.re ≤ -1 / 2 ∧ 0 < z.im ∧ 1 ≤ ‖z + 1‖ := by
  rw [coe_mem_triangleClosedSet_iff_closure, closure_triangleInterior]
  rfl

theorem triangleClosedSet_finite_height_floor {z : ℂ}
    (hz : (z : OnePoint ℂ) ∈ triangleClosedSet) : stripRight ≤ z.im :=
  triangleClosedRegion_im_lower_bound ((coe_mem_triangleClosedSet_iff z).mp hz)

theorem triangleClosedSet_no_real_points {z : ℂ} (hz : z.im = 0) :
    (z : OnePoint ℂ) ∉ triangleClosedSet := by
  intro h
  have hp := (coe_mem_triangleClosedSet_iff z).mp h
  exact hp.2.2.1.ne' hz

theorem infty_mem_triangleClosedSet : (∞ : OnePoint ℂ) ∈ triangleClosedSet :=
  triangle_infty_mem_closure

/-- The ideal vertex is an actual point of the closed source. -/
def triangleClosedInfinity : TriangleClosedDomain := ⟨∞, infty_mem_triangleClosedSet⟩

/-- The actual source image, now regarded inside its own compact closure. -/
def triangleClosedInterior : TopologicalSpace.Opens TriangleClosedDomain :=
  ⟨{x | x.val ∈ onePointDomain triangleInterior},
    (isOpen_onePointDomain triangleInterior_isOpen).preimage continuous_subtype_val⟩

@[simp] theorem mem_triangleClosedInterior (x : TriangleClosedDomain) :
    x ∈ triangleClosedInterior ↔ x.val ∈ onePointDomain triangleInterior := Iff.rfl

@[simp] theorem coe_mem_triangleClosedInterior {z : ℂ}
    (hz : (z : OnePoint ℂ) ∈ triangleClosedSet) :
    (⟨(z : OnePoint ℂ), hz⟩ : TriangleClosedDomain) ∈ triangleClosedInterior ↔
      z ∈ triangleInterior :=
  coe_mem_onePointDomain

@[simp] theorem triangleClosedInfinity_notMem_interior :
    triangleClosedInfinity ∉ triangleClosedInterior :=
  infty_notMem_onePointDomain triangleInterior

theorem triangleClosedInterior_isOpen :
    IsOpen (triangleClosedInterior : Set TriangleClosedDomain) := triangleClosedInterior.isOpen

/-- The original interior is dense in this very closed source. -/
theorem triangleClosedInterior_dense :
    Dense (triangleClosedInterior : Set TriangleClosedDomain) := by
  have hi : ((↑) : TriangleClosedDomain → OnePoint ℂ) ''
      (triangleClosedInterior : Set TriangleClosedDomain) =
      onePointDomain triangleInterior := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, subset_closure hx⟩, hx, rfl⟩
  apply Subtype.dense_iff.mpr
  rw [hi]
  exact Subset.refl _

/-- The original complex domain maps to its actual finite points in the closure. -/
def triangleClosedInclusion (z : triangleDomain) : TriangleClosedDomain :=
  ⟨(z : ℂ), subset_closure (coe_mem_onePointDomain.mpr z.property)⟩

@[simp] theorem triangleClosedInclusion_val (z : triangleDomain) :
    (triangleClosedInclusion z : OnePoint ℂ) = (z : ℂ) := rfl

theorem triangleClosedInclusion_continuous : Continuous triangleClosedInclusion :=
  (OnePoint.continuous_coe.comp continuous_subtype_val).subtype_mk _

theorem triangleClosedInclusion_mem_interior (z : triangleDomain) :
    triangleClosedInclusion z ∈ triangleClosedInterior :=
  coe_mem_onePointDomain.mpr z.property

/-- The original analytic domain and the dense open part have exactly their
natural subspace topologies. -/
def triangleClosedInteriorHomeomorph : triangleDomain ≃ₜ triangleClosedInterior where
  toFun z := ⟨triangleClosedInclusion z, triangleClosedInclusion_mem_interior z⟩
  invFun x := (onePointDomainHomeomorph triangleInterior).symm ⟨x.val.val, x.property⟩
  left_inv z := by
    exact (onePointDomainHomeomorph triangleInterior).symm_apply_apply z
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : onePointDomain triangleInterior => (y : OnePoint ℂ))
      ((onePointDomainHomeomorph triangleInterior).apply_symm_apply ⟨x.val.val, x.property⟩)
  continuous_toFun := triangleClosedInclusion_continuous.subtype_mk _
  continuous_invFun :=
    (onePointDomainHomeomorph triangleInterior).symm.continuous.comp
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

@[simp] theorem triangleClosedInteriorHomeomorph_apply (z : triangleDomain) :
    ((triangleClosedInteriorHomeomorph z : TriangleClosedDomain) : OnePoint ℂ) =
      (z : ℂ) := rfl

@[simp] theorem triangleClosedInteriorHomeomorph_symm_apply
    (x : triangleClosedInterior) :
    ((triangleClosedInteriorHomeomorph.symm x : ℂ) : OnePoint ℂ) = x.val.val := by
  exact congrArg (fun y : triangleClosedInterior => y.val.val)
    (triangleClosedInteriorHomeomorph.apply_symm_apply x)

/-- The given interior Riemann map is a genuine disc homeomorphism on the
actual dense open subset of the compact source. -/
def triangleClosedInteriorDiscHomeomorph :
    triangleClosedInterior ≃ₜ Metric.ball (0 : ℂ) 1 :=
  triangleClosedInteriorHomeomorph.symm.trans triangleBiholomorph.toHomeomorph

@[simp] theorem triangleClosedInteriorDiscHomeomorph_apply (z : triangleDomain) :
    triangleClosedInteriorDiscHomeomorph (triangleClosedInteriorHomeomorph z) =
      triangleBiholomorph z := by
  change triangleBiholomorph
    (triangleClosedInteriorHomeomorph.symm (triangleClosedInteriorHomeomorph z)) = _
  rw [triangleClosedInteriorHomeomorph.symm_apply_apply]

/-- Passing to the closed-source subtype does not alter the ambient
finite frontier condition. -/
theorem coe_mem_triangleOnePoint_frontier_iff (z : ℂ) :
    (z : OnePoint ℂ) ∈ frontier (onePointDomain triangleInterior) ↔
      z ∈ frontier triangleInterior := by
  change ((z : OnePoint ℂ) ∈ closure (onePointDomain triangleInterior) ∧
      (z : OnePoint ℂ) ∉ interior (onePointDomain triangleInterior)) ↔
    (z ∈ closure triangleInterior ∧ z ∉ interior triangleInterior)
  rw [(isOpen_onePointDomain triangleInterior_isOpen).interior_eq,
    triangleInterior_isOpen.interior_eq]
  exact and_congr (coe_mem_triangleClosedSet_iff_closure z)
    (not_congr coe_mem_onePointDomain)

/-- Boundary membership in the closed source is precisely ambient
frontier membership of its original open interior image. -/
theorem triangleClosedBoundary_iff_frontier (x : TriangleClosedDomain) :
    x ∉ triangleClosedInterior ↔ x.val ∈ frontier (onePointDomain triangleInterior) := by
  change x.val ∉ onePointDomain triangleInterior ↔
    x.val ∈ closure (onePointDomain triangleInterior) ∧
      x.val ∉ interior (onePointDomain triangleInterior)
  rw [(isOpen_onePointDomain triangleInterior_isOpen).interior_eq]
  exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
