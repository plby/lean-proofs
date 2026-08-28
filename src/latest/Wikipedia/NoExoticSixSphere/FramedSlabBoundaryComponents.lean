import Wikipedia.NoExoticSixSphere.FramedSlabDisconnectedBoundaryKernel

/-!
# The original endpoint inclusions and their integral homology sum

Use the retained boundary diffeomorphism. Its two restrictions are open
embeddings with disjoint images and the specified original endpoint
values. The actual integral disjoint-union homology equivalence shows
that the sum of these original inclusion maps is an isomorphism.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData

open CylinderFiberSlab

local notation "V" => EuclideanSpace ℝ (Fin 6)

variable {m n : ℕ} {z : Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) z s t}
  {hd : m = n + 6} {a : Sphere m} (A : d.FramedSlabData 6 hd a)

def nativeEndpointHomeomorph :
    ({x : Sphere m // d.leftMap x = z} ⊕ {x : Sphere m // d.rightMap x = z}) ≃ₜ
      A.nativeBoundary := by
  let := A.atlas
  let : ChartedSpace V
      {p : slab d.map z s t // ((𝓡∂ 1).prod (𝓡 6)).IsBoundaryPoint p} := A.boundaryAtlas
  let := regularFiberAtlas d.leftMap d.smooth_left z d.regular_left 6 (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right z d.regular_right 6 (by simpa using hd)
  exact A.boundaryDiffeomorph.toHomeomorph

def nativeBoundaryInl : C({x : Sphere m // d.leftMap x = z}, A.nativeBoundary) :=
  ⟨fun x ↦ A.nativeEndpointHomeomorph (Sum.inl x),
    A.nativeEndpointHomeomorph.continuous.comp continuous_inl⟩

def nativeBoundaryInr : C({x : Sphere m // d.rightMap x = z}, A.nativeBoundary) :=
  ⟨fun x ↦ A.nativeEndpointHomeomorph (Sum.inr x),
    A.nativeEndpointHomeomorph.continuous.comp continuous_inr⟩

theorem nativeBoundaryInl_value (x : {x : Sphere m // d.leftMap x = z}) :
    (A.nativeBoundaryInl x).val = (d.leftEndpoint x).val := A.boundary_left x

theorem nativeBoundaryInr_value (x : {x : Sphere m // d.rightMap x = z}) :
    (A.nativeBoundaryInr x).val = (d.rightEndpoint x).val := A.boundary_right x

theorem isOpenEmbedding_nativeBoundaryInl : Topology.IsOpenEmbedding A.nativeBoundaryInl :=
  A.nativeEndpointHomeomorph.isOpenEmbedding.comp Topology.IsOpenEmbedding.inl

theorem isOpenEmbedding_nativeBoundaryInr : Topology.IsOpenEmbedding A.nativeBoundaryInr :=
  A.nativeEndpointHomeomorph.isOpenEmbedding.comp Topology.IsOpenEmbedding.inr

theorem disjoint_nativeBoundaryInclusions :
    Disjoint (range A.nativeBoundaryInl) (range A.nativeBoundaryInr) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, h⟩
  exact Sum.inr_ne_inl (A.nativeEndpointHomeomorph.injective h)

theorem nativeBoundaryInclusions_cover (p : A.nativeBoundary) :
    p ∈ range A.nativeBoundaryInl ∨ p ∈ range A.nativeBoundaryInr := by
  obtain ⟨x, rfl⟩ := A.nativeEndpointHomeomorph.surjective p
  rcases x with x | x
  · exact Or.inl ⟨x, rfl⟩
  · exact Or.inr ⟨x, rfl⟩

def integralBoundarySumEquiv (k : ℕ) :
    (SingularHomology {x : Sphere m // d.leftMap x = z} k ×
      SingularHomology {x : Sphere m // d.rightMap x = z} k) ≃ₗ[ℤ]
      SingularHomology A.nativeBoundary k :=
  (sumHomologyEquiv _ _ k).symm.trans (homeomorphHomologyEquiv A.nativeEndpointHomeomorph k)

theorem integralBoundarySumEquiv_apply (k : ℕ)
    (u : SingularHomology {x : Sphere m // d.leftMap x = z} k ×
      SingularHomology {x : Sphere m // d.rightMap x = z} k) :
    A.integralBoundarySumEquiv k u = singularHomologyMap A.nativeBoundaryInl k u.1 +
      singularHomologyMap A.nativeBoundaryInr k u.2 := by
  let e : C({x : Sphere m // d.leftMap x = z} ⊕ {x : Sphere m // d.rightMap x = z},
      A.nativeBoundary) := ⟨A.nativeEndpointHomeomorph, A.nativeEndpointHomeomorph.continuous⟩
  change singularHomologyMap e k
    ((sumHomologyEquiv _ _ k).symm u) = _
  rw [sumHomologyEquiv_symm_apply, map_add, ← LinearMap.comp_apply,
    ← singularHomologyMap_comp, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

end NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData
