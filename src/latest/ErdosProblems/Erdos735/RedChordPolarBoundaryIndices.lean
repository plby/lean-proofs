/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos735.RedChordPolarBoundary
import ErdosProblems.Erdos735.PolarBoundaryAcross

/-!
# Cyclic indices of a concrete polar red chord

The concrete projective endpoints supplied by `RedChordPolarBoundary` are
enumerated injectively by the cyclic corner indices of the polar boundary.
Consequently a reduced ordinary red line cuts that boundary at exactly two
cyclic indices, not merely at two unlabelled projective points.
-/

open Classical
open scoped LinearAlgebra.Projectivization Matrix
open Matrix

namespace Erdos735.RedChordPolarBoundaryIndices

noncomputable section

open ProjectiveArrangement SignVector
open SignVector.PolarFace SignVector.PolarPlaneChart
open SignVector.PolarBoundaryOrder
open SignVector.PolarBoundaryAcross
open SignVector.RedChordSector
open RedChordPolarBoundary

abbrev Point := ProjectiveArrangement.Point

variable {B : Finset Point} [Nonempty {b // b ∈ B}]

omit [Nonempty {b // b ∈ B}] in
private theorem normal_cross
    (i j : {b // b ∈ B}) (hij : i ≠ j) :
    normalVec i.1 ⨯₃ normalVec j.1 ≠ 0 := by
  apply normalVec_cross_ne_zero
  intro h
  exact hij (Subtype.ext h)

private theorem boundaryProjectiveVertex_mem_projectiveVertices
    {f : StrictFace (fun b : {b // b ∈ B} ↦ normalVec b.1)}
    {x : Vec3}
    (hx : Realizes (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x)
    (hspan : Submodule.span ℝ
      (Set.range (fun b : {b // b ∈ B} ↦ normalVec b.1)) = ⊤)
    (t : Fin (Erdos957.hullVertexCount
      (boundaryPolygon (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x))) :
    boundaryProjectiveVertex f hx normal_cross hspan t ∈
      projectiveVertices B := by
  let i : {b // b ∈ B} := boundaryOwner f hx normal_cross hspan t
  let j : {b // b ∈ B} := boundaryOwner f hx normal_cross hspan
    (Erdos957.cyclicSucc t)
  have hij : i ≠ j := boundaryOwner_ne_succ f hx normal_cross hspan t
  let pq : DistinctPointPair B := ⟨(i, j), hij⟩
  have hv : boundaryProjectiveVertex f hx normal_cross hspan t =
      indexedIntersection B pq := by
    rfl
  rw [hv]
  exact indexedIntersection_mem_projectiveVertices B pq

/-- The finite set of projective corners of a strict polar face does not
depend on the chosen interior point used to normalize the polar slice. -/
theorem polarBoundaryVertices_witness_independent
    (f : StrictFace (fun b : {b // b ∈ B} ↦ normalVec b.1))
    {x y : Vec3}
    (hx : Realizes (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x)
    (hy : Realizes (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 y)
    (hspan : Submodule.span ℝ
      (Set.range (fun b : {b // b ∈ B} ↦ normalVec b.1)) = ⊤) :
    polarBoundaryVertices f hx hspan =
      polarBoundaryVertices f hy hspan := by
  apply Finset.Subset.antisymm
  · intro v hv
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hv
    let z := cornerVector f hx normal_cross hspan t
    have hz0 : z ≠ 0 := cornerVector_ne_zero f hx normal_cross hspan t
    have hzweak : WeaklyRealizes
        (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 z :=
      cornerVector_weaklyRealizes f hx normal_cross hspan t
    have hcorner : Projectivization.mk ℝ z hz0 =
        boundaryProjectiveVertex f hx normal_cross hspan t :=
      cornerVector_projectivization_eq_boundaryProjectiveVertex hx hspan t
    have hzmem : Projectivization.mk ℝ z hz0 ∈ projectiveVertices B := by
      rw [hcorner]
      exact boundaryProjectiveVertex_mem_projectiveVertices hx hspan t
    obtain ⟨u, hu⟩ := weak_projectiveVertex_eq_boundaryProjectiveVertex
      hy hspan hz0 hzweak hzmem
    apply Finset.mem_image.mpr
    exact ⟨u, Finset.mem_univ _, hu.symm.trans hcorner⟩
  · intro v hv
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hv
    let z := cornerVector f hy normal_cross hspan t
    have hz0 : z ≠ 0 := cornerVector_ne_zero f hy normal_cross hspan t
    have hzweak : WeaklyRealizes
        (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 z :=
      cornerVector_weaklyRealizes f hy normal_cross hspan t
    have hcorner : Projectivization.mk ℝ z hz0 =
        boundaryProjectiveVertex f hy normal_cross hspan t :=
      cornerVector_projectivization_eq_boundaryProjectiveVertex hy hspan t
    have hzmem : Projectivization.mk ℝ z hz0 ∈ projectiveVertices B := by
      rw [hcorner]
      exact boundaryProjectiveVertex_mem_projectiveVertices hy hspan t
    obtain ⟨u, hu⟩ := weak_projectiveVertex_eq_boundaryProjectiveVertex
      hx hspan hz0 hzweak hzmem
    apply Finset.mem_image.mpr
    exact ⟨u, Finset.mem_univ _, hu.symm.trans hcorner⟩

/-- Filtering the polar corners by incidence is likewise independent of the
normalizing interior point. -/
theorem incidentPolarBoundaryVertices_witness_independent
    (f : StrictFace (fun b : {b // b ∈ B} ↦ normalVec b.1))
    {x y : Vec3}
    (hx : Realizes (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x)
    (hy : Realizes (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 y)
    (hspan : Submodule.span ℝ
      (Set.range (fun b : {b // b ∈ B} ↦ normalVec b.1)) = ⊤)
    (a : Point) :
    incidentPolarBoundaryVertices f hx hspan a =
      incidentPolarBoundaryVertices f hy hspan a := by
  unfold incidentPolarBoundaryVertices
  rw [polarBoundaryVertices_witness_independent f hx hy hspan]

/-- Endpoint indices in the fixed polar boundary used by
`PolarBoundaryAcross`.  Unlike `polarRedEndpointIndices`, this definition
uses `faceWitness`, so its index type is definitionally `BoundaryIndex`. -/
def faceRedEndpointIndices
    (f : StrictFace (fun b : {b // b ∈ B} ↦ normalVec b.1))
    (hspan : Submodule.span ℝ
      (Set.range (fun b : {b // b ∈ B} ↦ normalVec b.1)) = ⊤)
    (a : Point) :
    Finset (BoundaryIndex (fun b : {b // b ∈ B} ↦ normalVec b.1) f) :=
  Finset.univ.filter fun t ↦ Incident
    (boundaryVertex (fun b : {b // b ∈ B} ↦ normalVec b.1)
      normal_cross hspan f t) a

/-- The fixed-boundary indices enumerate exactly the incident projective
polar corners. -/
theorem image_faceRedEndpointIndices
    (f : StrictFace (fun b : {b // b ∈ B} ↦ normalVec b.1))
    (hspan : Submodule.span ℝ
      (Set.range (fun b : {b // b ∈ B} ↦ normalVec b.1)) = ⊤)
    (a : Point) :
    (faceRedEndpointIndices f hspan a).image
        (boundaryVertex (fun b : {b // b ∈ B} ↦ normalVec b.1)
          normal_cross hspan f) =
      incidentPolarBoundaryVertices f
        (faceWitness_realizes
          (fun b : {b // b ∈ B} ↦ normalVec b.1) f) hspan a := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi, hiv⟩ := Finset.mem_image.mp hv
    have hinc := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_image.mpr
      exact ⟨(finRotate _).symm i, Finset.mem_univ _, hiv⟩
    · rw [← hiv]
      exact hinc
  · intro hv
    have hvf := Finset.mem_filter.mp hv
    obtain ⟨t, -, htv⟩ := Finset.mem_image.mp hvf.1
    apply Finset.mem_image.mpr
    refine ⟨finRotate _ t, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change Incident
        (boundaryProjectiveVertex f
          (faceWitness_realizes
            (fun b : {b // b ∈ B} ↦ normalVec b.1) f)
          normal_cross hspan ((finRotate _).symm (finRotate _ t))) a
      rw [Equiv.symm_apply_apply, htv]
      exact hvf.2
    · change boundaryProjectiveVertex f
        (faceWitness_realizes
          (fun b : {b // b ∈ B} ↦ normalVec b.1) f)
        normal_cross hspan ((finRotate _).symm (finRotate _ t)) = v
      rw [Equiv.symm_apply_apply]
      exact htv

/-- The concrete projective vertex enumeration of the fixed polar boundary
is injective. -/
theorem faceBoundaryVertex_injective
    (f : StrictFace (fun b : {b // b ∈ B} ↦ normalVec b.1))
    (hspan : Submodule.span ℝ
      (Set.range (fun b : {b // b ∈ B} ↦ normalVec b.1)) = ⊤) :
    Function.Injective
      (boundaryVertex (fun b : {b // b ∈ B} ↦ normalVec b.1)
        normal_cross hspan f) := by
  intro i j hij
  apply (finRotate _).symm.injective
  apply boundaryProjectiveVertex_injective f
    (faceWitness_realizes
      (fun b : {b // b ∈ B} ↦ normalVec b.1) f) normal_cross hspan
  exact hij

/-- Usable fixed-boundary form: a feasible ordinary red line in a reduced
magic configuration has exactly two endpoint indices in the genuine polar
boundary cycle based at `faceWitness`. -/
theorem faceRedEndpointIndices_card_of_restricted
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    [Nonempty {b // b ∈ nonordinaryPoints P}]
    (hred : IsReducedMagic P w c)
    {a : Point} (ha : a ∈ ordinaryPoints P)
    (f : StrictFace
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1))
    (hspan : Submodule.span ℝ
      (Set.range (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1)) = ⊤)
    (hrest : RestrictedRealizable
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1)
      (normalVec a) f.1) :
    (faceRedEndpointIndices f hspan a).card = 2 := by
  obtain ⟨x, hx, hax⟩ := hrest
  let D : EndpointData
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) f.1
      (normalVec a) x hx :=
    endpointDataOfRestricted (normalVec_ne_zero a) hx hax hspan
  let vertex := boundaryVertex
    (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1)
    normal_cross hspan f
  have hinj : Function.Injective vertex :=
    faceBoundaryVertex_injective f hspan
  calc
    (faceRedEndpointIndices f hspan a).card =
        ((faceRedEndpointIndices f hspan a).image vertex).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ = (incidentPolarBoundaryVertices f
        (faceWitness_realizes
          (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) f)
        hspan a).card := by
      rw [image_faceRedEndpointIndices]
    _ = (incidentPolarBoundaryVertices f hx hspan a).card := by
      rw [incidentPolarBoundaryVertices_witness_independent f
        (faceWitness_realizes
          (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) f)
        hx hspan a]
    _ = 2 := incidentPolarBoundaryVertices_card hred ha hx D hax hspan

/-- Transport the exact-two result through any boundary-index equivalence
whose vertex map agrees with the concrete polar projective vertices.  This
is the adapter used when a rotation realization has its own face-index
type. -/
theorem compatibleEndpointIndices_card_of_restricted
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    [Nonempty {b // b ∈ nonordinaryPoints P}]
    (hred : IsReducedMagic P w c)
    {a : Point} (ha : a ∈ ordinaryPoints P)
    (f : StrictFace
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1))
    (hspan : Submodule.span ℝ
      (Set.range (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1)) = ⊤)
    (hrest : RestrictedRealizable
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1)
      (normalVec a) f.1)
    (e : J ≃ BoundaryIndex
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) f)
    (vertex : J → ℙ ℝ Vec3)
    (hvertex : ∀ j, vertex j =
      boundaryVertex
        (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1)
        normal_cross hspan f (e j)) :
    (Finset.univ.filter fun j ↦ Incident (vertex j) a).card = 2 := by
  calc
    (Finset.univ.filter fun j ↦ Incident (vertex j) a).card =
        (faceRedEndpointIndices f hspan a).card := by
      apply Finset.card_bij (fun j _ ↦ e j)
      · intro j hj
        have hjinc : Incident (vertex j) a := by
          simpa using (Finset.mem_filter.mp hj).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← hvertex j]
        exact hjinc
      · intro i hi j hj hij
        exact e.injective hij
      · intro i hi
        refine ⟨e.symm i, ?_, e.apply_symm_apply i⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have hiinc : Incident
            (boundaryVertex
              (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1)
              normal_cross hspan f i) a :=
          (Finset.mem_filter.mp hi).2
        rw [hvertex, e.apply_symm_apply]
        exact hiinc
    _ = 2 := faceRedEndpointIndices_card_of_restricted
      hred ha f hspan hrest

/-- Cyclic polar-boundary indices whose projective corner lies on the
specified concrete affine-dual line. -/
def polarRedEndpointIndices
    (f : StrictFace (fun b : {b // b ∈ B} ↦ normalVec b.1))
    {x : Vec3}
    (hx : Realizes (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x)
    (hspan : Submodule.span ℝ
      (Set.range (fun b : {b // b ∈ B} ↦ normalVec b.1)) = ⊤)
    (a : Point) :
    Finset (Fin (Erdos957.hullVertexCount
      (boundaryPolygon (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x))) :=
  Finset.univ.filter fun t ↦
    Incident (boundaryProjectiveVertex f hx normal_cross hspan t) a

/-- Mapping the incident cyclic indices to their concrete projective corners
gives exactly the finite set of incident polar-boundary vertices. -/
theorem image_polarRedEndpointIndices
    (f : StrictFace (fun b : {b // b ∈ B} ↦ normalVec b.1))
    {x : Vec3}
    (hx : Realizes (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x)
    (hspan : Submodule.span ℝ
      (Set.range (fun b : {b // b ∈ B} ↦ normalVec b.1)) = ⊤)
    (a : Point) :
    (polarRedEndpointIndices f hx hspan a).image
        (boundaryProjectiveVertex f hx normal_cross hspan) =
      incidentPolarBoundaryVertices f hx hspan a := by
  ext v
  simp only [polarRedEndpointIndices, incidentPolarBoundaryVertices,
    polarBoundaryVertices, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, rfl⟩, ht⟩
  · rintro ⟨⟨t, rfl⟩, ht⟩
    exact ⟨t, ht, rfl⟩

/-- For a reduced magic configuration, every ordinary line meeting a strict
blue face has exactly two cyclic polar-boundary endpoint indices. -/
theorem polarRedEndpointIndices_card
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    [Nonempty {b // b ∈ nonordinaryPoints P}]
    (hred : IsReducedMagic P w c)
    {a : Point} (ha : a ∈ ordinaryPoints P)
    {f : StrictFace
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1)}
    {x : Vec3}
    (hx : Realizes
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) f.1 x)
    (D : EndpointData
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) f.1
      (normalVec a) x hx)
    (hax : normalVec a ⬝ᵥ x = 0)
    (hspan : Submodule.span ℝ
      (Set.range (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1)) = ⊤) :
    (polarRedEndpointIndices f hx hspan a).card = 2 := by
  let vertex := boundaryProjectiveVertex f hx normal_cross hspan
  have hinj : Function.Injective vertex :=
    boundaryProjectiveVertex_injective f hx normal_cross hspan
  calc
    (polarRedEndpointIndices f hx hspan a).card =
        ((polarRedEndpointIndices f hx hspan a).image vertex).card :=
      (Finset.card_image_of_injective _ hinj).symm
    _ = (incidentPolarBoundaryVertices f hx hspan a).card := by
      rw [image_polarRedEndpointIndices]
    _ = 2 := incidentPolarBoundaryVertices_card hred ha hx D hax hspan

end

end Erdos735.RedChordPolarBoundaryIndices
