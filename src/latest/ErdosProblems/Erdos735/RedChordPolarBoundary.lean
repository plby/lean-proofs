/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos735.PolarBoundaryEndpointBridge
import ErdosProblems.Erdos735.RedChordConcreteEndpoints

/-!
# Red restriction endpoints on the concrete polar boundary

Weak endpoints which are actual blue arrangement vertices are exactly
represented by consecutive-owner projective vertices of the polar boundary.
-/

open Classical
open scoped LinearAlgebra.Projectivization Matrix
open Matrix

namespace Erdos735.RedChordPolarBoundary

noncomputable section

open ProjectiveArrangement SignVector
open SignVector.PolarFace SignVector.PolarPlaneChart
open SignVector.PolarBoundaryOrder
open SignVector.PolarBoundaryEndpointBridge
open SignVector.RedChordSector

abbrev Point := ProjectiveArrangement.Point

variable {B : Finset Point} [Nonempty {b // b ∈ B}]

private theorem normal_cross
    (i j : {b // b ∈ B}) (hij : i ≠ j) :
    normalVec i.1 ⨯₃ normalVec j.1 ≠ 0 := by
  apply normalVec_cross_ne_zero
  intro h
  exact hij (Subtype.ext h)

private theorem polar_zero_of_normal_zero
    {f : StrictFace (fun b : {b // b ∈ B} ↦ normalVec b.1)}
    {x y : Vec3}
    (hx : Realizes (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x)
    (i : {b // b ∈ B}) (hi : normalVec i.1 ⬝ᵥ y = 0) :
    polarPoint (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x i ⬝ᵥ y = 0 := by
  rw [polarPoint, smul_dotProduct, orientedNormal_dot]
  cases hsi : f.1 i <;> simp [signed, hsi, hi]

private theorem normal_zero_of_polar_zero
    {f : StrictFace (fun b : {b // b ∈ B} ↦ normalVec b.1)}
    {x y : Vec3}
    (hx : Realizes (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x)
    (i : {b // b ∈ B})
    (hi : polarPoint (fun b : {b // b ∈ B} ↦ normalVec b.1)
      f.1 x i ⬝ᵥ y = 0) :
    normalVec i.1 ⬝ᵥ y = 0 := by
  rw [polarPoint, smul_dotProduct, orientedNormal_dot] at hi
  have hsigned : signed (f.1 i) (normalVec i.1 ⬝ᵥ y) = 0 :=
    (mul_eq_zero.mp hi).resolve_left (inv_ne_zero (polarDenom_ne_zero hx i))
  cases hsi : f.1 i <;> simpa [signed, hsi] using hsigned

/-- The literal projective vertices between consecutive polar-boundary
owners. -/
def polarBoundaryVertices
    (f : StrictFace (fun b : {b // b ∈ B} ↦ normalVec b.1))
    {x : Vec3}
    (hx : Realizes (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x)
    (hspan : Submodule.span ℝ
      (Set.range (fun b : {b // b ∈ B} ↦ normalVec b.1)) = ⊤) :
    Finset (ℙ ℝ Vec3) :=
  Finset.univ.image (boundaryProjectiveVertex f hx normal_cross hspan)

/-- Polar-boundary vertices incident with a specified concrete affine dual
line. -/
def incidentPolarBoundaryVertices
    (f : StrictFace (fun b : {b // b ∈ B} ↦ normalVec b.1))
    {x : Vec3}
    (hx : Realizes (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x)
    (hspan : Submodule.span ℝ
      (Set.range (fun b : {b // b ∈ B} ↦ normalVec b.1)) = ⊤)
    (a : Point) : Finset (ℙ ℝ Vec3) :=
  (polarBoundaryVertices f hx hspan).filter fun v ↦ Incident v a

/-- A weak point of a blue chamber which is an actual projective arrangement
vertex equals one of the label-preserving consecutive-owner vertices of the
polar boundary. -/
theorem weak_projectiveVertex_eq_boundaryProjectiveVertex
    {f : StrictFace (fun b : {b // b ∈ B} ↦ normalVec b.1)}
    {x y : Vec3}
    (hx : Realizes (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x)
    (hspan : Submodule.span ℝ
      (Set.range (fun b : {b // b ∈ B} ↦ normalVec b.1)) = ⊤)
    (hy0 : y ≠ 0)
    (hy : WeaklyRealizes
      (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 y)
    (hvertex : Projectivization.mk ℝ y hy0 ∈ projectiveVertices B) :
    ∃ t : Fin (Erdos957.hullVertexCount
        (boundaryPolygon (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x)),
      Projectivization.mk ℝ y hy0 =
        boundaryProjectiveVertex f hx normal_cross hspan t := by
  unfold projectiveVertices at hvertex
  obtain ⟨pq, -, hpq⟩ := Finset.mem_image.mp hvertex
  let i : {b // b ∈ B} := pq.1.1
  let j : {b // b ∈ B} := pq.1.2
  have hij : i ≠ j := pq.2
  have hii : Incident (Projectivization.mk ℝ y hy0) i.1 := by
    rw [← hpq]
    exact indexedIntersection_incident_left B pq
  have hijinc : Incident (Projectivization.mk ℝ y hy0) j.1 := by
    rw [← hpq]
    exact indexedIntersection_incident_right B pq
  have hni : normalVec i.1 ⬝ᵥ y = 0 :=
    (onProjectiveLine_mk_iff _ _ hy0).mp hii
  have hnj : normalVec j.1 ⬝ᵥ y = 0 :=
    (onProjectiveLine_mk_iff _ _ hy0).mp hijinc
  obtain ⟨t, hleft, hright⟩ := exists_consecutive_zero_owners f hx
    normal_cross hspan hy0 hy hij
    (polar_zero_of_normal_zero hx i hni)
    (polar_zero_of_normal_zero hx j hnj)
  let a := boundaryOwner f hx normal_cross hspan t
  let b := boundaryOwner f hx normal_cross hspan (Erdos957.cyclicSucc t)
  have hab : a.1 ≠ b.1 := by
    intro h
    exact (boundaryOwner_ne_succ f hx normal_cross hspan t) (Subtype.ext h)
  refine ⟨t, ?_⟩
  apply eq_of_two_common_lines hab
  · apply (onProjectiveLine_mk_iff _ _ hy0).2
    exact normal_zero_of_polar_zero hx a hleft
  · apply (onProjectiveLine_mk_iff _ _ hy0).2
    exact normal_zero_of_polar_zero hx b hright
  · exact boundaryProjectiveVertex_on_left f hx normal_cross hspan t
  · exact boundaryProjectiveVertex_on_right f hx normal_cross hspan t

/-- The lifted polar supporting covector represents the same projective
corner as the cross product of the two consecutive concrete owner normals. -/
theorem cornerVector_projectivization_eq_boundaryProjectiveVertex
    {f : StrictFace (fun b : {b // b ∈ B} ↦ normalVec b.1)}
    {x : Vec3}
    (hx : Realizes (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x)
    (hspan : Submodule.span ℝ
      (Set.range (fun b : {b // b ∈ B} ↦ normalVec b.1)) = ⊤)
    (t : Fin (Erdos957.hullVertexCount
      (boundaryPolygon (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x))) :
    Projectivization.mk ℝ (cornerVector f hx normal_cross hspan t)
        (PolarBoundaryEndpointBridge.cornerVector_ne_zero f hx normal_cross hspan t) =
      boundaryProjectiveVertex f hx normal_cross hspan t := by
  let a := boundaryOwner f hx normal_cross hspan t
  let b := boundaryOwner f hx normal_cross hspan (Erdos957.cyclicSucc t)
  have hab : a.1 ≠ b.1 := by
    intro h
    exact (boundaryOwner_ne_succ f hx normal_cross hspan t) (Subtype.ext h)
  apply eq_of_two_common_lines hab
  · apply (onProjectiveLine_mk_iff _ _
      (PolarBoundaryEndpointBridge.cornerVector_ne_zero f hx normal_cross hspan t)).2
    exact cornerVector_on_left_owner f hx normal_cross hspan t
  · apply (onProjectiveLine_mk_iff _ _
      (PolarBoundaryEndpointBridge.cornerVector_ne_zero f hx normal_cross hspan t)).2
    exact cornerVector_on_right_owner f hx normal_cross hspan t
  · exact boundaryProjectiveVertex_on_left f hx normal_cross hspan t
  · exact boundaryProjectiveVertex_on_right f hx normal_cross hspan t

private theorem orientedSum_dot_pos_of_weak_of_span
    {f : StrictFace (fun b : {b // b ∈ B} ↦ normalVec b.1)}
    {x y : Vec3}
    (hx : Realizes (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x)
    (hspan : Submodule.span ℝ
      (Set.range (fun b : {b // b ∈ B} ↦ normalVec b.1)) = ⊤)
    (hy0 : y ≠ 0)
    (hy : WeaklyRealizes
      (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 y) :
    0 < orientedSum
      (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 ⬝ᵥ y := by
  let n := fun b : {b // b ∈ B} ↦ normalVec b.1
  have hex : ∃ i, 0 < signed (f.1 i) (n i ⬝ᵥ y) := by
    by_contra hnot
    push Not at hnot
    have hallSigned : ∀ i, signed (f.1 i) (n i ⬝ᵥ y) = 0 := by
      intro i
      exact le_antisymm (hnot i) (hy i)
    have hall : ∀ i, n i ⬝ᵥ y = 0 := by
      intro i
      have hi := hallSigned i
      cases hsi : f.1 i <;> simpa [signed, hsi] using hi
    let L : Vec3 →ₗ[ℝ] ℝ :=
      { toFun := fun z ↦ z ⬝ᵥ y
        map_add' := by intro u v; simp [add_dotProduct]
        map_smul' := by intro c z; simp [smul_dotProduct] }
    have hrange : Set.range n ⊆ L.ker := by
      rintro z ⟨i, rfl⟩
      exact hall i
    have hle : Submodule.span ℝ (Set.range n) ≤ L.ker :=
      (Submodule.span_le).2 hrange
    rw [hspan] at hle
    have hself : y ⬝ᵥ y = 0 := hle (by simp)
    exact hy0 (dotProduct_self_eq_zero.mp hself)
  rw [orientedSum, sum_dotProduct]
  apply Finset.sum_pos' (fun i _ ↦ by
    simpa [orientedNormal_dot] using hy i)
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, Finset.mem_univ i, by simpa [orientedNormal_dot] using hi⟩

/-- Conversely, any concrete polar-boundary corner on the red line is one
of the two explicit restriction-sector endpoints. -/
theorem boundaryProjectiveVertex_eq_endpoint_of_incident
    {a : Point}
    {f : StrictFace (fun b : {b // b ∈ B} ↦ normalVec b.1)}
    {x : Vec3}
    (hx : Realizes (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x)
    (D : EndpointData (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1
      (normalVec a) x hx)
    (hax : normalVec a ⬝ᵥ x = 0)
    (hspan : Submodule.span ℝ
      (Set.range (fun b : {b // b ∈ B} ↦ normalVec b.1)) = ⊤)
    (t : Fin (Erdos957.hullVertexCount
      (boundaryPolygon (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1 x)))
    (hinc : Incident (boundaryProjectiveVertex f hx normal_cross hspan t) a) :
    boundaryProjectiveVertex f hx normal_cross hspan t =
        lowerProjectiveEndpoint
          (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1
          (normalVec a) x D.lower_nonempty hx ∨
      boundaryProjectiveVertex f hx normal_cross hspan t =
        upperProjectiveEndpoint
          (fun b : {b // b ∈ B} ↦ normalVec b.1) f.1
          (normalVec a) x D.upper_nonempty hx := by
  let n := fun b : {b // b ∈ B} ↦ normalVec b.1
  let y := cornerVector f hx normal_cross hspan t
  have hy0 : y ≠ 0 :=
    PolarBoundaryEndpointBridge.cornerVector_ne_zero f hx normal_cross hspan t
  have hproj : Projectivization.mk ℝ y hy0 =
      boundaryProjectiveVertex f hx normal_cross hspan t :=
    cornerVector_projectivization_eq_boundaryProjectiveVertex hx hspan t
  have hry : normalVec a ⬝ᵥ y = 0 := by
    apply (onProjectiveLine_mk_iff _ _ hy0).mp
    rw [hproj]
    exact hinc
  have hyweak : WeaklyRealizes n f.1 y :=
    cornerVector_weaklyRealizes f hx normal_cross hspan t
  have hsumy : 0 < orientedSum n f.1 ⬝ᵥ y :=
    orientedSum_dot_pos_of_weak_of_span hx hspan hy0 hyweak
  have hsumx : 0 < orientedSum n f.1 ⬝ᵥ x := by
    rw [orientedSum, sum_dotProduct]
    exact Finset.sum_pos (fun i _ ↦ by
      simpa [n, orientedNormal_dot] using hx i) Finset.univ_nonempty
  let alpha : ℝ :=
    (orientedSum n f.1 ⬝ᵥ x) / (orientedSum n f.1 ⬝ᵥ y)
  have halpha : 0 < alpha := div_pos hsumx hsumy
  let z : Vec3 := alpha • y
  have hz0 : z ≠ 0 := smul_ne_zero halpha.ne' hy0
  have hzweak : WeaklyRealizes n f.1 z := by
    intro i
    dsimp only [z]
    simp only [dotProduct_smul, smul_eq_mul, signed_mul]
    exact mul_nonneg halpha.le (hyweak i)
  have hrz : normalVec a ⬝ᵥ z = 0 := by
    simp [z, dotProduct_smul, hry]
  have hsumz : orientedSum n f.1 ⬝ᵥ z =
      orientedSum n f.1 ⬝ᵥ x := by
    dsimp only [z, alpha]
    rw [dotProduct_smul, smul_eq_mul]
    field_simp [hsumy.ne']
  have hrdiff : normalVec a ⬝ᵥ (z - x) = 0 := by
    rw [dotProduct_sub, hrz, hax]
    ring
  have hsumdiff : orientedSum n f.1 ⬝ᵥ (z - x) = 0 := by
    rw [dotProduct_sub, hsumz]
    ring
  obtain ⟨r, hr⟩ := eq_smul_cross_of_dot_eq_zero
    D.direction_ne_zero hrdiff hsumdiff
  have hzchart : z = chartPoint n f.1 (normalVec a) x r := by
    calc
      z = (z - x) + x := by module
      _ = r • direction n f.1 (normalVec a) + x := by rw [hr]; rfl
      _ = chartPoint n f.1 (normalVec a) x r := by
        simp only [chartPoint]
        module
  have hznot : ¬ Realizes n f.1 z := by
    intro hzreal
    let i := boundaryOwner f hx normal_cross hspan t
    have hniy : n i ⬝ᵥ y = 0 :=
      cornerVector_on_left_owner f hx normal_cross hspan t
    have hniz : n i ⬝ᵥ z = 0 := by
      simp [z, dotProduct_smul, hniy]
    have hi := hzreal i
    rw [hniz] at hi
    cases hsi : f.1 i <;> simp [signed, hsi] at hi
  have hrboundary := (D.boundary_iff r).1 <| by
    rw [← hzchart]
    exact ⟨hzweak, hznot⟩
  have hmk : Projectivization.mk ℝ y hy0 =
      Projectivization.mk ℝ z hz0 := by
    symm
    apply (Projectivization.mk_eq_mk_iff' ℝ z y hz0 hy0).2
    exact ⟨alpha, rfl⟩
  rcases hrboundary with hrlo | hrup
  · left
    subst r
    calc
      boundaryProjectiveVertex f hx normal_cross hspan t =
          Projectivization.mk ℝ y hy0 := hproj.symm
      _ = Projectivization.mk ℝ z hz0 := hmk
      _ = lowerProjectiveEndpoint n f.1 (normalVec a) x D.lower_nonempty hx := by
        unfold lowerProjectiveEndpoint
        apply (Projectivization.mk_eq_mk_iff' ℝ _ _ hz0
          (chartPoint_ne_zero hx _)).2
        exact ⟨1, by simpa using hzchart.symm⟩
  · right
    subst r
    calc
      boundaryProjectiveVertex f hx normal_cross hspan t =
          Projectivization.mk ℝ y hy0 := hproj.symm
      _ = Projectivization.mk ℝ z hz0 := hmk
      _ = upperProjectiveEndpoint n f.1 (normalVec a) x D.upper_nonempty hx := by
        unfold upperProjectiveEndpoint
        apply (Projectivization.mk_eq_mk_iff' ℝ _ _ hz0
          (chartPoint_ne_zero hx _)).2
        exact ⟨1, by simpa using hzchart.symm⟩

/-- The lower explicit restriction-sector endpoint is one of the concrete
polar boundary vertices. -/
theorem lowerEndpoint_eq_boundaryProjectiveVertex
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
    ∃ t, lowerProjectiveEndpoint
        (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) f.1
        (normalVec a) x D.lower_nonempty hx =
      boundaryProjectiveVertex f hx normal_cross hspan t := by
  let y := chartPoint
    (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) f.1
    (normalVec a) x
    (lowerEndpoint
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) f.1
      (normalVec a) x D.lower_nonempty)
  have hy0 : y ≠ 0 := chartPoint_ne_zero hx _
  have hyweak : WeaklyRealizes
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) f.1 y :=
    (D.boundary_iff _).2 (Or.inl rfl) |>.1
  exact weak_projectiveVertex_eq_boundaryProjectiveVertex hx hspan hy0 hyweak
    (RedChordConcreteEndpoints.lowerEndpoint_mem_projectiveVertices
      hred ha D hax)

/-- The upper explicit restriction-sector endpoint is one of the concrete
polar boundary vertices. -/
theorem upperEndpoint_eq_boundaryProjectiveVertex
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
    ∃ t, upperProjectiveEndpoint
        (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) f.1
        (normalVec a) x D.upper_nonempty hx =
      boundaryProjectiveVertex f hx normal_cross hspan t := by
  let y := chartPoint
    (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) f.1
    (normalVec a) x
    (upperEndpoint
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) f.1
      (normalVec a) x D.upper_nonempty)
  have hy0 : y ≠ 0 := chartPoint_ne_zero hx _
  have hyweak : WeaklyRealizes
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) f.1 y :=
    (D.boundary_iff _).2 (Or.inr rfl) |>.1
  exact weak_projectiveVertex_eq_boundaryProjectiveVertex hx hspan hy0 hyweak
    (RedChordConcreteEndpoints.upperEndpoint_mem_projectiveVertices
      hred ha D hax)

/-- The two explicit endpoints form a two-element subset of the genuine
label-preserving polar boundary vertex set. -/
theorem projectiveEndpoints_card_and_subset_polarBoundary
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
    (projectiveEndpoints
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) f.1
      (normalVec a) x D.lower_nonempty D.upper_nonempty hx).card = 2 ∧
    projectiveEndpoints
      (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) f.1
      (normalVec a) x D.lower_nonempty D.upper_nonempty hx ⊆
        polarBoundaryVertices f hx hspan := by
  constructor
  · exact D.projective_card
  · intro v hv
    simp only [projectiveEndpoints, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · obtain ⟨t, ht⟩ := lowerEndpoint_eq_boundaryProjectiveVertex
        hred ha hx D hax hspan
      exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht.symm⟩
    · obtain ⟨t, ht⟩ := upperEndpoint_eq_boundaryProjectiveVertex
        hred ha hx D hax hspan
      exact Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht.symm⟩

/-- For a reduced magic configuration, the polar-boundary vertices on a
feasible red line are literally the two explicit sector endpoints. -/
theorem incidentPolarBoundaryVertices_eq_projectiveEndpoints
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
    incidentPolarBoundaryVertices f hx hspan a =
      projectiveEndpoints
        (fun b : {b // b ∈ nonordinaryPoints P} ↦ normalVec b.1) f.1
        (normalVec a) x D.lower_nonempty D.upper_nonempty hx := by
  ext v
  constructor
  · intro hv
    have hv' := Finset.mem_filter.mp hv
    obtain ⟨t, -, htv⟩ := Finset.mem_image.mp hv'.1
    have hincident : Incident
        (boundaryProjectiveVertex f hx normal_cross hspan t) a := by
      rw [htv]
      exact hv'.2
    have hends := boundaryProjectiveVertex_eq_endpoint_of_incident
      hx D hax hspan t hincident
    simp only [projectiveEndpoints, Finset.mem_insert, Finset.mem_singleton]
    rcases hends with h | h
    · exact Or.inl (htv.symm.trans h)
    · exact Or.inr (htv.symm.trans h)
  · intro hv
    simp only [projectiveEndpoints, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · obtain ⟨t, ht⟩ := lowerEndpoint_eq_boundaryProjectiveVertex
        hred ha hx D hax hspan
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht.symm⟩, ?_⟩
      apply (onProjectiveLine_mk_iff _ _ (chartPoint_ne_zero hx _)).2
      exact D.lower_on_red hax
    · obtain ⟨t, ht⟩ := upperEndpoint_eq_boundaryProjectiveVertex
        hred ha hx D hax hspan
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨t, Finset.mem_univ _, ht.symm⟩, ?_⟩
      apply (onProjectiveLine_mk_iff _ _ (chartPoint_ne_zero hx _)).2
      exact D.upper_on_red hax

/-- Exact cardinality form of the concrete red-chord endpoint theorem on
the genuine polar boundary. -/
theorem incidentPolarBoundaryVertices_card
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
    (incidentPolarBoundaryVertices f hx hspan a).card = 2 := by
  rw [incidentPolarBoundaryVertices_eq_projectiveEndpoints hred ha hx D hax hspan]
  exact D.projective_card

end

end Erdos735.RedChordPolarBoundary
