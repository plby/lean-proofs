import ErdosProblems.Erdos735.LeviConvexCore
import ErdosProblems.Erdos735.SignVectorIncidence
import ErdosProblems.Erdos735.PolarFace

/-!
# Levi interfaces for sign-vector arrangements

This file connects the finite sign-vector faces and edges to the line/face
interface used by Levi's triangle theorem.
-/

namespace Erdos735
namespace SignVectorArrangement

open SignVector
open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The combinatorial degree of a strict sign-vector face. -/
noncomputable def strictFaceDegree (n : I → Vec3) (f : StrictFace n) : ℕ :=
  (faceEdges n f).card

/-- The owner of an arrangement edge is its unique zero sign coordinate. -/
def strictEdgeOwner {n : I → Vec3} (e : StrictEdge n) : I :=
  e.1.1

/-- A strict face is incident with line `i` when one of its boundary edges
has zero coordinate `i`. -/
noncomputable def LineFaceIncident (n : I → Vec3)
    (i : I) (f : StrictFace n) : Prop :=
  ∃ e ∈ faceEdges n f, strictEdgeOwner e = i

noncomputable instance lineFaceIncidentDecidable (n : I → Vec3) :
    DecidableRel (LineFaceIncident n) :=
  fun _ _ ↦ Classical.dec _

/-- On a fixed face there is at most one open edge with a given owner: all
the remaining signs are forced by the face. -/
lemma strictEdge_eq_of_faceEdges_of_owner_eq {n : I → Vec3}
    {f : StrictFace n} {e e' : StrictEdge n}
    (he : e ∈ faceEdges n f) (he' : e' ∈ faceEdges n f)
    (howner : strictEdgeOwner e = strictEdgeOwner e') : e = e' := by
  rcases e with ⟨⟨i, s⟩, hs⟩
  rcases e' with ⟨⟨j, t⟩, ht⟩
  change i = j at howner
  subst j
  apply Subtype.ext
  change (⟨i, s⟩ : EdgeCode I) = ⟨i, t⟩
  congr 1
  funext k
  have his := (mem_faceEdges_iff n f ⟨⟨i, s⟩, hs⟩).mp he k
  have hit := (mem_faceEdges_iff n f ⟨⟨i, t⟩, ht⟩).mp he' k
  exact his.symm.trans hit

lemma strictEdgeOwner_injOn_faceEdges (n : I → Vec3) (f : StrictFace n) :
    Set.InjOn strictEdgeOwner (faceEdges n f : Set (StrictEdge n)) := by
  intro e he e' he' h
  exact strictEdge_eq_of_faceEdges_of_owner_eq he he' h

/-- The finite set of line labels that own a boundary edge of `f`. -/
noncomputable def faceEdgeOwners (n : I → Vec3) (f : StrictFace n) : Finset I :=
  (faceEdges n f).image strictEdgeOwner

lemma card_faceEdgeOwners (n : I → Vec3) (f : StrictFace n) :
    (faceEdgeOwners n f).card = strictFaceDegree n f := by
  exact Finset.card_image_of_injOn (strictEdgeOwner_injOn_faceEdges n f)

lemma mem_faceEdgeOwners_iff (n : I → Vec3) (f : StrictFace n) (i : I) :
    i ∈ faceEdgeOwners n f ↔ LineFaceIncident n i f := by
  simp [faceEdgeOwners, LineFaceIncident, strictEdgeOwner]

/-- The owner set of a strict face is exactly the set of indices whose
canonical restriction of the face sign vector is feasible.  This form does
not use a chosen witness or a general-position hypothesis. -/
lemma mem_faceEdgeOwners_iff_edgeFeasible_faceEdgeCode
    (n : I → Vec3) (f : StrictFace n) (i : I) :
    i ∈ faceEdgeOwners n f ↔
      EdgeFeasible n (SignVector.PolarFace.faceEdgeCode f.1 i) := by
  rw [mem_faceEdgeOwners_iff]
  constructor
  · rintro ⟨e, he, howner⟩
    rcases e with ⟨⟨j, t⟩, ht⟩
    change j = i at howner
    subst j
    have hsign := (mem_faceEdges_iff n f
      (⟨⟨i, t⟩, ht⟩ : StrictEdge n)).mp he
    have hcode : SignVector.PolarFace.faceEdgeCode f.1 i =
        (⟨i, t⟩ : EdgeCode I) := by
      change (⟨i, fun k ↦ f.1 k.1⟩ : EdgeCode I) = ⟨i, t⟩
      congr 1
      funext k
      exact hsign k
    simpa [hcode] using ht
  · intro hi
    let e : StrictEdge n :=
      ⟨SignVector.PolarFace.faceEdgeCode f.1 i, hi⟩
    refine ⟨e, ?_, rfl⟩
    rw [mem_faceEdges_iff]
    intro j
    rfl

/-- With pairwise projectively distinct normals, the boundary-line owners
of a face are precisely the extreme indices of its normalized polar hull.
This is the exact extraction criterion needed when a geometric construction
produces a triangular polar hull. -/
theorem faceEdgeOwners_eq_extremeIndices
    {n : I → Vec3} (f : StrictFace n) {x : Vec3}
    (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0) :
    faceEdgeOwners n f = SignVector.PolarFace.extremeIndices n f.1 x := by
  ext i
  rw [mem_faceEdgeOwners_iff_edgeFeasible_faceEdgeCode,
    SignVector.PolarFace.edgeFeasible_faceEdgeCode_iff_extreme hx hcross,
    SignVector.PolarFace.mem_extremeIndices,
    SignVector.PolarFace.mem_polarVertices]

/-- A face whose normalized polar hull has exactly three extreme indices is
a triangular strict face, with exactly those three line owners. -/
theorem strictFaceDegree_eq_three_of_extremeIndices_eq
    {n : I → Vec3} (f : StrictFace n) {x : Vec3}
    (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hextreme : SignVector.PolarFace.extremeIndices n f.1 x = {i, j, k}) :
    strictFaceDegree n f = 3 := by
  rw [← card_faceEdgeOwners,
    faceEdgeOwners_eq_extremeIndices f hx hcross, hextreme]
  simp [hij, hik, hjk]

/-- A concrete three-vertex description of the normalized polar hull gives
the exact three boundary owners.  Pairwise projective independence is what
lets one recover an owner label from equality of polar points. -/
theorem faceEdgeOwners_eq_of_polarVertices_eq_three
    {n : I → Vec3} (f : StrictFace n) {x : Vec3}
    (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    {i j k : I}
    (hvertices : SignVector.PolarFace.polarVertices n f.1 x =
      {SignVector.PolarFace.polarPoint n f.1 x i,
        SignVector.PolarFace.polarPoint n f.1 x j,
        SignVector.PolarFace.polarPoint n f.1 x k}) :
    faceEdgeOwners n f = {i, j, k} := by
  rw [faceEdgeOwners_eq_extremeIndices f hx hcross]
  ext a
  rw [SignVector.PolarFace.mem_extremeIndices, hvertices]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (hai | haj | hak)
    · exact Or.inl ((SignVector.PolarFace.polarPoint_injective hx hcross) hai)
    · exact Or.inr (Or.inl
        ((SignVector.PolarFace.polarPoint_injective hx hcross) haj))
    · exact Or.inr (Or.inr
        ((SignVector.PolarFace.polarPoint_injective hx hcross) hak))
  · rintro (rfl | rfl | rfl) <;> simp

/-- If every normalized polar point lies in the triangle generated by three
feasible boundary owners, then those three points are all and only the polar
vertices.  This packages the convex-cone calculation needed for an exterior
wedge without asking that calculation to reason about `extremePoints`. -/
theorem polarVertices_eq_three_of_subset_convexHull
    {n : I → Vec3} (f : StrictFace n) {x : Vec3}
    (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    {i j k : I}
    (hcontain : ∀ a : I,
      SignVector.PolarFace.polarPoint n f.1 x a ∈
        convexHull ℝ
          ({SignVector.PolarFace.polarPoint n f.1 x i,
            SignVector.PolarFace.polarPoint n f.1 x j,
            SignVector.PolarFace.polarPoint n f.1 x k} : Set Vec3))
    (hi : EdgeFeasible n (SignVector.PolarFace.faceEdgeCode f.1 i))
    (hj : EdgeFeasible n (SignVector.PolarFace.faceEdgeCode f.1 j))
    (hk : EdgeFeasible n (SignVector.PolarFace.faceEdgeCode f.1 k)) :
    SignVector.PolarFace.polarVertices n f.1 x =
      {SignVector.PolarFace.polarPoint n f.1 x i,
        SignVector.PolarFace.polarPoint n f.1 x j,
        SignVector.PolarFace.polarPoint n f.1 x k} := by
  let P := SignVector.PolarFace.polarPoints n f.1 x
  let T : Set Vec3 :=
    {SignVector.PolarFace.polarPoint n f.1 x i,
      SignVector.PolarFace.polarPoint n f.1 x j,
      SignVector.PolarFace.polarPoint n f.1 x k}
  have hPT : convexHull ℝ (P : Set Vec3) = convexHull ℝ T := by
    apply Set.Subset.antisymm
    · apply convexHull_min
      · intro p hp
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hp
        exact hcontain a
      · exact convex_convexHull ℝ T
    · apply convexHull_mono
      intro p hp
      change p = SignVector.PolarFace.polarPoint n f.1 x i ∨
        p = SignVector.PolarFace.polarPoint n f.1 x j ∨
        p = SignVector.PolarFace.polarPoint n f.1 x k at hp
      rcases hp with rfl | rfl | rfl <;>
        exact SignVector.PolarFace.polarPoint_mem_polarPoints n f.1 x _
  have hiext : SignVector.PolarFace.polarPoint n f.1 x i ∈
      (convexHull ℝ (P : Set Vec3)).extremePoints ℝ :=
    (SignVector.PolarFace.edgeFeasible_faceEdgeCode_iff_extreme
      hx hcross i).mp hi
  have hjext : SignVector.PolarFace.polarPoint n f.1 x j ∈
      (convexHull ℝ (P : Set Vec3)).extremePoints ℝ :=
    (SignVector.PolarFace.edgeFeasible_faceEdgeCode_iff_extreme
      hx hcross j).mp hj
  have hkext : SignVector.PolarFace.polarPoint n f.1 x k ∈
      (convexHull ℝ (P : Set Vec3)).extremePoints ℝ :=
    (SignVector.PolarFace.edgeFeasible_faceEdgeCode_iff_extreme
      hx hcross k).mp hk
  ext p
  rw [SignVector.PolarFace.mem_polarVertices]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hp
    have hpT : p ∈ T := by
      have hp' : p ∈ (convexHull ℝ T).extremePoints ℝ := by
        rwa [← hPT]
      exact extremePoints_convexHull_subset hp'
    exact hpT
  · rintro (rfl | rfl | rfl)
    · exact hiext
    · exact hjext
    · exact hkext

/-- Exterior-wedge output in its most convenient algebraic form: triangle
containment of all polar generators together with feasibility of the three
walls directly yields selected-line incidence and degree three. -/
theorem incident_and_degree_eq_three_of_polarTriangle
    {n : I → Vec3} (f : StrictFace n) {x : Vec3}
    (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hcontain : ∀ a : I,
      SignVector.PolarFace.polarPoint n f.1 x a ∈
        convexHull ℝ
          ({SignVector.PolarFace.polarPoint n f.1 x i,
            SignVector.PolarFace.polarPoint n f.1 x j,
            SignVector.PolarFace.polarPoint n f.1 x k} : Set Vec3))
    (hi : EdgeFeasible n (SignVector.PolarFace.faceEdgeCode f.1 i))
    (hj : EdgeFeasible n (SignVector.PolarFace.faceEdgeCode f.1 j))
    (hk : EdgeFeasible n (SignVector.PolarFace.faceEdgeCode f.1 k)) :
    LineFaceIncident n i f ∧ strictFaceDegree n f = 3 := by
  have hvertices := polarVertices_eq_three_of_subset_convexHull
    f hx hcross hcontain hi hj hk
  have howners := faceEdgeOwners_eq_of_polarVertices_eq_three
    f hx hcross hvertices
  constructor
  · rw [← mem_faceEdgeOwners_iff, howners]
    simp
  · rw [← card_faceEdgeOwners, howners]
    simp [hij, hik, hjk]

/-- Exact three polar vertices certify both incidence with each of their
owners and degree three.  This is the final algebraic extraction expected
from an exterior-wedge construction. -/
theorem incident_and_degree_eq_three_of_polarVertices_eq_three
    {n : I → Vec3} (f : StrictFace n) {x : Vec3}
    (hx : Realizes n f.1 x)
    (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
    {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hvertices : SignVector.PolarFace.polarVertices n f.1 x =
      {SignVector.PolarFace.polarPoint n f.1 x i,
        SignVector.PolarFace.polarPoint n f.1 x j,
        SignVector.PolarFace.polarPoint n f.1 x k}) :
    LineFaceIncident n i f ∧ strictFaceDegree n f = 3 := by
  have howners := faceEdgeOwners_eq_of_polarVertices_eq_three
    f hx hcross hvertices
  constructor
  · rw [← mem_faceEdgeOwners_iff]
    rw [howners]
    simp
  · rw [← card_faceEdgeOwners, howners]
    simp [hij, hik, hjk]

/-- A three-generator positive cone certificate gives the exact three edge
owners of a face.  This is the non-normalized counterpart of the polar
triangle criterion: it is often substantially easier for an affine exterior
wedge to express every oriented arrangement normal as a nonnegative linear
combination of its three wall normals than to manipulate convex hulls. -/
theorem faceEdgeOwners_eq_three_of_orientedCone
    {n : I → Vec3} (f : StrictFace n) (hn : ∀ a, n a ≠ 0)
    {i j k : I}
    (hi : EdgeFeasible n (SignVector.PolarFace.faceEdgeCode f.1 i))
    (hj : EdgeFeasible n (SignVector.PolarFace.faceEdgeCode f.1 j))
    (hk : EdgeFeasible n (SignVector.PolarFace.faceEdgeCode f.1 k))
    (hcone : ∀ a : I, ∃ α β γ : ℝ,
      0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧
      SignVector.PolarFace.orientedNormal n f.1 a =
        α • SignVector.PolarFace.orientedNormal n f.1 i +
        β • SignVector.PolarFace.orientedNormal n f.1 j +
        γ • SignVector.PolarFace.orientedNormal n f.1 k) :
    faceEdgeOwners n f = {i, j, k} := by
  classical
  ext a
  rw [mem_faceEdgeOwners_iff_edgeFeasible_faceEdgeCode]
  constructor
  · intro ha
    by_contra haijk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at haijk
    rcases haijk with ⟨hai, haj, hak⟩
    obtain ⟨y, hy, hay⟩ := ha
    obtain ⟨α, β, γ, hα, hβ, hγ, hrepr⟩ := hcone a
    have hiy : 0 <
        SignVector.PolarFace.orientedNormal n f.1 i ⬝ᵥ y := by
      rw [SignVector.PolarFace.orientedNormal_dot]
      simpa [SignVector.otherNormals,
        SignVector.PolarFace.faceEdgeCode] using hy ⟨i, Ne.symm hai⟩
    have hjy : 0 <
        SignVector.PolarFace.orientedNormal n f.1 j ⬝ᵥ y := by
      rw [SignVector.PolarFace.orientedNormal_dot]
      simpa [SignVector.otherNormals,
        SignVector.PolarFace.faceEdgeCode] using hy ⟨j, Ne.symm haj⟩
    have hky : 0 <
        SignVector.PolarFace.orientedNormal n f.1 k ⬝ᵥ y := by
      rw [SignVector.PolarFace.orientedNormal_dot]
      simpa [SignVector.otherNormals,
        SignVector.PolarFace.faceEdgeCode] using hy ⟨k, Ne.symm hak⟩
    have hay₀ : n a ⬝ᵥ y = 0 := by
      simpa [SignVector.PolarFace.faceEdgeCode] using hay
    have hay' :
        SignVector.PolarFace.orientedNormal n f.1 a ⬝ᵥ y = 0 := by
      rw [SignVector.PolarFace.orientedNormal_dot,
        SignVector.PolarFace.signed_eq_signScalar_mul, hay₀, mul_zero]
    have hsum := congrArg (fun z : Vec3 ↦ z ⬝ᵥ y) hrepr
    rw [hay'] at hsum
    have hsum' : 0 =
        α * (SignVector.PolarFace.orientedNormal n f.1 i ⬝ᵥ y) +
        β * (SignVector.PolarFace.orientedNormal n f.1 j ⬝ᵥ y) +
        γ * (SignVector.PolarFace.orientedNormal n f.1 k ⬝ᵥ y) := by
      simpa only [add_dotProduct, smul_dotProduct, smul_eq_mul] using hsum
    have hαzero : α = 0 := by nlinarith
    have hβzero : β = 0 := by nlinarith
    have hγzero : γ = 0 := by nlinarith
    have horientedzero :
        SignVector.PolarFace.orientedNormal n f.1 a = 0 := by
      simpa [hαzero, hβzero, hγzero] using hrepr
    apply hn a
    rw [← SignVector.PolarFace.signScalar_smul_orientedNormal n f.1 a,
      horientedzero, smul_zero]
  · intro ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hi
    · exact hj
    · exact hk

/-- The positive-cone certificate also gives selected-line incidence and
degree three directly. -/
theorem incident_and_degree_eq_three_of_orientedCone
    {n : I → Vec3} (f : StrictFace n) (hn : ∀ a, n a ≠ 0)
    {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : EdgeFeasible n (SignVector.PolarFace.faceEdgeCode f.1 i))
    (hj : EdgeFeasible n (SignVector.PolarFace.faceEdgeCode f.1 j))
    (hk : EdgeFeasible n (SignVector.PolarFace.faceEdgeCode f.1 k))
    (hcone : ∀ a : I, ∃ α β γ : ℝ,
      0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧
      SignVector.PolarFace.orientedNormal n f.1 a =
        α • SignVector.PolarFace.orientedNormal n f.1 i +
        β • SignVector.PolarFace.orientedNormal n f.1 j +
        γ • SignVector.PolarFace.orientedNormal n f.1 k) :
    LineFaceIncident n i f ∧ strictFaceDegree n f = 3 := by
  have howners := faceEdgeOwners_eq_three_of_orientedCone
    f hn hi hj hk hcone
  constructor
  · rw [← mem_faceEdgeOwners_iff, howners]
    simp
  · rw [← card_faceEdgeOwners, howners]
    simp [hij, hik, hjk]

/-- Antipodal strict spherical face. -/
noncomputable def antipodalStrictFace {n : I → Vec3}
    (f : StrictFace n) : StrictFace n :=
  ⟨antipodalSign f.1, (realizable_antipodalSign_iff n f.1).2 f.2⟩

@[simp] theorem antipodalStrictFace_sign {n : I → Vec3}
    (f : StrictFace n) :
    (antipodalStrictFace f).1 = antipodalSign f.1 := rfl

theorem antipodalStrictFace_ne [Nonempty I] {n : I → Vec3}
    (f : StrictFace n) : antipodalStrictFace f ≠ f := by
  intro h
  have hs := congrArg (fun g : StrictFace n ↦ g.1) h
  exact antipodalSign_ne f.1 hs

@[simp] theorem antipodalStrictFace_involutive_base {n : I → Vec3}
    (f : StrictFace n) :
    antipodalStrictFace (antipodalStrictFace f) = f := by
  apply Subtype.ext
  simp [antipodalStrictFace, antipodalSign_antipodalSign]

/-- Equality in the projective face quotient, written without introducing a
quotient type. -/
def SameAntipodalFaceOrbit {n : I → Vec3}
    (f g : StrictFace n) : Prop :=
  f = g ∨ antipodalStrictFace f = g

theorem SameAntipodalFaceOrbit.refl {n : I → Vec3} (f : StrictFace n) :
    SameAntipodalFaceOrbit f f := Or.inl rfl

theorem SameAntipodalFaceOrbit.symm {n : I → Vec3} {f g : StrictFace n}
    (h : SameAntipodalFaceOrbit f g) : SameAntipodalFaceOrbit g f := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · right
    rw [← h, antipodalStrictFace_involutive_base]

theorem SameAntipodalFaceOrbit.trans {n : I → Vec3} {f g q : StrictFace n}
    (hfg : SameAntipodalFaceOrbit f g)
    (hgq : SameAntipodalFaceOrbit g q) : SameAntipodalFaceOrbit f q := by
  rcases hfg with rfl | hfg
  · exact hgq
  · rcases hgq with rfl | hgq
    · exact Or.inr hfg
    · left
      rw [← hgq, ← hfg, antipodalStrictFace_involutive_base]

/-- Restricting an antipodal chamber to a wall is feasible exactly when the
original restriction is. -/
theorem edgeFeasible_faceEdgeCode_antipodal_iff
    {n : I → Vec3} (f : StrictFace n) (i : I) :
    EdgeFeasible n
        (SignVector.PolarFace.faceEdgeCode (antipodalStrictFace f).1 i) ↔
      EdgeFeasible n (SignVector.PolarFace.faceEdgeCode f.1 i) := by
  constructor
  · rintro ⟨x, hx, hzero⟩
    refine ⟨-x, ?_, ?_⟩
    · intro j
      have hj := hx j
      cases hsign : f.1 j.1 <;>
        simp [SignVector.otherNormals, SignVector.PolarFace.faceEdgeCode,
          antipodalStrictFace, antipodalSign, dotProduct_neg,
          SignVector.signed, hsign] at hj ⊢
      all_goals linarith
    · simpa [SignVector.PolarFace.faceEdgeCode, dotProduct_neg] using hzero
  · rintro ⟨x, hx, hzero⟩
    refine ⟨-x, ?_, ?_⟩
    · intro j
      have hj := hx j
      cases hsign : f.1 j.1 <;>
        simp [SignVector.otherNormals, SignVector.PolarFace.faceEdgeCode,
          antipodalStrictFace, antipodalSign, dotProduct_neg,
          SignVector.signed, hsign] at hj ⊢
      all_goals linarith
    · simpa [SignVector.PolarFace.faceEdgeCode, dotProduct_neg] using hzero

/-- Antipodal spherical chambers have the same arrangement-line owners. -/
theorem faceEdgeOwners_antipodalStrictFace {n : I → Vec3}
    (f : StrictFace n) :
    faceEdgeOwners n (antipodalStrictFace f) = faceEdgeOwners n f := by
  ext i
  rw [mem_faceEdgeOwners_iff_edgeFeasible_faceEdgeCode,
    mem_faceEdgeOwners_iff_edgeFeasible_faceEdgeCode,
    edgeFeasible_faceEdgeCode_antipodal_iff]

/-- Antipodal spherical chambers have the same incidence lines. -/
theorem lineFaceIncident_antipodalStrictFace_iff {n : I → Vec3}
    (i : I) (f : StrictFace n) :
    LineFaceIncident n i (antipodalStrictFace f) ↔
      LineFaceIncident n i f := by
  rw [← mem_faceEdgeOwners_iff, ← mem_faceEdgeOwners_iff,
    faceEdgeOwners_antipodalStrictFace]

/-- Antipodal spherical chambers have the same combinatorial degree. -/
theorem strictFaceDegree_antipodalStrictFace {n : I → Vec3}
    (f : StrictFace n) :
    strictFaceDegree n (antipodalStrictFace f) = strictFaceDegree n f := by
  rw [← card_faceEdgeOwners, faceEdgeOwners_antipodalStrictFace,
    card_faceEdgeOwners]

/-- Exact three-owner extraction is enough to certify that a sign-vector
face is triangular. -/
lemma strictFaceDegree_eq_three_of_faceEdgeOwners_eq
    {n : I → Vec3} {f : StrictFace n} {i j k : I}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (howners : faceEdgeOwners n f = {i, j, k}) :
    strictFaceDegree n f = 3 := by
  rw [← card_faceEdgeOwners, howners]
  simp [hij, hik, hjk]

/-- Levi's theorem in the exact finite sign-vector form consumed by the
discharging argument. -/
def HasSignVectorLeviProperty (n : I → Vec3) : Prop :=
  HasLeviTriangleProperty I (StrictFace n) (strictFaceDegree n)
    (LineFaceIncident n)

theorem HasSignVectorLeviProperty.three_le_incident_triangles
    {n : I → Vec3} (H : HasSignVectorLeviProperty n) (i : I) :
    3 ≤ (Finset.univ.filter fun f : StrictFace n =>
      LineFaceIncident n i f ∧ strictFaceDegree n f = 3).card :=
  H i

/-- Three explicitly constructed, pairwise distinct triangular faces give
the local Levi bound for one selected line. -/
theorem three_le_incident_triangles_of_injective
    {n : I → Vec3} (i : I) (face : Fin 3 → StrictFace n)
    (hface : Function.Injective face)
    (hincident : ∀ t, LineFaceIncident n i (face t))
    (hdegree : ∀ t, strictFaceDegree n (face t) = 3) :
    3 ≤ (Finset.univ.filter fun f : StrictFace n =>
      LineFaceIncident n i f ∧ strictFaceDegree n f = 3).card := by
  let T : Finset (StrictFace n) := Finset.univ.image face
  have hTcard : T.card = 3 := by
    rw [Finset.card_image_of_injective _ hface]
    simp
  have hsubset : T ⊆ Finset.univ.filter fun f : StrictFace n =>
      LineFaceIncident n i f ∧ strictFaceDegree n f = 3 := by
    intro f hf
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hf
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hincident t, hdegree t⟩
  calc
    3 = T.card := hTcard.symm
    _ ≤ _ := Finset.card_le_card hsubset

/-- A uniform explicit choice of three triangular faces per owner assembles
to the Stage-4-facing sign-vector Levi property. -/
theorem hasSignVectorLeviProperty_of_three_faces
    {n : I → Vec3} (face : I → Fin 3 → StrictFace n)
    (hface : ∀ i, Function.Injective (face i))
    (hincident : ∀ i t, LineFaceIncident n i (face i t))
    (hdegree : ∀ i t, strictFaceDegree n (face i t) = 3) :
    HasSignVectorLeviProperty n := by
  intro i
  exact three_le_incident_triangles_of_injective
    i (face i) (hface i) (hincident i) (hdegree i)

/-- Finite bridge used in the last ABKPR step.  An alleged evil--evil path
selects a line and injects all triangles incident with that line into the two
endpoint triangles; Levi's lower bound makes this impossible. -/
structure EvilPathLineCertificate (n : I → Vec3) where
  selectedLine : I
  endpointTriangle : Fin 2 → StrictFace n
  endpoint_injective : Function.Injective endpointTriangle
  allIncidentTrianglesAreEndpoints :
    ∀ f : StrictFace n,
      LineFaceIncident n selectedLine f → strictFaceDegree n f = 3 →
        ∃ k, endpointTriangle k = f

theorem no_evil_path_of_levi_certificate
    {n : I → Vec3} (H : HasSignVectorLeviProperty n)
    (C : EvilPathLineCertificate n) : False := by
  let T : Finset (StrictFace n) := Finset.univ.filter fun f =>
    LineFaceIncident n C.selectedLine f ∧ strictFaceDegree n f = 3
  have hthree : 3 ≤ T.card := H C.selectedLine
  have hsubset : T ⊆ Finset.univ.image C.endpointTriangle := by
    intro f hf
    have hparts := (Finset.mem_filter.mp hf).2
    obtain ⟨k, hk⟩ := C.allIncidentTrianglesAreEndpoints f hparts.1 hparts.2
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_image_of_injective _ C.endpoint_injective] at hcard
  simp at hcard
  omega

/-- The antipodally correct spherical form of Levi's projective theorem.
Three projective triangle orbits give at least six strict spherical faces. -/
def HasProjectiveSignVectorLeviProperty (n : I → Vec3) : Prop :=
  ∀ i : I, 6 ≤ (Finset.univ.filter fun f : StrictFace n ↦
    LineFaceIncident n i f ∧ strictFaceDegree n f = 3).card

/-- Correct spherical encoding of a projective two-endpoint certificate.
Every incident strict triangle is one of two representatives or the
antipode of one of those representatives. -/
structure ProjectiveEvilPathLineCertificate (n : I → Vec3) where
  selectedLine : I
  endpointTriangle : Fin 2 → StrictFace n
  allIncidentTrianglesAreEndpointOrAntipode :
    ∀ f : StrictFace n,
      LineFaceIncident n selectedLine f → strictFaceDegree n f = 3 →
        ∃ k, endpointTriangle k = f ∨
          antipodalStrictFace (endpointTriangle k) = f

/-- Six spherical triangles (three projective antipodal orbits) cannot be
covered by the two endpoint representatives and their antipodes. -/
theorem no_evil_path_of_projective_levi_certificate
    {n : I → Vec3} (H : HasProjectiveSignVectorLeviProperty n)
    (C : ProjectiveEvilPathLineCertificate n) : False := by
  let T : Finset (StrictFace n) := Finset.univ.filter fun f ↦
    LineFaceIncident n C.selectedLine f ∧ strictFaceDegree n f = 3
  let endpointOrAntipode : Fin 2 × Bool → StrictFace n := fun kb ↦
    if kb.2 then antipodalStrictFace (C.endpointTriangle kb.1)
    else C.endpointTriangle kb.1
  have hsix : 6 ≤ T.card := H C.selectedLine
  have hsubset : T ⊆ Finset.univ.image endpointOrAntipode := by
    intro f hf
    have hparts := (Finset.mem_filter.mp hf).2
    obtain ⟨k, hk | hk⟩ :=
      C.allIncidentTrianglesAreEndpointOrAntipode f hparts.1 hparts.2
    · exact Finset.mem_image.mpr ⟨(k, false), Finset.mem_univ _, by
        simpa [endpointOrAntipode] using hk⟩
    · exact Finset.mem_image.mpr ⟨(k, true), Finset.mem_univ _, by
        simpa [endpointOrAntipode] using hk⟩
  have hcard := Finset.card_le_card hsubset
  have himage : (Finset.univ.image endpointOrAntipode).card ≤ 4 := by
    calc
      (Finset.univ.image endpointOrAntipode).card ≤
          (Finset.univ : Finset (Fin 2 × Bool)).card :=
        Finset.card_image_le
      _ = 4 := by simp
  omega

end SignVectorArrangement
end Erdos735
