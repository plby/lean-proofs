/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos735.PolarBoundaryAcross
import ErdosProblems.Erdos735.PolarBoundaryEndpointBridge

open Classical
noncomputable section
open scoped Matrix LinearAlgebra.Projectivization
open Matrix

namespace Erdos735.SignVector.PolarBoundaryAcrossEndpoints

open PolarFace PolarPlaneChart PolarBoundaryOrder
open PolarBoundaryEndpointBridge RedChordSector
open PolarBoundaryAcross

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
variable (n : I → Vec3) (hn : ∀ i, n i ≠ 0)
variable (hcross : ∀ i j, i ≠ j → n i ⨯₃ n j ≠ 0)
variable (hspan : Submodule.span ℝ (Set.range n) = ⊤)

/-- A nonzero weak face point on two distinct arrangement lines is one of
the face's literal consecutive-owner projective corners. -/
theorem weak_mk_eq_boundaryProjectiveVertex
    (f : StrictFace n) {x y : Vec3} (hx : Realizes n f.1 x)
    (hy0 : y ≠ 0) (hy : WeaklyRealizes n f.1 y)
    {i j : I} (hij : i ≠ j) (hiy : n i ⬝ᵥ y = 0)
    (hjy : n j ⬝ᵥ y = 0) :
    ∃ t : Fin (Erdos957.hullVertexCount (boundaryPolygon n f.1 x)),
      Projectivization.mk ℝ y hy0 =
        boundaryProjectiveVertex f hx hcross hspan t := by
  obtain ⟨t, hleft, hright⟩ := exists_consecutive_zero_owners f hx
    hcross hspan hy0 hy hij
    (by
      rw [polarPoint, smul_dotProduct, orientedNormal_dot]
      cases f.1 i <;> simp [signed, hiy])
    (by
      rw [polarPoint, smul_dotProduct, orientedNormal_dot]
      cases f.1 j <;> simp [signed, hjy])
  let a := boundaryOwner f hx hcross hspan t
  let b := boundaryOwner f hx hcross hspan (Erdos957.cyclicSucc t)
  have hab : a ≠ b := boundaryOwner_ne_succ f hx hcross hspan t
  have hay : n a ⬝ᵥ y = 0 := by
    rw [polarPoint, smul_dotProduct, orientedNormal_dot] at hleft
    have hsigned : signed (f.1 a) (n a ⬝ᵥ y) = 0 :=
      (mul_eq_zero.mp hleft).resolve_left (inv_ne_zero (polarDenom_ne_zero hx a))
    cases hsa : f.1 a <;> simpa [signed, hsa] using hsigned
  have hby : n b ⬝ᵥ y = 0 := by
    rw [polarPoint, smul_dotProduct, orientedNormal_dot] at hright
    have hsigned : signed (f.1 b) (n b ⬝ᵥ y) = 0 :=
      (mul_eq_zero.mp hright).resolve_left (inv_ne_zero (polarDenom_ne_zero hx b))
    cases hsb : f.1 b <;> simpa [signed, hsb] using hsigned
  obtain ⟨c, hc⟩ := eq_smul_cross_of_dot_eq_zero (hcross a b hab) hay hby
  refine ⟨t, ?_⟩
  rw [boundaryProjectiveVertex]
  exact (Projectivization.mk_eq_mk_iff' ℝ y (n a ⨯₃ n b) hy0
    (hcross a b hab)).2 ⟨c, hc.symm⟩

omit [Nonempty I] in
/-- Weak realization is unchanged when one flips a face sign on a normal
which vanishes at the weak point. -/
theorem weaklyRealizes_oppositeFace_of_zero
    (f : StrictFace n) (e : StrictEdge n) (he : e ∈ faceEdges n f)
    {y : Vec3} (hy : WeaklyRealizes n f.1 y)
    (hzero : n e.1.1 ⬝ᵥ y = 0) :
    WeaklyRealizes n (oppositeFace n hn f e).1 y := by
  intro k
  by_cases hk : k = e.1.1
  · subst k
    rw [hzero]
    cases (oppositeFace n hn f e).1 e.1.1 <;> simp [signed]
  · have hinc : f.1 k = e.1.2 ⟨k, hk⟩ :=
      (mem_faceEdges_iff n f e).mp he ⟨k, hk⟩
    have hsign : (oppositeFace n hn f e).1 k = f.1 k := by
      rw [oppositeFace, edgeFace_sign, extendEdgeSign_other e.1 _ hk, hinc]
    rw [hsign]
    exact hy k

theorem boundaryVertex_succ_eq_boundaryProjectiveVertex
    (f : StrictFace n) (t : BoundaryIndex n f) :
    boundaryVertex n hcross hspan f (Erdos957.cyclicSucc t) =
      boundaryProjectiveVertex f (faceWitness_realizes n f) hcross hspan t := by
  change boundaryProjectiveVertex f (faceWitness_realizes n f) hcross hspan
      ((finRotate _).symm (Erdos957.cyclicSucc t)) = _
  rw [(finRotate _).symm_apply_apply]

private theorem owner_index_injective (f : StrictFace n) :
    Function.Injective
      (boundaryOwner f (faceWitness_realizes n f) hcross hspan) := by
  intro i j hij
  apply (boundaryOwnerEquiv f (faceWitness_realizes n f) hcross hspan).injective
  exact Subtype.ext hij

/-- A polar corner of `d.1` which is incident with `d`'s edge is one of the
two literal endpoints of the same edge on the opposite face. -/
theorem corner_is_across_endpoint
    (d : IndexedDart n)
    (t : BoundaryIndex n d.1)
    (ht : (boundaryEdge n hcross hspan d.1 d.2).1.1 =
          boundaryOwner d.1 (faceWitness_realizes n d.1) hcross hspan t ∨
        (boundaryEdge n hcross hspan d.1 d.2).1.1 =
          boundaryOwner d.1 (faceWitness_realizes n d.1) hcross hspan
            (Erdos957.cyclicSucc t)) :
    boundaryProjectiveVertex d.1 (faceWitness_realizes n d.1) hcross hspan t =
        boundaryVertex n hcross hspan
          (across n hn hcross hspan d).1 (across n hn hcross hspan d).2 ∨
      boundaryProjectiveVertex d.1 (faceWitness_realizes n d.1) hcross hspan t =
        boundaryVertex n hcross hspan
          (across n hn hcross hspan d).1
          (Erdos957.cyclicSucc (across n hn hcross hspan d).2) := by
  let f := d.1
  let e := boundaryEdge n hcross hspan d.1 d.2
  let g := (across n hn hcross hspan d).1
  let j := (across n hn hcross hspan d).2
  let y := cornerVector f (faceWitness_realizes n f) hcross hspan t
  have hy0 : y ≠ 0 := PolarBoundaryOrder.cornerVector_ne_zero f
    (faceWitness_realizes n f) hcross hspan t
  have hyl : n (boundaryOwner f (faceWitness_realizes n f) hcross hspan t)
      ⬝ᵥ y = 0 := cornerVector_on_left_owner f
        (faceWitness_realizes n f) hcross hspan t
  have hyr : n (boundaryOwner f (faceWitness_realizes n f) hcross hspan
      (Erdos957.cyclicSucc t)) ⬝ᵥ y = 0 :=
    cornerVector_on_right_owner f (faceWitness_realizes n f) hcross hspan t
  have hezero : n e.1.1 ⬝ᵥ y = 0 := by
    rcases ht with ht | ht
    · rw [ht]
      exact hyl
    · rw [ht]
      exact hyr
  have hyf : WeaklyRealizes n f.1 y :=
    cornerVector_weaklyRealizes f (faceWitness_realizes n f) hcross hspan t
  have heface : e ∈ faceEdges n f := boundaryEdge_mem n hcross hspan d.1 d.2
  have hyg : WeaklyRealizes n g.1 y := by
    have hop := weaklyRealizes_oppositeFace_of_zero n hn f e heface hyf hezero
    have hgeq : g = oppositeFace n hn f e := by
      exact across_face_eq_edgeFace_flip n hn hcross hspan d
    rw [hgeq]
    exact hop
  have hlr : boundaryOwner f (faceWitness_realizes n f) hcross hspan t ≠
      boundaryOwner f (faceWitness_realizes n f) hcross hspan
        (Erdos957.cyclicSucc t) :=
    boundaryOwner_ne_succ f (faceWitness_realizes n f) hcross hspan t
  obtain ⟨u, hu⟩ := weak_mk_eq_boundaryProjectiveVertex n hcross hspan g
    (faceWitness_realizes n g) hy0 hyg hlr hyl hyr
  have hfg : boundaryProjectiveVertex f (faceWitness_realizes n f) hcross hspan t =
      boundaryProjectiveVertex g (faceWitness_realizes n g) hcross hspan u := by
    rw [← cornerProjectiveVertex_eq_boundaryProjectiveVertex f
      (faceWitness_realizes n f) hcross hspan t, cornerProjectiveVertex]
    exact hu
  have hezero_g : n e.1.1 ⬝ᵥ
      cornerVector g (faceWitness_realizes n g) hcross hspan u = 0 := by
    have hincY : ProjectiveArrangement.OnProjectiveLine (n e.1.1)
        (Projectivization.mk ℝ y hy0) :=
      (ProjectiveArrangement.onProjectiveLine_mk_iff _ _ hy0).2 hezero
    have hincG : ProjectiveArrangement.OnProjectiveLine (n e.1.1)
        (boundaryProjectiveVertex g (faceWitness_realizes n g) hcross hspan u) := by
      rwa [hu] at hincY
    rw [← cornerProjectiveVertex_eq_boundaryProjectiveVertex g
      (faceWitness_realizes n g) hcross hspan u, cornerProjectiveVertex,
      ProjectiveArrangement.onProjectiveLine_mk_iff] at hincG
    exact hincG
  have heowner : e.1.1 ∈ edgeOwners n g.1 := by
    have he_g : e ∈ faceEdges n g := by
      have hm := boundaryEdge_mem n hcross hspan g j
      have hsame : e = boundaryEdge n hcross hspan g j :=
        across_sameEdge n hn hcross hspan d
      rwa [← hsame] at hm
    exact (ownerFaceEdgeEquiv g).symm ⟨e, he_g⟩ |>.2
  have hendpoint := owner_eq_endpoint_of_dot_cornerVector_eq_zero g
    (faceWitness_realizes n g) hcross hspan u e.1.1 heowner hezero_g
  have hej : e.1.1 =
      boundaryOwner g (faceWitness_realizes n g) hcross hspan j := by
    have hs := congrArg (fun z : StrictEdge n ↦ z.1.1)
      (across_sameEdge n hn hcross hspan d)
    exact hs
  rcases hendpoint with heu | heu
  · have hju : j = u := owner_index_injective n hcross hspan g (hej.symm.trans heu)
    right
    change boundaryProjectiveVertex f (faceWitness_realizes n f) hcross hspan t =
      boundaryVertex n hcross hspan g (Erdos957.cyclicSucc j)
    rw [hju, boundaryVertex_succ_eq_boundaryProjectiveVertex]
    exact hfg
  · have hju : j = Erdos957.cyclicSucc u :=
      owner_index_injective n hcross hspan g (hej.symm.trans heu)
    left
    change boundaryProjectiveVertex f (faceWitness_realizes n f) hcross hspan t =
      boundaryVertex n hcross hspan g j
    rw [hju, boundaryVertex_succ_eq_boundaryProjectiveVertex]
    exact hfg

theorem boundaryVertex_start_is_across_endpoint (d : IndexedDart n) :
    boundaryVertex n hcross hspan d.1 d.2 =
        boundaryVertex n hcross hspan
          (across n hn hcross hspan d).1 (across n hn hcross hspan d).2 ∨
      boundaryVertex n hcross hspan d.1 d.2 =
        boundaryVertex n hcross hspan
          (across n hn hcross hspan d).1
          (Erdos957.cyclicSucc (across n hn hcross hspan d).2) := by
  let t : BoundaryIndex n d.1 := (finRotate _).symm d.2
  have hs : Erdos957.cyclicSucc t = d.2 := (finRotate _).apply_symm_apply d.2
  have ht : (boundaryEdge n hcross hspan d.1 d.2).1.1 =
      boundaryOwner d.1 (faceWitness_realizes n d.1) hcross hspan
        (Erdos957.cyclicSucc t) := by
    rw [hs]
    rfl
  have h := corner_is_across_endpoint n hn hcross hspan d t (Or.inr ht)
  exact h

theorem boundaryVertex_finish_is_across_endpoint (d : IndexedDart n) :
    boundaryVertex n hcross hspan d.1 (Erdos957.cyclicSucc d.2) =
        boundaryVertex n hcross hspan
          (across n hn hcross hspan d).1 (across n hn hcross hspan d).2 ∨
      boundaryVertex n hcross hspan d.1 (Erdos957.cyclicSucc d.2) =
        boundaryVertex n hcross hspan
          (across n hn hcross hspan d).1
          (Erdos957.cyclicSucc (across n hn hcross hspan d).2) := by
  have ht : (boundaryEdge n hcross hspan d.1 d.2).1.1 =
      boundaryOwner d.1 (faceWitness_realizes n d.1) hcross hspan d.2 := rfl
  have h := corner_is_across_endpoint n hn hcross hspan d d.2 (Or.inl ht)
  simpa only [boundaryVertex_succ_eq_boundaryProjectiveVertex] using h

def projectiveEdgeVertices (f : StrictFace n) (i : BoundaryIndex n f) :
    Finset (ℙ ℝ Vec3) :=
  {boundaryVertex n hcross hspan f i,
    boundaryVertex n hcross hspan f (Erdos957.cyclicSucc i)}

theorem projectiveEdgeVertices_across (d : IndexedDart n) :
    projectiveEdgeVertices n hcross hspan d.1 d.2 =
      projectiveEdgeVertices n hcross hspan
        (across n hn hcross hspan d).1 (across n hn hcross hspan d).2 := by
  apply Finset.Subset.antisymm
  · intro v hv
    simp only [projectiveEdgeVertices, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
    rcases hv with rfl | rfl
    · exact boundaryVertex_start_is_across_endpoint n hn hcross hspan d
    · exact boundaryVertex_finish_is_across_endpoint n hn hcross hspan d
  · intro v hv
    have hinv := across_involutive n hn hcross hspan d
    have hsub := boundaryVertex_start_is_across_endpoint n hn hcross hspan
      (across n hn hcross hspan d)
    have hfin := boundaryVertex_finish_is_across_endpoint n hn hcross hspan
      (across n hn hcross hspan d)
    simp only [projectiveEdgeVertices, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
    rw [hinv] at hsub hfin
    rcases hv with rfl | rfl
    · exact hsub
    · exact hfin

end Erdos735.SignVector.PolarBoundaryAcrossEndpoints
