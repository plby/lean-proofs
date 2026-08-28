import Wikipedia.HopfProblem.OrbitPairClosedPushoutGluing

/-!
# The literal product-boundary union is the required pushout

The closed-cover criterion identifies the union with the actual pushout
of the two product faces over their intersection. The face embeddings
and intersection witnesses use the original maps, not replacement
subspaces or a presumed preservation of quotient maps by products.
-/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Set Topology

namespace Wikipedia.HopfProblem.OrbitPair.NeighborhoodProduct

variable {A X : TopCat.{u}} {B Y : TopCat.{v}} (i : A ⟶ X) (j : B ⟶ Y)

def cornerLeft : TopCat.of (A × B) ⟶ TopCat.of (A × Y) :=
  TopCat.ofHom ((ContinuousMap.id A).prodMap j.hom)

def cornerRight : TopCat.of (A × B) ⟶ TopCat.of (X × B) :=
  TopCat.ofHom (i.hom.prodMap (ContinuousMap.id B))

def leftFace : TopCat.of (A × Y) ⟶ TopCat.of ↥(boundary i j) :=
  TopCat.ofHom
    ⟨fun p ↦ ⟨(i p.1, p.2), Or.inl ⟨p.1, rfl⟩⟩,
      ((i.hom.continuous.comp continuous_fst).prodMk continuous_snd).subtype_mk _⟩

def rightFace : TopCat.of (X × B) ⟶ TopCat.of ↥(boundary i j) :=
  TopCat.ofHom
    ⟨fun p ↦ ⟨(p.1, j p.2), Or.inr ⟨p.2, rfl⟩⟩,
      (continuous_fst.prodMk (j.hom.continuous.comp continuous_snd)).subtype_mk _⟩

theorem face_square : cornerLeft (A := A) j ≫ leftFace i j =
    cornerRight (B := B) i ≫ rightFace i j := rfl

theorem range_leftFace : Set.range (leftFace i j) =
    {q : ↥(boundary i j) | q.val.1 ∈ Set.range i} := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, rfl⟩
  · rintro ⟨a, ha⟩
    refine ⟨(a, q.val.2), ?_⟩
    apply Subtype.ext
    exact Prod.ext ha rfl

theorem range_rightFace : Set.range (rightFace i j) =
    {q : ↥(boundary i j) | q.val.2 ∈ Set.range j} := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.2, rfl⟩
  · rintro ⟨b, hb⟩
    refine ⟨(q.val.1, b), ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl hb

theorem leftFace_isClosedEmbedding (hi : IsClosedEmbedding i) :
    IsClosedEmbedding (leftFace i j) := by
  have he : IsEmbedding (fun p : A × Y ↦ (i p.1, p.2)) := hi.isEmbedding.prodMap .id
  refine ⟨he.codRestrict (boundary i j) (fun p ↦ Or.inl ⟨p.1, rfl⟩), ?_⟩
  rw [range_leftFace]
  exact hi.isClosed_range.preimage (continuous_fst.comp continuous_subtype_val)

theorem rightFace_isClosedEmbedding (hj : IsClosedEmbedding j) :
    IsClosedEmbedding (rightFace i j) := by
  have he : IsEmbedding (fun p : X × B ↦ (p.1, j p.2)) := IsEmbedding.id.prodMap hj.isEmbedding
  refine ⟨he.codRestrict (boundary i j) (fun p ↦ Or.inr ⟨p.2, rfl⟩), ?_⟩
  rw [range_rightFace]
  exact hj.isClosed_range.preimage (continuous_snd.comp continuous_subtype_val)

theorem face_cover (q : ↥(boundary i j)) :
    q ∈ Set.range (leftFace i j) ∨ q ∈ Set.range (rightFace i j) := by
  rw [range_leftFace, range_rightFace]
  exact q.property

theorem face_intersection (p : A × Y) (q : X × B) (h : leftFace i j p = rightFace i j q) :
    ∃ s : A × B, cornerLeft (A := A) j s = p ∧ cornerRight (B := B) i s = q := by
  have hv : (i p.1, p.2) = (q.1, j q.2) := congrArg Subtype.val h
  refine ⟨(p.1, q.2), ?_, ?_⟩
  · change (p.1, j q.2) = p
    exact Prod.ext rfl (congrArg (fun r : X × Y ↦ r.2) hv).symm
  · change (i p.1, q.2) = q
    exact Prod.ext (congrArg (fun r : X × Y ↦ r.1) hv) rfl

theorem isPushout (hi : IsClosedEmbedding i) (hj : IsClosedEmbedding j) :
    IsPushout (cornerLeft (A := A) j) (cornerRight (B := B) i) (leftFace i j) (rightFace i j) :=
  ClosedPushout.isPushout (leftFace_isClosedEmbedding i j hi)
    (rightFace_isClosedEmbedding i j hj) (face_cover i j) (face_intersection i j) (face_square i j)

theorem inclusion_isClosedEmbedding (hi : IsClosedEmbedding i) (hj : IsClosedEmbedding j) :
    IsClosedEmbedding (inclusion i j) := by
  refine ⟨IsEmbedding.subtypeVal, ?_⟩
  rw [range_inclusion]
  exact (hi.isClosed_range.preimage continuous_fst).union
    (hj.isClosed_range.preimage continuous_snd)

end Wikipedia.HopfProblem.OrbitPair.NeighborhoodProduct
