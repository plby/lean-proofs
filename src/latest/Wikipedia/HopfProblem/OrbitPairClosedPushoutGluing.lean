import Wikipedia.HopfProblem.OrbitPairNeighborhoodProductData

/-!
# Gluing across a closed cover with a specified intersection

The two pieces are embedded as closed subspaces. Every overlap is
represented by the specified common domain. Compatible maps therefore
paste continuously, using the inverses of the embeddings on their actual
ranges. This gives a pushout criterion in the native category `TopCat`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Set Topology

namespace Wikipedia.HopfProblem.OrbitPair.ClosedPushout

variable {S A B P Z : TopCat.{u}} {f : S ⟶ A} {g : S ⟶ B}
    {i : A ⟶ P} {j : B ⟶ P}
    (hi : IsClosedEmbedding i) (hj : IsClosedEmbedding j)
    (hc : ∀ p, p ∈ Set.range i ∨ p ∈ Set.range j)
    (hs : ∀ a b, i a = j b → ∃ s, f s = a ∧ g s = b)
    (F : A ⟶ Z) (G : B ⟶ Z) (w : f ≫ F = g ≫ G)

def glueFunction (p : P) : Z := by
  classical
  exact if hp : p ∈ Set.range i then F (hi.isEmbedding.toHomeomorph.symm ⟨p, hp⟩)
    else G (hj.isEmbedding.toHomeomorph.symm ⟨p, (hc p).resolve_left hp⟩)

theorem glueFunction_left (p : P) (hp : p ∈ Set.range i) :
    glueFunction hi hj hc F G p = F (hi.isEmbedding.toHomeomorph.symm ⟨p, hp⟩) := by
  classical
  exact dif_pos hp

theorem glueFunction_inl (a : A) : glueFunction hi hj hc F G (i a) = F a := by
  rw [glueFunction_left hi hj hc F G _ ⟨a, rfl⟩]
  exact congrArg F (hi.isEmbedding.toHomeomorph.symm_apply_apply a)

include hs w in
theorem glueFunction_inr (b : B) : glueFunction hi hj hc F G (j b) = G b := by
  classical
  by_cases hp : j b ∈ Set.range i
  · obtain ⟨a, ha⟩ := hp
    obtain ⟨s, hsa, hsb⟩ := hs a b ha
    rw [← ha, glueFunction_inl]
    exact (congrArg F hsa).symm.trans
      ((congrArg (fun m ↦ m s) w).trans (congrArg G hsb))
  · change (if hp : j b ∈ Set.range i then _ else _) = _
    rw [dif_neg hp]
    exact congrArg G (hj.isEmbedding.toHomeomorph.symm_apply_apply b)

include hs w in
theorem glueFunction_right (p : P) (hp : p ∈ Set.range j) :
    glueFunction hi hj hc F G p = G (hj.isEmbedding.toHomeomorph.symm ⟨p, hp⟩) := by
  have h := glueFunction_inr hi hj hc hs F G w (hj.isEmbedding.toHomeomorph.symm ⟨p, hp⟩)
  have he : j (hj.isEmbedding.toHomeomorph.symm ⟨p, hp⟩) = p :=
    congrArg Subtype.val (hj.isEmbedding.toHomeomorph.apply_symm_apply ⟨p, hp⟩)
  rw [he] at h
  exact h

include hs w in
theorem continuous_glueFunction : Continuous (glueFunction hi hj hc F G) := by
  have hl : ContinuousOn (glueFunction hi hj hc F G) (Set.range i) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (F.hom.continuous.comp hi.isEmbedding.toHomeomorph.symm.continuous).congr
      (fun p ↦ (glueFunction_left hi hj hc F G p.val p.property).symm)
  have hr : ContinuousOn (glueFunction hi hj hc F G) (Set.range j) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (G.hom.continuous.comp hj.isEmbedding.toHomeomorph.symm.continuous).congr
      (fun p ↦ (glueFunction_right hi hj hc hs F G w p.val p.property).symm)
  have he : Set.range i ∪ Set.range j = univ := eq_univ_of_forall hc
  apply continuousOn_univ.mp
  rw [← he]
  exact hl.union_of_isClosed hr hi.isClosed_range hj.isClosed_range

def glue : P ⟶ Z :=
  TopCat.ofHom ⟨glueFunction hi hj hc F G, continuous_glueFunction hi hj hc hs F G w⟩

theorem inl_glue : i ≫ glue hi hj hc hs F G w = F := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  exact glueFunction_inl hi hj hc F G

theorem inr_glue : j ≫ glue hi hj hc hs F G w = G := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  exact glueFunction_inr hi hj hc hs F G w

include hc in
theorem hom_ext {φ ψ : P ⟶ Z} (h₁ : i ≫ φ = i ≫ ψ) (h₂ : j ≫ φ = j ≫ ψ) : φ = ψ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro p
  rcases hc p with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · exact congrArg (fun m ↦ m a) h₁
  · exact congrArg (fun m ↦ m b) h₂

include hi hj hc hs in
theorem isPushout (hw : f ≫ i = g ≫ j) : IsPushout f g i j := by
  apply IsPushout.mk' hw
  · intro T φ ψ h₁ h₂
    exact hom_ext hc h₁ h₂
  · intro T F G w
    exact ⟨glue hi hj hc hs F G w, inl_glue hi hj hc hs F G w, inr_glue hi hj hc hs F G w⟩

end Wikipedia.HopfProblem.OrbitPair.ClosedPushout
