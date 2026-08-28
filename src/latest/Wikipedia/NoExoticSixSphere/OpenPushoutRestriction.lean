import Wikipedia.NoExoticSixSphere.PushoutOutsideAttachment
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Removing points from the attached leg of an actual pushout

An open subset of the pushout containing the whole base is again a
pushout, with the attaching space unchanged and the other leg restricted
to its actual preimage. The proof keeps the original maps and the
subspace topology. Injectivity of the attaching inclusion is sufficient;
the attaching map into the base need not be injective.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Set Topology TopologicalSpace
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.OpenPushoutRestriction

variable {S A B P : TopCat.{u}} {f : S ⟶ A} {g : S ⟶ B}
  {i : A ⟶ P} {j : B ⟶ P} (hP : IsPushout f g i j)
  (U : Opens P) (hA : ∀ a, i a ∈ U)

def left : A ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun a ↦ ⟨i a, hA a⟩, i.hom.continuous.subtype_mk _⟩

def right : TopCat.of (j ⁻¹' (U : Set P)) ⟶ TopCat.of U :=
  TopCat.ofHom ⟨fun b ↦ ⟨j b.val, b.property⟩,
    (j.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

include hP hA in
theorem attaching_mem (s : S) : j (g s) ∈ U := by
  have he : i (f s) = j (g s) := congrArg (fun k ↦ k s) hP.w
  exact he ▸ hA (f s)

def attaching : S ⟶ TopCat.of (j ⁻¹' (U : Set P)) :=
  TopCat.ofHom ⟨fun s ↦ ⟨g s, attaching_mem hP U hA s⟩,
    g.hom.continuous.subtype_mk _⟩

theorem square : f ≫ left U hA = attaching hP U hA ≫ right (j := j) U := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro s
  exact Subtype.ext (congrArg (fun k ↦ k s) hP.w)

def sumMap : C(A ⊕ (j ⁻¹' (U : Set P)), U) :=
  ⟨Sum.elim (left U hA) (right (j := j) U),
    continuous_sumElim.mpr ⟨(left U hA).hom.continuous, (right (j := j) U).hom.continuous⟩⟩

include hP in
theorem sumMap_surjective : Function.Surjective (sumMap (j := j) U hA) := by
  intro x
  obtain (⟨a, ha⟩ | ⟨b, hb⟩) := Types.eq_or_eq_of_isPushout (hP.map (forget TopCat)) x.val
  · exact ⟨Sum.inl a, Subtype.ext ha⟩
  · change j b = x.val at hb
    have hbu : j b ∈ U := by rw [hb]; exact x.property
    exact ⟨Sum.inr ⟨b, hbu⟩, Subtype.ext hb⟩

theorem preimage_image_left (W : Set U) :
    i ⁻¹' (Subtype.val '' W) = left U hA ⁻¹' W := by
  change (Subtype.val ∘ left U hA) ⁻¹' (Subtype.val '' W) = _
  rw [Set.preimage_comp, Set.preimage_image_eq _ Subtype.val_injective]

theorem preimage_image_right (W : Set U) :
    j ⁻¹' (Subtype.val '' W) =
      Subtype.val '' (right (j := j) U ⁻¹' W) := by
  ext b
  constructor
  · rintro ⟨x, hx, he⟩
    have hb : j b ∈ U := he ▸ x.property
    refine ⟨⟨b, hb⟩, ?_, rfl⟩
    have he' : right (j := j) U ⟨b, hb⟩ = x := Subtype.ext he.symm
    change right (j := j) U ⟨b, hb⟩ ∈ W
    exact he'.symm ▸ hx
  · rintro ⟨b', hb', he⟩
    exact ⟨right (j := j) U b', hb', congrArg j he⟩

include hP in
theorem isQuotientMap_sumMap : IsQuotientMap (sumMap (j := j) U hA) := by
  refine ⟨.of_isOpen_preimage_iff_isOpen (fun W ↦ ?_), sumMap_surjective hP U hA⟩
  constructor
  · intro hW
    have hleft : IsOpen (left U hA ⁻¹' W) := (isOpen_sum_iff.mp hW).1
    have hright : IsOpen (right (j := j) U ⁻¹' W) := (isOpen_sum_iff.mp hW).2
    have hambient : IsOpen (Subtype.val '' W : Set P) := by
      apply (PushoutOutsideAttachment.isOpen_iff hP _).mpr
      rw [preimage_image_left U hA, preimage_image_right (j := j) U]
      exact ⟨hleft, (U.isOpen.preimage j.hom.continuous).isOpenEmbedding_subtypeVal.isOpenMap
        _ hright⟩
    have hsub := hambient.preimage (continuous_subtype_val : Continuous (Subtype.val : U → P))
    simpa only [Set.preimage_image_eq _ Subtype.val_injective] using hsub
  · exact fun hW ↦ hW.preimage (sumMap (j := j) U hA).continuous

variable (hg : Function.Injective g) {Z : TopCat.{u}}
  (F : A ⟶ Z) (G : TopCat.of (j ⁻¹' (U : Set P)) ⟶ Z)
  (hFG : f ≫ F = attaching hP U hA ≫ G)

include hP hg hFG in
theorem cross_compatible (a : A) (b : j ⁻¹' (U : Set P)) (he : i a = j b.val) :
    F a = G b := by
  obtain ⟨s, hs, ht⟩ := ClosedPushout.overlap_witness hP hg a b.val he
  have hb : attaching hP U hA s = b := Subtype.ext ht
  exact (congrArg F hs).symm.trans
    ((congrArg (fun k ↦ k s) hFG).trans (congrArg G hb))

include hP hg hFG in
theorem sum_respects : Function.FactorsThrough (Sum.elim F G) (sumMap (j := j) U hA) := by
  intro x y hxy
  cases x with
  | inl a =>
    cases y with
    | inl a' =>
      exact congrArg F (ClosedPushout.base_injective hP hg (congrArg Subtype.val hxy))
    | inr b =>
      exact cross_compatible hP U hA hg F G hFG a b (congrArg Subtype.val hxy)
  | inr b =>
    cases y with
    | inl a =>
      exact (cross_compatible hP U hA hg F G hFG a b (congrArg Subtype.val hxy).symm).symm
    | inr b' =>
      have he : j b.val = j b'.val := congrArg Subtype.val hxy
      by_cases hb : b.val ∈ Set.range g
      · obtain ⟨s, hs⟩ := hb
        have hcross : i (f s) = j b.val :=
          (congrArg (fun k ↦ k s) hP.w).trans (congrArg j hs)
        exact (cross_compatible hP U hA hg F G hFG (f s) b hcross).symm.trans
          (cross_compatible hP U hA hg F G hFG (f s) b' (hcross.trans he))
      · exact congrArg G (Subtype.ext (PushoutOutsideAttachment.eq_of_notMem_range hP hb he))

def glue : TopCat.of U ⟶ Z :=
  TopCat.ofHom (IsQuotientMap.lift (isQuotientMap_sumMap hP U hA)
    ⟨Sum.elim F G, continuous_sumElim.mpr ⟨F.hom.continuous, G.hom.continuous⟩⟩
    (sum_respects hP U hA hg F G hFG))

theorem left_glue : left U hA ≫ glue hP U hA hg F G hFG = F := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro a
  exact ContinuousMap.congr_fun
    (IsQuotientMap.lift_comp (isQuotientMap_sumMap hP U hA)
      ⟨Sum.elim F G, continuous_sumElim.mpr ⟨F.hom.continuous, G.hom.continuous⟩⟩
      (sum_respects hP U hA hg F G hFG)) (Sum.inl a)

theorem right_glue : right (j := j) U ≫ glue hP U hA hg F G hFG = G := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro b
  exact ContinuousMap.congr_fun
    (IsQuotientMap.lift_comp (isQuotientMap_sumMap hP U hA)
      ⟨Sum.elim F G, continuous_sumElim.mpr ⟨F.hom.continuous, G.hom.continuous⟩⟩
      (sum_respects hP U hA hg F G hFG)) (Sum.inr b)

include hP hg in
theorem isPushout : IsPushout f (attaching hP U hA) (left U hA) (right (j := j) U) := by
  apply IsPushout.mk' (square hP U hA)
  · intro T φ ψ hl hr
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    obtain ⟨a | b, he⟩ := sumMap_surjective hP U hA x
    · rw [← he]
      exact congrArg (fun k ↦ k a) hl
    · rw [← he]
      exact congrArg (fun k ↦ k b) hr
  · intro T F G hFG
    exact ⟨glue hP U hA hg F G hFG, left_glue hP U hA hg F G hFG,
      right_glue hP U hA hg F G hFG⟩

end NoExoticSixSphere.OpenPushoutRestriction
