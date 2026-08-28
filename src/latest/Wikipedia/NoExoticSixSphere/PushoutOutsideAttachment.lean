import Wikipedia.HopfProblem.OrbitPairPushoutClosedEmbedding

/-!
# Subspaces away from the attaching locus in an actual pushout

An element outside the attaching image cannot be identified with another
element of its leg or with an element of the opposite leg. A set-valued
separator follows from the native pushout after forgetting topology.
Open- and closed-set detection on the two legs prove that an open or closed
embedding avoiding the attaching image remains such in the pushout.
No injectivity, compactness, or separation hypotheses on the span are used.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Set Topology
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.PushoutOutsideAttachment

variable {S A B P : TopCat.{u}} {f : S ⟶ A} {g : S ⟶ B}
    {i : A ⟶ P} {j : B ⟶ P} (hP : IsPushout f g i j)

open Classical in
include hP in
theorem exists_separator : ∃ d : P → Option B,
    (∀ a, d (i a) = none) ∧
      ∀ b, d (j b) = if b ∈ Set.range g then none else some b := by
  classical
  let F : (forget TopCat).obj A ⟶ Option B := ↾fun _ ↦ none
  let G : (forget TopCat).obj B ⟶ Option B :=
    ↾fun b ↦ if b ∈ Set.range g then none else some b
  have hc : (forget TopCat).map f ≫ F = (forget TopCat).map g ≫ G := by
    apply ConcreteCategory.hom_ext
    intro s
    change none = if g s ∈ Set.range g then none else some (g s)
    rw [if_pos (Set.mem_range_self s)]
  let d := (hP.map (forget TopCat)).desc F G hc
  refine ⟨d, ?_, ?_⟩
  · intro a
    exact ConcreteCategory.congr_hom ((hP.map (forget TopCat)).inl_desc F G hc) a
  · intro b
    exact ConcreteCategory.congr_hom ((hP.map (forget TopCat)).inr_desc F G hc) b

include hP in
theorem eq_of_notMem_range {b c : B} (hb : b ∉ Set.range g) (h : j b = j c) : b = c := by
  classical
  obtain ⟨d, _, hd⟩ := exists_separator hP
  have he := congrArg d h
  rw [hd b, hd c, if_neg hb] at he
  by_cases hc : c ∈ Set.range g
  · rw [if_pos hc] at he
    cases he
  · rw [if_neg hc] at he
    exact Option.some.inj he

include hP in
theorem ne_other_of_notMem_range {b : B} (hb : b ∉ Set.range g) (a : A) : j b ≠ i a := by
  classical
  obtain ⟨d, hi, hj⟩ := exists_separator hP
  intro h
  have he := congrArg d h
  rw [hj b, if_neg hb, hi a] at he
  cases he

variable {T : TopCat.{u}} (k : T ⟶ B)

include hP in
theorem comp_injective (hk : Function.Injective k) (havoid : ∀ t, k t ∉ Set.range g) :
    Function.Injective (k ≫ j) := by
  intro t t' h
  exact hk (eq_of_notMem_range hP (havoid t) h)

variable (hk : IsClosedEmbedding k) (havoid : ∀ t, k t ∉ Set.range g)

include hP havoid in
theorem preimage_image_left (C : Set T) : i ⁻¹' ((k ≫ j) '' C) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro a ⟨t, _, h⟩
  exact ne_other_of_notMem_range hP (havoid t) a h

include hP havoid in
theorem preimage_image_right (C : Set T) : j ⁻¹' ((k ≫ j) '' C) = k '' C := by
  ext b
  constructor
  · rintro ⟨t, ht, h⟩
    exact ⟨t, ht, eq_of_notMem_range hP (havoid t) h⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, rfl⟩

include hP hk havoid in
theorem comp_isClosedEmbedding : IsClosedEmbedding (k ≫ j) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap (k ≫ j).hom.continuous
    (comp_injective hP k hk.injective havoid)
  intro C hC
  apply (ClosedPushout.isClosed_iff hP ((k ≫ j) '' C)).mpr
  rw [preimage_image_left hP k havoid, preimage_image_right hP k havoid]
  exact ⟨isClosed_empty, hk.isClosedMap C hC⟩

include hP in
theorem isOpen_iff (U : Set P) : IsOpen U ↔ IsOpen (i ⁻¹' U) ∧ IsOpen (j ⁻¹' U) := by
  rw [← isClosed_compl_iff, ClosedPushout.isClosed_iff hP]
  simp only [Set.preimage_compl, isClosed_compl_iff]

include hP havoid in
theorem comp_isOpenEmbedding (hkOpen : IsOpenEmbedding k) : IsOpenEmbedding (k ≫ j) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap (k ≫ j).hom.continuous
    (comp_injective hP k hkOpen.injective havoid)
  intro C hC
  apply (isOpen_iff hP ((k ≫ j) '' C)).mpr
  rw [preimage_image_left hP k havoid, preimage_image_right hP k havoid]
  exact ⟨isOpen_empty, hkOpen.isOpenMap C hC⟩

end NoExoticSixSphere.PushoutOutsideAttachment
