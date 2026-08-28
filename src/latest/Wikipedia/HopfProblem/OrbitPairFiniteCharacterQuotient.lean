import Wikipedia.HopfProblem.OrbitPairFiniteCharacters

/-!
# The actual quotient over a finite character neighborhood

Both the total space and base are open subspaces of the original
spaces. The restricted projection is an open quotient with the
original unit-circle fibres.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] unitCircleMulAction unitCircleAction_continuous

variable (s : Finset SmoothOrbitCharacter)

instance finiteCharacter_mulAction : MulAction Circle (finiteCharacterDomain s) where
  smul u x := ⟨u • x.val, (finiteCharacterDomain_invariant s u x.val).mpr x.property⟩
  one_smul x := Subtype.ext (one_smul Circle x.val)
  mul_smul u v x := Subtype.ext (mul_smul u v x.val)

instance finiteCharacter_continuousSMul : ContinuousSMul Circle (finiteCharacterDomain s) :=
  ⟨(continuous_fst.smul (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩

def finiteCharacterOrbitImage : TopologicalSpace.Opens CircleOrbitSpace.OrbitSpace :=
  ⟨CircleOrbitSpace.quotientMap '' (finiteCharacterDomain s : Set Threefold.Space),
    CircleOrbitSpace.quotientMap_isOpenQuotientMap.isOpenMap _ (finiteCharacterDomain s).isOpen⟩

def finiteCharacterProjection (x : finiteCharacterDomain s) : finiteCharacterOrbitImage s :=
  ⟨CircleOrbitSpace.quotientMap x.val, ⟨x.val, x.property, rfl⟩⟩

theorem finiteCharacterProjection_continuous : Continuous (finiteCharacterProjection s) :=
  (CircleOrbitSpace.quotientMap_continuous.comp continuous_subtype_val).subtype_mk _

theorem finiteCharacterProjection_surjective : Function.Surjective (finiteCharacterProjection s) := by
  rintro ⟨y, x, hx, he⟩
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

theorem finiteCharacterProjection_isOpenMap : IsOpenMap (finiteCharacterProjection s) :=
  (CircleOrbitSpace.quotientMap_isOpenQuotientMap.isOpenMap.domRestrict
    (finiteCharacterDomain s).isOpen).subtype_mk _

theorem finiteCharacterProjection_isOpenQuotientMap : IsOpenQuotientMap (finiteCharacterProjection s) :=
  ⟨finiteCharacterProjection_surjective s, finiteCharacterProjection_continuous s,
    finiteCharacterProjection_isOpenMap s⟩

theorem finiteCharacterProjection_smul (u : Circle) (x : finiteCharacterDomain s) :
    finiteCharacterProjection s (u • x) = finiteCharacterProjection s x :=
  Subtype.ext (quotientMap_unitCircle_smul u x.val)

theorem finiteCharacterProjection_eq_iff (x y : finiteCharacterDomain s) :
    finiteCharacterProjection s x = finiteCharacterProjection s y ↔ ∃ u : Circle, u • y = x := by
  constructor
  · intro h
    obtain ⟨u, hu⟩ := (quotientMap_eq_iff_unitCircle x.val y.val).mp (congrArg Subtype.val h)
    exact ⟨u, Subtype.ext hu⟩
  · rintro ⟨u, rfl⟩
    exact finiteCharacterProjection_smul s u y

theorem finiteCharacterOrbitImage_subset_freeOrbitLocus :
    (finiteCharacterOrbitImage s : Set CircleOrbitSpace.OrbitSpace) ⊆ freeOrbitLocus := by
  rintro _ ⟨x, hx, rfl⟩
  exact quotientMap_mem_freeOrbitLocus ⟨x, finiteCharacterDomain_subset_freeLocus s hx⟩

theorem quotientMap_preimage_finiteCharacterOrbitImage :
    CircleOrbitSpace.quotientMap ⁻¹' (finiteCharacterOrbitImage s : Set CircleOrbitSpace.OrbitSpace) =
      (finiteCharacterDomain s : Set Threefold.Space) := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨u, rfl⟩ := (quotientMap_eq_iff_unitCircle x y).mp he.symm
    exact (finiteCharacterDomain_invariant s u y).mpr hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem compact_free_quotient_in_finiteCharacterOrbitImage (K : Set freeOrbitLocus)
    (hK : IsCompact K) : ∃ s : Finset SmoothOrbitCharacter,
      ∀ y ∈ K, y.val ∈ finiteCharacterOrbitImage s := by
  obtain ⟨s, hs⟩ := compact_free_quotient_finite_characters K hK
  refine ⟨s, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := freeOrbitProjection_surjective y
  exact ⟨x.val, (characterEnergy_pos_iff s x.val).mpr (hs x hy), rfl⟩

end Wikipedia.HopfProblem.OrbitPair
