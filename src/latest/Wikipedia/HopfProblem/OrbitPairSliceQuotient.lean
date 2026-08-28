import Wikipedia.HopfProblem.OrbitPairCharacterPhase

/-!
# Character slices identify actual open subsets of the original quotient

The quotient map on the identity-phase slice is an open embedding.
Together with phase splitting this gives product charts whose first
coordinate is literally the original orbit projection.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] Threefold.chartedSpace unitCircleMulAction
  unitCircleAction_continuous

local notation "Q" => CircleOrbitSpace.OrbitSpace

namespace SmoothOrbitCharacter

variable (F : SmoothOrbitCharacter)

/-- Removing phase gives a point of the actual slice. -/
def sliceProjection (x : F.nonzeroSet) : F.Slice := (F.productHomeomorph x).2

theorem sliceProjection_continuous : Continuous F.sliceProjection :=
  continuous_snd.comp F.productHomeomorph.continuous

theorem sliceProjection_surjective : Function.Surjective F.sliceProjection := by
  intro s
  refine ⟨F.productHomeomorph.symm (1, s), ?_⟩
  exact congrArg Prod.snd (F.productHomeomorph.apply_symm_apply (1, s))

theorem sliceProjection_isOpenMap : IsOpenMap F.sliceProjection :=
  isOpenMap_snd.comp F.productHomeomorph.isOpenMap

/-- Inclusion of the actual slice followed by the original quotient map. -/
def sliceOrbitMap (s : F.Slice) : Q := CircleOrbitSpace.quotientMap s.val.val

theorem sliceOrbitMap_continuous : Continuous F.sliceOrbitMap :=
  CircleOrbitSpace.quotientMap_continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val)

@[simp] theorem sliceOrbitMap_sliceProjection (x : F.nonzeroSet) :
    F.sliceOrbitMap (F.sliceProjection x) = CircleOrbitSpace.quotientMap x.val :=
  quotientMap_unitCircle_smul (F.phase x)⁻¹ x.val

theorem sliceOrbitMap_injective : Function.Injective F.sliceOrbitMap := by
  intro s t h
  obtain ⟨u, hu⟩ := (quotientMap_eq_iff_unitCircle s.val.val t.val.val).mp h
  have he : u • t.val = s.val := Subtype.ext hu
  have hp := F.phase_equivariant u t.val
  rw [he, s.property, t.property, mul_one] at hp
  have hu1 : u = 1 := hp.symm
  apply Subtype.ext
  simpa only [hu1, one_smul] using he.symm

theorem sliceOrbitMap_isOpenMap : IsOpenMap F.sliceOrbitMap := by
  apply IsOpenMap.of_comp F.sliceProjection_continuous F.sliceProjection_surjective
  have he : F.sliceOrbitMap ∘ F.sliceProjection =
      CircleOrbitSpace.quotientMap ∘ (Subtype.val : F.nonzeroSet → Threefold.Space) :=
    funext F.sliceOrbitMap_sliceProjection
  rw [he]
  exact CircleOrbitSpace.quotientMap_isOpenQuotientMap.isOpenMap.comp
    F.nonzeroSet.isOpen.isOpenMap_subtype_val

theorem sliceOrbitMap_isOpenEmbedding : IsOpenEmbedding F.sliceOrbitMap :=
  .of_continuous_injective_isOpenMap F.sliceOrbitMap_continuous
    F.sliceOrbitMap_injective F.sliceOrbitMap_isOpenMap

/-- An actual open set of the original orbit space. -/
def orbitImage : TopologicalSpace.Opens Q :=
  ⟨range F.sliceOrbitMap, F.sliceOrbitMap_isOpenMap.isOpen_range⟩

def sliceOrbitHomeomorph : F.Slice ≃ₜ F.orbitImage :=
  F.sliceOrbitMap_isOpenEmbedding.isEmbedding.toHomeomorph

theorem orbitImage_eq : (F.orbitImage : Set Q) =
    CircleOrbitSpace.quotientMap '' (F.nonzeroSet : Set Threefold.Space) := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s.val.val, s.val.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨F.sliceProjection ⟨x, hx⟩, F.sliceOrbitMap_sliceProjection ⟨x, hx⟩⟩

theorem quotientMap_preimage_orbitImage :
    CircleOrbitSpace.quotientMap ⁻¹' (F.orbitImage : Set Q) =
      (F.nonzeroSet : Set Threefold.Space) := by
  rw [F.orbitImage_eq]
  ext x
  constructor
  · rintro ⟨y, hy, hq⟩
    obtain ⟨u, rfl⟩ := (quotientMap_eq_iff_unitCircle x y).mp hq.symm
    exact F.nonzeroSet_smul u y hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem orbitImage_subset_freeOrbitLocus : (F.orbitImage : Set Q) ⊆ freeOrbitLocus := by
  rw [F.orbitImage_eq]
  rintro _ ⟨x, hx, rfl⟩
  exact quotientMap_mem_freeOrbitLocus ⟨x, F.nonzeroSet_subset_freeLocus hx⟩

/-- Product with the original orbit point as its first coordinate. -/
def orbitProductHomeomorph : F.nonzeroSet ≃ₜ F.orbitImage × Circle :=
  F.productHomeomorph.trans
    ((Homeomorph.prodCongr (Homeomorph.refl Circle) F.sliceOrbitHomeomorph).trans
      (Homeomorph.prodComm Circle F.orbitImage))

@[simp] theorem orbitProductHomeomorph_fst (x : F.nonzeroSet) :
    ((F.orbitProductHomeomorph x).1 : Q) = CircleOrbitSpace.quotientMap x.val :=
  F.sliceOrbitMap_sliceProjection x

@[simp] theorem orbitProductHomeomorph_snd (x : F.nonzeroSet) :
    (F.orbitProductHomeomorph x).2 = F.phase x := rfl

end SmoothOrbitCharacter

end Wikipedia.HopfProblem.OrbitPair
