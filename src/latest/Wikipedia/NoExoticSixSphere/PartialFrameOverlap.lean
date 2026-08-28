import Wikipedia.NoExoticSixSphere.PartialFrameTransition

/-!
# The actual intersection of two partial-frame bundle charts

The intersection carries its original subspace topology. In the first chart
it is the product of the base intersection and the smaller frame space.
The two actual inclusion maps have fiber coordinates equal respectively to
the second projection and to the proved transition map.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ColumnBundle

open GLOrthonormalization Set

variable {n r : ℕ} (v : UnitSphere (Vector (r + 1)))
  (c d : UnitSphere (Vector (n + 1)))

abbrev Patch := (column v) ⁻¹' baseSet c
abbrev Overlap := Patch v c ∩ Patch v d

def overlapForward (a : Overlap v c d) : ↥(baseSet c ∩ baseSet d) × Space n r :=
  (⟨column v a.val, a.property⟩, (toCoordinates v c a.val).2)

def overlapBackward (p : ↥(baseSet c ∩ baseSet d) × Space n r) : Overlap v c d :=
  ⟨fromCoordinates v c (p.1.val, p.2), by
    change column v (fromCoordinates v c (p.1.val, p.2)) ∈ baseSet c ∩ baseSet d
    rw [column_fromCoordinates]
    exact p.1.property⟩

theorem continuous_overlapForward : Continuous (overlapForward v c d) := by
  have ha : Continuous (fun a : Overlap v c d ↦ a.val) := continuous_subtype_val
  have hb : Continuous (fun a : Overlap v c d ↦ column v a.val) :=
    (column v).continuous.comp ha
  have ht := continuous_toCoordinates v c (fun a : Overlap v c d ↦ a.val) ha
    (fun a ↦ a.property.1)
  exact (hb.subtype_mk _).prodMk ht.snd

theorem continuous_overlapBackward : Continuous (overlapBackward v c d) := by
  let pmap : ↥(baseSet c ∩ baseSet d) × Space n r →
      UnitSphere (Vector (n + 1)) × Space n r := fun p ↦ (p.1.val, p.2)
  have hp : Continuous pmap :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hf := continuous_fromCoordinates v c pmap hp (fun p ↦ p.1.property.1)
  exact hf.subtype_mk _

def overlapHomeomorph : Overlap v c d ≃ₜ ↥(baseSet c ∩ baseSet d) × Space n r where
  toFun := overlapForward v c d
  invFun := overlapBackward v c d
  left_inv a := Subtype.ext (fromCoordinates_toCoordinates v c a.val)
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (column_fromCoordinates v c (p.1.val, p.2))
    · change (toCoordinates v c (fromCoordinates v c (p.1.val, p.2))).2 = p.2
      exact congrArg Prod.snd (toCoordinates_fromCoordinates v c (p.1.val, p.2))
  continuous_toFun := continuous_overlapForward v c d
  continuous_invFun := continuous_overlapBackward v c d

theorem overlapHomeomorph_symm_val (p : ↥(baseSet c ∩ baseSet d) × Space n r) :
    ((overlapHomeomorph v c d).symm p).val = fromCoordinates v c (p.1.val, p.2) := rfl

def patchFiber : C(Patch v c, Space n r) :=
  ⟨fun a ↦ (toCoordinates v c a.val).2,
    (continuous_toCoordinates v c Subtype.val continuous_subtype_val Subtype.property).snd⟩

def overlapLeft : C(Overlap v c d, Patch v c) :=
  ContinuousMap.inclusion inter_subset_left

def overlapRight : C(Overlap v c d, Patch v d) :=
  ContinuousMap.inclusion inter_subset_right

theorem overlapLeft_fiber (p : ↥(baseSet c ∩ baseSet d) × Space n r) :
    patchFiber v c (overlapLeft v c d ((overlapHomeomorph v c d).symm p)) = p.2 := by
  change (toCoordinates v c (fromCoordinates v c (p.1.val, p.2))).2 = p.2
  rw [toCoordinates_fromCoordinates]

theorem overlapRight_fiber (p : ↥(baseSet c ∩ baseSet d) × Space n r) :
    patchFiber v d (overlapRight v c d ((overlapHomeomorph v c d).symm p)) =
      transition v d c p.1.val p.2 := rfl

end NoExoticSixSphere.Stiefel.ColumnBundle
