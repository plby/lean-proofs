import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalCuspMap

/-!
# The full image of the native cusp canonical bundle

The map defined by inverse cotangent pullback along the actual cusp
inclusion is injective.  Its image is exactly the restriction of the
global canonical bundle to the full cusp patch.  The original native
patch biholomorphism and the actual fibre pullback give an explicit
two-sided inverse on that full image.
-/

noncomputable section

open Function Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Cusp

open CuspGeometry

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

/-- The inverse cotangent comparison is injective on the actual bundle
total space, since both its base inclusion and each fibre map are injective. -/
theorem nativeForwardMap_injective : Injective nativeForwardMap := by
  intro p q h
  obtain ⟨x, v⟩ := p
  obtain ⟨y, w⟩ := q
  have hb : CuspGeometry.inclusion x = CuspGeometry.inclusion y :=
    congrArg Bundle.TotalSpace.proj h
  have hxy := CuspGeometry.inclusion_injective hb
  subst y
  have hv : (inclusionPullback x).symm v = (inclusionPullback x).symm w :=
    congrArg (fun r : bundle.TotalSpace => id (α := ℂ) r.2) h
  have hvw := (inclusionPullback x).symm.injective hv
  subst w
  rfl

theorem nativeForwardMap_mem_patch (p : nativeBundle.TotalSpace) :
    (nativeForwardMap p).proj ∈
      (Threefold.liftedPatch (some none) : Set Threefold.Space) :=
  (nativePatchBiholomorph p.proj).property

/-- Every global canonical covector over the full cusp patch comes from
a unique vector in the original native cusp canonical bundle. -/
theorem nativeForwardMap_range :
    range nativeForwardMap =
      (Bundle.TotalSpace.proj : bundle.TotalSpace → Threefold.Space) ⁻¹'
        (Threefold.liftedPatch (some none) : Set Threefold.Space) := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    exact nativeForwardMap_mem_patch q
  · intro hp
    obtain ⟨y, v⟩ := p
    have hy : y ∈ range CuspGeometry.inclusion := by
      rw [CuspGeometry.inclusion_range]
      exact hp
    obtain ⟨x, hx⟩ := hy
    subst y
    refine ⟨⟨x, inclusionPullback x v⟩, ?_⟩
    simp only [nativeForwardMap, ContinuousLinearEquiv.symm_apply_apply]

/-- The literal full preimage is open for the original global bundle
topology, so it carries the inherited open-submanifold atlas. -/
def fullPatchTotalOpen : TopologicalSpace.Opens bundle.TotalSpace :=
  ⟨(Bundle.TotalSpace.proj : bundle.TotalSpace → Threefold.Space) ⁻¹'
      (Threefold.liftedPatch (some none) : Set Threefold.Space),
    (Threefold.liftedPatch (some none)).isOpen.preimage
      (FiberBundle.continuous_proj ℂ bundle.Fiber)⟩

@[simp] theorem fullPatchTotalOpen_coe :
    (fullPatchTotalOpen : Set bundle.TotalSpace) =
      (Bundle.TotalSpace.proj : bundle.TotalSpace → Threefold.Space) ⁻¹'
        (Threefold.liftedPatch (some none) : Set Threefold.Space) := rfl

/-- The actual full cusp-patch total space with its inherited open-submanifold atlas. -/
abbrev FullPatchTotalSpace := ↥fullPatchTotalOpen

/-- The same actual canonical-bundle map, with its full image as codomain. -/
def nativeForwardMapToPatch (p : nativeBundle.TotalSpace) : FullPatchTotalSpace :=
  ⟨nativeForwardMap p, nativeForwardMap_mem_patch p⟩

@[simp] theorem nativeForwardMapToPatch_val (p : nativeBundle.TotalSpace) :
    (nativeForwardMapToPatch p).val = nativeForwardMap p := rfl

@[simp] theorem nativeForwardMapToPatch_proj (p : nativeBundle.TotalSpace) :
    (nativeForwardMapToPatch p).val.proj = CuspGeometry.inclusion p.proj := rfl

theorem nativeForwardMapToPatch_injective : Injective nativeForwardMapToPatch := by
  intro p q h
  exact nativeForwardMap_injective (congrArg Subtype.val h)

theorem nativeForwardMapToPatch_surjective : Surjective nativeForwardMapToPatch := by
  intro p
  have hp : p.val ∈ range nativeForwardMap := by
    rw [nativeForwardMap_range]
    exact p.property
  obtain ⟨q, hq⟩ := hp
  exact ⟨q, Subtype.ext hq⟩

/-- The explicit inverse uses the original native patch inverse on the
base and genuine derivative pullback on each canonical fibre. -/
def nativeBackwardMap (p : FullPatchTotalSpace) : nativeBundle.TotalSpace :=
  let x := nativePatchBiholomorph.symm ⟨p.val.proj, p.property⟩
  ⟨x, inclusionPullback x (id (α := ℂ) p.val.2)⟩

@[simp] theorem nativeBackwardMap_proj (p : FullPatchTotalSpace) :
    (nativeBackwardMap p).proj =
      nativePatchBiholomorph.symm ⟨p.val.proj, p.property⟩ := rfl

theorem nativeBackwardMap_inclusion_proj (p : FullPatchTotalSpace) :
    CuspGeometry.inclusion (nativeBackwardMap p).proj = p.val.proj :=
  congrArg Subtype.val
    (nativePatchBiholomorph.apply_symm_apply ⟨p.val.proj, p.property⟩)

@[simp] theorem nativeForwardMapToPatch_nativeBackwardMap (p : FullPatchTotalSpace) :
    nativeForwardMapToPatch (nativeBackwardMap p) = p := by
  apply Subtype.ext
  apply Bundle.TotalSpace.ext
  · exact nativeBackwardMap_inclusion_proj p
  · apply heq_of_eq
    change (inclusionPullback
      (nativePatchBiholomorph.symm ⟨p.val.proj, p.property⟩)).symm
        (inclusionPullback
          (nativePatchBiholomorph.symm ⟨p.val.proj, p.property⟩) (id (α := ℂ) p.val.2)) =
      id (α := ℂ) p.val.2
    exact (inclusionPullback _).symm_apply_apply _

@[simp] theorem nativeBackwardMap_nativeForwardMapToPatch (p : nativeBundle.TotalSpace) :
    nativeBackwardMap (nativeForwardMapToPatch p) = p := by
  apply nativeForwardMap_injective
  exact congrArg Subtype.val
    (nativeForwardMapToPatch_nativeBackwardMap (nativeForwardMapToPatch p))

/-- An explicit equivalence with the full global cusp-patch total space.
Its two maps are the actual inverse cotangent and cotangent comparisons. -/
def nativePatchTotalEquiv : nativeBundle.TotalSpace ≃ FullPatchTotalSpace where
  toFun := nativeForwardMapToPatch
  invFun := nativeBackwardMap
  left_inv := nativeBackwardMap_nativeForwardMapToPatch
  right_inv := nativeForwardMapToPatch_nativeBackwardMap

@[simp] theorem nativePatchTotalEquiv_apply (p : nativeBundle.TotalSpace) :
    nativePatchTotalEquiv p = nativeForwardMapToPatch p := rfl

@[simp] theorem nativePatchTotalEquiv_symm_apply (p : FullPatchTotalSpace) :
    nativePatchTotalEquiv.symm p = nativeBackwardMap p := rfl

@[simp] theorem nativePatchTotalEquiv_proj (p : nativeBundle.TotalSpace) :
    (nativePatchTotalEquiv p).val.proj = CuspGeometry.inclusion p.proj := rfl

@[simp] theorem nativePatchTotalEquiv_symm_proj (p : FullPatchTotalSpace) :
    (nativePatchTotalEquiv.symm p).proj =
      nativePatchBiholomorph.symm ⟨p.val.proj, p.property⟩ := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Cusp
