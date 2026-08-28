import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalCuspRange
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalCuspLocalDiffeomorph

/-!
# The actual full-patch cusp canonical-bundle biholomorphism

The previously constructed inverse cotangent map is a local
biholomorphism and a bijection onto the full global cusp-patch total
space.  Its explicit inverse is therefore holomorphic for the inherited
open-submanifold atlas.  The biholomorphism below retains exactly the
original total-space equivalence and its explicit cotangent inverse.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Cusp

open ToricCharts CuspGeometry

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] CuspGeometry.nativeChartedSpace Threefold.chartedSpace

/-- Restrict only the target to the literal full image, with its inherited
open-submanifold atlas. -/
theorem nativeForwardMapToPatch_isLocalDiffeomorph :
    IsLocalDiffeomorph ((I₃).prod I₁) ((IF).prod I₁) ω nativeForwardMapToPatch :=
  isLocalDiffeomorph_codRestrictOpens ((I₃).prod I₁) ((IF).prod I₁)
    nativeForwardMap_isLocalDiffeomorph fullPatchTotalOpen nativeForwardMap_mem_patch

theorem nativeForwardMapToPatch_holomorphic :
    ContMDiff ((I₃).prod I₁) ((IF).prod I₁) ω nativeForwardMapToPatch :=
  nativeForwardMapToPatch_isLocalDiffeomorph.contMDiff

/-- The explicit native-patch and cotangent inverse, not a replacement
inverse or a transported chart structure, is holomorphic. -/
theorem nativeBackwardMap_holomorphic :
    ContMDiff ((IF).prod I₁) ((I₃).prod I₁) ω nativeBackwardMap := by
  let e := nativeForwardMapToPatch_isLocalDiffeomorph.diffeomorphOfBijective
    ⟨nativeForwardMapToPatch_injective, nativeForwardMapToPatch_surjective⟩
  have h : nativeBackwardMap = e.symm := by
    funext p
    apply nativeForwardMapToPatch_injective
    rw [nativeForwardMapToPatch_nativeBackwardMap]
    exact (e.apply_symm_apply p).symm
  rw [h]
  exact e.symm.contMDiff

/-- The actual native cusp canonical bundle is biholomorphic, fibrewise
linearly over the native cusp inclusion, to the full cusp-patch restriction
of the original global canonical bundle. -/
def nativePatchTotalBiholomorph :
    Diffeomorph ((I₃).prod I₁) ((IF).prod I₁)
      nativeBundle.TotalSpace FullPatchTotalSpace ω where
  toEquiv := nativePatchTotalEquiv
  contMDiff_toFun := nativeForwardMapToPatch_holomorphic
  contMDiff_invFun := nativeBackwardMap_holomorphic

@[simp] theorem nativePatchTotalBiholomorph_toEquiv :
    nativePatchTotalBiholomorph.toEquiv = nativePatchTotalEquiv := rfl

@[simp] theorem nativePatchTotalBiholomorph_apply (p : nativeBundle.TotalSpace) :
    nativePatchTotalBiholomorph p = nativeForwardMapToPatch p := rfl

@[simp] theorem nativePatchTotalBiholomorph_symm_apply (p : FullPatchTotalSpace) :
    nativePatchTotalBiholomorph.symm p = nativeBackwardMap p := rfl

@[simp] theorem nativePatchTotalBiholomorph_val (p : nativeBundle.TotalSpace) :
    (nativePatchTotalBiholomorph p).val = nativeForwardMap p := rfl

@[simp] theorem nativePatchTotalBiholomorph_proj (p : nativeBundle.TotalSpace) :
    (nativePatchTotalBiholomorph p).val.proj = CuspGeometry.inclusion p.proj := rfl

@[simp] theorem nativePatchTotalBiholomorph_symm_proj (p : FullPatchTotalSpace) :
    (nativePatchTotalBiholomorph.symm p).proj =
      nativePatchBiholomorph.symm ⟨p.val.proj, p.property⟩ := rfl

@[simp] theorem nativePatchTotalBiholomorph_mk (x : LocalSpace)
    (v : nativeBundle.Fiber x) :
    (nativePatchTotalBiholomorph ⟨x, v⟩).val =
      ⟨CuspGeometry.inclusion x, (inclusionPullback x).symm v⟩ := rfl

@[simp] theorem nativePatchTotalBiholomorph_symm_mk
    (y : Threefold.liftedPatch (some none)) (v : bundle.Fiber y.val) :
    nativePatchTotalBiholomorph.symm ⟨⟨y.val, v⟩, y.property⟩ =
      ⟨nativePatchBiholomorph.symm y,
        inclusionPullback (nativePatchBiholomorph.symm y) (id (α := ℂ) v)⟩ := rfl

theorem nativePatchTotalBiholomorph_add (x : LocalSpace)
    (v w : nativeBundle.Fiber x) :
    id (α := ℂ) (nativePatchTotalBiholomorph ⟨x, v + w⟩).val.2 =
      id (α := ℂ) (nativePatchTotalBiholomorph ⟨x, v⟩).val.2 +
        id (α := ℂ) (nativePatchTotalBiholomorph ⟨x, w⟩).val.2 :=
  nativeForwardMap_add x v w

theorem nativePatchTotalBiholomorph_smul (x : LocalSpace)
    (c : ℂ) (v : nativeBundle.Fiber x) :
    id (α := ℂ) (nativePatchTotalBiholomorph ⟨x, c • v⟩).val.2 =
      c • id (α := ℂ) (nativePatchTotalBiholomorph ⟨x, v⟩).val.2 :=
  nativeForwardMap_smul x c v

/-- The unrestricted actual bundle map is an open embedding into the
unchanged global canonical total space. -/
theorem nativeForwardMap_openEmbedding : IsOpenEmbedding nativeForwardMap :=
  isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
    ⟨nativeForwardMap_continuous, nativeForwardMap_injective,
      nativeForwardMap_isLocalDiffeomorph.isOpenMap⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Cusp
