import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPatchFrames
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackBundle
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackLocalDiffeomorph

/-!
# Holomorphic canonical comparisons over the full actual patches

The bundle comparison induced by the actual piece inclusion is
holomorphic in the original canonical-bundle atlases.  Its target below
is the natural open inverse image of the full base patch in the global
canonical bundle, with no transported topology or complex structure.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical

open TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model
local notation "I₁" => modelWithCornersSelf ℂ ℂ

attribute [local instance] Threefold.chartedSpace localPieceChartedSpace
  localPiece_nonempty localPiece_isManifold

local instance patchesHolomorphicGlobalManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

theorem patchPushforward_holomorphic (i : Index) :
    ContMDiff ((IF).prod I₁) ((IF).prod I₁) ω (patchPushforward i) :=
  Pullback.forwardMap_holomorphic (inclusion_isLocalDiffeomorph i)

/-- The full restriction of the genuine global bundle to the actual
piece patch, with its ordinary open-subspace topology and atlas. -/
def bundlePatch (i : Index) : TopologicalSpace.Opens bundle.TotalSpace :=
  ⟨(Bundle.TotalSpace.proj : bundle.TotalSpace → Threefold.Space) ⁻¹'
    (Threefold.liftedPatch i : Set Threefold.Space),
      (Threefold.liftedPatch i).isOpen.preimage bundle.continuous_proj⟩

/-- The restricted bundle's actual base projection. -/
def bundlePatchProjection (i : Index) (p : bundlePatch i) : Threefold.liftedPatch i :=
  ⟨p.val.proj, p.property⟩

def patchPushforwardToPatch (i : Index) (p : (localBundle i).TotalSpace) : bundlePatch i :=
  ⟨patchPushforward i p, (Threefold.patchBiholomorph i p.proj).property⟩

@[simp] theorem patchPushforwardToPatch_val (i : Index) (p : (localBundle i).TotalSpace) :
    (patchPushforwardToPatch i p : bundle.TotalSpace) = patchPushforward i p := rfl

theorem patchPushforwardToPatch_bijective (i : Index) :
    Function.Bijective (patchPushforwardToPatch i) := by
  constructor
  · intro p q h
    exact patchPushforward_injective i (congrArg Subtype.val h)
  · intro p
    have hp : p.val ∈ range (patchPushforward i) := by
      rw [patchPushforward_range]
      exact p.property
    obtain ⟨q, hq⟩ := hp
    exact ⟨q, Subtype.ext hq⟩

theorem patchPushforwardToPatch_continuous (i : Index) :
    Continuous (patchPushforwardToPatch i) :=
  (patchPushforward_holomorphic i).continuous.subtype_mk _

/-- The actual bundle map is locally biholomorphic, with its native
bundle atlases, since it is the inverse-pullback map of a local biholomorphism. -/
theorem patchPushforward_isLocalDiffeomorph (i : Index) :
    IsLocalDiffeomorph ((IF).prod I₁) ((IF).prod I₁) ω (patchPushforward i) :=
  Pullback.forwardMap_isLocalDiffeomorph (inclusion_isLocalDiffeomorph i)

theorem patchPushforwardToPatch_isLocalDiffeomorph (i : Index) :
    IsLocalDiffeomorph ((IF).prod I₁) ((IF).prod I₁) ω (patchPushforwardToPatch i) :=
  isLocalDiffeomorph_codRestrictOpens ((IF).prod I₁) ((IF).prod I₁)
    (patchPushforward_isLocalDiffeomorph i) (bundlePatch i)
    (fun p => (Threefold.patchBiholomorph i p.proj).property)

/-- An actual holomorphic line-bundle comparison over the entire patch:
both total-space directions are holomorphic for the original atlases. -/
def patchBundleBiholomorph (i : Index) :
    Diffeomorph ((IF).prod I₁) ((IF).prod I₁)
      (localBundle i).TotalSpace (bundlePatch i) ω :=
  (patchPushforwardToPatch_isLocalDiffeomorph i).diffeomorphOfBijective
    (patchPushforwardToPatch_bijective i)

@[simp] theorem patchBundleBiholomorph_val (i : Index)
    (p : (localBundle i).TotalSpace) :
    (patchBundleBiholomorph i p : bundle.TotalSpace) = patchPushforward i p := rfl

@[simp] theorem patchBundleBiholomorph_proj (i : Index)
    (p : (localBundle i).TotalSpace) :
    (patchBundleBiholomorph i p).val.proj = Threefold.inclusion i p.proj := rfl

theorem patchBundleBiholomorph_projection (i : Index) (p : (localBundle i).TotalSpace) :
    bundlePatchProjection i (patchBundleBiholomorph i p) =
      Threefold.patchBiholomorph i p.proj := Subtype.ext rfl

theorem patchBundleBiholomorph_symm_proj (i : Index) (p : bundlePatch i) :
    ((patchBundleBiholomorph i).symm p).proj =
      (Threefold.patchBiholomorph i).symm (bundlePatchProjection i p) := by
  apply (Threefold.patchBiholomorph i).injective
  change Threefold.patchBiholomorph i ((patchBundleBiholomorph i).symm p).proj =
    Threefold.patchBiholomorph i
      ((Threefold.patchBiholomorph i).symm (bundlePatchProjection i p))
  rw [(Threefold.patchBiholomorph i).apply_symm_apply]
  apply Subtype.ext
  exact congrArg (fun q : bundlePatch i => q.val.proj)
    ((patchBundleBiholomorph i).apply_symm_apply p)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical
