import Wikipedia.NoExoticSixSphere.FourDiskParityBallPush
import Wikipedia.NoExoticSixSphere.UnitDiskClamp
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# A retraction onto the actual punctured disk

Radial clamping first enters the original closed disk without hitting any
of its native singular points. The finite original chart pushes then
remove all open holes. The resulting retraction fixes the entire original
punctured disk and makes its inclusion injective on integral homology.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourDisk.ParityBallSystem

open GLOrthonormalization DiskDoublePoints
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} (P : ParityBallSystem g)

def inclusionComplement : C(P.puncturedDisk, SingularComplement g) where
  toFun y := ⟨y.val, fun hs ↦ y.property.2 (P.singular_subset_openHoles hs)⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

include P in
theorem clamp_not_singular (y : SingularComplement g) :
    UnitDiskClamp.map y.val ∉ singularSet g := by
  by_cases hy : ‖y.val‖ ≤ 1
  · rw [UnitDiskClamp.map_of_norm_le y.val hy]
    exact y.property
  · intro hs
    have hn := mem_ball_zero_iff.mp (P.singular_subset_interior hs)
    rw [UnitDiskClamp.norm_map_of_one_le y.val (le_of_not_ge hy)] at hn
    exact lt_irrefl _ hn

def clampComplement : C(SingularComplement g, SingularComplement g) where
  toFun y := ⟨UnitDiskClamp.map y.val, P.clamp_not_singular y⟩
  continuous_toFun :=
    (UnitDiskClamp.continuous_map.comp continuous_subtype_val).subtype_mk _

theorem clampComplement_mem_disk (y : SingularComplement g) :
    (P.clampComplement y).val ∈ closedBall 0 1 := UnitDiskClamp.map_mem_closedBall y.val

theorem clampComplement_fixed (y : SingularComplement g) (hy : y.val ∈ closedBall 0 1) :
    P.clampComplement y = y :=
  Subtype.ext (UnitDiskClamp.map_of_norm_le y.val (mem_closedBall_zero_iff.mp hy))

theorem exists_retraction : ∃ R : C(SingularComplement g, P.puncturedDisk),
    R.comp P.inclusionComplement = ContinuousMap.id P.puncturedDisk := by
  obtain ⟨r, hfix, havoid, hdisk⟩ := P.exists_push_all
  let f : C(SingularComplement g, SingularComplement g) := r.comp P.clampComplement
  have hf (y : SingularComplement g) : (f y).val ∈ P.puncturedDisk :=
    ⟨hdisk _ (P.clampComplement_mem_disk y), havoid _⟩
  let R : C(SingularComplement g, P.puncturedDisk) := {
    toFun y := ⟨(f y).val, hf y⟩
    continuous_toFun := (continuous_subtype_val.comp f.continuous).subtype_mk hf }
  refine ⟨R, ContinuousMap.ext (fun y ↦ ?_)⟩
  apply Subtype.ext
  change (r (P.clampComplement (P.inclusionComplement y))).val = y.val
  rw [P.clampComplement_fixed (P.inclusionComplement y) y.property.1,
    hfix (P.inclusionComplement y) y.property.2]
  rfl

theorem inclusionComplement_homology_injective (n : ℕ) :
    Injective (singularHomologyMap P.inclusionComplement n) := by
  obtain ⟨R, hR⟩ := P.exists_retraction
  have he : (singularHomologyMap R n).comp (singularHomologyMap P.inclusionComplement n) =
      LinearMap.id := by
    rw [← singularHomologyMap_comp, hR, singularHomologyMap_id]
  intro a b hab
  have h := congrArg (singularHomologyMap R n) hab
  change ((singularHomologyMap R n).comp (singularHomologyMap P.inclusionComplement n)) a =
    ((singularHomologyMap R n).comp (singularHomologyMap P.inclusionComplement n)) b at h
  simpa only [he, LinearMap.id_apply] using h

def complementOuterBoundary : C(Sphere 3, SingularComplement g) :=
  P.inclusionComplement.comp P.outerBoundary

def complementLink (x : singularSet g) : C(Sphere 3, SingularComplement g) :=
  P.inclusionComplement.comp (P.linkingSphere x)

end NoExoticSixSphere.GenericFourDisk.ParityBallSystem
