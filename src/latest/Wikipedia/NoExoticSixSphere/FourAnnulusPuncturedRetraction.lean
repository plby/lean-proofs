import Wikipedia.NoExoticSixSphere.FourAnnulusParityBallPush
import Wikipedia.NoExoticSixSphere.SphereAnnulusClamp
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# A literal retraction onto the original punctured annulus

Clamping nonzero vectors into radii one through two avoids the actual
annulus singularities. The original finite chart pushes then remove all
open holes. The resulting map fixes the whole punctured annulus, including
both endpoint spheres and all links. Its original inclusion is therefore
injective on integral homology in every degree.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourAnnulus.ParityBallSystem

open GLOrthonormalization AnnulusDoublePoints SphereAnnulus
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} (P : ParityBallSystem g)

def inclusionComplement : C(P.puncturedAnnulus, SingularComplement g) where
  toFun y := ⟨y.val, SphereAnnulus.ne_zero ⟨y.val, y.property.1⟩,
    fun hs ↦ y.property.2 (P.singular_subset_openHoles hs)⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

include P in
theorem clamp_not_singular (y : SingularComplement g) : clamp y.val ∉ singularSet g := by
  by_cases hleft : ‖y.val‖ ≤ 1
  · intro hs
    have hn := (P.singular_subset_interior hs).1
    rw [norm_clamp_of_norm_le_one y.val y.property.1 hleft] at hn
    exact lt_irrefl _ hn
  · by_cases hright : 2 ≤ ‖y.val‖
    · intro hs
      have hn := (P.singular_subset_interior hs).2
      rw [norm_clamp_of_two_le_norm y.val y.property.1 hright] at hn
      exact lt_irrefl _ hn
    · have hy : y.val ∈ domain 3 :=
        ⟨(lt_of_not_ge hleft).le, (lt_of_not_ge hright).le⟩
      rw [clamp_of_mem_domain y.val hy]
      exact y.property.2

def clampComplement : C(SingularComplement g, SingularComplement g) where
  toFun y := ⟨clamp y.val, clamp_ne_zero y.val y.property.1, P.clamp_not_singular y⟩
  continuous_toFun :=
    ((continuousOn_clamp 3).mono (fun _ hy ↦ hy.1)).domRestrict.subtype_mk _

theorem clampComplement_mem_annulus (y : SingularComplement g) :
    (P.clampComplement y).val ∈ domain 3 := clamp_mem_domain y.val y.property.1

theorem clampComplement_fixed (y : SingularComplement g) (hy : y.val ∈ domain 3) :
    P.clampComplement y = y := Subtype.ext (clamp_of_mem_domain y.val hy)

theorem exists_retraction : ∃ R : C(SingularComplement g, P.puncturedAnnulus),
    R.comp P.inclusionComplement = ContinuousMap.id P.puncturedAnnulus := by
  obtain ⟨r, hfix, havoid, hannulus⟩ := P.exists_push_all
  let f : C(SingularComplement g, SingularComplement g) := r.comp P.clampComplement
  have hf (y : SingularComplement g) : (f y).val ∈ P.puncturedAnnulus :=
    ⟨hannulus _ (P.clampComplement_mem_annulus y), havoid _⟩
  let R : C(SingularComplement g, P.puncturedAnnulus) := {
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

def complementInnerBoundary : C(Sphere 3, SingularComplement g) :=
  P.inclusionComplement.comp P.innerBoundary

def complementOuterBoundary : C(Sphere 3, SingularComplement g) :=
  P.inclusionComplement.comp P.outerBoundary

def complementLink (x : singularSet g) : C(Sphere 3, SingularComplement g) :=
  P.inclusionComplement.comp (P.linkingSphere x)

end NoExoticSixSphere.GenericFourAnnulus.ParityBallSystem
