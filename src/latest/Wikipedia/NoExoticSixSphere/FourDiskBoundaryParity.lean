import Wikipedia.NoExoticSixSphere.FourDiskBoundaryRelation
import Wikipedia.NoExoticSixSphere.PartialFrameSphereHomology

/-!
# The actual disk boundary obstruction is the sum of its linking values

The signed integral boundary relation is evaluated by the checked frame
homology invariant. Modulo two its unit signs disappear. Thus parity-one
links and an even number of actual punctures force the original outer
frame to extend. No immersion of the whole disk is asserted.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourDisk.ParityBallSystem

open GLOrthonormalization DiskDoublePoints Stiefel
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} (P : ParityBallSystem g)

theorem outer_frame_obstruction_eq_sum [Fintype (singularSet g)] (r : ℕ)
    (F : C(P.puncturedDisk, Space (3 + (r + 2)) (r + 2))) :
    sphereThirdObstruction r (F.comp P.outerBoundary) =
      ∑ x, sphereThirdObstruction r (F.comp (P.linkingSphere x)) := by
  have h : sphereThirdObstruction r (F.comp P.outerBoundary) =
      ∑ x, P.boundaryCoefficient x • sphereThirdObstruction r (F.comp (P.linkingSphere x)) := by
    have he := congrArg (fun a ↦ stableThirdHomologyEquivZModTwo r (singularHomologyMap F 3 a))
      (P.outer_eq_sum_linkingSpheres sphereThirdClass)
    simpa only [sphereThirdObstruction_eq_homology, singularHomologyMap_comp,
      LinearMap.comp_apply, map_sum, map_zsmul] using he
  rw [h]
  apply Finset.sum_congr rfl
  intro x _
  rcases P.boundaryCoefficient_eq_one_or_neg_one x with hx | hx
  · rw [hx, one_zsmul]
  · rw [hx, neg_one_zsmul, ZMod.neg_eq_self_mod_two]

theorem outer_frame_obstruction_zero_of_even_links (r : ℕ)
    (F : C(P.puncturedDisk, Space (3 + (r + 2)) (r + 2)))
    (heven : Even (singularSet g).ncard)
    (hlinks : ∀ x : singularSet g, sphereThirdObstruction r (F.comp (P.linkingSphere x)) = 1) :
    sphereThirdObstruction r (F.comp P.outerBoundary) = 0 := by
  let := P.finite_singular.to_subtype
  let := Fintype.ofFinite (singularSet g)
  have hcard : (Fintype.card (singularSet g) : ZMod 2) = 0 := by
    apply ZMod.natCast_eq_zero_iff_even.mpr
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact heven
  have h := P.outer_frame_obstruction_eq_sum r F
  simpa only [hlinks, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard] using h

theorem outer_frame_extends_of_even_links (r : ℕ)
    (F : C(P.puncturedDisk, Space (3 + (r + 2)) (r + 2)))
    (heven : Even (singularSet g).ncard)
    (hlinks : ∀ x : singularSet g, sphereThirdObstruction r (F.comp (P.linkingSphere x)) = 1) :
    DiskBoundary.Extends (F.comp P.outerBoundary) :=
  (sphereThirdObstruction_zero_iff_extension r (F.comp P.outerBoundary)).mp
    (P.outer_frame_obstruction_zero_of_even_links r F heven hlinks)

end NoExoticSixSphere.GenericFourDisk.ParityBallSystem
