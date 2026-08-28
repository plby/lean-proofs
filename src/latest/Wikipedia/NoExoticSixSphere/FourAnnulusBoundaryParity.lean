import Wikipedia.NoExoticSixSphere.FourAnnulusBoundaryRelation
import Wikipedia.NoExoticSixSphere.PartialFrameParityComplete
import Wikipedia.NoExoticSixSphere.PartialFrameSphereHomology

/-!
# Equality of the two original annulus frame obstructions

The signed two-ended homology relation evaluates to a difference of frame
obstructions. Its unit signs disappear modulo two. Parity-one links and
an even number of actual punctures therefore identify the two endpoint
obstructions, and completeness gives a homotopy between those endpoint
frames. Neither endpoint obstruction is asserted to vanish.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourAnnulus.ParityBallSystem

open GLOrthonormalization AnnulusDoublePoints Stiefel
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {g : Vector 4 → M} (P : ParityBallSystem g)

theorem outer_sub_inner_frame_obstruction_eq_sum [Fintype (singularSet g)] (r : ℕ)
    (F : C(P.puncturedAnnulus, Space (3 + (r + 2)) (r + 2))) :
    sphereThirdObstruction r (F.comp P.outerBoundary) -
        sphereThirdObstruction r (F.comp P.innerBoundary) =
      ∑ x, sphereThirdObstruction r (F.comp (P.linkingSphere x)) := by
  have h : sphereThirdObstruction r (F.comp P.outerBoundary) -
        sphereThirdObstruction r (F.comp P.innerBoundary) =
      ∑ x, P.boundaryCoefficient x • sphereThirdObstruction r (F.comp (P.linkingSphere x)) := by
    have he := congrArg (fun a ↦ stableThirdHomologyEquivZModTwo r (singularHomologyMap F 3 a))
      (P.outer_sub_inner_eq_sum_linkingSpheres sphereThirdClass)
    simpa only [sphereThirdObstruction_eq_homology, singularHomologyMap_comp,
      LinearMap.comp_apply, map_sub, map_sum, map_zsmul] using he
  rw [h]
  apply Finset.sum_congr rfl
  intro x _
  rcases P.boundaryCoefficient_eq_one_or_neg_one x with hx | hx
  · rw [hx, one_zsmul]
  · rw [hx, neg_one_zsmul, ZMod.neg_eq_self_mod_two]

theorem outer_frame_obstruction_eq_inner_of_even_links (r : ℕ)
    (F : C(P.puncturedAnnulus, Space (3 + (r + 2)) (r + 2)))
    (heven : Even (singularSet g).ncard)
    (hlinks : ∀ x : singularSet g, sphereThirdObstruction r (F.comp (P.linkingSphere x)) = 1) :
    sphereThirdObstruction r (F.comp P.outerBoundary) =
      sphereThirdObstruction r (F.comp P.innerBoundary) := by
  let := P.finite_singular.to_subtype
  let := Fintype.ofFinite (singularSet g)
  have hcard : (Fintype.card (singularSet g) : ZMod 2) = 0 := by
    apply ZMod.natCast_eq_zero_iff_even.mpr
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    exact heven
  apply sub_eq_zero.mp
  have h := P.outer_sub_inner_frame_obstruction_eq_sum r F
  simpa only [hlinks, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard] using h

theorem outer_frame_homotopic_inner_of_even_links (r : ℕ)
    (F : C(P.puncturedAnnulus, Space (3 + (r + 2)) (r + 2)))
    (heven : Even (singularSet g).ncard)
    (hlinks : ∀ x : singularSet g, sphereThirdObstruction r (F.comp (P.linkingSphere x)) = 1) :
    (F.comp P.outerBoundary).Homotopic (F.comp P.innerBoundary) :=
  (sphereThirdObstruction_eq_iff_homotopic r _ _).mp
    (P.outer_frame_obstruction_eq_inner_of_even_links r F heven hlinks)

end NoExoticSixSphere.GenericFourAnnulus.ParityBallSystem
