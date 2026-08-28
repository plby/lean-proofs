import Wikipedia.HopfProblem.ThreefoldHomologyFourthWangSource
import Wikipedia.HopfProblem.ThreefoldHomologyFifthKernel
import Wikipedia.HopfProblem.ThreefoldHomologyEllipticFibreKernel
import Wikipedia.HopfProblem.ThreefoldHomologyCuspFourthKernel

/-!
# A single actual Wang coordinate detects fifth homology

The original source columns force the three Wang values of a fourth
attachment relation to agree in the common integral `uwδ` direction.
The original cap maps together with their Wang maps jointly detect each
boundary class.  Consequently the actual fifth homology injects into
the integers through its cusp Wang coordinate.

This preserves the actual connecting homomorphism.  It does not assert
that the remaining integer coordinate is zero: that still requires the
full regular-fibre attachment calculation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthWang

open SingularMayerVietoris ThreefoldOverlapMappingTorus TrianglePeriodFamily

/-- All three actual Wang classes of a zero regular image have the same
original `uwδ` coordinate. -/
theorem overlap_wang_coordinates (a : StarOverlapHomology 4)
    (ha : starOverlapToRegularHomologyMap 4 a = 0) (i : Puncture) :
    FlatTorus.singularH3Coordinates (overlapWangHomologyMap i 3 (a i)) =
      Pi.single 3 (FlatTorus.singularH3Coordinates (overlapWangHomologyMap none 3 (a none)) 3) := by
  have h := wang_cancellation 3 a ha
  have hc := (commonThirdInvariant_iff (overlapWangHomologyMap none 3 (a none))).mp
    ⟨h.2.2.1, h.2.2.2⟩
  cases i with
  | none => exact hc
  | some j =>
    cases j with
    | three => rw [h.1]; exact hc
    | four => rw [h.2.1]; exact hc

/-- The actual fifth-degree coordinate is the cusp component of the original
connecting map, followed by its genuine Wang map and original ordered torus coordinate. -/
def fifthWangCoordinate : SingularHomology Space 5 →ₗ[ℤ] ℤ :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun := fun a => FlatTorus.singularH3Coordinates
        (overlapWangHomologyMap none 3 (starConnectingHomomorphism 4 a none)) 3
      map_zero' := by simp only [map_zero, Pi.zero_apply]
      map_add' := by intro a b; simp only [map_add, Pi.add_apply] }

@[simp] theorem fifthWangCoordinate_apply (a : SingularHomology Space 5) :
    fifthWangCoordinate a = FlatTorus.singularH3Coordinates
      (overlapWangHomologyMap none 3 (starConnectingHomomorphism 4 a none)) 3 := rfl

theorem connecting_four_regular_zero (a : SingularHomology Space 5) :
    starOverlapToRegularHomologyMap 4 (starConnectingHomomorphism 4 a) = 0 :=
  congrArg Prod.fst ((star_exact_at_intersection 4).apply_apply_eq_zero a)

theorem connecting_four_cap_zero (a : SingularHomology Space 5) (i : Puncture) :
    singularHomologyMap (overlapToFilling i) 4 (starConnectingHomomorphism 4 a i) = 0 := by
  have h := congrFun (congrArg Prod.snd
    ((star_exact_at_intersection 4).apply_apply_eq_zero a)) i
  exact neg_eq_zero.mp h

/-- The single integer gives all three literal Wang values of an actual fifth class. -/
theorem fifthWangCoordinate_coordinates (a : SingularHomology Space 5) (i : Puncture) :
    FlatTorus.singularH3Coordinates
        (overlapWangHomologyMap i 3 (starConnectingHomomorphism 4 a i)) =
      Pi.single 3 (fifthWangCoordinate a) :=
  overlap_wang_coordinates (starConnectingHomomorphism 4 a) (connecting_four_regular_zero a) i

/-- Vanishing of that actual integer forces the original fifth homology class to vanish. -/
theorem fifthWangCoordinate_eq_zero (a : SingularHomology Space 5)
    (ha : fifthWangCoordinate a = 0) : a = 0 := by
  have hw (i : Puncture) :
      overlapWangHomologyMap i 3 (starConnectingHomomorphism 4 a i) = 0 := by
    apply FlatTorus.singularH3Coordinates.injective
    rw [fifthWangCoordinate_coordinates, ha, map_zero]
    simp
  have hd : starConnectingHomomorphism 4 a = 0 := by
    funext i
    cases i with
    | none =>
      apply (overlapHomologyEquiv none 4).injective
      rw [Pi.zero_apply, map_zero]
      apply ThreefoldHomologyCuspFibre.cuspCap_wang_four_eq_zero
      · have h := LinearMap.congr_fun (boundaryFillingHomologyMap_retraction none 4)
          (starConnectingHomomorphism 4 a none)
        change boundaryFillingHomologyMap none 4
            (overlapHomologyEquiv none 4 (starConnectingHomomorphism 4 a none)) =
          singularHomologyMap (overlapToFilling none) 4
            (starConnectingHomomorphism 4 a none) at h
        exact h.trans (connecting_four_cap_zero a none)
      · exact hw none
    | some j =>
      exact EllipticFibre.overlapFilling_wang_eq_zero j 3 _
        (connecting_four_cap_zero a (some j)) (hw (some j))
  apply FifthDegree.connecting_four_injective
  rw [hd, map_zero]

/-- Fifth integral homology injects into one integer coordinate by an actual geometric map. -/
theorem fifthWangCoordinate_injective : Function.Injective fifthWangCoordinate := by
  intro a b hab
  apply sub_eq_zero.mp
  apply fifthWangCoordinate_eq_zero
  rw [map_sub, hab, sub_self]

/-- The image is retained as its actual subgroup of the integers, not assigned a rank in advance. -/
def homologyFiveWangRangeEquiv :
    SingularHomology Space 5 ≃ₗ[ℤ] LinearMap.range fifthWangCoordinate :=
  LinearEquiv.ofInjective fifthWangCoordinate fifthWangCoordinate_injective

@[simp] theorem homologyFiveWangRangeEquiv_val (a : SingularHomology Space 5) :
    (homologyFiveWangRangeEquiv a).val = fifthWangCoordinate a := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthWang
