import Wikipedia.NoExoticSixSphere.CommonSmallCapConnecting
import Wikipedia.HopfProblem.SingularMayerVietorisSequenceTransport
import Wikipedia.HopfProblem.SingularMayerVietorisSequenceRightTransport

/-!
# Exactness for the original mod-two Mayer--Vietoris maps

The first and second maps are the signed intersection inclusions and
the sum of the original ambient inclusions. The native small-chain
short exact sequence and its actual subdivision comparison prove all
three range-kernel identities, retaining the original connecting map.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.ModTwoMayerVietoris

variable {X : Type} [TopologicalSpace X] (U V : Set X)

def firstMap (n : ℕ) : ModHomology 2 (U ∩ V : Set X) n →ₗ[ℤ]
    (ModHomology 2 U n × ModHomology 2 V n) :=
  biprodSequenceFirstMap (smallSequence U V).f n

def secondMap (n : ℕ) : (ModHomology 2 U n × ModHomology 2 V n) →ₗ[ℤ] ModHomology 2 X n :=
  biprodSequenceSecondMap (biprod.desc (RelativeCoefficients.inclusion Coefficient U)
    (RelativeCoefficients.inclusion Coefficient V)) n

/-- The original first map has the two original intersection maps with signs `(+,-)`. -/
theorem firstMap_apply (n : ℕ) (a : ModHomology 2 (U ∩ V : Set X) n) :
    firstMap U V n a =
      (modHomologyMap 2 (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n a,
        -modHomologyMap 2 (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)) n a) :=
  biprodSequenceFirstMap_lift_neg _ _ n a

/-- The original second map is the sum of the original two ambient inclusions. -/
theorem secondMap_apply (n : ℕ) (a : ModHomology 2 U n × ModHomology 2 V n) :
    secondMap U V n a = modHomologyMap 2 (subtypeInclusion U) n a.1 +
      modHomologyMap 2 (subtypeInclusion V) n a.2 :=
  biprodSequenceSecondMap_desc _ _ n a

theorem secondMap_eq_comparison (n : ℕ) :
    secondMap U V n = (homologyLinearMap (smallInclusion U V) n).comp
      (biprodSequenceSecondMap (smallSequence U V).g n) := by
  apply LinearMap.ext
  intro a
  let b := (homologyBiprodEquiv (modComplex 2 U) (modComplex 2 V) n).symm a
  exact (congrArg (fun f => homologyLinearMap f n b) (second_inclusion U V)).symm.trans
    (LinearMap.congr_fun (homologyLinearMap_comp (smallSequence U V).g (smallInclusion U V) n) b)

variable (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

theorem secondMap_eq_transport (n : ℕ) :
    secondMap U V n = (smallEquiv U V hU hV hcover n).toLinearMap.comp
      (biprodSequenceSecondMap (smallSequence U V).g n) := secondMap_eq_comparison U V n

include hU hV hcover

/-- Exactness at the actual overlap homology. -/
theorem exact_left (n : ℕ) :
    LinearMap.range (connecting U V hU hV hcover n) = LinearMap.ker (firstMap U V n) := by
  exact (rightTransport_connecting_range (smallEquiv U V hU hV hcover (n + 1))
    (connectingMap (smallSequence_shortExact U V) n)).trans
      (biprodSequence_exact_at_leftHomology (smallSequence_shortExact U V) n)

/-- Exactness at the product of the actual two subspace homology groups. -/
theorem exact_middle (n : ℕ) :
    LinearMap.range (firstMap U V n) = LinearMap.ker (secondMap U V n) := by
  exact (biprodSequence_exact_at_middleHomology (smallSequence_shortExact U V) n).trans
    ((rightTransport_second_ker (smallEquiv U V hU hV hcover n)
      (biprodSequenceSecondMap (smallSequence U V).g n)).symm.trans
        (congrArg LinearMap.ker (secondMap_eq_transport U V hU hV hcover n)).symm)

/-- Exactness at actual positive-degree ambient homology. -/
theorem exact_right (n : ℕ) :
    LinearMap.range (secondMap U V (n + 1)) =
      LinearMap.ker (connecting U V hU hV hcover n) := by
  exact (congrArg LinearMap.range (secondMap_eq_transport U V hU hV hcover (n + 1))).trans
    (rightTransport_range_eq_ker (smallEquiv U V hU hV hcover (n + 1)) _ _
      (biprodSequence_exact_at_rightHomology (smallSequence_shortExact U V) n))

/-- The original degree-zero endpoint is surjective. -/
theorem secondMap_zero_surjective : Function.Surjective (secondMap U V 0) := by
  exact (secondMap_eq_transport U V hU hV hcover 0).symm ▸
    rightTransport_second_surjective (smallEquiv U V hU hV hcover 0) _
      (biprodSequence_second_zero_surjective (smallSequence_shortExact U V))

end NoExoticSixSphere.ModTwoMayerVietoris
