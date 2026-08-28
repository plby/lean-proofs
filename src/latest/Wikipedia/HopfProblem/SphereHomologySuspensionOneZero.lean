import Wikipedia.HopfProblem.SingularMayerVietoris
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePointClass

/-!
# The actual degree-zero Mayer--Vietoris map for a connected overlap

Every continuous map between path-connected spaces induces the identity
in the actual augmentation markings of degree-zero singular homology.
Consequently that induced map is bijective. The first component of the
actual Mayer--Vietoris overlap map is therefore injective when the
overlap and first subset are path-connected. When both subsets are
path-connected its two augmentation coordinates are exactly `(a,-a)`.
-/

noncomputable section

open scoped ContinuousMap

namespace Wikipedia.HopfProblem.SphereHomology

open SingularMayerVietoris PeriodTorusHigherHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual degree-zero map of any continuous map between path-connected spaces is injective. -/
theorem singularHomologyMap_zero_injective [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : C(X, Y)) : Function.Injective (singularHomologyMap f 0) := by
  intro a b h
  apply (connectedHomologyZeroEquiv X).injective
  simpa only [connectedHomologyZeroEquiv_natural] using
    congrArg (connectedHomologyZeroEquiv Y) h

/-- The actual degree-zero map is also surjective, with preimages determined by augmentation. -/
theorem singularHomologyMap_zero_surjective [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : C(X, Y)) : Function.Surjective (singularHomologyMap f 0) := by
  intro b
  refine ⟨(connectedHomologyZeroEquiv X).symm (connectedHomologyZeroEquiv Y b), ?_⟩
  apply (connectedHomologyZeroEquiv Y).injective
  rw [connectedHomologyZeroEquiv_natural, LinearEquiv.apply_symm_apply]

/-- Bijectivity concerns the actual induced map, not merely abstract isomorphic groups. -/
theorem singularHomologyMap_zero_bijective [PathConnectedSpace X] [PathConnectedSpace Y]
    (f : C(X, Y)) : Function.Bijective (singularHomologyMap f 0) :=
  ⟨singularHomologyMap_zero_injective f, singularHomologyMap_zero_surjective f⟩

/-- The actual overlap map is injective if its overlap and first subset are path-connected. -/
theorem leftHomologyMap_zero_injective (U V : Set X)
    [PathConnectedSpace (U ∩ V : Set X)] [PathConnectedSpace U] :
    Function.Injective (leftHomologyMap U V 0) := by
  intro a b h
  apply singularHomologyMap_zero_injective
    (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U))
  simpa only [leftHomologyMap_apply] using congrArg Prod.fst h

/-- Its actual linear kernel is zero, without any first-homology hypothesis. -/
theorem leftHomologyMap_zero_ker (U V : Set X)
    [PathConnectedSpace (U ∩ V : Set X)] [PathConnectedSpace U] :
    LinearMap.ker (leftHomologyMap U V 0) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (leftHomologyMap_zero_injective U V)

/-- The two actual augmentation coordinates retain the Mayer--Vietoris difference sign. -/
theorem leftHomologyMap_zero_coordinates (U V : Set X)
    [PathConnectedSpace (U ∩ V : Set X)] [PathConnectedSpace U] [PathConnectedSpace V]
    (a : SingularHomology (U ∩ V : Set X) 0) :
    (connectedHomologyZeroEquiv U (leftHomologyMap U V 0 a).1,
        connectedHomologyZeroEquiv V (leftHomologyMap U V 0 a).2) =
      (connectedHomologyZeroEquiv (U ∩ V : Set X) a,
        -connectedHomologyZeroEquiv (U ∩ V : Set X) a) := by
  rw [leftHomologyMap_apply]
  simp only [map_neg, connectedHomologyZeroEquiv_natural]

end Wikipedia.HopfProblem.SphereHomology
