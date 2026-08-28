import Wikipedia.NoExoticSixSphere.RelativeNormalizedFiberProjection
import Wikipedia.NoExoticSixSphere.RelativeFiberClassNaturality

/-!
# Naturality of the actual descended relative-to-fiber homology map

The raw-simplex formula removes any need for choices of normalization
to commute. Actual normalized relative simplex classes generate the
source homology; on those generators naturality is the literal cone-path
map followed by the original relative homology map.
-/

noncomputable section

open Set
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.RelativeNormalizedFiberClasses

open RelativeSingularHomology RelativeSimplexCycles

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
  (U : Set X) [SimplyConnectedSpace U] (V : Set Y) [SimplyConnectedSpace V]
  (a : U) (b : V)
  (hπU : Function.Surjective
    (HigherHomotopy.map (N := Fin 2) (subtypeInclusion U) (y := a) rfl))
  (hπV : Function.Surjective
    (HigherHomotopy.map (N := Fin 2) (subtypeInclusion V) (y := b) rfl))
  (f : C(X, Y)) (hf : Set.MapsTo f U V) (hab : f a.val = b.val)

theorem homologyMap_naturality :
    (homologyMap V b hπV).comp (RelativeSingularHomology.map f hf 3) =
      (singularHomologyMap (RelativeFiberMap.map f hf a b hab) 2).comp
        (homologyMap U a hπU) := by
  let L := (homologyMap V b hπV).comp (RelativeSingularHomology.map f hf 3)
  let R := (singularHomologyMap (RelativeFiberMap.map f hf a b hab) 2).comp
    (homologyMap U a hπU)
  have he : L.comp (RelativeNormalizedThreeHomology.classOperator U a hπU) =
      R.comp (RelativeNormalizedThreeHomology.classOperator U a hπU) := by
    apply chainMap_ext X 3
    intro smp
    let τ := RelativeNormalizedThreeHomology.relativeSimplex U a hπU smp
    have hτ : τ.val (stdSimplex.vertex (S := ℝ) (0 : Fin 4)) = a.val :=
      RelativeTwoSkeletonNormalization.endpoint_verticesBased U a hπU 3 smp 0
    have hraw : homologyMap V b hπV (RelativeSingularHomology.map f hf 3 (homologyClass U 2 τ)) =
        singularHomologyMap (RelativeFiberMap.map f hf a b hab) 2
          (homologyMap U a hπU (homologyClass U 2 τ)) := by
      rw [map_homologyClass,
        homologyMap_simplex_eq_fiberClass V b hπV (mapSimplex f hf 3 τ)
          ((congrArg f hτ).trans hab),
        homologyMap_simplex_eq_fiberClass U a hπU τ hτ]
      exact (RelativeFiberMap.fiberClass_natural f hf a b hab 0 τ hτ).symm
    have hE := RelativeNormalizedThreeHomology.classOperator_simplex U a hπU smp
    exact (congrArg L hE).trans (hraw.trans (congrArg R hE.symm))
  apply LinearMap.ext
  intro z
  obtain ⟨c, rfl⟩ := RelativeNormalizedThreeHomology.classOperator_surjective U a hπU z
  exact LinearMap.congr_fun he c

end NoExoticSixSphere.RelativeNormalizedFiberClasses
