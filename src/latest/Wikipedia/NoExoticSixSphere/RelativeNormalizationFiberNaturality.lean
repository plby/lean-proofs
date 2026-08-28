import Wikipedia.NoExoticSixSphere.RelativeNormalizationFiberDescent
import Wikipedia.NoExoticSixSphere.RelativeSimplexConnecting
import Wikipedia.NoExoticSixSphere.RelativeFiberClassNaturality

/-!
# Naturality and the original connecting map in every normalized degree

The raw-simplex formula proves both identities on actual normalized
relative simplex generators. It removes any need for independently
chosen normalization families to commute with a map of pairs.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.RelativeNormalization.Data

open RelativeSingularHomology RelativeSimplexCycles

variable {X : Type} [TopologicalSpace X] {U : Set X} {a : U} {n : ℕ} (D : Data U a n)

theorem projection_fiberHomologyMap :
    (singularHomologyMap (HomotopyFiber.projection (subtypeInclusion U) a.val) (n + 2)).comp
      D.fiberHomologyMap = connecting U (n + 2) := by
  have he : ((singularHomologyMap
      (HomotopyFiber.projection (subtypeInclusion U) a.val) (n + 2)).comp
        D.fiberHomologyMap).comp D.relativeClassOperator =
      (connecting U (n + 2)).comp D.relativeClassOperator := by
    apply chainMap_ext X (n + 3)
    intro smp
    simp only [LinearMap.comp_apply, relativeClassOperator_simplex]
    rw [D.fiberHomologyMap_simplex_eq_fiberClass (D.relativeSimplex smp)
      (D.vertices (n + 3) smp 0)]
    exact RelativeSimplexConnecting.projection_fiberClass U a n (D.relativeSimplex smp)
      (D.vertices (n + 3) smp 0)
  apply LinearMap.ext
  intro z
  obtain ⟨c, rfl⟩ := D.relativeClassOperator_surjective z
  exact LinearMap.congr_fun he c

variable {Y : Type} [TopologicalSpace Y] {V : Set Y} {b : V} (E : Data V b n)
  (f : C(X, Y)) (hf : Set.MapsTo f U V) (hab : f a.val = b.val)

theorem fiberHomologyMap_naturality :
    E.fiberHomologyMap.comp (RelativeSingularHomology.map f hf (n + 3)) =
      (singularHomologyMap (RelativeFiberMap.map f hf a b hab) (n + 2)).comp
        D.fiberHomologyMap := by
  let L := E.fiberHomologyMap.comp (RelativeSingularHomology.map f hf (n + 3))
  let R := (singularHomologyMap (RelativeFiberMap.map f hf a b hab) (n + 2)).comp D.fiberHomologyMap
  have he : L.comp D.relativeClassOperator = R.comp D.relativeClassOperator := by
    apply chainMap_ext X (n + 3)
    intro smp
    let τ := D.relativeSimplex smp
    have hτ : τ.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4))) = a.val :=
      D.vertices (n + 3) smp 0
    have hraw : E.fiberHomologyMap
        (RelativeSingularHomology.map f hf (n + 3) (homologyClass U (n + 2) τ)) =
      singularHomologyMap (RelativeFiberMap.map f hf a b hab) (n + 2)
        (D.fiberHomologyMap (homologyClass U (n + 2) τ)) := by
      rw [map_homologyClass,
        E.fiberHomologyMap_simplex_eq_fiberClass (mapSimplex f hf (n + 3) τ)
          ((congrArg f hτ).trans hab),
        D.fiberHomologyMap_simplex_eq_fiberClass τ hτ]
      exact (RelativeFiberMap.fiberClass_natural f hf a b hab n τ hτ).symm
    have hE := D.relativeClassOperator_simplex smp
    exact (congrArg L hE).trans (hraw.trans (congrArg R hE.symm))
  apply LinearMap.ext
  intro z
  obtain ⟨c, rfl⟩ := D.relativeClassOperator_surjective z
  exact LinearMap.congr_fun he c

end NoExoticSixSphere.RelativeNormalization.Data
