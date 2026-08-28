import Wikipedia.NoExoticSixSphere.RelativeSimplexMaps
import Wikipedia.NoExoticSixSphere.RelativeSimplexFiberClass

/-!
# The actual inclusion-fiber map of a based map of pairs

Map the source point by the restricted map and postcompose the original
path by the ambient map. The compact-open topology gives continuity.
Evaluation, source projection, and the existing simplex cone lift commute
with this literal map; whole-source paths remain whole-source paths.
-/

noncomputable section

open Set
open scoped unitInterval
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.RelativeFiberMap

open RelativeFiberHomology RelativeSimplexCycles

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {U : Set X} {V : Set Y} (f : C(X, Y)) (hf : Set.MapsTo f U V)
  (a : U) (b : V) (hab : f a.val = b.val)

def map : C(Fiber U a, Fiber V b) where
  toFun p := ⟨(RelativeSingularHomology.restrictedMap f hf p.val.1, f.comp p.val.2),
    congrArg f p.property.1, (congrArg f p.property.2).trans hab⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact (RelativeSingularHomology.restrictedMap f hf).continuous.comp
        (continuous_fst.comp continuous_subtype_val)
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun p : Fiber U a × I ↦ f (p.1.val.2 p.2))
      exact f.continuous.comp (continuous_eval.comp
        ((continuous_snd.comp (continuous_subtype_val.comp continuous_fst)).prodMk
          continuous_snd))

theorem map_path (p : Fiber U a) (t : I) : (map f hf a b hab p).val.2 t = f (p.val.2 t) := rfl

theorem projection_map :
    (HomotopyFiber.projection (subtypeInclusion V) b.val).comp (map f hf a b hab) =
      (RelativeSingularHomology.restrictedMap f hf).comp
        (HomotopyFiber.projection (subtypeInclusion U) a.val) := rfl

theorem map_subspace : Set.MapsTo (map f hf a b hab)
    (RelativeFiberSubspacePaths.subspace U a) (RelativeFiberSubspacePaths.subspace V b) :=
  fun _ hp t ↦ hf (hp t)

theorem map_liftedSimplex (n : ℕ) (smp : RelativeSimplex U (n + 1))
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 2))) = a.val) :
    (map f hf a b hab).comp (RelativeSimplexFiberClass.liftedSimplex U a n smp hv) =
      RelativeSimplexFiberClass.liftedSimplex V b n (mapSimplex f hf (n + 1) smp)
        ((congrArg f hv).trans hab) := rfl

end NoExoticSixSphere.RelativeFiberMap
