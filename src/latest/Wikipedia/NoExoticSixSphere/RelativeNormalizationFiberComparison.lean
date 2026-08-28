import Wikipedia.NoExoticSixSphere.RelativeNormalizationTransgression

/-!
# Actual fiber homology comparison from normalized relative homology

The original transgression detects injectivity, and the constructed
normalized relative-to-fiber maps supply surjectivity. Their proved
naturality keeps the original continuous fiber map throughout. The
normalization data are explicit inputs, not an excision assumption.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.RelativeNormalization

open RelativeFiberHomology EndingPathPair

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {U : Set X} {V : Set Y} {a : U} {b : V} {n : ℕ}
  (D : Data U a n) (D' : Data (subspace U a) (EndingPathPair.basepoint U a) n)
  (E : Data V b n) (E' : Data (subspace V b) (EndingPathPair.basepoint V b) n)
  (f : C(X, Y)) (hf : Set.MapsTo f U V) (hab : f a.val = b.val)

include D D' in
theorem fiber_homology_injective
    (hi : Function.Injective (RelativeSingularHomology.map f hf (n + 3))) :
    Function.Injective (singularHomologyMap (RelativeFiberMap.map f hf a b hab) (n + 2)) := by
  intro x y hxy
  apply D.transgression_injective D'
  apply hi
  rw [transgression_natural f hf a b hab, transgression_natural f hf a b hab, hxy]

include D E E' in
theorem fiber_homology_surjective
    (hs : Function.Surjective (RelativeSingularHomology.map f hf (n + 3))) :
    Function.Surjective (singularHomologyMap (RelativeFiberMap.map f hf a b hab) (n + 2)) := by
  intro z
  obtain ⟨c, hc⟩ := E.fiberHomologyMap_surjective E' z
  obtain ⟨r, hr⟩ := hs c
  refine ⟨D.fiberHomologyMap r, ?_⟩
  have he := LinearMap.congr_fun (D.fiberHomologyMap_naturality E f hf hab) r
  change E.fiberHomologyMap (RelativeSingularHomology.map f hf (n + 3) r) =
    singularHomologyMap (RelativeFiberMap.map f hf a b hab) (n + 2) (D.fiberHomologyMap r) at he
  exact he.symm.trans ((congrArg E.fiberHomologyMap hr).trans hc)

include D D' E E' in
theorem fiber_homology_bijective
    (hb : Function.Bijective (RelativeSingularHomology.map f hf (n + 3))) :
    Function.Bijective (singularHomologyMap (RelativeFiberMap.map f hf a b hab) (n + 2)) :=
  ⟨fiber_homology_injective D D' f hf hab hb.injective,
    fiber_homology_surjective D E E' f hf hab hb.surjective⟩

end NoExoticSixSphere.RelativeNormalization
