import Wikipedia.NoExoticSixSphere.RelativeFiberMap

/-!
# Naturality of the original cone-path fiber class

The actual fiber map commutes with the lifted simplex and carries
whole-source paths to whole-source paths. Naturality of the genuine
absolute-to-relative map then identifies the original absolute classes.
No compatibility of separately chosen normalizations is assumed.
-/

noncomputable section

open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.RelativeFiberMap

open RelativeFiberHomology RelativeSimplexCycles RelativeSingularHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {U : Set X} {V : Set Y} (f : C(X, Y)) (hf : Set.MapsTo f U V)
  (a : U) (b : V) (hab : f a.val = b.val)

theorem fiberClass_natural (n : ℕ) (smp : RelativeSimplex U (n + 3))
    (hv : smp.val (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 4))) = a.val) :
    singularHomologyMap (map f hf a b hab) (n + 2)
        (RelativeSimplexFiberClass.fiberClass U a n smp hv) =
      RelativeSimplexFiberClass.fiberClass V b n (mapSimplex f hf (n + 3) smp)
        ((congrArg f hv).trans hab) := by
  let F := map f hf a b hab
  have hF := map_subspace f hf a b hab
  have he : mapSimplex F hF (n + 2)
      (RelativeSimplexFiberClass.relativeSimplex U a (n + 2) smp hv) =
        RelativeSimplexFiberClass.relativeSimplex V b (n + 2)
          (mapSimplex f hf (n + 3) smp) ((congrArg f hv).trans hab) := by
    apply Subtype.ext
    exact map_liftedSimplex f hf a b hab (n + 2) smp hv
  apply (RelativeSimplexFiberClass.fiberHomologyEquiv V b n).injective
  change toRelative (RelativeFiberSubspacePaths.subspace V b) (n + 2) _ =
    toRelative (RelativeFiberSubspacePaths.subspace V b) (n + 2) _
  have hn := LinearMap.congr_fun (toRelative_naturality F hF (n + 2))
    (RelativeSimplexFiberClass.fiberClass U a n smp hv)
  change RelativeSingularHomology.map F hF (n + 2)
      (toRelative (RelativeFiberSubspacePaths.subspace U a) (n + 2)
        (RelativeSimplexFiberClass.fiberClass U a n smp hv)) =
    toRelative (RelativeFiberSubspacePaths.subspace V b) (n + 2)
      (singularHomologyMap F (n + 2) (RelativeSimplexFiberClass.fiberClass U a n smp hv)) at hn
  have h₁ := congrArg (RelativeSingularHomology.map F hF (n + 2))
    (RelativeSimplexFiberClass.fiberClass_toRelative U a n smp hv)
  have h₂ := map_homologyClass F hF (n + 1)
    (RelativeSimplexFiberClass.relativeSimplex U a (n + 2) smp hv)
  have h₃ := congrArg (homologyClass (RelativeFiberSubspacePaths.subspace V b) (n + 1)) he
  have h₄ := RelativeSimplexFiberClass.fiberClass_toRelative V b n
    (mapSimplex f hf (n + 3) smp) ((congrArg f hv).trans hab)
  exact hn.symm.trans (h₁.trans (h₂.trans (h₃.trans h₄.symm)))

end NoExoticSixSphere.RelativeFiberMap
