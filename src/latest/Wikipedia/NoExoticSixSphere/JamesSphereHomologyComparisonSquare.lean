import Wikipedia.NoExoticSixSphere.JamesSphereWordHomology
import Wikipedia.NoExoticSixSphere.JamesSphereLoopHomology
import Wikipedia.NoExoticSixSphere.JamesSphereActionHomotopy

/-!
# The actual James comparison commutes with both homology splittings

Projection commutes exactly and prepend commutes up to the constructed
generator-concatenation homotopy. Thus the proved word and loop homology
splittings conjugate the sphere-product comparison map to two copies of
the original comparison map. This identifies the maps; it does not yet
prove that the comparison induces isomorphisms.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.HomologyComparison

def productComparison (n : ℕ) : C(WordHomology.Parameter n, LoopParameter n) :=
  (ContinuousMap.id (Sphere n)).prodMap (loopComparison n)

theorem projection_map (n : ℕ) :
    (loopProjection n).comp (productComparison n) =
      (loopComparison n).comp (WordHomology.projection n) := rfl

theorem action_map (n : ℕ) :
    (generatorAction n).comp (productComparison n) = loopAction n := rfl

theorem projection_homology (n d : ℕ) (a : SingularHomology (WordHomology.Parameter n) d) :
    singularHomologyMap (loopProjection n) d (singularHomologyMap (productComparison n) d a) =
      singularHomologyMap (loopComparison n) d
        (singularHomologyMap (WordHomology.projection n) d a) := by
  have h := congrArg (fun q ↦ singularHomologyMap q d) (projection_map n)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  exact LinearMap.congr_fun h a

theorem action_homology (n d : ℕ) (a : SingularHomology (WordHomology.Parameter n) d) :
    singularHomologyMap (generatorAction n) d (singularHomologyMap (productComparison n) d a) =
      singularHomologyMap (loopComparison n) d
        (singularHomologyMap (WordHomology.action n) d a) := by
  have h := homotopy_homologyMap (actionHomotopy n) d
  rw [← action_map n, singularHomologyMap_comp, singularHomologyMap_comp] at h
  exact (LinearMap.congr_fun h a).symm

theorem splitting_square (n d : ℕ) (hd : d ≠ 0)
    (a : SingularHomology (WordHomology.Parameter n) d) :
    LoopHomology.projectionActionEquiv n d hd (singularHomologyMap (productComparison n) d a) =
      (singularHomologyMap (loopComparison n) d (WordHomology.projectionActionEquiv n d hd a).1,
        singularHomologyMap (loopComparison n) d
          (WordHomology.projectionActionEquiv n d hd a).2) := by
  rw [LoopHomology.projectionActionEquiv_apply, WordHomology.projectionActionEquiv_apply]
  exact Prod.ext (projection_homology n d a) (action_homology n d a)

theorem product_bijective_iff (n d : ℕ) (hd : d ≠ 0) :
    Function.Bijective (singularHomologyMap (productComparison n) d) ↔
      Function.Bijective (singularHomologyMap (loopComparison n) d) := by
  let W := WordHomology.projectionActionEquiv n d hd
  let L := LoopHomology.projectionActionEquiv n d hd
  let f := singularHomologyMap (productComparison n) d
  let g := singularHomologyMap (loopComparison n) d
  have hs : L ∘ f = (Prod.map g g) ∘ W := funext (splitting_square n d hd)
  have h₁ : Function.Bijective (L ∘ f) ↔ Function.Bijective f :=
    Function.Bijective.of_comp_iff' L.bijective f
  have h₂ : Function.Bijective ((Prod.map g g) ∘ W) ↔ Function.Bijective (Prod.map g g) :=
    Function.Bijective.of_comp_iff (Prod.map g g) W.bijective
  change Function.Bijective f ↔ Function.Bijective g
  rw [← h₁, hs, h₂, Prod.map_bijective, and_self]

end NoExoticSixSphere.JamesSphere.HomologyComparison
