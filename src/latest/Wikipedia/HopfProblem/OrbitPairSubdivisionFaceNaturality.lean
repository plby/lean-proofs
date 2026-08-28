import Wikipedia.HopfProblem.OrbitPairSubdivisionBarycentreNaturality

/-!
# Face compatibility of the native subdivision homeomorphisms

The barycentre identity is extended over each nerve simplex by affine
interpolation. It therefore gives exact naturality on native realizations
for every injective simplex map, and hence along all simplex faces.
-/

noncomputable section

universe u

open CategoryTheory Simplicial PartialOrder

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

open FirstHurewicz RealizationSimplex AffineCoordinates

theorem barycentricMap_naturality {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) [Mono f] :
    (barycentricMap.{u} n).comp (SSet.toTop.map (SimplexCategory.sd.map f)).hom =
      (SimplexCategory.toTop₀.map f).hom.comp (barycentricMap m) := by
  apply continuousMap_ext_characteristic
  intro k x t
  have hl := nerveInterpolation_characteristic
    (NonemptyFiniteChains (ULift.{u} (Fin (n + 1)))) (chainBarycentre n) k
    ((SimplexCategory.sd.map f).app (Opposite.op ⦋k⦌) x) t
  have hr := nerveInterpolation_characteristic
    (NonemptyFiniteChains (ULift.{u} (Fin (m + 1)))) (chainBarycentre m) k x t
  change barycentricMap n ((SSet.toTop.map (SimplexCategory.sd.map f))
    (characteristic (SimplexCategory.sd.obj ⦋m⦌) k x t)) =
      stdSimplex.map f.toOrderHom (barycentricMap m
        (characteristic (SimplexCategory.sd.obj ⦋m⦌) k x t))
  refine ((congrArg (barycentricMap n)
    (realizedMap_characteristic (SimplexCategory.sd.map f) k x t)).trans hl).trans ?_
  have hv :
      (fun i : Fin (k + 1) ↦ chainBarycentre n
        ((x.obj i).map (SimplexCategory.toPartOrd.{u}.map f).hom)) =
      (fun i ↦ stdSimplex.map f.toOrderHom (chainBarycentre m (x.obj i))) :=
    funext (fun i ↦ chainBarycentre_map f (x.obj i))
  exact (congrArg (fun a ↦ weighted a t) hv).trans
    ((simplex_map_weighted f.toOrderHom (fun i ↦ chainBarycentre m (x.obj i)) t).symm.trans
      (congrArg (stdSimplex.map f.toOrderHom) hr.symm))

theorem barycentricHomeomorph_naturality {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) [Mono f]
    (z : SSet.toTop.obj (SimplexCategory.sd.{u}.obj ⦋m⦌)) :
    barycentricHomeomorph n ((SSet.toTop.map (SimplexCategory.sd.map f)) z) =
      stdSimplex.map f.toOrderHom (barycentricHomeomorph m z) :=
  congrArg (fun g : C(SSet.toTop.obj (SimplexCategory.sd.{u}.obj ⦋m⦌), Simplex n) ↦ g z)
    (barycentricMap_naturality f)

theorem stdSimplexSubdivisionHomeomorph_naturality {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌) [Mono f]
    (z : SSet.toTop.obj (SSet.sd.obj (SSet.stdSimplex.{u}.obj ⦋m⦌))) :
    stdSimplexSubdivisionHomeomorph n ((SSet.toTop.map (SSet.sd.map (SSet.stdSimplex.map f))) z) =
      stdSimplex.map f.toOrderHom (stdSimplexSubdivisionHomeomorph m z) := by
  have h := congrArg
    (fun g : SSet.sd.obj (SSet.stdSimplex.{u}.obj ⦋m⦌) ⟶ SimplexCategory.sd.obj ⦋n⦌ ↦
      (SSet.toTop.map g) z) (SSet.stdSimplex.sdIso.hom.naturality f)
  simp only [Functor.map_comp, CategoryTheory.comp_apply] at h
  exact (congrArg (barycentricHomeomorph n) h).trans
    (barycentricHomeomorph_naturality f
      ((SSet.toTop.map (SSet.stdSimplex.sdIso.hom.app ⦋m⦌)) z))

end Wikipedia.HopfProblem.OrbitPair.Subdivision
