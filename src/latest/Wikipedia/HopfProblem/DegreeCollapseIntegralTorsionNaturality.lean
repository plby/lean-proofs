import Wikipedia.HopfProblem.DegreeCollapseIntegralTorsionCohomology

/-!
# The original torsion evaluation is natural for actual chain maps

The original cochain pullback of a cocycle has the pullback rational
primitive as one possible primitive. Agreement on original cycles
identifies it with the constructed primitive. Descent retains the
actual homology map and the actual integral cohomology pullback.
-/

noncomputable section

open CategoryTheory Function

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation

open SingularCohomologyFree SingularMayerVietoris.ModuleHomology

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule

variable {K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : K ⟶ L) (n : ℕ)
  [Finite (K.homology n)] [Subsingleton (K.homology (n + 1))]
  [Subsingleton (L.homology (n + 1))]

theorem rationalPrimitive_chainMap_cycle (c : Cocycle (dualComplex L) (n + 1))
    (z : Cycle K n) :
    rationalPrimitive K n (mapCocycles (dualMap f) (n + 1) c) z.val =
      rationalPrimitive L n c ((f.f n).hom z.val) := by
  apply rational_eq_on_cycles_of_same_boundary K n
    (rationalPrimitive K n (mapCocycles (dualMap f) (n + 1) c))
    ((rationalPrimitive L n c).comp (f.f n).hom) ?_ z
  ext b
  have he : (f.f n).hom ((K.d (n + 1) n).hom b) =
      (L.d (n + 1) n).hom ((f.f (n + 1)).hom b) :=
    congrArg (fun g : K.X (n + 1) ⟶ L.X n ↦ g.hom b) (f.comm (n + 1) n).symm
  change rationalPrimitive K n (mapCocycles (dualMap f) (n + 1) c)
      ((K.d (n + 1) n).hom b) =
    rationalPrimitive L n c ((f.f n).hom ((K.d (n + 1) n).hom b))
  rw [rationalPrimitive_boundary, he, rationalPrimitive_boundary,
    mapCocycles_val, dualMap_f_apply]
  rfl

theorem torsionEvaluation_naturality [Finite (L.homology n)]
    (a : Cohomology L (n + 1)) (b : K.homology n) :
    torsionEvaluation K n ((HomologicalComplex.homologyMap (dualMap f) (n + 1)).hom a) b =
      torsionEvaluation L n a ((HomologicalComplex.homologyMap f n).hom b) := by
  obtain ⟨c, rfl⟩ := cocycleClass_surjective (dualComplex L) (n + 1) a
  obtain ⟨z, rfl⟩ := cycleClass_surjective K n b
  rw [homologyMap_cocycleClass, homologyMap_cycleClass,
    torsionEvaluation_cocycle_cycle, torsionEvaluation_cocycle_cycle, mapCycles_val]
  exact congrArg RationalResidue.residue (rationalPrimitive_chainMap_cycle f n c z)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation
