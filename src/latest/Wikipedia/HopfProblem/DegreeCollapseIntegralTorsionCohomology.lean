import Wikipedia.HopfProblem.DegreeCollapseIntegralTorsionCocycles

/-!
# Torsion evaluation on the original integral cohomology

An actual integral coboundary has its original integral cochain as a
rational primitive. Primitive independence makes its residue character
zero. Descend through the original cohomology-class map, retaining the
original cocycle, cycle and bounding-chain formulas.
-/

noncomputable section

open CategoryTheory Function

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation

open SingularCohomologyFree SingularMayerVietoris.ModuleHomology

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
  [Finite (K.homology n)] [Subsingleton (K.homology (n + 1))]

theorem cocycleCharacters_coboundary (β : K.X n →ₗ[ℤ] ℤ) :
    cocycleCharacters K n (coboundaryCocycle (dualComplex K) (n + 1) β) = 0 := by
  ext a
  obtain ⟨z, rfl⟩ := cycleClass_surjective K n a
  rw [cocycleCharacters_cycle]
  have he := rational_eq_on_cycles_of_same_boundary K n
    (rationalPrimitive K n (coboundaryCocycle (dualComplex K) (n + 1) β))
    (RationalResidue.integralCast.comp β)
    ((rationalPrimitive_spec K n (coboundaryCocycle (dualComplex K) (n + 1) β)).trans rfl) z
  exact (congrArg RationalResidue.residue he).trans (RationalResidue.residue_intCast (β z.val))

theorem cocycleCharacters_classKernel :
    LinearMap.ker (cocycleClass (dualComplex K) (n + 1)) ≤
      LinearMap.ker (cocycleCharacters K n) := by
  intro c hc
  obtain ⟨β, hβ⟩ := (cocycleClass_eq_zero_iff (dualComplex K) (n + 1) c).mp hc
  have he : coboundaryCocycle (dualComplex K) (n + 1) β = c := Subtype.ext hβ
  exact (congrArg (cocycleCharacters K n) he).symm.trans (cocycleCharacters_coboundary K n β)

def torsionEvaluation :
    Cohomology K (n + 1) →ₗ[ℤ] (K.homology n →ₗ[ℤ] RationalResidue.Value) :=
  descendLinear (cocycleClass (dualComplex K) (n + 1))
    (cocycleClass_surjective (dualComplex K) (n + 1))
    (cocycleCharacters K n) (cocycleCharacters_classKernel K n)

theorem torsionEvaluation_cocycleClass (c : Cocycle (dualComplex K) (n + 1)) :
    torsionEvaluation K n (cocycleClass (dualComplex K) (n + 1) c) =
      cocycleCharacters K n c :=
  descendLinear_apply _ _ _ _ _

theorem torsionEvaluation_cocycle_cycle (c : Cocycle (dualComplex K) (n + 1))
    (z : Cycle K n) :
    torsionEvaluation K n (cocycleClass (dualComplex K) (n + 1) c) (cycleClass K n z) =
      RationalResidue.residue (rationalPrimitive K n c z.val) := by
  rw [torsionEvaluation_cocycleClass, cocycleCharacters_cycle]

theorem torsionEvaluation_bounding_formula (c : Cocycle (dualComplex K) (n + 1))
    (z : Cycle K n) (l : ℤ) (hl : l ≠ 0) (b : K.X (n + 1))
    (hb : (K.d (n + 1) n).hom b = l • z.val) :
    torsionEvaluation K n (cocycleClass (dualComplex K) (n + 1) c) (cycleClass K n z) =
      RationalResidue.residue ((c.val b : ℚ) / (l : ℚ)) := by
  rw [torsionEvaluation_cocycle_cycle, rationalPrimitive_bounding_formula K n c z l hl b hb]

end Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation
