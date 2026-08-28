import Wikipedia.HopfProblem.DegreeCollapseIntegralTorsionCohomology
import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocalFree

/-!
# The original torsion evaluation detects integral cohomology classes

A zero residue character makes the rational primitive integer-valued on
the original cycles. Lift those values to integers and extend them along
the original cycle retraction. The resulting original integral cochain
has coboundary equal to the original cocycle. Only the outgoing boundary
image needs projectivity; free integral chains supply it.
-/

noncomputable section

open CategoryTheory Function

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation

open SingularCohomologyFree SingularCohomologyFree.LocalEvaluation
open SingularMayerVietoris.ModuleHomology

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
  [Finite (K.homology n)] [Subsingleton (K.homology (n + 1))]

theorem eq_zero_of_torsionEvaluation_eq_zero
    [Module.Projective ℤ (OutgoingImage K n)] (a : Cohomology K (n + 1))
    (ha : torsionEvaluation K n a = 0) : a = 0 := by
  obtain ⟨c, rfl⟩ := cocycleClass_surjective (dualComplex K) (n + 1) a
  let : Module ℤ (Cycle K n) := (Cycle K n).module
  have hz : ∀ z : Cycle K n,
      RationalResidue.residue (((rationalPrimitive K n c).comp (Cycle K n).subtype) z) = 0 := by
    intro z
    have he := LinearMap.congr_fun ha (cycleClass K n z)
    rw [torsionEvaluation_cocycle_cycle] at he
    exact he
  obtain ⟨β, hβ⟩ := RationalResidue.exists_integer_lift
    ((rationalPrimitive K n c).comp (Cycle K n).subtype) hz
  obtain ⟨ψ, hψ⟩ := exists_extension_from_cycles K n β
  have hc : ψ.comp (K.d (n + 1) n).hom = c.val := by
    ext b
    apply RationalResidue.integralCast_injective
    calc
      RationalResidue.integralCast (ψ ((K.d (n + 1) n).hom b)) =
          RationalResidue.integralCast (β (boundaryCycle K n b)) :=
        congrArg RationalResidue.integralCast (hψ (boundaryCycle K n b))
      _ = rationalPrimitive K n c ((K.d (n + 1) n).hom b) :=
        LinearMap.congr_fun hβ (boundaryCycle K n b)
      _ = RationalResidue.integralCast (c.val b) := rationalPrimitive_boundary K n c b
  exact (cocycleClass_eq_zero_iff (dualComplex K) (n + 1) c).mpr ⟨ψ, hc⟩

theorem torsionEvaluation_injective [Module.Projective ℤ (OutgoingImage K n)] :
    Injective (torsionEvaluation K n) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply eq_zero_of_torsionEvaluation_eq_zero K n (a - b)
  rw [map_sub, hab, sub_self]

theorem torsionEvaluation_injective_of_free [∀ j, Module.Free ℤ (K.X j)] :
    Injective (torsionEvaluation K n) := by
  let : Module.Projective ℤ (OutgoingImage K n) :=
    SingularCohomologyFreeEvaluation.submodule_projective_int
      (LinearMap.range (K.d n ((ComplexShape.down ℕ).next n)).hom)
  exact torsionEvaluation_injective K n

end Wikipedia.HopfProblem.DegreeCollapse.IntegralTorsionEvaluation
