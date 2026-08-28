import Wikipedia.HopfProblem.DegreeCollapseIntegralCupOneCycles
import Wikipedia.HopfProblem.DegreeCollapseIntegralTorsionDenominator
import Wikipedia.HopfProblem.DegreeCollapseIntegralTorsionSingular

/-!
# Torsion symmetry on actual capped seven-cycles

The original integral cocycles are capped with the same original
seven-cycle. The constructed common integer primitives and the signed
cup-one identity prove symmetry of their original torsion evaluations.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralSevenLinking

open FirstHurewicz SingularCohomologyFree SingularMayerVietoris SingularCohomologyCup
open IntegralTorsionEvaluation

variable {X : Type} [TopologicalSpace X]

def capSevenCycle (α : Cocycle (singularCochainComplex X) 4)
    (Ω : ModuleHomology.Cycle (singularComplex X) 7) :
    ModuleHomology.Cycle (singularComplex X) 3 :=
  ModuleHomology.mkCycle (singularComplex X) 3
    (IntegralCap.capInDegree (p := 4) (q := 3) rfl α.val Ω.val)
    (IntegralCap.cap_is_cycle_of_boundary_killed 4 2 α.val
      (cocycle_condition (singularCochainComplex X) 4 α) Ω.val
      (by rw [ModuleHomology.cycle_condition, map_zero]))

theorem capSevenCycle_val (α : Cocycle (singularCochainComplex X) 4)
    (Ω : ModuleHomology.Cycle (singularComplex X) 7) :
    (capSevenCycle α Ω).val = IntegralCap.capInDegree (p := 4) (q := 3) rfl α.val Ω.val := rfl

variable [Finite (SingularHomology X 3)] [Subsingleton (SingularHomology X 4)]

theorem torsionEvaluation_capSevenCycle (α β : Cocycle (singularCochainComplex X) 4)
    (u : Cochain X 3)
    (hu : coboundary u = Nat.card (SingularHomology X 3) • α.val)
    (Ω : ModuleHomology.Cycle (singularComplex X) 7) :
    singularTorsionEvaluation X 3 (cocycleClass (singularCochainComplex X) 4 α)
      (ModuleHomology.cycleClass (singularComplex X) 3 (capSevenCycle β Ω)) =
      RationalResidue.residue
        ((cup β.val u Ω.val : ℚ) / (Nat.card (SingularHomology X 3) : ℚ)) := by
  change torsionEvaluation (singularComplex X) 3 _ _ = _
  rw [torsionEvaluation_cardPrimitive_formula (singularComplex X) 3 α u hu]
  change RationalResidue.residue
    ((u (IntegralCap.capInDegree (p := 4) (q := 3) rfl β.val Ω.val) : ℚ) / _) = _
  rw [IntegralCap.evaluate_cap]
  rfl

theorem torsionEvaluation_capSevenCycle_symmetry
    (α β : Cocycle (singularCochainComplex X) 4)
    (Ω : ModuleHomology.Cycle (singularComplex X) 7) :
    singularTorsionEvaluation X 3 (cocycleClass (singularCochainComplex X) 4 α)
      (ModuleHomology.cycleClass (singularComplex X) 3 (capSevenCycle β Ω)) =
    singularTorsionEvaluation X 3 (cocycleClass (singularCochainComplex X) 4 β)
      (ModuleHomology.cycleClass (singularComplex X) 3 (capSevenCycle α Ω)) := by
  let (j : ℕ) : Module.Free ℤ ((singularComplex X).X j) := Module.Free.of_basis (chainBasis X j)
  obtain ⟨u, hu⟩ := exists_integer_cardPrimitive (singularComplex X) 3 α
  obtain ⟨v, hv⟩ := exists_integer_cardPrimitive (singularComplex X) 3 β
  change coboundary u = Nat.card (SingularHomology X 3) • α.val at hu
  change coboundary v = Nat.card (SingularHomology X 3) • β.val at hv
  rw [torsionEvaluation_capSevenCycle α β u hu Ω, torsionEvaluation_capSevenCycle β α v hv Ω]
  have hN : (Nat.card (SingularHomology X 3) : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hu' : coboundary u = (Nat.card (SingularHomology X 3) : ℤ) • α.val := by
    simpa only [natCast_zsmul] using hu
  have hv' : coboundary v = (Nat.card (SingularHomology X 3) : ℤ) • β.val := by
    simpa only [natCast_zsmul] using hv
  simpa only [Int.cast_natCast] using
    IntegralCupOne.residue_cup_commonPrimitive_symmetry _ hN α.val β.val
      (cocycle_condition (singularCochainComplex X) 4 β) u v hu' hv' Ω

end Wikipedia.HopfProblem.DegreeCollapse.IntegralSevenLinking
