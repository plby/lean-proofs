import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionPeriodBasic
import Wikipedia.HopfProblem.TrianglePeriodFamilyLocal
import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalFactors

/-!
# Vertical translations on the actual triangle quotient family

Every actual right block fixes the original second period coordinate.
This proves commutation with all triangle words, so the literal period
translations descend through the existing triangle orbit quotient.
-/

noncomputable section

open Set Matrix
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Triangle

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] [MulAction TriangleGroup B]
  (D : TrianglePeriodFamily.Data V B)

theorem rightBlock_vector (g : TriangleGroup) (b : B) (s : ℂ) :
    D.rightBlock g b *ᵥ Period.vector s = Period.vector s := by
  rw [Period.vector_eq_smul, Matrix.mulVec_smul, D.rightBlock_fixes_second]

/-- This uses the all-word right-block identity, not merely the two
generator formulas. -/
theorem vectorFlow_complexLift (s : ℂ) (g : TriangleGroup) (x : B × ComplexPlane₂) :
    Period.vectorFlow s (D.complexLift g x) =
      D.complexLift g (Period.vectorFlow s x) := by
  simp only [Period.vectorFlow, TrianglePeriodFamily.Data.complexLift,
    Matrix.mulVec_add, rightBlock_vector]

theorem periodFlow_smul (s : ℂ) (g : TriangleGroup) (x : D.TotalSpace) :
    letI := D.totalAction
    Period.flow D.periods s (g • x) = g • Period.flow D.periods s x := by
  let := D.totalAction
  obtain ⟨w, rfl⟩ := D.periods.quotientMap_surjective x
  rw [← D.complexLift_quotientMap, Period.flow_quotientMap,
    vectorFlow_complexLift, D.complexLift_quotientMap, Period.flow_quotientMap]

/-- The actual orbit-quotient translation. -/
def flow (s : ℂ) : D.Space → D.Space := by
  let := D.totalAction
  exact Quotient.lift (fun x => D.quotient (Period.flow D.periods s x)) (by
    intro x y hxy
    have he : D.quotient x = D.quotient y := Quotient.sound hxy
    obtain ⟨g, hg⟩ := (D.quotient_eq_iff x y).mp he
    rw [← hg, periodFlow_smul, D.quotient_smul])

@[simp] theorem flow_quotient (s : ℂ) (x : D.TotalSpace) :
    flow D s (D.quotient x) = D.quotient (Period.flow D.periods s x) := rfl

@[simp] theorem flow_projection (s : ℂ) (x : D.Space) :
    D.projection (flow D s x) = D.projection x := by
  obtain ⟨x, rfl⟩ := D.quotient_surjective x
  rw [flow_quotient, D.projection_quotient, D.projection_quotient, Period.flow_projection]

@[simp] theorem flow_zero (x : D.Space) : flow D 0 x = x := by
  obtain ⟨x, rfl⟩ := D.quotient_surjective x
  rw [flow_quotient, Period.flow_zero]

theorem flow_add (s t : ℂ) (x : D.Space) :
    flow D (s + t) x = flow D s (flow D t x) := by
  obtain ⟨x, rfl⟩ := D.quotient_surjective x
  simp only [flow_quotient, Period.flow_add]

@[simp] theorem flow_int_cast (n : ℤ) (x : D.Space) : flow D (n : ℂ) x = x := by
  obtain ⟨x, rfl⟩ := D.quotient_surjective x
  rw [flow_quotient, Period.flow_int_cast]

/-- Freeness of the actual base covering rules out extra stabilizers
introduced by the triangle quotient on a fixed smooth fibre. -/
theorem flow_quotient_eq_self_iff
    (hq : IsQuotientCoveringMap D.baseQuotient TriangleGroup)
    (s : ℂ) (x : D.TotalSpace) :
    flow D s (D.quotient x) = D.quotient x ↔
      Period.vector s ∈ (D.periods.point x.1).lattice := by
  let := D.totalAction
  let := hq.isCancelSMul
  rw [flow_quotient]
  constructor
  · intro h
    obtain ⟨g, hg⟩ := (D.quotient_eq_iff (Period.flow D.periods s x) x).mp h
    have hb : g • x.1 = x.1 := congrArg Prod.fst hg
    have hg1 : g = 1 := IsCancelSMul.right_cancel g 1 x.1
      (hb.trans (one_smul TriangleGroup x.1).symm)
    have he : Period.flow D.periods s x = x := by
      simpa only [hg1, one_smul] using hg.symm
    exact (Period.flow_eq_self_iff D.periods s x).mp he
  · intro h
    rw [(Period.flow_eq_self_iff D.periods s x).mpr h]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Triangle
