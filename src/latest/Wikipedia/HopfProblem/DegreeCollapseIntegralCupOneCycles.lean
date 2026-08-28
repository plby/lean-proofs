import Wikipedia.HopfProblem.DegreeCollapseIntegralCupOne
import Wikipedia.HopfProblem.DegreeCollapseRationalResidue
import Wikipedia.HopfProblem.DegreeCollapseIntegralCapBoundary

/-!
# Symmetric torsion residues on the original seven-cycles

The signed cup-one identity makes the commutator divisible by the
common integral denominator. The original cup Leibniz identity then
identifies the two torsion residues on every original seven-cycle.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCupOne

open FirstHurewicz SingularCohomologyCup SingularMayerVietoris

variable {X : Type} [TopologicalSpace X]

theorem cupOne53_zero_left (β : Cochain X 3) : cupOne53 (0 : Cochain X 5) β = 0 := by
  apply chainMap_ext X 7
  intro σ
  simp only [cupOne53_simplex, value53, faceValue, LinearMap.zero_apply, zero_mul, add_zero]

theorem cupOne44_smul_right (α β : Cochain X 4) (N : ℤ) :
    cupOne44 α (N • β) = N • cupOne44 α β := by
  apply chainMap_ext X 7
  intro σ
  simp only [cupOne44_simplex, LinearMap.smul_apply, smul_eq_mul, value44, faceValue]
  ring

theorem coboundary_on_seven_cycle (η : Cochain X 6)
    (Ω : ModuleHomology.Cycle (singularComplex X) 7) : coboundary η Ω.val = 0 := by
  change η (((singularComplex X).d 7 6).hom Ω.val) = 0
  rw [ModuleHomology.cycle_condition, map_zero]

theorem cup_commutator_cycle (α : Cochain X 4) (u : Cochain X 3)
    (hα : coboundary α = 0) (Ω : ModuleHomology.Cycle (singularComplex X) 7) :
    cup α u Ω.val - cup u α Ω.val = -(cupOne44 α (coboundary u) Ω.val) := by
  have he := LinearMap.congr_fun (coboundary_cupOne43 α u) Ω.val
  rw [coboundary_on_seven_cycle, hα, cupOne53_zero_left] at he
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.zero_apply] at he
  linarith

theorem cup_commonPrimitive_cycle (N : ℤ) (hN : N ≠ 0) (α β : Cochain X 4)
    (u v : Cochain X 3) (hu : coboundary u = N • α) (hv : coboundary v = N • β)
    (Ω : ModuleHomology.Cycle (singularComplex X) 7) :
    cup α v Ω.val = cup u β Ω.val := by
  have he := LinearMap.congr_fun (coboundary_cup u v) Ω.val
  rw [coboundary_on_seven_cycle] at he
  change 0 = cup (coboundary u) v Ω.val + (-1 : ℤ) ^ 3 * cup u (coboundary v) Ω.val at he
  rw [hu, hv, cup_smul_left, cup_smul_right] at he
  simp only [LinearMap.smul_apply, smul_eq_mul] at he
  have hm : N * cup α v Ω.val = N * cup u β Ω.val := by norm_num at he; linarith
  exact mul_left_cancel₀ hN hm

theorem residue_div_eq_of_sub_eq_mul (x y N k : ℤ) (hN : N ≠ 0) (h : x - y = N * k) :
    RationalResidue.residue ((x : ℚ) / (N : ℚ)) =
      RationalResidue.residue ((y : ℚ) / (N : ℚ)) := by
  apply sub_eq_zero.mp
  rw [← map_sub, ← sub_div, ← Int.cast_sub]
  exact (RationalResidue.residue_div_eq_zero_iff (x - y) N hN).mpr ⟨k, h⟩

theorem residue_cup_commonPrimitive_symmetry (N : ℤ) (hN : N ≠ 0) (α β : Cochain X 4)
    (hβ : coboundary β = 0) (u v : Cochain X 3)
    (hu : coboundary u = N • α) (hv : coboundary v = N • β)
    (Ω : ModuleHomology.Cycle (singularComplex X) 7) :
    RationalResidue.residue ((cup β u Ω.val : ℚ) / (N : ℚ)) =
      RationalResidue.residue ((cup α v Ω.val : ℚ) / (N : ℚ)) := by
  have hc := cup_commonPrimitive_cycle N hN α β u v hu hv Ω
  have hm := cup_commutator_cycle β u hβ Ω
  rw [hu, cupOne44_smul_right, LinearMap.smul_apply, smul_eq_mul, ← hc] at hm
  apply residue_div_eq_of_sub_eq_mul _ _ N (-(cupOne44 β α Ω.val)) hN
  linarith

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCupOne
