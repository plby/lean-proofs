import Wikipedia.HopfProblem.ThreefoldHomologyThirdSourceLattice
import Mathlib.Tactic.LinearCombination

/-!
# The exact integral relation among the degree-three source columns

For order-four shear `2 * k4`, every zero source pair is a unique
integer multiple of the displayed relation.  The conclusion holds even
without a separate cusp-invariance hypothesis on the input vector:
the zero source equations already force the stated cusp vector.
-/

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdSource

open PeriodTorusHigherHomologyExterior

/-- The original order-three coordinates of an integral source relation. -/
def kernelThreeCoordinates (c3 k : ℤ) : Fin 2 → ℤ := ![(2 * c3 + 4) * k, 2 * k]

/-- The original order-four coordinates of the same relation. -/
def kernelFourCoordinates (k4 k : ℤ) : Fin 2 → ℤ := ![(3 - 2 * k4) * k, -2 * k]

/-- The original cusp vector of the relation, independent of either shear. -/
def kernelCuspCoordinates (k : ℤ) : Fin 6 → ℤ := cuspVector 0 (2 * k) (12 * k) 0

theorem kernelCuspCoordinates_fixed (k : ℤ) :
    squareM₀ *ᵥ kernelCuspCoordinates k = kernelCuspCoordinates k :=
  cuspVector_fixed _ _ _ _

/-- The displayed integral relation has zero under both original source columns. -/
theorem kernelCoordinates_source_zero (c3 k4 k : ℤ) :
    sourcePair c3 (2 * k4) (kernelThreeCoordinates c3 k)
      (kernelFourCoordinates k4 k) (kernelCuspCoordinates k) = 0 := by
  rw [sourcePair, threeWangVector_apply, fourWangVector_apply, kernelCuspCoordinates,
    squareA₂_cuspVector]
  apply Prod.ext <;> funext i <;> fin_cases i <;>
    simp [kernelThreeCoordinates, kernelFourCoordinates, cuspVector] <;> ring

theorem kernelThreeCoordinates_injective (c3 : ℤ) :
    Function.Injective (kernelThreeCoordinates c3) := by
  intro k l h
  have h₁ := congrFun h (1 : Fin 2)
  change 2 * k = 2 * l at h₁
  omega

/-- There are no further integral zero-source relations. -/
theorem sourcePair_eq_zero_iff (c3 k4 : ℤ) (a3 a4 : Fin 2 → ℤ) (v : Fin 6 → ℤ) :
    sourcePair c3 (2 * k4) a3 a4 v = 0 ↔
      ∃ k : ℤ, a3 = kernelThreeCoordinates c3 k ∧
        a4 = kernelFourCoordinates k4 k ∧ v = kernelCuspCoordinates k := by
  constructor
  · intro h
    have hz₃ : threeWangVector c3 a3 - squareA₂ *ᵥ v = 0 := congrArg Prod.fst h
    have hz₄ : fourWangVector (2 * k4) a4 - v = 0 := congrArg Prod.snd h
    have hv : v = fourWangVector (2 * k4) a4 := (sub_eq_zero.mp hz₄).symm
    have heq : threeWangVector c3 a3 = fourWangVector (2 * k4) a4 := by
      have heq := sub_eq_zero.mp hz₃
      rw [hv, fourWangVector_fixed] at heq
      exact heq
    rw [threeWangVector_apply, fourWangVector_apply] at heq
    have h₂ := congrFun heq (2 : Fin 6)
    have h₃ := congrFun heq (3 : Fin 6)
    have h₄ := congrFun heq (4 : Fin 6)
    change a3 1 = -a4 1 at h₂
    change 3 * (a3 0 - c3 * a3 1) = 2 * (2 * a4 0 - (2 * k4) * a4 1) at h₃
    change -(a3 0 - c3 * a3 1) + 2 * a3 1 =
      -(2 * a4 0 - (2 * k4) * a4 1) - 3 * a4 1 at h₄
    have hb₄ : a4 1 = -a3 1 := by omega
    rw [hb₄] at h₃ h₄
    have hα : a3 0 - c3 * a3 1 = 2 * a3 1 := by
      linear_combination h₃ + 2 * h₄
    have hβ : 2 * a4 0 + 2 * k4 * a3 1 = 3 * a3 1 := by
      linear_combination h₄ + hα
    have heven : (2 : ℤ) ∣ a3 1 := by
      refine ⟨a4 0 + (k4 - 1) * a3 1, ?_⟩
      linear_combination -hβ
    obtain ⟨k, hk⟩ := heven
    have ha₃ : a3 = kernelThreeCoordinates c3 k := by
      ext i
      fin_cases i
      · change a3 0 = (2 * c3 + 4) * k
        rw [hk] at hα
        linear_combination hα
      · exact hk
    have ha₄ : a4 = kernelFourCoordinates k4 k := by
      ext i
      fin_cases i
      · change a4 0 = (3 - 2 * k4) * k
        apply mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0)
        rw [hk] at hβ
        linear_combination hβ
      · change a4 1 = -2 * k
        rw [hb₄, hk]
        ring
    have hv' : v = kernelCuspCoordinates k := by
      rw [hv, ha₄, fourWangVector_apply]
      ext i
      fin_cases i <;> simp [kernelFourCoordinates, kernelCuspCoordinates, cuspVector] <;> ring
    exact ⟨k, ha₃, ha₄, hv'⟩
  · rintro ⟨k, rfl, rfl, rfl⟩
    exact kernelCoordinates_source_zero c3 k4 k

/-- The integer parameter in the exact source-kernel description is unique. -/
theorem sourcePair_eq_zero_existsUnique (c3 k4 : ℤ) (a3 a4 : Fin 2 → ℤ)
    (v : Fin 6 → ℤ) (h : sourcePair c3 (2 * k4) a3 a4 v = 0) :
    ∃! k : ℤ, a3 = kernelThreeCoordinates c3 k ∧
      a4 = kernelFourCoordinates k4 k ∧ v = kernelCuspCoordinates k := by
  obtain ⟨k, h₃, h₄, hv⟩ := (sourcePair_eq_zero_iff c3 k4 a3 a4 v).mp h
  refine ⟨k, ⟨h₃, h₄, hv⟩, ?_⟩
  intro l hl
  apply kernelThreeCoordinates_injective c3
  exact hl.1.symm.trans h₃

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.ThirdSource
