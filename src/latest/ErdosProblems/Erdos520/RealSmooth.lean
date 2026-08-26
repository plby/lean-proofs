import ErdosProblems.Erdos520.ScalingIntegral
import ErdosProblems.Erdos520.SmoothMartingale
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.MeasureTheory.Function.Floor

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Real cutoffs for smooth sums

The paper integrates the step function `z ↦ Ψ(z,y)` over the positive real
axis.  The arithmetic development uses natural cutoffs, so this file supplies
the exact bridge via the natural floor.
-/

/-- Smooth partial sum with a real cutoff.  Negative cutoffs give the empty
positive sum because `Nat.floor` is zero there. -/
noncomputable def ΨReal (omega : Omega) (z : ℝ) (y : ℕ) : ℝ :=
  Ψ omega ⌊z⌋₊ y

/-- Coefficient in the fresh Walsh expansion at a real cutoff. -/
noncomputable def realFreshCoefficient
    (old : Omega) (z : ℝ) (a : ℕ) (S : Finset ℕ) : ℝ :=
  ΨReal old (z / (freshProduct S : ℝ)) a

theorem realFreshCoefficient_eq_freshCoefficient_floor
    (old : Omega) (z : ℝ) (a : ℕ) (S : Finset ℕ) :
    realFreshCoefficient old z a S =
      freshCoefficient old ⌊z⌋₊ a S := by
  simp only [realFreshCoefficient, ΨReal, freshCoefficient]
  rw [Nat.floor_div_natCast]

/-- Equation (18) at a real cutoff. -/
theorem ΨReal_eq_freshWalshExpansion
    (omega : Omega) (z : ℝ) {a b : ℕ} (hab : a ≤ b) :
    ΨReal omega z b =
      ∑ S ∈ (freshPrimes a b).powerset,
        freshCharacter omega S * realFreshCoefficient omega z a S := by
  rw [ΨReal, Ψ_eq_freshWalshExpansion omega ⌊z⌋₊ hab]
  unfold freshWalshExpansion
  apply Finset.sum_congr rfl
  intro S _hS
  rw [realFreshCoefficient_eq_freshCoefficient_floor]

/-- For fixed signs, the real-cutoff smooth sum is measurable in the cutoff. -/
theorem measurable_ΨReal_cutoff (omega : Omega) (y : ℕ) :
    Measurable fun z : ℝ => ΨReal omega z y := by
  unfold ΨReal
  exact (measurable_of_countable fun n : ℕ => Ψ omega n y).comp
    Nat.measurable_floor

/-- Joint measurability in the real cutoff and the sign configuration. -/
theorem measurable_ΨReal_joint (y : ℕ) :
    Measurable fun x : ℝ × Omega => ΨReal x.2 x.1 y := by
  have hNat : Measurable fun x : ℕ × Omega => Ψ x.2 x.1 y := by
    apply measurable_from_prod_countable_right
    intro n
    exact ((stronglyMeasurable_Ψ_filtration n y).mono
      (εFiltration.le y)).measurable
  exact hNat.comp
    ((Nat.measurable_floor.comp measurable_fst).prodMk measurable_snd)

/-- Equation (21) for the real-cutoff smooth energy. -/
theorem integral_ΨReal_div_mul_inv_sq_Ioi
    (old : Omega) (a : ℕ) {d : ℕ} (hd : 0 < d) :
    (∫ z in Ioi (0 : ℝ),
        |ΨReal old (z / (d : ℝ)) a| ^ 2 / z ^ 2) =
      ((d : ℝ)⁻¹) *
        ∫ w in Ioi (0 : ℝ), |ΨReal old w a| ^ 2 / w ^ 2 := by
  simpa only using!
    (integral_comp_div_mul_inv_sq_Ioi
      (fun w : ℝ => |ΨReal old w a| ^ 2)
      (d := (d : ℝ)) (by exact_mod_cast hd))

end Problem520
end Erdos
