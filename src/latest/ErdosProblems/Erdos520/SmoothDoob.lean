import ErdosProblems.Erdos520.Doob
import ErdosProblems.Erdos520.SmoothMartingale

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open MeasureTheory

namespace Erdos
namespace Problem520

/-!
# Doob's inequality for the concrete smooth-sum martingale

The generic finite Doob theorem is instantiated here for `p ↦ Ψ(z,p)`.
The conditional/fiber version used for a thin interval is obtained by the
same theorem after fixing the old coordinates; this global version records
all measurability and moment side conditions in the actual model.
-/

theorem integrable_abs_Ψ_pow (z p r : ℕ) :
    Integrable (fun omega : Omega => |Ψ omega z p| ^ r) μ := by
  have hmeas : StronglyMeasurable
      (fun omega : Omega => |Ψ omega z p| ^ r) := by
    simpa only [Real.norm_eq_abs] using!
      ((stronglyMeasurable_Ψ_filtration z p).norm.pow r).mono
        (εFiltration.le p)
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    (((squarefreeSmoothSets z p).card : ℝ) ^ r)
  exact ae_of_all μ fun omega => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) r)]
    exact pow_le_pow_left₀ (abs_nonneg _) (by
      simpa only [Real.norm_eq_abs] using! norm_Ψ_le_card omega z p) r

theorem memLp_two_abs_Ψ_pow (z p r : ℕ) :
    MemLp (fun omega : Omega => |Ψ omega z p| ^ r) 2 μ := by
  have hmeas : StronglyMeasurable
      (fun omega : Omega => |Ψ omega z p| ^ r) := by
    simpa only [Real.norm_eq_abs] using!
      ((stronglyMeasurable_Ψ_filtration z p).norm.pow r).mono
        (εFiltration.le p)
  apply MemLp.of_bound hmeas.aestronglyMeasurable
    (((squarefreeSmoothSets z p).card : ℝ) ^ r)
  exact ae_of_all μ fun omega => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) r)]
    exact pow_le_pow_left₀ (abs_nonneg _) (by
      simpa only [Real.norm_eq_abs] using! norm_Ψ_le_card omega z p) r

/-- Concrete finite even-moment Doob estimate for the smooth partial sums. -/
theorem integral_sq_finiteRunningMax_abs_Ψ_pow_le (z r n : ℕ) :
    ∫ omega,
        finiteRunningMax (fun p omega => |Ψ omega z p| ^ r) n omega ^ 2 ∂μ
      ≤ 4 * ∫ omega, |Ψ omega z n| ^ (2 * r) ∂μ := by
  exact Martingale.integral_sq_finiteRunningMax_abs_pow_le
    (martingale_Ψ z) r n (integrable_abs_Ψ_pow z · r)
      (memLp_two_abs_Ψ_pow z n r)

end Problem520
end Erdos
