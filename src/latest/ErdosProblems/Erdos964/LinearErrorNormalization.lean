import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real

/-!
# Negligibility of a linear counting error at logarithmic sieve scale
-/

namespace Erdos964

open Filter
open scoped Topology

theorem tendsto_normalized_linear_error {ι : Type*} {l : Filter ι}
    (f g N L : ι → ℝ) (C : ℝ) (hN : ∀ᶠ i in l, 0 < N i)
    (hL : Tendsto L l atTop) (herror : ∀ᶠ i in l, |f i - g i| ≤ C * N i) :
    Tendsto (fun i => f i / (N i * (L i) ^ 3) - g i / (N i * (L i) ^ 3)) l (𝓝 0) := by
  have htail : Tendsto (fun i => C / (L i) ^ 3) l (𝓝 0) :=
    ((tendsto_pow_atTop (by decide : (3 : ℕ) ≠ 0)).comp hL).const_div_atTop C
  apply (tendsto_iff_norm_sub_tendsto_zero (E := ℝ)).mpr
  apply squeeze_zero' (Eventually.of_forall (fun i => norm_nonneg _)) _ htail
  filter_upwards [hN, herror, hL.eventually (eventually_gt_atTop 0)] with i hNi hi hLi
  simp only [sub_zero, Real.norm_eq_abs]
  rw [← sub_div, abs_div, abs_of_pos (mul_pos hNi (pow_pos hLi 3))]
  calc
    _ ≤ (C * N i) / (N i * (L i) ^ 3) :=
      div_le_div_of_nonneg_right hi (by positivity)
    _ = C / (L i) ^ 3 := by field_simp

end Erdos964
