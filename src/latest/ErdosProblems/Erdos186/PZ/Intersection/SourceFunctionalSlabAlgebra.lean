/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceFunctionalSlabDenseDilation

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Pure real algebra used to cancel the uniform scale denominator. -/
theorem fixed_lt_dilation_mul_of_growth
    {D K c p dilation gamma : ℝ}
    (hD : 0 < D) (hc : 0 < c) (_hgamma : 0 < gamma)
    (hgrowth : D * K / c < p)
    (hpower : c * p ≤ gamma * (D * dilation)) :
    K < dilation * gamma := by
  have hfixed : D * K < c * p := by
    calc
      D * K = (D * K / c) * c := by rw [div_mul_cancel₀ _ hc.ne']
      _ < p * c := mul_lt_mul_of_pos_right hgrowth hc
      _ = c * p := by ring
  have hscaled : D * K < D * (dilation * gamma) := by
    calc
      D * K < c * p := hfixed
      _ ≤ gamma * (D * dilation) := hpower
      _ = D * (dilation * gamma) := by ring
  exact (mul_lt_mul_iff_of_pos_left hD).mp hscaled

end

end Erdos186.PZ.Intersection
