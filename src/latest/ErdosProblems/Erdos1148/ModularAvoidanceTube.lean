import ErdosProblems.Erdos1148.ModularHaarAvoidance
import ErdosProblems.Erdos1148.ModularHaarBowenBall

/-! # Bowen neighborhoods of an avoidance set avoid a smaller open set -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma mem_forwardHaarTube_zero_of_close {η : ℝ} {g : SL(2, ℝ)} (hg : EntryCloseOne η g) :
    g ∈ forwardHaarTube η 0 := by
  exact ⟨hg, by simpa only [neg_zero, Real.exp_zero, mul_one] using hg.2.2.1⟩

theorem modularForwardHaarBall_subset_avoidance {η : ℝ}
    {U V : Set ModularOrbitSpace}
    (hthick : ∀ x ∈ V, ∀ u ∈ forwardHaarTube η 0, modularRightTranslate u x ∈ U)
    (n : ℕ) (g : SL(2, ℝ)) (hg : modularMk g ∈ finiteOrbitAvoidance modularTimeOne U n) :
    modularForwardHaarBall η n g ⊆ finiteOrbitAvoidance modularTimeOne V n := by
  rintro y ⟨h, hh, rfl⟩ j hj hV
  have hjR : (j : ℝ) ≤ n := by exact_mod_cast hj.le
  have hc := (entryForwardBowenTube_iff_flow_closeness (Nat.cast_nonneg n) h).mp hh
    j ⟨Nat.cast_nonneg j, hjR⟩
  let u := (diagonalFlow (-(j : ℝ)) * h * diagonalFlow j)⁻¹
  have hu : u ∈ forwardHaarTube η 0 := mem_forwardHaarTube_zero_of_close (entryCloseOne_inv hc)
  have hU := hthick (modularTimeOne^[j] (modularMk (g * h))) hV u hu
  have heq : modularRightTranslate u (modularTimeOne^[j] (modularMk (g * h))) =
      modularTimeOne^[j] (modularMk g) := by
    rw [modularTimeOne_iterate_mk, modularTimeOne_iterate_mk, modularRightTranslate_mk]
    congr 1
    dsimp only [u]
    rw [diagonalFlow_neg]
    group
  rw [heq] at hU
  exact hg j hj hU

end Erdos1148.DukeArithmetic
