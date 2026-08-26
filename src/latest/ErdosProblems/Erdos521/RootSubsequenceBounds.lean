/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Subsequence and reciprocal-count bounds used for the total-root limsup.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.ReversalRoots
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

namespace Erdos521

open Filter
open scoped Topology

theorem le_limsup_of_subsequence_lower_bound (f g : ℕ → ℝ) (u : ℕ → ℕ)
    (hu : Tendsto u atTop atTop) (L : ℝ) (hg : Tendsto g atTop (𝓝 L))
    (hgf : ∀ᶠ j : ℕ in atTop, g j ≤ f (u j)) :
    (L : EReal) ≤ limsup (fun n ↦ (f n : EReal)) atTop := by
  have hbound : ∀ᶠ j : ℕ in atTop, (g j : EReal) ≤ (f (u j) : EReal) :=
    hgf.mono (fun _ h ↦ EReal.coe_le_coe_iff.mpr h)
  calc
    (L : EReal) = limsup (fun j ↦ (g j : EReal)) atTop := (EReal.tendsto_coe.mpr hg).limsup_eq.symm
    _ ≤ limsup (fun j ↦ (f (u j) : EReal)) atTop := limsup_le_limsup hbound
    _ ≤ limsup (fun n ↦ (f n : EReal)) atTop :=
      hu.limsup_comp_le_limsup (u := fun n ↦ (f n : EReal))

noncomputable def reversalLowerStatistic (ε : ℕ → ℝ) (n : ℕ) : ℝ :=
  (interiorRootCount ε n : ℝ) / Real.log n +
    (interiorRootCount (reversedCoefficients n ε) n : ℝ) / Real.log n - 2 / Real.log n

theorem reversalLowerStatistic_le (ε : ℕ → ℝ) {n : ℕ} (hn : 2 ≤ n)
    (hε₀ : ε 0 ≠ 0) (hεn : ε n ≠ 0) : reversalLowerStatistic ε n ≤ normalizedRootCount ε n := by
  unfold reversalLowerStatistic normalizedRootCount
  rw [← add_div, ← sub_div]
  exact div_le_div_of_nonneg_right (rootCount_reversal_lower ε n hε₀ hεn)
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))

theorem two_div_log_subsequence_tendsto_zero (u : ℕ → ℕ) (hu : Tendsto u atTop atTop) :
    Tendsto (fun j : ℕ ↦ (2 : ℝ) / Real.log (u j)) atTop (𝓝 0) := by
  apply tendsto_bdd_div_atTop_nhds_zero (b := 2) (B := 2)
  · exact Eventually.of_forall (fun _ ↦ le_rfl)
  · exact Eventually.of_forall (fun _ ↦ le_rfl)
  · exact Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hu)

theorem reversalLowerStatistic_subsequence_limit (ε : ℕ → ℝ) (u : ℕ → ℕ)
    (hu : Tendsto u atTop atTop)
    (hinter : Tendsto (fun n : ℕ ↦ (interiorRootCount ε n : ℝ) / Real.log n) atTop (𝓝 (1 / Real.pi)))
    (hrev : Tendsto (fun j ↦ (interiorRootCount (reversedCoefficients (u j) ε) (u j) : ℝ) /
      Real.log (u j)) atTop (𝓝 (1 / Real.pi))) :
    Tendsto (fun j ↦ reversalLowerStatistic ε (u j)) atTop (𝓝 (2 / Real.pi)) := by
  have h : Tendsto (fun j ↦ reversalLowerStatistic ε (u j)) atTop
      (𝓝 (1 / Real.pi + 1 / Real.pi - 0)) :=
    ((hinter.comp hu).add hrev).sub (two_div_log_subsequence_tendsto_zero u hu)
  have heq : 1 / Real.pi + 1 / Real.pi - (0 : ℝ) = 2 / Real.pi := by ring
  rwa [heq] at h

end Erdos521
