import ErdosProblems.Erdos720.CycleHost
import ErdosProblems.Erdos720.PathHost

open Filter Topology
open scoped SimpleGraph

noncomputable section

namespace Erdos720

open SimpleGraph

lemma sizeRamsey_cycle_le (n : ℕ) (hn : 2 * cycleVertexConstant + 2 ≤ n) :
    sizeRamsey (cycleGraph n) ≤ cycleRamseyEdgeConstant * n := by
  obtain ⟨H, hE, hA⟩ := exists_linear_cycle_ramsey_host n hn
  exact (sizeRamsey_le_of_witness
    ⟨Fintype.card (CycleTemplate n), H, rfl, hA⟩).trans hE

lemma tendsto_zero_of_eventually_linear (a : ℕ → ℕ) (C : ℕ)
    (hlin : ∀ᶠ n in atTop, a n ≤ C * n) :
    Tendsto (fun n : ℕ ↦ (a n : ℝ) / (n : ℝ) ^ 2) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n ↦ div_nonneg (by positivity) (sq_nonneg _)
  · filter_upwards [hlin, eventually_gt_atTop 0] with n hn hnpos
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hcast : (a n : ℝ) ≤ (C * n : ℕ) := by exact_mod_cast hn
    calc
      (a n : ℝ) / (n : ℝ) ^ 2 ≤ (C * n : ℕ) / (n : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right hcast (sq_nonneg _)
      _ = (C : ℝ) / n := by
        push_cast
        field_simp
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

lemma not_tendsto_atTop_of_eventually_linear (a : ℕ → ℕ) (C : ℕ)
    (hlin : ∀ᶠ n in atTop, a n ≤ C * n) :
    ¬ Tendsto (fun n : ℕ ↦ (a n : ℝ) / (n : ℝ)) atTop atTop := by
  intro htop
  have hlower : ∀ᶠ n : ℕ in atTop,
      (C : ℝ) + 1 ≤ (a n : ℝ) / (n : ℝ) := (tendsto_atTop.1 htop) _
  have hupper : ∀ᶠ n : ℕ in atTop,
      (a n : ℝ) / (n : ℝ) ≤ C := by
    filter_upwards [hlin, eventually_gt_atTop 0] with n hn hnpos
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    apply (div_le_iff₀ hnreal).2
    exact_mod_cast hn
  obtain ⟨n, hlo, hup⟩ := (hlower.and hupper).exists
  linarith

lemma eventually_path_linear :
    ∀ᶠ n : ℕ in atTop, sizeRamsey (pathGraph (n + 1)) ≤ 6272 * n := by
  filter_upwards [eventually_ge_atTop 16] with n hn
  calc
    sizeRamsey (pathGraph (n + 1)) ≤ 3136 * (n + 1) :=
      sizeRamsey_path_le (n + 1) (by omega)
    _ ≤ 6272 * n := by omega

lemma eventually_cycle_linear :
    ∀ᶠ n : ℕ in atTop,
      sizeRamsey (cycleGraph n) ≤ cycleRamseyEdgeConstant * n := by
  filter_upwards [eventually_ge_atTop (2 * cycleVertexConstant + 2)] with n hn
  exact sizeRamsey_cycle_le n hn

/-- The first proposed assertion in Problem 720 is false: the normalized path
size-Ramsey numbers do not tend to infinity. -/
theorem path_sizeRamsey_ratio_not_tendsto_atTop :
    ¬ Tendsto (fun n : ℕ ↦ (sizeRamsey (pathGraph (n + 1)) : ℝ) / n)
      atTop atTop :=
  not_tendsto_atTop_of_eventually_linear _ 6272 eventually_path_linear

/-- The second proposed path assertion is true. -/
theorem path_sizeRamsey_div_sq_tendsto_zero :
    Tendsto (fun n : ℕ ↦
      (sizeRamsey (pathGraph (n + 1)) : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds 0) :=
  tendsto_zero_of_eventually_linear _ 6272 eventually_path_linear

/-- The cycle assertion is true; indeed the proof establishes a linear bound. -/
theorem cycle_sizeRamsey_div_sq_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (sizeRamsey (cycleGraph n) : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds 0) :=
  tendsto_zero_of_eventually_linear _ cycleRamseyEdgeConstant eventually_cycle_linear

end Erdos720
