/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The almost-sure liminf follows from the proved interior strong law and cone records.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.InteriorStrongLaw
import ErdosProblems.Erdos521.CoefficientProbability
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

theorem normalizedRootCount_liminf_eq_of_interior_limit (ε : ℕ → ℝ)
    (hlim : Tendsto (fun n : ℕ ↦ (interiorRootCount ε n : ℝ) / Real.log n)
      atTop (𝓝 (1 / Real.pi)))
    (hrecord : ∀ N, ∃ m, N ≤ m ∧ rootCount ε (2 * m + 1) = interiorRootCount ε (2 * m + 1)) :
    liminf (fun n ↦ (normalizedRootCount ε n : EReal)) atTop = (1 / Real.pi : ℝ) := by
  have hE := EReal.tendsto_coe.mpr hlim
  apply le_antisymm
  · choose m hm heq using hrecord
    let u : ℕ → ℕ := fun k ↦ 2 * m k + 1
    have hu : Tendsto u atTop atTop := by
      apply tendsto_atTop_mono _ tendsto_id
      intro k
      have h := hm k
      change k ≤ 2 * m k + 1
      omega
    have hseq : Tendsto (fun k ↦ normalizedRootCount ε (u k)) atTop (𝓝 (1 / Real.pi)) := by
      apply (hlim.comp hu).congr
      intro k
      dsimp only [Function.comp_apply, normalizedRootCount, u]
      rw [heq k]
    have hsub := hu.liminf_le_liminf_comp (u := fun n ↦ (normalizedRootCount ε n : EReal))
    exact hsub.trans_eq (EReal.tendsto_coe.mpr hseq).liminf_eq
  · rw [← hE.liminf_eq]
    refine liminf_le_liminf ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    apply EReal.coe_le_coe_iff.mpr
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (interiorRootCount_le ε n))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))

theorem ae_normalizedRootCount_liminf :
    ∀ᵐ ε ∂sequenceLaw,
      liminf (fun n ↦ (normalizedRootCount ε n : EReal)) atTop = (1 / Real.pi : ℝ) := by
  filter_upwards [ae_interiorRootCount_div_log_limit, ae_infinite_rootCount_eq_interior]
    with ε hlim hrecord
  exact normalizedRootCount_liminf_eq_of_interior_limit ε hlim hrecord

end Erdos521
