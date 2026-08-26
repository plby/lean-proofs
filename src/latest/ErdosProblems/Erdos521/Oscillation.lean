/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The unconditional oscillation theorem and the negative answer to Erdős Problem 521.
Informal sources: XianJun An and Vincent Lin; Rob Sneiderman; Do.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.RootLimsup
import ErdosProblems.Erdos521.RootLiminf

namespace Erdos521

open MeasureTheory Filter
open scoped Topology

theorem ae_rootCount_oscillation : ClaimedOscillation :=
  ae_normalizedRootCount_liminf.and ae_normalizedRootCount_limsup

theorem ae_not_tendsto_normalizedRootCount :
    ∀ᵐ ε ∂sequenceLaw, ∀ L : ℝ, ¬ Tendsto (normalizedRootCount ε) atTop (𝓝 L) := by
  filter_upwards [ae_normalizedRootCount_liminf, ae_normalizedRootCount_limsup]
    with ε hinf hsup
  intro L hL
  have hE := EReal.tendsto_coe.mpr hL
  have heq : (L : EReal) = (1 / Real.pi : ℝ) := hE.liminf_eq.symm.trans hinf
  have hbad : (↑(2 / Real.pi : ℝ) : EReal) ≤ (1 / Real.pi : ℝ) :=
    hsup.trans_eq (hE.limsup_eq.trans heq)
  have hgap : (1 / Real.pi : ℝ) < 2 / Real.pi :=
    div_lt_div_of_pos_right (by norm_num) Real.pi_pos
  exact hgap.not_ge (EReal.coe_le_coe_iff.mp hbad)

theorem not_conjecture : ¬ Conjecture := by
  intro h
  obtain ⟨ε, hnot, hlim⟩ := (ae_not_tendsto_normalizedRootCount.and h).exists
  exact hnot (2 / Real.pi) hlim

end Erdos521
