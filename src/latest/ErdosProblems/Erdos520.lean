/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Sigurd William Rachlew Høystad.
Released under Apache 2.0 license as described in Erdos520/LICENSE.

Formalization by Sigurd William Rachlew Høystad with GPT-5.6 Pro and Claude Fable 5.
Source: https://github.com/saasom/Erdos520/tree/v1.1.0
Revision: dea062793bf11efd962752ee378ef84720c9857e (Lean 4.30.0-rc2).
Claim: https://www.erdosproblems.com/forum/thread/520/proof-claims#proof-claim-183
-/
import ErdosProblems.Erdos520.Unconditional

open Filter MeasureTheory
open scoped Topology

namespace Erdos.Problem520

theorem normalized_tendsto_zero :
    ∀ᵐ omega ∂μ, Tendsto (fun N : ℕ =>
      |partialSum omega N| / Real.sqrt ((N : ℝ) * Real.log (Real.log N)))
      atTop (𝓝 0) :=
  erdos520Disproof_unconditional

theorem not_erdos_520 :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ᵐ omega ∂μ,
      limsup (fun N : ℕ =>
        partialSum omega N / Real.sqrt ((N : ℝ) * Real.log (Real.log N))) atTop = c := by
  rintro ⟨c, hc, hlimsup⟩
  have hfalse : ∀ᵐ omega ∂μ, False := by
    filter_upwards [erdos520NoPositiveConstant_unconditional, hlimsup] with omega hne heq
    exact hne c hc heq
  obtain ⟨_, h⟩ := hfalse.exists
  exact h

end Erdos.Problem520
