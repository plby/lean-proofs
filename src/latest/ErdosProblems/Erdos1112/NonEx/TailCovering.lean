/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Copyright 2026 Johan Land.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 1112.
Informal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
Formal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
GPT-5.5 and Gemini 3.1 supplied advice and adversarial review.
Source: https://www.erdosproblems.com/1112#post-7375
https://github.com/beetree/math_erdos_1112/tree/63ed94d3e802782aeb521095c17d6109a2dc57b5
Original Lean version: 4.27.0.
Original Mathlib commit: a3a10db0e9d66acbebf76c5e6a135066525ac900.
-/
/-
The tail-covering property — `kA` eventually contains a full
congruence class. Paper: the paper's notation subsection and
the paper's non-existence section.
-/
import ErdosProblems.Erdos1112.Basic

namespace Erdos1112
namespace Proof

/-- `kA` contains a full congruence-class tail: there are `m ≥ 1`, a *reduced*
residue `ρ < m` (so the class is genuinely infinite), and `X₀` with
`{x ≥ X₀ : x ≡ ρ (mod m)} ⊆ kFoldSumset k a`.

The requirement `ρ < m` is essential: without it the degenerate residue
`ρ = m` covers the empty class and makes the property vacuously true, so the
notion would carry no information. -/
def TailCovering (k : ℕ) (a : ℕ → ℕ) : Prop :=
  ∃ m, 0 < m ∧ ∃ ρ, ρ < m ∧ ∃ X₀, ∀ x, X₀ ≤ x → x % m = ρ → x ∈ kFoldSumset k a

/-- Tail-covering with modulus 1 from "contains all large integers". -/
lemma TailCovering.of_cofinite {k : ℕ} {a : ℕ → ℕ}
    (h : ∃ X₀, ∀ x, X₀ ≤ x → x ∈ kFoldSumset k a) : TailCovering k a := by
  obtain ⟨X₀, hX⟩ := h
  exact ⟨1, one_pos, 0, one_pos, X₀, fun x hx _ => hX x hx⟩

end Proof
end Erdos1112
