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
the lambda-lift lemma: mod-`a` frame certificates and the λ-lift.

`FrameCert a b M x Y Z` is THE certificate notion of the development: it is
stated per-residue (`M − 1 + height ≤ a·x` for some box representative of
every class mod `a`), which makes it
  (i)  kernel-decidable row-by-row (`frameCertOK`, Tables.lean),
  (ii) consumable by `frame_lemma` with `S := a·x − (M−1)`, and
  (iii) EXACTLY transported by the λ-lift: one step `(a,b,M) → (a,b+a,M+a)`
       adds `(j+k)·a ≤ (Y+Z)·a` to each height and `(Y+Z+1)·a` to the budget
       side, so the lift-stability hypothesis is literally the decided table
       property `Y + Z + 1 ≤ a` — no interface gap.
-/
import ErdosProblems.Erdos1112.Sharp.Frame
import ErdosProblems.Erdos1112.Sharp.Defs

namespace Erdos1112
namespace Proof

/-- A mod-`a` frame certificate: `M` positive (rules out the `M = 0`
degenerate where the ℕ-truncated budget fails to lift), within budget,
lift-stable, and every residue class mod `a` has a box representative whose
height clears the padding window per-residue. -/
def FrameCert (a b M x Y Z : ℕ) : Prop :=
  0 < M ∧ x + Y + Z ≤ M - 1 ∧ Y + Z + 1 ≤ a ∧
  ∀ ρ < a, ∃ j k, j ≤ Y ∧ k ≤ Z ∧ (j * b + k * M) % a = ρ ∧
    M - 1 + (j * b + k * M) ≤ a * x

/-- A frame certificate yields the (SHARP) witness for its triple. -/
theorem FrameCert.sharpTriple {a b M x Y Z : ℕ} (h : FrameCert a b M x Y Z) :
    SharpTriple a b M := by
  obtain ⟨hM, hbudget, hstab, hreps⟩ := h
  have ha : 0 < a := by omega
  have hMax : M - 1 ≤ a * x := by
    obtain ⟨j, k, -, -, -, hh⟩ := hreps 0 ha
    omega
  refine ⟨Multiset.replicate Y b + Multiset.replicate Z M +
    Multiset.replicate x a, ?_, ?_, a * x - (M - 1), ?_⟩
  · intro w hw
    rcases Multiset.mem_add.mp hw with hw | hw
    · rcases Multiset.mem_add.mp hw with hw | hw
      · exact Or.inr (Or.inl (Multiset.eq_of_mem_replicate hw))
      · exact Or.inr (Or.inr (Multiset.eq_of_mem_replicate hw))
    · exact Or.inl (Multiset.eq_of_mem_replicate hw)
  · simp only [Multiset.card_add, Multiset.card_replicate]
    omega
  · intro i hi
    apply frame_lemma ha (S := a * x - (M - 1))
    · intro ρ hρ
      obtain ⟨j, k, hj, hk, hres, hh⟩ := hreps ρ hρ
      exact ⟨j, k, hj, hk, hres, by omega⟩
    · omega
    · omega

/-- **the lambda-lift lemma (λ-lift), one step.** A frame certificate transports from
`(a, b, M)` to `(a, b+a, M+a)`, with padding grown by exactly the decided
stability margin `Y + Z + 1 ≤ a`. -/
theorem FrameCert.lift {a b M x Y Z : ℕ} (h : FrameCert a b M x Y Z) :
    FrameCert a (b + a) (M + a) (x + (Y + Z + 1)) Y Z := by
  obtain ⟨hM, hbudget, hstab, hreps⟩ := h
  refine ⟨by omega, by omega, hstab, ?_⟩
  intro ρ hρ
  obtain ⟨j, k, hj, hk, hres, hh⟩ := hreps ρ hρ
  have h1 : j * (b + a) + k * (M + a) = j * b + k * M + (j + k) * a := by ring
  refine ⟨j, k, hj, hk, ?_, ?_⟩
  · rw [h1, Nat.add_mul_mod_self_right]
    exact hres
  · have h2 : (j + k) * a ≤ (Y + Z) * a := Nat.mul_le_mul_right a (by omega)
    have h3 : a * (x + (Y + Z + 1)) = a * x + (Y + Z + 1) * a := by ring
    have h4 : (Y + Z + 1) * a = (Y + Z) * a + a := by ring
    omega

/-- **the lambda-lift lemma, iterated**: the whole λ-chain above a certified base. -/
theorem FrameCert.lift_iter {a b M x Y Z : ℕ} (h : FrameCert a b M x Y Z) :
    ∀ lam : ℕ, FrameCert a (b + lam * a) (M + lam * a)
      (x + lam * (Y + Z + 1)) Y Z := by
  intro lam
  induction lam with
  | zero => simpa using h
  | succ lam ih =>
      have step := ih.lift
      have e1 : b + lam * a + a = b + (lam + 1) * a := by ring
      have e2 : M + lam * a + a = M + (lam + 1) * a := by ring
      have e3 : x + lam * (Y + Z + 1) + (Y + Z + 1) = x + (lam + 1) * (Y + Z + 1) := by
        ring
      rwa [e1, e2, e3] at step

end Proof
end Erdos1112
