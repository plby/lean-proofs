/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Copyright 2026 Johan Land.
Licensed under the Apache License, Version 2.0; see Erdos1112/LICENSE and Erdos1112/NOTICE.
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
The four final results of Erdős Problem 1112, proved from the development
in namespace `Erdos1112.Proof`. Definitions are in `Erdos1112/Definitions.lean`;
conclusion-only wrappers are expanded in the statements below.
-/
import ErdosProblems.Erdos1112.Existence.Nested
import ErdosProblems.Erdos1112.NonEx.Main

namespace Erdos1112

/-- Existence half with the paper's explicit ratio bound: when
`d₂ ≥ k + 1`, the concrete ratio `192 · d₂` works. -/
theorem erdos_1112_existence_bound (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁)
    (hd : d₁ < d₂) (h : k + 1 ≤ d₂) :
    ∀ b : ℕ → ℕ, IsLacunaryWith (192 * d₂) b →
      ∃ a : ℕ → ℕ, HasGapsIn d₁ d₂ a ∧ Disjoint (kFoldSumset k a) (Set.range b) :=
  Proof.existence_bound k d₁ d₂ hk hd₁ hd h

/-- Non-existence half in the strong, constructive `Nonempty`-intersection
form. The underlying `Proof.strong_nonexistence` produces
the `¬ Disjoint` witness; `Set.not_disjoint_iff_nonempty_inter` exhibits the actual
collision point `kA ∩ B`. -/
theorem erdos_1112_strong_nonexistence (k d₁ d₂ : ℕ) (hk : 3 ≤ k)
    (hd₁ : 1 ≤ d₁) (h : d₂ ≤ k) (R : ℕ → ℕ) :
    ∃ b : ℕ → ℕ, IsVarLacunaryWith R b ∧
      ∀ a : ℕ → ℕ, HasGapsIn d₁ d₂ a →
        (kFoldSumset k a ∩ Set.range b).Nonempty := by
  obtain ⟨b, hb, hdef⟩ := Proof.strong_nonexistence k d₁ d₂ hk hd₁ h R
  exact ⟨b, hb, fun a ha => Set.not_disjoint_iff_nonempty_inter.mp (hdef a ha)⟩

/-- **Erdős Problem 1112, the dichotomy**: `r` exists iff
`d₂ ≥ k + 1`. Derived from the two halves exactly as in the paper's assembly section. -/
theorem erdos_1112 (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂) :
    (∃ r : ℕ, ∀ b : ℕ → ℕ, IsLacunaryWith r b →
      ∃ a : ℕ → ℕ, HasGapsIn d₁ d₂ a ∧ Disjoint (kFoldSumset k a) (Set.range b)) ↔
      k + 1 ≤ d₂ := by
  constructor
  · rintro ⟨r, hr⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨b, hb, hdef⟩ :=
      erdos_1112_strong_nonexistence k d₁ d₂ hk hd₁ (by omega) (fun _ => r)
    obtain ⟨a, ha, hdisj⟩ := hr b (isVarLacunaryWith_const_iff.mp hb)
    exact (Set.not_disjoint_iff_nonempty_inter.mpr (hdef a ha)) hdisj
  · intro h
    exact ⟨192 * d₂, erdos_1112_existence_bound k d₁ d₂ hk hd₁ hd h⟩

/-- **Erdős Problem 1112, in the problem's literal integer phrasing.**

The problem asks for an *integer* `r`. `QuestionInt` quantifies `r : ℤ`; by the bridge
`question_iff_questionInt` this is equivalent to `Question`, so the dichotomy holds
verbatim for the integer form too. This closes the one modelling step that was
previously argued only in prose. -/
theorem erdos_1112_int (k d₁ d₂ : ℕ) (hk : 3 ≤ k) (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂) :
    (∃ r : ℤ, ∀ b : ℕ → ℕ, IsLacunaryWithInt r b →
      ∃ a : ℕ → ℕ, HasGapsIn d₁ d₂ a ∧ Disjoint (kFoldSumset k a) (Set.range b)) ↔
      k + 1 ≤ d₂ :=
  (question_iff_questionInt k d₁ d₂).symm.trans (erdos_1112 k d₁ d₂ hk hd₁ hd)

#print axioms erdos_1112_existence_bound
-- 'Erdos1112.erdos_1112_existence_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms erdos_1112_strong_nonexistence
-- 'Erdos1112.erdos_1112_strong_nonexistence' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
#print axioms erdos_1112
-- 'Erdos1112.erdos_1112' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms erdos_1112_int
-- 'Erdos1112.erdos_1112_int' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos1112
