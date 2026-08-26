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
The diagonal certificate lemma. Given any ratio sequence `R`,
a single `B` (hitting every congruence class at arbitrarily large heights,
while growing as fast as `R` demands) defeats every tail-covering `A`.
Paper: the non-existence section.

`hall` supplies the normalized covering `TailCoveringN` (reduced residue
`ρ < m`; `NonEx/Kit.lean`), the form exported by every non-existence case lemma.
-/
import ErdosProblems.Erdos1112.NonEx.Kit

namespace Erdos1112
namespace Proof

/-! ### The enumeration of congruence classes

`certPair i = (m, ρ)` with `m ≥ 1`, `ρ < m`, hitting every such pair at
arbitrarily large indices `i` (the outer `Nat.pair` coordinate is free). -/

/-- Modulus component of the class enumeration. -/
def certM (i : ℕ) : ℕ := (Nat.unpair (Nat.unpair i).1).1 + 1

/-- Residue component of the class enumeration (reduced mod `certM`). -/
def certR (i : ℕ) : ℕ := (Nat.unpair (Nat.unpair i).1).2 % certM i

lemma certM_pos (i : ℕ) : 0 < certM i := Nat.succ_pos _

lemma certR_lt (i : ℕ) : certR i < certM i := Nat.mod_lt _ (certM_pos i)

/-- Every reduced class `(m, ρ)` recurs at indices beyond any bound. -/
lemma cert_hit (m ρ N : ℕ) (hρ : ρ < m) :
    ∃ i, N ≤ i ∧ certM i = m ∧ certR i = ρ := by
  refine ⟨Nat.pair (Nat.pair (m - 1) ρ) N, Nat.right_le_pair _ _, ?_, ?_⟩
  · change (Nat.unpair (Nat.unpair _).1).1 + 1 = m
    rw [Nat.unpair_pair, Nat.unpair_pair]
    omega
  · change (Nat.unpair (Nat.unpair _).1).2 % _ = ρ
    rw [certM, Nat.unpair_pair, Nat.unpair_pair]
    simp only
    have hm : m - 1 + 1 = m := by omega
    rw [hm, Nat.mod_eq_of_lt hρ]

/-! ### The diagonal sequence `B` -/

/-- Any reduced congruence class contains elements above any threshold. -/
lemma exists_in_class (m ρ t : ℕ) (hρ : ρ < m) :
    ∃ x, t < x ∧ x % m = ρ := by
  refine ⟨ρ + m * (t + 1), ?_, ?_⟩
  · have h1 : t + 1 ≤ m * (t + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρ]

/-- The certificate sequence: `certB R i` is the least element of the class
`(certM i, certR i)` exceeding `max (R (i-1) · certB R (i-1))
(max (certB R (i-1)) i)` (and exceeding `0` at `i = 0`). -/
def certB (R : ℕ → ℕ) : ℕ → ℕ
  | 0 => Nat.find (exists_in_class (certM 0) (certR 0) 0 (certR_lt 0))
  | i + 1 => Nat.find (exists_in_class (certM (i + 1)) (certR (i + 1))
      (max (R i * certB R i) (max (certB R i) (i + 1))) (certR_lt (i + 1)))

lemma certB_zero_spec (R : ℕ → ℕ) :
    0 < certB R 0 ∧ certB R 0 % certM 0 = certR 0 :=
  Nat.find_spec (exists_in_class (certM 0) (certR 0) 0 (certR_lt 0))

lemma certB_succ_spec (R : ℕ → ℕ) (i : ℕ) :
    max (R i * certB R i) (max (certB R i) (i + 1)) < certB R (i + 1) ∧
      certB R (i + 1) % certM (i + 1) = certR (i + 1) :=
  Nat.find_spec (exists_in_class (certM (i + 1)) (certR (i + 1)) _ (certR_lt (i + 1)))

lemma certB_mod (R : ℕ → ℕ) (i : ℕ) : certB R i % certM i = certR i := by
  cases i with
  | zero => exact (certB_zero_spec R).2
  | succ i => exact (certB_succ_spec R i).2

lemma certB_ge (R : ℕ → ℕ) (i : ℕ) : i ≤ certB R i := by
  cases i with
  | zero => exact Nat.zero_le _
  | succ i =>
      have := (certB_succ_spec R i).1
      omega

lemma certB_lacunary (R : ℕ → ℕ) : IsVarLacunaryWith R (certB R) := by
  refine ⟨(certB_zero_spec R).1, strictMono_nat_of_lt_succ fun i => ?_, fun i => ?_⟩
  · have := (certB_succ_spec R i).1
    omega
  · have := (certB_succ_spec R i).1
    omega

/-- **the corresponding paper lemma (certificate).** If every `(d₁,d₂)`-sequence is tail-covering
(normalized form), then for every ratio sequence `R` there is a single
var-lacunary `B` meeting `kA` for every admissible `A`. The hypothesis uses
the normalized covering `TailCoveringN` (reduced residue `ρ < m`). -/
theorem strong_nonexistence_of_tailCovering (k d₁ d₂ : ℕ) (R : ℕ → ℕ)
    (hall : ∀ a : ℕ → ℕ, HasGapsIn d₁ d₂ a → TailCoveringN k a) :
    ∃ b : ℕ → ℕ, IsVarLacunaryWith R b ∧
      ∀ a : ℕ → ℕ, HasGapsIn d₁ d₂ a →
        ¬ Disjoint (kFoldSumset k a) (Set.range b) := by
  refine ⟨certB R, certB_lacunary R, fun a ha => ?_⟩
  obtain ⟨m, hm, ρ, hρ, X₀, hX⟩ := hall a ha
  obtain ⟨i, hiN, hiM, hiR⟩ := cert_hit m ρ X₀ hρ
  refine not_disjoint_of_mem (i := i) (hX (certB R i) ?_ ?_)
  · have := certB_ge R i
    omega
  · rw [← hiM, ← hiR]
    exact certB_mod R i

end Proof
end Erdos1112
