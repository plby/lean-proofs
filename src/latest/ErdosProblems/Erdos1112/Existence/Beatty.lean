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
Shifted Beatty sequences, their gaps, cluster containment, and the safety
criterion. Paper: the existence section.
-/
import ErdosProblems.Erdos1112.Basic

namespace Erdos1112
namespace Proof

/-- The shifted Beatty sequence with real slope `γ` and offset `c`:
`beatty γ c i = c + ⌊(i+1)·γ⌋₊` (indices `i ≥ 0` encode the paper's `i ≥ 1`). -/
noncomputable def beatty (γ : ℝ) (c : ℕ) (i : ℕ) : ℕ :=
  c + (⌊((i : ℝ) + 1) * γ⌋).toNat

/-- Floors of consecutive Beatty terms differ by `d₂ − 1` or `d₂` when the
slope lies in `(d₂ − 1, d₂)`. -/
lemma beatty_floor_gap {d₂ : ℕ} {γ : ℝ} (hγl : (d₂ : ℝ) - 1 < γ)
    (hγu : γ < d₂) (x : ℝ) :
    ⌊x * γ⌋ + ((d₂ : ℤ) - 1) ≤ ⌊(x + 1) * γ⌋ ∧
      ⌊(x + 1) * γ⌋ ≤ ⌊x * γ⌋ + (d₂ : ℤ) := by
  have hx : (x + 1) * γ = x * γ + γ := by ring
  constructor
  · have h1 : x * γ + (((d₂ : ℤ) - 1 : ℤ) : ℝ) ≤ (x + 1) * γ := by
      push_cast
      rw [hx]
      linarith
    calc ⌊x * γ⌋ + ((d₂ : ℤ) - 1)
        = ⌊x * γ + (((d₂ : ℤ) - 1 : ℤ) : ℝ)⌋ := (Int.floor_add_intCast _ _).symm
      _ ≤ ⌊(x + 1) * γ⌋ := Int.floor_le_floor h1
  · have h2 : (x + 1) * γ ≤ x * γ + ((d₂ : ℤ) : ℝ) := by
      push_cast
      rw [hx]
      linarith
    calc ⌊(x + 1) * γ⌋ ≤ ⌊x * γ + ((d₂ : ℤ) : ℝ)⌋ := Int.floor_le_floor h2
      _ = ⌊x * γ⌋ + (d₂ : ℤ) := Int.floor_add_intCast _ _

/-- For slope `γ ∈ (d₂−1, d₂)`, the Beatty gaps lie in `{d₂−1, d₂} ⊆ [d₁, d₂]`,
and the sequence starts positive: it is an admissible `A`. -/
theorem beatty_hasGapsIn {d₁ d₂ c : ℕ} {γ : ℝ}
    (hd₁ : 1 ≤ d₁) (hd : d₁ < d₂)
    (hγl : (d₂ : ℝ) - 1 < γ) (hγu : γ < d₂) :
    HasGapsIn d₁ d₂ (beatty γ c) := by
  have hd₂ : 2 ≤ d₂ := by omega
  have hγ1 : (1 : ℝ) ≤ γ := by
    have h2 : (2 : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast hd₂
    linarith
  -- floors along the sequence are ≥ 1, so `toNat` is faithful
  have hfloor_ge : ∀ i : ℕ, (1 : ℤ) ≤ ⌊((i : ℝ) + 1) * γ⌋ := by
    intro i
    apply Int.le_floor.mpr
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) i]
  constructor
  · -- positivity of the first term
    have := hfloor_ge 0
    unfold beatty
    omega
  · intro i
    have key := beatty_floor_gap hγl hγu ((i : ℝ) + 1)
    have hA := hfloor_ge i
    have hB := hfloor_ge (i + 1)
    have hcast : ((i + 1 : ℕ) : ℝ) + 1 = ((i : ℝ) + 1) + 1 := by push_cast; ring
    unfold beatty
    rw [hcast]
    constructor
    · have := key.1
      omega
    · have := key.2
      omega

/-- Cluster containment (1.1): every element of `k·A_{γ,c}` lies in
`(k·c + s·γ − k, k·c + s·γ]` for some integer `s ≥ k`. -/
theorem beatty_mem_cluster {k c : ℕ} {γ : ℝ} (hk : 0 < k) (hγ : 0 < γ) {n : ℕ}
    (hn : n ∈ kFoldSumset k (beatty γ c)) :
    ∃ s : ℕ, k ≤ s ∧ (k * c + s * γ - k : ℝ) < n ∧ (n : ℝ) ≤ k * c + s * γ := by
  obtain ⟨f, rfl⟩ := hn
  have hfl : ∀ j : Fin k, (0 : ℤ) ≤ ⌊((f j : ℝ) + 1) * γ⌋ := fun j =>
    Int.floor_nonneg.mpr (by positivity)
  -- the ℤ-level value of each term
  have hterm : ∀ j : Fin k,
      ((beatty γ c (f j) : ℕ) : ℤ) = (c : ℤ) + ⌊((f j : ℝ) + 1) * γ⌋ := by
    intro j
    unfold beatty
    push_cast [Int.toNat_of_nonneg (hfl j)]
    ring
  -- the whole sum, over ℝ
  have hn' : ((∑ j, beatty γ c (f j) : ℕ) : ℝ) =
      k * c + ∑ j, ((⌊((f j : ℝ) + 1) * γ⌋ : ℤ) : ℝ) := by
    have h1 : ((∑ j, beatty γ c (f j) : ℕ) : ℤ) =
        k * c + ∑ j, ⌊((f j : ℝ) + 1) * γ⌋ := by
      push_cast
      rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib]
      simp [mul_comm]
    exact_mod_cast h1
  -- the index sum, over ℝ
  have hs : ∑ j, (((f j : ℝ) + 1) * γ) = ((∑ j, (f j + 1) : ℕ) : ℝ) * γ := by
    rw [← Finset.sum_mul]
    push_cast
    ring_nf
  refine ⟨∑ j, (f j + 1), ?_, ?_, ?_⟩
  · calc k = ∑ _j : Fin k, 1 := by simp
      _ ≤ ∑ j, (f j + 1) := Finset.sum_le_sum fun j _ => by omega
  · -- strict lower bound: sum of (x_j − 1 < ⌊x_j⌋)
    have hlt : ∑ j, (((f j : ℝ) + 1) * γ - 1) <
        ∑ j, ((⌊((f j : ℝ) + 1) * γ⌋ : ℤ) : ℝ) := by
      refine Finset.sum_lt_sum_of_nonempty ?_ fun j _ => Int.sub_one_lt_floor _
      exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hk)
    have hsub : ∑ j, (((f j : ℝ) + 1) * γ - 1) =
        ((∑ j, (f j + 1) : ℕ) : ℝ) * γ - k := by
      rw [Finset.sum_sub_distrib, hs]
      simp
    rw [hn']
    linarith [hsub ▸ hlt]
  · -- upper bound: sum of (⌊x_j⌋ ≤ x_j)
    have hle : ∑ j, ((⌊((f j : ℝ) + 1) * γ⌋ : ℤ) : ℝ) ≤
        ∑ j, ((f j : ℝ) + 1) * γ :=
      Finset.sum_le_sum fun j _ => Int.floor_le _
    rw [hn']
    linarith [hs ▸ hle]

/-- Safety criterion (1.1): if no integer `s ≥ 1` has `s·γ ∈ [b − k·c, b − k·c + k]`
then `b ∉ k·A_{γ,c}`. -/
theorem beatty_avoids {k c b : ℕ} {γ : ℝ} (hk : 0 < k) (hγ : 0 < γ)
    (hsafe : ∀ s : ℕ, 0 < s →
      (s * γ : ℝ) ∉ Set.Icc ((b : ℝ) - k * c) ((b : ℝ) - k * c + k)) :
    b ∉ kFoldSumset k (beatty γ c) := by
  intro hb
  obtain ⟨s, hsk, hlo, hhi⟩ := beatty_mem_cluster hk hγ hb
  refine hsafe s (lt_of_lt_of_le hk hsk) ⟨?_, ?_⟩
  · linarith
  · linarith

end Proof
end Erdos1112
