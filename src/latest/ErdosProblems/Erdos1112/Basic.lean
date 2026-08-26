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
Bridge lemmas on the frozen definitions of `Erdos1112.lean`.

This file must contain no `sorry`. It provides the working API for
`IsLacunaryWith`, `HasGapsIn`, `kFoldSumset`, `RatioWorks`, `IsVarLacunaryWith`
without ever restating them. (`RatioWorks.mono` already lives, proved, in the
frozen file — we reuse it and do not restate it.)

Convention: API lemmas about a frozen def live in that def's namespace (so dot
notation works); everything else lives in `Erdos1112.Proof`.
-/
import ErdosProblems.Erdos1112.Definitions

namespace Erdos1112

namespace Proof

/-! ### Variable-ratio vs constant-ratio lacunarity -/

/-- A constant ratio sequence specializes `IsVarLacunaryWith` to
`IsLacunaryWith` definitionally. -/
lemma isVarLacunaryWith_const {r : ℕ} {b : ℕ → ℕ} :
    IsVarLacunaryWith (fun _ => r) b ↔ IsLacunaryWith r b :=
  Iff.rfl

/-! ### `kFoldSumset` -/

lemma mem_kFoldSumset {k : ℕ} {a : ℕ → ℕ} {n : ℕ} :
    n ∈ kFoldSumset k a ↔ ∃ f : Fin k → ℕ, n = ∑ j, a (f j) :=
  Iff.rfl

lemma sum_mem_kFoldSumset {k : ℕ} {a : ℕ → ℕ} (f : Fin k → ℕ) :
    (∑ j, a (f j)) ∈ kFoldSumset k a :=
  ⟨f, rfl⟩

/-- The constant configuration: `k · a i ∈ kA`. -/
lemma const_mem_kFoldSumset {k : ℕ} {a : ℕ → ℕ} (i : ℕ) :
    k * a i ∈ kFoldSumset k a := by
  refine ⟨fun _ => i, ?_⟩
  simp [Finset.sum_const]

/-- Disjointness with `Set.range b`, unfolded to the pointwise form used
throughout the non-existence development. -/
lemma disjoint_range_iff {k : ℕ} {a b : ℕ → ℕ} :
    Disjoint (kFoldSumset k a) (Set.range b) ↔
      ∀ n ∈ kFoldSumset k a, ∀ i, n ≠ b i := by
  rw [Set.disjoint_left]
  constructor
  · intro h n hn i hni
    exact h hn ⟨i, hni.symm⟩
  · rintro h n hn ⟨i, rfl⟩
    exact h _ hn i rfl

/-- Failure of disjointness from an explicit hit. -/
lemma not_disjoint_of_mem {k : ℕ} {a b : ℕ → ℕ} {i : ℕ}
    (h : b i ∈ kFoldSumset k a) :
    ¬ Disjoint (kFoldSumset k a) (Set.range b) := by
  rw [disjoint_range_iff]
  push Not
  exact ⟨b i, h, i, rfl⟩

/-- The gap word of a sequence: `gap a n = a (n+1) − a n`. -/
def gap (a : ℕ → ℕ) (n : ℕ) : ℕ := a (n + 1) - a n

/-- **Generic discrete intermediate-value lemma.** A walk `f : ℕ → ℤ` that
starts at or below `lo`, reaches at or above `hi` by step `N`, and never
increases by more than `σ` per step, lands inside the window `[lo, hi]`
provided the window is at least as wide as one step (`σ ≤ hi − lo + 1`). Used
three times: the sweep crossing (2.7), the Sturmian ladder (2.10 Step 3), and
the Slot Lemma coarse dial (2.12). -/
lemma discrete_ivt {f : ℕ → ℤ} {N : ℕ} {lo hi σ : ℤ}
    (h0 : f 0 ≤ lo) (hN : hi ≤ f N) (hlohi : lo ≤ hi)
    (hstep : ∀ n, n < N → f (n + 1) - f n ≤ σ) (hwidth : σ ≤ hi - lo + 1) :
    ∃ n, n ≤ N ∧ lo ≤ f n ∧ f n ≤ hi := by
  classical
  have hPN : lo ≤ f N := le_trans hlohi hN
  have hex : ∃ n, lo ≤ f n := ⟨N, hPN⟩
  have hm : lo ≤ f (Nat.find hex) := Nat.find_spec hex
  have hmN : Nat.find hex ≤ N := Nat.find_le hPN
  rcases Nat.eq_zero_or_pos (Nat.find hex) with hm0 | hmpos
  · refine ⟨0, Nat.zero_le _, ?_, ?_⟩
    · rw [hm0] at hm; exact hm
    · have : f 0 = lo := le_antisymm h0 (by rw [hm0] at hm; exact hm)
      omega
  · set m := Nat.find hex with hmdef
    have hprev : ¬ lo ≤ f (m - 1) :=
      Nat.find_min hex (show m - 1 < m by omega)
    have hstep' : f m - f (m - 1) ≤ σ := by
      have hlt : m - 1 < N := by omega
      have := hstep (m - 1) hlt
      rwa [Nat.sub_add_cancel hmpos] at this
    exact ⟨m, hmN, hm, by omega⟩

end Proof

/-! ### Consequences of `HasGapsIn` (in its namespace, for dot notation) -/

namespace HasGapsIn

open Proof

variable {d₁ d₂ : ℕ} {a : ℕ → ℕ}

lemma monotone (h : HasGapsIn d₁ d₂ a) : Monotone a :=
  monotone_nat_of_le_succ fun n => le_trans (Nat.le_add_right _ _) (h.2 n).1

-- `HasGapsIn.strictMono` is provided by the frozen statement file.

lemma pos (h : HasGapsIn d₁ d₂ a) (n : ℕ) : 0 < a n :=
  lt_of_lt_of_le h.1 (h.monotone (Nat.zero_le n))

/-- Linear lower bound `a 0 + n·d₁ ≤ a n`. -/
lemma le_apply (h : HasGapsIn d₁ d₂ a) (n : ℕ) :
    a 0 + n * d₁ ≤ a n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 := (h.2 n).1
      have h2 : (n + 1) * d₁ = n * d₁ + d₁ := by ring
      omega

/-- Linear upper bound `a n ≤ a 0 + n·d₂`. -/
lemma apply_le (h : HasGapsIn d₁ d₂ a) (n : ℕ) :
    a n ≤ a 0 + n * d₂ := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 := (h.2 n).2
      have h2 : (n + 1) * d₂ = n * d₂ + d₂ := by ring
      omega

/-- A gap sequence is unbounded (given `1 ≤ d₁`). -/
lemma exists_gt (hd : 1 ≤ d₁) (h : HasGapsIn d₁ d₂ a) (N : ℕ) :
    ∃ n, N < a n := by
  refine ⟨N + 1, ?_⟩
  have h1 := h.le_apply (N + 1)
  have h2 : N + 1 ≤ (N + 1) * d₁ := Nat.le_mul_of_pos_right (N + 1) hd
  have h3 := h.1
  omega

/-- Tails of gap sequences are gap sequences. -/
lemma tail (h : HasGapsIn d₁ d₂ a) (T : ℕ) :
    HasGapsIn d₁ d₂ (fun n => a (T + n)) :=
  ⟨h.pos T, fun i => h.2 (T + i)⟩

lemma gap_le (h : HasGapsIn d₁ d₂ a) (n : ℕ) : gap a n ≤ d₂ := by
  have := h.2 n; unfold Proof.gap; omega

lemma le_gap (h : HasGapsIn d₁ d₂ a) (n : ℕ) : d₁ ≤ gap a n := by
  have := h.2 n; unfold Proof.gap; omega

lemma succ_eq_add_gap (h : HasGapsIn d₁ d₂ a) (n : ℕ) :
    a (n + 1) = a n + gap a n := by
  have := (h.2 n).1; unfold Proof.gap; omega

/-- `a n = a 0 + ∑_{i<n} gap a i`. -/
lemma eq_add_sum_gaps (h : HasGapsIn d₁ d₂ a) (n : ℕ) :
    a n = a 0 + ∑ i ∈ Finset.range n, gap a i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← Nat.add_assoc, ← ih, ← h.succ_eq_add_gap]

end HasGapsIn

end Erdos1112
