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
The two-letter combinatorial core: the interval property, the sweep, the
width dichotomy, and the boundary width (palindrome–border–period).

Setting: tail gaps `g_n = δ + e·h_n`, `h_n ∈ {0,1}`, `gcd(δ, δ+e) = 1`,
`q_n = h_1 + ⋯ + h_n`, `W_s = {∑ q_{i_t} : ∑ i_t = s}` (k summands,
repetitions allowed), `W₂(σ) = max−min of q_i + q_j on i+j = σ`.

Interface note: `Wset` does not constrain `1 ≤ f j`. Index `0`
(contributing `qCount h 0 = 0`) matches the paper's tail convention
`a_{1+i}, i ≥ 0` (`x ∈ kA − k·a₁` uses `i_t ≥ 0`), is required for
the antidiagonal pair placements of the width lemmas (`WidthTwoAt` pairs may
use index 0), and is harmless in the sweep.
-/
import ErdosProblems.Erdos1112.NonEx.GapWord

namespace Erdos1112
namespace Proof

/-- Prefix-count of a binary word `h : ℕ → Bool` (1-indexed positions,
`q h 0 = 0`). -/
def qCount (h : ℕ → Bool) (n : ℕ) : ℕ :=
  (Finset.range n).sum fun i => if h (i + 1) then 1 else 0

lemma qCount_succ (h : ℕ → Bool) (n : ℕ) :
    qCount h (n + 1) = qCount h n + (if h (n + 1) then 1 else 0) :=
  Finset.sum_range_succ _ n

lemma qCount_le (h : ℕ → Bool) (n : ℕ) : qCount h n ≤ n := by
  calc qCount h n ≤ ∑ _i ∈ Finset.range n, 1 :=
        Finset.sum_le_sum fun i _ => by split <;> omega
    _ = n := by simp

/-- The `k`-summand antidiagonal value set
`W_s = {∑_t q_{i_t} : i_t ≥ 0, ∑_t i_t = s}`. -/
def Wset (h : ℕ → Bool) (k s : ℕ) : Set ℕ :=
  {w | ∃ f : Fin k → ℕ, (∑ j, f j) = s ∧ (∑ j, qCount h (f j)) = w}

/-- Two-index antidiagonal width `W₂(σ) ≥ 2` witnessed by two pairs. -/
def WidthTwoAt (h : ℕ → Bool) (σ : ℕ) : Prop :=
  ∃ i j i' j', i + j = σ ∧ i' + j' = σ ∧
    qCount h i + qCount h j + 2 ≤ qCount h i' + qCount h j'

/-! ### `Wset` algebra -/

/-- Transport of `Wset` membership along index/antidiagonal equalities
(placement arithmetic). -/
lemma Wset.congr_mem {h : ℕ → Bool} {k k' s s' w : ℕ} (hk : k = k')
    (hs : s = s') (hw : w ∈ Wset h k s) : w ∈ Wset h k' s' := hk ▸ hs ▸ hw

lemma Wset.single (h : ℕ → Bool) (i : ℕ) : qCount h i ∈ Wset h 1 i :=
  ⟨fun _ => i, by simp, by simp⟩

lemma Wset.add {h : ℕ → Bool} {k₁ k₂ s₁ s₂ w₁ w₂ : ℕ}
    (h₁ : w₁ ∈ Wset h k₁ s₁) (h₂ : w₂ ∈ Wset h k₂ s₂) :
    w₁ + w₂ ∈ Wset h (k₁ + k₂) (s₁ + s₂) := by
  obtain ⟨f, hfs, hfw⟩ := h₁
  obtain ⟨g, hgs, hgw⟩ := h₂
  refine ⟨Fin.append f g, ?_, ?_⟩
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hfs, hgs]
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [hfw, hgw]

lemma Wset.pair (h : ℕ → Bool) (i j : ℕ) :
    qCount h i + qCount h j ∈ Wset h 2 (i + j) :=
  Wset.add (Wset.single h i) (Wset.single h j)

lemma Wset.nsmul {h : ℕ → Bool} {k s w : ℕ} (m : ℕ) (hw : w ∈ Wset h k s) :
    m * w ∈ Wset h (m * k) (m * s) := by
  induction m with
  | zero =>
      simp only [Nat.zero_mul]
      exact ⟨Fin.elim0, by simp, by simp⟩
  | succ m ih =>
      have h1 := Wset.add ih hw
      simp only [Nat.succ_mul]
      exact h1

lemma Wset.le_sum {h : ℕ → Bool} {k s w : ℕ} (hw : w ∈ Wset h k s) : w ≤ s := by
  obtain ⟨f, hfs, hfw⟩ := hw
  calc w = ∑ j, qCount h (f j) := hfw.symm
    _ ≤ ∑ j, f j := Finset.sum_le_sum fun j _ => qCount_le h (f j)
    _ = s := hfs

lemma Wset.nonempty {h : ℕ → Bool} {k : ℕ} (hk : 0 < k) (s : ℕ) :
    ∃ w, w ∈ Wset h k s := by
  have h1 : qCount h s ∈ Wset h 1 s := Wset.single h s
  have h2 : (0 : ℕ) ∈ Wset h (k - 1) 0 :=
    ⟨fun _ => 0, by simp, by simp [qCount]⟩
  have h3 := Wset.add h1 h2
  have hk' : 1 + (k - 1) = k := by omega
  have hs' : s + 0 = s := by omega
  exact ⟨qCount h s + 0, Wset.congr_mem hk' hs' h3⟩

/-! ### Window endpoints -/

/-- Left endpoint of the antidiagonal window. -/
noncomputable def wmin (h : ℕ → Bool) (k s : ℕ) : ℕ := sInf (Wset h k s)

/-- Right endpoint of the antidiagonal window. -/
noncomputable def wmax (h : ℕ → Bool) (k s : ℕ) : ℕ := sSup (Wset h k s)

lemma bddAbove_Wset (h : ℕ → Bool) (k s : ℕ) : BddAbove (Wset h k s) :=
  ⟨s, fun _ hw => Wset.le_sum hw⟩

lemma wmin_mem {h : ℕ → Bool} {k : ℕ} (hk : 0 < k) (s : ℕ) :
    wmin h k s ∈ Wset h k s :=
  Nat.sInf_mem (Wset.nonempty hk s)

lemma wmax_mem {h : ℕ → Bool} {k : ℕ} (hk : 0 < k) (s : ℕ) :
    wmax h k s ∈ Wset h k s :=
  Nat.sSup_mem (Wset.nonempty hk s) (bddAbove_Wset h k s)

lemma wmin_le {h : ℕ → Bool} {k s w : ℕ} (hw : w ∈ Wset h k s) :
    wmin h k s ≤ w :=
  Nat.sInf_le hw

lemma le_wmax {h : ℕ → Bool} {k s w : ℕ} (hw : w ∈ Wset h k s) :
    w ≤ wmax h k s :=
  le_csSup (bddAbove_Wset h k s) hw

lemma wmax_le_sum {h : ℕ → Bool} {k : ℕ} (hk : 0 < k) (s : ℕ) :
    wmax h k s ≤ s :=
  Wset.le_sum (wmax_mem hk s)

/-- One up-step of a configuration: bump one index; the value moves by
`0` or `1`. -/
lemma Wset.step_up {h : ℕ → Bool} {k s w : ℕ} (hk : 0 < k)
    (hw : w ∈ Wset h k s) :
    ∃ v ∈ Wset h k (s + 1), w ≤ v ∧ v ≤ w + 1 := by
  obtain ⟨f, hfs, hfw⟩ := hw
  refine ⟨∑ j, qCount h (Function.update f ⟨0, hk⟩ (f ⟨0, hk⟩ + 1) j),
    ⟨Function.update f ⟨0, hk⟩ (f ⟨0, hk⟩ + 1), ?_, rfl⟩, ?_, ?_⟩
  all_goals
    have e1 := sum_update_add (fun (_ : Fin k) v => v) f ⟨0, hk⟩ (f ⟨0, hk⟩ + 1)
    have e2 := sum_update_add (fun (_ : Fin k) v => qCount h v) f ⟨0, hk⟩
      (f ⟨0, hk⟩ + 1)
    have q1 := qCount_succ h (f ⟨0, hk⟩)
    have hq : (if h (f ⟨0, hk⟩ + 1) then 1 else 0) ≤ 1 := by split <;> omega
    omega

/-- One down-step of a configuration: shrink one nonzero index; the value
drops by `0` or `1`. -/
lemma Wset.step_down {h : ℕ → Bool} {k s w : ℕ} (hw : w ∈ Wset h k (s + 1)) :
    ∃ v ∈ Wset h k s, w ≤ v + 1 := by
  obtain ⟨f, hfs, hfw⟩ := hw
  have hj : ∃ j₀ : Fin k, 1 ≤ f j₀ := by
    by_contra hn
    push Not at hn
    have : ∑ j, f j = 0 := Finset.sum_eq_zero fun j _ => by have := hn j; omega
    omega
  obtain ⟨j₀, hj₀⟩ := hj
  have hfj : f j₀ - 1 + 1 = f j₀ := by omega
  refine ⟨∑ j, qCount h (Function.update f j₀ (f j₀ - 1) j),
    ⟨Function.update f j₀ (f j₀ - 1), ?_, rfl⟩, ?_⟩
  all_goals
    have e1 := sum_update_add (fun (_ : Fin k) v => v) f j₀ (f j₀ - 1)
    have e2 := sum_update_add (fun (_ : Fin k) v => qCount h v) f j₀ (f j₀ - 1)
    have q1 : qCount h (f j₀) = qCount h (f j₀ - 1) + (if h (f j₀) then 1 else 0) := by
      have := qCount_succ h (f j₀ - 1); rwa [hfj] at this
    have hq : (if h (f j₀) then 1 else 0) ≤ 1 := by split <;> omega
    omega

/-- `wmax(s+1) ≤ wmax(s) + 1`: the sweep's step bound. -/
lemma wmax_succ_le (h : ℕ → Bool) {k : ℕ} (hk : 0 < k) (s : ℕ) :
    wmax h k (s + 1) ≤ wmax h k s + 1 := by
  obtain ⟨v, hv, hv2⟩ := Wset.step_down (wmax_mem hk (s + 1))
  exact le_trans hv2 (Nat.add_le_add_right (le_wmax hv) 1)

/-- `wmax(s+t) ≤ wmax(s) + t` (iterated step bound). -/
lemma wmax_add_le (h : ℕ → Bool) {k : ℕ} (hk : 0 < k) (s t : ℕ) :
    wmax h k (s + t) ≤ wmax h k s + t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have h1 := wmax_succ_le h hk (s + t)
      have he1 : s + (t + 1) = s + t + 1 := by omega
      rw [he1]
      omega

lemma wmin_succ_le (h : ℕ → Bool) {k : ℕ} (hk : 0 < k) (s : ℕ) :
    wmin h k (s + 1) ≤ wmin h k s + 1 := by
  obtain ⟨v, hv, _, hv2⟩ := Wset.step_up hk (wmin_mem hk s)
  exact le_trans (wmin_le hv) hv2

lemma wmin_add_le (h : ℕ → Bool) {k : ℕ} (hk : 0 < k) (s e : ℕ) :
    wmin h k (s + e) ≤ wmin h k s + e := by
  induction e with
  | zero => simp
  | succ e ih =>
      have h1 : s + (e + 1) = (s + e) + 1 := by omega
      rw [h1]
      have h2 := wmin_succ_le h hk (s + e)
      omega

/-! ### the corresponding paper lemma -/

/-- Connectivity walk: two configurations on the same antidiagonal are
joined by single-index moves changing the value by at most 1; any value
between their values is attained. Strong induction on the `ℓ¹` distance. -/
private lemma connect_aux (h : ℕ → Bool) (k s : ℕ) :
    ∀ D : ℕ, ∀ f f' : Fin k → ℕ, (∑ j, f j) = s → (∑ j, f' j) = s →
      (∑ j, ((f j : ℤ) - f' j).natAbs) = D →
      ∀ u, (∑ j, qCount h (f j)) ≤ u → u ≤ (∑ j, qCount h (f' j)) →
      u ∈ Wset h k s := by
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    intro f f' hfs hfs' hD u hu hu'
    rcases eq_or_lt_of_le hu with heq | hlt
    · exact ⟨f, hfs, heq⟩
    by_cases hff' : f = f'
    · subst hff'
      exact absurd (hlt.trans_le hu') (lt_irrefl _)
    -- find a descent coordinate and an ascent coordinate
    have hex_a : ∃ a, f' a < f a := by
      by_contra hno
      push Not at hno
      apply hff'
      funext j
      by_contra hj
      have hjlt : f j < f' j := lt_of_le_of_ne (hno j) hj
      have hsum : (∑ j, f j) < ∑ j, f' j :=
        Finset.sum_lt_sum (fun i _ => hno i) ⟨j, Finset.mem_univ j, hjlt⟩
      omega
    have hex_b : ∃ b, f b < f' b := by
      by_contra hno
      push Not at hno
      apply hff'
      funext j
      by_contra hj
      have hjlt : f' j < f j := lt_of_le_of_ne (hno j) (Ne.symm hj)
      have hsum : (∑ j, f' j) < ∑ j, f j :=
        Finset.sum_lt_sum (fun i _ => hno i) ⟨j, Finset.mem_univ j, hjlt⟩
      omega
    obtain ⟨a, ha⟩ := hex_a
    obtain ⟨b, hb⟩ := hex_b
    have hab : a ≠ b := fun hh => by rw [hh] at ha; omega
    -- the move f → g: pull 1 from coordinate a, push 1 onto coordinate b
    set F1 := Function.update f a (f a - 1) with hF1def
    set g := Function.update F1 b (f b + 1) with hgdef
    have hF1a : F1 a = f a - 1 := by rw [hF1def, Function.update_self]
    have hF1b : F1 b = f b := by rw [hF1def, Function.update_of_ne (Ne.symm hab)]
    -- index sums
    have e1 : (∑ j, g j) + F1 b = (f b + 1) + ∑ j, F1 j := by
      rw [hgdef]; exact sum_update_add (fun _ v => v) F1 b (f b + 1)
    have e2 : (∑ j, F1 j) + f a = (f a - 1) + ∑ j, f j := by
      rw [hF1def]; exact sum_update_add (fun _ v => v) f a (f a - 1)
    have hgs : (∑ j, g j) = s := by omega
    -- values
    have e3 : (∑ j, qCount h (g j)) + qCount h (F1 b) =
        qCount h (f b + 1) + ∑ j, qCount h (F1 j) := by
      rw [hgdef]; exact sum_update_add (fun _ v => qCount h v) F1 b (f b + 1)
    have e4 : (∑ j, qCount h (F1 j)) + qCount h (f a) =
        qCount h (f a - 1) + ∑ j, qCount h (f j) := by
      rw [hF1def]; exact sum_update_add (fun _ v => qCount h v) f a (f a - 1)
    have q1 := qCount_succ h (f b)
    have q2 : qCount h (f a) = qCount h (f a - 1) + (if h (f a) then 1 else 0) := by
      have hfa : f a - 1 + 1 = f a := by omega
      have := qCount_succ h (f a - 1)
      rw [hfa] at this
      exact this
    have hqb : (if h (f b + 1) then 1 else 0) ≤ 1 := by split <;> omega
    have hqa : (if h (f a) then 1 else 0) ≤ 1 := by split <;> omega
    have hF1bq : qCount h (F1 b) = qCount h (f b) := by rw [hF1b]
    -- distances
    have e5 : (∑ j, ((g j : ℤ) - f' j).natAbs) + ((F1 b : ℤ) - f' b).natAbs =
        (((f b + 1 : ℕ) : ℤ) - f' b).natAbs + ∑ j, ((F1 j : ℤ) - f' j).natAbs := by
      rw [hgdef]
      exact sum_update_add (fun j v => ((v : ℤ) - f' j).natAbs) F1 b (f b + 1)
    have e6 : (∑ j, ((F1 j : ℤ) - f' j).natAbs) + ((f a : ℤ) - f' a).natAbs =
        (((f a - 1 : ℕ) : ℤ) - f' a).natAbs + ∑ j, ((f j : ℤ) - f' j).natAbs := by
      rw [hF1def]
      exact sum_update_add (fun j v => ((v : ℤ) - f' j).natAbs) f a (f a - 1)
    have hpair : ((f a : ℤ) - f' a).natAbs + ((f b : ℤ) - f' b).natAbs ≤
        ∑ j, ((f j : ℤ) - f' j).natAbs := by
      have hps : ∑ j ∈ ({a, b} : Finset (Fin k)), ((f j : ℤ) - f' j).natAbs =
          ((f a : ℤ) - f' a).natAbs + ((f b : ℤ) - f' b).natAbs :=
        Finset.sum_pair hab
      have hle : ∑ j ∈ ({a, b} : Finset (Fin k)), ((f j : ℤ) - f' j).natAbs ≤
          ∑ j, ((f j : ℤ) - f' j).natAbs :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      omega
    have hF1bd : ((F1 b : ℤ) - f' b).natAbs = ((f b : ℤ) - f' b).natAbs := by
      rw [hF1b]
    -- the two moved coordinates each shed exactly one unit of distance
    have hNAb1 : (((f b + 1 : ℕ) : ℤ) - f' b).natAbs =
        ((f b : ℤ) - f' b).natAbs - 1 := by omega
    have hNAa1 : (((f a - 1 : ℕ) : ℤ) - f' a).natAbs =
        ((f a : ℤ) - f' a).natAbs - 1 := by omega
    have hNAa_pos : 1 ≤ ((f a : ℤ) - f' a).natAbs := by omega
    have hNAb_pos : 1 ≤ ((f b : ℤ) - f' b).natAbs := by omega
    -- recurse at distance D - 2
    have hgD : (∑ j, ((g j : ℤ) - f' j).natAbs) = D - 2 := by omega
    have hDlt : D - 2 < D := by omega
    have hgV : (∑ j, qCount h (g j)) ≤ u := by omega
    exact ih (D - 2) hDlt g f' hgs hfs' hgD u hgV hu'

/-- **the corresponding paper lemma (interval property)**: `W_s` is a full integer interval. -/
theorem Wset_interval (h : ℕ → Bool) (k s : ℕ)
    {w w' u : ℕ} (hw : w ∈ Wset h k s) (hw' : w' ∈ Wset h k s)
    (hu : w ≤ u) (hu' : u ≤ w') : u ∈ Wset h k s := by
  obtain ⟨f, hfs, hfw⟩ := hw
  obtain ⟨f', hfs', hfw'⟩ := hw'
  exact connect_aux h k s _ f f' hfs hfs' rfl u (by omega) (by omega)

/-! ### Bridges between the ambient sequence and `Wset` (used by sweep and
the Sturmian ladder). -/

/-- The two-letter ambient identity: `a n = a 0 + δ·n + e·q_n`. -/
lemma sweep_a_eq {d₁ d₂ : ℕ} {a : ℕ → ℕ} (hgaps : HasGapsIn d₁ d₂ a)
    (h : ℕ → Bool) (δ e : ℕ)
    (hgap : ∀ n, gap a n = δ + e * (if h (n + 1) then 1 else 0)) (n : ℕ) :
    a n = a 0 + δ * n + e * qCount h n := by
  induction n with
  | zero => simp [qCount]
  | succ n ih =>
      rw [hgaps.succ_eq_add_gap n, hgap n, ih, qCount_succ]
      ring

/-- Config bridge: every `w ∈ W_s` realizes `k·a₀ + δ·s + e·w ∈ kA`. -/
lemma mem_kFold_of_Wset {k d₁ d₂ : ℕ} {a : ℕ → ℕ} (hgaps : HasGapsIn d₁ d₂ a)
    (h : ℕ → Bool) (δ e : ℕ)
    (hgap : ∀ n, gap a n = δ + e * (if h (n + 1) then 1 else 0))
    {s w : ℕ} (hw : w ∈ Wset h k s) :
    k * a 0 + δ * s + e * w ∈ kFoldSumset k a := by
  obtain ⟨f, hfs, hfw⟩ := hw
  refine ⟨f, ?_⟩
  have hbridge : ∀ j : Fin k, a (f j) = a 0 + δ * f j + e * qCount h (f j) :=
    fun j => sweep_a_eq hgaps h δ e hgap (f j)
  have e1 : (∑ j, a (f j)) =
      (∑ _j : Fin k, a 0) + δ * (∑ j, f j) + e * (∑ j, qCount h (f j)) := by
    rw [Finset.sum_congr rfl (fun j _ => hbridge j), Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  rw [e1, hfs, hfw, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]

set_option maxHeartbeats 2400000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
/-- **the corresponding paper lemma (sweep)**: if the windows have width `≥ d₂ − 1` for all
large `s`, the two-letter tail's `kA` contains all large integers.
(Interface in terms of the ambient sequence.) -/
theorem sweep {k d₁ d₂ : ℕ} {a : ℕ → ℕ} (hk : 3 ≤ k)
    (hgaps : HasGapsIn d₁ d₂ a)
    (h : ℕ → Bool) (δ e : ℕ) (hδ : 0 < δ) (he : 0 < e)
    (hco : Nat.Coprime δ (δ + e)) (hd₂ : d₂ = δ + e)
    (hgap : ∀ n, gap a n = δ + e * (if h (n + 1) then 1 else 0))
    (S₀ : ℕ)
    (hwidth : ∀ s, S₀ ≤ s → ∃ w w', w ∈ Wset h k s ∧ w' ∈ Wset h k s ∧
      w + (d₂ - 1) ≤ w') :
    TailCovering k a := by
  have hk0 : 0 < k := by omega
  have hd2pos : 0 < d₂ := by omega
  have hδe : Nat.Coprime δ e := by
    have h' : δ.Coprime (e + δ) := by rwa [Nat.add_comm] at hco
    exact (Nat.coprime_add_self_right).mp h'
  refine ⟨1, one_pos, 0, one_pos, k * a 0 + d₂ * (S₀ + e) + 1, fun x hx _ => ?_⟩
  -- reduced target `x' = x − k·a₀`
  set x' : ℕ := x - k * a 0 with hx'def
  have hx'ge : d₂ * (S₀ + e) + 1 ≤ x' := by omega
  have hxx' : x = k * a 0 + x' := by omega
  -- an admissible level `s₀ ∈ [S₀, S₀+e)` with `δ·s₀ ≡ x' (mod e)`
  obtain ⟨s₀, hs₀lo, hs₀hi, hs₀mod⟩ := exists_mul_mod_eq he hδe x' S₀
  -- `w₀ := (x' − δ·s₀)/e` (one exact division)
  have hwm₀ : wmax h k s₀ ≤ s₀ := wmax_le_sum hk0 s₀
  have hδs₀ : δ * s₀ + e * wmax h k s₀ ≤ x' := by
    have h1 : e * wmax h k s₀ ≤ e * s₀ := Nat.mul_le_mul_left e hwm₀
    have h2 : δ * s₀ + e * s₀ = d₂ * s₀ := by rw [hd₂]; ring
    have h3 : d₂ * s₀ ≤ d₂ * (S₀ + e) := Nat.mul_le_mul_left d₂ (by omega)
    omega
  have hle₀ : δ * s₀ ≤ x' := by omega
  have hdvd : e ∣ x' - δ * s₀ := (Nat.modEq_iff_dvd' hle₀).mp hs₀mod
  set w₀ : ℕ := (x' - δ * s₀) / e with hw₀def
  have hew₀ : e * w₀ = x' - δ * s₀ := Nat.mul_div_cancel' hdvd
  have hw₀ge : wmax h k s₀ ≤ w₀ := by
    have : e * wmax h k s₀ ≤ e * w₀ := by omega
    exact Nat.le_of_mul_le_mul_left this he
  -- the ℤ walk `g j = wmax(s₀+j·e) − w₀ + δ·j`, window `[0, d₂−1]`, step `≤ d₂`
  set g : ℕ → ℤ := fun j => (wmax h k (s₀ + j * e) : ℤ) - w₀ + δ * j with hgdef
  set N : ℕ := w₀ + d₂ with hNdef
  have hg0 : g 0 ≤ 0 := by
    have he0 : g 0 = (wmax h k s₀ : ℤ) - w₀ := by simp [hgdef]
    rw [he0]; omega
  have hgN : (d₂ : ℤ) - 1 ≤ g N := by
    have heN : g N = (wmax h k (s₀ + N * e) : ℤ) - w₀ + δ * N := by simp [hgdef]
    rw [heN, hNdef]
    have hwpos : (0 : ℤ) ≤ (wmax h k (s₀ + (w₀ + d₂) * e) : ℤ) := by positivity
    have hδ1 : (1 : ℤ) ≤ δ := by exact_mod_cast hδ
    have hmul : (w₀ : ℤ) + d₂ ≤ (δ : ℤ) * (w₀ + d₂) := by
      have hnn : (0 : ℤ) ≤ (w₀ : ℤ) + d₂ := by positivity
      calc (w₀ : ℤ) + d₂ = 1 * ((w₀ : ℤ) + d₂) := by ring
        _ ≤ (δ : ℤ) * ((w₀ : ℤ) + d₂) := by
            apply mul_le_mul_of_nonneg_right hδ1 hnn
    have hNe : ((w₀ + d₂ : ℕ) : ℤ) = (w₀ : ℤ) + d₂ := by push_cast; ring
    rw [hNe]
    linarith [hwpos, hmul]
  have hstep : ∀ j, j < N → g (j + 1) - g j ≤ d₂ := by
    intro j _
    have hΔ : wmax h k (s₀ + (j + 1) * e) ≤ wmax h k (s₀ + j * e) + e := by
      have he1 : s₀ + (j + 1) * e = (s₀ + j * e) + e := by ring
      rw [he1]; exact wmax_add_le h hk0 _ e
    have hcast : ((wmax h k (s₀ + (j + 1) * e) : ℤ)) ≤ (wmax h k (s₀ + j * e) : ℤ) + e := by
      exact_mod_cast hΔ
    have hstepeq : g (j + 1) - g j =
        (wmax h k (s₀ + (j + 1) * e) : ℤ) - (wmax h k (s₀ + j * e) : ℤ) + δ := by
      simp only [hgdef]; push_cast; ring
    have hd2e : (d₂ : ℤ) = δ + e := by rw [hd₂]; push_cast; ring
    rw [hstepeq, hd2e]; linarith [hcast]
  have hlohi : (0 : ℤ) ≤ (d₂ : ℤ) - 1 := by
    have h1 : (1 : ℤ) ≤ (d₂ : ℤ) := by exact_mod_cast hd2pos
    omega
  obtain ⟨j, hjN, hjlo, hjhi⟩ :=
    discrete_ivt hg0 hgN hlohi hstep (by omega)
  -- decode: `w_j := wmax(s_j) − g j` lies in the window `W_{s_j}`
  set sj : ℕ := s₀ + j * e with hsjdef
  have hwj_le : (w₀ : ℤ) - δ * j ≤ wmax h k sj := by
    simp only [hgdef, ← hsjdef] at hjlo; linarith
  have hwj_ge : wmin h k sj ≤ (w₀ : ℤ) - δ * j := by
    obtain ⟨wa, wb, hwa, hwb, hwab⟩ := hwidth sj (by simp only [hsjdef]; omega)
    have hmn := wmin_le hwa
    have hmx := le_wmax hwb
    simp only [hgdef, ← hsjdef] at hjhi
    have hd2m1 : (d₂ : ℤ) - 1 ≤ (wmax h k sj : ℤ) - (wmin h k sj : ℤ) := by
      have : (wmin h k sj) + (d₂ - 1) ≤ wmax h k sj := by omega
      have hcast : ((wmin h k sj : ℤ)) + ((d₂ : ℤ) - 1) ≤ (wmax h k sj : ℤ) := by
        have h1 : ((wmin h k sj : ℤ)) + ((d₂ : ℤ) - 1) = ((wmin h k sj + (d₂ - 1) : ℕ) : ℤ) := by
          push_cast; omega
        rw [h1]; exact_mod_cast this
      linarith
    linarith
  -- `w_j : ℕ` with `x' = δ·sj + e·w_j`
  set wj : ℕ := w₀ - δ * j with hwjdef
  have hwjnn : δ * j ≤ w₀ := by
    have : (0 : ℤ) ≤ (w₀ : ℤ) - δ * j := le_trans (by positivity) hwj_ge
    have : (δ * j : ℤ) ≤ w₀ := by linarith
    exact_mod_cast this
  have hwjcast : ((wj : ℤ)) = (w₀ : ℤ) - δ * j := by simp only [hwjdef]; push_cast [hwjnn]; ring
  have hwj_mem : wj ∈ Wset h k sj := by
    apply Wset_interval h k sj (wmin_mem hk0 sj) (wmax_mem hk0 sj)
    · rw [← Nat.cast_le (α := ℤ), hwjcast]; exact hwj_ge
    · rw [← Nat.cast_le (α := ℤ), hwjcast]; exact hwj_le
  have hx'eq : x' = δ * sj + e * wj := by
    have h1 : (x' : ℤ) = δ * sj + e * wj := by
      have hesj : (e : ℤ) * w₀ = x' - δ * s₀ := by
        rw [← Nat.cast_mul, hew₀]; push_cast [hle₀]; ring
      rw [hwjcast]
      simp only [hsjdef]
      push_cast
      ring_nf
      ring_nf at hesj
      linarith
    exact_mod_cast h1
  -- conclude `x ∈ kA`
  rw [hxx', hx'eq, ← Nat.add_assoc]
  exact mem_kFold_of_Wset hgaps h δ e hgap hwj_mem

/-- A **palindromic prefix** `h[1..τ]`: `h (i+1) = h (τ - i)` for every interior
position `i < τ`. This is exactly the `W₂(τ) = 0` shape (the corresponding paper lemma). -/
def IsPalindromePrefix (h : ℕ → Bool) (τ : ℕ) : Prop :=
  ∀ i, i < τ → h (i + 1) = h (τ - i)

/-- **2.9 border step 1** (`W₂(τ) = 0 ⟹ palindrome`). If the antidiagonal sum
`qCount i + qCount (τ - i)` is constant in `i` — given in adjacent-difference
form — then `h[1..τ]` is a palindromic prefix. Pure `qCount_succ` bit algebra. -/
theorem palindrome_of_qCount_const {h : ℕ → Bool} {τ : ℕ}
    (hconst : ∀ i, i < τ →
      qCount h (i + 1) + qCount h (τ - (i + 1)) = qCount h i + qCount h (τ - i)) :
    IsPalindromePrefix h τ := by
  intro i hi
  have hc := hconst i hi
  have hq1 := qCount_succ h i
  have hq2 := qCount_succ h (τ - (i + 1))
  rw [show τ - (i + 1) + 1 = τ - i from by omega] at hq2
  have hbit : (if h (i + 1) then (1 : ℕ) else 0) = (if h (τ - i) then 1 else 0) := by
    omega
  cases hb1 : h (i + 1) <;> cases hb2 : h (τ - i) <;> simp_all

/-- **2.9 border step 2** (`border ⟹ period`). Two palindromic prefixes, at
`τ` and `τ - Δ`, force period `Δ` on the window `(Δ, τ]`: `h m = h (m - Δ)`.
(Classical border–period duality, done by index chasing with `i := τ - m`.) -/
theorem period_of_two_palindromes {h : ℕ → Bool} {τ Δ : ℕ}
    (hΔ : 0 < Δ) (hΔτ : Δ ≤ τ)
    (hτ : IsPalindromePrefix h τ) (hτΔ : IsPalindromePrefix h (τ - Δ)) :
    ∀ m, Δ < m → m ≤ τ → h m = h (m - Δ) := by
  intro m hm1 hm2
  have e1 := hτ (τ - m) (by omega)
  have e2 := hτΔ (τ - m) (by omega)
  rw [show τ - (τ - m) = m from by omega] at e1
  rw [show τ - Δ - (τ - m) = m - Δ from by omega] at e2
  rw [← e1]; exact e2

/-- **2.9 border step 3** (`period windows ⟹ eventual periodicity`).
Arbitrarily long period-`Δ` windows (from an unbounded family of palindromes)
make `h` eventually periodic with period `Δ` — the shape refuted by `hnp`. -/
theorem eventuallyPeriodic_of_period_windows {h : ℕ → Bool} {Δ : ℕ} (hΔ : 0 < Δ)
    (hwin : ∀ N, ∃ τ, N ≤ τ ∧ ∀ m, Δ < m → m ≤ τ → h m = h (m - Δ)) :
    ∃ p, 0 < p ∧ ∃ T, ∀ n, T ≤ n → h (n + p) = h n := by
  refine ⟨Δ, hΔ, 1, fun n hn => ?_⟩
  obtain ⟨τ, hτN, hτp⟩ := hwin (n + Δ)
  have hstep := hτp (n + Δ) (by omega) (by omega)
  rwa [show n + Δ - Δ = n from by omega] at hstep

/-- **the corresponding paper lemma (even boundary `d₂ = k`)**: when the repetition trick falls one
short (`2⌊(k-1)/2⌋ = k-2 < d₂-1`), the width bound still holds for large `s`.
Proof by contradiction: if it fails at unboundedly many `s`, the two config
families (config (1) `(k/2-1)` extremal pairs + free pair at `τ`, config (2)
with one pair shifted to `σ₁`, free pair at `τ-Δ`) force `W₂(τ)=W₂(τ-Δ)=0`,
hence palindromic prefixes at `τ, τ-Δ` (`palindrome_of_qCount_const`), hence
period `Δ` on `(Δ, τ]` (`period_of_two_palindromes`); `τ(s) → ∞` gives eventual
periodicity (`eventuallyPeriodic_of_period_windows`), contradicting `hnp`. -/
theorem width_even_boundary {k d₂ : ℕ} (h : ℕ → Bool) (hk : 3 ≤ k)
    (hd : d₂ ≤ k) (hbdry : 2 * ((k - 1) / 2) < d₂ - 1)
    (σ₀ : ℕ) (hσ₀ : WidthTwoAt h σ₀)
    (hnp : ¬ ∃ p, 0 < p ∧ ∃ T, ∀ n, T ≤ n → h (n + p) = h n)
    (hunbal : ∀ T, ∃ σ, T ≤ σ ∧ WidthTwoAt h σ) :
    ∃ S₀, ∀ s, S₀ ≤ s → ∃ w w', w ∈ Wset h k s ∧ w' ∈ Wset h k s ∧
      w + (d₂ - 1) ≤ w' := by
  obtain ⟨i, j, i', j', hij, hij', hwidth⟩ := hσ₀
  obtain ⟨σ₁, hσ₁ge, i₁, j₁, i₁', j₁', hij1, hij1', hwidth1⟩ := hunbal (σ₀ + 1)
  set L := qCount h i + qCount h j with hL
  set H := qCount h i' + qCount h j' with hH
  set L₁ := qCount h i₁ + qCount h j₁ with hL1
  set H₁ := qCount h i₁' + qCount h j₁' with hH1
  set Δ := σ₁ - σ₀ with hΔdef
  have hΔ : 0 < Δ := by omega
  -- the boundary hypothesis forces `k` even and `d₂ = k`
  have hkev : k % 2 = 0 := by omega
  have hd2k : d₂ = k := by omega
  have hLmem : L ∈ Wset h 2 σ₀ := hij ▸ Wset.pair h i j
  have hHmem : H ∈ Wset h 2 σ₀ := hij' ▸ Wset.pair h i' j'
  have hL1mem : L₁ ∈ Wset h 2 σ₁ := hij1 ▸ Wset.pair h i₁ j₁
  have hH1mem : H₁ ∈ Wset h 2 σ₁ := hij1' ▸ Wset.pair h i₁' j₁'
  by_contra hcon
  push Not at hcon
  apply hnp
  apply eventuallyPeriodic_of_period_windows hΔ
  intro N
  obtain ⟨s, hsge, hsnar⟩ := hcon (N + (k / 2 - 1) * σ₀ + σ₁ + Δ)
  set τ := s - (k / 2 - 1) * σ₀ with hτdef
  refine ⟨τ, by omega, ?_⟩
  -- **The core** : with the width `≤ k-2`, any base config with a `(k-2)`-spread
  -- plus a free pair on antidiagonal `τ'` forces that antidiagonal constant,
  -- i.e. `h[1..τ']` palindromic.
  have key : ∀ blo bhi B τ' : ℕ, blo ∈ Wset h (k - 2) B → bhi ∈ Wset h (k - 2) B →
      blo + (k - 2) ≤ bhi → B + τ' = s → IsPalindromePrefix h τ' := by
    intro blo bhi B τ' hblo hbhi hspread hBs
    apply palindrome_of_qCount_const
    intro x hx
    have mk : ∀ z, z ≤ τ' → ∀ b, b ∈ Wset h (k - 2) B →
        b + (qCount h z + qCount h (τ' - z)) ∈ Wset h k s := by
      intro z hz b hb
      have hpz : qCount h z + qCount h (τ' - z) ∈ Wset h 2 τ' :=
        Wset.congr_mem rfl (show z + (τ' - z) = τ' from by omega) (Wset.pair h z (τ' - z))
      exact Wset.congr_mem (show k - 2 + 2 = k from by omega) hBs (Wset.add hb hpz)
    have h1 := hsnar _ _ (mk x (by omega) blo hblo) (mk (x + 1) (by omega) bhi hbhi)
    have h2 := hsnar _ _ (mk (x + 1) (by omega) blo hblo) (mk x (by omega) bhi hbhi)
    omega
  -- config family (1) at `τ` : `(k/2-1)` pairs at `σ₀`
  have hcoef : (k / 2 - 1) * σ₀ = (k / 2 - 2) * σ₀ + σ₀ := by
    rw [show k / 2 - 1 = (k / 2 - 2) + 1 from by omega, Nat.succ_mul]
  have hspread1 : ∀ x y : ℕ, x + 2 ≤ y → (k / 2 - 1) * x + (k - 2) ≤ (k / 2 - 1) * y := by
    intro x y hxy
    have hm := Nat.mul_le_mul_left (k / 2 - 1) hxy
    have he : (k / 2 - 1) * (x + 2) = (k / 2 - 1) * x + (k / 2 - 1) * 2 := by ring
    have h2 : (k / 2 - 1) * 2 = k - 2 := by omega
    omega
  have hpalτ : IsPalindromePrefix h τ :=
    key ((k / 2 - 1) * L) ((k / 2 - 1) * H) ((k / 2 - 1) * σ₀) τ
      (Wset.congr_mem (show (k / 2 - 1) * 2 = k - 2 from by omega) rfl
        (Wset.nsmul (k / 2 - 1) hLmem))
      (Wset.congr_mem (show (k / 2 - 1) * 2 = k - 2 from by omega) rfl
        (Wset.nsmul (k / 2 - 1) hHmem))
      (hspread1 L H hwidth) (by omega)
  -- config family (2) at `τ - Δ` : `(k/2-2)` pairs at `σ₀` + one pair at `σ₁`
  have hbaseLo : (k / 2 - 2) * L + L₁ ∈ Wset h (k - 2) ((k / 2 - 2) * σ₀ + σ₁) :=
    Wset.congr_mem (show (k / 2 - 2) * 2 + 2 = k - 2 from by omega) rfl
      (Wset.add (Wset.nsmul (k / 2 - 2) hLmem) hL1mem)
  have hbaseHi : (k / 2 - 2) * H + H₁ ∈ Wset h (k - 2) ((k / 2 - 2) * σ₀ + σ₁) :=
    Wset.congr_mem (show (k / 2 - 2) * 2 + 2 = k - 2 from by omega) rfl
      (Wset.add (Wset.nsmul (k / 2 - 2) hHmem) hH1mem)
  have hspread2 : (k / 2 - 2) * L + L₁ + (k - 2) ≤ (k / 2 - 2) * H + H₁ := by
    have hm := Nat.mul_le_mul_left (k / 2 - 2) hwidth
    have he : (k / 2 - 2) * (L + 2) = (k / 2 - 2) * L + (k / 2 - 2) * 2 := by ring
    have h2 : (k / 2 - 2) * 2 = k - 4 := by omega
    omega
  have hpalτΔ : IsPalindromePrefix h (τ - Δ) :=
    key ((k / 2 - 2) * L + L₁) ((k / 2 - 2) * H + H₁) ((k / 2 - 2) * σ₀ + σ₁) (τ - Δ)
      hbaseLo hbaseHi hspread2 (by omega)
  exact period_of_two_palindromes hΔ (by omega) hpalτ hpalτΔ

/-- **the corresponding paper lemma(a) + 2.9**: width production. If some antidiagonal has
`W₂(σ₀) ≥ 2` then (odd `k`, or even `k` with `d₂ ≤ k−1`, or even `k` at the
boundary `d₂ = k` given every tail unbalanced and non-periodicity — Lemma
2.9's palindrome/border/period argument) the sweep hypothesis holds. -/
theorem width_of_unbalanced {k d₂ : ℕ} (h : ℕ → Bool) (hk : 3 ≤ k)
    (hd : d₂ ≤ k) (σ₀ : ℕ) (hσ₀ : WidthTwoAt h σ₀)
    (hnp : ¬ ∃ p, 0 < p ∧ ∃ T, ∀ n, T ≤ n → h (n + p) = h n)
    (hunbal : ∀ T, ∃ σ, T ≤ σ ∧ WidthTwoAt h σ) :
    ∃ S₀, ∀ s, S₀ ≤ s → ∃ w w', w ∈ Wset h k s ∧ w' ∈ Wset h k s ∧
      w + (d₂ - 1) ≤ w' := by
  obtain ⟨i, j, i', j', hij, hij', hwidth⟩ := hσ₀
  set p := (k - 1) / 2 with hp
  set L := qCount h i + qCount h j with hL
  set H := qCount h i' + qCount h j' with hH
  rcases Nat.lt_or_ge (d₂ - 1) (2 * p + 1) with hcov | hbdry
  · -- **2.8(a) repetition**: `p` low/high pairs at `σ₀` + a free block absorbing `s`.
    refine ⟨p * σ₀, fun s hs => ?_⟩
    obtain ⟨F, hF⟩ := Wset.nonempty (show 0 < k - 2 * p by omega) (s - p * σ₀)
    have hLmem : L ∈ Wset h 2 σ₀ := hij ▸ Wset.pair h i j
    have hHmem : H ∈ Wset h 2 σ₀ := hij' ▸ Wset.pair h i' j'
    have hcount : p * 2 + (k - 2 * p) = k := by omega
    have hsum : p * σ₀ + (s - p * σ₀) = s := by omega
    refine ⟨p * L + F, p * H + F,
      Wset.congr_mem hcount hsum (Wset.add (Wset.nsmul p hLmem) hF),
      Wset.congr_mem hcount hsum (Wset.add (Wset.nsmul p hHmem) hF), ?_⟩
    -- `p·H ≥ p·(L+2) = p·L + 2p ≥ p·L + (d₂-1)`
    have : p * L + 2 * p ≤ p * H := by
      have := Nat.mul_le_mul_left p hwidth; ring_nf at this ⊢; omega
    omega
  · -- **2.9 boundary** (`even k`, `d₂ = k`): repetition falls one short.
    exact width_even_boundary h hk hd (by omega) σ₀
      ⟨i, j, i', j', hij, hij', hwidth⟩ hnp hunbal

end Proof
end Erdos1112
