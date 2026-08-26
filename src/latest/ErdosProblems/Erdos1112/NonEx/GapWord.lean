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
The non-existence reductions: tail alphabet `G∞`, the tail index,
gcd rescaling, the one-letter case, and the eventually-periodic case.
Paper: the non-existence section.

Interface notes:
* `tailCovering_of_single_letter` and `tailCovering_of_eventually_periodic`
  require `hd₁ : 1 ≤ d₁`. Without it both statements are *false* (with
  `d₁ = 0` the sequence may be eventually constant — e.g. all gaps eventually
  `0` — making `kA` finite, while the hypotheses hold). `NonEx/Main.lean` has
  `hd₁` ambiently available.
* `tailCovering_of_rescaled` uses the additive shape
  `∀ n, a (T + n) = c + g * a' n` for an arbitrary offset `c`, which the
  caller realizes with e.g. `c := a T`, `a' n := (a (T+n) - a T) / g` (or any
  positive-base variant). Phrasing it additively avoids `ℕ`-subtraction
  truncation; no gap or positivity hypotheses on `a'` are needed.
* Each lemma is proved in normalized form (`tailCoveringN_*`, reduced residue
  `ρ < m`; see `NonEx/Kit.lean`) and then weakened to the `TailCovering`
  form under the original name.
-/
import ErdosProblems.Erdos1112.NonEx.Kit

namespace Erdos1112
namespace Proof

/-- The tail alphabet of the gap word: values occurring infinitely often. -/
def tailAlphabet (a : ℕ → ℕ) : Set ℕ :=
  {d | ∀ N, ∃ n, N ≤ n ∧ gap a n = d}

section Reductions

variable {k d₁ d₂ : ℕ} {a : ℕ → ℕ}

/-- Tail-alphabet letters obey the gap bounds. -/
lemma mem_tailAlphabet_bounds (h : HasGapsIn d₁ d₂ a) {x : ℕ}
    (hx : x ∈ tailAlphabet a) : d₁ ≤ x ∧ x ≤ d₂ := by
  obtain ⟨n, -, rfl⟩ := hx 0
  exact ⟨h.le_gap n, h.gap_le n⟩

/-- Past some index, every gap value belongs to the tail alphabet
(the tail index; classical, uses finiteness of `[d₁, d₂]`). -/
theorem exists_tail_index (h : HasGapsIn d₁ d₂ a) :
    ∃ T, ∀ n, T ≤ n → gap a n ∈ tailAlphabet a := by
  classical
  have key : ∀ d, d ∉ tailAlphabet a → ∃ N, ∀ n, N ≤ n → gap a n ≠ d := by
    intro d hd
    simp only [tailAlphabet, Set.mem_ofPred_eq, not_forall] at hd
    obtain ⟨N, hN⟩ := hd
    push Not at hN
    exact ⟨N, hN⟩
  set F : ℕ → ℕ := fun d =>
    if hd : d ∈ tailAlphabet a then 0 else (key d hd).choose with hF
  refine ⟨(Finset.Icc d₁ d₂).sup F, fun n hn => ?_⟩
  by_contra hbad
  have hmem : gap a n ∈ Finset.Icc d₁ d₂ :=
    Finset.mem_Icc.mpr ⟨h.le_gap n, h.gap_le n⟩
  have hFn : F (gap a n) ≤ (Finset.Icc d₁ d₂).sup F := Finset.le_sup hmem
  have hFval : F (gap a n) = (key _ hbad).choose := by
    rw [hF]; simp [hbad]
  exact (key _ hbad).choose_spec n (by omega) rfl

/-- **One letter**, normalized form: a single-letter tail
alphabet gives an AP tail, hence tail-covering with `m = δ`. -/
theorem tailCoveringN_of_single_letter (hk : 0 < k) (hd₁ : 1 ≤ d₁)
    (h : HasGapsIn d₁ d₂ a) (hone : ∃ δ, tailAlphabet a = {δ}) :
    TailCoveringN k a := by
  obtain ⟨δ, hδ⟩ := hone
  obtain ⟨T, hT⟩ := exists_tail_index h
  have hgapT : ∀ n, T ≤ n → gap a n = δ := by
    intro n hn
    have := hT n hn
    rwa [hδ, Set.mem_singleton_iff] at this
  have hδpos : 0 < δ := by
    have h1 := hgapT T le_rfl
    have h2 := h.le_gap T
    omega
  have key : ∀ j, a (T + j) = a T + δ * j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have h3 : T + (j + 1) = T + j + 1 := by omega
        rw [h3, h.succ_eq_add_gap (T + j), hgapT _ (Nat.le_add_right _ _), ih]
        ring
  exact tailCoveringN_of_AP hδpos fun j => kfold_AP_mem hk (fun j => T + j) key j

/-- **Eventually periodic**, normalized form: an eventually
periodic gap word gives tail-covering with `m = ` the period sum
(single-anchor shortcut: `k` copies from one AP). -/
theorem tailCoveringN_of_eventually_periodic (hk : 0 < k) (hd₁ : 1 ≤ d₁)
    (h : HasGapsIn d₁ d₂ a)
    (hper : ∃ p, 0 < p ∧ ∃ T, ∀ n, T ≤ n → gap a (n + p) = gap a n) :
    TailCoveringN k a := by
  obtain ⟨p, hp, T, hT⟩ := hper
  set s := ∑ i ∈ Finset.range p, gap a (T + i) with hs_def
  -- period sum is positive
  have hspos : 0 < s := by
    have h1 : p * d₁ ≤ s := by
      calc p * d₁ = ∑ _i ∈ Finset.range p, d₁ := by
            rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
        _ ≤ s := Finset.sum_le_sum fun i _ => h.le_gap (T + i)
    have h2 := Nat.mul_le_mul hp hd₁
    omega
  -- one-period block advance
  have block : ∀ n, a (n + p) = a n + ∑ i ∈ Finset.range p, gap a (n + i) := by
    intro n
    have h1 := (h.tail n).eq_add_sum_gaps p
    simp only [Nat.add_zero] at h1
    have h2 : ∀ i, gap (fun m => a (n + m)) i = gap a (n + i) := by
      intro i
      change a (n + (i + 1)) - a (n + i) = a (n + i + 1) - a (n + i)
      rw [← Nat.add_assoc]
    rwa [Finset.sum_congr rfl fun i _ => h2 i] at h1
  -- periodicity iterates
  have per_iter : ∀ j i, gap a (T + i + j * p) = gap a (T + i) := by
    intro j
    induction j with
    | zero => intro i; simp
    | succ j ih =>
        intro i
        have h1 : T + i + (j + 1) * p = (T + i + j * p) + p := by
          have : (j + 1) * p = j * p + p := by ring
          omega
        rw [h1, hT _ (by omega), ih i]
  -- the anchored AP
  have key : ∀ j, a (T + j * p) = a T + s * j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have h1 : T + (j + 1) * p = (T + j * p) + p := by
          have : (j + 1) * p = j * p + p := by ring
          omega
        have h3 : ∑ i ∈ Finset.range p, gap a (T + j * p + i) = s := by
          rw [hs_def]
          refine Finset.sum_congr rfl fun i _ => ?_
          have h4 : T + j * p + i = T + i + j * p := by omega
          rw [h4, per_iter j i]
        rw [h1, block (T + j * p), h3, ih]
        ring
  exact tailCoveringN_of_AP hspos fun j => kfold_AP_mem hk (fun j => T + j * p) key j

/-- **the corresponding paper lemma (rescaling)**, normalized form, redesigned interface: if past
`T` the sequence is an affine image `a (T + n) = c + g · a' n` of some `a'`,
then normalized tail-covering transports from `a'` to `a` (class modulus
`g·m'`). No hypotheses on `a'` beyond the covering are needed. -/
theorem tailCoveringN_of_rescaled {k : ℕ} {a : ℕ → ℕ} (T g c : ℕ)
    (hg : 0 < g) (a' : ℕ → ℕ) (ha' : ∀ n, a (T + n) = c + g * a' n)
    (hcov : TailCoveringN k a') : TailCoveringN k a := by
  obtain ⟨m', hm', ρ', hρ', X₀', hX'⟩ := hcov
  have hgm : 0 < g * m' := Nat.mul_pos hg hm'
  refine ⟨g * m', hgm, (k * c + g * ρ') % (g * m'), Nat.mod_lt _ hgm,
    k * c + g * X₀' + g * ρ', fun x hx hmod => ?_⟩
  -- extract the class parameter
  have hle : k * c + g * ρ' ≤ x := by omega
  have hdvd : g * m' ∣ x - (k * c + g * ρ') :=
    (Nat.modEq_iff_dvd' hle).mp
      (show Nat.ModEq (g * m') (k * c + g * ρ') x from hmod.symm)
  obtain ⟨t, ht⟩ := hdvd
  have hxeq : x = k * c + g * ρ' + g * m' * t := by omega
  -- the rescaled target
  set y := ρ' + m' * t with hy
  have hy_mod : y % m' = ρ' := by
    rw [hy, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρ']
  have hy_ge : X₀' ≤ y := by
    have h1 : g * X₀' ≤ g * m' * t := by omega
    have h2 : X₀' ≤ m' * t := by
      have h1' : g * X₀' ≤ g * (m' * t) := by rw [← mul_assoc]; exact h1
      exact Nat.le_of_mul_le_mul_left h1' hg
    omega
  obtain ⟨f, hf⟩ := hX' y hy_ge hy_mod
  -- push the witness through the affine map
  refine ⟨fun j => T + f j, ?_⟩
  have h1 : ∀ j : Fin k, a (T + f j) = c + g * a' (f j) := fun j => ha' (f j)
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    ← Finset.mul_sum, ← hf]
  have hgy : g * y = g * ρ' + g * m' * t := by
    rw [hy, Nat.mul_add, ← mul_assoc]
  omega

/-! ### `TailCovering`-form wrappers -/

/-- **One letter**: a single-letter tail alphabet gives an AP
tail, hence tail-covering. (Requires `hd₁`; see the header note.) -/
theorem tailCovering_of_single_letter (hk : 0 < k) (hd₁ : 1 ≤ d₁)
    (h : HasGapsIn d₁ d₂ a) (hone : ∃ δ, tailAlphabet a = {δ}) :
    TailCovering k a :=
  (tailCoveringN_of_single_letter hk hd₁ h hone).toTailCovering

/-- **Eventually periodic**: an eventually periodic gap word
gives tail-covering. (Requires `hd₁`; see the header note.) -/
theorem tailCovering_of_eventually_periodic (hk : 0 < k) (hd₁ : 1 ≤ d₁)
    (h : HasGapsIn d₁ d₂ a)
    (hper : ∃ p, 0 < p ∧ ∃ T, ∀ n, T ≤ n → gap a (n + p) = gap a n) :
    TailCovering k a :=
  (tailCoveringN_of_eventually_periodic hk hd₁ h hper).toTailCovering

/-- **the corresponding paper lemma (rescaling)**: transport of tail-covering along
`a (T + ·) = c + g · a' ·`. (Additive interface; see the header note.) -/
theorem tailCovering_of_rescaled {k : ℕ} {a : ℕ → ℕ} (T g c : ℕ)
    (hg : 0 < g) (a' : ℕ → ℕ) (ha' : ∀ n, a (T + n) = c + g * a' n)
    (hcov : TailCoveringN k a') : TailCovering k a :=
  (tailCoveringN_of_rescaled T g c hg a' ha' hcov).toTailCovering

end Reductions

end Proof
end Erdos1112
