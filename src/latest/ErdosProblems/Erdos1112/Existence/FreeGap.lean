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
The free-gap lemma. Paper: the existence section.

Formalization note (deviation from the paper, safe direction): instead of the
relevance-interval analysis we take `s₁ := ⌈t / hi⌉₊` and exhibit the single
free gap `(gl, w) := ((t+k)/(s₁+1), t/s₁)`:
  * `w ≤ hi` by the ceiling bound; `hi·t ≤ w·t + d₂²` by its minimality;
  * `w − k ≥ 15/32` (from `hi ≥ d₂ − 1/2`, `d₂² ≤ t/32`, `k ≤ d₂ − 1`);
  * the exact identity `(w − gl)·(s₁+1) = w − k` gives the gap length;
  * `(w − gl)·t ≤ d₂²` and `4d₂² ≤ (hi−lo)·t` place the gap inside `[lo, hi]`;
  * safety of any `γ` in the OPEN gap is pure monotonicity in `s`:
    `s ≤ s₁ ⇒ s·γ < s·w ≤ t` and `s ≥ s₁+1 ⇒ s·γ > s·gl ≥ t + k`.
The closed middle third `[gl + (w−gl)/3, w − (w−gl)/3]` has length
`(w−gl)/3 ≥ d₂/(48t)`. All interior reasoning is `t`-scaled (division-free).
-/
import ErdosProblems.Erdos1112.Existence.Beatty

namespace Erdos1112
namespace Proof

/-- `γ` is safe for target `t`: no positive multiple `s·γ` lands in `[t, t+k]`. -/
def SafeFor (k : ℕ) (t γ : ℝ) : Prop :=
  ∀ s : ℕ, 0 < s → (s * γ : ℝ) ∉ Set.Icc t (t + k)

set_option maxHeartbeats 1600000 in
-- Allow extra elaboration work for the arithmetic and combinatorial case splits.
/-- **Free-gap lemma** (1.2). Let `t ≥ 32·d₂²` and `[lo, hi] ⊆ [d₂ − 1/2, d₂]`
with `hi − lo ≥ 4·d₂²/t`. Then there is a closed subinterval `[lo', hi']` of
length `≥ d₂/(48·t)` all of whose slopes are safe for `t`. -/
theorem exists_safe_subinterval {k d₂ : ℕ} (hk : 1 ≤ k) (hkd : k + 1 ≤ d₂)
    {t lo hi : ℝ} (ht : 32 * (d₂ : ℝ) ^ 2 ≤ t)
    (hlo : (d₂ : ℝ) - 1 / 2 ≤ lo) (hhi : hi ≤ d₂)
    (hlen : 4 * (d₂ : ℝ) ^ 2 / t ≤ hi - lo) :
    ∃ lo' hi', lo ≤ lo' ∧ hi' ≤ hi ∧ (d₂ : ℝ) / (48 * t) ≤ hi' - lo' ∧
      ∀ γ ∈ Set.Icc lo' hi', SafeFor k t γ := by
  -- ambient facts
  have hd₂2 : (2 : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast (by omega : 2 ≤ d₂)
  have hkd' : (k : ℝ) + 1 ≤ (d₂ : ℝ) := by exact_mod_cast hkd
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (by nlinarith) ht
  have hlo32 : (3 : ℝ) / 2 ≤ lo := by linarith
  -- t-scaled interval length: 4d₂² ≤ (hi − lo)·t
  have hlen4 : 4 * (d₂ : ℝ) ^ 2 ≤ (hi - lo) * t := by
    have h := mul_le_mul_of_nonneg_right hlen (le_of_lt ht0)
    rwa [div_mul_cancel₀ _ (ne_of_gt ht0)] at h
  have hlohi : lo < hi := by
    by_contra hcon
    push Not at hcon
    have h := mul_nonpos_of_nonpos_of_nonneg
      (by linarith : hi - lo ≤ 0) (le_of_lt ht0)
    nlinarith
  have hhi0 : (0 : ℝ) < hi := by linarith
  -- the pivotal index; make it opaque immediately after extracting its bounds
  obtain ⟨s₁, h_le, h_lt⟩ : ∃ s₁ : ℕ, t / hi ≤ (s₁ : ℝ) ∧ (s₁ : ℝ) < t / hi + 1 :=
    ⟨⌈t / hi⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one (le_of_lt (div_pos ht0 hhi0))⟩
  have hs₁_pos : (0 : ℝ) < (s₁ : ℝ) := lt_of_lt_of_le (div_pos ht0 hhi0) h_le
  have hs₁1_pos : (0 : ℝ) < (s₁ : ℝ) + 1 := by linarith
  -- multiplicative forms of the ceiling bounds
  have hs₁hi_ge : t ≤ (s₁ : ℝ) * hi := by
    rw [div_le_iff₀ hhi0] at h_le; linarith
  have hs₁hi_lt : (s₁ : ℝ) * hi < t + hi := by
    have h := mul_lt_mul_of_pos_right h_lt hhi0
    rwa [add_mul, one_mul, div_mul_cancel₀ t (ne_of_gt hhi0)] at h
  -- size bounds on s₁
  have hs₁d₂ : t ≤ (s₁ : ℝ) * (d₂ : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hhi (le_of_lt hs₁_pos)
    linarith [hs₁hi_ge]
  have hs₁_ub : ((s₁ : ℝ) + 1) * (d₂ : ℝ) ≤ 3 * t := by
    have hhi_lb : (3 / 4 : ℝ) * (d₂ : ℝ) ≤ hi := by nlinarith
    have h1 : (s₁ : ℝ) * ((3 / 4) * (d₂ : ℝ)) ≤ (s₁ : ℝ) * hi :=
      mul_le_mul_of_nonneg_left hhi_lb (le_of_lt hs₁_pos)
    have h2 : 32 * (d₂ : ℝ) ≤ t := by nlinarith
    nlinarith [hs₁hi_lt]
  -- the gap endpoints, as opaque reals with their defining products
  obtain ⟨w, hw_mul⟩ : ∃ w : ℝ, w * (s₁ : ℝ) = t :=
    ⟨t / (s₁ : ℝ), div_mul_cancel₀ t (ne_of_gt hs₁_pos)⟩
  obtain ⟨gl, hgl_mul⟩ : ∃ gl : ℝ, gl * ((s₁ : ℝ) + 1) = t + (k : ℝ) :=
    ⟨(t + (k : ℝ)) / ((s₁ : ℝ) + 1), div_mul_cancel₀ _ (ne_of_gt hs₁1_pos)⟩
  have hw_pos : (0 : ℝ) < w := by
    by_contra hcon
    push Not at hcon
    have h := mul_nonpos_of_nonpos_of_nonneg hcon (le_of_lt hs₁_pos)
    rw [hw_mul] at h
    linarith
  have hgl_pos : (0 : ℝ) < gl := by
    by_contra hcon
    push Not at hcon
    have h := mul_nonpos_of_nonpos_of_nonneg hcon (le_of_lt hs₁1_pos)
    rw [hgl_mul] at h
    linarith
  have hw_le_hi : w ≤ hi := by
    by_contra hcon
    push Not at hcon
    have h := mul_lt_mul_of_pos_right hcon hs₁_pos
    rw [hw_mul] at h
    nlinarith [hs₁hi_ge]
  -- minimality of s₁, t-scaled: hi·t ≤ w·t + d₂²
  have hw_ge : hi * t ≤ w * t + (d₂ : ℝ) ^ 2 := by
    have hkey : (s₁ : ℝ) * hi * w = t * hi := by
      calc (s₁ : ℝ) * hi * w = w * (s₁ : ℝ) * hi := by ring
        _ = t * hi := by rw [hw_mul]
    have h := mul_lt_mul_of_pos_right hs₁hi_lt hw_pos
    rw [hkey] at h
    have hw_d₂ : hi * w ≤ (d₂ : ℝ) ^ 2 := by
      have a1 : hi * w ≤ hi * hi :=
        mul_le_mul_of_nonneg_left hw_le_hi (by linarith)
      have a2 : hi * hi ≤ (d₂ : ℝ) * (d₂ : ℝ) :=
        mul_le_mul hhi hhi (by linarith) (by linarith)
      calc hi * w ≤ hi * hi := a1
        _ ≤ (d₂ : ℝ) * (d₂ : ℝ) := a2
        _ = (d₂ : ℝ) ^ 2 := by ring
    -- h : t·hi < (t + hi)·w  ⇒  hi·t < w·t + hi·w ≤ w·t + d₂²
    have hexp : (t + hi) * w = t * w + hi * w := by ring
    rw [hexp] at h
    have hc1 : t * hi = hi * t := by ring
    have hc2 : t * w = w * t := by ring
    rw [hc1, hc2] at h
    linarith [hw_d₂]
  -- the k-margin: w − k ≥ 15/32
  have hw_k : (15 / 32 : ℝ) ≤ w - (k : ℝ) := by
    by_contra hcon
    push Not at hcon
    have h1 : w < (d₂ : ℝ) - 17 / 32 := by linarith
    have h2 : w * t < ((d₂ : ℝ) - 17 / 32) * t := mul_lt_mul_of_pos_right h1 ht0
    have h3 : ((d₂ : ℝ) - 1 / 2) * t ≤ hi * t :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt ht0)
    nlinarith [hw_ge]
  -- exact gap-length identity and positivity
  have hlenmul : (w - gl) * ((s₁ : ℝ) + 1) = w - (k : ℝ) := by
    linear_combination hw_mul - hgl_mul
  have hwgl_pos : (0 : ℝ) < w - gl := by
    by_contra hcon
    push Not at hcon
    have h := mul_nonpos_of_nonpos_of_nonneg hcon (le_of_lt hs₁1_pos)
    rw [hlenmul] at h
    linarith
  -- the gap sits above lo: (w − gl)·t ≤ d₂², then gl·t ≥ lo·t
  have ht_le : t ≤ ((s₁ : ℝ) + 1) * (d₂ : ℝ) := by
    rw [add_mul, one_mul]
    linarith [hs₁d₂]
  have hwgl_t : (w - gl) * t ≤ (d₂ : ℝ) ^ 2 := by
    have step1 : (w - gl) * t ≤ (w - gl) * (((s₁ : ℝ) + 1) * (d₂ : ℝ)) :=
      mul_le_mul_of_nonneg_left ht_le (le_of_lt hwgl_pos)
    have step2 : (w - gl) * (((s₁ : ℝ) + 1) * (d₂ : ℝ)) = (w - (k : ℝ)) * (d₂ : ℝ) := by
      rw [← hlenmul]; ring
    have step3 : (w - (k : ℝ)) * (d₂ : ℝ) ≤ (d₂ : ℝ) * (d₂ : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith [hw_le_hi]) (by linarith)
    calc (w - gl) * t ≤ (w - gl) * (((s₁ : ℝ) + 1) * (d₂ : ℝ)) := step1
      _ = (w - (k : ℝ)) * (d₂ : ℝ) := step2
      _ ≤ (d₂ : ℝ) * (d₂ : ℝ) := step3
      _ = (d₂ : ℝ) ^ 2 := by ring
  have hgl_t : lo * t ≤ gl * t := by
    have e1 : (w - gl) * t = w * t - gl * t := by ring
    have e2 : (hi - lo) * t = hi * t - lo * t := by ring
    rw [e1] at hwgl_t
    rw [e2] at hlen4
    linarith [hw_ge, hwgl_t, hlen4, sq_nonneg ((d₂ : ℝ))]
  have hgl_ge_lo : lo ≤ gl := by
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_right hcon ht0
    linarith
  -- the middle third and its length
  refine ⟨gl + (w - gl) / 3, w - (w - gl) / 3, by linarith, by linarith [hw_le_hi], ?_, ?_⟩
  · -- d₂/(48t) ≤ (w−gl)/3, i.e. d₂ ≤ 16·t·(w−gl)
    have hgoal16 : (d₂ : ℝ) ≤ 16 * (t * (w - gl)) := by
      have hint1 : ((s₁ : ℝ) + 1) * (d₂ : ℝ) * (w - gl) ≤ 3 * t * (w - gl) :=
        mul_le_mul_of_nonneg_right hs₁_ub (le_of_lt hwgl_pos)
      have hint2 : (w - gl) * ((s₁ : ℝ) + 1) * (d₂ : ℝ) = (w - (k : ℝ)) * (d₂ : ℝ) := by
        rw [hlenmul]
      have hint3 : (15 / 32 : ℝ) * (d₂ : ℝ) ≤ (w - (k : ℝ)) * (d₂ : ℝ) :=
        mul_le_mul_of_nonneg_right hw_k (by linarith)
      have hchain : (15 / 32 : ℝ) * (d₂ : ℝ) ≤ 3 * (t * (w - gl)) := by
        calc (15 / 32 : ℝ) * (d₂ : ℝ) ≤ (w - (k : ℝ)) * (d₂ : ℝ) := hint3
          _ = (w - gl) * ((s₁ : ℝ) + 1) * (d₂ : ℝ) := hint2.symm
          _ = ((s₁ : ℝ) + 1) * (d₂ : ℝ) * (w - gl) := by ring
          _ ≤ 3 * t * (w - gl) := hint1
          _ = 3 * (t * (w - gl)) := by ring
      linarith [hchain, hd₂2]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 48 * t)]
    have hring : (w - (w - gl) / 3 - (gl + (w - gl) / 3)) * (48 * t) =
        16 * (t * (w - gl)) := by ring
    rw [hring]
    exact hgoal16
  · -- safety of every γ in the closed middle third
    rintro γ ⟨hγl, hγu⟩ s hs
    have hγ_lt_w : γ < w := by linarith [hwgl_pos]
    have hγ_gt_gl : gl < γ := by linarith [hwgl_pos]
    have hs0 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
    rintro ⟨hmem1, hmem2⟩
    rcases Nat.lt_or_ge s (s₁ + 1) with hss | hss
    · -- s ≤ s₁ ⇒ s·γ < t
      have hss' : (s : ℝ) ≤ (s₁ : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hss
      have h11 : (s : ℝ) * γ < (s : ℝ) * w := mul_lt_mul_of_pos_left hγ_lt_w hs0
      have h12 : (s : ℝ) * w ≤ (s₁ : ℝ) * w :=
        mul_le_mul_of_nonneg_right hss' (le_of_lt hw_pos)
      have hcomm : (s₁ : ℝ) * w = t := by linear_combination hw_mul
      linarith [h11, h12, hcomm]
    · -- s ≥ s₁ + 1 ⇒ s·γ > t + k
      have hs' : (s₁ : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast hss
      have h14 : ((s₁ : ℝ) + 1) * gl ≤ (s : ℝ) * gl :=
        mul_le_mul_of_nonneg_right hs' (le_of_lt hgl_pos)
      have h15 : (s : ℝ) * gl < (s : ℝ) * γ := mul_lt_mul_of_pos_left hγ_gt_gl hs0
      have hcomm : ((s₁ : ℝ) + 1) * gl = t + (k : ℝ) := by linear_combination hgl_mul
      linarith [h14, h15, hcomm]

end Proof
end Erdos1112
