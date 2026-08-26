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
Morse–Hedlund, stage 4: quantitative syndeticity input for the uniform-hitting lemma
— Dirichlet step + circle walk.

Design (replaces compactness/ε-net bookkeeping by a walk): Dirichlet
(`Real.exists_int_int_abs_mul_sub_le`) supplies `j ≥ 1`, `K` with
`0 < |jα − K| < b`; if the sign is negative, the multiple
`j' := ⌊1/|θ|⌋₊ · j` flips it (`⌊1/|θ|⌋₊·θ + 1 ∈ (0, |θ|)`, nonzero by
irrationality).  With a positive step `θ < ε/2` the fract-walk
`x_{m+1} = fract(x_m + θ)` enters any arc `(u, u+ε) ⊆ [0,1]` within
`M = 2⌈1/θ⌉₊ + 2` steps: from below `u` it climbs by exact `+θ` (no wrap
possible) and the first crossing lands in `(u, u+θ]`; from above `u` it must
wrap within `⌈1/θ⌉₊` steps, and the wrap successor lies in `[0, θ)` — a hit
if `> u`, otherwise the climb applies.  All uniform in the start point,
hence in the phase `β` and the block position `N`.
-/
import ErdosProblems.Erdos1112.NonEx.TwoLetter.Core

namespace Erdos1112
namespace Proof
namespace MH

/-- Positive Dirichlet step below `b` for irrational `α`.
Route: `exists_nat_gt (1/b)`; `Real.exists_int_int_abs_mul_sub_le`;
nonzeroness via `(hα.natCast_mul _).ne_int`; sign flip via `⌊1/(−θ)⌋₊`
multiple as in the module docstring. -/
theorem exists_pos_step {α : ℝ} (hα : Irrational α) {b : ℝ}
    (hb0 : 0 < b) (hb : b ≤ 1 / 2) :
    ∃ (j : ℕ) (K : ℤ), 1 ≤ j ∧ 0 < (j : ℝ) * α - K ∧ (j : ℝ) * α - K < b := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (1 / b)
  have hn₀pos : 0 < n₀ := by
    rcases Nat.eq_zero_or_pos n₀ with h | h
    · exfalso; rw [h] at hn₀; simp only [Nat.cast_zero] at hn₀
      have : (0 : ℝ) < 1 / b := by positivity
      linarith
    · exact h
  obtain ⟨j₀, k₀, hk₀pos, hk₀n, habs⟩ := Real.exists_int_int_abs_mul_sub_le α hn₀pos
  have hk₀ne : k₀ ≠ 0 := by omega
  have hb' : (1 : ℝ) / (n₀ + 1) < b := by
    rw [div_lt_iff₀ (by positivity)]
    have h1 : 1 < n₀ * b := (div_lt_iff₀ hb0).mp hn₀
    nlinarith [h1, hb0]
  have hθb : |(k₀ : ℝ) * α - j₀| < b := lt_of_le_of_lt habs hb'
  have hθne : (k₀ : ℝ) * α - j₀ ≠ 0 := sub_ne_zero.mpr ((hα.intCast_mul hk₀ne).ne_int j₀)
  have hcastk : ((k₀.toNat : ℕ) : ℝ) = (k₀ : ℝ) := by
    have := Int.toNat_of_nonneg (le_of_lt hk₀pos); exact_mod_cast this
  rcases lt_or_gt_of_ne hθne with hneg | hpos
  · -- θ < 0: flip via `M = ⌊1/(-θ)⌋₊`
    set θ' : ℝ := -((k₀ : ℝ) * α - j₀) with hθ'
    have hθ'0 : 0 < θ' := by rw [hθ']; linarith
    have hθ'b : θ' < b := by rw [hθ']; rw [abs_lt] at hθb; linarith
    set M : ℕ := ⌊1 / θ'⌋₊ with hM_def
    have hinv1 : 1 < 1 / θ' := by rw [lt_div_iff₀ hθ'0]; linarith
    have hM1 : 1 ≤ M := by
      rw [hM_def]; exact Nat.le_floor (by exact_mod_cast le_of_lt hinv1)
    have hMle : (M : ℝ) * θ' ≤ 1 := by
      have hfl : (M : ℝ) ≤ 1 / θ' := by
        rw [hM_def]; exact Nat.floor_le (le_of_lt (div_pos one_pos hθ'0))
      calc (M : ℝ) * θ' ≤ (1 / θ') * θ' := mul_le_mul_of_nonneg_right hfl (le_of_lt hθ'0)
        _ = 1 := by field_simp
    have hMgt : 1 < ((M : ℝ) + 1) * θ' := by
      have hlt : 1 / θ' < (M : ℝ) + 1 := by rw [hM_def]; exact Nat.lt_floor_add_one _
      have hh : (1 / θ') * θ' < ((M : ℝ) + 1) * θ' := mul_lt_mul_of_pos_right hlt hθ'0
      rwa [one_div_mul_cancel (ne_of_gt hθ'0)] at hh
    have hjpos : 1 ≤ M * k₀.toNat := by
      have h1 : 1 ≤ k₀.toNat := by omega
      calc 1 = 1 * 1 := by ring
        _ ≤ M * k₀.toNat := Nat.mul_le_mul hM1 h1
    have hval : (↑(M * k₀.toNat) : ℝ) * α - (↑((M : ℤ) * j₀ - 1) : ℝ) = 1 - M * θ' := by
      push_cast [hcastk]; rw [hθ']; ring
    refine ⟨M * k₀.toNat, (M : ℤ) * j₀ - 1, hjpos, ?_, ?_⟩
    · rw [hval]
      have hne0 : (↑(M * k₀.toNat) : ℝ) * α - (↑((M : ℤ) * j₀ - 1) : ℝ) ≠ 0 :=
        sub_ne_zero.mpr ((hα.natCast_mul (by omega : M * k₀.toNat ≠ 0)).ne_int _)
      rw [hval] at hne0
      rcases lt_or_gt_of_ne (Ne.symm hne0) with h | h
      · exact h
      · linarith
    · rw [hval]
      have hexp : ((M : ℝ) + 1) * θ' = M * θ' + θ' := by ring
      linarith [hMgt, hθ'b, hexp]
  · -- θ > 0: direct
    refine ⟨k₀.toNat, j₀, by omega, ?_, ?_⟩
    · rw [hcastk]; exact hpos
    · rw [hcastk]; rw [abs_lt] at hθb; linarith

/-- The fract-walk with positive step `θ` (with `2θ < ε`) enters every arc
`(u, u+ε) ⊆ [0,1]` within a bounded number of steps, uniformly in the start.
Route: `T := ⌈1/θ⌉₊`, `M := 2T + 2`; step lemmas via `Int.fract_eq_self` /
`Int.fract_sub_intCast`; exact-climb by induction; first crossing by
`Nat.find`; wrap analysis as in the module docstring. -/
theorem walk_enters {θ ε : ℝ} (hθ0 : 0 < θ) (hθε : 2 * θ < ε) :
    ∃ M : ℕ, ∀ x : ℕ → ℝ, (∀ m, x (m + 1) = Int.fract (x m + θ)) →
      0 ≤ x 0 → x 0 < 1 → ∀ u : ℝ, 0 ≤ u → u + ε ≤ 1 →
      ∃ m, m ≤ M ∧ x m ∈ Set.Ioo u (u + ε) := by
  classical
  refine ⟨⌊2 / θ⌋₊ + 2, fun x hx hx0 hx1 u hu hue => ?_⟩
  set M₀ : ℕ := ⌊2 / θ⌋₊ + 2 with hM₀
  have hMθ : 2 < (M₀ : ℝ) * θ := by
    have h1 : 2 / θ < (⌊2 / θ⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (2 / θ)
    have h2 : (2 / θ) * θ = 2 := by field_simp
    have h3 := mul_lt_mul_of_pos_right h1 hθ0
    rw [hM₀]; push_cast; nlinarith [h3, h2, hθ0]
  -- unwrap: `y m = x 0 + m θ`, so `x m = fract (y m)`
  set y : ℕ → ℝ := fun m => x 0 + m * θ with hy_def
  have hkey : ∀ z : ℝ, Int.fract (Int.fract z + θ) = Int.fract (z + θ) := by
    intro z
    have harg : Int.fract z + θ = (z + θ) - ((⌊z⌋ : ℤ) : ℝ) := by
      rw [← Int.self_sub_floor]; ring
    rw [harg, Int.fract_sub_intCast]
  have hxy : ∀ m, x m = Int.fract (y m) := by
    intro m
    induction m with
    | zero =>
        simp only [hy_def, Nat.cast_zero, zero_mul, add_zero]
        exact (Int.fract_eq_self.mpr ⟨hx0, hx1⟩).symm
    | succ m ih =>
        rw [hx m, ih, hkey]
        congr 1
        simp only [hy_def]; push_cast; ring
  -- first crossing of `u + 1`
  have hcrossM : u + 1 < y M₀ := by
    simp only [hy_def]; nlinarith [hMθ, hx0, hue, hθε, hθ0]
  have hcross : ∃ m, u + 1 < y m := ⟨M₀, hcrossM⟩
  set m := Nat.find hcross with hm_def
  have hm_spec : u + 1 < y m := Nat.find_spec hcross
  have hm_le : m ≤ M₀ := Nat.find_le hcrossM
  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso; rw [h] at hm_spec
      simp only [hy_def, Nat.cast_zero, zero_mul, add_zero] at hm_spec
      linarith
    · exact h
  have hm_prev : ¬ (u + 1 < y (m - 1)) := Nat.find_min hcross (by omega)
  have hyu1 : y (m - 1) ≤ u + 1 := not_lt.mp hm_prev
  have hymrec : y m = y (m - 1) + θ := by
    simp only [hy_def]; rw [Nat.cast_sub hm_pos]; push_cast; ring
  have hym_hi : y m < u + 1 + ε := by rw [hymrec]; linarith [hyu1, hθε, hθ0]
  -- `y m ∈ (u+1, 2)`, so `fract (y m) = y m - 1`
  have hfloor : ⌊y m⌋ = 1 := by
    rw [Int.floor_eq_iff]
    constructor <;> push_cast <;> [linarith [hm_spec, hu]; linarith [hym_hi, hue]]
  have hxm : x m = y m - 1 := by
    rw [hxy m, ← Int.self_sub_floor, hfloor]; push_cast; ring
  exact ⟨m, hm_le, by rw [hxm]; linarith [hm_spec], by rw [hxm]; linarith [hym_hi]⟩

end MH
end Proof
end Erdos1112
