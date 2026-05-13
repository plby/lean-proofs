/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 907.
https://www.erdosproblems.com/forum/thread/907

Informal authors:
- N. G. de Bruijn

Formal authors:
- Aristotle
- Pietro Monticone

URLs:
- https://www.erdosproblems.com/forum/thread/907#post-5277
- https://gist.githubusercontent.com/pitmonticone/f419ac0a78259498f93fd60d49c0b3ea/raw/959cb0ef93596d9ade256e3cd0f4141e66176e04/Erdos907.lean
-/
/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Aristotle (Harmonic)
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.UniformSpace.Uniformizable

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.longLine false
set_option linter.style.maxHeartbeats false
set_option linter.style.multiGoal false
set_option linter.style.show false

/-!
# Erdős Problem 907

Let `f : ℝ → ℝ` be such that `f(x + h) - f(x)` is continuous for every
`h > 0`. Is it true that `f = g + H` for some continuous `g` and additive
`H` (i.e., `H(x + y) = H(x) + H(y)`)?

## Answer

**Yes.** Answered in the affirmative by de Bruijn (1951).

## References

* N. G. de Bruijn, *Functions whose differences belong to a given class*,
  Nieuw Arch. Wiskunde (2) (1951), 194–218.
* [Erdős Problem #907](https://www.erdosproblems.com/907).
-/

namespace Erdos907

open Filter Topology Set Metric

/-! ## Definitions -/

/-- `H` is additive: `H(x + y) = H(x) + H(y)` for all `x, y`. -/
def IsAdditiveFn (H : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, H (x + y) = H x + H y

/-- The Cauchy difference `f(x + h) - f(x) - f(h) + f(0)`, measuring
deviation from additivity. -/
def cauchyDiff (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  f (x + h) - f x - f h + f 0

/-- `f` has period 1: `f(x + 1) = f(x)` for all `x`. -/
def PeriodicMod1 (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, f (x + 1) = f x

/-- All difference functions `x ↦ f(x + h) - f(x)` are continuous. -/
def HasContinuousDifferences (f : ℝ → ℝ) : Prop :=
  ∀ h : ℝ, Continuous fun x => f (x + h) - f x

/-! ## Step 1: Algebraic properties of the Cauchy difference -/

/-- If `f` has continuous differences, then `cauchyDiff f` is separately
continuous in each variable. -/
lemma cauchyDiff_separately_continuous (f : ℝ → ℝ)
    (hf : HasContinuousDifferences f) :
    (∀ h : ℝ, Continuous fun x => cauchyDiff f x h) ∧
    (∀ x : ℝ, Continuous fun h => cauchyDiff f x h) := by
  unfold cauchyDiff
  constructor
  · intro h
    exact ((hf h).sub continuous_const).add continuous_const
  · intro x
    have : Continuous fun h => f (h + x) - f h := hf x
    have : Continuous fun h => f (h + x) - f h - f x + f 0 :=
      (this.sub continuous_const).add continuous_const
    convert this using 1
    ext h; ring_nf

/-! ## Step 2: Baire category argument for separately continuous functions -/

/-- The set of `x` where `φ(x, ·)` has oscillation `≤ 1` at rational
scale `1/(m+1)` on `[-1, 1]` is closed. -/
lemma equicont_set_isClosed (φ : ℝ → ℝ → ℝ)
    (hx : ∀ h : ℝ, Continuous fun x => φ x h) (m : ℕ) :
    IsClosed {x : ℝ | ∀ (q q' : ℚ), (↑q : ℝ) ∈ Icc (-1) 1 → (↑q' : ℝ) ∈ Icc (-1) 1 →
      |(q : ℝ) - q'| ≤ 1 / (m + 1 : ℝ) → |φ x q - φ x q'| ≤ 1} := by
  simp +decide only [setOf_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun hi =>
    isClosed_iInter fun hj => isClosed_iInter fun h => isClosed_le ?_ ?_ <;> continuity

/-- The equicontinuity sets `E_m` cover all of `ℝ`, by uniform
continuity of `φ(x, ·)` on `[-1, 1]`. -/
lemma equicont_sets_cover (φ : ℝ → ℝ → ℝ)
    (hh : ∀ x : ℝ, Continuous fun h => φ x h) :
    ⋃ m : ℕ, {x : ℝ | ∀ (q q' : ℚ), (↑q : ℝ) ∈ Icc (-1) 1 → (↑q' : ℝ) ∈ Icc (-1) 1 →
      |(q : ℝ) - q'| ≤ 1 / (m + 1 : ℝ) → |φ x q - φ x q'| ≤ 1} = univ := by
  ext x
  simp [Set.mem_iUnion];
  obtain ⟨ δ, hδ_pos, hδ ⟩ : ∃ δ > 0, ∀ h h' : ℝ, -1 ≤ h → h ≤ 1 → -1 ≤ h' → h' ≤ 1 → |h - h'| < δ → |φ x h - φ x h'| < 1 := by
    have := Metric.uniformContinuousOn_iff.mp ( isCompact_Icc.uniformContinuousOn_of_continuous ( show ContinuousOn ( fun h => φ x h ) ( Set.Icc ( -1 ) 1 ) from Continuous.continuousOn ( hh x ) ) ) 1 zero_lt_one; aesop;
  exact ⟨ ⌈δ⁻¹⌉₊, fun q q' hq hq' hq'' hq''' h => le_of_lt <| hδ q q' hq hq' hq'' hq''' <| lt_of_le_of_lt h <| inv_lt_of_inv_lt₀ hδ_pos <| by linarith [ Nat.le_ceil ( δ⁻¹ ) ] ⟩

set_option maxHeartbeats 800000 in
/-- From equicontinuity on a set with nonempty interior, derive
the existence of a joint continuity point. -/
lemma joint_continuity_from_equicont (φ : ℝ → ℝ → ℝ)
    (hx : ∀ h : ℝ, Continuous fun x => φ x h)
    (hh : ∀ x : ℝ, Continuous fun h => φ x h)
    (m : ℕ)
    (a : ℝ) (ha : a ∈ interior {x : ℝ | ∀ (q q' : ℚ), (↑q : ℝ) ∈ Icc (-1) 1 →
      (↑q' : ℝ) ∈ Icc (-1) 1 → |(q : ℝ) - q'| ≤ 1 / (m + 1 : ℝ) →
      |φ x q - φ x q'| ≤ 1}) :
    ∃ p : ℝ × ℝ, ContinuousAt (Function.uncurry φ) p := by
  by_contra h_contra
  push Not at h_contra
  generalize_proofs at *;
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∈ interior {x : ℝ | ∀ q q' : ℚ, (q : ℝ) ∈ Icc (-1) 1 → (q' : ℝ) ∈ Icc (-1) 1 → |(q : ℝ) - q'| ≤ 1 / (m + 1) → |φ x q - φ x q'| ≤ 1} := by
    use a;
  obtain ⟨r, hr⟩ : ∃ r > 0, ∀ x, abs (x - x₀) < r → ∀ q q' : ℚ, (q : ℝ) ∈ Icc (-1) 1 → (q' : ℝ) ∈ Icc (-1) 1 → |(q : ℝ) - q'| ≤ 1 / (m + 1) → |φ x q - φ x q'| ≤ 1 := by
    exact Metric.mem_nhds_iff.mp ( mem_interior_iff_mem_nhds.mp hx₀ )
  generalize_proofs at *; (
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ ∈ Metric.ball x₀ r, ∀ k : ℕ, ∃ m : ℕ, x₁ ∈ interior {x : ℝ | ∀ q q' : ℚ, (q : ℝ) ∈ Icc (-k : ℝ) k → (q' : ℝ) ∈ Icc (-k : ℝ) k → |(q : ℝ) - q'| ≤ 1 / (m + 1) → |φ x q - φ x q'| ≤ 1 / (k + 1)} := by
    have h_baire : ∀ k : ℕ, Dense (⋃ m : ℕ, interior {x : ℝ | ∀ q q' : ℚ, (q : ℝ) ∈ Icc (-k : ℝ) k → (q' : ℝ) ∈ Icc (-k : ℝ) k → |(q : ℝ) - q'| ≤ 1 / (m + 1) → |φ x q - φ x q'| ≤ 1 / (k + 1)}) := by
      intro k
      have h_cover : ⋃ m : ℕ, {x : ℝ | ∀ q q' : ℚ, (q : ℝ) ∈ Icc (-k : ℝ) k → (q' : ℝ) ∈ Icc (-k : ℝ) k → |(q : ℝ) - q'| ≤ 1 / (m + 1) → |φ x q - φ x q'| ≤ 1 / (k + 1)} = Set.univ := by
        ext x
        simp [Set.mem_iUnion];
        have h_eq_cont_at_x : ∀ ε > 0, ∃ δ > 0, ∀ h h' : ℝ, -k ≤ h → h ≤ k → -k ≤ h' → h' ≤ k → |h - h'| < δ → |φ x h - φ x h'| < ε := by
          have h_eq_cont_at_x : UniformContinuousOn (fun h => φ x h) (Set.Icc (-k : ℝ) k) := by
            exact ( isCompact_Icc.uniformContinuousOn_of_continuous ( hh x |> Continuous.continuousOn ) )
          generalize_proofs at *; (
          exact fun ε ε_pos => by rcases Metric.uniformContinuousOn_iff.mp h_eq_cont_at_x ε ε_pos with ⟨ δ, δ_pos, hδ ⟩ ; exact ⟨ δ, δ_pos, fun h h' hh₁ hh₂ hh₃ hh₄ hh₅ => hδ h ⟨ hh₁, hh₂ ⟩ h' ⟨ hh₃, hh₄ ⟩ hh₅ ⟩ ;)
        generalize_proofs at *; (
        obtain ⟨ δ, hδ_pos, hδ ⟩ := h_eq_cont_at_x ( ( k + 1 : ℝ ) ⁻¹ ) ( by positivity );
        exact ⟨ ⌈δ⁻¹⌉₊, fun q q' hq hq' hq'' hq''' hq'''' => le_of_lt <| hδ q q' ( mod_cast hq ) ( mod_cast hq' ) ( mod_cast hq'' ) ( mod_cast hq''' ) <| lt_of_le_of_lt hq'''' <| inv_lt_of_inv_lt₀ hδ_pos <| by linarith [ Nat.le_ceil ( δ⁻¹ ) ] ⟩)
      generalize_proofs at *; (
      have h_closed : ∀ m : ℕ, IsClosed {x : ℝ | ∀ q q' : ℚ, (q : ℝ) ∈ Icc (-k : ℝ) k → (q' : ℝ) ∈ Icc (-k : ℝ) k → |(q : ℝ) - q'| ≤ 1 / (m + 1) → |φ x q - φ x q'| ≤ 1 / (k + 1)} := by
        intro m
        simp [Set.setOf_forall];
        refine isClosed_iInter fun q => isClosed_iInter fun q' => isClosed_iInter fun hq =>
          isClosed_iInter fun hq' => isClosed_iInter fun hq'' => isClosed_iInter fun hq''' =>
          isClosed_iInter fun hq'''' => isClosed_le ?_ ?_ <;> continuity
      exact dense_iUnion_interior_of_closed h_closed h_cover)
    generalize_proofs at *; (
    have h_baire : Dense (⋂ k : ℕ, ⋃ m : ℕ, interior {x : ℝ | ∀ q q' : ℚ, (q : ℝ) ∈ Icc (-k : ℝ) k → (q' : ℝ) ∈ Icc (-k : ℝ) k → |(q : ℝ) - q'| ≤ 1 / (m + 1) → |φ x q - φ x q'| ≤ 1 / (k + 1)}) := by
      exact dense_iInter_of_isOpen ( fun k => isOpen_iUnion fun m => isOpen_interior ) h_baire
    generalize_proofs at *; (
    have := h_baire.exists_mem_open ( Metric.isOpen_ball ) ⟨ x₀, Metric.mem_ball_self hr.1 ⟩ ; aesop;))
  generalize_proofs at *; (
  obtain ⟨ hx₁₁, hx₁₂ ⟩ := hx₁; specialize h_contra ( x₁, 0 ) ; simp_all +decide [ ContinuousAt ] ; (
  have h_eq_cont : ∀ ε > 0, ∃ δ > 0, ∀ x, abs (x - x₁) < δ → ∀ h, abs h < δ → abs (φ x h - φ x 0) < ε := by
    intro ε hε
    obtain ⟨k, hk⟩ : ∃ k : ℕ, 1 / (k + 1 : ℝ) < ε / 3 := by
      exact ⟨ ⌊ε⁻¹ * 3⌋₊, by rw [ div_lt_iff₀ ] <;> nlinarith [ Nat.lt_floor_add_one ( ε⁻¹ * 3 ), mul_inv_cancel₀ ( ne_of_gt hε ) ] ⟩
    generalize_proofs at *; (
    obtain ⟨ m, hm ⟩ := hx₁₂ ( k + 1 ) ; simp_all +decide [ mem_interior_iff_mem_nhds, Metric.mem_nhds_iff ] ; (
    obtain ⟨ δ, hδ₁, hδ₂ ⟩ := hm; use Min.min δ ( 1 / ( m + 1 ) ) ; simp_all +decide [ Set.subset_def ] ; (
    refine ⟨by positivity, fun x hx₁ hx₂ h hh₁ hh₂ => ?_⟩
    have h_eq_cont : ∀ q : ℚ, abs (q : ℝ) < (m + 1 : ℝ)⁻¹ → abs (φ x q - φ x 0) ≤ (k + 1 + 1 : ℝ)⁻¹ := by
      intro q hq; specialize hδ₂ x hx₁ q 0; simp_all +decide [ abs_lt ] ;
      exact hδ₂ ( by linarith [ inv_le_one_of_one_le₀ ( by linarith : ( m : ℝ ) + 1 ≥ 1 ) ] ) ( by exact_mod_cast ( by linarith [ inv_le_one_of_one_le₀ ( by linarith : ( m : ℝ ) + 1 ≥ 1 ) ] : ( q : ℝ ) ≤ k + 1 ) ) ( by linarith ) ( by linarith ) ( abs_le.mpr ⟨ by linarith, by linarith ⟩ ) |> le_trans <| by norm_num;
    generalize_proofs at *; (
    obtain ⟨q_n, hq_n⟩ : ∃ q_n : ℕ → ℚ, Filter.Tendsto (fun n => q_n n : ℕ → ℝ) Filter.atTop (nhds h) ∧ ∀ n, abs (q_n n : ℝ) < (m + 1 : ℝ)⁻¹ := by
      have h_dense : ∀ ε > 0, ∃ q : ℚ, abs (q - h) < ε ∧ abs (q : ℝ) < (m + 1 : ℝ)⁻¹ := by
        intro ε hε
        obtain ⟨q, hq⟩ : ∃ q : ℚ, abs (q - h) < min ε ((m + 1 : ℝ)⁻¹ - abs h) := by
          exact exists_rat_btwn ( show h - Min.min ε ( ( m + 1 : ℝ ) ⁻¹ - |h| ) < h by linarith [ lt_min hε ( sub_pos.mpr hh₂ ) ] ) |> fun ⟨ q, hq₁, hq₂ ⟩ => ⟨ q, abs_lt.mpr ⟨ by linarith, by linarith ⟩ ⟩ ;
        generalize_proofs at *; (
        exact ⟨ q, lt_of_lt_of_le hq ( min_le_left _ _ ), by cases abs_cases ( q : ℝ ) <;> cases abs_cases h <;> linarith [ abs_lt.mp hq, min_le_right ε ( ( m + 1 : ℝ ) ⁻¹ - |h| ) ] ⟩)
      generalize_proofs at *; (
      exact ⟨ fun n => Classical.choose ( h_dense ( 1 / ( n + 1 ) ) ( by positivity ) ), tendsto_iff_norm_sub_tendsto_zero.mpr <| squeeze_zero ( fun _ => by positivity ) ( fun n => Classical.choose_spec ( h_dense ( 1 / ( n + 1 ) ) ( by positivity ) ) |>.1.le ) <| tendsto_one_div_add_atTop_nhds_zero_nat, fun n => Classical.choose_spec ( h_dense ( 1 / ( n + 1 ) ) ( by positivity ) ) |>.2 ⟩)
    generalize_proofs at *; (
    have h_cont : Filter.Tendsto (fun n => φ x (q_n n : ℝ)) Filter.atTop (nhds (φ x h)) := by
      exact hh x |> Continuous.continuousAt |> fun h => h.tendsto.comp hq_n.1
    generalize_proofs at *; (
    have h_cont : Filter.Tendsto (fun n => φ x (q_n n : ℝ) - φ x 0) Filter.atTop (nhds (φ x h - φ x 0)) := by
      exact h_cont.sub_const _
    generalize_proofs at *; (
    exact lt_of_le_of_lt ( le_of_tendsto' ( h_cont.abs ) fun n => h_eq_cont _ ( hq_n.2 n ) ) ( by nlinarith [ inv_mul_cancel₀ ( by linarith : ( k : ℝ ) + 1 + 1 ≠ 0 ), inv_mul_cancel₀ ( by linarith : ( k : ℝ ) + 1 ≠ 0 ) ] ))))))))
  generalize_proofs at *; (
  refine h_contra ?_;
  rw [ Metric.tendsto_nhds_nhds ] at *;
  intro ε hε; rcases h_eq_cont ( ε / 2 ) ( half_pos hε ) with ⟨ δ, hδ, H ⟩ ; rcases Metric.continuous_iff.mp ( hx 0 ) x₁ ( ε / 2 ) ( half_pos hε ) with ⟨ δ', hδ', H' ⟩ ; use Min.min δ δ'; simp_all +decide [ Prod.dist_eq ] ;
  exact fun a b ha hb ha' hb' => abs_lt.mpr ⟨ by linarith [ abs_lt.mp ( H a ha b hb ), abs_lt.mp ( H' a ha' ) ], by linarith [ abs_lt.mp ( H a ha b hb ), abs_lt.mp ( H' a ha' ) ] ⟩ ;))))

/-- **Baire category theorem for separate continuity.** Every separately
continuous `φ : ℝ → ℝ → ℝ` has at least one point of joint continuity. -/
lemma separately_continuous_has_joint_continuity_point
    (φ : ℝ → ℝ → ℝ)
    (hx : ∀ h : ℝ, Continuous fun x => φ x h)
    (hh : ∀ x : ℝ, Continuous fun h => φ x h) :
    ∃ p : ℝ × ℝ, ContinuousAt (Function.uncurry φ) p := by
  have hclosed := fun m => equicont_set_isClosed φ hx m
  have hcover := equicont_sets_cover φ hh
  obtain ⟨m, hm⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  obtain ⟨a, ha⟩ := hm
  exact joint_continuity_from_equicont φ hx hh m a ha

/-! ## Step 3: Joint continuity propagates everywhere -/

/-- If `cauchyDiff f` is jointly continuous at one point, then it is
jointly continuous everywhere, by the algebraic identity. -/
lemma cauchyDiff_continuousAt_everywhere (f : ℝ → ℝ)
    (hf : HasContinuousDifferences f)
    (p : ℝ × ℝ) (hp : ContinuousAt (Function.uncurry (cauchyDiff f)) p) :
    ∀ q : ℝ × ℝ, ContinuousAt (Function.uncurry (cauchyDiff f)) q := by
  have h_identity : ∀ u v x₀ h₀ x y : ℝ, cauchyDiff f x y = cauchyDiff f (x₀ + (x-u)) (h₀ + (y-v)) + (f (x + y) - f (x₀ + h₀ + (x-u) + (y-v))) + (f (x₀ + (x-u)) - f x) + (f (h₀ + (y-v)) - f y) := by
    grind +locals;
  intro q
  obtain ⟨u, v⟩ := q
  have h_cont_at : ContinuousAt (fun (x, y) => cauchyDiff f (p.1 + (x-u)) (p.2 + (y-v)) + (f (x + y) - f (p.1 + p.2 + (x-u) + (y-v))) + (f (p.1 + (x-u)) - f x) + (f (p.2 + (y-v)) - f y)) (u, v) := by
    refine ContinuousAt.add (ContinuousAt.add (ContinuousAt.add ?_ ?_) ?_) ?_;
    · convert hp.tendsto.comp ( show Filter.Tendsto ( fun x : ℝ × ℝ => ( p.1 + ( x.1 - u ), p.2 + ( x.2 - v ) ) ) ( nhds ( u, v ) ) ( nhds p ) from Continuous.tendsto' ( by continuity ) _ _ <| by simp +decide ) using 1;
      norm_num [ ContinuousAt ];
      rfl;
    · have h_cont_at : ContinuousAt (fun x => f x - f (x + (p.1 + p.2 - u - v))) (u + v) := by
        have h_cont_at : ContinuousAt (fun x => f (x + (p.1 + p.2 - u - v)) - f x) (u + v) := by
          exact hf _ |> Continuous.continuousAt;
        simpa using h_cont_at.neg;
      convert h_cont_at.tendsto.comp ( show Filter.Tendsto ( fun x : ℝ × ℝ => x.1 + x.2 ) ( nhds ( u, v ) ) ( nhds ( u + v ) ) from Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) ) using 2 ; ring_nf;
      norm_num [ ContinuousAt, Function.comp ] ; ring_nf;
      exact iff_of_eq ( by congr; ext; rw [ Function.comp_apply ] ; ring_nf );
    · have := hf ( p.1 - u );
      convert this.continuousAt.comp ( continuousAt_fst ) using 2 ; ring_nf;
      rw [ Function.comp_apply ] ; ring_nf;
    · convert hf ( p.2 - v ) |> Continuous.continuousAt |> ContinuousAt.comp <| continuousAt_snd using 1;
      grind +splitImp;
  convert h_cont_at using 1;
  exact funext fun x => h_identity u v p.1 p.2 x.1 x.2

/-- `cauchyDiff f` is jointly continuous whenever `f` has continuous
differences. Combines Steps 1–3: separate continuity → Baire → propagation. -/
lemma cauchyDiff_continuous (f : ℝ → ℝ)
    (hf : HasContinuousDifferences f) :
    Continuous (Function.uncurry (cauchyDiff f)) := by
  rw [continuous_iff_continuousAt]
  intro q
  obtain ⟨sc1, sc2⟩ := cauchyDiff_separately_continuous f hf
  obtain ⟨p, hp⟩ := separately_continuous_has_joint_continuity_point _ sc1 sc2
  exact cauchyDiff_continuousAt_everywhere f hf p hp q

/-! ## Step 4: Reduction to the periodic case -/

/-- Construct a continuous function `G` such that `f - G` is periodic
with period 1, by telescoping the differences `f(x+1) - f(x)`. -/
noncomputable def buildG (c : ℝ → ℝ) (x : ℝ) : ℝ :=
  Int.fract x * c 0 +
    if (0 : ℤ) ≤ ⌊x⌋ then
      (Finset.range (⌊x⌋).toNat).sum fun k => c (Int.fract x + ↑k)
    else
      -((Finset.range ((-⌊x⌋).toNat)).sum fun k => c (Int.fract x + ↑(⌊x⌋) + ↑k))

/-- `buildG c` satisfies the telescoping relation
`buildG c (x + 1) - buildG c x = c x`. -/
lemma buildG_satisfies (c : ℝ → ℝ) (x : ℝ) :
    buildG c (x + 1) - buildG c x = c x := by
  have hx : ⌊x + 1⌋ = ⌊x⌋ + 1 := by
    norm_num [ Int.floor_eq_iff ]
  have hx_fract : Int.fract (x + 1) = Int.fract x := by
    norm_num [ Int.fract_eq_fract ]
  have hx_eq : x = ⌊x⌋ + Int.fract x := by
    rw [ Int.floor_add_fract ];
  unfold buildG;
  rcases n : ⌊x⌋ with ( _ | n ) <;> simp +decide [ n, hx, hx_fract ] at hx_eq ⊢;
  · rw [ Finset.sum_range_succ ] ; norm_num [ n ] at * ; rw [ hx_eq ] ; ring_nf;
    grind +qlia;
  · norm_num [ Finset.sum_range_succ', Int.negSucc_eq ];
    split_ifs <;> ring_nf at *;
    · subst_vars; norm_num at *;
      rw [ ← hx_eq ];
    · exact congr_arg _ ( by linarith )

/-- `buildG c` is continuous whenever `c` is continuous. -/
lemma buildG_continuous (c : ℝ → ℝ) (hc : Continuous c) :
    Continuous (buildG c) := by
  have h_cont_on_intervals : ∀ n : ℤ, ContinuousOn (buildG c) (Set.Icc (n : ℝ) (n + 1)) := by
    intro n
    induction n using Int.induction_on with
    | zero =>
      refine ContinuousOn.congr (f := fun x => x * c 0) ?_ fun x hx => ?_
      · exact continuousOn_id.mul continuousOn_const
      · unfold buildG
        cases eq_or_lt_of_le hx.2 <;> simp_all +decide
        have : ⌊x⌋ = 0 := Int.floor_eq_iff.mpr ⟨by norm_num; linarith, by norm_num; linarith⟩
        norm_num [this, Int.fract]
    | succ n ih =>
      have h_buildG_succ : ∀ x : ℝ, buildG c (x + 1) = buildG c x + c x := by
        exact fun x => buildG_satisfies c x ▸ by ring
      have h_cont_succ : ContinuousOn (fun x => buildG c (x - 1) + c (x - 1)) (Set.Icc (n + 1 : ℝ) (n + 2)) := by
        exact ContinuousOn.add (ih.comp (continuousOn_id.sub continuousOn_const) fun x hx =>
          ⟨by norm_num at *; linarith, by norm_num at *; linarith⟩)
          (hc.comp_continuousOn (continuousOn_id.sub continuousOn_const))
      convert h_cont_succ using 1 ; norm_num [← h_buildG_succ] ; ring_nf
      norm_num ; ring_nf
    | pred k hk =>
      have h_buildG_succ : ∀ x : ℝ, buildG c (x + 1) = buildG c x + c x := by
        exact fun x => eq_add_of_sub_eq' (buildG_satisfies c x)
      have h_cont_shift : ContinuousOn (fun x => buildG c (x + 1) - c x) (Set.Icc (-k - 1 : ℝ) (-k)) := by
        exact ContinuousOn.sub (hk.comp (continuousOn_id.add continuousOn_const) fun x hx =>
          ⟨by norm_num; linarith [hx.1, hx.2], by norm_num; linarith [hx.1, hx.2]⟩)
          (hc.continuousOn)
      aesop
  refine continuous_iff_continuousAt.2 fun x => ?_;
  by_cases hx : ∃ n : ℤ, x = n;
  · obtain ⟨ n, rfl ⟩ := hx;
    have h_cont_at_int : Filter.Tendsto (buildG c) (nhdsWithin (n : ℝ) (Set.Iio n)) (nhds (buildG c n)) ∧ Filter.Tendsto (buildG c) (nhdsWithin (n : ℝ) (Set.Ioi n)) (nhds (buildG c n)) := by
      constructor;
      · have h_cont_at_int : Filter.Tendsto (buildG c) (nhdsWithin (n : ℝ) (Set.Ioo (n - 1) n)) (nhds (buildG c n)) := by
          have h_cont_at_int : ContinuousOn (buildG c) (Set.Icc (n - 1 : ℝ) n) := by
            convert h_cont_on_intervals ( n - 1 ) using 1 ; norm_num;
          have := h_cont_at_int n ( by norm_num );
          exact this.mono_left ( nhdsWithin_mono _ <| Set.Ioo_subset_Icc_self );
        simp +zetaDelta at *;
        convert h_cont_at_int using 1;
      · have := h_cont_on_intervals n;
        have := this.continuousWithinAt ( show ( n : ℝ ) ∈ Set.Icc ( n : ℝ ) ( n + 1 ) by norm_num );
        convert this.mono_left _ using 2;
        norm_num [ nhdsWithin, Filter.mem_inf_principal ];
        exact Filter.eventually_of_mem ( Iio_mem_nhds ( show ( n : ℝ ) < n + 1 by norm_num ) ) fun x hx => fun hx' => ⟨ le_of_lt hx', le_of_lt hx ⟩;
    exact continuousAt_iff_continuous_left'_right'.mpr ⟨ h_cont_at_int.1, h_cont_at_int.2 ⟩;
  · obtain ⟨n, hn⟩ : ∃ n : ℤ, (n : ℝ) < x ∧ x < (n + 1 : ℝ) := by
      exact ⟨ ⌊x⌋, lt_of_le_of_ne ( Int.floor_le x ) fun h => hx ⟨ _, h.symm ⟩, Int.lt_floor_add_one x ⟩;
    exact h_cont_on_intervals n |> ContinuousOn.continuousAt <| Icc_mem_nhds hn.1 hn.2

/-- Any function with continuous differences can be written as `G + F`
where `G` is continuous and `F` is periodic with period 1 and has
continuous differences. -/
lemma reduction_to_periodic (f : ℝ → ℝ) (hf : HasContinuousDifferences f) :
    ∃ G : ℝ → ℝ, Continuous G ∧
      PeriodicMod1 (fun x => f x - G x) ∧
      HasContinuousDifferences (fun x => f x - G x) := by
  let c : ℝ → ℝ := fun x => f (x + 1) - f x
  have hc : Continuous c := hf 1
  refine ⟨buildG c, buildG_continuous c hc, ?_, ?_⟩
  · intro x
    have h := buildG_satisfies c x
    show f (x + 1) - buildG c (x + 1) = f x - buildG c x
    linarith
  · intro h
    show Continuous fun x => (f (x + h) - buildG c (x + h)) - (f x - buildG c x)
    have : (fun x => (f (x + h) - buildG c (x + h)) - (f x - buildG c x)) =
           fun x => (f (x + h) - f x) - (buildG c (x + h) - buildG c x) := by ext x; ring
    rw [this]
    exact (hf h).sub ((buildG_continuous c hc |>.comp (continuous_add_const h)).sub
      (buildG_continuous c hc))

/-! ## Step 5: Hyers–Ulam stability for approximate additivity -/

/-- **Hyers–Ulam theorem.** If `|f(x+y) - f(x) - f(y)| ≤ M` for all
`x, y` and `f(0) = 0`, then there exists an additive `H` with
`|f(x) - H(x)| ≤ M` for all `x`. The proof constructs `H` as the
pointwise limit `H(x) = lim f(2ⁿx)/2ⁿ`. -/
lemma hyers_ulam (f : ℝ → ℝ) (_hf0 : f 0 = 0) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ x y : ℝ, |f (x + y) - f x - f y| ≤ M) :
    ∃ H : ℝ → ℝ, IsAdditiveFn H ∧ ∀ x : ℝ, |f x - H x| ≤ M := by
  have h_cauchy_seq : ∀ x, CauchySeq (fun n => f (2 ^ n * x) / 2 ^ n) := by
    intro x
    have h_cauchy_seq_step : ∀ n, abs (f (2^(n+1) * x) / 2^(n+1) - f (2^n * x) / 2^n) ≤ M / 2^(n+1) := by
      intro n; specialize hf ( 2 ^ n * x ) ( 2 ^ n * x ) ; ring_nf at *; norm_num at *;
      exact abs_le.mpr ⟨ by nlinarith [ abs_le.mp hf, pow_pos ( by norm_num : ( 0 : ℝ ) < 1 / 2 ) n ], by nlinarith [ abs_le.mp hf, pow_pos ( by norm_num : ( 0 : ℝ ) < 1 / 2 ) n ] ⟩;
    fapply cauchySeq_of_le_geometric;
    exacts [ 1 / 2, M / 2, by norm_num, fun n => by rw [ dist_comm ] ; exact le_trans ( h_cauchy_seq_step n ) ( by ring_nf; norm_num ) ];
  choose H hH using fun x => cauchySeq_tendsto_of_complete ( h_cauchy_seq x );
  refine ⟨H, ?_, ?_⟩;
  · intros x y
    have h_lim : Filter.Tendsto (fun n => (f (2 ^ n * (x + y)) - f (2 ^ n * x) - f (2 ^ n * y)) / 2 ^ n) Filter.atTop (nhds 0) := by
      have h1 : ∀ᶠ n in Filter.atTop, ‖(f (2 ^ n * (x + y)) - f (2 ^ n * x) - f (2 ^ n * y)) / 2 ^ n‖ ≤ M / 2 ^ n :=
        Filter.Eventually.of_forall fun n => by
          simpa [abs_div, mul_add] using
            div_le_div_of_nonneg_right (hf (2 ^ n * x) (2 ^ n * y))
              (by positivity : (0 : ℝ) ≤ 2 ^ n)
      exact squeeze_zero_norm' h1
        (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two))
    exact tendsto_nhds_unique ( hH ( x + y ) ) ( by simpa [ sub_div ] using h_lim.add ( hH x |> Filter.Tendsto.add <| hH y ) );
  · intro x
    have h_abs : ∀ n, |f x - f (2 ^ n * x) / 2 ^ n| ≤ M * (1 - 1 / 2 ^ n) := by
      intro n
      have h_abs_step : ∀ k : ℕ, |f (2 ^ k * x) - 2 ^ k * f x| ≤ M * (2 ^ k - 1) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          simp_all +decide [pow_succ', mul_assoc]; ring_nf at *
          have := hf (x * 2 ^ k) (x * 2 ^ k); ring_nf at *
          exact abs_le.mpr ⟨by linarith [abs_le.mp ih, abs_le.mp this],
            by linarith [abs_le.mp ih, abs_le.mp this]⟩
      rw [ abs_le ];
      constructor <;> nlinarith [ abs_le.mp ( h_abs_step n ), show ( 0 : ℝ ) < 2 ^ n by positivity, div_mul_cancel₀ ( f ( 2 ^ n * x ) ) ( show ( 2 ^ n : ℝ ) ≠ 0 by positivity ), one_div_mul_cancel ( show ( 2 ^ n : ℝ ) ≠ 0 by positivity ), pow_pos ( zero_lt_two' ℝ ) n ];
    exact le_of_tendsto' ( Filter.Tendsto.abs ( tendsto_const_nhds.sub ( hH x ) ) ) fun n => le_trans ( h_abs n ) ( mul_le_of_le_one_right hM ( sub_le_self _ ( by positivity ) ) )

/-! ## Step 6: Bounded periodic functions with continuous differences are continuous -/

/-- A bounded periodic function with continuous differences is
continuous. Uses a telescoping identity + uniform Cauchy difference
bounds to prove continuity at 0, then propagates everywhere. -/
lemma bounded_continuous_differences_implies_continuous (f : ℝ → ℝ)
    (hf : HasContinuousDifferences f)
    (hcont : Continuous (Function.uncurry (cauchyDiff f)))
    (hperiodic : PeriodicMod1 f)
    (hbdd : ∃ M : ℝ, ∀ x : ℝ, |f x| ≤ M) :
    Continuous f := by
  have h_telescope : ∀ n : ℕ, ∀ h : ℝ, 0 < n → |n * (f h - f 0)| ≤ n * (SupSet.sSup (Set.image (fun x => |cauchyDiff f x h|) (Set.Icc 0 1))) + 2 * hbdd.choose := by
    intros n h hn_pos
    have h_telescope : |f (n * h) - f 0 - n * (f h - f 0)| ≤ n * sSup (Set.image (fun x => |cauchyDiff f x h|) (Set.Icc 0 1)) := by
      have h_telescope : ∀ k : ℕ, |f ((k + 1) * h) - f (k * h) - (f h - f 0)| ≤ sSup (Set.image (fun x => |cauchyDiff f x h|) (Set.Icc 0 1)) := by
        intro k
        have h_cauchy_diff : |cauchyDiff f (k * h) h| ≤ sSup (Set.image (fun x => |cauchyDiff f x h|) (Set.Icc 0 1)) := by
          have h_periodic : cauchyDiff f (k * h) h = cauchyDiff f (k * h - ⌊k * h⌋) h := by
            unfold cauchyDiff;
            induction ⌊(k : ℝ) * h⌋ using Int.induction_on with
            | zero => simp_all +decide [PeriodicMod1]
            | succ n ihn => simp_all +decide [PeriodicMod1]; grind
            | pred n ihn => simp_all +decide [PeriodicMod1]; grind
          exact h_periodic.symm ▸ le_csSup ( by exact ( IsCompact.bddAbove ( isCompact_Icc.image ( show Continuous fun x => |cauchyDiff f x h| from continuous_abs.comp ( hcont.comp ( continuous_id.prodMk continuous_const ) ) ) ) ) ) ( Set.mem_image_of_mem _ ⟨ Int.fract_nonneg _, Int.fract_lt_one _ |> le_of_lt ⟩ );
        convert h_cauchy_diff using 1 ; unfold cauchyDiff ; ring_nf;
      induction hn_pos <;> simp_all +decide [ add_mul ];
      · exact le_trans ( abs_nonneg _ ) ( h_telescope 0 );
      · exact abs_le.mpr ⟨ by linarith [ abs_le.mp ‹_›, abs_le.mp ( h_telescope ‹_› ) ], by linarith [ abs_le.mp ‹_›, abs_le.mp ( h_telescope ‹_› ) ] ⟩;
    exact abs_le.mpr ⟨ by linarith [ abs_le.mp h_telescope, abs_le.mp ( hbdd.choose_spec ( n * h ) ), abs_le.mp ( hbdd.choose_spec 0 ) ], by linarith [ abs_le.mp h_telescope, abs_le.mp ( hbdd.choose_spec ( n * h ) ), abs_le.mp ( hbdd.choose_spec 0 ) ] ⟩;
  have h_unif_bound : ∀ ε > 0, ∃ δ > 0, ∀ x h, |h| < δ → |cauchyDiff f x h| < ε := by
    intro ε hε_pos
    obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x h, |h| < δ → |cauchyDiff f (x - ⌊x⌋) h| < ε := by
      have h_unif_bound : ∀ ε > 0, ∃ δ > 0, ∀ x h, |h| < δ → x ∈ Set.Icc 0 1 → |cauchyDiff f x h| < ε := by
        intro ε hε_pos
        have h_unif_bound : UniformContinuousOn (Function.uncurry (cauchyDiff f)) (Set.Icc 0 1 ×ˢ Set.Icc (-1) 1) := by
          exact ( isCompact_Icc.prod CompactIccSpace.isCompact_Icc ).uniformContinuousOn_of_continuous hcont.continuousOn;
        have := Metric.uniformContinuousOn_iff.mp h_unif_bound ε hε_pos;
        obtain ⟨ δ, hδ_pos, H ⟩ := this; use Min.min δ 1; norm_num [ hδ_pos ];
        intro x h hx₁ hx₂ hx₃ hx₄; specialize H ( x, h ) ⟨ ⟨ hx₃, hx₄ ⟩, ⟨ by linarith [ abs_lt.mp hx₂ ], by linarith [ abs_lt.mp hx₂ ] ⟩ ⟩ ( x, 0 ) ⟨ ⟨ hx₃, hx₄ ⟩, ⟨ by linarith [ abs_lt.mp hx₂ ], by linarith [ abs_lt.mp hx₂ ] ⟩ ⟩ ; simp_all +decide [ Prod.dist_eq ] ;
        simp_all +decide [ cauchyDiff ];
      exact Exists.elim ( h_unif_bound ε hε_pos ) fun δ hδ => ⟨ δ, hδ.1, fun x h hh => hδ.2 _ _ hh ⟨ Int.fract_nonneg _, Int.fract_lt_one _ |> le_of_lt ⟩ ⟩;
    use δ, hδ_pos;
    intro x h hh; convert hδ x h hh using 1; unfold cauchyDiff; ring_nf;
    rw [ show f ( x + h ) = f ( x + ( h - ⌊x⌋ ) ) by exact Function.Periodic.int_mul hperiodic ⌊x⌋ ( x + ( h - ⌊x⌋ ) ) ▸ by ring_nf, show f x = f ( x - ⌊x⌋ ) by exact Function.Periodic.int_mul hperiodic ⌊x⌋ ( x - ⌊x⌋ ) ▸ by ring_nf ] ; ring_nf;
  have h_cont_at_zero : ContinuousAt f 0 := by
    have h_cont_at_zero_aux : ∀ ε > 0, ∃ δ > 0, ∀ h, |h| < δ → |f h - f 0| < ε := by
      intros ε hε_pos
      obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x h, |h| < δ → |cauchyDiff f x h| < ε / 2 := h_unif_bound (ε / 2) (half_pos hε_pos);
      obtain ⟨n, hn_pos, hn⟩ : ∃ n : ℕ, 0 < n ∧ 2 * hbdd.choose / (n : ℝ) < ε / 2 := by
        exact ⟨ ⌊2 * hbdd.choose / ( ε / 2 ) ⌋₊ + 1, Nat.succ_pos _, by rw [ div_lt_iff₀ ] <;> push_cast <;> nlinarith [ Nat.lt_floor_add_one ( 2 * hbdd.choose / ( ε / 2 ) ), mul_div_cancel₀ ( 2 * hbdd.choose ) ( ne_of_gt ( half_pos hε_pos ) ) ] ⟩;
      refine ⟨δ, hδ_pos, fun h hh => ?_⟩ ; specialize h_telescope n h hn_pos ; simp_all +decide [abs_mul];
      have h_sSup : sSup ((fun x => |cauchyDiff f x h|) '' Icc 0 1) ≤ ε / 2 := by
        exact csSup_le ( Set.Nonempty.image _ <| Set.nonempty_Icc.mpr zero_le_one ) <| Set.forall_mem_image.mpr fun x hx => le_of_lt <| hδ x h hh;
      rw [ div_lt_iff₀ ] at hn <;> nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast ];
    exact Metric.continuousAt_iff.2 fun ε hε => by simpa using h_cont_at_zero_aux ε hε;
  rw [ continuous_iff_continuousAt ];
  intro x;
  have := hf x;
  have := this.tendsto 0; simp_all +decide [ ContinuousAt ] ;
  convert this.comp ( show Filter.Tendsto ( fun y => y - x ) ( nhds x ) ( nhds 0 ) by exact tendsto_sub_nhds_zero_iff.mpr Filter.tendsto_id ) |> Filter.Tendsto.add <| h_cont_at_zero.comp ( show Filter.Tendsto ( fun y => y - x ) ( nhds x ) ( nhds 0 ) by exact tendsto_sub_nhds_zero_iff.mpr Filter.tendsto_id ) using 2 <;> norm_num

/-! ## Step 7: The periodic case -/

/-- For a periodic function with jointly continuous Cauchy difference,
the Cauchy difference is globally bounded (by compactness of `[0,1]²`). -/
lemma cauchyDiff_periodic_bounded (f : ℝ → ℝ)
    (hperiodic : PeriodicMod1 f)
    (hcont : Continuous (Function.uncurry (cauchyDiff f))) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x h, |cauchyDiff f x h| ≤ M := by
  have h_periodic : ∀ x h : ℝ, cauchyDiff f x h = cauchyDiff f (x - ⌊x⌋) (h - ⌊h⌋) := by
    intros x h; unfold cauchyDiff; simp +decide;
    have h_periodic_simp : ∀ x : ℝ, f x = f (Int.fract x) := by
      exact fun x => by simpa using Function.Periodic.int_mul hperiodic ⌊x⌋ ( Int.fract x ) ;
    rw [ h_periodic_simp ( x + h ), h_periodic_simp x, h_periodic_simp h ];
    rw [ h_periodic_simp ( Int.fract x + Int.fract h ) ];
    rw [ ← Int.fract_add_intCast ( Int.fract x + Int.fract h ) ⌊x⌋ ] ; norm_num [ add_assoc, Int.fract_add ] ;
    rw [ ← add_assoc, Int.fract_eq_fract.mpr ];
    exact ⟨ ⌊h⌋, by linarith [ Int.fract_add_floor x, Int.fract_add_floor h ] ⟩;
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x h : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ h → h ≤ 1 → |cauchyDiff f x h| ≤ M := by
    exact IsCompact.exists_bound_of_continuousOn ( CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc ) ( hcont.continuousOn ) |> fun ⟨ M, hM ⟩ => ⟨ M, fun x h hx₁ hx₂ hy₁ hy₂ => hM ( x, h ) ⟨ ⟨ hx₁, hx₂ ⟩, ⟨ hy₁, hy₂ ⟩ ⟩ ⟩;
  exact ⟨ Max.max M 0, by positivity, fun x h => le_trans ( h_periodic x h ▸ hM _ _ ( Int.fract_nonneg _ ) ( Int.fract_lt_one _ |> le_of_lt ) ( Int.fract_nonneg _ ) ( Int.fract_lt_one _ |> le_of_lt ) ) ( le_max_left _ _ ) ⟩

/-- **Periodic case of the main theorem.** A periodic function with
continuous differences decomposes as `g + H` with `g` continuous and
`H` additive. Uses Hyers–Ulam stability + the fact that `H(1) = 0`
(forced by periodicity and boundedness). -/
lemma periodic_decomposition (f : ℝ → ℝ)
    (hperiodic : PeriodicMod1 f)
    (hf : HasContinuousDifferences f) :
    ∃ g H : ℝ → ℝ, Continuous g ∧ IsAdditiveFn H ∧ ∀ x, f x = g x + H x := by
  have hφ_cont := cauchyDiff_continuous f hf
  obtain ⟨M, hM_pos, hM⟩ := cauchyDiff_periodic_bounded f hperiodic hφ_cont
  let F : ℝ → ℝ := fun x => f x - f 0
  have hF0 : F 0 = 0 := sub_self _
  have hFM : ∀ x y, |F (x + y) - F x - F y| ≤ M := by
    intro x y
    have : F (x + y) - F x - F y = cauchyDiff f x y := by
      show f (x + y) - f 0 - (f x - f 0) - (f y - f 0) = _
      unfold cauchyDiff; ring
    rw [this]; exact hM x y
  obtain ⟨H, hH_add, hH_bound⟩ := hyers_ulam F hF0 M hM_pos hFM
  refine ⟨fun x => f x - H x, H, ?_, hH_add, fun x => by ring⟩
  have hg_bdd : ∃ M', ∀ x, |f x - H x| ≤ M' := by
    refine ⟨M + |f 0|, fun x => ?_⟩
    calc |f x - H x| = |(F x - H x) + f 0| := by show _ = |(f x - f 0 - H x) + f 0|; ring_nf
      _ ≤ |F x - H x| + |f 0| := abs_add_le _ _
      _ ≤ M + |f 0| := by linarith [hH_bound x]
  have hg_diff : HasContinuousDifferences (fun x => f x - H x) := by
    intro h
    have hHconst : ∀ x, H (x + h) - H x = H h := fun x => by
      have := hH_add x h; linarith
    show Continuous fun x => (f (x + h) - H (x + h)) - (f x - H x)
    have : (fun x => (f (x + h) - H (x + h)) - (f x - H x)) =
           fun x => (f (x + h) - f x) - H h := by
      ext x; have := hHconst x; linarith
    rw [this]; exact (hf h).sub continuous_const
  have hH1 : H 1 = 0 := by
    by_contra h1
    have h1pos : 0 < |H 1| := abs_pos.mpr h1
    have hHn : ∀ n : ℕ, H (↑n) = ↑n * H 1 := by
      intro n; induction n with
      | zero =>
        have h0 := hH_add 0 0
        simp only [Nat.cast_zero, zero_mul, zero_add] at *
        linarith
      | succ n ih =>
        have := hH_add (↑n) 1
        simp only [Nat.cast_succ] at *
        linarith
    have hFn : ∀ n : ℕ, F (↑n) = 0 := by
      intro n; induction n with
      | zero => simp only [Nat.cast_zero]; exact hF0
      | succ n ih =>
        have hp := hperiodic (↑n)
        show f (↑(n + 1)) - f 0 = 0
        simp only [Nat.cast_succ]
        linarith [ih]
    have hbound : ∀ n : ℕ, |↑n * H 1| ≤ M := by
      intro n
      rw [← hHn n]
      calc |H (↑n)| = |H (↑n) - F (↑n)| := by rw [hFn n, sub_zero]
        _ = |F (↑n) - H (↑n)| := abs_sub_comm _ _
        _ ≤ M := hH_bound (↑n)
    obtain ⟨n, hn⟩ := exists_nat_gt (M / |H 1|)
    have h1 := hbound n
    have h2 : (↑n : ℝ) * |H 1| ≤ M := by rwa [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)] at h1
    have h3 : M < (↑n : ℝ) * |H 1| := by rwa [div_lt_iff₀ h1pos] at hn
    linarith
  have hg_periodic : PeriodicMod1 (fun x => f x - H x) := by
    intro x
    show f (x + 1) - H (x + 1) = f x - H x
    have := hH_add x 1
    linarith [hperiodic x, hH1]
  exact bounded_continuous_differences_implies_continuous _
    hg_diff (cauchyDiff_continuous _ hg_diff) hg_periodic hg_bdd

/-! ## Main theorem -/

/-- **de Bruijn's theorem (all differences).** If `x ↦ f(x+h) - f(x)` is
continuous for every `h`, then `f = g + H` with `g` continuous and `H`
additive. Combines periodic reduction with the periodic case. -/
theorem erdos907_of_all_h (f : ℝ → ℝ)
    (hf : ∀ h : ℝ, Continuous fun x => f (x + h) - f x) :
    ∃ g H : ℝ → ℝ, Continuous g ∧ IsAdditiveFn H ∧ ∀ x, f x = g x + H x := by
  obtain ⟨G, hG_cont, hperiodic, hF_diff⟩ := reduction_to_periodic f hf
  obtain ⟨g₀, H, hg₀_cont, hH_add, hdecomp⟩ := periodic_decomposition _ hperiodic hF_diff
  exact ⟨fun x => g₀ x + G x, H, hg₀_cont.add hG_cont, hH_add, fun x => by linarith [hdecomp x]⟩

/-- Continuity of `x ↦ f(x + h) - f(x)` for all `h > 0` implies it
for all `h`. For `h < 0`, use `f(x+h) - f(x) = -(f(x) - f(x+h))`. -/
lemma hasContinuousDifferences_of_pos (f : ℝ → ℝ)
    (hf : ∀ h : ℝ, 0 < h → Continuous fun x => f (x + h) - f x) :
    HasContinuousDifferences f := by
  intro h
  rcases lt_trichotomy h 0 with hh | rfl | hh
  · have : (fun x => f (x + h) - f x) = fun x => -(f ((x + h) + (-h)) - f (x + h)) := by grind
    rw [this]
    exact (hf (-h) (neg_pos.mpr hh)).comp (continuous_id.add continuous_const) |>.neg
  · simp [continuous_const]
  · exact hf h hh

/-- **Theorem 1.1 (de Bruijn & Erdős).** If `f : ℝ → ℝ` is such that, for each `h > 0`,
`x ↦ f(x + h) - f(x)` is continuous, then `f = g + H` where `g` is continuous and `H`
is additive. -/
theorem erdos907 (f : ℝ → ℝ)
    (hf : ∀ h : ℝ, 0 < h → Continuous fun x => f (x + h) - f x) :
    ∃ g H : ℝ → ℝ, Continuous g ∧ IsAdditiveFn H ∧ ∀ x, f x = g x + H x :=
  erdos907_of_all_h f <| hasContinuousDifferences_of_pos f hf

#print axioms erdos907

end Erdos907
