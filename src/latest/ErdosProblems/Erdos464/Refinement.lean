/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 464.
Informal author: Bernard de Mathan.
Formal authors: Aristotle, JoshuaB.
Source: https://www.erdosproblems.com/forum/thread/464#post-7120
https://aristotle.harmonic.fun/dashboard/requests/f9894d2d-4bb1-42da-9301-e508aa881b17
Original Lean version: 4.28.0, confirmed by the user who supplied the source files.
The original Mathlib revision and a license notice were not supplied.
-/
import Mathlib

set_option linter.mathlibStandardSet false

namespace Erdos464

/-!
# Refining a lacunary sequence to one with bounded ratios

Given a sequence `a : ℕ → ℕ` of naturals with `μ₀ * a k ≤ a (k+1)` (a lacunary lower bound), we
build a real sequence `Q` whose consecutive ratios lie in `[√μ₀, μ₀]` and whose range contains
every `a k`.

The construction is a small state machine on `ℝ × ℕ`: the state `(v, k)` means "current value `v`,
next target `a k`".  From `(v,k)` we jump to `(a k, k+1)` if `a k ≤ μ₀ v`, otherwise we multiply by
`√μ₀`.
-/

noncomputable def refStep (μ₀ : ℝ) (a : ℕ → ℕ) (p : ℝ × ℕ) : ℝ × ℕ :=
  if (a p.2 : ℝ) ≤ μ₀ * p.1 then ((a p.2 : ℝ), p.2 + 1) else (Real.sqrt μ₀ * p.1, p.2)

noncomputable def refState (μ₀ : ℝ) (a : ℕ → ℕ) (n : ℕ) : ℝ × ℕ :=
  (refStep μ₀ a)^[n] ((a 0 : ℝ), 1)

noncomputable def Qseq (μ₀ : ℝ) (a : ℕ → ℕ) (n : ℕ) : ℝ := (refState μ₀ a n).1

/-! ## Basic facts -/

lemma sqrt_mu_gt_one (μ₀ : ℝ) (hμ : 1 < μ₀) : 1 < Real.sqrt μ₀ := by
  exact Real.lt_sqrt_of_sq_lt ( by linarith )

lemma sqrt_mu_le_mu (μ₀ : ℝ) (hμ : 1 < μ₀) : Real.sqrt μ₀ ≤ μ₀ := by
  rw [ Real.sqrt_le_left ] <;> nlinarith

lemma refState_succ (μ₀ : ℝ) (a : ℕ → ℕ) (n : ℕ) :
    refState μ₀ a (n + 1) = refStep μ₀ a (refState μ₀ a n) := by
  exact Function.iterate_succ_apply' _ _ _

lemma refStep_jump (μ₀ : ℝ) (a : ℕ → ℕ) (v : ℝ) (k : ℕ) (h : (a k : ℝ) ≤ μ₀ * v) :
    refStep μ₀ a (v, k) = ((a k : ℝ), k + 1) := by
  exact if_pos h

lemma refStep_far (μ₀ : ℝ) (a : ℕ → ℕ) (v : ℝ) (k : ℕ) (h : μ₀ * v < (a k : ℝ)) :
    refStep μ₀ a (v, k) = (Real.sqrt μ₀ * v, k) := by
  exact if_neg h.not_ge

/-! ## Invariant and ratio bounds -/

/-
The invariant maintained by the state machine.
-/
lemma refInv (a : ℕ → ℕ) (ha0 : 0 < a 0) (μ₀ : ℝ) (hμ : 1 < μ₀)
    (hlac : ∀ k, μ₀ * (a k : ℝ) ≤ a (k + 1)) (n : ℕ) :
    0 < (refState μ₀ a n).1 ∧ Real.sqrt μ₀ * (refState μ₀ a n).1 ≤ (a (refState μ₀ a n).2 : ℝ) := by
  induction' n with n ih;
  · exact ⟨ Nat.cast_pos.mpr ha0, by simpa [ refState ] using le_trans ( mul_le_mul_of_nonneg_right ( Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith ⟩ ) <| Nat.cast_nonneg _ ) ( hlac 0 ) ⟩;
  · simp_all +decide [ refState_succ ];
    unfold refStep; split_ifs <;> simp_all +decide ;
    · exact ⟨ Nat.cast_pos.mp ( lt_of_lt_of_le ( mul_pos ( Real.sqrt_pos.mpr ( zero_lt_one.trans hμ ) ) ih.1 ) ih.2 ), by nlinarith [ hlac ( refState μ₀ a n |>.2 ), Real.sqrt_nonneg μ₀, Real.sq_sqrt ( show 0 ≤ μ₀ by positivity ) ] ⟩;
    · exact ⟨ by positivity, by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ μ₀ by positivity ) ] ⟩

lemma refPos (a : ℕ → ℕ) (ha0 : 0 < a 0) (μ₀ : ℝ) (hμ : 1 < μ₀)
    (hlac : ∀ k, μ₀ * (a k : ℝ) ≤ a (k + 1)) (n : ℕ) : 0 < Qseq μ₀ a n :=
  (refInv a ha0 μ₀ hμ hlac n).1

lemma refRatio_lo (a : ℕ → ℕ) (ha0 : 0 < a 0) (μ₀ : ℝ) (hμ : 1 < μ₀)
    (hlac : ∀ k, μ₀ * (a k : ℝ) ≤ a (k + 1)) (n : ℕ) :
    Real.sqrt μ₀ * Qseq μ₀ a n ≤ Qseq μ₀ a (n + 1) := by
  -- Let `v := (refState μ₀ a n).1`, `k := (refState μ₀ a n).2`. `Qseq μ₀ a n = v`.
  set v := (refState μ₀ a n).1
  set k := (refState μ₀ a n).2
  have hv : Qseq μ₀ a n = v := by
    rfl;
  -- Rewrite `Qseq μ₀ a (n+1) = (refState μ₀ a (n+1)).1 = (refStep μ₀ a (v,k)).1` via `refState_succ`.
  have hQn1 : Qseq μ₀ a (n + 1) = (refStep μ₀ a (v, k)).1 := by
    exact congr_arg Prod.fst ( refState_succ μ₀ a n );
  have := refInv a ha0 μ₀ hμ hlac n; unfold refStep at *; split_ifs at * <;> nlinarith [ Real.sqrt_nonneg μ₀, Real.sq_sqrt <| show 0 ≤ μ₀ by positivity ] ;

lemma refRatio_hi (a : ℕ → ℕ) (ha0 : 0 < a 0) (μ₀ : ℝ) (hμ : 1 < μ₀)
    (hlac : ∀ k, μ₀ * (a k : ℝ) ≤ a (k + 1)) (n : ℕ) :
    Qseq μ₀ a (n + 1) ≤ μ₀ * Qseq μ₀ a n := by
  unfold Qseq
  rw [refState_succ]
  dsimp only [refStep]
  split_ifs with h
  · exact h
  · exact mul_le_mul_of_nonneg_right (sqrt_mu_le_mu μ₀ hμ)
      (refInv a ha0 μ₀ hμ hlac n).1.le

/-! ## Reaching each target -/

/-
After enough `√μ₀`-multiplications the value overtakes the next target.
-/
lemma exists_jump_time (μ₀ : ℝ) (hμ : 1 < μ₀) (a : ℕ → ℕ) (v : ℝ) (hv : 0 < v) (k : ℕ) :
    ∃ T : ℕ, (a k : ℝ) ≤ μ₀ * (Real.sqrt μ₀ ^ T * v) := by
  -- Since `Real.sqrt μ₀ > 1` (`sqrt_mu_gt_one μ₀ hμ`), `Real.sqrt μ₀ ^ T → ∞` as `T → ∞` (`tendsto_pow_atTop_atTop_of_one_lt`).
  have h_sqrt_pow : Filter.Tendsto (fun T => Real.sqrt μ₀ ^ T) Filter.atTop Filter.atTop := by
    exact tendsto_pow_atTop_atTop_of_one_lt ( Real.lt_sqrt_of_sq_lt ( by linarith ) );
  exact Filter.Eventually.exists ( h_sqrt_pow.eventually_ge_atTop ( ( a k : ℝ ) / ( μ₀ * v ) ) ) |> fun ⟨ T, hT ⟩ => ⟨ T, by nlinarith [ show 0 < μ₀ * v by positivity, mul_div_cancel₀ ( a k : ℝ ) ( by positivity : ( μ₀ * v ) ≠ 0 ) ] ⟩

/-
While the target is far, iterating just multiplies by `√μ₀` and keeps the pointer.
-/
lemma iterate_far (μ₀ : ℝ) (a : ℕ → ℕ) (v : ℝ) (k : ℕ) (i : ℕ)
    (h : ∀ j, j < i → μ₀ * (Real.sqrt μ₀ ^ j * v) < (a k : ℝ)) :
    (refStep μ₀ a)^[i] (v, k) = (Real.sqrt μ₀ ^ i * v, k) := by
  induction i <;> simp_all +decide [ Function.iterate_succ_apply' ];
  rename_i n hn
  rw [hn fun j hj => h j hj.le, refStep_far μ₀ a _ _ (h n le_rfl)]
  congr 1
  rw [pow_succ]
  ring

/-
From any valid state, the machine eventually jumps to the current target.
-/
lemma reaches (μ₀ : ℝ) (hμ : 1 < μ₀) (a : ℕ → ℕ) (v : ℝ) (hv : 0 < v) (k : ℕ) :
    ∃ t : ℕ, (refStep μ₀ a)^[t] (v, k) = ((a k : ℝ), k + 1) := by
  obtain ⟨ T, hT ⟩ := exists_jump_time μ₀ hμ a v hv k;
  -- Use `classical` and let `t₀ := Nat.find ⟨T, hT⟩` for that existence.
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℕ, (a k : ℝ) ≤ μ₀ * (Real.sqrt μ₀ ^ t₀ * v) ∧ ∀ j < t₀, ¬((a k : ℝ) ≤ μ₀ * (Real.sqrt μ₀ ^ j * v)) := by
    exact ⟨ Nat.find ( ⟨ T, hT ⟩ : ∃ t₀, ( a k : ℝ ) ≤ μ₀ * ( Real.sqrt μ₀ ^ t₀ * v ) ), Nat.find_spec ( ⟨ T, hT ⟩ : ∃ t₀, ( a k : ℝ ) ≤ μ₀ * ( Real.sqrt μ₀ ^ t₀ * v ) ), fun j hj => Nat.find_min ( ⟨ T, hT ⟩ : ∃ t₀, ( a k : ℝ ) ≤ μ₀ * ( Real.sqrt μ₀ ^ t₀ * v ) ) hj ⟩;
  use t₀ + 1; have := iterate_far μ₀ a v k t₀; simp_all +decide [ Function.iterate_succ_apply' ] ;
  exact refStep_jump μ₀ a _ _ ht₀.1

/-
Every target `a k` is hit by the state machine.
-/
lemma refState_hits (a : ℕ → ℕ) (ha0 : 0 < a 0) (μ₀ : ℝ) (hμ : 1 < μ₀)
    (hlac : ∀ k, μ₀ * (a k : ℝ) ≤ a (k + 1)) (k : ℕ) :
    ∃ n, refState μ₀ a n = ((a k : ℝ), k + 1) := by
  induction' k with k ih;
  · exact ⟨ 0, rfl ⟩;
  · -- By `reaches`, there exists `t` such that `(refStep μ₀ a)^[t] ((a k:ℝ), k+1) = ((a (k+1):ℝ), k+2)`.
    obtain ⟨t, ht⟩ : ∃ t : ℕ, (refStep μ₀ a)^[t] ((a k : ℝ), k + 1) = ((a (k + 1) : ℝ), k + 2) := by
      apply reaches μ₀ hμ a (a k : ℝ) (by
      exact Nat.cast_pos.mpr ( show 0 < a k from Nat.recOn k ha0 fun n hn => Nat.cast_pos.mp ( lt_of_lt_of_le ( by positivity ) ( hlac n ) ) )) (k + 1);
    obtain ⟨ n, hn ⟩ := ih; use n + t; simp_all +decide [ Function.iterate_add_apply, refState ] ;
    rw [ ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hn, ht ]

/-- Existence of the refined sequence with bounded ratios containing every `a k`. -/
theorem exists_refinement (a : ℕ → ℕ) (ha0 : 0 < a 0)
    (μ₀ : ℝ) (hμ : 1 < μ₀) (hlac : ∀ k, μ₀ * (a k : ℝ) ≤ a (k + 1)) :
    ∃ Q : ℕ → ℝ, (∀ n, 0 < Q n) ∧
      (∀ n, Real.sqrt μ₀ * Q n ≤ Q (n + 1)) ∧
      (∀ n, Q (n + 1) ≤ μ₀ * Q n) ∧
      (∀ k, ∃ n, Q n = (a k : ℝ)) := by
  refine ⟨Qseq μ₀ a, refPos a ha0 μ₀ hμ hlac, refRatio_lo a ha0 μ₀ hμ hlac,
    refRatio_hi a ha0 μ₀ hμ hlac, ?_⟩
  intro k
  obtain ⟨n, hn⟩ := refState_hits a ha0 μ₀ hμ hlac k
  exact ⟨n, by rw [Qseq, hn]⟩

end Erdos464
