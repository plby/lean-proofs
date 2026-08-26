/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Released under the Apache 2.0 license. This file has been modified. -/
/-
Erdős Problem 146. Informal proof: Astra (internal OpenAI model).
Formalization: Astra (internal OpenAI model), OpenAI team.
Source: https://www.erdosproblems.com/forum/thread/146#post-8253
https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean
Original Lean/Mathlib version: 4.32.0. Ported to 4.33.0.
-/
import ErdosProblems.Erdos146.MainTheorem

open Filter

namespace Erdos146

theorem not_erdos_146 :
    ¬ (∀ (r q : ℕ) (H : SimpleGraph (Fin q)),
      0 < r → H.IsBipartite → IsDegenerate r H →
        Asymptotics.IsBigO Filter.atTop
          (fun n : ℕ => (SimpleGraph.extremalNumber n H : ℝ))
          (fun n : ℕ => (n : ℝ) ^ (((2 : ℕ) : ℝ) - 1 / (r : ℝ)))) := by
  intro hconjecture
  obtain ⟨q, H, _hconnected, hbipartite, hdegenerate, _hdegree,
    c, ε, hc, hε, hlower⟩ := twoDegenerateExtremalCounterexample
  have hbigO := hconjecture 2 q H (by norm_num)
    hbipartite hdegenerate
  obtain ⟨C, hupper⟩ := Asymptotics.isBigO_iff.mp hbigO
  have hupper' :
      ∀ᶠ n : ℕ in Filter.atTop,
        (SimpleGraph.extremalNumber n H : ℝ) ≤
          C * (n : ℝ) ^ ((3 : ℝ) / 2) := by
    filter_upwards [hupper] with n hn
    have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hextremal_nonneg :
        (0 : ℝ) ≤ (SimpleGraph.extremalNumber n H : ℝ) :=
      Nat.cast_nonneg _
    have hnormalized :
        (SimpleGraph.extremalNumber n H : ℝ) ≤
          C * (n : ℝ) ^ ((2 : ℝ) - 1 / (2 : ℝ)) := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hextremal_nonneg,
        abs_of_nonneg (Real.rpow_nonneg hnnonneg _), Nat.cast_ofNat] using hn
    convert hnormalized using 1
    norm_num
  have hlarge :=
    Erdos146.eventually_constant_le_positive_nat_rpow
      (C + 1) c ε hc hε
  have himpossible : ∀ᶠ n : ℕ in Filter.atTop, False := by
    filter_upwards [hlower, hupper', hlarge,
      Filter.eventually_gt_atTop 0] with n hlow hupp hlarge_n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hscale : 0 < (n : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.rpow_pos_of_pos hnreal _
    have hdecompose :
        c * (n : ℝ) ^ ((3 : ℝ) / 2 + ε) =
          (c * (n : ℝ) ^ ε) * (n : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [Real.rpow_add hnreal]
      ring
    rw [hdecompose] at hlow
    have hscaled := mul_le_mul_of_nonneg_right hlarge_n hscale.le
    nlinarith
  exact himpossible.exists.elim (fun _ h => h)

#print axioms not_erdos_146
-- 'Erdos146.not_erdos_146' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos146
