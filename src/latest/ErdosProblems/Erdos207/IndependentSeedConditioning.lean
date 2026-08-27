/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteFiberAveraging

/-! # A fixed independent seed preserves the complete original-data marginal -/

namespace Erdos207.FiniteLaw

open Finset
open scoped NNReal

noncomputable section

theorem jointBind_const_probability_product
    {D R : Type*} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]
    (P : FiniteLaw D) (Q : FiniteLaw R) (A : D → Prop) (B : R → Prop) :
    (P.jointBind (fun _ ↦ Q)).probability (fun z ↦ B z.2 ∧ A z.1) =
      P.probability A * Q.probability B := by
  classical
  rw [probability_jointBind]
  unfold probability
  rw [sum_mul]
  apply sum_congr rfl
  intro d _
  by_cases hd : A d <;> simp [hd]

theorem independent_seed_marginal
    {Ω D R : Type*} [Fintype Ω] [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]
    (L : FiniteLaw Ω) (data : Ω → D) (seed : Ω → R) (P : FiniteLaw D) (Q : FiniteLaw R)
    (hind : map (fun x ↦ (data x, seed x)) L = P.jointBind (fun _ ↦ Q)) :
    map seed L = Q := by
  calc
    _ = map Prod.snd (map (fun x ↦ (data x, seed x)) L) := (map_comp L _ _).symm
    _ = map Prod.snd (P.jointBind (fun _ ↦ Q)) := congrArg (map Prod.snd) hind
    _ = Q := by rw [map_jointBind_snd, bind_const]

theorem condition_independent_seed_preserves_data
    {Ω D R : Type*} [Fintype Ω] [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]
    (L : FiniteLaw Ω) (data : Ω → D) (seed : Ω → R) (P : FiniteLaw D) (Q : FiniteLaw R)
    (hind : map (fun x ↦ (data x, seed x)) L = P.jointBind (fun _ ↦ Q))
    (r : R) (hr : 0 < L.probability (fun x ↦ seed x = r)) :
    map data (L.conditionOn (fun x ↦ seed x = r) hr) = P := by
  classical
  have hmarg := independent_seed_marginal L data seed P Q hind
  have hmass : L.probability (fun x ↦ seed x = r) = Q.mass r := by
    rw [← map_mass_eq_probability, hmarg]
  have hpos : 0 < Q.mass r := hmass ▸ hr
  apply ext_probability
  intro A
  rw [probability_map, conditionOn_probability]
  have hnum : L.probability (fun x ↦ seed x = r ∧ A (data x)) =
      P.probability A * Q.mass r := by
    have h := congrArg (fun M : FiniteLaw (D × R) ↦
      M.probability (fun z ↦ z.2 = r ∧ A z.1)) hind
    rw [probability_map, jointBind_const_probability_product P Q A (fun z ↦ z = r),
      probability_eq_mass] at h
    exact h
  rw [hnum, hmass]
  exact mul_div_cancel_right₀ _ hpos.ne'

theorem exists_fixed_independent_seed
    {Ω D R : Type*} [Fintype Ω] [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]
    (L : FiniteLaw Ω) (data : Ω → D) (seed : Ω → R) (P : FiniteLaw D) (Q : FiniteLaw R)
    (hind : map (fun x ↦ (data x, seed x)) L = P.jointBind (fun _ ↦ Q))
    (Bad : Ω → Prop) (GoodSeed : R → Prop) (epsilon eta delta : ℝ≥0)
    (hdelta : 0 < delta) (hbad : L.probability Bad ≤ epsilon)
    (hseed : Q.probability (fun r ↦ ¬ GoodSeed r) ≤ eta)
    (hbudget : eta + epsilon / delta < 1) :
    ∃ r, ∃ hr : 0 < L.probability (fun x ↦ seed x = r),
      GoodSeed r ∧
      map data (L.conditionOn (fun x ↦ seed x = r) hr) = P ∧
      (L.conditionOn (fun x ↦ seed x = r) hr).SupportedOn (fun x ↦ seed x = r) ∧
      (L.conditionOn (fun x ↦ seed x = r) hr).probability Bad < delta := by
  have hmarg := independent_seed_marginal L data seed P Q hind
  obtain ⟨r, hr, hg, hb⟩ := exists_good_seed_with_small_conditional_failure L seed Bad GoodSeed
    epsilon eta delta hdelta hbad (by simpa only [hmarg] using hseed) hbudget
  exact ⟨r, hr, hg, condition_independent_seed_preserves_data L data seed P Q hind r hr,
    conditionOn_supported _ _ _, hb⟩

end

end Erdos207.FiniteLaw
