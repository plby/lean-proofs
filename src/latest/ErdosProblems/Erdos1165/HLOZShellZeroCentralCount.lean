/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZShellZeroReplacementNumerics

/-!
# The fixed central-count comparison in the shell-zero replacement argument

The replacement step in HLOZ (4.49)--(4.54) is performed after fixing the
exact number `r` of source coordinates.  It does **not** compare the source
with the union over every possible mixture of the two windows.  Instead it
uses the single central replacement count

`s = floor (C / (1 + C) * r)`.

This file isolates the finite, heterogeneous product algebra for that exact
comparison.  It is deliberately separate from the pathwise construction of
the events `D_eta`, `theta`, and `V_eta`: those events supply one finite set
of `r` coordinates and the coordinatewise window-mass comparison used here.
-/

open scoped BigOperators

namespace Erdos1165.HLOZShellZeroCentralCount

noncomputable section

variable {Coordinate : Type*} [Fintype Coordinate] [DecidableEq Coordinate]

/-- Product mass when every selected coordinate is in the source (`I₁`)
window. -/
def allUpperProductMass (upperMass : Coordinate → ℝ) : ℝ :=
  ∏ c, upperMass c

/-- Product mass of one fixed choice of coordinates which remain in `I₁`;
the complementary coordinates are replaced by values in `I₀`. -/
def mixedSubsetProductMass
    (upperMass lowerMass : Coordinate → ℝ) (A : Finset Coordinate) : ℝ :=
  (∏ c ∈ A, upperMass c) * (∏ c ∈ Aᶜ, lowerMass c)

/-- Total product mass with exactly `s` coordinates in `I₁`. -/
def exactUpperCountProductMass
    (upperMass lowerMass : Coordinate → ℝ) (s : ℕ) : ℝ :=
  ∑ A ∈ (Finset.univ : Finset Coordinate).powersetCard s,
    mixedSubsetProductMass upperMass lowerMass A

/-- The exact central count used in HLOZ (4.51). -/
def centralReplacementUpperCount (C : ℝ) (r : ℕ) : ℕ :=
  ⌊C / (1 + C) * r⌋₊

/-- The exact ratio delivered by the finite comparison with one central
replacement count. -/
def centralReplacementRatio (C : ℝ) (r : ℕ) : ℝ :=
  let s := centralReplacementUpperCount C r
  C ^ (r - s) / (r.choose s : ℝ)

lemma centralReplacementUpperCount_le
    {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    centralReplacementUpperCount C r ≤ r := by
  unfold centralReplacementUpperCount
  apply Nat.floor_le_of_le
  have hden : 0 < 1 + C := by linarith
  have hfrac : C / (1 + C) ≤ 1 :=
    (div_le_one₀ hden).2 (by linarith)
  have hr : (0 : ℝ) ≤ r := by positivity
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hfrac hr

lemma mixedSubsetProductMass_nonneg
    (upperMass lowerMass : Coordinate → ℝ)
    (hupper : ∀ c, 0 ≤ upperMass c)
    (hlower : ∀ c, 0 ≤ lowerMass c) (A : Finset Coordinate) :
    0 ≤ mixedSubsetProductMass upperMass lowerMass A := by
  unfold mixedSubsetProductMass
  exact mul_nonneg
    (Finset.prod_nonneg fun c _ ↦ hupper c)
    (Finset.prod_nonneg fun c _ ↦ hlower c)

lemma allUpperProductMass_eq_compl_mul
    (upperMass : Coordinate → ℝ) (A : Finset Coordinate) :
    allUpperProductMass upperMass =
      (∏ c ∈ Aᶜ, upperMass c) * (∏ c ∈ A, upperMass c) := by
  unfold allUpperProductMass
  exact (Finset.prod_compl_mul_prod A upperMass).symm

/-- One fixed `s`-subset comparison.  Every coordinate moved from `I₁` to
`I₀` costs at most a factor `C`. -/
theorem allUpperProductMass_le_pow_mul_mixedSubset
    (upperMass lowerMass : Coordinate → ℝ)
    (hupper : ∀ c, 0 ≤ upperMass c)
    {C : ℝ}
    (hratio : ∀ c, upperMass c ≤ C * lowerMass c)
    (A : Finset Coordinate) :
    allUpperProductMass upperMass ≤
      C ^ (Fintype.card Coordinate - A.card) *
        mixedSubsetProductMass upperMass lowerMass A := by
  rw [allUpperProductMass_eq_compl_mul upperMass A]
  unfold mixedSubsetProductMass
  have hcomp :
      (∏ c ∈ Aᶜ, upperMass c) ≤ ∏ c ∈ Aᶜ, C * lowerMass c := by
    apply Finset.prod_le_prod
    · intro c _
      exact hupper c
    · intro c _
      exact hratio c
  have hcard : Aᶜ.card = Fintype.card Coordinate - A.card := by
    change (Finset.univ \ A).card = Fintype.card Coordinate - A.card
    simp [Finset.card_sdiff]
  calc
    (∏ c ∈ Aᶜ, upperMass c) * (∏ c ∈ A, upperMass c) ≤
        (∏ c ∈ Aᶜ, C * lowerMass c) * (∏ c ∈ A, upperMass c) :=
      mul_le_mul_of_nonneg_right hcomp
        (Finset.prod_nonneg fun c _ ↦ hupper c)
    _ = (C ^ (Fintype.card Coordinate - A.card)) *
        ((∏ c ∈ A, upperMass c) * (∏ c ∈ Aᶜ, lowerMass c)) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, hcard]
      ring

/-- Cross-multiplied exact-count comparison.  This form avoids division and
is often the most convenient input for a stopped-fibre mass identity. -/
theorem choose_mul_allUpperProductMass_le
    (upperMass lowerMass : Coordinate → ℝ)
    (hupper : ∀ c, 0 ≤ upperMass c)
    {C : ℝ}
    (hratio : ∀ c, upperMass c ≤ C * lowerMass c)
    (s : ℕ) :
    (Fintype.card Coordinate).choose s * allUpperProductMass upperMass ≤
      C ^ (Fintype.card Coordinate - s) *
        exactUpperCountProductMass upperMass lowerMass s := by
  classical
  let P := (Finset.univ : Finset Coordinate).powersetCard s
  have hpoint : ∀ A ∈ P,
      allUpperProductMass upperMass ≤
        C ^ (Fintype.card Coordinate - s) *
          mixedSubsetProductMass upperMass lowerMass A := by
    intro A hA
    have hcard : A.card = s := (Finset.mem_powersetCard.mp hA).2
    simpa only [hcard] using
      allUpperProductMass_le_pow_mul_mixedSubset upperMass lowerMass
        hupper hratio A
  calc
    (Fintype.card Coordinate).choose s * allUpperProductMass upperMass =
        ∑ A ∈ P, allUpperProductMass upperMass := by
      simp [P, Finset.card_powersetCard]
    _ ≤ ∑ A ∈ P,
        C ^ (Fintype.card Coordinate - s) *
          mixedSubsetProductMass upperMass lowerMass A := by
      exact Finset.sum_le_sum fun A hA ↦ hpoint A hA
    _ = C ^ (Fintype.card Coordinate - s) *
        exactUpperCountProductMass upperMass lowerMass s := by
      unfold exactUpperCountProductMass
      rw [Finset.mul_sum]

/-- Divided exact-count comparison. -/
theorem allUpperProductMass_le_choose_ratio_mul
    (upperMass lowerMass : Coordinate → ℝ)
    (hupper : ∀ c, 0 ≤ upperMass c)
    {C : ℝ}
    (hratio : ∀ c, upperMass c ≤ C * lowerMass c)
    (s : ℕ) (hs : s ≤ Fintype.card Coordinate) :
    allUpperProductMass upperMass ≤
      (C ^ (Fintype.card Coordinate - s) /
        ((Fintype.card Coordinate).choose s : ℝ)) *
          exactUpperCountProductMass upperMass lowerMass s := by
  have hchooseNat : 0 < (Fintype.card Coordinate).choose s :=
    Nat.choose_pos hs
  have hchoose : (0 : ℝ) < (Fintype.card Coordinate).choose s := by
    exact_mod_cast hchooseNat
  rw [div_mul_eq_mul_div, le_div_iff₀ hchoose]
  simpa only [mul_comm] using
    choose_mul_allUpperProductMass_le upperMass lowerMass hupper
      hratio s

/-- The literal HLOZ fixed central-count comparison, with the coordinate
cardinality exposed as the exact source count `r`. -/
theorem allUpperProductMass_le_centralReplacementRatio_mul
    (upperMass lowerMass : Coordinate → ℝ)
    (hupper : ∀ c, 0 ≤ upperMass c)
    {C : ℝ} (hC : 0 ≤ C)
    (hratio : ∀ c, upperMass c ≤ C * lowerMass c)
    (r : ℕ) (hcard : Fintype.card Coordinate = r) :
    allUpperProductMass upperMass ≤
      centralReplacementRatio C r *
        exactUpperCountProductMass upperMass lowerMass
          (centralReplacementUpperCount C r) := by
  subst r
  exact allUpperProductMass_le_choose_ratio_mul upperMass lowerMass
    hupper hratio _
    (centralReplacementUpperCount_le hC _)

/-! ## The central count is exponentially better than the source count -/

/-
The quantitative mode estimate below is being developed in a separate
downstream module.  Keeping the checked finite central-count API above
available is important for the pathwise stopped-fibre construction.

/-- The homogeneous weight of the configurations with exactly `k` upper
coordinates.  This is used only to estimate the deterministic coefficient;
the product comparison above remains fully heterogeneous. -/
def weightedChoose (C : ℝ) (r k : ℕ) : ℝ :=
  (r.choose k : ℝ) * C ^ k

lemma weightedChoose_nonneg {C : ℝ} (hC : 0 ≤ C) (r k : ℕ) :
    0 ≤ weightedChoose C r k := by
  unfold weightedChoose
  positivity

lemma weightedChoose_succ_mul (C : ℝ) (r k : ℕ) :
    weightedChoose C r (k + 1) * (k + 1 : ℝ) =
      weightedChoose C r k * (C * (r - k : ℕ)) := by
  unfold weightedChoose
  have hchoose :
      (r.choose (k + 1) : ℝ) * (k + 1 : ℕ) =
        (r.choose k : ℝ) * (r - k : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq r k
  rw [pow_succ]
  calc
    (r.choose (k + 1) : ℝ) * (C ^ k * C) * (k + 1 : ℕ) =
        ((r.choose (k + 1) : ℝ) * (k + 1 : ℕ)) * C ^ k * C := by ring
    _ = ((r.choose k : ℝ) * (r - k : ℕ)) * C ^ k * C := by rw [hchoose]
    _ = (r.choose k : ℝ) * C ^ k * (C * (r - k : ℕ)) := by ring

lemma weightedChoose_le_succ
    {C : ℝ} (hC : 0 ≤ C) {r k : ℕ}
    (hstep : (k + 1 : ℝ) ≤ C * (r - k : ℕ)) :
    weightedChoose C r k ≤ weightedChoose C r (k + 1) := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  apply (mul_le_mul_right hk).mp
  rw [weightedChoose_succ_mul]
  exact mul_le_mul_of_nonneg_left hstep (weightedChoose_nonneg hC r k)

lemma weightedChoose_succ_le
    {C : ℝ} (hC : 0 ≤ C) {r k : ℕ}
    (hstep : C * (r - k : ℕ) ≤ (k + 1 : ℝ)) :
    weightedChoose C r (k + 1) ≤ weightedChoose C r k := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  apply (mul_le_mul_right hk).mp
  rw [weightedChoose_succ_mul]
  exact mul_le_mul_of_nonneg_left hstep (weightedChoose_nonneg hC r k)

/-- The usual binomial mode, used as an intermediary. -/
def weightedChooseMode (C : ℝ) (r : ℕ) : ℕ :=
  ⌊C / (1 + C) * (r + 1)⌋₊

lemma weightedChooseMode_le
    {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    weightedChooseMode C r ≤ r := by
  unfold weightedChooseMode
  apply Nat.floor_le_of_le
  have hden : 0 < 1 + C := by linarith
  have hfrac_lt : C / (1 + C) < 1 :=
    (div_lt_one₀ hden).2 (by linarith)
  have hrpos : (0 : ℝ) < r + 1 := by positivity
  have hlt : C / (1 + C) * ((r : ℝ) + 1) < (r : ℝ) + 1 :=
    (mul_lt_mul_right hrpos).2 hfrac_lt
  have hnonneg : 0 ≤ C / (1 + C) * ((r : ℝ) + 1) :=
    mul_nonneg (div_nonneg hC hden.le) (by positivity)
  have hfloor : ⌊C / (1 + C) * ((r : ℝ) + 1)⌋₊ < r + 1 :=
    (Nat.floor_lt hnonneg).2 (by exact_mod_cast hlt)
  simpa only [Nat.cast_add, Nat.cast_one] using Nat.le_of_lt_succ hfloor

lemma weightedChoose_step_up_before_mode
    {C : ℝ} (hC : 0 ≤ C) {r k : ℕ}
    (hk : k < weightedChooseMode C r) :
    weightedChoose C r k ≤ weightedChoose C r (k + 1) := by
  apply weightedChoose_le_succ hC
  have hmodeFloor :
      (weightedChooseMode C r : ℝ) ≤
        C / (1 + C) * (r + 1 : ℕ) := by
    unfold weightedChooseMode
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.floor_le
        (mul_nonneg (div_nonneg hC (by linarith)) (by positivity)) :
          (⌊C / (1 + C) * ((r : ℝ) + 1)⌋₊ : ℝ) ≤
            C / (1 + C) * ((r : ℝ) + 1))
  have hkcast : (k + 1 : ℕ) ≤ weightedChooseMode C r := by omega
  have hbasic : (k + 1 : ℝ) ≤ C / (1 + C) * (r + 1 : ℕ) :=
    (by exact_mod_cast hkcast).trans hmodeFloor
  have hkr : k ≤ r :=
    (Nat.le_of_lt hk).trans (weightedChooseMode_le hC r)
  have hden : 0 < 1 + C := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hden] at hbasic
  rw [Nat.cast_sub hkr]
  push_cast at hbasic
  linarith

lemma weightedChoose_step_down_after_mode
    {C : ℝ} (hC : 0 ≤ C) {r k : ℕ}
    (hmode : weightedChooseMode C r ≤ k) (hkr : k < r) :
    weightedChoose C r (k + 1) ≤ weightedChoose C r k := by
  apply weightedChoose_succ_le hC
  have hmodeSucc : C / (1 + C) * (r + 1 : ℕ) <
      (weightedChooseMode C r + 1 : ℕ) := by
    unfold weightedChooseMode
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (C / (1 + C) * ((r : ℝ) + 1)))
  have hbasic : C / (1 + C) * (r + 1 : ℕ) < (k + 1 : ℕ) :=
    hmodeSucc.trans_le (by exact_mod_cast Nat.add_le_add_right hmode 1)
  have hden : 0 < 1 + C := by linarith
  have hbasic' : C * (r + 1 : ℝ) < (k + 1 : ℝ) * (1 + C) := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden] at hbasic
    simpa only [Nat.cast_add, Nat.cast_one] using hbasic
  rw [Nat.cast_sub (Nat.le_of_lt hkr)]
  push_cast
  linarith

lemma weightedChoose_le_mode
    {C : ℝ} (hC : 0 ≤ C) (r k : ℕ) (hk : k ≤ r) :
    weightedChoose C r k ≤ weightedChoose C r (weightedChooseMode C r) := by
  by_cases hleft : k ≤ weightedChooseMode C r
  · have hchain : ∀ n, k ≤ n → n ≤ weightedChooseMode C r →
        weightedChoose C r k ≤ weightedChoose C r n := by
      intro n hkn
      induction n, hkn using Nat.le_induction with
      | base =>
          intro _
          exact le_rfl
      | succ n hkn ih =>
          intro hnext
          exact (ih (by omega)).trans
            (weightedChoose_step_up_before_mode hC (by omega))
    exact hchain _ hleft le_rfl
  · have hmodek : weightedChooseMode C r ≤ k := by omega
    have hchain : ∀ n, weightedChooseMode C r ≤ n → n ≤ r →
        weightedChoose C r n ≤ weightedChoose C r (weightedChooseMode C r) := by
      intro n hmn
      induction n, hmn using Nat.le_induction with
      | base =>
          intro _
          exact le_rfl
      | succ n hmn ih =>
          intro hnext
          exact (weightedChoose_step_down_after_mode hC hmn (by omega)).trans
            (ih (by omega))
    exact hchain _ hmodek hk

lemma sum_weightedChoose (C : ℝ) (r : ℕ) :
    (1 + C) ^ r = ∑ k ∈ Finset.range (r + 1), weightedChoose C r k := by
  rw [show 1 + C = C + 1 by ring, add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [weightedChoose, one_pow, mul_one]
  ring

theorem one_add_pow_le_mode
    {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    (1 + C) ^ r ≤
      (r + 1 : ℕ) * weightedChoose C r (weightedChooseMode C r) := by
  rw [sum_weightedChoose]
  calc
    (∑ k ∈ Finset.range (r + 1), weightedChoose C r k) ≤
        ∑ _k ∈ Finset.range (r + 1),
          weightedChoose C r (weightedChooseMode C r) := by
      apply Finset.sum_le_sum
      intro k hk
      exact weightedChoose_le_mode hC r k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    _ = (r + 1 : ℕ) * weightedChoose C r (weightedChooseMode C r) := by
      simp

lemma central_le_mode {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    centralReplacementUpperCount C r ≤ weightedChooseMode C r := by
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_left (by norm_num : (r : ℝ) ≤ r + 1)
    (div_nonneg hC (by linarith))

lemma mode_le_central_add_one {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    weightedChooseMode C r ≤ centralReplacementUpperCount C r + 1 := by
  have hden : 0 < 1 + C := by linarith
  have hfrac_lt : C / (1 + C) < 1 :=
    (div_lt_one₀ hden).2 (by linarith)
  have hcenterLt : C / (1 + C) * (r : ℝ) <
      (centralReplacementUpperCount C r + 1 : ℕ) := by
    unfold centralReplacementUpperCount
    exact Nat.lt_floor_add_one _
  have hmodeArgLt : C / (1 + C) * (r + 1 : ℕ) <
      (centralReplacementUpperCount C r + 2 : ℕ) := by
    push_cast at hcenterLt ⊢
    nlinarith [div_nonneg hC hden.le]
  unfold weightedChooseMode
  have hnonneg : 0 ≤ C / (1 + C) * ((r : ℝ) + 1) :=
    mul_nonneg (div_nonneg hC hden.le) (by positivity)
  have hfloor : ⌊C / (1 + C) * ((r : ℝ) + 1)⌋₊ <
      centralReplacementUpperCount C r + 2 :=
    (Nat.floor_lt hnonneg).2 (by
      simpa only [Nat.cast_add, Nat.cast_one] using hmodeArgLt)
  exact Nat.le_of_lt_succ (by simpa only [Nat.add_assoc] using hfloor)

lemma weightedChoose_mode_le_one_add_mul_central
    {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    weightedChoose C r (weightedChooseMode C r) ≤
      (1 + C) * weightedChoose C r (centralReplacementUpperCount C r) := by
  have hcases := mode_le_central_add_one hC r
  have hle := central_le_mode hC r
  have hEq : weightedChooseMode C r = centralReplacementUpperCount C r ∨
      weightedChooseMode C r = centralReplacementUpperCount C r + 1 := by omega
  rcases hEq with h | h
  · rw [h]
    exact le_mul_of_one_le_left (weightedChoose_nonneg hC _ _)
      (by linarith)
  · rw [h]
    have hslt : centralReplacementUpperCount C r < r := by
      by_contra hn
      have hsr := centralReplacementUpperCount_le hC r
      have hsrEq : centralReplacementUpperCount C r = r := by omega
      have hmodeEq : weightedChooseMode C r = r + 1 := by omega
      exact (not_le_of_gt (Nat.lt_succ_self r))
        (hmodeEq ▸ weightedChooseMode_le hC r)
    have hcenterArgLt : C / (1 + C) * (r : ℝ) <
        (centralReplacementUpperCount C r + 1 : ℕ) := by
      unfold centralReplacementUpperCount
      exact Nat.lt_floor_add_one _
    have hden : 0 < 1 + C := by linarith
    have hstep : C * (r - centralReplacementUpperCount C r : ℕ) ≤
        (1 + C) * (centralReplacementUpperCount C r + 1 : ℕ) := by
      rw [Nat.cast_sub (Nat.le_of_lt hslt)]
      push_cast at hcenterArgLt ⊢
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden] at hcenterArgLt
      linarith
    have hpos : (0 : ℝ) < centralReplacementUpperCount C r + 1 := by positivity
    apply (mul_le_mul_right hpos).mp
    rw [weightedChoose_succ_mul]
    exact mul_le_mul_of_nonneg_left hstep
      (weightedChoose_nonneg hC r (centralReplacementUpperCount C r))

theorem one_add_pow_le_central
    {C : ℝ} (hC : 0 ≤ C) (r : ℕ) :
    (1 + C) ^ r ≤
      (r + 1 : ℕ) * (1 + C) *
        weightedChoose C r (centralReplacementUpperCount C r) := by
  exact (one_add_pow_le_mode hC r).trans <| by
    have h := mul_le_mul_of_nonneg_left
      (weightedChoose_mode_le_one_add_mul_central hC r)
      (by positivity : (0 : ℝ) ≤ (r + 1 : ℕ))
    simpa only [mul_assoc] using h

-/

end

end Erdos1165.HLOZShellZeroCentralCount
