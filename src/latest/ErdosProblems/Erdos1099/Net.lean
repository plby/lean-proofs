/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1099.Basic
import Mathlib.Analysis.Complex.Exponential

/-!
# The finite logarithmic subset net for Erdős Problem 1099

This file deliberately uses only finite sums.  The terminal error at depth `r`
is `2⁻ʳ`; no infinite product or infinite tail is needed.
-/

open Finset Set
open scoped BigOperators

namespace Erdos1099.Net

noncomputable section

/-- The `i`-th dyadic scale, written without an integer exponent. -/
def dyadic (i : ℕ) : ℝ := (1 / 2 : ℝ) ^ i

/-- The natural-logarithmic digit attached to `2^i + 1`. -/
def delta (i : ℕ) : ℝ := Real.log (1 + dyadic i)

@[simp] lemma dyadic_zero : dyadic 0 = 1 := by simp [dyadic]

lemma dyadic_pos (i : ℕ) : 0 < dyadic i := by
  exact pow_pos (by norm_num) i

lemma dyadic_nonneg (i : ℕ) : 0 ≤ dyadic i := (dyadic_pos i).le

lemma one_add_dyadic_pos (i : ℕ) : 0 < 1 + dyadic i := by
  linarith [dyadic_pos i]

lemma delta_nonneg (i : ℕ) : 0 ≤ delta i := by
  rw [delta, Real.log_nonneg_iff (one_add_dyadic_pos i)]
  linarith [dyadic_nonneg i]

lemma delta_le_dyadic (i : ℕ) : delta i ≤ dyadic i := by
  simpa [delta] using Real.log_le_sub_one_of_pos (one_add_dyadic_pos i)

lemma delta_zero : delta 0 = Real.log 2 := by norm_num [delta, dyadic]

/-- The elementary first-order part of the expansion of a finite product. -/
lemma one_add_sum_le_prod_one_add {ι : Type*}
    (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hfa : 0 ≤ f a := hf a (by simp)
      have hsum : 0 ≤ ∑ i ∈ s, f i :=
        Finset.sum_nonneg fun i hi ↦ hf i (by simp [hi])
      have hone : 0 ≤ 1 + f a := by linarith
      calc
        1 + (f a + ∑ i ∈ s, f i)
            ≤ (1 + f a) * (1 + ∑ i ∈ s, f i) := by nlinarith
        _ ≤ (1 + f a) * ∏ i ∈ s, (1 + f i) := by
          exact mul_le_mul_of_nonneg_left (ih fun i hi ↦ hf i (by simp [hi])) hone

/-- A finite geometric tail identity.  It is the source of the terminal
`dyadic r` error in the net construction. -/
lemma sum_Icc_dyadic_add_dyadic (i n : ℕ) :
    (∑ j ∈ Finset.Icc (i + 1) (i + n), dyadic j) + dyadic (i + n) = dyadic i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have htop : i + (n + 1) = (i + n) + 1 := by omega
      rw [htop, Finset.sum_Icc_succ_top (by omega)]
      have hdyadic :
          dyadic (i + n + 1) + dyadic (i + n + 1) = dyadic (i + n) := by
        simp only [dyadic, pow_succ]
        ring
      calc
        (∑ j ∈ Finset.Icc (i + 1) (i + n), dyadic j) +
              dyadic (i + n + 1) + dyadic (i + n + 1) =
            (∑ j ∈ Finset.Icc (i + 1) (i + n), dyadic j) +
              dyadic (i + n) := by rw [add_assoc, hdyadic]
        _ = dyadic i := ih

lemma sum_Icc_dyadic_add_dyadic' {i r : ℕ} (hir : i ≤ r) :
    (∑ j ∈ Finset.Icc (i + 1) r, dyadic j) + dyadic r = dyadic i := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hir
  exact sum_Icc_dyadic_add_dyadic i n

/-- The key finite digit inequality.  In paper notation this is
`δᵢ ≤ 2⁻ʳ + ∑_{i<j≤r} δⱼ`. -/
lemma delta_le_terminal_add_sum {i r : ℕ} (hir : i ≤ r) :
    delta i ≤ dyadic r + ∑ j ∈ Finset.Icc (i + 1) r, delta j := by
  let s := Finset.Icc (i + 1) r
  let P : ℝ := ∏ j ∈ s, (1 + dyadic j)
  have hP : 1 + ∑ j ∈ s, dyadic j ≤ P := by
    exact one_add_sum_le_prod_one_add s dyadic fun j _ ↦ dyadic_nonneg j
  have hsum : (∑ j ∈ s, dyadic j) + dyadic r = dyadic i := by
    simpa [s] using sum_Icc_dyadic_add_dyadic' hir
  have hPpos : 0 < P := by
    dsimp [P, s]
    exact Finset.prod_pos fun j _ ↦ one_add_dyadic_pos j
  have hmain : 1 + dyadic i ≤ Real.exp (dyadic r) * P := by
    have hexp : 1 + dyadic r ≤ Real.exp (dyadic r) := by
      simpa [add_comm] using Real.add_one_le_exp (dyadic r)
    have hleft : 0 ≤ 1 + dyadic r := by linarith [dyadic_nonneg r]
    have hright : 0 ≤ 1 + ∑ j ∈ s, dyadic j := by
      have hsnonneg : 0 ≤ ∑ j ∈ s, dyadic j :=
        Finset.sum_nonneg fun j _ ↦ dyadic_nonneg j
      linarith
    calc
      1 + dyadic i = (1 + dyadic r) + ∑ j ∈ s, dyadic j := by linarith
      _ ≤ (1 + dyadic r) * (1 + ∑ j ∈ s, dyadic j) := by
        have hsnonneg : 0 ≤ ∑ j ∈ s, dyadic j :=
          Finset.sum_nonneg fun j _ ↦ dyadic_nonneg j
        nlinarith [mul_nonneg (dyadic_nonneg r) hsnonneg]
      _ ≤ Real.exp (dyadic r) * P := by
        exact mul_le_mul hexp hP hright (Real.exp_pos _).le
  have hlog := Real.log_le_log (one_add_dyadic_pos i) hmain
  rw [Real.log_mul (Real.exp_ne_zero _) hPpos.ne', Real.log_exp] at hlog
  rw [Real.log_prod] at hlog
  · simpa [delta, s, add_comm] using hlog
  · intro j hj
    exact (one_add_dyadic_pos j).ne'

/-! ## Concrete finite subset sums -/

/-- All subset sums of the first `r` logarithmic digits. -/
def subsetSums (r : ℕ) : Set ℝ :=
  {x | ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 r ∧ x = ∑ i ∈ S, delta i}

/-- Internal interval version of the finite greedy construction. -/
lemma exists_finset_sum_net_aux (i n : ℕ) {x : ℝ}
    (hx0 : 0 ≤ x)
    (hx : x ≤ dyadic (i + n) + ∑ j ∈ Finset.Icc i (i + n), delta j) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc i (i + n) ∧
      0 ≤ x - ∑ j ∈ S, delta j ∧
      x - ∑ j ∈ S, delta j ≤ dyadic (i + n) := by
  induction n generalizing i x with
  | zero =>
      by_cases hsmall : x ≤ dyadic i
      · refine ⟨∅, by simp, by simpa, by simpa⟩
      · have hdi : delta i ≤ dyadic i := delta_le_dyadic i
        refine ⟨{i}, by simp, ?_, ?_⟩
        · simp only [Finset.sum_singleton]
          linarith
        · simpa using hx
  | succ n ih =>
      let r := i + (n + 1)
      let T := dyadic r + ∑ j ∈ Finset.Icc (i + 1) r, delta j
      have hir : i ≤ r := by simp [r]
      have hdi : delta i ≤ T := by
        simpa [T] using delta_le_terminal_add_sum hir
      have hsplit :
          (∑ j ∈ Finset.Icc i r, delta j) =
            delta i + ∑ j ∈ Finset.Icc (i + 1) r, delta j := by
        have hset : Finset.Icc i r = insert i (Finset.Icc (i + 1) r) := by
          ext j
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hset, Finset.sum_insert (by simp)]
      by_cases hsmall : x ≤ T
      · have hr : (i + 1) + n = r := by simp [r, Nat.add_assoc, Nat.add_comm n 1]
        obtain ⟨S, hSsub, hS0, hSg⟩ := ih (i := i + 1) (x := x) hx0 (by
          simpa [hr, T] using hsmall)
        refine ⟨S, ?_, hS0, ?_⟩
        · intro j hj
          have hj' := hSsub hj
          simp only [Finset.mem_Icc] at hj' ⊢
          omega
        · simpa [hr] using hSg
      · have hxsub0 : 0 ≤ x - delta i := by linarith
        have hxsubup : x - delta i ≤ T := by
          rw [hsplit] at hx
          dsimp [T]
          dsimp [r] at hx ⊢
          linarith
        have hr : (i + 1) + n = r := by simp [r, Nat.add_assoc, Nat.add_comm n 1]
        obtain ⟨S, hSsub, hS0, hSg⟩ := ih (i := i + 1) (x := x - delta i)
          hxsub0 (by simpa [hr, T] using hxsubup)
        have hiS : i ∉ S := by
          intro hi
          have := hSsub hi
          simp only [Finset.mem_Icc] at this
          omega
        refine ⟨insert i S, ?_, ?_, ?_⟩
        · intro j hj
          simp only [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · simp
          · have hj' := hSsub hj
            simp only [Finset.mem_Icc] at hj' ⊢
            omega
        · rw [Finset.sum_insert hiS]
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hS0
        · rw [Finset.sum_insert hiS]
          convert hSg using 1
          · ring
          · congr 1
            omega

/-- The concrete one-sided subset-sum net on `[0, log 2]`, with terminal
error `2⁻ʳ`. -/
lemma exists_subsetSum_below {r : ℕ} {x : ℝ}
    (hx0 : 0 ≤ x) (hx2 : x ≤ Real.log 2) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 r ∧
      0 ≤ x - ∑ i ∈ S, delta i ∧
      x - ∑ i ∈ S, delta i ≤ dyadic r := by
  have hbudget : Real.log 2 ≤ dyadic r + ∑ j ∈ Finset.Icc 1 r, delta j := by
    simpa [delta_zero] using (delta_le_terminal_add_sum (i := 0) (r := r) (Nat.zero_le r))
  cases r with
  | zero =>
      refine ⟨∅, by simp, by simpa, ?_⟩
      simpa using hx2.trans hbudget
  | succ n =>
      have hb : x ≤ dyadic (1 + n) + ∑ j ∈ Finset.Icc 1 (1 + n), delta j := by
        simpa [Nat.add_comm] using hx2.trans hbudget
      simpa [Nat.add_comm] using exists_finset_sum_net_aux 1 n hx0 hb

/-- A set is a one-sided net on `[A,B]` with error `g`.  Requiring the
approximating point itself to remain in `[A,B]` makes the mesh consequence
available at both endpoints. -/
def IsOneSidedNet (P : Set ℝ) (A B g : ℝ) : Prop :=
  ∀ x ∈ Set.Icc A B, ∃ y ∈ P ∩ Set.Icc A B, 0 ≤ x - y ∧ x - y ≤ g

/-- Every adjacent pair of points in `P ∩ [A,B]` is at distance at most `m`. -/
def HasMeshAtMost (P : Set ℝ) (A B m : ℝ) : Prop :=
  ∀ x ∈ P ∩ Set.Icc A B, ∀ y ∈ P ∩ Set.Icc A B, x < y →
    (∀ z ∈ P ∩ Set.Icc A B, ¬ (x < z ∧ z < y)) → y - x ≤ m

/-- A one-sided `g`-net has mesh at most `2g`, by applying the net property
at the midpoint of a hypothetical larger gap. -/
lemma IsOneSidedNet.hasMeshAtMost {P : Set ℝ} {A B g : ℝ}
    (hnet : IsOneSidedNet P A B g) : HasMeshAtMost P A B (2 * g) := by
  intro x hx y hy hxy hadj
  by_contra hgap
  have hmid : (x + y) / 2 ∈ Set.Icc A B := by
    constructor
    · linarith [hx.2.1, hy.2.1]
    · linarith [hx.2.2, hy.2.2]
  obtain ⟨z, hz, hz0, hzg⟩ := hnet ((x + y) / 2) hmid
  apply hadj z hz
  constructor <;> linarith

lemma subsetSums_oneSidedNet (r : ℕ) :
    IsOneSidedNet (subsetSums r) 0 (Real.log 2) (dyadic r) := by
  intro x hx
  obtain ⟨S, hSsub, hS0, hSg⟩ := exists_subsetSum_below hx.1 hx.2
  let y := ∑ i ∈ S, delta i
  have hy0 : 0 ≤ y := by
    dsimp [y]
    exact Finset.sum_nonneg fun i _ ↦ delta_nonneg i
  have hyx : y ≤ x := by linarith
  refine ⟨y, ⟨?_, hy0, hyx.trans hx.2⟩, hS0, hSg⟩
  exact ⟨S, hSsub, rfl⟩

/-- The concrete subset sums have mesh at most `2 * 2⁻ʳ = 2^(1-r)`. -/
lemma subsetSums_hasMeshAtMost (r : ℕ) :
    HasMeshAtMost (subsetSums r) 0 (Real.log 2) (2 * dyadic r) :=
  (subsetSums_oneSidedNet r).hasMeshAtMost

/-! ## Two elementary bounds used to locate the logarithmic shells -/

/-- Every finite partial digit sum is strictly below `1`. -/
lemma sum_delta_lt_one (r : ℕ) :
    (∑ i ∈ Finset.Icc 1 r, delta i) < 1 := by
  cases r with
  | zero => simp
  | succ n =>
      have hle : (∑ i ∈ Finset.Icc 1 (n + 1), delta i) ≤
          ∑ i ∈ Finset.Icc 1 (n + 1), dyadic i := by
        exact Finset.sum_le_sum fun i _ ↦ delta_le_dyadic i
      have hgeom := sum_Icc_dyadic_add_dyadic' (i := 0) (r := n + 1) (by omega)
      have hpos := dyadic_pos (n + 1)
      simp only [Nat.zero_add, dyadic_zero] at hgeom
      linarith

end

end Erdos1099.Net
