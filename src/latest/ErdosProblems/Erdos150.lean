/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 150.
https://www.erdosproblems.com/forum/thread/150

Informal authors:
- Domagoj Bradač

Formal authors:
- Aristotle
- Pietro Monticone

URLs:
- https://www.erdosproblems.com/forum/thread/150#post-5145
- https://gist.githubusercontent.com/pitmonticone/d8558d3361ad2d673b5405239ea30700/raw/c966009555b83985762dac9faaf705aad3f48199/Erdos150.lean
-/
/-
Note: this file was modified from its original form.
-/

/-
Copyright (c) 2026 Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pietro Monticone, Aristotle (Harmonic)
-/
import Mathlib

/-! # Erdős Problem 150: Minimal Vertex Cuts

We formalise Bradač's solution to Erdős Problem 150. The key result is that for any simple graph
`G` on a finite vertex set `V` and any two vertices `u ≠ v`, the number of inclusion-wise minimal
vertex sets separating `u` from `v` is at most `2 · ∑_{k=0}^{⌊|V|/3⌋} C(|V|, k)`.

This implies the growth rate `α = lim c(n)^{1/n}` satisfies `α < 2`, answering Erdős and
Nešetřil's question in the affirmative.
-/
namespace Erdos150

open Finset Fintype Real SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Definitions -/

/-- `IsSeparator G u v T` holds when `T ⊆ V \ {u,v}` separates `u` from `v`: every walk from `u`
to `v` in `G` passes through some vertex of `T`. -/
def IsSeparator (G : SimpleGraph V) (u v : V) (T : Finset V) : Prop :=
  u ∉ T ∧ v ∉ T ∧ ∀ w : G.Walk u v, ∃ x ∈ w.support, x ∈ T

/-- `IsMinSeparator G u v T` holds when `T` is an inclusion-wise minimal vertex separator of `u`
and `v` in `G`. -/
def IsMinSeparator (G : SimpleGraph V) (u v : V) (T : Finset V) : Prop :=
  IsSeparator G u v T ∧ ∀ T' : Finset V, T' ⊂ T → ¬IsSeparator G u v T'

/-- The set of all minimal `(u,v)`-separators in `G`. -/
def minSepSet (G : SimpleGraph V) (u v : V) : Set (Finset V) :=
  {T | IsMinSeparator G u v T}

/-- The number of minimal `(u,v)`-separators in `G`. -/
noncomputable def numMinSeps (G : SimpleGraph V) (u v : V) : ℕ :=
  (minSepSet G u v).ncard

/-- The connected component of `u` in `G` avoiding `T`: the set of vertices reachable from `u` via
walks whose vertices all lie outside `T`. -/
def componentAvoiding (G : SimpleGraph V) (T : Finset V) (u : V) : Set V :=
  {x : V | ∃ w : G.Walk u x, ∀ y ∈ w.support, y ∉ T}

/-- The outer neighbourhood of a set `S` in `G`: vertices outside `S` adjacent to some vertex in
`S`. -/
def outerNeighborhood (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  univ.filter fun v ↦ v ∉ S ∧ ∃ u ∈ S, G.Adj u v

/-! ## Helper lemmas -/

omit [Fintype V] [DecidableEq V] in
/-- A vertex belongs to its own component (when not in `T`). -/
lemma mem_componentAvoiding_self (G : SimpleGraph V) (T : Finset V) (u : V) (hu : u ∉ T) :
    u ∈ componentAvoiding G T u :=
  ⟨.nil, fun y hy ↦ by
    simp only [Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hy; rwa [hy]⟩

omit [Fintype V] [DecidableEq V] in
/-- The component avoiding `T` is disjoint from `T`. -/
lemma componentAvoiding_disjoint_T (G : SimpleGraph V) (T : Finset V) (u : V) :
    Disjoint (componentAvoiding G T u) (↑T : Set V) := by
  rw [Set.disjoint_left]
  intro x hx
  obtain ⟨w, hw⟩ := hx
  induction w <;> aesop

omit [Fintype V] [DecidableEq V] in
/-- The component is closed under adjacency outside `T`. -/
lemma componentAvoiding_adj_closed (G : SimpleGraph V) (T : Finset V) (u x y : V)
    (hx : x ∈ componentAvoiding G T u) (hy : y ∉ T) (hadj : G.Adj x y) :
    y ∈ componentAvoiding G T u := by
  obtain ⟨w, hw⟩ := hx
  exact ⟨w.append (.cons hadj .nil), by simp; aesop⟩

omit [Fintype V] [DecidableEq V] in
/-- When `T` separates `u` from `v`, their components are disjoint. -/
lemma componentAvoiding_disjoint_uv (G : SimpleGraph V) (T : Finset V) (u v : V)
    (hsep : IsSeparator G u v T) :
    Disjoint (componentAvoiding G T u) (componentAvoiding G T v) := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  obtain ⟨w₁, hw₁⟩ := hx₁; obtain ⟨w₂, hw₂⟩ := hx₂
  have ⟨w, hw⟩ : ∃ w : G.Walk u v, ∀ y ∈ w.support, y ∉ T :=
    ⟨w₁.append w₂.reverse, fun y hy ↦ by
      simp only [Walk.mem_support_append_iff, Walk.support_reverse] at hy; aesop⟩
  grind [hsep.2.2 w]

omit [Fintype V] [DecidableEq V] in
/-- Vertices adjacent to the component but outside it must lie in `T`. -/
lemma outerNbhd_component_sub (G : SimpleGraph V) (T : Finset V) (u : V) (x : V)
    (hx_not_comp : x ∉ componentAvoiding G T u)
    (hx_adj : ∃ y ∈ componentAvoiding G T u, G.Adj y x) :
    x ∈ (T : Set V) := by
  obtain ⟨y, hy₁, hy₂⟩ := hx_adj
  exact not_not.1 fun hx₃ ↦ hx_not_comp <|
    componentAvoiding_adj_closed G T u y x hy₁ hx₃ hy₂

omit [Fintype V] [DecidableEq V] in
/-- For a minimal separator, every vertex of `T` has a neighbour in the `u`-component.
Uses minimality: removing any vertex from `T` would reconnect `u` and `v`. -/
lemma minSep_T_sub_outerNbhd (G : SimpleGraph V) (T : Finset V) (u v : V)
    (hmin : IsMinSeparator G u v T) (x : V) (hxT : x ∈ T) :
    ∃ y ∈ componentAvoiding G T u, G.Adj y x := by
  classical
  by_contra h
  set T' := T.erase x
  have hT'_sep : IsSeparator G u v T' := by
    refine ⟨?_, ?_, ?_⟩
    · simp_all; have := hmin.1.1; aesop
    · exact fun hv ↦ hmin.1.2.1 (mem_of_mem_erase hv)
    · intro w
      by_contra h_contra
      push Not at h_contra
      have hw_support : ∀ y ∈ w.support, y ≠ x → y ∉ T := by
        grind
      have hw_support_x : x ∈ w.support := by
        have := hmin.1.2.2 w; simp_all
        grind +ring
      obtain ⟨i, hi⟩ : ∃ i, w.getVert i = x ∧ ∀ j < i, w.getVert j ≠ x := by
        obtain ⟨i, hi⟩ : ∃ i, w.getVert i = x := by
          rw [Walk.mem_support_iff_exists_getVert] at hw_support_x; tauto
        use Nat.find (⟨i, hi⟩ : ∃ i, w.getVert i = x)
        exact ⟨Nat.find_spec (⟨i, hi⟩ : ∃ i, w.getVert i = x),
          fun j hj hj' ↦ Nat.find_min (⟨i, hi⟩ : ∃ i, w.getVert i = x) hj hj'⟩
      have h_ind : ∀ j ≤ i, w.getVert j ∈ componentAvoiding G T u := by
        intro j hj
        induction j with
        | zero =>
          simp_all only [not_exists, not_and, ne_eq, zero_le, Walk.getVert_zero]
          exact mem_componentAvoiding_self G T u (by have := hmin.1.1; aesop)
        | succ j ih => grind +suggestions
      have h_adj : G.Adj (w.getVert (i - 1)) x := by
        rcases i
        · simp_all only [not_exists, not_and, nonpos_iff_eq_zero, zero_tsub]
          exact hmin.1.1 (by aesop)
        · have := h_ind _ le_rfl
          simp_all only
          exact absurd (componentAvoiding_disjoint_T G T u)
            (Set.not_disjoint_iff.mpr ⟨x, this, hxT⟩)
      exact h ⟨w.getVert (i - 1), by grind, h_adj⟩
  exact hmin.2 T' (erase_ssubset hxT) hT'_sep

omit [Fintype V] [DecidableEq V] in
/-- `IsSeparator` is symmetric in `u` and `v`. -/
lemma isSeparator_comm (G : SimpleGraph V) (u v : V) (T : Finset V) :
    IsSeparator G u v T ↔ IsSeparator G v u T := by
  constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> refine ⟨by tauto, by tauto, ?_⟩ <;>
    intro w <;> have := h₃ w.reverse <;> aesop

omit [Fintype V] [DecidableEq V] in
/-- `IsMinSeparator` is symmetric in `u` and `v`. -/
lemma isMinSeparator_comm (G : SimpleGraph V) (u v : V) (T : Finset V) :
    IsMinSeparator G u v T ↔ IsMinSeparator G v u T := by
  grind [IsMinSeparator, isSeparator_comm]

/-- For a minimal `(u,v)`-separator `T`, we have
`T = outerNeighborhood G Sᵤ` where `Sᵤ` is the `u`-component avoiding `T`. -/
lemma T_eq_outerNeighborhood_component (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
    (T : Finset V) (hT : IsMinSeparator G u v T) :
    T = outerNeighborhood G (Set.toFinite (componentAvoiding G T u)).toFinset := by
  ext x
  constructor
  · intro hxT
    obtain ⟨y, hy_comp, hy_adj⟩ := minSep_T_sub_outerNbhd G T u v hT x hxT
    exact mem_filter.mpr ⟨mem_univ x,
      fun hx ↦ (componentAvoiding_disjoint_T G T u).le_bot ⟨by aesop, hxT⟩,
      y, by aesop, hy_adj⟩
  · intro hx
    obtain ⟨y, hy, hadj⟩ := (mem_filter.mp hx).2.2
    exact outerNbhd_component_sub G T u x
      (fun hx_comp ↦ by have := (mem_filter.mp hx).2.1; aesop)
      ⟨y, by aesop, hadj⟩

/-! ## Key structural lemma -/

/-- Every minimal `(u,v)`-separator is either small
(`card ≤ ⌊|V|/3⌋`) or the outer neighbourhood of a small set.
This is the core of Bradač's pigeonhole argument. -/
lemma minSep_mem_smallOrNeighborhood (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)
    (T : Finset V) (hT : IsMinSeparator G u v T) :
    T.card ≤ Fintype.card V / 3 ∨
    ∃ S : Finset V, S.card ≤ Fintype.card V / 3 ∧ T = outerNeighborhood G S := by
  by_cases h : T.card ≤ Fintype.card V / 3
  · exact Or.inl h
  · set Su := (Set.toFinite (componentAvoiding G T u)).toFinset
    set Sv := (Set.toFinite (componentAvoiding G T v)).toFinset
    have h_union : Su.card + Sv.card + T.card ≤ Fintype.card V := by
      rw [← card_union_of_disjoint,
          ← card_union_of_disjoint]
      · exact card_le_univ _
      · simp +zetaDelta only [not_le, disjoint_union_left] at *
        exact ⟨disjoint_left.mpr fun x hx hx' ↦ by
            have := componentAvoiding_disjoint_T G T u
            exact this.le_bot
              ⟨by simpa using hx, by simpa using hx'⟩,
          disjoint_left.mpr fun x hx hx' ↦ by
            have := componentAvoiding_disjoint_T G T v
            exact this.le_bot
              ⟨by simpa using hx, by simpa using hx'⟩⟩
      · exact disjoint_left.mpr fun x hxu hxv ↦
          Set.disjoint_left.mp
            (componentAvoiding_disjoint_uv G T u v hT.1)
            (Set.Finite.mem_toFinset _ |>.1 hxu)
            (Set.Finite.mem_toFinset _ |>.1 hxv)
    have : Su.card ≤ Fintype.card V / 3 ∨ Sv.card ≤ Fintype.card V / 3 := by omega
    rcases this with hSu | hSv
    · exact Or.inr ⟨Su, hSu,
        T_eq_outerNeighborhood_component G u v T hT⟩
    · exact Or.inr ⟨Sv, hSv, by
        convert T_eq_outerNeighborhood_component G v u T
          (isMinSeparator_comm G u v T |>.1 hT) using 1⟩

/-! ## Main bound -/

omit [DecidableEq V] in
/-- **Bradač's Theorem (Erdős Problem 150).** The number of minimal `(u,v)`-separators in a graph
on `n` vertices is at most `2 · ∑_{k=0}^{⌊n/3⌋} C(n, k)`. -/
theorem numMinSeps_le (G : SimpleGraph V) (u v : V) :
    numMinSeps G u v ≤
      2 * ∑ k ∈ range (Fintype.card V / 3 + 1), (Fintype.card V).choose k := by
  classical
  suffices h :
      (minSepSet G u v).ncard ≤
        (univ.filter fun S : Finset V ↦ S.card ≤ Fintype.card V / 3).card +
        (univ.filter fun S : Finset V ↦ S.card ≤ Fintype.card V / 3).card by
    convert h using 1
    rw [show (filter (fun S : Finset V ↦ S.card ≤ Fintype.card V / 3) univ) =
      Finset.biUnion (range (Fintype.card V / 3 + 1))
        fun k ↦ powersetCard k univ from ?_, card_biUnion]
    · simp [two_mul, card_powersetCard]
    · exact fun i hi j hj hij ↦ disjoint_left.mpr fun x hx hx' ↦ hij <| by
        rw [mem_powersetCard] at hx hx'; omega
    · ext S; simp [mem_biUnion, mem_powersetCard]
  have h_sub :
      minSepSet G u v ⊆
        (↑(univ.filter fun S : Finset V ↦ S.card ≤ Fintype.card V / 3) : Set (Finset V)) ∪
        (↑(image (fun S : Finset V ↦ outerNeighborhood G S)
          (univ.filter fun S : Finset V ↦ S.card ≤ Fintype.card V / 3)) :
            Set (Finset V)) := by
    intro T hT
    have := minSep_mem_smallOrNeighborhood G u v T hT
    simp only [Set.mem_union, mem_coe, mem_filter, mem_univ, true_and, mem_image]
    rcases this with h | ⟨S, hS, hTS⟩ <;> grind
  calc (minSepSet G u v).ncard
      ≤ _ := Set.ncard_le_ncard h_sub
    _ ≤ _ := Set.ncard_union_le _ _
    _ ≤ _ := Nat.add_le_add
      (by rw [Set.ncard_coe_finset]) (by rw [Set.ncard_coe_finset]; exact card_image_le)

section BradacFull

/-! ## §1. Binary entropy and the precise bound α ≤ 2^{H(1/3)}

The *binary entropy function* is
`H₂(p) = -p log₂ p - (1-p) log₂(1-p)`. Bradač's bound
`numMinSeps ≤ 2·Σ_{k≤n/3} C(n,k)` combined with the standard
entropy bound on binomial tail sums gives
`c(n)^{1/n} → α ≤ 2^{H₂(1/3)} ≈ 1.8899…`.
-/

/-- The binary entropy function
`H₂(p) = -p log₂ p - (1-p) log₂(1-p)`, using logarithm base 2.
Defined for all reals; meaningful on `[0,1]`. -/
noncomputable def binEntropy₂ (p : ℝ) : ℝ :=
  -(p * Real.logb 2 p + (1 - p) * Real.logb 2 (1 - p))

/-! ### Binomial tail sum entropy bound

The standard bound: for `0 < α < 1/2`,
`Σ_{k=0}^{⌊αn⌋} C(n,k) ≤ 2^{H₂(α)·n}`.
-/

/-- The binomial tail sum satisfies the entropy bound: for any `ε > 0`, eventually
`∑_{k=0}^{⌊n/3⌋} C(n,k) ≤ 2^{(H₂(1/3)+ε)·n}`. -/
theorem binomial_tail_entropy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∑ k ∈ range (n / 3 + 1), (n.choose k : ℝ)) ≤
        (2 : ℝ) ^ ((binEntropy₂ (1/3) + ε) * ↑n) := by
  have h_entropy_bound : ∀ n : ℕ,
      (∑ k ∈ range (n / 3 + 1), (n.choose k : ℝ)) ≤
        (n + 1) * 2 ^ ((binEntropy₂ (1 / 3) : ℝ) * n) := by
    have h_binom_sum : ∀ n : ℕ,
        (∑ k ∈ range (n / 3 + 1), (n.choose k : ℝ)) ≤
          (n + 1) * (2 : ℝ) ^ (n * (-(1 / 3 : ℝ) * Real.logb 2 (1 / 3) -
            (2 / 3 : ℝ) * Real.logb 2 (2 / 3))) := by
      intro n
      have h_binom_sum : ∀ k ∈ range (n / 3 + 1),
          (n.choose k : ℝ) ≤
            (2 : ℝ) ^ (n * (-(1 / 3 : ℝ) * Real.logb 2 (1 / 3) -
              (2 / 3 : ℝ) * Real.logb 2 (2 / 3))) := by
        intro k hk
        have h_binom : (n.choose k : ℝ) ≤
            (1 / 3) ^ (-k : ℝ) * (2 / 3) ^ (-(n - k) : ℝ) := by
          have h_binom :
              (n.choose k : ℝ) * (1 / 3 : ℝ) ^ k * (2 / 3 : ℝ) ^ (n - k) ≤ 1 := by
            have h_binom :
                (n.choose k : ℝ) * (1 / 3 : ℝ) ^ k * (2 / 3 : ℝ) ^ (n - k) ≤
                (∑ i ∈ range (n + 1),
                  (n.choose i : ℝ) * (1 / 3 : ℝ) ^ i * (2 / 3 : ℝ) ^ (n - i)) :=
              le_trans (by norm_num)
                (single_le_sum (fun i _ ↦ by positivity)
                  (mem_range.mpr (Nat.lt_succ_of_le (show k ≤ n from by
                    linarith [mem_range.mp hk, Nat.div_mul_le_self n 3]))))
            have h_binom_sum :
                ∑ i ∈ range (n + 1),
                  (n.choose i : ℝ) * (1 / 3 : ℝ) ^ i * (2 / 3 : ℝ) ^ (n - i) =
                  (1 / 3 + 2 / 3) ^ n := by
              rw [add_pow]; congr; ext; ring
            exact h_binom.trans <| h_binom_sum.symm ▸ by norm_num
          norm_num [Real.rpow_neg] at *
          rw [inv_mul_eq_div, le_div_iff₀] <;> norm_num [Real.rpow_sub] at *
          rw [le_div_iff₀ (by positivity)]
          convert mul_le_mul_of_nonneg_right h_binom
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) k) using 1
          · ring_nf
            simp [mul_assoc, ← pow_add,
              add_tsub_cancel_of_le (show k ≤ n from hk.trans (Nat.div_le_self _ _))]
          · ring
        convert h_binom.trans _ using 1 ; (
          try (norm_num [Real.rpow_def_of_pos, Real.logb]; ring_nf; norm_num))
        rw [← Real.exp_add]
        norm_num [Real.log_div]; ring_nf; norm_num
        nlinarith [Real.log_pos one_lt_two, show (k : ℝ) ≤ n / 3 by
            exact le_div_iff₀' (by norm_num) |>.2 <| by
              norm_cast; linarith [mem_range.mp hk, Nat.div_mul_le_self n 3]]
      refine le_trans (sum_le_sum h_binom_sum) ?_
      norm_num; ring_nf; norm_cast
      norm_num [Nat.succ_le_iff]
      exact mul_le_mul_of_nonneg_right
        (mod_cast Nat.div_le_self _ _) (by positivity)
    convert h_binom_sum using 3
    norm_num [binEntropy₂]; ring_nf
  have h_exp_growth_bound : ∃ N : ℕ, ∀ n ≥ N, (n + 1 : ℝ) ≤ 2 ^ (ε * n) := by
    have h_exp_growth : Filter.Tendsto
        (fun n : ℕ ↦ (n + 1 : ℝ) / 2 ^ (ε * n)) Filter.atTop (nhds 0) := by
      suffices h_log : Filter.Tendsto
          (fun m : ℝ ↦ (m / Real.log 2 + 1) / Real.exp (ε * m))
          Filter.atTop (nhds 0) by
        convert h_log.comp (tendsto_natCast_atTop_atTop.atTop_mul_const
            (Real.log_pos one_lt_two)) using 2
        norm_num [Real.rpow_def_of_pos]; ring_nf
      have h_lim : Filter.Tendsto (fun m : ℝ ↦ m / Real.exp (ε * m))
          Filter.atTop (nhds 0) := by
        suffices h_lim_y : Filter.Tendsto (fun y : ℝ ↦ y / Real.exp y)
            Filter.atTop (nhds 0) by
          have := h_lim_y.comp (Filter.tendsto_id.const_mul_atTop hε)
          convert this.const_mul ε⁻¹ using 2 <;>
            norm_num [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hε.ne']
        simpa [Real.exp_neg] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
      ring_nf
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using Filter.Tendsto.add
        (h_lim.mul_const (Real.log 2)⁻¹)
        (tendsto_inv_atTop_zero.comp
          (Real.tendsto_exp_atTop.comp (Filter.tendsto_id.atTop_mul_const hε)))
    exact Filter.eventually_atTop.mp (h_exp_growth.eventually (gt_mem_nhds zero_lt_one)) |>
      fun ⟨N, hN⟩ ↦ ⟨N, fun n hn ↦ by
        have := hN n hn; rw [div_lt_one (by positivity)] at this; linarith⟩
  obtain ⟨N, hN⟩ := h_exp_growth_bound; use N
  intro n hn
  convert le_trans (h_entropy_bound n)
    (mul_le_mul_of_nonneg_right (hN n hn)
      (by positivity)) using 1
  rw [← Real.rpow_add (by positivity)]; ring_nf

/-! ## §2. Global count `c(n)` and its bound

`c(n)` is the maximum number of minimal vertex cuts (i.e., minimal
vertex separators for *some* pair `u ≠ v`) over all simple graphs
on `n` vertices. The per-pair bound implies a global bound. -/

/-- A *minimal vertex cut* in `G` is a set that is a minimal
`(u,v)`-separator for some pair of distinct vertices `u, v`. -/
def IsMinCut (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∃ u v : V, u ≠ v ∧ IsMinSeparator G u v T

/-- The set of all minimal vertex cuts in `G`. -/
def minCutSet (G : SimpleGraph V) : Set (Finset V) :=
  {T | IsMinCut G T}

/-- The number of minimal vertex cuts in `G`. -/
noncomputable def numMinCuts (G : SimpleGraph V) : ℕ :=
  (minCutSet G).ncard

/-- `c(n)` is the maximum number of minimal vertex cuts over all simple graphs on `Fin n`. We use
`sSup` of a finite set of natural numbers. -/
noncomputable def c (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), numMinCuts G = k}

omit [Fintype V] [DecidableEq V] in
/-- Every minimal cut is a minimal separator for some pair, so the set of all minimal cuts is the
union over pairs of `minSepSet`. -/
lemma minCutSet_subset_union (G : SimpleGraph V) :
    minCutSet G ⊆ ⋃ (u : V) (v : V), minSepSet G u v := by
  intro T ⟨u, v, _, huv⟩
  exact Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨v, huv⟩⟩

/-- The sharper global bound: every minimal vertex cut is a minimal
`(u,v)`-separator for some `u, v`, so is counted by the per-pair
bound. Since the per-pair bound counts sets of size `≤ n/3` or
neighbourhoods of such sets, the global count is at most
`2 · ∑_{k≤n/3} C(n,k)`. -/
theorem c_n_bound (n : ℕ) :
    c n ≤ 2 * ∑ k ∈ range (n / 3 + 1), n.choose k := by
  refine csSup_le ?_ ?_
  · exact ⟨_, ⟨⊥, inferInstance, rfl⟩⟩
  · have h_numMinCuts_le :
        ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        numMinCuts G ≤ 2 * ∑ k ∈ range (n / 3 + 1), n.choose k := by
      intro G hG
      have h_numMinSeps_le : ∀ u v : Fin n, u ≠ v →
          numMinSeps G u v ≤ 2 * ∑ k ∈ range (n / 3 + 1), n.choose k := by
        intro u v huv
        apply Erdos150.numMinSeps_le G u v |> le_trans <| by norm_num [Fintype.card_fin]
      have h_numMinCuts_le :
          (minCutSet G).ncard ≤ 2 * ∑ k ∈ range (n / 3 + 1), n.choose k := by
        have : minCutSet G ⊆ ⋃ (u : Fin n) (v : Fin n), minSepSet G u v :=
          minCutSet_subset_union G
        have h_minSepSet_subset : ∀ u v : Fin n, u ≠ v →
            minSepSet G u v ⊆
              filter (fun T ↦ T.card ≤ n / 3 ∨
                  ∃ S : Finset (Fin n), S.card ≤ n / 3 ∧ T = outerNeighborhood G S)
                (powerset (univ : Finset (Fin n))) := by
          intro u v huv T hT
          have hT_minSep : IsMinSeparator G u v T := hT
          have := minSep_mem_smallOrNeighborhood G u v T hT_minSep
          aesop
        have h_ncard_le :
            (minCutSet G).ncard ≤
              (filter (fun T ↦ T.card ≤ n / 3 ∨
                  ∃ S : Finset (Fin n), S.card ≤ n / 3 ∧ T = outerNeighborhood G S)
                (powerset (univ : Finset (Fin n)))).card := by
          rw [← Set.ncard_coe_finset]
          exact Set.ncard_le_ncard
            (show minCutSet G ⊆ _ from fun x hx ↦ by
              rcases hx with ⟨u, v, huv, h⟩
              exact h_minSepSet_subset u v huv h)
        have h_small_card :
            (filter (fun T ↦ T.card ≤ n / 3)
              (powerset (univ : Finset (Fin n)))).card ≤
              ∑ k ∈ range (n / 3 + 1), n.choose k := by
          rw [show filter (fun T ↦ card T ≤ n / 3)
              (powerset (univ : Finset (Fin n))) =
            Finset.biUnion (range (n / 3 + 1))
              fun k ↦ powersetCard k (univ : Finset (Fin n))
            from ?_, card_biUnion] <;>
            norm_num [card_powersetCard]
          · exact fun i hi j hj hij ↦ disjoint_left.mpr fun x hx₁ hx₂ ↦ hij <| by
                  rw [mem_powersetCard] at hx₁ hx₂; aesop
          · ext; simp [mem_biUnion, mem_powersetCard]
        have h_nbhd_card :
            (filter (fun T ↦
                ∃ S : Finset (Fin n), S.card ≤ n / 3 ∧ T = outerNeighborhood G S)
              (powerset (univ : Finset (Fin n)))).card ≤
              ∑ k ∈ range (n / 3 + 1), n.choose k := by
          have h_img :
              (image (fun S : Finset (Fin n) ↦ outerNeighborhood G S)
                (filter (fun S ↦ S.card ≤ n / 3)
                  (powerset (univ : Finset (Fin n))))).card ≤
                ∑ k ∈ range (n / 3 + 1), n.choose k :=
            le_trans card_image_le h_small_card
          exact le_trans (card_le_card fun x hx ↦ by aesop) h_img
        calc (minCutSet G).ncard
            ≤ _ := h_ncard_le
          _ ≤ _ := card_le_card (fun x hx ↦ by aesop)
          _ ≤ _ := card_union_le _ _
          _ ≤ _ := add_le_add h_small_card h_nbhd_card
          _ = _ := by linarith
      exact h_numMinCuts_le
    aesop

end BradacFull

section LimitAndBound

open Filter Topology Real

/-! ## §4. The limit α exists and α ≤ 2^{H(1/3)} -/

/-- The maximum number of minimal `(u,v)`-separators over all simple graphs on `n` vertices and all
pairs `u ≠ v`. Returns `0` for `n < 2`. -/
noncomputable def maxPairSeps (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj) (u v : Fin n),
    u ≠ v ∧ numMinSeps G u v = k}

/-- The set defining `maxPairSeps` is nonempty for `n ≥ 2`. -/
lemma maxPairSeps_set_nonempty {n : ℕ} (hn : 2 ≤ n) :
    {k : ℕ | ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj) (u v : Fin n),
      u ≠ v ∧ numMinSeps G u v = k}.Nonempty := by
  by_contra h_empty
  simp_all only [Set.Nonempty, ne_eq, exists_const, Set.mem_setOf_eq, ↓existsAndEq, not_exists]
  exact absurd (h_empty ⟨0, by linarith⟩ ⟨1, by linarith⟩) (by norm_num)

/-- The set defining `maxPairSeps` is bounded above. -/
lemma maxPairSeps_bdd_above (n : ℕ) :
    BddAbove {k : ℕ | ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj) (u v : Fin n),
      u ≠ v ∧ numMinSeps G u v = k} := by
  use 2 ^ n
  rintro k ⟨G, x, u, v, huv, rfl⟩
  refine le_trans (Set.ncard_le_ncard (show minSepSet G u v ⊆ Set.univ from Set.subset_univ _)) ?_
  norm_num [Set.ncard_univ]

/-- `maxPairSeps n ≥ 1` for `n ≥ 2`. -/
lemma maxPairSeps_pos {n : ℕ} (hn : 2 ≤ n) : 0 < maxPairSeps n := by
  have h_sep : IsMinSeparator (⊥ : SimpleGraph (Fin n)) ⟨0, by linarith⟩ ⟨1, by linarith⟩ ∅ := by
    constructor <;> norm_num [IsSeparator]; rintro ⟨⟩; aesop
  exact (Nat.pos_of_ne_zero (by
    rw [numMinSeps]; exact Set.ncard_ne_zero_of_mem h_sep)).trans_le <|
      le_csSup (maxPairSeps_bdd_above n) ⟨_, inferInstance, _, _, by norm_num, rfl⟩

/-- `maxPairSeps n ≤ 2^n`. -/
lemma maxPairSeps_le_two_pow (n : ℕ) : maxPairSeps n ≤ 2 ^ n := by
  apply csSup_le'
  rintro k ⟨G, x, u, v, huv, rfl⟩
  calc numMinSeps G u v ≤ Set.univ.ncard := Set.ncard_le_ncard (Set.subset_univ _)
    _ = 2 ^ n := by norm_num [Set.ncard_univ]

/-- Every minimal separator for a specific pair is a minimal cut, so `maxPairSeps n ≤ c n`. -/
lemma maxPairSeps_le_c (n : ℕ) : maxPairSeps n ≤ c n := by
  have h_subset :
      ∀ k ∈ {k : ℕ | ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj) (u v : Fin n),
        u ≠ v ∧ numMinSeps G u v = k}, k ≤ c n := by
    intro k hk
    obtain ⟨G, x, u, v, huv, hk_eq⟩ := hk
    have h_card : numMinSeps G u v ≤ numMinCuts G := Set.ncard_le_ncard fun T hT ↦ ⟨u, v, huv, hT⟩
    exact hk_eq ▸ le_trans h_card <| le_csSup
      (Set.Finite.bddAbove <| Set.Finite.subset
        (Set.toFinite <| Set.range fun G : SimpleGraph (Fin n) ↦ numMinCuts G)
          fun x hx ↦ by aesop) ⟨G, x, rfl⟩
  exact csSup_le' h_subset

/-- The number of minimal cuts is at most `n^2 * maxPairSeps n`. -/
lemma c_le_sq_mul_maxPairSeps (n : ℕ) : c n ≤ n ^ 2 * maxPairSeps n := by
  have h_c_le : ∀ G : SimpleGraph (Fin n), numMinCuts G ≤ n ^ 2 * maxPairSeps n := by
    intro G
    have h_numMinCuts_le :
        numMinCuts G ≤ ∑ u : Fin n, ∑ v : Fin n,
          if u ≠ v then numMinSeps G u v else 0 := by
      have h_card_le :
          (minCutSet G).ncard ≤ ∑ u : Fin n, ∑ v : Fin n,
            (if u ≠ v then (minSepSet G u v).ncard else 0) := by
        have h_card_le : ∀ (S : Finset (Fin n × Fin n)),
            (⋃ p ∈ S, if p.1 ≠ p.2 then minSepSet G p.1 p.2 else ∅).ncard ≤
              ∑ p ∈ S,
                (if p.1 ≠ p.2 then (minSepSet G p.1 p.2).ncard else 0) := by
          intro S
          induction S using Finset.induction with
          | empty => norm_num [Set.ncard_empty]
          | insert _ _ h_nmem ih =>
            simp_all only [ne_eq, ite_not, mem_insert, Set.iUnion_iUnion_eq_or_left,
              sum_insert h_nmem]
            exact le_trans (Set.ncard_union_le _ _) (add_le_add (by aesop) ih)
        convert h_card_le (univ : Finset (Fin n × Fin n)) using 1
        · congr with x; aesop
        · erw [sum_product]
      convert h_card_le using 1
    have h_numMinSeps_le_maxPairSeps : ∀ u v : Fin n, u ≠ v →
        numMinSeps G u v ≤ maxPairSeps n :=
      fun u v huv ↦ le_csSup (maxPairSeps_bdd_above n) <| by grind +splitIndPred
    refine le_trans h_numMinCuts_le ?_
    refine le_trans (sum_le_sum fun i hi ↦
      sum_le_sum fun j hj ↦
        show (if i ≠ j then numMinSeps G i j else 0) ≤
          maxPairSeps n from by aesop) ?_
    norm_num; ring_nf; norm_num
  exact csSup_le' fun k hk ↦ by aesop

/-! ### Merged graph construction for super-multiplicativity -/

/-- Embedding of `G₁`'s vertex `i` into the merged graph. Maps `0..n` to `0..n` and `n+1` to
`n+m+1`. -/
def mergeEmb₁ (n m : ℕ) (i : Fin (n + 2)) : Fin (n + m + 2) :=
  if h : i.val ≤ n then ⟨i.val, by omega⟩
  else ⟨n + m + 1, by omega⟩

/-- Embedding of `G₂`'s vertex `j` into the merged graph. Maps `0` to `0`, `1..m` to `n+1..n+m`,
and `m+1` to `n+m+1`. -/
def mergeEmb₂ (n m : ℕ) (j : Fin (m + 2)) : Fin (n + m + 2) :=
  if j.val = 0 then ⟨0, by omega⟩
  else if h : j.val ≤ m then ⟨n + j.val, by omega⟩
  else ⟨n + m + 1, by omega⟩

/-- `mergeEmb₁` is injective. -/
lemma mergeEmb₁_injective (n m : ℕ) : Function.Injective (mergeEmb₁ n m) := by
  intro i j hij
  by_cases hi : i.val ≤ n
  · by_cases hj : j.val ≤ n
    · unfold mergeEmb₁ at hij; aesop
    · simp_all [Fin.ext_iff, mergeEmb₁]
  · by_cases hj : j.val ≤ n <;>
      simp_all [Fin.ext_iff, mergeEmb₁]
    · linarith
    · grind

/-- `mergeEmb₂` is injective. -/
lemma mergeEmb₂_injective (n m : ℕ) : Function.Injective (mergeEmb₂ n m) := by
  unfold mergeEmb₂; intro i j h
  rcases i with ⟨_ | i, hi⟩ <;> rcases j with ⟨_ | j, hj⟩ <;> norm_num at h ⊢
  · split_ifs at h <;> cases h
  · split_ifs at h <;> cases h
  · grind

/-- `mergeEmb₁` maps `0` to `0`. -/
lemma mergeEmb₁_source (n m : ℕ) :
    mergeEmb₁ n m ⟨0, by omega⟩ = (⟨0, by omega⟩ : Fin (n + m + 2)) := by
  unfold mergeEmb₁; aesop

/-- `mergeEmb₁` maps `n+1` to `n+m+1`. -/
lemma mergeEmb₁_sink (n m : ℕ) :
    mergeEmb₁ n m ⟨n + 1, by omega⟩ = (⟨n + m + 1, by omega⟩ : Fin (n + m + 2)) := by
  unfold mergeEmb₁; aesop

/-- `mergeEmb₂` maps `0` to `0`. -/
lemma mergeEmb₂_source (n m : ℕ) :
    mergeEmb₂ n m ⟨0, by omega⟩ = (⟨0, by omega⟩ : Fin (n + m + 2)) := by
  unfold mergeEmb₂; simp

/-- `mergeEmb₂` maps `m+1` to `n+m+1`. -/
lemma mergeEmb₂_sink (n m : ℕ) :
    mergeEmb₂ n m ⟨m + 1, by omega⟩ = (⟨n + m + 1, by omega⟩ : Fin (n + m + 2)) :=
  Eq.symm (by unfold mergeEmb₂; simp)

/-- Adjacency relation for the merged graph. -/
def mergedAdj (n m : ℕ) (G₁ : SimpleGraph (Fin (n + 2))) (G₂ : SimpleGraph (Fin (m + 2)))
    (a b : Fin (n + m + 2)) : Prop :=
  (∃ i j : Fin (n + 2), mergeEmb₁ n m i = a ∧ mergeEmb₁ n m j = b ∧ G₁.Adj i j) ∨
  (∃ i j : Fin (m + 2), mergeEmb₂ n m i = a ∧ mergeEmb₂ n m j = b ∧ G₂.Adj i j)

/-- The merged adjacency relation is symmetric. -/
lemma mergedAdj_symm (n m : ℕ) (G₁ : SimpleGraph (Fin (n + 2)))
    (G₂ : SimpleGraph (Fin (m + 2))) : Symmetric (mergedAdj n m G₁ G₂) := by
  intro a b hab
  rcases hab with
    (⟨i, j, rfl, rfl, hij⟩ | ⟨i, j, rfl, rfl, hij⟩) <;>
    [exact Or.inl ⟨j, i, rfl, rfl, G₁.symm hij⟩;
     exact Or.inr ⟨j, i, rfl, rfl, G₂.symm hij⟩]

/-- The merged adjacency relation is irreflexive. -/
lemma mergedAdj_loopless (n m : ℕ) (G₁ : SimpleGraph (Fin (n + 2)))
    (G₂ : SimpleGraph (Fin (m + 2))) : Std.Irrefl (mergedAdj n m G₁ G₂) := by
  constructor; intro a ha; obtain ⟨i, j, hi, hj, hij⟩ := ha
  · have := mergeEmb₁_injective n m (hi.trans hj.symm); aesop
  · obtain ⟨i, j, hi, hj, hij⟩ := ‹_›
    have := mergeEmb₂_injective n m (hi.trans hj.symm); aesop

/-- The merged graph on `Fin (n+m+2)`, formed by identifying the endpoints of `G₁` on `Fin (n+2)`
and `G₂` on `Fin (m+2)`. -/
def mergedGraph (n m : ℕ) (G₁ : SimpleGraph (Fin (n + 2)))
    (G₂ : SimpleGraph (Fin (m + 2))) : SimpleGraph (Fin (n + m + 2)) where
  Adj := mergedAdj n m G₁ G₂
  symm := mergedAdj_symm n m G₁ G₂
  loopless := mergedAdj_loopless n m G₁ G₂

/-- The image of `mergeEmb₁`'s internal vertices (`{1,...,n}`) is disjoint from `mergeEmb₂`'s
internal vertices (`{n+1,...,n+m}`). -/
lemma emb_images_internal_disjoint (n m : ℕ)
    (S₁ : Finset (Fin (n + 2)))
    (S₂ : Finset (Fin (m + 2)))
    (hS₁ : ∀ x ∈ S₁, x.val ≠ 0 ∧ x.val ≠ n + 1)
    (hS₂ : ∀ x ∈ S₂, x.val ≠ 0 ∧ x.val ≠ m + 1) :
    Disjoint (S₁.image (mergeEmb₁ n m))
      (S₂.image (mergeEmb₂ n m)) := by
  simp only [Finset.disjoint_left, mem_image, not_exists]
  intro a ha x hx
  grind [mergeEmb₁, mergeEmb₂]

/-- The images of `mergeEmb₁` and `mergeEmb₂` overlap only at the shared endpoints `0` and
`n+m+1`. -/
lemma mergeEmb_image_inter (n m : ℕ) (i : Fin (n + 2)) (j : Fin (m + 2))
    (h : mergeEmb₁ n m i = mergeEmb₂ n m j) :
    (i = ⟨0, by omega⟩ ∧ j = ⟨0, by omega⟩) ∨ (i = ⟨n + 1, by omega⟩ ∧ j = ⟨m + 1, by omega⟩) := by
  grind +locals

/-- If `u` is in the combined component and `v` is an adjacent vertex not in `T`, then `v` is also
in the combined component. -/
lemma merged_component_closure (n m : ℕ) (G₁ : SimpleGraph (Fin (n + 2)))
    (G₂ : SimpleGraph (Fin (m + 2))) (S₁ : Finset (Fin (n + 2))) (S₂ : Finset (Fin (m + 2)))
    (h₁ : IsSeparator G₁ ⟨0, by omega⟩ ⟨n + 1, by omega⟩ S₁)
    (h₂ : IsSeparator G₂ ⟨0, by omega⟩ ⟨m + 1, by omega⟩ S₂) (u v : Fin (n + m + 2))
    (hu : u ∈ Set.image (mergeEmb₁ n m) (componentAvoiding G₁ S₁ ⟨0, by omega⟩) ∪
      Set.image (mergeEmb₂ n m) (componentAvoiding G₂ S₂ ⟨0, by omega⟩))
    (hv : v ∉ S₁.image (mergeEmb₁ n m) ∪ S₂.image (mergeEmb₂ n m))
    (hadj : (mergedGraph n m G₁ G₂).Adj u v) :
    v ∈ Set.image (mergeEmb₁ n m) (componentAvoiding G₁ S₁ ⟨0, by omega⟩) ∪
      Set.image (mergeEmb₂ n m) (componentAvoiding G₂ S₂ ⟨0, by omega⟩) := by
  rcases hadj with h₁ | h₂
  · rcases h₁ with ⟨i, j, rfl, rfl, hij⟩
    simp_all only [IsSeparator, Fin.zero_eta, Set.mem_union, Set.mem_image, mem_union, mem_image,
      not_or, not_exists, not_and]
    rcases hu with (⟨x, hx, hx'⟩ | ⟨x, hx, hx'⟩)
    · refine Or.inl ⟨j, ?_, rfl⟩
      exact componentAvoiding_adj_closed G₁ S₁ 0 i j
        (by rwa [mergeEmb₁_injective n m hx'] at hx) (fun hj ↦ hv.1 j hj rfl) hij
    · have h_cases : x = ⟨0, by omega⟩ ∧ i = ⟨0, by omega⟩ ∨
          x = ⟨m + 1, by omega⟩ ∧ i = ⟨n + 1, by omega⟩ := by grind +locals
      cases h_cases
      · grind +suggestions
      · simp_all only [mergeEmb₁, mergeEmb₂]
        exact False.elim <| h₂.2.1 <| by
          obtain ⟨w, hw⟩ := hx
          exact False.elim <| h₂.2.2 w |> fun ⟨x, hx₁, hx₂⟩ ↦ hw x hx₁ hx₂
  · obtain ⟨i, j, rfl, rfl, hij⟩ := h₂
    simp_all only [Fin.zero_eta]
    rcases hu with hu | hu <;>
      simp_all only [Set.mem_union, Set.mem_image, (mergeEmb₂_injective n m).eq_iff,
        exists_eq_right]
    · obtain ⟨x, hx, hx'⟩ := hu
      have := mergeEmb_image_inter n m x i
      simp_all only [mem_union, mem_image, not_or, not_exists, not_and, Fin.zero_eta, forall_const]
      cases this <;> simp_all only [IsSeparator]
      · exact Or.inr ⟨SimpleGraph.Walk.cons hij SimpleGraph.Walk.nil, by aesop⟩
      · contrapose! h₁; aesop
    · exact Or.inr (componentAvoiding_adj_closed G₂ S₂ 0 i j hu (by aesop) hij)

/-- Vertices reachable from `0` in the merged graph avoiding `T = emb₁(S₁) ∪ emb₂(S₂)` are
contained in `emb₁(C₁) ∪ emb₂(C₂)`. -/
lemma merged_walk_stays_in_components (n m : ℕ) (G₁ : SimpleGraph (Fin (n + 2)))
    (G₂ : SimpleGraph (Fin (m + 2))) (S₁ : Finset (Fin (n + 2))) (S₂ : Finset (Fin (m + 2)))
    (h₁ : IsSeparator G₁ ⟨0, by omega⟩ ⟨n + 1, by omega⟩ S₁)
    (h₂ : IsSeparator G₂ ⟨0, by omega⟩ ⟨m + 1, by omega⟩ S₂) (u v : Fin (n + m + 2))
    (hu : u ∈ Set.image (mergeEmb₁ n m) (componentAvoiding G₁ S₁ ⟨0, by omega⟩) ∪
      Set.image (mergeEmb₂ n m) (componentAvoiding G₂ S₂ ⟨0, by omega⟩))
    (w : (mergedGraph n m G₁ G₂).Walk u v)
    (hw : ∀ x ∈ w.support,
      x ∉ S₁.image (mergeEmb₁ n m) ∪ S₂.image (mergeEmb₂ n m)) :
    v ∈ Set.image (mergeEmb₁ n m) (componentAvoiding G₁ S₁ ⟨0, by omega⟩) ∪
      Set.image (mergeEmb₂ n m) (componentAvoiding G₂ S₂ ⟨0, by omega⟩) := by
  revert v
  intro v w hw
  induction w with
  | nil => simp_all
  | cons hadj _ ih =>
    apply ih
    · apply merged_component_closure n m G₁ G₂ S₁ S₂ ‹_› ‹_› _ _ hu (by exact hw _ (by simp)) hadj
    · exact fun x hx ↦ hw x <| by simp [hx]

/-- The combined set `emb₁(S₁) ∪ emb₂(S₂)` is a separator in the merged graph when
`S₁` and `S₂` are separators in `G₁` and `G₂`. -/
lemma merged_isSeparator (n m : ℕ) (G₁ : SimpleGraph (Fin (n + 2)))
    (G₂ : SimpleGraph (Fin (m + 2))) (S₁ : Finset (Fin (n + 2))) (S₂ : Finset (Fin (m + 2)))
    (h₁ : IsSeparator G₁ ⟨0, by omega⟩ ⟨n + 1, by omega⟩ S₁)
    (h₂ : IsSeparator G₂ ⟨0, by omega⟩ ⟨m + 1, by omega⟩ S₂) :
    IsSeparator (mergedGraph n m G₁ G₂) ⟨0, by omega⟩ ⟨n + m + 1, by omega⟩
      (S₁.image (mergeEmb₁ n m) ∪ S₂.image (mergeEmb₂ n m)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp_all only [IsSeparator, Fin.zero_eta, mem_union, mem_image, not_or, not_exists, not_and]
    unfold mergeEmb₁ mergeEmb₂; aesop
  · simp_all only [IsSeparator, Fin.zero_eta, mem_union, mem_image, not_or, not_exists,
      mergeEmb₁, mergeEmb₂]
    grind +suggestions
  · intro w
    by_contra h_contra
    push Not at h_contra
    have h_sink_in_components :
        ⟨n + m + 1, by omega⟩ ∈
          Set.image (mergeEmb₁ n m) (componentAvoiding G₁ S₁ ⟨0, by omega⟩) ∪
          Set.image (mergeEmb₂ n m) (componentAvoiding G₂ S₂ ⟨0, by omega⟩) := by
      apply merged_walk_stays_in_components n m G₁ G₂ S₁ S₂ h₁ h₂ ⟨0, by omega⟩
        ⟨n + m + 1, by omega⟩ (Or.inl ⟨⟨0, by omega⟩,
          mem_componentAvoiding_self _ _ _ (by simpa using h₁.1), mergeEmb₁_source n m⟩) w h_contra
    rcases h_sink_in_components with h | h
    · obtain ⟨x, hx, hx'⟩ := h
      simp_all [mergeEmb₁]
      by_cases hx'' : x.val ≤ n <;> simp_all [Fin.ext_iff]
      have hx_eq : x = ⟨n + 1, by omega⟩ := Fin.ext (by linarith [Fin.is_lt x])
      have := h₁.2.2
      simp_all [IsSeparator]
      obtain ⟨w, hw⟩ := hx; specialize this w; aesop
    · obtain ⟨x, hx, hx'⟩ := h
      unfold mergeEmb₂ at hx'
      rcases x with ⟨_ | x, hx⟩ <;> norm_num at *
      simp_all only [Fin.zero_eta, Fin.ext_iff]
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ ‹_›) with h | h <;> first | omega | skip
      have : x = m := by omega
      subst this
      exact absurd hx (fun h ↦ h₂.2.1 <| by
        obtain ⟨w, hw⟩ := h; exact False.elim <| h₂.2.2 w |> fun ⟨x, hx₁, hx₂⟩ ↦ hw x hx₁ hx₂)

/-- Stronger version of `walk_map_emb₁`: tracks that the support of the lifted walk corresponds
exactly to `mergeEmb₁` applied to the original walk's support. -/
lemma walk_map_emb₁_support (n m : ℕ) (G₁ : SimpleGraph (Fin (n + 2)))
    (G₂ : SimpleGraph (Fin (m + 2))) (u v : Fin (n + 2)) (w : G₁.Walk u v) :
    ∃ w' : (mergedGraph n m G₁ G₂).Walk (mergeEmb₁ n m u) (mergeEmb₁ n m v),
      ∀ x ∈ w'.support, ∃ y ∈ w.support, x = mergeEmb₁ n m y := by
  induction w with
  | nil => exact ⟨.nil, by simp [SimpleGraph.Walk.support]⟩
  | cons hadj _ ih =>
    obtain ⟨w', hw'⟩ := ih
    exact ⟨.cons (Or.inl ⟨_, _, rfl, rfl, hadj⟩) w', by simp_all [SimpleGraph.Walk.support_cons]⟩

/-- Stronger version of `walk_map_emb₂`: tracks that the support of the lifted walk corresponds
exactly to `mergeEmb₂` applied to the original walk's support. -/
lemma walk_map_emb₂_support (n m : ℕ) (G₁ : SimpleGraph (Fin (n + 2)))
    (G₂ : SimpleGraph (Fin (m + 2))) (u v : Fin (m + 2)) (w : G₂.Walk u v) :
    ∃ w' : (mergedGraph n m G₁ G₂).Walk (mergeEmb₂ n m u) (mergeEmb₂ n m v),
      ∀ x ∈ w'.support, ∃ y ∈ w.support, x = mergeEmb₂ n m y := by
  induction w
  · exact ⟨SimpleGraph.Walk.nil, by simp⟩
  · rename_i h₁ h₂ h₃
    obtain ⟨w', hw'⟩ := h₃
    use SimpleGraph.Walk.cons
      (show (mergedGraph n m G₁ G₂).Adj (mergeEmb₂ n m _) (mergeEmb₂ n m _) from ?_) w'
    · simp_all
    · exact Or.inr ⟨_, _, rfl, rfl, h₁⟩

/-- If a walk in `G₁` avoids `S₁ \ {a}`, its image in the merged graph avoids any `T'` that is a
proper subset of `emb₁(S₁) ∪ emb₂(S₂)` missing `emb₁(a)`. -/
lemma merged_walk_avoids_sub₁ (n m : ℕ) (G₁ : SimpleGraph (Fin (n + 2)))
    (G₂ : SimpleGraph (Fin (m + 2))) (S₁ : Finset (Fin (n + 2))) (S₂ : Finset (Fin (m + 2)))
    (h₂ : IsSeparator G₂ ⟨0, by omega⟩ ⟨m + 1, by omega⟩ S₂)
    (a : Fin (n + 2)) (ha : a ∈ S₁) (T' : Finset (Fin (n + m + 2)))
    (hT' : T' ⊆ S₁.image (mergeEmb₁ n m) ∪ S₂.image (mergeEmb₂ n m))
    (ha_out : mergeEmb₁ n m a ∉ T')
    (w₁ : G₁.Walk ⟨0, by omega⟩ ⟨n + 1, by omega⟩)
    (hw₁ : ∀ y ∈ w₁.support, y ∉ S₁.erase a) :
    ∃ w' : (mergedGraph n m G₁ G₂).Walk ⟨0, by omega⟩ ⟨n + m + 1, by omega⟩,
      ∀ x ∈ w'.support, x ∉ T' := by
  obtain ⟨w', hw'⟩ :
      ∃ w' : (mergedGraph n m G₁ G₂).Walk
          (mergeEmb₁ n m ⟨0, by omega⟩) (mergeEmb₁ n m ⟨n + 1, by omega⟩),
        ∀ x ∈ w'.support, ∃ y ∈ w₁.support, x = mergeEmb₁ n m y :=
    walk_map_emb₁_support n m G₁ G₂
      ⟨0, Decidable.byContradiction fun a ↦ mergeEmb₁_source._proof_1 n a⟩
      ⟨n + 1, Decidable.byContradiction fun a ↦ mergeEmb₁_sink._proof_1 n a⟩ w₁
  use w'.copy (by exact mergeEmb₁_source n m) (by exact mergeEmb₁_sink n m)
  intro x hx hx'
  specialize hw' x
  simp_all only [Fin.zero_eta, subset_iff, mem_union, mem_image, Walk.support_copy, forall_const]
  obtain ⟨y, hy, rfl⟩ := hw'
  specialize hT' hx'
  rcases hT' with (⟨z, hz, hz'⟩ | ⟨z, hz, hz'⟩)
  · have := mergeEmb₁_injective n m hz'; aesop
  · have := mergeEmb_image_inter n m y z
    simp_all only [mem_erase, ne_eq, not_and, Fin.zero_eta, forall_const]
    cases this <;> simp_all [IsSeparator]

/-- Same as `merged_walk_avoids_sub₁` but for `G₂`. -/
lemma merged_walk_avoids_sub₂ (n m : ℕ) (G₁ : SimpleGraph (Fin (n + 2)))
    (G₂ : SimpleGraph (Fin (m + 2))) (S₁ : Finset (Fin (n + 2))) (S₂ : Finset (Fin (m + 2)))
    (h₁ : IsSeparator G₁ ⟨0, by omega⟩ ⟨n + 1, by omega⟩ S₁) (b : Fin (m + 2))
    (T' : Finset (Fin (n + m + 2)))
    (hT' : T' ⊆ S₁.image (mergeEmb₁ n m) ∪ S₂.image (mergeEmb₂ n m))
    (hb_out : mergeEmb₂ n m b ∉ T')
    (w₂ : G₂.Walk ⟨0, by omega⟩ ⟨m + 1, by omega⟩)
    (hw₂ : ∀ y ∈ w₂.support, y ∉ S₂.erase b) :
    ∃ w' : (mergedGraph n m G₁ G₂).Walk ⟨0, by omega⟩ ⟨n + m + 1, by omega⟩,
      ∀ x ∈ w'.support, x ∉ T' := by
  obtain ⟨w', hw'⟩ :=
    walk_map_emb₂_support n m G₁ G₂ ⟨0, by omega⟩ ⟨m + 1, by omega⟩ w₂
  refine ⟨w'.copy (mergeEmb₂_source n m) (mergeEmb₂_sink n m), ?_⟩
  simp_all only [Fin.zero_eta, subset_iff, mem_union, mem_image, mem_erase, ne_eq, not_and,
    Walk.support_copy]
  intro x hx hxT'
  obtain ⟨y, hy, rfl⟩ := hw' x hx
  by_cases hyb : y = b <;>
    simp_all [IsSeparator]
  obtain ⟨a, ha, ha'⟩ := hT' hxT'
  · have := mergeEmb_image_inter n m a y ha'
    simp_all; grind +ring
  · obtain ⟨a, ha, ha'⟩ := ‹_›
    have := mergeEmb₂_injective n m ha'; aesop

/-- The combined set is a minimal separator. -/
lemma merged_isMinSeparator (n m : ℕ) (G₁ : SimpleGraph (Fin (n + 2)))
    (G₂ : SimpleGraph (Fin (m + 2))) (S₁ : Finset (Fin (n + 2))) (S₂ : Finset (Fin (m + 2)))
    (h₁ : IsMinSeparator G₁ ⟨0, by omega⟩ ⟨n + 1, by omega⟩ S₁)
    (h₂ : IsMinSeparator G₂ ⟨0, by omega⟩ ⟨m + 1, by omega⟩ S₂) :
    IsMinSeparator (mergedGraph n m G₁ G₂) ⟨0, by omega⟩ ⟨n + m + 1, by omega⟩
      (S₁.image (mergeEmb₁ n m) ∪ S₂.image (mergeEmb₂ n m)) := by
  refine ⟨?_, ?_⟩
  · apply merged_isSeparator n m G₁ G₂ S₁ S₂ h₁.1 h₂.1
  · intro T' hT' hT'_sub
    by_cases h_case :
        ∃ a ∈ S₁.image (mergeEmb₁ n m), a ∉ T'
    · obtain ⟨a, ha₁, ha₂⟩ := h_case
      obtain ⟨a', ha'_mem, rfl⟩ := mem_image.mp ha₁
      have ha'_walk :
          ∃ w₁ : G₁.Walk ⟨0, by omega⟩ ⟨n + 1, by omega⟩,
            ∀ y ∈ w₁.support, y ∉ S₁.erase a' := by
        have := h₁.2 (S₁.erase a') ?_
        · simp_all only [Fin.zero_eta, IsSeparator, mem_image, mem_erase, not_and, not_forall,
            not_exists]
          exact this
            (fun h ↦ by have := h₁.1.1; aesop)
            (fun h ↦ by have := h₁.1.2.1; aesop) |>
            fun ⟨w₁, hw₁⟩ ↦ ⟨w₁, hw₁⟩
        · simp_all only [Fin.zero_eta, IsSeparator, mem_image];exact erase_ssubset ha'_mem
      obtain ⟨w₁, hw₁⟩ := ha'_walk
      obtain ⟨w', hw'⟩ :=
        merged_walk_avoids_sub₁ n m G₁ G₂ S₁ S₂ h₂.1 a' ha'_mem T' hT'.1 ha₂ w₁ hw₁
      exact absurd hT'_sub (by unfold IsSeparator; aesop)
    · obtain ⟨b, hb⟩ : ∃ b ∈ S₂.image (mergeEmb₂ n m), b ∉ T' := by grind
      obtain ⟨b', hb', hb'_not_in_T'⟩ :
          ∃ b' ∈ S₂, mergeEmb₂ n m b' = b ∧ mergeEmb₂ n m b' ∉ T' := by grind
      obtain ⟨w₂, hw₂⟩ :
          ∃ w₂ : G₂.Walk ⟨0, by omega⟩ ⟨m + 1, by omega⟩,
            ∀ y ∈ w₂.support, y ∉ S₂.erase b' := by
        have := h₂.2 (S₂.erase b') ?_ <;>
          simp_all only [Fin.zero_eta, IsSeparator, mem_image, exists_exists_and_eq_and, not_exists,
            not_and, Decidable.not_not, mem_erase, ne_eq, not_forall]
        · exact this
            (fun h ↦ by have := h₂.1.1; aesop)
            (fun h ↦ by have := h₂.1.2.1; aesop) |>
            fun ⟨w₂, hw₂⟩ ↦ ⟨w₂, hw₂⟩
        · exact erase_ssubset hb'
      obtain ⟨w', hw'⟩ : ∃ w' : (mergedGraph n m G₁ G₂).Walk ⟨0, by omega⟩ ⟨n + m + 1, by omega⟩,
        ∀ x ∈ w'.support, x ∉ T' :=
          merged_walk_avoids_sub₂ n m G₁ G₂ S₁ S₂ h₁.1 b' T' hT'.subset hb'_not_in_T'.2 w₂ hw₂
      exact absurd (hT'_sub.2.2 w') (by tauto)

/-- The map `(S₁, S₂) ↦ S₁.image mergeEmb₁ ∪ S₂.image mergeEmb₂` is injective on
pairs of min separators. -/
lemma merge_sep_injective (n m : ℕ) (G₁ : SimpleGraph (Fin (n + 2)))
    (G₂ : SimpleGraph (Fin (m + 2))) (S₁ S₁' : Finset (Fin (n + 2)))
    (S₂ S₂' : Finset (Fin (m + 2)))
    (hS₁ : IsMinSeparator G₁ ⟨0, by omega⟩ ⟨n + 1, by omega⟩ S₁)
    (hS₁' : IsMinSeparator G₁ ⟨0, by omega⟩ ⟨n + 1, by omega⟩ S₁')
    (hS₂ : IsMinSeparator G₂ ⟨0, by omega⟩ ⟨m + 1, by omega⟩ S₂)
    (hS₂' : IsMinSeparator G₂ ⟨0, by omega⟩ ⟨m + 1, by omega⟩ S₂')
    (heq : S₁.image (mergeEmb₁ n m) ∪ S₂.image (mergeEmb₂ n m) =
      S₁'.image (mergeEmb₁ n m) ∪ S₂'.image (mergeEmb₂ n m)) :
    S₁ = S₁' ∧ S₂ = S₂' := by
  have h_S₁_internal :
      ∀ x ∈ S₁, x.val ≠ 0 ∧ x.val ≠ n + 1 := by
    intro x hx; refine ⟨fun h ↦ hS₁.1.1 ?_,
      fun h ↦ hS₁.1.2.1 ?_⟩ <;>
      rwa [show x = ⟨_, _⟩ from Fin.ext h] at hx
  have h_S₂_internal :
      ∀ y ∈ S₂, y.val ≠ 0 ∧ y.val ≠ m + 1 := by
    intro y hy; refine ⟨fun h ↦ hS₂.1.1 ?_,
      fun h ↦ hS₂.1.2.1 ?_⟩ <;>
      rwa [show y = ⟨_, _⟩ from Fin.ext h] at hy
  have h_S₁'_internal :
      ∀ x ∈ S₁', x.val ≠ 0 ∧ x.val ≠ n + 1 := by
    intro x hx; refine ⟨fun h ↦ hS₁'.1.1 ?_,
      fun h ↦ hS₁'.1.2.1 ?_⟩ <;>
      rwa [show x = ⟨_, _⟩ from Fin.ext h] at hx
  have h_S₂'_internal :
      ∀ y ∈ S₂', y.val ≠ 0 ∧ y.val ≠ m + 1 := by
    intro y hy; refine ⟨fun h ↦ hS₂'.1.1 ?_,
      fun h ↦ hS₂'.1.2.1 ?_⟩ <;>
      rwa [show y = ⟨_, _⟩ from Fin.ext h] at hy
  have h_disj :
      Disjoint (S₁.image (mergeEmb₁ n m)) (S₂'.image (mergeEmb₂ n m)) ∧
      Disjoint (S₁'.image (mergeEmb₁ n m)) (S₂.image (mergeEmb₂ n m)) :=
    ⟨emb_images_internal_disjoint n m S₁ S₂' h_S₁_internal h_S₂'_internal,
      emb_images_internal_disjoint n m S₁' S₂ h_S₁'_internal h_S₂_internal⟩
  have h_eq :
      S₁.image (mergeEmb₁ n m) = S₁'.image (mergeEmb₁ n m) ∧
      S₂.image (mergeEmb₂ n m) = S₂'.image (mergeEmb₂ n m) := by
    simp_all only [Fin.zero_eta, Finset.ext_iff, mem_union, mem_image, ne_eq, Fin.val_eq_zero_iff]
    constructor <;> intro a <;> specialize heq a <;>
      simp_all [Finset.disjoint_left]
    · grind
    · grind +extAll
  exact ⟨image_injective (mergeEmb₁_injective n m) h_eq.1,
    image_injective (mergeEmb₂_injective n m) h_eq.2⟩

/-- For any `G₁`, `G₂`, the number of minimal separators in the merged graph is at least the
product of the numbers in `G₁` and `G₂`. -/
lemma numMinSeps_merged_ge_prod (n m : ℕ) (G₁ : SimpleGraph (Fin (n + 2)))
    (G₂ : SimpleGraph (Fin (m + 2))) :
    numMinSeps G₁ ⟨0, by omega⟩ ⟨n + 1, by omega⟩ * numMinSeps G₂ ⟨0, by omega⟩ ⟨m + 1, by omega⟩ ≤
      numMinSeps (mergedGraph n m G₁ G₂) ⟨0, by omega⟩ ⟨n + m + 1, by omega⟩ := by
  by_contra h_contra
  set S₁ := minSepSet G₁ ⟨0, by omega⟩ ⟨n + 1, by omega⟩
  set S₂ := minSepSet G₂ ⟨0, by omega⟩ ⟨m + 1, by omega⟩
  set S₃ := minSepSet (mergedGraph n m G₁ G₂) ⟨0, by omega⟩ ⟨n + m + 1, by omega⟩
  have h_inj : Set.InjOn
      (fun (p : Finset (Fin (n + 2)) × Finset (Fin (m + 2))) ↦
        p.1.image (mergeEmb₁ n m) ∪ p.2.image (mergeEmb₂ n m)) (S₁ ×ˢ S₂) := by
    intro p hp q hq h_eq
    have := merge_sep_injective n m G₁ G₂ p.1 q.1 p.2 q.2 hp.1 hq.1 hp.2 hq.2 h_eq
    grind [merge_sep_injective]
  have h_subset : Set.image
      (fun (p : Finset (Fin (n + 2)) × Finset (Fin (m + 2))) ↦
        p.1.image (mergeEmb₁ n m) ∪ p.2.image (mergeEmb₂ n m))
      (S₁ ×ˢ S₂) ⊆ S₃ := by
    rintro _ ⟨p, hp, rfl⟩
    exact merged_isMinSeparator n m G₁ G₂ p.1 p.2 hp.1 hp.2
  have h_card : Set.ncard (Set.image
      (fun (p : Finset (Fin (n + 2)) × Finset (Fin (m + 2))) ↦
        p.1.image (mergeEmb₁ n m) ∪ p.2.image (mergeEmb₂ n m))
      (S₁ ×ˢ S₂)) = Set.ncard S₁ * Set.ncard S₂ := by
    rw [Set.InjOn.ncard_image h_inj, Set.ncard_prod]
  exact h_contra <| h_card ▸ Set.ncard_le_ncard h_subset |> le_trans (by rfl)

/-- `σ` is a graph homomorphism from `G` to `G.comap σ⁻¹`. -/
def comapSymmHom {V : Type*} [DecidableEq V] (G : SimpleGraph V) (σ : V ≃ V) :
    G →g G.comap σ.symm :=
  ⟨σ, fun {a b} h ↦ by simp only [SimpleGraph.comap, Equiv.symm_apply_apply]; exact h⟩

/-- `σ⁻¹` is a graph homomorphism from `G.comap σ⁻¹` to `G`. -/
def comapSymmInvHom {V : Type*} [DecidableEq V] (G : SimpleGraph V) (σ : V ≃ V) :
    G.comap σ.symm →g G :=
  ⟨σ.symm, fun h ↦ h⟩

/-- `IsSeparator` is preserved under relabeling via `σ`. -/
lemma isSeparator_comap_iff {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (σ : V ≃ V) (u v : V) (T : Finset V) :
    IsSeparator (G.comap σ.symm) (σ u) (σ v) (T.image σ) ↔ IsSeparator G u v T := by
  unfold IsSeparator
  constructor <;> intro h
  · refine ⟨fun hu ↦ h.1 (mem_image_of_mem _ hu),
      fun hv ↦ h.2.1 (mem_image_of_mem _ hv), fun w ↦ ?_⟩
    obtain ⟨x, hx, hx'⟩ := h.2.2 (w.map (comapSymmHom G σ))
    unfold comapSymmHom at hx; aesop
  · simp_all only [mem_image, σ.injective.eq_iff, exists_eq_right, not_false_eq_true,
      ↓existsAndEq,and_true, true_and]
    intro w
    obtain ⟨w', hw'⟩ : ∃ w' : G.Walk u v, w'.support = w.support.map (σ.symm) := by
      refine ⟨?_, ?_⟩
      · exact (w.map (comapSymmInvHom G σ)).copy
          (by simp [comapSymmInvHom]) (by simp [comapSymmInvHom])
      · simp [comapSymmInvHom]
    obtain ⟨x, hx, hx'⟩ := h.2.2 w'; use x; aesop

/-- `IsMinSeparator` is preserved under relabeling via `σ`. -/
lemma isMinSeparator_comap_iff {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (σ : V ≃ V) (u v : V) (T : Finset V) :
    IsMinSeparator (G.comap σ.symm) (σ u) (σ v) (T.image σ) ↔ IsMinSeparator G u v T := by
  constructor
  · intro h
    constructor
    · obtain ⟨h₁, h₂⟩ := h
      convert isSeparator_comap_iff G σ u v T |>.1 h₁ using 1
    · intro T' hT' hT''
      have := h.2 (T'.image σ)
      simp_all only [ssubset_def, subset_iff, not_forall, mem_image,
        forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, EmbeddingLike.apply_eq_iff_eq,
        exists_eq_right, implies_true, and_self, forall_const]
      exact this (by rw [isSeparator_comap_iff]; tauto)
  · intro h_min_sep
    apply And.intro
    · convert isSeparator_comap_iff G σ u v T |>.2 h_min_sep.1 using 1
    · intro T' hT' h_sep'
      have h_comap : IsSeparator G u v (T'.image σ.symm) := by
        convert isSeparator_comap_iff _ _ _ _ _ |>.1 _ using 1
        exacts [inferInstance, σ, by simpa [image_image] using h_sep']
      have := h_min_sep.2 (image σ.symm T') ?_ <;> simp_all [ssubset_def]
      grind

/-- `numMinSeps` is invariant under relabeling. -/
lemma numMinSeps_comap_eq {V : Type*} (G : SimpleGraph V) (σ : V ≃ V) (u v : V) :
    numMinSeps (G.comap σ.symm) (σ u) (σ v) = numMinSeps G u v := by
  classical
  rw [numMinSeps, numMinSeps, eq_comm]
  have h_bij : minSepSet G u v =
      (minSepSet (G.comap σ.symm) (σ u) (σ v)).image (fun T ↦ T.image σ.symm) := by
    ext T; simp only [minSepSet, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hT
      use T.image σ
      convert isMinSeparator_comap_iff G σ u v T |>.2 hT using 1
      simp [Finset.ext_iff]
    · rintro ⟨T', hT', rfl⟩
      convert isMinSeparator_comap_iff G σ u v (T'.image σ.symm) |>.1 _ using 1
      simp only [image_image, Equiv.self_comp_symm, image_id]
      exact hT'
  rw [h_bij, Set.ncard_image_of_injective _ (image_injective σ.symm.injective)]

/-- Relabeling: for any `G` with pair `u ≠ v`, there exists `G'` with the same `numMinSeps` at the
canonical pair `(0, n+1)`. -/
lemma numMinSeps_perm (n : ℕ) (G : SimpleGraph (Fin (n + 2))) (u v : Fin (n + 2)) (huv : u ≠ v) :
    ∃ (G' : SimpleGraph (Fin (n + 2))) (_ : DecidableRel G'.Adj),
      numMinSeps G' ⟨0, by omega⟩ ⟨n + 1, by omega⟩ = numMinSeps G u v := by
  obtain ⟨σ, hσ⟩ :
      ∃ σ : Fin (n + 2) ≃ Fin (n + 2), σ u = ⟨0, by linarith⟩ ∧ σ v = ⟨n + 1, by linarith⟩ := by
    obtain ⟨σ, hσ⟩ : ∃ σ : Fin (n + 2) ≃ Fin (n + 2), σ u = ⟨0, by linarith⟩ :=
      ⟨Equiv.swap u ⟨0, by linarith⟩, by simp⟩
    refine ⟨Equiv.swap (σ v) ⟨n + 1, by linarith⟩ * σ, ?_, ?_⟩ <;> aesop
  grind [numMinSeps_comap_eq G σ u v]

/-- **Super-multiplicativity** (Proposition 1 in Bradač). Merging two graphs at their endpoints
yields a graph whose minimal separator count is at least the product. -/
lemma maxPairSeps_supermult (n m : ℕ) :
    maxPairSeps (n + 2) * maxPairSeps (m + 2) ≤ maxPairSeps (n + m + 2) := by
  have h_prod :
      ∀ (n m : ℕ) (G₁ : SimpleGraph (Fin (n + 2))) [DecidableRel G₁.Adj]
        (G₂ : SimpleGraph (Fin (m + 2))) [DecidableRel G₂.Adj],
      numMinSeps G₁ ⟨0, by omega⟩ ⟨n + 1, by omega⟩ *
          numMinSeps G₂ ⟨0, by omega⟩ ⟨m + 1, by omega⟩ ≤
        numMinSeps (mergedGraph n m G₁ G₂) ⟨0, by omega⟩ ⟨n + m + 1, by omega⟩ := by
    intro n m G₁ _ G₂ _
    exact numMinSeps_merged_ge_prod n m G₁ G₂
  revert h_prod; intro h
  have h_sup : ∀ (k₁ k₂ : ℕ),
        k₁ ∈ {k : ℕ |
          ∃ (G : SimpleGraph (Fin (n + 2))) (_ : DecidableRel G.Adj) (u v : Fin (n + 2)),
            u ≠ v ∧ numMinSeps G u v = k} →
        k₂ ∈ {k : ℕ |
          ∃ (G : SimpleGraph (Fin (m + 2))) (_ : DecidableRel G.Adj) (u v : Fin (m + 2)),
            u ≠ v ∧ numMinSeps G u v = k} →
        k₁ * k₂ ≤ maxPairSeps (n + m + 2) := by
    intro k₁ k₂ hk₁ hk₂
    obtain ⟨G₁, x₁, u₁, v₁, hu₁, hv₁⟩ := hk₁
    obtain ⟨G₂, x₂, u₂, v₂, hu₂, hv₂⟩ := hk₂
    obtain ⟨G₁', x₁', hG₁'⟩ := numMinSeps_perm n G₁ u₁ v₁ hu₁
    obtain ⟨G₂', x₂', hG₂'⟩ := numMinSeps_perm m G₂ u₂ v₂ hu₂
    have := h n m G₁' G₂'; simp_all only [Fin.zero_eta, forall_const, ne_eq, ge_iff_le]
    refine le_trans this (le_csSup (maxPairSeps_bdd_above _) ?_)
    simp; aesop
  apply h_sup
  · have h_nonempty : {k : ℕ |
          ∃ (G : SimpleGraph (Fin (n + 2))) (_ : DecidableRel G.Adj) (u v : Fin (n + 2)),
            u ≠ v ∧ numMinSeps G u v = k}.Nonempty :=
      ⟨_, ⟨⊤, by infer_instance, 0, 1, by norm_num, rfl⟩⟩
    exact Nat.sSup_mem h_nonempty (maxPairSeps_bdd_above _) |>
      fun ⟨G, hG, u, v, huv, h⟩ ↦ ⟨G, hG, u, v, huv, h⟩
  · convert Nat.sSup_mem (maxPairSeps_set_nonempty (show 2 ≤ m + 2 from by linarith)) using 1
    exact ⟨fun h ↦ fun _ ↦ h, fun h ↦ h (maxPairSeps_bdd_above _)⟩

/-- The sequence `n ↦ -log(maxPairSeps(n+2))` is subadditive. -/
lemma neg_log_maxPairSeps_subadditive :
    Subadditive (fun n ↦ -Real.log (maxPairSeps (n + 2) : ℝ)) := by
  intro m n; norm_num [Subadditive]
  rw [← Real.log_mul, Real.log_le_log_iff] <;> norm_cast <;> norm_num [maxPairSeps_pos]
  · convert maxPairSeps_supermult n m using 1; ring_nf
  · exact ne_of_gt (maxPairSeps_pos (by linarith))
  · exact ne_of_gt (maxPairSeps_pos (by linarith))

/-- The sequence `n ↦ -log(maxPairSeps(n+2)) / n` is bounded below. -/
lemma neg_log_maxPairSeps_bdd_below :
    BddBelow (Set.range (fun n ↦ -log (maxPairSeps (n + 2) : ℝ) / ↑n)) := by
  refine ⟨-3 * log 2, fun y hy ↦ ?_⟩
  obtain ⟨n, hn⟩ := hy
  have h_log : log (maxPairSeps (n + 2)) ≤ (n + 2) * log 2 := by
    refine le_trans (log_le_log (Nat.cast_pos.mpr <| maxPairSeps_pos <| by linarith) <|
      Nat.cast_le.mpr <| maxPairSeps_le_two_pow _) ?_
    norm_num [log_pow]
  by_cases hn : n = 0 <;> simp_all [div_eq_iff]
  · linarith [log_pos one_lt_two]
  · nlinarith [show (n : ℝ) ≥ 1 by exact Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hn),
      log_pos one_lt_two]

/-- **Proposition 1.** The limit `α = lim c(n)^{1/n}` exists. -/
theorem limit_alpha_exists :
    ∃ α : ℝ, Filter.Tendsto (fun n ↦ (c n : ℝ) ^ (1 / n : ℝ))
      Filter.atTop (nhds α) := by
  by_contra! h_contra
  obtain ⟨h, hh⟩ : ∃ h : ℝ, Filter.Tendsto
      (fun n ↦ -Real.log (maxPairSeps (n + 2) : ℝ) / (n : ℝ)) Filter.atTop (nhds h) :=
    ⟨_, neg_log_maxPairSeps_subadditive.tendsto_lim neg_log_maxPairSeps_bdd_below⟩
  have h_exp : Filter.Tendsto (fun n ↦ (maxPairSeps n : ℝ) ^ (1 / (n : ℝ)))
      Filter.atTop (nhds (Real.exp (-h))) := by
    have h_exp : Filter.Tendsto
        (fun n ↦ Real.exp (Real.log (maxPairSeps n : ℝ) / (n : ℝ)))
        Filter.atTop (nhds (Real.exp (-h))) := by
      apply Real.continuous_exp.continuousAt.tendsto.comp
      have h_log : Filter.Tendsto
          (fun n ↦ Real.log (maxPairSeps (n + 2) : ℝ) / (n + 2 : ℝ))
          Filter.atTop (nhds (-h)) := by
        have h_exp : Filter.Tendsto
            (fun n ↦ Real.log (maxPairSeps (n + 2) : ℝ) / (n : ℝ))
            Filter.atTop (nhds (-h)) := by
          simpa [neg_div, div_neg] using hh.neg
        have h_exp : Filter.Tendsto
            (fun n ↦ (Real.log (maxPairSeps (n + 2) : ℝ) / (n : ℝ)) * (n / (n + 2 : ℝ)))
            Filter.atTop (nhds (-h)) := by
          convert h_exp.mul (tendsto_natCast_div_add_atTop (2 : ℝ)) using 2; ring
        exact h_exp.congr' (by
          filter_upwards [Filter.eventually_gt_atTop 0] with n hn using by
            rw [div_mul_div_cancel₀ (by positivity)])
      rw [← Filter.tendsto_add_atTop_iff_nat 2]; aesop
    refine h_exp.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn using by
        rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr <| maxPairSeps_pos <| by linarith)]
        ring_nf
  have h_bound : ∀ n : ℕ, n ≥ 2 →
      (c n : ℝ) ^ (1 / (n : ℝ)) ≤
        (n : ℝ) ^ (2 / (n : ℝ)) * (maxPairSeps n : ℝ) ^ (1 / (n : ℝ)) := by
    intro n hn
    have h_bd : (c n : ℝ) ≤ (n : ℝ) ^ 2 * (maxPairSeps n : ℝ) := by
      exact_mod_cast c_le_sq_mul_maxPairSeps n
    convert Real.rpow_le_rpow (by positivity) h_bd (by positivity : (0 : ℝ) ≤ 1 / n) using 1
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    ring_nf
  have h_lim : Filter.Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ (2 / (n : ℝ)) * (maxPairSeps n : ℝ) ^ (1 / (n : ℝ)))
      Filter.atTop (nhds (Real.exp (-h))) := by
    convert Filter.Tendsto.mul
      (show Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (2 / (n : ℝ)))
        Filter.atTop (nhds 1) from ?_)
      h_exp using 2 <;> norm_num
    simpa using Filter.Tendsto.comp
      (show Filter.Tendsto (fun x : ℝ ↦ x ^ (2 / x)) Filter.atTop (nhds 1) from by
          simpa using tendsto_rpow_div_mul_add (2 : ℝ) (1 : ℝ) 0)
      tendsto_natCast_atTop_atTop
  exact h_contra _
    (tendsto_of_tendsto_of_tendsto_of_le_of_le' h_exp h_lim
      (by filter_upwards [Filter.eventually_ge_atTop 2] with n hn using
          Real.rpow_le_rpow (Nat.cast_nonneg _) (mod_cast maxPairSeps_le_c n) (by positivity))
      (by filter_upwards [Filter.eventually_ge_atTop 2] with n hn using h_bound n hn))

/-- **α ≤ 2^{H₂(1/3)}**. The growth rate of `c(n)` satisfies the entropy bound. -/
theorem alpha_le_two_pow_entropy
    (α : ℝ) (hα : Filter.Tendsto (fun n ↦ (c n : ℝ) ^ (1 / n : ℝ))
      Filter.atTop (nhds α)) : α ≤ 2 ^ binEntropy₂ (1 / 3) := by
  by_contra h_contra
  have h_bound : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      (c n : ℝ) ≤ 2 * (2 : ℝ) ^ ((binEntropy₂ (1 / 3) + ε) * n) := by
    intro ε hε_pos
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (2 * ∑ k ∈ range (n / 3 + 1), n.choose k : ℝ) ≤
        2 * (2 : ℝ) ^ ((binEntropy₂ (1 / 3) + ε) * n) := by
      obtain ⟨N, hN⟩ := binomial_tail_entropy_bound ε hε_pos
      use N; aesop
    exact ⟨N, fun n hn ↦ le_trans (mod_cast c_n_bound n) (hN n hn)⟩
  have h_root_bound : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      (c n : ℝ) ^ (1 / n : ℝ) ≤
        (2 : ℝ) ^ (binEntropy₂ (1 / 3) + ε) * (2 : ℝ) ^ (1 / n : ℝ) := by
    intro ε hε_pos
    obtain ⟨N, hN⟩ := h_bound ε hε_pos
    use N + 1; intro n hn
    have h_root : (c n : ℝ) ^ (1 / n : ℝ) ≤
        (2 * (2 : ℝ) ^ ((binEntropy₂ (1 / 3) + ε) * n)) ^ (1 / n : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (hN n (by linarith)) (by positivity)
    convert h_root using 1
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
    ring_nf; norm_num [show n ≠ 0 by linarith]; ring_nf
  have h_limit_bound : ∀ ε > 0, α ≤ (2 : ℝ) ^ (binEntropy₂ (1 / 3) + ε) := by
    intro ε hε_pos
    obtain ⟨N, hN⟩ := h_root_bound ε hε_pos
    have h_lim : Filter.Tendsto
        (fun n : ℕ ↦ (2 : ℝ) ^ (binEntropy₂ (1 / 3) + ε) * (2 : ℝ) ^ (1 / n : ℝ))
        Filter.atTop (nhds ((2 : ℝ) ^ (binEntropy₂ (1 / 3) + ε))) := by
      simpa using tendsto_const_nhds.mul
        (tendsto_const_nhds.rpow tendsto_inv_atTop_nhds_zero_nat (by norm_num))
    exact le_of_tendsto_of_tendsto hα h_lim
      (Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ hN n hn⟩)
  have h_limit_zero : Filter.Tendsto (fun ε : ℝ ↦ (2 : ℝ) ^ (binEntropy₂ (1 / 3) + ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((2 : ℝ) ^ binEntropy₂ (1 / 3))) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      (Continuous.tendsto' (by apply_rules [Continuous.rpow] <;> continuity) _ _ <| by norm_num)
  exact h_contra <| le_of_tendsto_of_tendsto tendsto_const_nhds h_limit_zero <|
    Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε ↦ h_limit_bound ε hε

/-- The limit `α = lim c(n)^{1/n}` exists and satisfies `α ≤ 2^{H₂(1/3)}`. -/
theorem limit_alpha_exists_and_le_two_pow_entropy :
    ∃ α, Filter.Tendsto (fun n ↦ (c n : ℝ) ^ (1 / n : ℝ)) .atTop (nhds α) ∧
      α ≤ 2 ^ binEntropy₂ (1 / 3) := by
  obtain ⟨α, hα⟩ := limit_alpha_exists
  exact ⟨α, hα, alpha_le_two_pow_entropy α hα⟩

theorem limit_alpha_exists_and_lt_two :
    ∃ α, Filter.Tendsto (fun n ↦ (c n : ℝ) ^ (1 / n : ℝ)) .atTop (nhds α) ∧
      α < 2 := by
  obtain ⟨α, hα, hα_le⟩ := limit_alpha_exists_and_le_two_pow_entropy
  refine ⟨α, hα, hα_le.trans_lt ?_⟩
  have h_entropy_eq : binEntropy₂ (1 / 3) = Real.log 3 / Real.log 2 - 2 / 3 := by
    have hlog2 : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos one_lt_two).ne'
    rw [binEntropy₂, Real.logb, Real.logb]
    norm_num [Real.log_div, Real.log_inv, Real.log_mul]
    field_simp [hlog2]
    ring
  have h_entropy_lt_one : binEntropy₂ (1 / 3) < 1 := by
    rw [h_entropy_eq]
    have hlog_pow : Real.log ((3 : ℝ) ^ 3) < Real.log ((2 : ℝ) ^ 5) := by
      exact Real.log_lt_log (by positivity) (by norm_num)
    rw [Real.log_pow, Real.log_pow] at hlog_pow
    norm_num at hlog_pow
    have hlog : Real.log (3 : ℝ) < (5 / 3 : ℝ) * Real.log 2 := by
      linarith
    have hdiv : Real.log (3 : ℝ) / Real.log 2 < (5 / 3 : ℝ) := by
      exact (div_lt_iff₀ (Real.log_pos one_lt_two)).2 (by simpa [mul_comm] using hlog)
    linarith
  convert Real.rpow_lt_rpow_of_exponent_lt one_lt_two h_entropy_lt_one
    using 1
  norm_num

#print axioms limit_alpha_exists_and_lt_two
-- 'Erdos150.limit_alpha_exists_and_lt_two' depends on axioms: [propext, Classical.choice,
-- Quot.sound]

end LimitAndBound

end Erdos150
