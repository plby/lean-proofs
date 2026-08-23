/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 191.
https://www.erdosproblems.com/forum/thread/191

Informal authors:
- Vojtěch Rödl

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos191.md
-/
import Mathlib
import Util.Ramsey

/-!
# Erdős Problem 191

For every `C > 0`, every red-blue coloring of the pairs of `{2, ..., n}` has, once
`n` is sufficiently large, a monochromatic clique whose `∑ x ∈ X, 1 / log x` is at
least `C`.

The proof is a qualitative finite specialization of the block argument of Rödl and
Conlon--Fox--Sudakov.  A deliberately coarse asymmetric Ramsey estimate supplies a
fixed positive amount of logarithmic weight in either color inside each of a family
of very widely separated blocks.  Repeated finite pigeonhole thinning makes every
pair of blocks monochromatic between them, and a final Ramsey argument on the block
indices combines enough local witnesses.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Erdos191

/-- The vertices in the finite formulation of Problem 191. -/
abbrev Vertices (n : ℕ) := {x : ℕ // x ∈ Finset.Icc 2 n}

/-- The logarithmic weight occurring in Problem 191. -/
def weight (x : ℕ) : ℝ := (Real.log (x : ℝ))⁻¹

/-- A set is monochromatic when it is a clique in the graph or in its complement. -/
def Monochromatic {α : Type*} (G : SimpleGraph α) (X : Finset α) : Prop :=
  G.IsClique X ∨ G.IsIndepSet X

/-- The exact finite assertion in Problem 191. -/
def HasLargeMonochromaticSet (C : ℝ) (n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Vertices n), ∃ X : Finset (Vertices n),
    Monochromatic G X ∧ C ≤ ∑ x ∈ X, weight x.1

/-- The inclusion of the finite interval in `ℕ`. -/
abbrev vertexEmbedding (n : ℕ) : Vertices n ↪ ℕ :=
  Function.Embedding.subtype _

/-- Extend a finite coloring to `ℕ`; vertices outside the interval have no edges. -/
def extendGraph {n : ℕ} (G : SimpleGraph (Vertices n)) : SimpleGraph ℕ :=
  G.map (vertexEmbedding n)

/-- Regard a bounded finset of naturals as a finset of interval vertices. -/
def liftFinset (n : ℕ) (S : Finset ℕ) : Finset (Vertices n) :=
  S.subtype (· ∈ Finset.Icc 2 n)

@[simp] lemma extendGraph_adj {n : ℕ} (G : SimpleGraph (Vertices n))
    (x y : Vertices n) :
    (extendGraph G).Adj x.1 y.1 ↔ G.Adj x y := by
  exact SimpleGraph.map_adj_apply

lemma map_liftFinset {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 2 n) :
    (liftFinset n S).map (vertexEmbedding n) = S := by
  exact Finset.subtype_map_of_mem hS

lemma isClique_map_iff_of_adj_iff {α β : Type*}
    {G : SimpleGraph α} {H : SimpleGraph β} (f : α ↪ β)
    (hAdj : ∀ x y, H.Adj (f x) (f y) ↔ G.Adj x y) (S : Finset α) :
    H.IsClique (S.map f) ↔ G.IsClique S := by
  constructor
  · intro h x hx y hy hxy
    apply (hAdj x y).mp
    exact h (Finset.mem_map.mpr ⟨x, hx, rfl⟩)
      (Finset.mem_map.mpr ⟨y, hy, rfl⟩) (f.injective.ne hxy)
  · intro h x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_map] at hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    apply (hAdj x y).mpr
    exact h hx hy (fun hxy' ↦ hxy (congrArg f hxy'))

lemma isIndepSet_map_iff_of_adj_iff {α β : Type*}
    {G : SimpleGraph α} {H : SimpleGraph β} (f : α ↪ β)
    (hAdj : ∀ x y, H.Adj (f x) (f y) ↔ G.Adj x y) (S : Finset α) :
    H.IsIndepSet (S.map f) ↔ G.IsIndepSet S := by
  constructor
  · intro h x hx y hy hxy hG
    exact h (Finset.mem_map.mpr ⟨x, hx, rfl⟩)
      (Finset.mem_map.mpr ⟨y, hy, rfl⟩) (f.injective.ne hxy) ((hAdj x y).mpr hG)
  · intro h x hx y hy hxy hH
    simp only [Finset.mem_coe, Finset.mem_map] at hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    exact h hx hy (fun hxy' ↦ hxy (congrArg f hxy')) ((hAdj x y).mp hH)

lemma monochromatic_map_iff_of_adj_iff {α β : Type*}
    {G : SimpleGraph α} {H : SimpleGraph β} (f : α ↪ β)
    (hAdj : ∀ x y, H.Adj (f x) (f y) ↔ G.Adj x y) (S : Finset α) :
    Monochromatic H (S.map f) ↔ Monochromatic G S := by
  simp only [Monochromatic, isClique_map_iff_of_adj_iff f hAdj S,
    isIndepSet_map_iff_of_adj_iff f hAdj S]

lemma monochromatic_extend_lift_iff {n : ℕ}
    (G : SimpleGraph (Vertices n)) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 2 n) :
    Monochromatic (extendGraph G) S ↔ Monochromatic G (liftFinset n S) := by
  simpa only [map_liftFinset hS] using
    (monochromatic_map_iff_of_adj_iff (vertexEmbedding n)
      (fun x y ↦ extendGraph_adj G x y) (liftFinset n S))

lemma sum_liftFinset {n : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 2 n) :
    (∑ x ∈ liftFinset n S, weight x.1) = ∑ x ∈ S, weight x := by
  calc
    (∑ x ∈ liftFinset n S, weight x.1) =
        ∑ x ∈ (liftFinset n S).map (vertexEmbedding n), weight x := by
      rw [Finset.sum_map]
      rfl
    _ = ∑ x ∈ S, weight x := by rw [map_liftFinset hS]

/-- The natural-number form used by the block construction. -/
def HasLargeMonochromaticSetOn (C : ℝ) (U : Finset ℕ) : Prop :=
  ∀ H : SimpleGraph ℕ, ∃ S : Finset ℕ,
    S ⊆ U ∧ Monochromatic H S ∧ C ≤ ∑ x ∈ S, weight x

lemma hasLargeMonochromaticSet_of_on {C : ℝ} {n : ℕ} {U : Finset ℕ}
    (hU : U ⊆ Finset.Icc 2 n) (h : HasLargeMonochromaticSetOn C U) :
    HasLargeMonochromaticSet C n := by
  intro G
  obtain ⟨S, hSU, hmono, hsum⟩ := h (extendGraph G)
  have hS : S ⊆ Finset.Icc 2 n := hSU.trans hU
  exact ⟨liftFinset n S, (monochromatic_extend_lift_iff G S hS).mp hmono,
    by rwa [sum_liftFinset hS]⟩

lemma weight_pos {x : ℕ} (hx : 2 ≤ x) : 0 < weight x := by
  rw [weight, inv_pos]
  exact Real.log_pos (by exact_mod_cast hx)

lemma weight_nonneg {x : ℕ} (hx : 2 ≤ x) : 0 ≤ weight x :=
  (weight_pos hx).le

/-! ## Finite pigeonhole and asymmetric Ramsey estimates -/

lemma exists_fiber_card_mul_ge {α β : Type*} [DecidableEq α]
    [Fintype β] [DecidableEq β] [Nonempty β] (s : Finset α) (f : α → β) :
    ∃ b : β, Fintype.card β * #{a ∈ s | f a = b} ≥ #s := by
  obtain ⟨b, -, hb⟩ := Finset.exists_max_image Finset.univ
    (fun b : β ↦ #{a ∈ s | f a = b}) Finset.univ_nonempty
  refine ⟨b, ?_⟩
  calc
    #s = ∑ b : β, #{a ∈ s | f a = b} := by
      exact Finset.card_eq_sum_card_fiberwise fun _ _ ↦ Finset.mem_univ _
    _ ≤ Fintype.card β * #{a ∈ s | f a = b} := by
      simpa [Nat.mul_comm] using
        Finset.sum_le_card_nsmul Finset.univ
          (fun b : β ↦ #{a ∈ s | f a = b}) #{a ∈ s | f a = b} hb

lemma exists_bool_pattern_constant_set {α γ : Type*}
    [DecidableEq α] [DecidableEq γ] (s : Finset α) (u : Finset γ)
    (pattern : α → u → Bool) :
    ∃ (p : u → Bool) (t : Finset α),
      t ⊆ s ∧ 2 ^ #u * #t ≥ #s ∧ ∀ a ∈ t, ∀ x : u, pattern a x = p x := by
  obtain ⟨p, hp⟩ := exists_fiber_card_mul_ge s pattern
  refine ⟨p, s.filter (pattern · = p), Finset.filter_subset _ _, ?_, ?_⟩
  · simpa using hp
  · intro a ha x
    exact congrFun (Finset.mem_filter.mp ha).2 x

/-- The elementary estimate `choose N m ≤ (e N / m)^m`. -/
lemma choose_le_exp_mul_div_pow (N m : ℕ) (hm : 1 ≤ m) :
    (Nat.choose N m : ℝ) ≤ (Real.exp 1 * N / m) ^ m := by
  have h_binom_le : (Nat.choose N m : ℝ) ≤ N ^ m / (m ^ m / Real.exp m) := by
    rw [le_div_iff₀ (by positivity)]
    have h_factorial : (Nat.factorial m : ℝ) ≥ (m / Real.exp 1) ^ m := by
      field_simp
      rw [div_pow, div_le_iff₀] <;> norm_num [Real.exp_pos]
      rw [Real.exp_eq_exp_ℝ]
      rw [← div_le_iff₀' (by positivity), NormedSpace.exp_eq_tsum_div]
      exact Summable.le_tsum (show Summable _ from Real.summable_pow_div_factorial _) m
        (fun _ _ ↦ by positivity)
    have h_choose : (Nat.choose N m : ℝ) ≤ N ^ m / (Nat.factorial m : ℝ) :=
      Nat.choose_le_pow_div m N
    rw [le_div_iff₀ (by positivity)] at h_choose
    exact le_trans
      (mul_le_mul_of_nonneg_left
        (by simpa [div_pow, Real.exp_nat_mul] using h_factorial)
        (Nat.cast_nonneg _)) h_choose
  convert h_binom_le using 1 <;> ring_nf
  norm_num [mul_assoc, mul_comm, mul_left_comm, ← Real.exp_nat_mul]

/-- A coarse but uniform off-diagonal estimate, sufficient for the qualitative theorem. -/
lemma ramseyNumber_mul_le_pow (q m : ℕ) (hm : 1 ≤ m) :
    Ramsey.ramseyNumber m ((2 ^ q) * m) ≤ 2 ^ ((q + 4) * m) := by
  let b : ℕ := 2 ^ q
  have hb : 1 ≤ b := by
    have : 0 < b := by positivity
    omega
  by_cases hm1 : m = 1
  · subst m
    have hR := Ramsey.ramseyNumber_le_choose 0 b
    calc
      Ramsey.ramseyNumber 1 (b * 1) = Ramsey.ramseyNumber 1 b := by rw [mul_one]
      _ ≤ Nat.choose (b - 1) 0 := by simpa using hR
      _ = 1 := Nat.choose_zero_right _
      _ ≤ 2 ^ ((q + 4) * 1) := Nat.one_le_two_pow
  have hm2 : 2 ≤ m := by omega
  have hR : Ramsey.ramseyNumber m (b * m) ≤
      Nat.choose (m - 1 + b * m - 1) (m - 1) := by
    simpa [Nat.sub_add_cancel hm] using Ramsey.ramseyNumber_le_choose (m - 1) (b * m)
  have hmbm : m ≤ b * m := by nlinarith
  have htop : m - 1 + b * m - 1 ≤ 2 * b * m := by
    calc
      m - 1 + b * m - 1 ≤ m + b * m := by omega
      _ ≤ b * m + b * m := Nat.add_le_add_right hmbm _
      _ = 2 * b * m := by ring
  have hchoose : Nat.choose (m - 1 + b * m - 1) (m - 1) ≤
      Nat.choose (2 * b * m) (m - 1) :=
    Nat.choose_le_choose (m - 1) htop
  have hbase : Real.exp 1 * (2 * b * m : ℕ) / ((m - 1 : ℕ) : ℝ) ≤
      16 * (b : ℝ) := by
    have he : Real.exp 1 ≤ 4 := Real.exp_one_lt_three.le.trans (by norm_num)
    have hmratio : (m : ℝ) ≤ 2 * (m - 1 : ℕ) := by
      exact_mod_cast (show m ≤ 2 * (m - 1) by omega)
    have hm1pos : (0 : ℝ) < (m - 1 : ℕ) := by
      exact_mod_cast (show 0 < m - 1 by omega)
    rw [div_le_iff₀ hm1pos]
    calc
      Real.exp 1 * (2 * b * m : ℕ) ≤ 4 * (2 * b * m : ℕ) := by gcongr
      _ = (8 * (b : ℝ)) * m := by norm_num; ring
      _ ≤ (8 * (b : ℝ)) * (2 * (m - 1 : ℕ)) := by gcongr
      _ = (16 * (b : ℝ)) * (m - 1 : ℕ) := by ring
  have hbinom : (Nat.choose (2 * b * m) (m - 1) : ℝ) ≤
      (16 * (b : ℝ)) ^ (m - 1) :=
    (choose_le_exp_mul_div_pow (2 * b * m) (m - 1) (by omega)).trans (by gcongr)
  have hpow_real : (Nat.choose (2 * b * m) (m - 1) : ℝ) ≤
      ((16 * b) ^ (m - 1) : ℕ) := by
    calc
      (Nat.choose (2 * b * m) (m - 1) : ℝ) ≤
          (16 * (b : ℝ)) ^ (m - 1) := hbinom
      _ = ((16 * b) ^ (m - 1) : ℕ) := by norm_num
  have hpow : Nat.choose (2 * b * m) (m - 1) ≤ (16 * b) ^ (m - 1) := by
    exact_mod_cast hpow_real
  have hbase_eq : 16 * b = 2 ^ (q + 4) := by simp [b, pow_add, mul_comm]
  have hlast : (16 * b) ^ (m - 1) ≤ 2 ^ ((q + 4) * m) := by
    rw [hbase_eq, ← pow_mul]
    exact Nat.pow_le_pow_right (by decide)
      (Nat.mul_le_mul_left (q + 4) (Nat.sub_le m 1))
  simpa [b] using hR.trans (hchoose.trans (hpow.trans hlast))

lemma weight_constant_bound (c : ℕ) :
    c * (2 * (4 * (c + 4) + 4) + 1) ≤ 2 ^ (4 * (c + 4)) := by
  calc
    c * (2 * (4 * (c + 4) + 4) + 1) ≤ 2 * (2 * c + 8) ^ 2 + 1 := by
      nlinarith
    _ ≤ 2 ^ (2 * (2 * c + 8)) := Nat.two_mul_sq_add_one_le_two_pow_two_mul _
    _ = 2 ^ (4 * (c + 4)) := by congr 1; omega

lemma constant_le_large_block_weight (c m : ℕ) (hm : 1 ≤ m) :
    (c : ℝ) ≤ ((2 ^ (4 * (c + 4)) * m : ℕ) : ℝ) *
      ((((2 * (4 * (c + 4) + 4)) * m + 1 : ℕ) : ℝ) * Real.log 2)⁻¹ := by
  let K := 2 * (4 * (c + 4) + 4)
  let b := 2 ^ (4 * (c + 4))
  have hlog_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog_le : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h.le
  have hdenom : 0 < (((K * m + 1 : ℕ) : ℝ) * Real.log 2) := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hdenom]
  have hKm : K * m + 1 ≤ (K + 1) * m := by nlinarith
  have hcb : c * (K + 1) ≤ b := by
    simpa [K, b] using weight_constant_bound c
  have hdenom_le :
      (((K * m + 1 : ℕ) : ℝ) * Real.log 2) ≤ ((K * m + 1 : ℕ) : ℝ) := by
    have hcoeff : (0 : ℝ) ≤ (K * m + 1 : ℕ) := by positivity
    simpa using mul_le_mul_of_nonneg_left hlog_le hcoeff
  calc
    (c : ℝ) * (((K * m + 1 : ℕ) : ℝ) * Real.log 2) ≤
        (c : ℝ) * ((K * m + 1 : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left hdenom_le (Nat.cast_nonneg c)
    _ ≤ (c : ℝ) * (((K + 1) * m : ℕ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hKm) (Nat.cast_nonneg c)
    _ = ((c * (K + 1) : ℕ) : ℝ) * m := by push_cast; ring
    _ ≤ (b : ℝ) * m := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcb) (Nat.cast_nonneg m)
    _ = ((b * m : ℕ) : ℝ) := by push_cast; ring

/-! ## Canonical finite block thinning -/

def CrossHomogeneous {α : Type*} (color : α → α → Bool)
    (s t : Finset α) : Prop :=
  ∃ c : Bool, ∀ x ∈ s, ∀ y ∈ t, color x y = c

lemma CrossHomogeneous.mono {α : Type*} {color : α → α → Bool}
    {s t s' t' : Finset α} (h : CrossHomogeneous color s t)
    (hs : s' ⊆ s) (ht : t' ⊆ t) : CrossHomogeneous color s' t' := by
  rcases h with ⟨c, hc⟩
  exact ⟨c, fun x hx y hy ↦ hc x (hs hx) y (ht hy)⟩

structure ThinResult {α : Type*} (color : α → α → Bool)
    (u s : Finset α) where
  pattern : u → Bool
  set : Finset α
  subset : set ⊆ s
  color_eq_pattern : ∀ x ∈ set, ∀ v : u, color v x = pattern v
  card_bound : s.card ≤ 2 ^ u.card * set.card

lemma thinResult_exists {α : Type*} (color : α → α → Bool)
    (u s : Finset α) : Nonempty (ThinResult color u s) := by
  classical
  let f : α → (u → Bool) := fun x v ↦ color v x
  rcases exists_fiber_card_mul_ge s f with ⟨p, hp⟩
  let t := s.filter fun x ↦ f x = p
  refine ⟨{
    pattern := p
    set := t
    subset := by simp [t]
    color_eq_pattern := ?_
    card_bound := ?_ }⟩
  · intro x hx v
    exact congrFun (Finset.mem_filter.mp hx).2 v
  · simpa [t, f, Fintype.card_fun] using hp

/-- Recursive cardinality budget for successive Boolean-pattern thinnings. -/
def SizedBlocks {α : Type*} : ℕ → List ℕ → List (Finset α) → Prop
  | _, [], [] => True
  | factor, u :: us, s :: ss =>
      factor * u ≤ s.card ∧ SizedBlocks (factor * 2 ^ u) us ss
  | _, _, _ => False

def PairwiseCrossHomogeneous {α : Type*} (color : α → α → Bool) :
    List (Finset α) → Prop
  | [] => True
  | s :: ss =>
      (∀ t ∈ ss, CrossHomogeneous color s t) ∧ PairwiseCrossHomogeneous color ss

lemma PairwiseCrossHomogeneous.get {α : Type*} {color : α → α → Bool}
    {ss : List (Finset α)} (h : PairwiseCrossHomogeneous color ss)
    {i j : ℕ} (hi : i < ss.length) (hj : j < ss.length) (hij : i < j) :
    CrossHomogeneous color (ss.get ⟨i, hi⟩) (ss.get ⟨j, hj⟩) := by
  induction ss generalizing i j with
  | nil => simp at hi
  | cons s ss ih =>
      simp only [PairwiseCrossHomogeneous] at h
      cases i with
      | zero =>
          have hjpos : 0 < j := hij
          obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
          simp only [List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ]
          exact h.1 _ (List.get_mem ss ⟨j, by simpa using hj⟩)
      | succ i =>
          cases j with
          | zero => omega
          | succ j =>
              simpa only [List.get_eq_getElem, List.getElem_cons_succ] using
                ih h.2 (by simpa using hi) (by simpa using hj) (by omega)

lemma crossHomogeneous_adj_dichotomy {α : Type*} (G : SimpleGraph α)
    [DecidableRel G.Adj]
    {s t : Finset α}
    (h : CrossHomogeneous (fun x y ↦ decide (G.Adj x y)) s t) :
    (∀ x ∈ s, ∀ y ∈ t, G.Adj x y) ∨
      (∀ x ∈ s, ∀ y ∈ t, ¬G.Adj x y) := by
  rcases h with ⟨c, hc⟩
  cases c with
  | false =>
      right
      intro x hx y hy
      simpa using hc x hx y hy
  | true =>
      left
      intro x hx y hy
      simpa using hc x hx y hy

lemma SizedBlocks.length_eq {α : Type*} {factor : ℕ} {us : List ℕ}
    {ss : List (Finset α)} (h : SizedBlocks factor us ss) : us.length = ss.length := by
  induction us generalizing factor ss with
  | nil => cases ss <;> simp_all [SizedBlocks]
  | cons u us ih =>
      cases ss with
      | nil => simp_all [SizedBlocks]
      | cons s ss =>
          simp only [SizedBlocks] at h
          exact congrArg Nat.succ (ih h.2)

lemma sizedBlocks_cancel_thinning {α : Type*} {factor c : ℕ}
    (hfactor : 0 < factor) {us : List ℕ} {ss ss' : List (Finset α)}
    (hsize : SizedBlocks (factor * c) us ss)
    (hthin : List.Forall₂
      (fun s s' ↦ s' ⊆ s ∧ s.card ≤ factor * s'.card) ss ss') :
    SizedBlocks c us ss' := by
  induction us generalizing factor c ss ss' with
  | nil =>
      have hslen := hsize.length_eq
      have htlen := hthin.length_eq
      cases ss <;> cases ss' <;> simp_all [SizedBlocks]
  | cons u us ih =>
      cases ss with
      | nil => simp_all [SizedBlocks]
      | cons s ss =>
          cases ss' with
          | nil => simp_all [SizedBlocks]
          | cons s' ss' =>
              simp only [SizedBlocks] at hsize ⊢
              cases hthin with
              | cons hhead htail =>
                  constructor
                  · apply le_of_mul_le_mul_left (a := factor) (by
                      calc
                        factor * (c * u) = (factor * c) * u := by ac_rfl
                        _ ≤ s.card := hsize.1
                        _ ≤ factor * s'.card := hhead.2) hfactor
                  · apply ih (factor := factor) (c := c * 2 ^ u) hfactor
                      (by simpa only [mul_assoc] using hsize.2) htail

lemma all_cross_of_forall₂_subset {α : Type*} {color : α → α → Bool}
    {s : Finset α} {ts ss : List (Finset α)}
    (hsub : List.Forall₂ (fun t u ↦ t ⊆ u) ts ss)
    (hcross : ∀ u ∈ ss, CrossHomogeneous color s u) :
    ∀ t ∈ ts, CrossHomogeneous color s t := by
  induction hsub with
  | nil => simp
  | cons htu _ ih =>
      intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact (hcross _ (by simp)).mono (fun _ h ↦ h) htu
      · exact ih (fun u hu ↦ hcross u (by simp [hu])) t ht

lemma forall₂_subset_trans {α : Type*} {ss tt uu : List (Finset α)}
    (hst : List.Forall₂ (fun s t ↦ s ⊆ t) ss tt)
    (htu : List.Forall₂ (fun t u ↦ t ⊆ u) tt uu) :
    List.Forall₂ (fun s u ↦ s ⊆ u) ss uu := by
  induction hst generalizing uu with
  | nil => cases htu; exact .nil
  | cons hhead _ ih =>
      cases htu with
      | cons hhead' htail' =>
          exact .cons (fun _ hx ↦ hhead' (hhead hx)) (ih htail')

theorem exists_canonical_subsets {α : Type*} (color : α → α → Bool)
    (d : ℕ) (samples targets : List ℕ) (blocks : List (Finset α))
    (hlen : samples.length ≤ d)
    (hsize : SizedBlocks 1 samples blocks)
    (htarget : List.Forall₂ (fun u q ↦ 2 ^ d * q ≤ u) samples targets) :
    ∃ sets : List (Finset α),
      List.Forall₂ (fun t s ↦ t ⊆ s) sets blocks ∧
      List.Forall₂ (fun t q ↦ q ≤ t.card) sets targets ∧
      PairwiseCrossHomogeneous color sets := by
  classical
  induction samples generalizing blocks targets with
  | nil =>
      cases blocks with
      | nil =>
          cases htarget with
          | nil => exact ⟨[], .nil, .nil, trivial⟩
      | cons s ss => simp [SizedBlocks] at hsize
  | cons u us ih =>
      cases blocks with
      | nil => simp [SizedBlocks] at hsize
      | cons s ss =>
          cases targets with
          | nil => cases htarget
          | cons q qs =>
              cases htarget with
              | cons htargetHead htargetTail =>
                  simp only [SizedBlocks, one_mul] at hsize
                  obtain ⟨sample, hsampleSub, hsampleCard⟩ :=
                    Finset.exists_subset_card_eq hsize.1
                  let result : ∀ j : Fin ss.length,
                      ThinResult color sample (ss.get j) :=
                    fun j ↦ Classical.choice (thinResult_exists color sample (ss.get j))
                  let thinned : List (Finset α) :=
                    List.ofFn fun j : Fin ss.length ↦ (result j).set
                  have hthin : List.Forall₂
                      (fun old new ↦ new ⊆ old ∧
                        old.card ≤ 2 ^ sample.card * new.card) ss thinned := by
                    rw [List.forall₂_iff_get]
                    constructor
                    · simp [thinned]
                    · intro i hi hi'
                      let j : Fin ss.length := ⟨i, hi⟩
                      have hget : thinned.get ⟨i, hi'⟩ = (result j).set := by
                        simp [thinned, j]
                      rw [hget]
                      exact ⟨(result j).subset, (result j).card_bound⟩
                  have hthinSub :
                      List.Forall₂ (fun new old ↦ new ⊆ old) thinned ss :=
                    hthin.flip.imp fun _ _ h ↦ h.1
                  have htailSize : SizedBlocks 1 us thinned := by
                    apply sizedBlocks_cancel_thinning
                      (factor := 2 ^ u) (c := 1) (by positivity)
                    · simpa [hsampleCard] using hsize.2
                    · simpa [hsampleCard] using hthin
                  have htailLen : us.length ≤ d :=
                    (Nat.le_succ us.length).trans (by simpa using hlen)
                  rcases ih qs thinned htailLen htailSize htargetTail with
                    ⟨tailSets, htailSub, htailTarget, htailCross⟩
                  let vector : α → (Fin ss.length → Bool) := fun x j ↦
                    if hx : x ∈ sample then (result j).pattern ⟨x, hx⟩ else false
                  rcases exists_fiber_card_mul_ge sample vector with ⟨p, hp⟩
                  let headSet : Finset α := sample.filter fun x ↦ vector x = p
                  have hheadSub : headSet ⊆ s := by
                    intro x hx
                    exact hsampleSub (Finset.mem_filter.mp hx).1
                  have hheadCard : q ≤ headSet.card := by
                    have huslen : us.length = ss.length := hsize.2.length_eq
                    have hpow : 2 ^ ss.length ≤ 2 ^ d := by
                      apply pow_le_pow_right' (by omega)
                      omega
                    have hmul : 2 ^ ss.length * q ≤ 2 ^ ss.length * headSet.card := by
                      calc
                        2 ^ ss.length * q ≤ 2 ^ d * q := Nat.mul_le_mul_right q hpow
                        _ ≤ u := htargetHead
                        _ = sample.card := hsampleCard.symm
                        _ ≤ 2 ^ ss.length * headSet.card := by
                          simpa [headSet, vector, Fintype.card_fun] using hp
                    exact Nat.le_of_mul_le_mul_left hmul (by positivity)
                  have hheadCross :
                      ∀ t ∈ thinned, CrossHomogeneous color headSet t := by
                    simp only [thinned, List.forall_mem_ofFn_iff]
                    intro j
                    refine ⟨p j, ?_⟩
                    intro x hx y hy
                    have hxsample : x ∈ sample := (Finset.mem_filter.mp hx).1
                    have hxvector : vector x = p := (Finset.mem_filter.mp hx).2
                    calc
                      color x y = (result j).pattern ⟨x, hxsample⟩ :=
                        (result j).color_eq_pattern y hy ⟨x, hxsample⟩
                      _ = vector x j := by simp [vector, hxsample]
                      _ = p j := congrFun hxvector j
                  refine ⟨headSet :: tailSets, ?_, ?_, ?_⟩
                  · exact .cons hheadSub (forall₂_subset_trans htailSub hthinSub)
                  · exact .cons hheadCard htailTarget
                  · exact ⟨all_cross_of_forall₂_subset htailSub hheadCross, htailCross⟩

/-! ## Logarithmic weights inside one dyadic block -/

lemma uniform_block_lower_bound {K m : ℕ} (hm : 1 ≤ m) :
    (((K + 1 : ℕ) : ℝ) * Real.log 2)⁻¹ ≤
      (m : ℝ) * (((K * m + 1 : ℕ) : ℝ) * Real.log 2)⁻¹ := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hleft : 0 < ((K + 1 : ℕ) : ℝ) * Real.log 2 := by positivity
  have hright : 0 < ((K * m + 1 : ℕ) : ℝ) * Real.log 2 := by positivity
  rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ hleft hright]
  have hm_real : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcoeff : ((K * m + 1 : ℕ) : ℝ) ≤
      (m : ℝ) * ((K + 1 : ℕ) : ℝ) := by
    push_cast
    nlinarith
  calc
    (1 : ℝ) * (((K * m + 1 : ℕ) : ℝ) * Real.log 2) =
        ((K * m + 1 : ℕ) : ℝ) * Real.log 2 := by ring
    _ ≤ ((m : ℝ) * ((K + 1 : ℕ) : ℝ)) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hcoeff hlog.le
    _ = (m : ℝ) * (((K + 1 : ℕ) : ℝ) * Real.log 2) := by ring

lemma weight_lower_bound_of_mem_Ico {K m x : ℕ} (hK : 1 ≤ K) (hm : 1 ≤ m)
    (hx : x ∈ Finset.Ico (2 ^ (K * m)) (2 ^ (K * m + 1))) :
    (((K * m + 1 : ℕ) : ℝ) * Real.log 2)⁻¹ ≤ weight x := by
  have hexp : 1 ≤ K * m := by
    have : 0 < K * m := Nat.mul_pos (by omega) (by omega)
    omega
  have hx_two : 2 ≤ x := by
    exact le_trans (by norm_num)
      (le_trans (Nat.pow_le_pow_right (by norm_num) hexp) (Finset.mem_Ico.mp hx).1)
  have hx_pos : (0 : ℝ) < x := by positivity
  have hupper_nat : x ≤ 2 ^ (K * m + 1) := Nat.le_of_lt (Finset.mem_Ico.mp hx).2
  have hupper : (x : ℝ) ≤ (2 : ℝ) ^ (K * m + 1) := by exact_mod_cast hupper_nat
  have hlog_upper :
      Real.log (x : ℝ) ≤ ((K * m + 1 : ℕ) : ℝ) * Real.log 2 := by
    calc
      Real.log (x : ℝ) ≤ Real.log ((2 : ℝ) ^ (K * m + 1)) :=
        Real.log_le_log hx_pos hupper
      _ = ((K * m + 1 : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 (K * m + 1)
  have hlog_pos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast hx_two)
  exact inv_anti₀ hlog_pos hlog_upper

lemma card_mul_le_sum_of_pointwise {s : Finset ℕ} {a : ℝ}
    (h : ∀ x ∈ s, a ≤ weight x) :
    (s.card : ℝ) * a ≤ ∑ x ∈ s, weight x := by
  simpa [nsmul_eq_mul] using s.card_nsmul_le_sum (fun x ↦ weight x) a h

lemma weighted_sum_lower_bound_of_subset_Ico {K m t : ℕ} {s : Finset ℕ}
    (hK : 1 ≤ K) (hm : 1 ≤ m)
    (hs : s ⊆ Finset.Ico (2 ^ (K * m)) (2 ^ (K * m + 1)))
    (hcard : s.card = t) :
    (t : ℝ) * (((K * m + 1 : ℕ) : ℝ) * Real.log 2)⁻¹ ≤
      ∑ x ∈ s, weight x := by
  rw [← hcard]
  exact card_mul_le_sum_of_pointwise fun x hx ↦
    weight_lower_bound_of_mem_Ico hK hm (hs hx)

lemma ramsey_on_finset {k l : ℕ} {α : Type*} (G : SimpleGraph α) (S : Finset α)
    (hcard : Ramsey.ramseyNumber k l ≤ S.card) :
    ∃ T : Finset α, T ⊆ S ∧ (G.IsNClique k T ∨ G.IsNIndepSet l T) := by
  classical
  let H : SimpleGraph {x // x ∈ (↑S : Set α)} := G.induce (↑S : Set α)
  have hprop : Ramsey.RamseyProperty k l S.card :=
    Ramsey.ramseyProperty_of_ramseyNumber_le hcard
  have hramsey : ¬ (H.CliqueFree k ∧ H.IndepSetFree l) :=
    Ramsey.ramseyProperty_of_card (by simp) hprop H
  by_cases hc : H.CliqueFree k
  · have hi : ¬ H.IndepSetFree l := fun hi ↦ hramsey ⟨hc, hi⟩
    simp only [SimpleGraph.IndepSetFree] at hi
    push Not at hi
    obtain ⟨t, ht⟩ := hi
    refine ⟨t.map (.subtype _), ?_, Or.inr ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact y.property
    · have htInd :
          (((⊤ : SimpleGraph.Subgraph G).induce (↑S : Set α)).coe).IsNIndepSet l t := by
        rw [← SimpleGraph.induce_eq_coe_induce_top]
        exact ht
      exact (SimpleGraph.isNIndepSet_induce (G := G)).mp htInd
  · simp only [SimpleGraph.CliqueFree] at hc
    push Not at hc
    obtain ⟨t, ht⟩ := hc
    refine ⟨t.map (.subtype _), ?_, Or.inl ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact y.property
    · have htInd :
          (((⊤ : SimpleGraph.Subgraph G).induce (↑S : Set α)).coe).IsNClique k t := by
        rw [← SimpleGraph.induce_eq_coe_induce_top]
        exact ht
      exact htInd.of_induce

private lemma exists_small_clique_of_ramsey {small big : ℕ} {α : Type*}
    (G : SimpleGraph α) (S : Finset α)
    (hramsey : Ramsey.ramseyNumber small big ≤ S.card)
    (hlargeImpossible : ∀ T : Finset α, T ⊆ S → G.IsNIndepSet big T → False) :
    ∃ T : Finset α, T ⊆ S ∧ G.IsNClique small T := by
  obtain ⟨T, hTS, hclique | hindep⟩ := ramsey_on_finset G S hramsey
  · exact ⟨T, hTS, hclique⟩
  · exact (hlargeImpossible T hTS hindep).elim

lemma exists_both_colors_in_block_uniform {K m big : ℕ} {C : ℝ}
    (G : SimpleGraph ℕ) (S : Finset ℕ)
    (hK : 1 ≤ K) (hm : 1 ≤ m)
    (hS : S ⊆ Finset.Ico (2 ^ (K * m)) (2 ^ (K * m + 1)))
    (hramsey : Ramsey.ramseyNumber m big ≤ S.card)
    (hbig : C ≤ (big : ℝ) * (((K * m + 1 : ℕ) : ℝ) * Real.log 2)⁻¹)
    (hno : ∀ T : Finset ℕ, T ⊆ S → Monochromatic G T →
      ¬ C ≤ ∑ x ∈ T, weight x) :
    ∃ R B : Finset ℕ,
      R ⊆ S ∧ B ⊆ S ∧ G.IsNClique m R ∧ G.IsNIndepSet m B ∧
      (((K + 1 : ℕ) : ℝ) * Real.log 2)⁻¹ ≤ ∑ x ∈ R, weight x ∧
      (((K + 1 : ℕ) : ℝ) * Real.log 2)⁻¹ ≤ ∑ x ∈ B, weight x := by
  classical
  have hlargeG : ∀ T : Finset ℕ, T ⊆ S → G.IsNIndepSet big T → False := by
    intro T hTS hT
    apply hno T hTS (Or.inr hT.isIndepSet)
    exact hbig.trans
      (weighted_sum_lower_bound_of_subset_Ico hK hm (hTS.trans hS) hT.card_eq)
  obtain ⟨R, hRS, hR⟩ :=
    exists_small_clique_of_ramsey G S hramsey hlargeG
  have hlargeCompl : ∀ T : Finset ℕ, T ⊆ S → Gᶜ.IsNIndepSet big T → False := by
    intro T hTS hT
    have hTG : G.IsNClique big T := by simpa using hT
    apply hno T hTS (Or.inl hTG.isClique)
    exact hbig.trans
      (weighted_sum_lower_bound_of_subset_Ico hK hm (hTS.trans hS) hTG.card_eq)
  obtain ⟨B, hBS, hBcompl⟩ :=
    exists_small_clique_of_ramsey Gᶜ S hramsey hlargeCompl
  have hB : G.IsNIndepSet m B := by simpa using hBcompl
  refine ⟨R, B, hRS, hBS, hR, hB, ?_, ?_⟩
  · exact (uniform_block_lower_bound hm).trans
      (weighted_sum_lower_bound_of_subset_Ico hK hm (hRS.trans hS) hR.card_eq)
  · exact (uniform_block_lower_bound hm).trans
      (weighted_sum_lower_bound_of_subset_Ico hK hm (hBS.trans hS) hB.card_eq)

/-! ## The predetermined widely separated blocks -/

structure BlockSpec where
  scale : ℕ
  sample : ℕ
  target : ℕ
  block : Finset ℕ

def blockSpecs (d L factor : ℕ) : ℕ → List BlockSpec
  | 0 => []
  | r + 1 =>
      let m := factor + d + 1
      let q := 2 ^ (L * m)
      let u := 2 ^ d * q
      { scale := m
        sample := u
        target := q
        block := Finset.Ico (2 ^ ((2 * L) * m)) (2 ^ ((2 * L) * m + 1)) } ::
        blockSpecs d L (factor * 2 ^ u) r

@[simp] lemma blockSpecs_length (d L factor r : ℕ) :
    (blockSpecs d L factor r).length = r := by
  induction r generalizing factor with
  | zero => simp [blockSpecs]
  | succ r ih => simp [blockSpecs, ih]

lemma blockSpecs_sample_target (d L factor r : ℕ) :
    List.Forall₂ (fun u q ↦ 2 ^ d * q ≤ u)
      ((blockSpecs d L factor r).map BlockSpec.sample)
      ((blockSpecs d L factor r).map BlockSpec.target) := by
  induction r generalizing factor with
  | zero => simp [blockSpecs]
  | succ r ih =>
      simp only [blockSpecs, List.map_cons]
      exact .cons le_rfl (ih (factor * 2 ^ (2 ^ d * 2 ^ (L * (factor + d + 1)))))

lemma blockSpecs_sized (d L factor r : ℕ) (hL : 1 ≤ L) (hfactor : 0 < factor) :
    SizedBlocks factor
      ((blockSpecs d L factor r).map BlockSpec.sample)
      ((blockSpecs d L factor r).map BlockSpec.block) := by
  induction r generalizing factor with
  | zero => simp [blockSpecs, SizedBlocks]
  | succ r ih =>
      let m := factor + d + 1
      let q := 2 ^ (L * m)
      let u := 2 ^ d * q
      have hfdm : factor + d ≤ L * m := by
        have hm : factor + d < m := by simp [m]
        exact hm.le.trans (Nat.le_mul_of_pos_left m hL)
      have hhead : factor * u ≤
          (Finset.Ico (2 ^ ((2 * L) * m)) (2 ^ ((2 * L) * m + 1))).card := by
        rw [Nat.card_Ico]
        have hpow : factor * u ≤ 2 ^ ((2 * L) * m) := by
          calc
            factor * u ≤ 2 ^ factor * u :=
              Nat.mul_le_mul_right u (show factor ≤ 2 ^ factor from Nat.lt_two_pow_self.le)
            _ = 2 ^ (factor + d + L * m) := by
              simp [u, q, pow_add]
              ring
            _ ≤ 2 ^ (L * m + L * m) := by
              exact Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hfdm (L * m))
            _ = 2 ^ ((2 * L) * m) := by congr 1 <;> ring
        have hpow_succ : 2 ^ ((2 * L) * m + 1) = 2 ^ ((2 * L) * m) * 2 := by
          rw [pow_succ]
        omega
      simp only [blockSpecs, List.map_cons, SizedBlocks]
      refine ⟨?_, ?_⟩
      · simpa [m, q, u] using hhead
      · simpa [m, q, u] using ih (factor * 2 ^ u) (by positivity)

lemma next_block_factor_gt_scale (d L factor : ℕ) (hL : 1 ≤ L) (hfactor : 0 < factor) :
    factor + d + 1 <
      factor * 2 ^ (2 ^ d * 2 ^ (L * (factor + d + 1))) := by
  let m := factor + d + 1
  let q := 2 ^ (L * m)
  let u := 2 ^ d * q
  have hm : 1 ≤ m := by simp [m]
  have hLm : 1 ≤ L * m := Nat.mul_pos (by omega) (by omega)
  have hq : 2 ≤ q := by
    simpa [q] using Nat.pow_le_pow_right (n := 2) (by decide) hLm
  have hd : d + 1 ≤ 2 ^ d := by
    have := Nat.lt_two_pow_self (n := d)
    omega
  have hu : d + 2 ≤ u := by
    calc
      d + 2 ≤ 2 * (d + 1) := by omega
      _ ≤ 2 ^ d * q := by
        simpa [mul_comm] using Nat.mul_le_mul hd hq
      _ = u := rfl
  have hdu : d + 3 ≤ 2 ^ u := by
    have := Nat.lt_two_pow_self (n := u)
    omega
  have hmul : factor * (d + 3) ≤ factor * 2 ^ u :=
    Nat.mul_le_mul_left factor hdu
  have hmiddle : factor + d + 2 ≤ factor * (d + 3) := by nlinarith
  have : m < factor * 2 ^ u := by simp only [m]; omega
  simpa [m, q, u] using this

lemma blockSpecs_scale_lower (d L factor r : ℕ) (hL : 1 ≤ L) (hfactor : 0 < factor)
    {s : BlockSpec} (hs : s ∈ blockSpecs d L factor r) :
    factor + d + 1 ≤ s.scale := by
  induction r generalizing factor with
  | zero => simp [blockSpecs] at hs
  | succ r ih =>
      let m := factor + d + 1
      let q := 2 ^ (L * m)
      let u := 2 ^ d * q
      simp only [blockSpecs, List.mem_cons] at hs
      rcases hs with rfl | hs
      · rfl
      · have htail := ih (factor * 2 ^ u) (by positivity) hs
        have hnext : m < factor * 2 ^ u := by
          simpa [m, q, u] using next_block_factor_gt_scale d L factor hL hfactor
        exact le_trans (by omega) htail

lemma blockSpecs_block_eq (d L factor r : ℕ) {s : BlockSpec}
    (hs : s ∈ blockSpecs d L factor r) :
    s.block = Finset.Ico (2 ^ ((2 * L) * s.scale)) (2 ^ ((2 * L) * s.scale + 1)) := by
  induction r generalizing factor with
  | zero => simp [blockSpecs] at hs
  | succ r ih =>
      simp only [blockSpecs, List.mem_cons] at hs
      rcases hs with rfl | hs
      · rfl
      · exact ih (factor := factor * 2 ^ (2 ^ d * 2 ^ (L * (factor + d + 1)))) hs

lemma blockSpecs_target_eq (d L factor r : ℕ) {s : BlockSpec}
    (hs : s ∈ blockSpecs d L factor r) :
    s.target = 2 ^ (L * s.scale) := by
  induction r generalizing factor with
  | zero => simp [blockSpecs] at hs
  | succ r ih =>
      simp only [blockSpecs, List.mem_cons] at hs
      rcases hs with rfl | hs
      · rfl
      · exact ih (factor := factor * 2 ^ (2 ^ d * 2 ^ (L * (factor + d + 1)))) hs

lemma blockSpecs_sample_eq (d L factor r : ℕ) {s : BlockSpec}
    (hs : s ∈ blockSpecs d L factor r) :
    s.sample = 2 ^ d * s.target := by
  induction r generalizing factor with
  | zero => simp [blockSpecs] at hs
  | succ r ih =>
      simp only [blockSpecs, List.mem_cons] at hs
      rcases hs with rfl | hs
      · rfl
      · exact ih (factor := factor * 2 ^ (2 ^ d * 2 ^ (L * (factor + d + 1)))) hs

lemma blockSpecs_pairwise_blocks (d L factor r : ℕ) (hL : 1 ≤ L)
    (hfactor : 0 < factor) :
    (blockSpecs d L factor r).Pairwise fun s t ↦ Disjoint s.block t.block := by
  induction r generalizing factor with
  | zero => simp [blockSpecs]
  | succ r ih =>
      let m := factor + d + 1
      let q := 2 ^ (L * m)
      let u := 2 ^ d * q
      let nextFactor := factor * 2 ^ u
      have hnext : m < nextFactor := by
        simpa [m, q, u, nextFactor] using next_block_factor_gt_scale d L factor hL hfactor
      simp only [blockSpecs, List.pairwise_cons]
      constructor
      · intro s hs
        have hsScale : nextFactor + d + 1 ≤ s.scale :=
          blockSpecs_scale_lower d L nextFactor r hL (by positivity) hs
        rw [Finset.disjoint_left]
        intro x hx hxs
        have hxUpper := (Finset.mem_Ico.mp hx).2
        have hxs' : x ∈ Finset.Ico (2 ^ ((2 * L) * s.scale))
            (2 ^ ((2 * L) * s.scale + 1)) := by
          rwa [← blockSpecs_block_eq d L nextFactor r hs]
        have hxsLower := (Finset.mem_Ico.mp hxs').1
        have hexp : (2 * L) * m + 1 ≤ (2 * L) * s.scale := by
          have hmScale : m < s.scale := lt_of_lt_of_le hnext (by omega : nextFactor ≤ s.scale)
          nlinarith
        have hp : 2 ^ ((2 * L) * m + 1) ≤ 2 ^ ((2 * L) * s.scale) :=
          Nat.pow_le_pow_right (by decide) hexp
        exact (not_lt_of_ge (hp.trans hxsLower)) hxUpper
      · simpa [m, q, u, nextFactor] using
          ih nextFactor (by positivity)

lemma blockSpecs_get_disjoint_of_lt (d L factor r : ℕ) (hL : 1 ≤ L)
    (hfactor : 0 < factor) {i j : Fin (blockSpecs d L factor r).length}
    (hij : i < j) :
    Disjoint ((blockSpecs d L factor r).get i).block
      ((blockSpecs d L factor r).get j).block := by
  exact (blockSpecs_pairwise_blocks d L factor r hL hfactor).rel_get_of_lt hij

lemma blockSpecs_get_disjoint (d L factor r : ℕ) (hL : 1 ≤ L)
    (hfactor : 0 < factor) {i j : Fin (blockSpecs d L factor r).length}
    (hij : i ≠ j) :
    Disjoint ((blockSpecs d L factor r).get i).block
      ((blockSpecs d L factor r).get j).block := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact blockSpecs_get_disjoint_of_lt d L factor r hL hfactor hij
  · exact (blockSpecs_get_disjoint_of_lt d L factor r hL hfactor hji).symm

/-- The finite set of all vertices in the predetermined block family. -/
def blockSpecsUnion (d L factor r : ℕ) : Finset ℕ :=
  ((blockSpecs d L factor r).map BlockSpec.block).foldr (· ∪ ·) ∅

lemma mem_foldr_union_iff {x : ℕ} (ss : List (Finset ℕ)) :
    x ∈ ss.foldr (· ∪ ·) ∅ ↔ ∃ s ∈ ss, x ∈ s := by
  induction ss with
  | nil => simp
  | cons s ss ih => simp [ih]

lemma block_subset_blockSpecsUnion (d L factor r : ℕ) {s : BlockSpec}
    (hs : s ∈ blockSpecs d L factor r) :
    s.block ⊆ blockSpecsUnion d L factor r := by
  intro x hx
  rw [blockSpecsUnion, mem_foldr_union_iff]
  exact ⟨s.block, List.mem_map.mpr ⟨s, hs, rfl⟩, hx⟩

lemma two_le_of_mem_blockSpecsUnion (d L factor r : ℕ) (hL : 1 ≤ L)
    (hfactor : 0 < factor) {x : ℕ} (hx : x ∈ blockSpecsUnion d L factor r) :
    2 ≤ x := by
  rw [blockSpecsUnion, mem_foldr_union_iff] at hx
  obtain ⟨b, hb, hxb⟩ := hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hb
  have hscale : 0 < s.scale := by
    have := blockSpecs_scale_lower d L factor r hL hfactor hs
    omega
  have hxb' : x ∈ Finset.Ico (2 ^ ((2 * L) * s.scale))
      (2 ^ ((2 * L) * s.scale + 1)) := by
    rwa [← blockSpecs_block_eq d L factor r hs]
  have hstart : 2 ≤ 2 ^ ((2 * L) * s.scale) := by
    apply Nat.one_lt_two_pow
    nlinarith
  exact hstart.trans (Finset.mem_Ico.mp hxb').1

theorem blockSpecsUnion_bounded (d L factor r : ℕ) (hL : 1 ≤ L)
    (hfactor : 0 < factor) :
    ∃ N : ℕ, blockSpecsUnion d L factor r ⊆ Finset.Icc 2 N := by
  let U := blockSpecsUnion d L factor r
  refine ⟨∑ x ∈ U, x, ?_⟩
  intro x hx
  simp only [Finset.mem_Icc]
  constructor
  · exact two_le_of_mem_blockSpecsUnion d L factor r hL hfactor hx
  · exact Finset.single_le_sum (fun y _ ↦ Nat.zero_le y) hx

def metaGraphOfParts {α ι : Type*} (G : SimpleGraph α)
    (parts : ι → Finset α) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ ∀ x ∈ parts i, ∀ y ∈ parts j, G.Adj x y
  symm := ⟨by
    rintro i j ⟨hij, h⟩
    refine ⟨Ne.symm hij, ?_⟩
    intro y hy x hx
    exact (h x hx y hy).symm⟩
  loopless := ⟨fun i h ↦ h.1 rfl⟩

lemma metaGraphOfParts_adj {α ι : Type*} (G : SimpleGraph α)
    (parts : ι → Finset α) {i j : ι} :
    (metaGraphOfParts G parts).Adj i j ↔
      i ≠ j ∧ ∀ x ∈ parts i, ∀ y ∈ parts j, G.Adj x y := by
  rfl

lemma pairwiseCross_get_dichotomy {α : Type*} (G : SimpleGraph α)
    [DecidableRel G.Adj] {sets : List (Finset α)}
    (hcross : PairwiseCrossHomogeneous (fun x y ↦ decide (G.Adj x y)) sets)
    {i j : Fin sets.length} (hij : i ≠ j) :
    (∀ x ∈ sets.get i, ∀ y ∈ sets.get j, G.Adj x y) ∨
      (∀ x ∈ sets.get i, ∀ y ∈ sets.get j, ¬G.Adj x y) := by
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · exact crossHomogeneous_adj_dichotomy G
      (hcross.get i.isLt j.isLt hij')
  · rcases crossHomogeneous_adj_dichotomy G
        (hcross.get j.isLt i.isLt hji') with h | h
    · left
      intro x hx y hy
      exact (h y hy x hx).symm
    · right
      intro x hx y hy hxy
      exact h y hy x hx hxy.symm

lemma metaGraphOfParts_not_adj_cross {α : Type*} (G : SimpleGraph α)
    [DecidableRel G.Adj] {sets : List (Finset α)}
    (hcross : PairwiseCrossHomogeneous (fun x y ↦ decide (G.Adj x y)) sets)
    {i j : Fin sets.length} (hij : i ≠ j)
    (hnot : ¬(metaGraphOfParts G (fun k : Fin sets.length ↦ sets.get k)).Adj i j) :
    ∀ x ∈ sets.get i, ∀ y ∈ sets.get j, ¬G.Adj x y := by
  rcases pairwiseCross_get_dichotomy G hcross hij with h | h
  · exact (hnot ⟨hij, h⟩).elim
  · exact h

/-! ## Reindexing the canonical list output -/

/-- Index a list known to have length `d` by `Fin d`. -/
def finGet {α : Type*} {d : ℕ} (xs : List α) (hlen : xs.length = d) (i : Fin d) : α :=
  xs.get (Fin.cast hlen.symm i)

lemma finGet_disjoint_of_pairwise {d : ℕ} {sets : List (Finset ℕ)}
    (hsets : sets.length = d) (hpair : sets.Pairwise Disjoint)
    {i j : Fin d} (hij : i ≠ j) :
    Disjoint (finGet sets hsets i) (finGet sets hsets j) := by
  change Disjoint (sets.get (Fin.cast hsets.symm i)) (sets.get (Fin.cast hsets.symm j))
  have hcast : Fin.cast hsets.symm i ≠ Fin.cast hsets.symm j := by
    intro h
    exact hij (Fin.cast_injective hsets.symm h)
  rcases lt_or_gt_of_ne hcast with hlt | hgt
  · exact hpair.rel_get_of_lt hlt
  · exact (hpair.rel_get_of_lt hgt).symm

lemma blockSpecs_finGet_disjoint (d L factor r : ℕ) (hL : 1 ≤ L)
    (hfactor : 0 < factor) {i j : Fin r} (hij : i ≠ j) :
    Disjoint
      (finGet ((blockSpecs d L factor r).map BlockSpec.block) (by simp) i)
      (finGet ((blockSpecs d L factor r).map BlockSpec.block) (by simp) j) := by
  apply finGet_disjoint_of_pairwise (by simp) ?_ hij
  rw [List.pairwise_map]
  exact blockSpecs_pairwise_blocks d L factor r hL hfactor

/-- `List.Forall₂` becomes a pointwise relation after reindexing both lists by
the same finite type. -/
lemma finGet_rel_of_forall₂ {α β : Type*} {R : α → β → Prop} {d : ℕ}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys)
    (hxs : xs.length = d) (hys : ys.length = d) (i : Fin d) :
    R (finGet xs hxs i) (finGet ys hys i) := by
  change R (xs.get ⟨i.val, _⟩) (ys.get ⟨i.val, _⟩)
  exact h.get
    (show i.val < xs.length by simpa only [hxs] using i.isLt)
    (show i.val < ys.length by simpa only [hys] using i.isLt)

lemma finGet_subset_of_forall₂ {α : Type*} {d : ℕ}
    {sets blocks : List (Finset α)}
    (h : List.Forall₂ (fun t s ↦ t ⊆ s) sets blocks)
    (hsets : sets.length = d) (hblocks : blocks.length = d) (i : Fin d) :
    finGet sets hsets i ⊆ finGet blocks hblocks i :=
  finGet_rel_of_forall₂ h hsets hblocks i

lemma finGet_card_ge_of_forall₂ {α : Type*} {d : ℕ}
    {sets : List (Finset α)} {targets : List ℕ}
    (h : List.Forall₂ (fun t q ↦ q ≤ t.card) sets targets)
    (hsets : sets.length = d) (htargets : targets.length = d) (i : Fin d) :
    finGet targets htargets i ≤ (finGet sets hsets i).card :=
  finGet_rel_of_forall₂ h hsets htargets i

/-- Package the list output of the canonical lemma as one `Fin d`-indexed
family while retaining the two aligned `Forall₂` conclusions. -/
theorem exists_fin_family_of_canonical {α : Type*} {d : ℕ}
    (sets blocks : List (Finset α)) (targets : List ℕ)
    (hblocks : blocks.length = d) (htargets : targets.length = d)
    (hsub : List.Forall₂ (fun t s ↦ t ⊆ s) sets blocks)
    (hcard : List.Forall₂ (fun t q ↦ q ≤ t.card) sets targets) :
    ∃ T : Fin d → Finset α,
      (∀ i, T i ⊆ finGet blocks hblocks i) ∧
      (∀ i, finGet targets htargets i ≤ (T i).card) := by
  have hsets : sets.length = d := hsub.length_eq.trans hblocks
  refine ⟨fun i ↦ finGet sets hsets i, ?_, ?_⟩
  · exact fun i ↦ finGet_subset_of_forall₂ hsub hsets hblocks i
  · exact fun i ↦ finGet_card_ge_of_forall₂ hcard hsets htargets i

lemma pairwiseCrossHomogeneous_finGet_of_lt {α : Type*}
    {color : α → α → Bool} {d : ℕ} {sets : List (Finset α)}
    (hpair : PairwiseCrossHomogeneous color sets) (hsets : sets.length = d)
    {i j : Fin d} (hij : i < j) :
    CrossHomogeneous color (finGet sets hsets i) (finGet sets hsets j) := by
  change CrossHomogeneous color (sets.get ⟨i.val, _⟩) (sets.get ⟨j.val, _⟩)
  exact hpair.get
    (show i.val < sets.length by simpa only [hsets] using i.isLt)
    (show j.val < sets.length by simpa only [hsets] using j.isLt) hij

/-- The common color chosen for an increasing pair of blocks.  The value on
non-increasing pairs is irrelevant and is fixed to `false`. -/
def orderedCrossColor {α : Type*} {color : α → α → Bool} {d : ℕ}
    (sets : List (Finset α)) (hsets : sets.length = d)
    (hpair : PairwiseCrossHomogeneous color sets) (i j : Fin d) : Bool :=
  if hij : i < j then
    Classical.choose (pairwiseCrossHomogeneous_finGet_of_lt hpair hsets hij)
  else false

lemma orderedCrossColor_spec {α : Type*} {color : α → α → Bool} {d : ℕ}
    {sets : List (Finset α)} {hsets : sets.length = d}
    {hpair : PairwiseCrossHomogeneous color sets} {i j : Fin d} (hij : i < j) :
    ∀ x ∈ finGet sets hsets i, ∀ y ∈ finGet sets hsets j,
      color x y = orderedCrossColor sets hsets hpair i j := by
  intro x hx y hy
  simp only [orderedCrossColor, dif_pos hij]
  exact Classical.choose_spec
    (pairwiseCrossHomogeneous_finGet_of_lt hpair hsets hij) x hx y hy

/-- The meta graph records whether the common color on an increasing pair of
canonical blocks is `true`.  `fromRel` supplies symmetry and looplessness. -/
def crossMetaGraph {α : Type*} {color : α → α → Bool} {d : ℕ}
    (sets : List (Finset α)) (hsets : sets.length = d)
    (hpair : PairwiseCrossHomogeneous color sets) : SimpleGraph (Fin d) :=
  SimpleGraph.fromRel fun i j ↦ orderedCrossColor sets hsets hpair i j = true

/-- For a symmetric coloring, the meta edge on two distinct block indices is
equivalent to the color of every cross pair being `true`. -/
lemma crossMetaGraph_adj_iff_color_true {α : Type*} {color : α → α → Bool}
    {d : ℕ} {sets : List (Finset α)} {hsets : sets.length = d}
    {hpair : PairwiseCrossHomogeneous color sets}
    (hsymm : ∀ x y, color x y = color y x)
    {i j : Fin d} (hij : i ≠ j)
    {x y : α} (hx : x ∈ finGet sets hsets i) (hy : y ∈ finGet sets hsets j) :
    (crossMetaGraph sets hsets hpair).Adj i j ↔ color x y = true := by
  rw [crossMetaGraph, SimpleGraph.fromRel_adj]
  by_cases hlt : i < j
  · have hnot : ¬j < i := not_lt_of_ge hlt.le
    have hspec := orderedCrossColor_spec (hsets := hsets) (hpair := hpair)
      hlt x hx y hy
    constructor
    · rintro ⟨_, hmeta | hmeta⟩
      · rwa [← hspec] at hmeta
      · simp [orderedCrossColor, hnot] at hmeta
    · intro hcolor
      refine ⟨hij, Or.inl ?_⟩
      rwa [← hspec]
  · have hji : j < i := lt_of_le_of_ne (not_lt.mp hlt) hij.symm
    have hspec := orderedCrossColor_spec (hsets := hsets) (hpair := hpair)
      hji y hy x hx
    have hspec' : color x y = orderedCrossColor sets hsets hpair j i := by
      rw [hsymm x y]
      exact hspec
    constructor
    · rintro ⟨_, hmeta | hmeta⟩
      · simp [orderedCrossColor, hlt] at hmeta
      · rwa [← hspec'] at hmeta
    · intro hcolor
      refine ⟨hij, Or.inr ?_⟩
      rwa [← hspec']

/-- Specialization to the Boolean adjacency coloring of a graph on naturals. -/
def graphCrossMeta (G : SimpleGraph ℕ) [DecidableRel G.Adj] {d : ℕ}
    (sets : List (Finset ℕ)) (hsets : sets.length = d)
    (hpair : PairwiseCrossHomogeneous (fun x y ↦ decide (G.Adj x y)) sets) :
    SimpleGraph (Fin d) :=
  crossMetaGraph sets hsets hpair

lemma graphCrossMeta_adj_iff {G : SimpleGraph ℕ} [DecidableRel G.Adj] {d : ℕ}
    {sets : List (Finset ℕ)} {hsets : sets.length = d}
    {hpair : PairwiseCrossHomogeneous (fun x y ↦ decide (G.Adj x y)) sets}
    {i j : Fin d} (hij : i ≠ j)
    {x y : ℕ} (hx : x ∈ finGet sets hsets i) (hy : y ∈ finGet sets hsets j) :
    (graphCrossMeta G sets hsets hpair).Adj i j ↔ G.Adj x y := by
  have hsymm : ∀ x y : ℕ, decide (G.Adj x y) = decide (G.Adj y x) := by
    intro x y
    simp only [G.adj_comm]
  simpa only [graphCrossMeta, decide_eq_true_eq] using
    (crossMetaGraph_adj_iff_color_true (hsets := hsets) (hpair := hpair)
      hsymm hij hx hy)

/-- One-shot bridge in the shape used by the final proof: aligned list data and
pairwise cross-homogeneity produce an indexed family and its meta graph. -/
theorem exists_fin_family_and_meta_of_canonical
    (G : SimpleGraph ℕ) [DecidableRel G.Adj] {d : ℕ}
    (sets blocks : List (Finset ℕ)) (targets : List ℕ)
    (hblocks : blocks.length = d) (htargets : targets.length = d)
    (hsub : List.Forall₂ (fun t s ↦ t ⊆ s) sets blocks)
    (hcard : List.Forall₂ (fun t q ↦ q ≤ t.card) sets targets)
    (hpair : PairwiseCrossHomogeneous (fun x y ↦ decide (G.Adj x y)) sets) :
    ∃ (T : Fin d → Finset ℕ) (M : SimpleGraph (Fin d)),
      (∀ i, T i ⊆ finGet blocks hblocks i) ∧
      (∀ i, finGet targets htargets i ≤ (T i).card) ∧
      (∀ ⦃i j : Fin d⦄, i ≠ j → ∀ ⦃x y : ℕ⦄,
        x ∈ T i → y ∈ T j → (M.Adj i j ↔ G.Adj x y)) := by
  have hsets : sets.length = d := hsub.length_eq.trans hblocks
  refine ⟨fun i ↦ finGet sets hsets i, graphCrossMeta G sets hsets hpair,
    ?_, ?_, ?_⟩
  · exact fun i ↦ finGet_subset_of_forall₂ hsub hsets hblocks i
  · exact fun i ↦ finGet_card_ge_of_forall₂ hcard hsets htargets i
  · intro i j hij x y hx hy
    exact graphCrossMeta_adj_iff hij hx hy

/-! ## The final Ramsey argument on the block indices -/

lemma isClique_biUnion_of_cross {α ι : Type*} (G : SimpleGraph α) [DecidableEq α]
    (s : Finset ι) (parts : ι → Finset α)
    (hlocal : ∀ i ∈ s, G.IsClique (parts i))
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∀ x ∈ parts i, ∀ y ∈ parts j, G.Adj x y) :
    G.IsClique (s.biUnion parts) := by
  intro x hx y hy hxy
  rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
  rcases Finset.mem_biUnion.mp hy with ⟨j, hj, hyj⟩
  by_cases hij : i = j
  · subst j
    exact hlocal i hi hxi hyj hxy
  · exact hcross i hi j hj hij x hxi y hyj

lemma isIndepSet_biUnion_of_cross {α ι : Type*}
    (G : SimpleGraph α) [DecidableEq α]
    (s : Finset ι) (parts : ι → Finset α)
    (hlocal : ∀ i ∈ s, G.IsIndepSet (parts i))
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∀ x ∈ parts i, ∀ y ∈ parts j, ¬G.Adj x y) :
    G.IsIndepSet (s.biUnion parts) := by
  intro x hx y hy hxy
  rcases Finset.mem_biUnion.mp hx with ⟨i, hi, hxi⟩
  rcases Finset.mem_biUnion.mp hy with ⟨j, hj, hyj⟩
  by_cases hij : i = j
  · subst j
    exact hlocal i hi hxi hyj hxy
  · exact hcross i hi j hj hij x hxi y hyj

lemma card_mul_le_sum_biUnion {α ι : Type*} [DecidableEq α]
    (s : Finset ι) (parts : ι → Finset α) (w : α → ℝ) (ε : ℝ)
    (hdisj : (s : Set ι).PairwiseDisjoint parts)
    (hpart : ∀ i ∈ s, ε ≤ ∑ x ∈ parts i, w x) :
    (s.card : ℝ) * ε ≤ ∑ x ∈ s.biUnion parts, w x := by
  rw [Finset.sum_biUnion hdisj]
  calc
    (s.card : ℝ) * ε = ∑ _i ∈ s, ε := by simp
    _ ≤ ∑ i ∈ s, ∑ x ∈ parts i, w x :=
      Finset.sum_le_sum fun i hi ↦ hpart i hi

lemma ramseyNumber_spec_exact (k l : ℕ)
    (G : SimpleGraph (Fin (Ramsey.ramseyNumber k l))) :
    (∃ s : Finset (Fin (Ramsey.ramseyNumber k l)),
      G.IsClique s ∧ s.card = k) ∨
    (∃ s : Finset (Fin (Ramsey.ramseyNumber k l)),
      G.IsIndepSet s ∧ s.card = l) := by
  classical
  by_contra! h
  exact (Ramsey.ramseyNumber_spec k l) G ⟨
    (fun s hs ↦ h.1 s hs.isClique hs.card_eq),
    (fun s hs ↦ h.2 s hs.isIndepSet hs.card_eq)⟩

lemma meta_ramsey_union {α : Type*} (q : ℕ) (G : SimpleGraph α) [DecidableEq α]
    (M : SimpleGraph (Fin (Ramsey.ramseyNumber q q)))
    (red blue : Fin (Ramsey.ramseyNumber q q) → Finset α)
    (U : Finset α) (w : α → ℝ) (ε : ℝ)
    (hredLocal : ∀ i, G.IsClique (red i))
    (hblueLocal : ∀ i, G.IsIndepSet (blue i))
    (hredCross : ∀ ⦃i j⦄, M.Adj i j →
      ∀ x ∈ red i, ∀ y ∈ red j, G.Adj x y)
    (hblueCross : ∀ ⦃i j⦄, i ≠ j → ¬M.Adj i j →
      ∀ x ∈ blue i, ∀ y ∈ blue j, ¬G.Adj x y)
    (hredDisj : (Set.univ : Set (Fin (Ramsey.ramseyNumber q q))).PairwiseDisjoint red)
    (hblueDisj : (Set.univ : Set (Fin (Ramsey.ramseyNumber q q))).PairwiseDisjoint blue)
    (hredSub : ∀ i, red i ⊆ U)
    (hblueSub : ∀ i, blue i ⊆ U)
    (hredWeight : ∀ i, ε ≤ ∑ x ∈ red i, w x)
    (hblueWeight : ∀ i, ε ≤ ∑ x ∈ blue i, w x) :
    (∃ X : Finset α, X ⊆ U ∧ G.IsClique X ∧
      (q : ℝ) * ε ≤ ∑ x ∈ X, w x) ∨
    (∃ X : Finset α, X ⊆ U ∧ G.IsIndepSet X ∧
      (q : ℝ) * ε ≤ ∑ x ∈ X, w x) := by
  classical
  rcases ramseyNumber_spec_exact q q M with hmeta | hmeta
  · rcases hmeta with ⟨s, hsClique, hsCard⟩
    left
    refine ⟨s.biUnion red, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.mp hx
      exact hredSub i hxi
    · apply isClique_biUnion_of_cross G s red
      · exact fun i _ ↦ hredLocal i
      · intro i hi j hj hij x hxi y hyj
        exact hredCross (hsClique hi hj hij) x hxi y hyj
    · calc
        (q : ℝ) * ε = (s.card : ℝ) * ε := by rw [hsCard]
        _ ≤ ∑ x ∈ s.biUnion red, w x := by
          apply card_mul_le_sum_biUnion s red w ε
          · intro i hi j hj hij
            exact hredDisj (by simp) (by simp) hij
          · exact fun i _ ↦ hredWeight i
  · rcases hmeta with ⟨s, hsIndep, hsCard⟩
    right
    refine ⟨s.biUnion blue, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.mp hx
      exact hblueSub i hxi
    · apply isIndepSet_biUnion_of_cross G s blue
      · exact fun i _ ↦ hblueLocal i
      · intro i hi j hj hij x hxi y hyj
        exact hblueCross hij (hsIndep hi hj hij) x hxi y hyj
    · calc
        (q : ℝ) * ε = (s.card : ℝ) * ε := by rw [hsCard]
        _ ≤ ∑ x ∈ s.biUnion blue, w x := by
          apply card_mul_le_sum_biUnion s blue w ε
          · intro i hi j hj hij
            exact hblueDisj (by simp) (by simp) hij
          · exact fun i _ ↦ hblueWeight i

/-! ## Resolution of Problem 191 -/

/-- **Erdős Problem 191 (affirmative resolution).**  For every positive real
`C`, all sufficiently large red-blue colorings of the pairs of
`{2, ..., n}` contain a monochromatic set of reciprocal-logarithmic weight at
least `C`. -/
theorem erdos_191 :
    ∀ C : ℝ, 0 < C → ∃ N : ℕ, ∀ n ≥ N, HasLargeMonochromaticSet C n := by
  classical
  intro C hC
  obtain ⟨c : ℕ, hc⟩ := exists_nat_ge C
  have hcpos : 0 < c := by
    have : (0 : ℝ) < c := hC.trans_le hc
    exact_mod_cast this
  let Q := 4 * (c + 4)
  let L := Q + 4
  let K := 2 * L
  let b := 2 ^ Q
  let δ : ℝ := ((((K + 1 : ℕ) : ℝ) * Real.log 2))⁻¹
  have hL : 1 ≤ L := by simp [L, Q]
  have hK : 1 ≤ K := by dsimp [K, L, Q]; omega
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨q : ℕ, hq⟩ := exists_nat_ge (C / δ)
  have hCq : C ≤ (q : ℝ) * δ := (div_le_iff₀ hδ).mp hq
  let d := Ramsey.ramseyNumber q q
  let specs := blockSpecs d L 1 d
  let samples := specs.map BlockSpec.sample
  let targets := specs.map BlockSpec.target
  let blocks := specs.map BlockSpec.block
  let U := blockSpecsUnion d L 1 d
  obtain ⟨N, hUN⟩ := blockSpecsUnion_bounded d L 1 d hL (by omega)
  refine ⟨N, ?_⟩
  intro n hn
  apply hasLargeMonochromaticSet_of_on (U := U)
  · intro x hx
    have hx' := hUN hx
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx').1,
      (Finset.mem_Icc.mp hx').2.trans hn⟩
  · intro G
    by_contra hnone
    have hno : ∀ S : Finset ℕ, S ⊆ U → Monochromatic G S →
        ¬ C ≤ ∑ x ∈ S, weight x := by
      intro S hSU hmono hsum
      exact hnone ⟨S, hSU, hmono, hsum⟩
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    have hspecs : specs.length = d := by simp [specs]
    have hsamples : samples.length = d := by simp [samples, hspecs]
    have htargets : targets.length = d := by simp [targets, hspecs]
    have hblocks : blocks.length = d := by simp [blocks, hspecs]
    obtain ⟨sets, hsetsSub, hsetsCard, hsetsCross⟩ :=
      exists_canonical_subsets (fun x y ↦ decide (G.Adj x y)) d samples targets blocks
        (by simp [samples, specs])
        (by simpa [samples, blocks, specs] using blockSpecs_sized d L 1 d hL (by omega))
        (by simpa [samples, targets, specs] using blockSpecs_sample_target d L 1 d)
    obtain ⟨T, M, hTSub, hTCard, hMeta⟩ :=
      exists_fin_family_and_meta_of_canonical G sets blocks targets hblocks htargets
        hsetsSub hsetsCard hsetsCross
    let spec : Fin d → BlockSpec := fun i ↦ finGet specs hspecs i
    have hspecMem (i : Fin d) : spec i ∈ specs := by
      exact List.get_mem specs (Fin.cast hspecs.symm i)
    have hTBlock (i : Fin d) : T i ⊆ (spec i).block := by
      simpa [blocks, spec, finGet] using hTSub i
    have htargetCard (i : Fin d) : (spec i).target ≤ (T i).card := by
      simpa [targets, spec, finGet] using hTCard i
    have hlocal : ∀ i : Fin d, ∃ R B : Finset ℕ,
        R ⊆ T i ∧ B ⊆ T i ∧
        G.IsNClique (spec i).scale R ∧ G.IsNIndepSet (spec i).scale B ∧
        δ ≤ ∑ x ∈ R, weight x ∧ δ ≤ ∑ x ∈ B, weight x := by
      intro i
      have hm : 1 ≤ (spec i).scale := by
        have := blockSpecs_scale_lower d L 1 d hL (by omega) (hspecMem i)
        omega
      apply exists_both_colors_in_block_uniform (K := K) (m := (spec i).scale)
        (big := b * (spec i).scale) G (T i) hK hm
      · intro x hx
        have hx' := hTBlock i hx
        rw [blockSpecs_block_eq d L 1 d (hspecMem i)] at hx'
        simpa [K] using hx'
      · calc
          Ramsey.ramseyNumber (spec i).scale (b * (spec i).scale) ≤
              2 ^ ((Q + 4) * (spec i).scale) := by
                simpa [b] using ramseyNumber_mul_le_pow Q (spec i).scale hm
          _ = (spec i).target := by
            simpa [L] using (blockSpecs_target_eq d L 1 d (hspecMem i)).symm
          _ ≤ (T i).card := htargetCard i
      · change C ≤ ((2 ^ (4 * (c + 4)) * (spec i).scale : ℕ) : ℝ) *
          ((((2 * (4 * (c + 4) + 4)) * (spec i).scale + 1 : ℕ) : ℝ) *
            Real.log 2)⁻¹
        exact hc.trans (constant_le_large_block_weight c (spec i).scale hm)
      · intro S hST hmono
        apply hno S (hST.trans ((hTBlock i).trans
          (block_subset_blockSpecsUnion d L 1 d (hspecMem i)))) hmono
    choose red blue hlocalSpec using hlocal
    have hredSub (i : Fin d) : red i ⊆ T i := (hlocalSpec i).1
    have hblueSub (i : Fin d) : blue i ⊆ T i := (hlocalSpec i).2.1
    have hredLocal (i : Fin d) : G.IsClique (red i) :=
      (hlocalSpec i).2.2.1.isClique
    have hblueLocal (i : Fin d) : G.IsIndepSet (blue i) :=
      (hlocalSpec i).2.2.2.1.isIndepSet
    have hredWeight (i : Fin d) : δ ≤ ∑ x ∈ red i, weight x :=
      (hlocalSpec i).2.2.2.2.1
    have hblueWeight (i : Fin d) : δ ≤ ∑ x ∈ blue i, weight x :=
      (hlocalSpec i).2.2.2.2.2
    have hTDisj : (Set.univ : Set (Fin d)).PairwiseDisjoint T := by
      intro i _ j _ hij
      exact (blockSpecs_finGet_disjoint d L 1 d hL (by omega) hij).mono
        (by simpa [blocks] using hTSub i) (by simpa [blocks] using hTSub j)
    have hredDisj : (Set.univ : Set (Fin d)).PairwiseDisjoint red := by
      intro i _ j _ hij
      exact (hTDisj (by simp) (by simp) hij).mono (hredSub i) (hredSub j)
    have hblueDisj : (Set.univ : Set (Fin d)).PairwiseDisjoint blue := by
      intro i _ j _ hij
      exact (hTDisj (by simp) (by simp) hij).mono (hblueSub i) (hblueSub j)
    have hredU (i : Fin d) : red i ⊆ U :=
      (hredSub i).trans ((hTBlock i).trans
        (block_subset_blockSpecsUnion d L 1 d (hspecMem i)))
    have hblueU (i : Fin d) : blue i ⊆ U :=
      (hblueSub i).trans ((hTBlock i).trans
        (block_subset_blockSpecsUnion d L 1 d (hspecMem i)))
    have hredCross : ∀ ⦃i j : Fin d⦄, M.Adj i j →
        ∀ x ∈ red i, ∀ y ∈ red j, G.Adj x y := by
      intro i j hij x hx y hy
      exact (hMeta hij.ne (hredSub i hx) (hredSub j hy)).mp hij
    have hblueCross : ∀ ⦃i j : Fin d⦄, i ≠ j → ¬ M.Adj i j →
        ∀ x ∈ blue i, ∀ y ∈ blue j, ¬ G.Adj x y := by
      intro i j hij hnot x hx y hy hadj
      exact hnot ((hMeta hij (hblueSub i hx) (hblueSub j hy)).mpr hadj)
    rcases meta_ramsey_union q G M red blue U weight δ hredLocal hblueLocal
        hredCross hblueCross hredDisj hblueDisj hredU hblueU hredWeight hblueWeight with
      ⟨X, hXU, hX, hXweight⟩ | ⟨X, hXU, hX, hXweight⟩
    · exact hnone ⟨X, hXU, Or.inl hX, hCq.trans hXweight⟩
    · exact hnone ⟨X, hXU, Or.inr hX, hCq.trans hXweight⟩

end Erdos191

#print axioms Erdos191.erdos_191
