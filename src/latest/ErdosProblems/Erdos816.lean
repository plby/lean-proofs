/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 816.
https://www.erdosproblems.com/forum/thread/816

Informal authors:
- Kaizhe Chen
- Jie Ma
- Zhen Liu
- Qinghou Zeng

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos816.md
-/
/-
This is a Lean formalization of the resolution of Erdős Problem 816.

Informal authors:
- Kaizhe Chen
- Jie Ma
- Zhen Liu
- Qinghou Zeng

The theorem below covers the complete valid range `n ≥ 2`.  The restriction is
necessary: `K₃` is a counterexample for `n = 1` when path means a simple path.
-/

import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.Group.Int.Sum
import Mathlib.Data.Finset.Disjoint
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

namespace Erdos816

open Finset
open scoped BigOperators

/-! ### Three-edge paths -/

/-- Four distinct vertices, in the displayed order, forming a three-edge path. -/
def JoinedByPathThree {V : Type*} (G : SimpleGraph V) (u v : V) : Prop :=
  ∃ x y, u ≠ x ∧ u ≠ y ∧ u ≠ v ∧ x ≠ y ∧ x ≠ v ∧ y ≠ v ∧
    G.Adj u x ∧ G.Adj x y ∧ G.Adj y v

lemma joinedByPathThree_of_adj {V : Type*} {G : SimpleGraph V} {u v x y : V}
    (hux : G.Adj u x) (hxy : G.Adj x y) (hyv : G.Adj y v)
    (hux' : u ≠ x) (huy : u ≠ y) (huv : u ≠ v) (hxy' : x ≠ y)
    (hxv : x ≠ v) (hyv' : y ≠ v) : JoinedByPathThree G u v := by
  exact ⟨x, y, hux', huy, huv, hxy', hxv, hyv', hux, hxy, hyv⟩

lemma JoinedByPathThree.symm {V : Type*} {G : SimpleGraph V} {u v : V}
    (h : JoinedByPathThree G u v) : JoinedByPathThree G v u := by
  rcases h with ⟨x, y, hux, huy, huv, hxy, hxv, hyv, h₁, h₂, h₃⟩
  exact ⟨y, x, hyv.symm, hxv.symm, huv.symm, hxy.symm, huy.symm, hux.symm,
    h₃.symm, h₂.symm, h₁.symm⟩

/-! ### A sharp finite sum bound -/

/-- Distinct natural labels bounded by `m` have at most the sum of the largest
`s.card` possible values.  The integer form avoids truncated subtraction. -/
lemma sum_injective_nat_le_top_values_int {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) (m : ℕ)
    (hinj : Set.InjOn f (↑s : Set α))
    (hbound : ∀ x ∈ s, f x ≤ m) :
    ((∑ x ∈ s, f x : ℕ) : ℤ) ≤
      ∑ i ∈ Finset.range s.card, ((m : ℤ) - (i : ℤ)) := by
  let t : Finset ℤ := s.image fun x ↦ (f x : ℤ)
  have ht_bound : ∀ z ∈ t, z ≤ (m : ℤ) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact_mod_cast hbound x hx
  have ht_card : t.card = s.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    apply hinj hx hy
    exact Int.ofNat_inj.mp hxy
  have ht_sum : (∑ z ∈ t, z) = ((∑ x ∈ s, f x : ℕ) : ℤ) := by
    calc
      ∑ z ∈ t, z = ∑ x ∈ s, (f x : ℤ) := by
        dsimp [t]
        rw [Finset.sum_image]
        intro x hx y hy hxy
        apply hinj hx hy
        exact Int.ofNat_inj.mp hxy
      _ = ((∑ x ∈ s, f x : ℕ) : ℤ) := by norm_cast
  have hsharp := Finset.sum_le_sum_range (s := t) (c := (m : ℤ)) ht_bound
  rw [ht_sum, ht_card] at hsharp
  exact hsharp

/-- An injective natural-valued labelling bounded by `m` has at most `m + 1`
elements. -/
lemma card_le_succ_of_injective_nat_le {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) (m : ℕ)
    (hinj : Set.InjOn f (↑s : Set α))
    (hbound : ∀ x ∈ s, f x ≤ m) : s.card ≤ m + 1 := by
  have himage : (s.image f).card = s.card := by
    apply Finset.card_image_of_injOn
    exact hinj
  have hsub : s.image f ⊆ Finset.range (m + 1) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hbound x hx))
  rw [← himage]
  simpa using Finset.card_le_card hsub

/-- Bounding every summand bounds the sum by cardinality times the bound. -/
lemma sum_le_card_mul {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) (m : ℕ)
    (hbound : ∀ x ∈ s, f x ≤ m) : ∑ x ∈ s, f x ≤ s.card * m := by
  calc
    ∑ x ∈ s, f x ≤ ∑ _x ∈ s, m := Finset.sum_le_sum fun x hx ↦ hbound x hx
    _ = s.card * m := by simp

/-! ### The equal-endpoint neighborhood partition -/

section PairPartition

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V)

/-- Neighbors common to `u` and `v`. -/
def common : Finset V := G.neighborFinset u ∩ G.neighborFinset v

/-- Neighbors of `u` which are neither `v` nor neighbors of `v`. -/
def leftOnly : Finset V := (G.neighborFinset u \ G.neighborFinset v).erase v

/-- Neighbors of `v` which are neither `u` nor neighbors of `u`. -/
def rightOnly : Finset V := (G.neighborFinset v \ G.neighborFinset u).erase u

/-- Vertices other than the endpoints adjacent to neither endpoint. -/
def neither : Finset V :=
  univ.filter fun w ↦ w ≠ u ∧ w ≠ v ∧ ¬G.Adj u w ∧ ¬G.Adj v w

@[simp] lemma mem_common {w : V} : w ∈ common G u v ↔ G.Adj u w ∧ G.Adj v w := by
  simp [common, G.mem_neighborFinset]

@[simp] lemma mem_leftOnly {w : V} :
    w ∈ leftOnly G u v ↔ G.Adj u w ∧ ¬G.Adj v w ∧ w ≠ v := by
  simp [leftOnly, G.mem_neighborFinset, and_assoc, and_left_comm, and_comm]

@[simp] lemma mem_rightOnly {w : V} :
    w ∈ rightOnly G u v ↔ G.Adj v w ∧ ¬G.Adj u w ∧ w ≠ u := by
  simp [rightOnly, G.mem_neighborFinset, and_assoc, and_left_comm, and_comm]

@[simp] lemma mem_neither {w : V} :
    w ∈ neither G u v ↔ w ≠ u ∧ w ≠ v ∧ ¬G.Adj u w ∧ ¬G.Adj v w := by
  simp [neither]

lemma pairwise_disjoint_parts :
    Disjoint (common G u v) (leftOnly G u v) ∧
    Disjoint (common G u v) (rightOnly G u v) ∧
    Disjoint (common G u v) (neither G u v) ∧
    Disjoint (leftOnly G u v) (rightOnly G u v) ∧
    Disjoint (leftOnly G u v) (neither G u v) ∧
    Disjoint (rightOnly G u v) (neither G u v) := by
  constructor
  · rw [Finset.disjoint_left]
    intro w hwC hwL
    exact (mem_leftOnly G u v).mp hwL |>.2.1 ((mem_common G u v).mp hwC).2
  constructor
  · rw [Finset.disjoint_left]
    intro w hwC hwR
    exact (mem_rightOnly G u v).mp hwR |>.2.1 ((mem_common G u v).mp hwC).1
  constructor
  · rw [Finset.disjoint_left]
    intro w hwC hwD
    exact (mem_neither G u v).mp hwD |>.2.2.1 ((mem_common G u v).mp hwC).1
  constructor
  · rw [Finset.disjoint_left]
    intro w hwL hwR
    exact (mem_leftOnly G u v).mp hwL |>.2.1 ((mem_rightOnly G u v).mp hwR).1
  constructor
  · rw [Finset.disjoint_left]
    intro w hwL hwD
    exact (mem_neither G u v).mp hwD |>.2.2.1 ((mem_leftOnly G u v).mp hwL).1
  · rw [Finset.disjoint_left]
    intro w hwR hwD
    exact (mem_neither G u v).mp hwD |>.2.2.2 ((mem_rightOnly G u v).mp hwR).1

lemma parts_union (huv : u ≠ v) :
    {u, v} ∪ (common G u v ∪ (leftOnly G u v ∪
      (rightOnly G u v ∪ neither G u v))) = univ := by
  ext w
  simp only [mem_union, mem_insert, mem_singleton, mem_common, mem_leftOnly,
    mem_rightOnly, mem_neither, mem_univ, iff_true]
  by_cases hwu : w = u
  · exact Or.inl (Or.inl hwu)
  by_cases hwv : w = v
  · exact Or.inl (Or.inr hwv)
  by_cases huw : G.Adj u w
  · by_cases hvw : G.Adj v w
    · exact Or.inr (Or.inl ⟨huw, hvw⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨huw, hvw, hwv⟩))
  · by_cases hvw : G.Adj v w
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hvw, huw, hwu⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hwu, hwv, huw, hvw⟩)))

lemma card_parts (huv : u ≠ v) :
    Fintype.card V = 2 + (common G u v).card + (leftOnly G u v).card +
      (rightOnly G u v).card + (neither G u v).card := by
  have hp := pairwise_disjoint_parts G u v
  have hu : ({u, v} : Finset V).card = 2 := by simp [huv]
  have huC : Disjoint ({u, v} : Finset V) (common G u v) := by
    simp [Finset.disjoint_left]
  have huL : Disjoint ({u, v} : Finset V) (leftOnly G u v) := by
    simp [Finset.disjoint_left]
  have huR : Disjoint ({u, v} : Finset V) (rightOnly G u v) := by
    simp [Finset.disjoint_left]
  have huD : Disjoint ({u, v} : Finset V) (neither G u v) := by
    simp [Finset.disjoint_left]
  have hRD : Disjoint (rightOnly G u v) (neither G u v) := hp.2.2.2.2.2
  have hLRD : Disjoint (leftOnly G u v) (rightOnly G u v ∪ neither G u v) :=
    disjoint_sup_right.mpr ⟨hp.2.2.2.1, hp.2.2.2.2.1⟩
  have hCLRD : Disjoint (common G u v)
      (leftOnly G u v ∪ (rightOnly G u v ∪ neither G u v)) :=
    disjoint_sup_right.mpr ⟨hp.1, disjoint_sup_right.mpr ⟨hp.2.1, hp.2.2.1⟩⟩
  have huRest : Disjoint ({u, v} : Finset V)
      (common G u v ∪ (leftOnly G u v ∪ (rightOnly G u v ∪ neither G u v))) :=
    disjoint_sup_right.mpr ⟨huC,
      disjoint_sup_right.mpr ⟨huL, disjoint_sup_right.mpr ⟨huR, huD⟩⟩⟩
  rw [← card_univ, ← parts_union G u v huv]
  rw [card_union_of_disjoint huRest, card_union_of_disjoint hCLRD,
    card_union_of_disjoint hLRD, card_union_of_disjoint hRD]
  simp [hu]
  omega

lemma sum_parts (huv : u ≠ v) (f : V → ℕ) :
    ∑ w, f w = f u + f v + (∑ w ∈ common G u v, f w) +
      (∑ w ∈ leftOnly G u v, f w) + (∑ w ∈ rightOnly G u v, f w) +
      ∑ w ∈ neither G u v, f w := by
  have hp := pairwise_disjoint_parts G u v
  have huC : Disjoint ({u, v} : Finset V) (common G u v) := by
    simp [Finset.disjoint_left]
  have huL : Disjoint ({u, v} : Finset V) (leftOnly G u v) := by
    simp [Finset.disjoint_left]
  have huR : Disjoint ({u, v} : Finset V) (rightOnly G u v) := by
    simp [Finset.disjoint_left]
  have huD : Disjoint ({u, v} : Finset V) (neither G u v) := by
    simp [Finset.disjoint_left]
  have hRD : Disjoint (rightOnly G u v) (neither G u v) := hp.2.2.2.2.2
  have hLRD : Disjoint (leftOnly G u v) (rightOnly G u v ∪ neither G u v) :=
    disjoint_sup_right.mpr ⟨hp.2.2.2.1, hp.2.2.2.2.1⟩
  have hCLRD : Disjoint (common G u v)
      (leftOnly G u v ∪ (rightOnly G u v ∪ neither G u v)) :=
    disjoint_sup_right.mpr ⟨hp.1, disjoint_sup_right.mpr ⟨hp.2.1, hp.2.2.1⟩⟩
  have huRest : Disjoint ({u, v} : Finset V)
      (common G u v ∪ (leftOnly G u v ∪ (rightOnly G u v ∪ neither G u v))) :=
    disjoint_sup_right.mpr ⟨huC,
      disjoint_sup_right.mpr ⟨huL, disjoint_sup_right.mpr ⟨huR, huD⟩⟩⟩
  change (∑ w ∈ (univ : Finset V), f w) = _
  rw [← parts_union G u v huv, Finset.sum_union huRest, Finset.sum_union hCLRD,
    Finset.sum_union hLRD, Finset.sum_union hRD]
  simp [huv]
  omega

lemma degree_eq_card_common_add_leftOnly (huv : u ≠ v) :
    G.degree u = (common G u v).card + (leftOnly G u v).card +
      if G.Adj u v then 1 else 0 := by
  rw [← G.card_neighborFinset_eq_degree]
  by_cases huvA : G.Adj u v
  · have hdecomp : G.neighborFinset u = common G u v ∪ leftOnly G u v ∪ {v} := by
      ext w
      simp only [G.mem_neighborFinset, mem_union, mem_common, mem_leftOnly, mem_singleton]
      constructor
      · intro huw
        by_cases hvw : G.Adj v w
        · exact Or.inl (Or.inl ⟨huw, hvw⟩)
        · by_cases hwv : w = v
          · exact Or.inr hwv
          · exact Or.inl (Or.inr ⟨huw, hvw, hwv⟩)
      · intro hw
        rcases hw with hw | hw
        · rcases hw with ⟨huw, -⟩ | ⟨huw, -, -⟩
          · exact huw
          · exact huw
        · subst w
          exact huvA
    have hCL := (pairwise_disjoint_parts G u v).1
    have hCv : Disjoint (common G u v) {v} := by
      rw [Finset.disjoint_singleton_right]
      intro hv
      exact G.loopless.irrefl v ((mem_common G u v).mp hv).2
    have hLv : Disjoint (leftOnly G u v) {v} := by simp [Finset.disjoint_left]
    have hCLv : Disjoint (common G u v ∪ leftOnly G u v) {v} :=
      disjoint_sup_left.mpr ⟨hCv, hLv⟩
    rw [hdecomp]
    rw [card_union_of_disjoint hCLv, card_union_of_disjoint hCL]
    simp [huvA]
  · have hdecomp : G.neighborFinset u = common G u v ∪ leftOnly G u v := by
      ext w
      simp only [G.mem_neighborFinset, mem_union, mem_common, mem_leftOnly]
      constructor
      · intro huw
        by_cases hvw : G.Adj v w
        · exact Or.inl ⟨huw, hvw⟩
        · refine Or.inr ⟨huw, hvw, ?_⟩
          rintro rfl
          exact huvA huw
      · intro hw
        rcases hw with ⟨huw, -⟩ | ⟨huw, -, -⟩
        · exact huw
        · exact huw
    rw [hdecomp]
    rw [card_union_of_disjoint (pairwise_disjoint_parts G u v).1]
    simp [huvA]

lemma degree_eq_card_common_add_rightOnly (huv : u ≠ v) :
    G.degree v = (common G u v).card + (rightOnly G u v).card +
      if G.Adj u v then 1 else 0 := by
  simpa [common, leftOnly, rightOnly, G.adj_comm, inter_comm] using
    degree_eq_card_common_add_leftOnly G v u huv.symm

lemma card_leftOnly_eq_card_rightOnly (huv : u ≠ v) (hdeg : G.degree u = G.degree v) :
    (leftOnly G u v).card = (rightOnly G u v).card := by
  rw [degree_eq_card_common_add_leftOnly G u v huv,
    degree_eq_card_common_add_rightOnly G u v huv] at hdeg
  omega

end PairPartition

/-! ### A maximal repeated degree lies in the lower half -/

private lemma choose_card_le_sum (s : Finset ℕ) : s.card.choose 2 ≤ ∑ x ∈ s, x := by
  rw [← Finset.card_product_filter_lt]
  calc
    #{p ∈ s ×ˢ s | p.1 < p.2} = ∑ x ∈ s, #{y ∈ s | y < x} := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
      exact Finset.sum_comm
    _ ≤ ∑ x ∈ s, x := by
      gcongr with x hx
      calc
        #{y ∈ s | y < x} ≤ (Finset.range x).card := Finset.card_le_card (by
          intro y hy
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hy).2)
        _ = x := Finset.card_range x

private lemma sum_injective_nat_defect {A : Type*} [DecidableEq A]
    (s : Finset A) (f : A → ℕ) (m : ℕ)
    (hinj : Set.InjOn f s) (hle : ∀ x ∈ s, f x ≤ m) :
    2 * (∑ x ∈ s, f x) + s.card * (s.card - 1) ≤ 2 * s.card * m := by
  let g : A → ℕ := fun x ↦ m - f x
  have hginj : Set.InjOn g s := by
    intro x hx y hy hxy
    apply hinj hx hy
    exact (tsub_right_inj (hle x hx) (hle y hy)).mp hxy
  have hcard : (s.image g).card = s.card := Finset.card_image_of_injOn hginj
  have hsum : ∑ y ∈ s.image g, y = ∑ x ∈ s, (m - f x) := by
    rw [Finset.sum_image hginj]
  have hchoose := choose_card_le_sum (s.image g)
  rw [hsum, Finset.sum_tsub_distrib s hle] at hchoose
  rw [Finset.sum_const_nat (m := m) (fun _ _ ↦ rfl)] at hchoose
  rw [hcard, Nat.choose_two_right] at hchoose
  have htwice := Nat.mul_le_mul_left 2 hchoose
  rw [mul_comm 2, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self s.card)] at htwice
  have hsumle := sum_le_card_mul s f m hle
  calc
    2 * (∑ x ∈ s, f x) + s.card * (s.card - 1) ≤
        2 * (∑ x ∈ s, f x) + 2 * (s.card * m - ∑ x ∈ s, f x) :=
      Nat.add_le_add_left htwice _
    _ = 2 * ((∑ x ∈ s, f x) + (s.card * m - ∑ x ∈ s, f x)) := by
      rw [Nat.mul_add]
    _ = 2 * (s.card * m) := by rw [Nat.add_sub_of_le hsumle]
    _ = 2 * s.card * m := by rw [Nat.mul_assoc]

/-- A degree value attained at two distinct vertices and maximal among all
degrees cannot exceed `n`.  This is the equal-endpoint counting core. -/
lemma maximal_repeated_degree_le_half
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n Δ : ℕ}
    (hn : 2 ≤ n)
    (hcard : Fintype.card V = 2 * n + 1)
    (hedges : n ^ 2 + n + 1 ≤ G.edgeFinset.card)
    (hno : ∀ {a b : V}, a ≠ b → G.degree a = G.degree b →
      ¬ JoinedByPathThree G a b)
    {u v : V}
    (huv : u ≠ v)
    (hdu : G.degree u = Δ)
    (hdv : G.degree v = Δ)
    (hmax : ∀ w : V, G.degree w ≤ Δ) :
    Δ ≤ n := by
  by_contra hle
  have hlarge : n + 1 ≤ Δ := by omega
  have huvdeg : G.degree u = G.degree v := hdu.trans hdv.symm
  have hnopath : ¬ JoinedByPathThree G u v := hno huv huvdeg
  let C := common G u v
  let L := leftOnly G u v
  let R := rightOnly G u v
  let D := neither G u v
  have hLR : L.card = R.card := by
    simpa [L, R] using card_leftOnly_eq_card_rightOnly G u v huv huvdeg
  have hparts : Fintype.card V = 2 + C.card + L.card + R.card + D.card := by
    simpa [C, L, R, D] using card_parts G u v huv
  have hforbid {x y : V}
      (hux : G.Adj u x) (hxv : x ≠ v)
      (hvy : G.Adj v y) (hyu : y ≠ u) : ¬ G.Adj x y := by
    intro hxy
    apply hnopath
    exact joinedByPathThree_of_adj hux hxy hvy.symm hux.ne hyu.symm huv
      hxy.ne hxv hvy.ne.symm
  have hCbound : ∀ x ∈ C, G.degree x ≤ 2 + D.card := by
    intro x hx
    have hxC : x ∈ common G u v := by simpa [C] using hx
    have hxA := (mem_common G u v).mp hxC
    rw [← G.card_neighborFinset_eq_degree]
    calc
      (G.neighborFinset x).card ≤ ({u, v} ∪ D).card := by
        apply Finset.card_le_card
        intro z hz
        have hxz : G.Adj x z := (G.mem_neighborFinset x z).mp hz
        simp only [mem_union, mem_insert, mem_singleton]
        by_cases hzu : z = u
        · exact Or.inl (Or.inl hzu)
        by_cases hzv : z = v
        · exact Or.inl (Or.inr hzv)
        refine Or.inr ?_
        have hnuz : ¬ G.Adj u z := by
          intro huz
          exact hforbid huz hzv hxA.2 hxA.1.ne.symm hxz.symm
        have hnvz : ¬ G.Adj v z := by
          intro hvz
          exact hforbid hxA.1 hxA.2.ne.symm hvz hzu hxz
        exact (mem_neither G u v).mpr ⟨hzu, hzv, hnuz, hnvz⟩
      _ ≤ 2 + D.card := by
        calc
          ({u, v} ∪ D).card ≤ ({u, v} : Finset V).card + D.card :=
            Finset.card_union_le (s := {u, v}) (t := D)
          _ ≤ 2 + D.card := by simp [huv]
  have hLbound : ∀ x ∈ L, G.degree x ≤ L.card + D.card := by
    intro x hx
    have hxL : x ∈ leftOnly G u v := by simpa [L] using hx
    have hxA := (mem_leftOnly G u v).mp hxL
    rw [← G.card_neighborFinset_eq_degree]
    calc
      (G.neighborFinset x).card ≤ ({u} ∪ (L.erase x ∪ D)).card := by
        apply Finset.card_le_card
        intro z hz
        have hxz : G.Adj x z := (G.mem_neighborFinset x z).mp hz
        simp only [mem_union, mem_singleton, mem_erase]
        by_cases hzu : z = u
        · exact Or.inl hzu
        refine Or.inr ?_
        have hnvz : ¬ G.Adj v z := by
          intro hvz
          exact hforbid hxA.1 hxA.2.2 hvz hzu hxz
        by_cases huz : G.Adj u z
        · refine Or.inl ⟨hxz.ne.symm, ?_⟩
          have hzv : z ≠ v := by
            rintro rfl
            exact hxA.2.1 hxz.symm
          have hzL : z ∈ leftOnly G u v :=
            (mem_leftOnly G u v).mpr ⟨huz, hnvz, hzv⟩
          simpa [L] using hzL
        · refine Or.inr ?_
          have hzv : z ≠ v := by
            rintro rfl
            exact hxA.2.1 hxz.symm
          exact (mem_neither G u v).mpr ⟨hzu, hzv, huz, hnvz⟩
      _ ≤ 1 + (L.erase x).card + D.card := by
        calc
          ({u} ∪ (L.erase x ∪ D)).card
              ≤ ({u} : Finset V).card + (L.erase x ∪ D).card :=
            Finset.card_union_le (s := {u}) (t := L.erase x ∪ D)
          _ ≤ 1 + ((L.erase x).card + D.card) := by
            simpa using Nat.add_le_add_left
              (Finset.card_union_le (s := L.erase x) (t := D)) 1
          _ = 1 + (L.erase x).card + D.card := by omega
      _ = L.card + D.card := by
        rw [Finset.card_erase_of_mem hx]
        have hxpos : 0 < L.card := Finset.card_pos.mpr ⟨x, hx⟩
        omega
  have hRbound : ∀ x ∈ R, G.degree x ≤ R.card + D.card := by
    intro x hx
    have hxR : x ∈ rightOnly G u v := by simpa [R] using hx
    have hxB := (mem_rightOnly G u v).mp hxR
    rw [← G.card_neighborFinset_eq_degree]
    calc
      (G.neighborFinset x).card ≤ ({v} ∪ (R.erase x ∪ D)).card := by
        apply Finset.card_le_card
        intro z hz
        have hxz : G.Adj x z := (G.mem_neighborFinset x z).mp hz
        simp only [mem_union, mem_singleton, mem_erase]
        by_cases hzv : z = v
        · exact Or.inl hzv
        refine Or.inr ?_
        have hnuz : ¬ G.Adj u z := by
          intro huz
          exact hforbid huz hzv hxB.1 hxB.2.2 hxz.symm
        by_cases hvz : G.Adj v z
        · refine Or.inl ⟨hxz.ne.symm, ?_⟩
          have hzu : z ≠ u := by
            rintro rfl
            exact hxB.2.1 hxz.symm
          have hzR : z ∈ rightOnly G u v :=
            (mem_rightOnly G u v).mpr ⟨hvz, hnuz, hzu⟩
          simpa [R] using hzR
        · refine Or.inr ?_
          have hzu : z ≠ u := by
            rintro rfl
            exact hxB.2.1 hxz.symm
          exact (mem_neither G u v).mpr ⟨hzu, hzv, hnuz, hvz⟩
      _ ≤ 1 + (R.erase x).card + D.card := by
        calc
          ({v} ∪ (R.erase x ∪ D)).card
              ≤ ({v} : Finset V).card + (R.erase x ∪ D).card :=
            Finset.card_union_le (s := {v}) (t := R.erase x ∪ D)
          _ ≤ 1 + ((R.erase x).card + D.card) := by
            simpa using Nat.add_le_add_left
              (Finset.card_union_le (s := R.erase x) (t := D)) 1
          _ = 1 + (R.erase x).card + D.card := by omega
      _ = R.card + D.card := by
        rw [Finset.card_erase_of_mem hx]
        have hxpos : 0 < R.card := Finset.card_pos.mpr ⟨x, hx⟩
        omega
  have hDbound : ∀ x ∈ D, G.degree x ≤ Δ := fun x _ ↦ hmax x
  have hDstruct : ∀ x ∈ D, G.degree x ≤ 2 * n - 2 := by
    intro x hx
    have hxD : x ∈ neither G u v := by simpa [D] using hx
    have hxN := (mem_neither G u v).mp hxD
    rw [← G.card_neighborFinset_eq_degree]
    calc
      (G.neighborFinset x).card ≤ ((univ : Finset V) \ {u, v, x}).card := by
        apply Finset.card_le_card
        intro z hz
        have hxz : G.Adj x z := (G.mem_neighborFinset x z).mp hz
        simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and, not_or]
        exact ⟨fun hzu ↦ hxN.2.2.1 (hzu ▸ hxz.symm),
          fun hzv ↦ hxN.2.2.2 (hzv ▸ hxz.symm), hxz.ne.symm⟩
      _ = Fintype.card V - 3 := by
        rw [Finset.card_sdiff]
        simp [huv, hxN.1.symm, hxN.2.1.symm]
      _ = 2 * n - 2 := by omega
  have hsumC : ∑ x ∈ C, G.degree x ≤ C.card * (2 + D.card) :=
    sum_le_card_mul C (fun x ↦ G.degree x) (2 + D.card) hCbound
  have hsumL : ∑ x ∈ L, G.degree x ≤ L.card * (L.card + D.card) :=
    sum_le_card_mul L (fun x ↦ G.degree x) (L.card + D.card) hLbound
  have hsumR : ∑ x ∈ R, G.degree x ≤ R.card * (R.card + D.card) :=
    sum_le_card_mul R (fun x ↦ G.degree x) (R.card + D.card) hRbound
  have hsumD : ∑ x ∈ D, G.degree x ≤ D.card * Δ :=
    sum_le_card_mul D (fun x ↦ G.degree x) Δ hDbound
  have hsumDstruct : ∑ x ∈ D, G.degree x ≤ D.card * (2 * n - 2) :=
    sum_le_card_mul D (fun x ↦ G.degree x) (2 * n - 2) hDstruct
  have hsumParts :
      ∑ w, G.degree w = G.degree u + G.degree v + (∑ w ∈ C, G.degree w) +
        (∑ w ∈ L, G.degree w) + (∑ w ∈ R, G.degree w) +
        ∑ w ∈ D, G.degree w := by
    simpa [C, L, R, D] using sum_parts G u v huv (fun w ↦ G.degree w)
  have hlower : 2 * (n ^ 2 + n + 1) ≤ ∑ w, G.degree w := by
    calc
      2 * (n ^ 2 + n + 1) ≤ 2 * G.edgeFinset.card := Nat.mul_le_mul_left 2 hedges
      _ = ∑ w, G.degree w := G.sum_degrees_eq_twice_card_edges.symm
  have hsize : 2 * n + 1 = 2 + C.card + 2 * L.card + D.card := by
    rw [hcard, hLR] at hparts
    omega
  by_cases huvA : G.Adj u v
  · have hDelta : Δ = C.card + L.card + 1 := by
      calc
        Δ = G.degree u := hdu.symm
        _ = C.card + L.card + 1 := by
          simpa [C, L, huvA] using degree_eq_card_common_add_leftOnly G u v huv
    have hCinj : Set.InjOn (fun x ↦ G.degree x) (↑C : Set V) := by
      intro x hx y hy hdeg
      by_contra hxy
      apply hno hxy hdeg
      have hxC : x ∈ common G u v := by simpa [C] using hx
      have hyC : y ∈ common G u v := by simpa [C] using hy
      have hxA := (mem_common G u v).mp hxC
      have hyA := (mem_common G u v).mp hyC
      exact joinedByPathThree_of_adj hxA.1.symm huvA hyA.2
        hxA.1.ne.symm hxA.2.ne.symm hxy huv hyA.1.ne hyA.2.ne
    have hCsharp :
        2 * (∑ x ∈ C, G.degree x) + C.card * (C.card - 1) ≤
          2 * C.card * (2 + D.card) :=
      sum_injective_nat_defect C (fun x ↦ G.degree x) (2 + D.card) hCinj hCbound
    have hCpos : 1 ≤ C.card := by omega
    have hCsub : C.card - 1 + 1 = C.card := Nat.sub_add_cancel hCpos
    have hnsub : 2 * n - 2 + 2 = 2 * n := Nat.sub_add_cancel (by omega)
    rw [← hLR] at hsumR
    rw [hsumParts, hdu, hdv] at hlower
    by_cases hnthree : 3 ≤ n
    · by_cases hDcase : Δ ≤ 2 * n - 2
      · nlinarith only [hDelta, hsize, hlower, hCsharp, hsumL, hsumR,
          hsumD, hnthree, hlarge, hDcase, hCsub, hnsub]
      · have hDcase' : 2 * n - 2 ≤ Δ := by omega
        nlinarith only [hDelta, hsize, hlower, hCsharp, hsumL, hsumR,
          hsumDstruct, hnthree, hlarge, hDcase', hCsub, hnsub]
    · have hn2 : n = 2 := by omega
      nlinarith only [hDelta, hsize, hlower, hCsharp, hsumL, hsumR,
        hsumDstruct, hn2, hlarge, hCsub, hnsub]
  · have hDelta : Δ = C.card + L.card := by
      calc
        Δ = G.degree u := hdu.symm
        _ = C.card + L.card := by
          simpa [C, L, huvA] using degree_eq_card_common_add_leftOnly G u v huv
    rw [← hLR] at hsumR
    rw [hsumParts, hdu, hdv] at hlower
    nlinarith only [hDelta, hsize, hlower, hsumC, hsumL, hsumR, hsumD,
      hlarge]

/-! ### The unique maximum-degree case -/

/-- If the labels above `γ` are injective and all labels are at most `d`, then
their sum is bounded by the constant baseline `γ` plus every possible positive
excess between `γ + 1` and `d`. -/
lemma sum_le_baseline_add_all_excesses
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ) (γ d : ℕ)
    (hbound : ∀ x ∈ s, f x ≤ d)
    (hinj : Set.InjOn f {x | x ∈ s ∧ γ < f x}) :
    (∑ x ∈ s, f x) ≤
      γ * s.card + ∑ k ∈ Finset.Ioc γ d, (k - γ) := by
  let high : Finset α := s.filter fun x ↦ γ < f x
  have hsplit : (∑ x ∈ s, (f x - γ)) = ∑ x ∈ high, (f x - γ) := by
    symm
    apply Finset.sum_subset
    · intro x hx
      exact (Finset.mem_filter.mp hx).1
    · intro x hxS hxNot
      have hle : f x ≤ γ := by
        simp only [high, Finset.mem_filter, not_and] at hxNot
        exact Nat.le_of_not_gt (hxNot hxS)
      simp [Nat.sub_eq_zero_of_le hle]
  have hhighInj : Set.InjOn f (↑high : Set α) := by
    intro x hx y hy hxy
    apply hinj
    · simpa only [high, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq] using hx
    · simpa only [high, Finset.mem_coe, Finset.mem_filter, Set.mem_setOf_eq] using hy
    · exact hxy
  have himage : high.image f ⊆ Finset.Ioc γ d := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_filter.mp hx).2,
      hbound x (Finset.mem_filter.mp hx).1⟩
  have hexcess :
      (∑ x ∈ high, (f x - γ)) ≤ ∑ k ∈ Finset.Ioc γ d, (k - γ) := by
    calc
      (∑ x ∈ high, (f x - γ)) = ∑ k ∈ high.image f, (k - γ) := by
        rw [Finset.sum_image hhighInj]
      _ ≤ ∑ k ∈ Finset.Ioc γ d, (k - γ) :=
        Finset.sum_le_sum_of_subset himage
  calc
    ∑ x ∈ s, f x ≤ ∑ x ∈ s, (γ + (f x - γ)) := by
      exact Finset.sum_le_sum fun x _ ↦ by omega
    _ = γ * s.card + ∑ x ∈ s, (f x - γ) := by
      simp [Finset.sum_add_distrib, Nat.mul_comm]
    _ ≤ γ * s.card + ∑ k ∈ Finset.Ioc γ d, (k - γ) := by
      rw [hsplit]
      exact Nat.add_le_add_left hexcess _

/-- A vertex with two common neighbors with `v` has degree different from every
other neighbor of `v`, when equal-degree endpoints of a three-edge path are
forbidden. -/
lemma degree_ne_of_two_common_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hno : ∀ {u w : V}, G.degree u = G.degree w →
      ¬ JoinedByPathThree G u w)
    {v u w : V} (hvu : G.Adj v u) (hvw : G.Adj v w) (huw : u ≠ w)
    (hcommon : 2 ≤ (G.neighborFinset u ∩ G.neighborFinset v).card) :
    G.degree u ≠ G.degree w := by
  intro hdeg
  apply hno hdeg
  let C := G.neighborFinset u ∩ G.neighborFinset v
  have hCcard : 2 ≤ C.card := by simpa [C] using hcommon
  have hnot : ¬ C ⊆ {w} := by
    intro hsub
    have hc := Finset.card_le_card hsub
    have hC : C.card ≤ 1 := by simpa using hc
    omega
  obtain ⟨x, hxC, hxw⟩ := Finset.not_subset.mp hnot
  have hxw' : x ≠ w := by simpa only [Finset.mem_singleton] using hxw
  have hux : G.Adj u x := (G.mem_neighborFinset u x).mp (Finset.mem_inter.mp hxC).1
  have hvx : G.Adj v x := (G.mem_neighborFinset v x).mp (Finset.mem_inter.mp hxC).2
  exact joinedByPathThree_of_adj hux hvx.symm hvw
    hux.ne hvu.ne.symm huw hvx.ne.symm hxw' hvw.ne

/-- Re-index the positive excesses over an interval by an initial segment. -/
lemma sum_Ioc_sub_eq_sum_range_succ (a r : ℕ) :
    (∑ k ∈ Finset.Ioc a (a + r), (k - a)) =
      ∑ i ∈ Finset.range r, (i + 1) := by
  have hIoc : Finset.Ioc a (a + r) =
      (Finset.range r).image (fun i ↦ a + i + 1) := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hk
      refine ⟨k - a - 1, ?_, ?_⟩ <;> omega
    · rintro ⟨i, hi, rfl⟩
      omega
  have hinj : Set.InjOn (fun i ↦ a + i + 1) (↑(Finset.range r) : Set ℕ) := by
    intro i hi j hj hij
    exact Nat.add_left_cancel (Nat.add_right_cancel hij)
  rw [hIoc, Finset.sum_image hinj]
  apply Finset.sum_congr rfl
  intro i hi
  omega

lemma twice_sum_range_succ (r : ℕ) :
    2 * (∑ i ∈ Finset.range r, (i + 1)) = r * (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ]
      nlinarith

/-- If the maximum degree is attained uniquely, the edge threshold forces it
to be at most `n + 1`. -/
lemma unique_max_degree_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {n : ℕ}
    (hn : 2 ≤ n)
    (hcard : Fintype.card V = 2 * n + 1)
    (hedges : n ^ 2 + n + 1 ≤ G.edgeFinset.card)
    (hno : ∀ {u w : V}, G.degree u = G.degree w →
      ¬ JoinedByPathThree G u w)
    (v : V)
    (hmax : ∀ w : V, G.degree w ≤ G.degree v)
    (huniq : ∀ w : V, G.degree w = G.degree v → w = v) :
    G.degree v ≤ n + 1 := by
  by_contra hle
  let Δ := G.degree v
  have hlarge : n + 2 ≤ Δ := by omega
  have hΔlt : Δ < 2 * n + 1 := by
    simpa [Δ, hcard] using G.degree_lt_card_verts v
  let s := Δ - n
  let p := n - s
  let T := p + 2
  let d := Δ - 1
  let r := 2 * s - 3
  have hslo : 2 ≤ s := by simp only [s]; omega
  have hsle : s ≤ n := by simp only [s]; omega
  have hsEq : Δ = n + s := by simp only [s]; omega
  have hpEq : n = p + s := by simp only [p]; omega
  have hTEq : T = p + 2 := rfl
  have hdEq : d + 1 = Δ := by simp only [d]; omega
  have hrEq : r + 3 = 2 * s := by simp only [r]; omega
  have hdTR : d = T + r := by omega
  let Nv := G.neighborFinset v
  have hNvcard : Nv.card = Δ := by
    simpa [Nv, Δ] using G.card_neighborFinset_eq_degree v
  have houtsideCard : ((univ : Finset V) \ Nv).card = p + 1 := by
    rw [Finset.card_sdiff]
    simp only [inter_univ, Finset.card_univ, hcard, hNvcard]
    omega
  have hcommon (u : V) (hu : u ∈ Nv) (huHigh : T < G.degree u) :
      2 ≤ (G.neighborFinset u ∩ Nv).card := by
    have hdiffSub : G.neighborFinset u \ Nv ⊆ (univ : Finset V) \ Nv := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
    have hdiff : (G.neighborFinset u \ Nv).card ≤ p + 1 := by
      rw [← houtsideCard]
      exact Finset.card_le_card hdiffSub
    have hsplit := Finset.card_inter_add_card_sdiff (G.neighborFinset u) Nv
    rw [G.card_neighborFinset_eq_degree] at hsplit
    omega
  have hbound : ∀ u ∈ Nv, G.degree u ≤ d := by
    intro u hu
    have huv : u ≠ v := by
      intro huv
      subst u
      exact G.loopless.irrefl v ((G.mem_neighborFinset v v).mp hu)
    have humax := hmax u
    have hune : G.degree u ≠ Δ := by
      intro hueq
      apply huv
      apply huniq u
      simpa [Δ] using hueq
    simp only [d]
    omega
  have hhighInj :
      Set.InjOn (fun u ↦ G.degree u) {u | u ∈ Nv ∧ T < G.degree u} := by
    intro u hu w hw hdeg
    by_contra huw
    have hvu : G.Adj v u := by
      simpa [Nv] using (G.mem_neighborFinset v u).mp hu.1
    have hvw : G.Adj v w := by
      simpa [Nv] using (G.mem_neighborFinset v w).mp hw.1
    exact (degree_ne_of_two_common_neighbors G hno hvu hvw huw
      (by simpa [Nv] using hcommon u hu.1 hu.2)) hdeg
  have hNsum :
      (∑ u ∈ Nv, G.degree u) ≤
        T * Δ + ∑ k ∈ Finset.Ioc T d, (k - T) := by
    have h := sum_le_baseline_add_all_excesses Nv (fun u ↦ G.degree u) T d
      hbound hhighInj
    simpa [hNvcard] using h
  let E := ∑ k ∈ Finset.Ioc T d, (k - T)
  have hE : 2 * E = r * (r + 1) := by
    calc
      2 * E = 2 * (∑ k ∈ Finset.Ioc T (T + r), (k - T)) := by
        simp only [E, hdTR]
      _ = 2 * (∑ i ∈ Finset.range r, (i + 1)) := by
        rw [sum_Ioc_sub_eq_sum_range_succ]
      _ = r * (r + 1) := twice_sum_range_succ r
  let closed := ({v} : Finset V) ∪ Nv
  let O := (univ : Finset V) \ closed
  have hvNv : Disjoint ({v} : Finset V) Nv := by
    rw [Finset.disjoint_singleton_left]
    intro hv
    exact G.loopless.irrefl v ((G.mem_neighborFinset v v).mp hv)
  have hclosedCard : closed.card = 1 + Δ := by
    simp only [closed]
    rw [Finset.card_union_of_disjoint hvNv]
    simp [hNvcard]
  have hclosedSub : closed ⊆ (univ : Finset V) := Finset.subset_univ closed
  have hOcard : O.card = p := by
    simp only [O]
    rw [Finset.card_sdiff]
    simp only [inter_univ, Finset.card_univ, hcard, hclosedCard]
    omega
  have hObound : ∀ u ∈ O, G.degree u ≤ d := by
    intro u hu
    have huv : u ≠ v := by
      intro huv
      subst u
      have hnot := (Finset.mem_sdiff.mp hu).2
      exact hnot (by simp [closed])
    have humax := hmax u
    have hune : G.degree u ≠ Δ := by
      intro hueq
      apply huv
      apply huniq u
      simpa [Δ] using hueq
    simp only [d]
    omega
  have hOsum : (∑ u ∈ O, G.degree u) ≤ p * d := by
    have h := sum_le_card_mul O (fun u ↦ G.degree u) d hObound
    simpa [hOcard] using h
  have hclosedSum :
      (∑ u ∈ closed, G.degree u) = Δ + ∑ u ∈ Nv, G.degree u := by
    simp only [closed]
    rw [Finset.sum_union hvNv]
    simp [Δ]
  have hsumSplit :
      ∑ u, G.degree u = Δ + (∑ u ∈ Nv, G.degree u) + ∑ u ∈ O, G.degree u := by
    have hsum := Finset.sum_sdiff hclosedSub (f := fun u ↦ G.degree u)
    change (∑ u ∈ (univ : Finset V), G.degree u) = _
    simp only [O]
    rw [← hsum, hclosedSum]
    omega
  have hlower : 2 * (n ^ 2 + n + 1) ≤ ∑ u, G.degree u := by
    calc
      2 * (n ^ 2 + n + 1) ≤ 2 * G.edgeFinset.card :=
        Nat.mul_le_mul_left 2 hedges
      _ = ∑ u, G.degree u := G.sum_degrees_eq_twice_card_edges.symm
  have hupper :
      ∑ u, G.degree u ≤ Δ + (T * Δ + E) + p * d := by
    rw [hsumSplit]
    exact Nat.add_le_add (Nat.add_le_add_left (by simpa [E] using hNsum) Δ) hOsum
  have hnumeric : Δ + (T * Δ + E) + p * d ≤ 2 * n ^ 2 + 2 * n + 1 := by
    nlinarith only [hsEq, hpEq, hTEq, hdEq, hrEq, hslo, hE]
  nlinarith only [hlower, hupper, hnumeric]

/-! ### Resolution of Erdős Problem 816 -/

/-- The slightly stronger monotone form of Erdős Problem 816: `n²+n+1`
edges may be replaced by "at least `n²+n+1` edges". -/
theorem erdos_816_of_at_least
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : 2 ≤ n)
    (hcard : Fintype.card V = 2 * n + 1)
    (hedges : n ^ 2 + n + 1 ≤ G.edgeFinset.card) :
    ∃ u v : V, u ≠ v ∧ G.degree u = G.degree v ∧ JoinedByPathThree G u v := by
  by_contra hcounterexample
  have hno : ∀ {u v : V}, G.degree u = G.degree v →
      ¬ JoinedByPathThree G u v := by
    intro u v hdegree hpath
    have huv : u ≠ v := by
      rcases hpath with ⟨x, y, -, -, huv, -⟩
      exact huv
    exact hcounterexample ⟨u, v, huv, hdegree, hpath⟩
  have hpos : 0 < Fintype.card V := by omega
  letI : Nonempty V := Fintype.card_pos_iff.mp hpos
  obtain ⟨v, -, hmax⟩ :=
    Finset.exists_max_image (univ : Finset V) (fun w ↦ G.degree w) Finset.univ_nonempty
  have hmax' : ∀ w : V, G.degree w ≤ G.degree v := by
    intro w
    exact hmax w (Finset.mem_univ w)
  have hlower : 2 * (n ^ 2 + n + 1) ≤ ∑ w, G.degree w := by
    calc
      2 * (n ^ 2 + n + 1) ≤ 2 * G.edgeFinset.card :=
        Nat.mul_le_mul_left 2 hedges
      _ = ∑ w, G.degree w := G.sum_degrees_eq_twice_card_edges.symm
  by_cases hrep : ∃ u : V, u ≠ v ∧ G.degree u = G.degree v
  · obtain ⟨u, huv, hdegree⟩ := hrep
    have hvle : G.degree v ≤ n :=
      maximal_repeated_degree_le_half G hn hcard hedges
        (fun hab hdeg ↦ hno hdeg) huv hdegree rfl hmax'
    have hall : ∀ w : V, G.degree w ≤ n := fun w ↦ (hmax' w).trans hvle
    have hupper : ∑ w, G.degree w ≤ (2 * n + 1) * n := by
      have h := sum_le_card_mul (univ : Finset V) (fun w ↦ G.degree w) n
        (fun w _ ↦ hall w)
      simpa [Finset.card_univ, hcard] using h
    nlinarith only [hlower, hupper]
  · have huniq : ∀ w : V, G.degree w = G.degree v → w = v := by
      intro w hdegree
      by_contra hwv
      exact hrep ⟨w, hwv, hdegree⟩
    have hvle := unique_max_degree_le G hn hcard hedges hno v hmax' huniq
    let R := (univ : Finset V).erase v
    have hRcard : R.card = 2 * n := by
      simp only [R]
      rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, hcard]
      omega
    have hRbound : ∀ w ∈ R, G.degree w ≤ n := by
      intro w hw
      have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
      have hwmax := hmax' w
      have hwne : G.degree w ≠ G.degree v := by
        intro hdegree
        exact hwv (huniq w hdegree)
      omega
    have hRsum : (∑ w ∈ R, G.degree w) ≤ 2 * n * n := by
      have h := sum_le_card_mul R (fun w ↦ G.degree w) n hRbound
      simpa [hRcard] using h
    have hsplit := Finset.sum_erase_add (univ : Finset V) (fun w ↦ G.degree w)
      (Finset.mem_univ v)
    have hupper : ∑ w, G.degree w ≤ 2 * n * n + (n + 1) := by
      change (∑ w ∈ (univ : Finset V), G.degree w) ≤ _
      rw [← hsplit]
      exact Nat.add_le_add hRsum hvle
    nlinarith only [hlower, hupper, hn]

/-- Erdős Problem 816 in its exact stated form.  The condition `n ≥ 2` is
necessary: for `n = 1`, the triangle has the required order and size but has
no simple three-edge path. -/
theorem erdos_816
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : ℕ) (hn : 2 ≤ n)
    (hcard : Fintype.card V = 2 * n + 1)
    (hedges : G.edgeFinset.card = n ^ 2 + n + 1) :
    ∃ u v : V, u ≠ v ∧ G.degree u = G.degree v ∧ JoinedByPathThree G u v := by
  apply erdos_816_of_at_least G n hn hcard
  omega

end Erdos816
