/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 35.
https://www.erdosproblems.com/forum/thread/35

Informal authors:
- Helmut Plünnecke

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos35.md
-/
/- Original license: Apache 2.0. -/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Schnirelmann
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 35

Let `B ⊆ ℕ` be an additive basis of order `k`, with `0 ∈ B`.  Plünnecke's
Schnirelmann-density inequality gives

`σ(A + B) ≥ σ(A) ^ (1 - 1 / k)`.

The elementary power estimate

`α ^ (1 - 1 / k) ≥ α + α * (1 - α) / k`

then resolves Erdős Problem 35 in the affirmative.  The finite core below is
the truncated addition-graph version of Plünnecke's magnification inequality;
the truncation is essential because Schnirelmann density uses every initial
interval.

Mathematical sources:

* H. Plünnecke, *Eine zahlentheoretische Anwendung der Graphentheorie*,
  J. Reine Angew. Math. 243 (1970), 171–183.
* R. Jin, *Density Versions of Plünnecke Inequality—Epsilon-Delta Approach*,
  in CANT 2011 and 2012, Springer Proc. Math. Stat. 101 (2014), 99–113,
  especially Theorem 3 and Section 4.
* https://www.erdosproblems.com/35
-/

open scoped BigOperators Pointwise
open Finset Set Real

attribute [local instance] Classical.propDecidable

noncomputable section

namespace Erdos35

/-- The exact order-`k` additive-basis predicate used in Problem 35.  Pointwise
natural scalar multiplication is the `k`-fold sumset, with `0 • B = {0}`. -/
def IsAdditiveBasisOfOrder (B : Set ℕ) (k : ℕ) : Prop :=
  k • B = Set.univ

/-- The number of elements of `A` in the closed natural interval `[a,b]`. -/
def countOn (A : Set ℕ) (a b : ℕ) : ℕ :=
  #{x ∈ Icc a b | x ∈ A}

/-- The number of elements of `A` in `{1, ..., n}`. -/
def countIn (A : Set ℕ) (n : ℕ) : ℕ :=
  #{x ∈ Ioc 0 n | x ∈ A}

lemma countIn_eq_countOn_one (A : Set ℕ) (n : ℕ) :
    countIn A n = countOn A 1 n := by
  have hinterval : Finset.Ioc 0 n = Finset.Icc 1 n := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    constructor
    · rintro ⟨hx0, hxn⟩
      exact ⟨Nat.succ_le_iff.2 hx0, hxn⟩
    · rintro ⟨hx1, hxn⟩
      exact ⟨Nat.succ_le_iff.1 hx1, hxn⟩
  simp only [countIn, countOn, hinterval]

lemma countIn_density (A : Set ℕ) (n : ℕ) :
    schnirelmannDensity A * n ≤ countIn A n := by
  exact schnirelmannDensity_mul_le_card_filter

lemma countIn_le (A : Set ℕ) (n : ℕ) : countIn A n ≤ n := by
  calc
    countIn A n ≤ #(Ioc 0 n) := card_filter_le _ _
    _ = n := by simp

lemma countOn_le_length (A : Set ℕ) {a b : ℕ} (hab : a ≤ b) :
    countOn A a b ≤ b - a + 1 := by
  calc
    countOn A a b ≤ #(Icc a b) := card_filter_le _ _
    _ = b - a + 1 := by
      rw [Nat.card_Icc]
      simpa [Nat.add_comm] using Nat.add_sub_assoc hab 1

/-- Truncated pointwise addition of two finite sets of naturals. -/
def truncAdd (n : ℕ) (A B : Finset ℕ) : Finset ℕ :=
  (A + B).filter (· ≤ n)

@[simp] lemma mem_truncAdd {n x : ℕ} {A B : Finset ℕ} :
    x ∈ truncAdd n A B ↔ ∃ a ∈ A, ∃ b ∈ B, a + b = x ∧ x ≤ n := by
  simp only [truncAdd, Finset.mem_filter, Finset.mem_add]
  constructor
  · rintro ⟨⟨a, ha, b, hb, hab⟩, hxn⟩
    exact ⟨a, ha, b, hb, hab, hxn⟩
  · rintro ⟨a, ha, b, hb, hab, hxn⟩
    exact ⟨⟨a, ha, b, hb, hab⟩, hxn⟩

lemma truncAdd_comm (n : ℕ) (A B : Finset ℕ) :
    truncAdd n A B = truncAdd n B A := by
  simp [truncAdd, add_comm]

@[simp] lemma truncAdd_empty_left (n : ℕ) (B : Finset ℕ) :
    truncAdd n ∅ B = ∅ := by simp [truncAdd]

@[simp] lemma truncAdd_empty_right (n : ℕ) (A : Finset ℕ) :
    truncAdd n A ∅ = ∅ := by simp [truncAdd]

lemma truncAdd_mono_left {n : ℕ} {A A' B : Finset ℕ} (h : A ⊆ A') :
    truncAdd n A B ⊆ truncAdd n A' B := by
  intro x hx
  rw [mem_truncAdd] at hx ⊢
  obtain ⟨a, ha, b, hb, rfl, hab⟩ := hx
  exact ⟨a, h ha, b, hb, rfl, hab⟩

lemma truncAdd_mono_right {n : ℕ} {A B B' : Finset ℕ} (h : B ⊆ B') :
    truncAdd n A B ⊆ truncAdd n A B' := by
  simpa only [truncAdd_comm n A B, truncAdd_comm n A B'] using
    truncAdd_mono_left (n := n) (B := A) h

lemma truncAdd_union_left (n : ℕ) (A A' B : Finset ℕ) :
    truncAdd n (A ∪ A') B = truncAdd n A B ∪ truncAdd n A' B := by
  ext x
  simp only [mem_truncAdd, Finset.mem_union]
  constructor
  · rintro ⟨a, ha, b, hb, hab, hxn⟩
    rcases ha with ha | ha
    · exact Or.inl ⟨a, ha, b, hb, hab, hxn⟩
    · exact Or.inr ⟨a, ha, b, hb, hab, hxn⟩
  · rintro (⟨a, ha, b, hb, hab, hxn⟩ | ⟨a, ha, b, hb, hab, hxn⟩)
    · exact ⟨a, Or.inl ha, b, hb, hab, hxn⟩
    · exact ⟨a, Or.inr ha, b, hb, hab, hxn⟩

lemma truncAdd_union_right (n : ℕ) (A B B' : Finset ℕ) :
    truncAdd n A (B ∪ B') = truncAdd n A B ∪ truncAdd n A B' := by
  simpa only [truncAdd_comm n A (B ∪ B'), truncAdd_comm n A B,
    truncAdd_comm n A B'] using truncAdd_union_left n B B' A

/-- Iterated truncated addition.  `truncIter n A B j` is
`(A + j • B) ∩ [0,n]`. -/
def truncIter (n : ℕ) (A B : Finset ℕ) : ℕ → Finset ℕ
  | 0 => A.filter (· ≤ n)
  | j + 1 => truncAdd n (truncIter n A B j) B

@[simp] lemma truncIter_zero (n : ℕ) (A B : Finset ℕ) :
    truncIter n A B 0 = A.filter (· ≤ n) := rfl

@[simp] lemma truncIter_succ (n : ℕ) (A B : Finset ℕ) (j : ℕ) :
    truncIter n A B (j + 1) = truncAdd n (truncIter n A B j) B := rfl

lemma truncIter_subset_range (n : ℕ) (A B : Finset ℕ) (j : ℕ) :
    truncIter n A B j ⊆ range (n + 1) := by
  induction j with
  | zero => simp [subset_iff]
  | succ j ih =>
      intro x hx
      obtain ⟨a, ha, b, hb, hab, hxn⟩ := mem_truncAdd.1 hx
      exact Finset.mem_range.2 (Nat.lt_succ_of_le hxn)

/-! ## Finite relation counting

The finite commutative-graph argument is most conveniently expressed in
terms of images, inverse images, and degrees of bipartite relations. -/

section RelationCounting

variable {ι : Type*} [DecidableEq ι]

/-- Image of a finite set through a relation, restricted to a prescribed
finite codomain. -/
def relImage (r : ι → ι → Prop) [DecidableRel r] (S T : Finset ι) : Finset ι :=
  T.filter fun y => ∃ x ∈ S, r x y

/-- Inverse image of a finite set through a relation, restricted to a
prescribed finite domain. -/
def relPreimage (r : ι → ι → Prop) [DecidableRel r] (S T : Finset ι) : Finset ι :=
  S.filter fun x => ∃ y ∈ T, r x y

omit [DecidableEq ι] in
@[simp] lemma mem_relImage {r : ι → ι → Prop} [DecidableRel r] {S T : Finset ι} {y : ι} :
    y ∈ relImage r S T ↔ y ∈ T ∧ ∃ x ∈ S, r x y := by
  classical
  simp [relImage]

omit [DecidableEq ι] in
@[simp] lemma mem_relPreimage {r : ι → ι → Prop} [DecidableRel r]
    {S T : Finset ι} {x : ι} :
    x ∈ relPreimage r S T ↔ x ∈ S ∧ ∃ y ∈ T, r x y := by
  classical
  simp [relPreimage]

omit [DecidableEq ι] in
lemma relImage_mono_left {r : ι → ι → Prop} [DecidableRel r]
    {S S' T : Finset ι} (h : S ⊆ S') : relImage r S T ⊆ relImage r S' T := by
  classical
  intro y hy
  obtain ⟨hyT, x, hx, hxy⟩ := mem_relImage.1 hy
  exact mem_relImage.2 ⟨hyT, x, h hx, hxy⟩

omit [DecidableEq ι] in
lemma relPreimage_mono_right {r : ι → ι → Prop} [DecidableRel r]
    {S T T' : Finset ι} (h : T ⊆ T') : relPreimage r S T ⊆ relPreimage r S T' := by
  classical
  intro x hx
  obtain ⟨hxS, y, hy, hxy⟩ := mem_relPreimage.1 hx
  exact mem_relPreimage.2 ⟨hxS, y, h hy, hxy⟩

omit [DecidableEq ι] in
/-- The layer-cake identity for a bounded natural-valued function on a
finset: the sum of its values is the sum of the cardinalities of its strict
superlevel sets. -/
lemma sum_card_filter_lt_eq_sum (S : Finset ι) (d : ι → ℕ) (M : ℕ)
    (hd : ∀ x ∈ S, d x ≤ M) :
    (∑ j ∈ range M, #{x ∈ S | j < d x}) = ∑ x ∈ S, d x := by
  classical
  change (∑ j ∈ range M, #(S.bipartiteAbove (fun j x => j < d x) j)) = _
  rw [sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow]
  apply sum_congr rfl
  intro x hx
  have hfilter :
      (range M).bipartiteBelow (fun j x => j < d x) x = range (d x) := by
    ext j
    simp only [bipartiteBelow, mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.trans_le (hd x hx), h⟩
  rw [hfilter, card_range]

omit [DecidableEq ι] in
/-- The level-two counting lemma in Petridis's weighted-separator proof.
The two expansion assumptions come from minimality of a middle-layer
separator.  The two degree assumptions are the numerical consequences of
the upward and downward commuting-square matchings. -/
lemma levelTwo_middle_card_eq
    (U₀ U₁ U₂ : Finset ι) (r₀₁ r₁₂ : ι → ι → Prop)
    [DecidableRel r₀₁] [DecidableRel r₁₂] (C : ℝ) (hC : 0 < C)
    (hforward : ∀ S ⊆ U₁, C * (#S : ℝ) ≤ #(relImage r₁₂ S U₂))
    (hbackward : ∀ S ⊆ U₁, (#S : ℝ) ≤ C * #(relPreimage r₀₁ U₀ S))
    (hdown : ∀ u ∈ U₁, ∀ v ∈ U₂, r₁₂ u v →
      #(U₀.bipartiteBelow r₀₁ u) ≤ #(U₁.bipartiteBelow r₁₂ v))
    (hup : ∀ v ∈ U₀, ∀ u ∈ U₁, r₀₁ v u →
      #(U₂.bipartiteAbove r₁₂ u) ≤ #(U₁.bipartiteAbove r₀₁ v))
    (hU₀ : ∀ v ∈ U₀, (U₁.bipartiteAbove r₀₁ v).Nonempty)
    (hU₁ : ∀ u ∈ U₁, (U₂.bipartiteAbove r₁₂ u).Nonempty) :
    C * (#U₀ : ℝ) = #U₁ := by
  classical
  let M := #U₀ + #U₁ + #U₂ + 1
  let din₁ : ι → ℕ := fun u => #(U₀.bipartiteBelow r₀₁ u)
  let din₂ : ι → ℕ := fun v => #(U₁.bipartiteBelow r₁₂ v)
  let dout₀ : ι → ℕ := fun v => #(U₁.bipartiteAbove r₀₁ v)
  let dout₁ : ι → ℕ := fun u => #(U₂.bipartiteAbove r₁₂ u)
  have hM0 : ∀ v ∈ U₀, dout₀ v ≤ M := by
    intro v hv
    calc
      dout₀ v ≤ #U₁ := Finset.card_le_card (filter_subset _ _)
      _ ≤ #U₀ + #U₁ := Nat.le_add_left _ _
      _ ≤ M := by
        dsimp [M]
        simp [Nat.add_assoc]
  have hM1out : ∀ u ∈ U₁, dout₁ u ≤ M := by
    intro u hu
    calc
      dout₁ u ≤ #U₂ := Finset.card_le_card (filter_subset _ _)
      _ ≤ #U₀ + #U₁ + #U₂ := Nat.le_add_left _ _
      _ ≤ M := by exact Nat.le_add_right _ 1
  have hM1in : ∀ u ∈ U₁, din₁ u ≤ M := by
    intro u hu
    calc
      din₁ u ≤ #U₀ := Finset.card_le_card (filter_subset _ _)
      _ ≤ M := by
        dsimp [M]
        simp [Nat.add_assoc]
  have hM2 : ∀ v ∈ U₂, din₂ v ≤ M := by
    intro v hv
    calc
      din₂ v ≤ #U₁ := Finset.card_le_card (filter_subset _ _)
      _ ≤ #U₀ + #U₁ := Nat.le_add_left _ _
      _ ≤ M := by
        dsimp [M]
        simp [Nat.add_assoc]
  have hforward_threshold : ∀ j < M,
      C * (#{u ∈ U₁ | j < din₁ u} : ℝ) ≤ #{v ∈ U₂ | j < din₂ v} := by
    intro j hj
    let S := U₁.filter fun u => j < din₁ u
    let T := U₂.filter fun v => j < din₂ v
    have himage : relImage r₁₂ S U₂ ⊆ T := by
      intro v hv
      obtain ⟨hvU₂, u, huS, huv⟩ := mem_relImage.1 hv
      have hu := mem_filter.1 huS
      exact mem_filter.2 ⟨hvU₂, hu.2.trans_le (hdown u hu.1 v hvU₂ huv)⟩
    exact (hforward S (filter_subset _ _)).trans
      (by exact_mod_cast Finset.card_le_card himage)
  have hbackward_threshold : ∀ j < M,
      (#{u ∈ U₁ | j < dout₁ u} : ℝ) ≤
        C * #{v ∈ U₀ | j < dout₀ v} := by
    intro j hj
    let S := U₁.filter fun u => j < dout₁ u
    let T := U₀.filter fun v => j < dout₀ v
    have hpreimage : relPreimage r₀₁ U₀ S ⊆ T := by
      intro v hv
      obtain ⟨hvU₀, u, huS, hvu⟩ := mem_relPreimage.1 hv
      have hu := mem_filter.1 huS
      exact mem_filter.2 ⟨hvU₀, hu.2.trans_le (hup v hvU₀ u hu.1 hvu)⟩
    calc
      (#S : ℝ) ≤ C * #(relPreimage r₀₁ U₀ S) :=
        hbackward S (filter_subset _ _)
      _ ≤ C * #T := mul_le_mul_of_nonneg_left
        (by exact_mod_cast Finset.card_le_card hpreimage) hC.le
  have hedge_forward :
      C * (∑ u ∈ U₁, (din₁ u : ℝ)) ≤ ∑ v ∈ U₂, (din₂ v : ℝ) := by
    have hsum₁ :
        (∑ j ∈ range M, (#{u ∈ U₁ | j < din₁ u} : ℝ)) =
          ∑ u ∈ U₁, (din₁ u : ℝ) := by
      exact_mod_cast sum_card_filter_lt_eq_sum U₁ din₁ M hM1in
    have hsum₂ :
        (∑ j ∈ range M, (#{v ∈ U₂ | j < din₂ v} : ℝ)) =
          ∑ v ∈ U₂, (din₂ v : ℝ) := by
      exact_mod_cast sum_card_filter_lt_eq_sum U₂ din₂ M hM2
    rw [← hsum₁, ← hsum₂, mul_sum]
    exact sum_le_sum fun j hj => hforward_threshold j (mem_range.1 hj)
  have hedge_backward :
      (∑ u ∈ U₁, (dout₁ u : ℝ)) ≤ C * ∑ v ∈ U₀, (dout₀ v : ℝ) := by
    have hsum₁ :
        (∑ j ∈ range M, (#{u ∈ U₁ | j < dout₁ u} : ℝ)) =
          ∑ u ∈ U₁, (dout₁ u : ℝ) := by
      exact_mod_cast sum_card_filter_lt_eq_sum U₁ dout₁ M hM1out
    have hsum₀ :
        (∑ j ∈ range M, (#{v ∈ U₀ | j < dout₀ v} : ℝ)) =
          ∑ v ∈ U₀, (dout₀ v : ℝ) := by
      exact_mod_cast sum_card_filter_lt_eq_sum U₀ dout₀ M hM0
    rw [← hsum₁, ← hsum₀, mul_sum]
    exact sum_le_sum fun j hj => hbackward_threshold j (mem_range.1 hj)
  have hedges₀₁ : (∑ u ∈ U₁, (din₁ u : ℝ)) = ∑ v ∈ U₀, (dout₀ v : ℝ) := by
    exact_mod_cast (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := U₀) (t := U₁) (r := r₀₁)).symm
  have hedges₁₂ : (∑ v ∈ U₂, (din₂ v : ℝ)) = ∑ u ∈ U₁, (dout₁ u : ℝ) := by
    exact_mod_cast (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := U₁) (t := U₂) (r := r₁₂)).symm
  have hedge_eq : (∑ u ∈ U₁, (dout₁ u : ℝ)) =
      C * ∑ v ∈ U₀, (dout₀ v : ℝ) := by
    apply le_antisymm hedge_backward
    calc
      C * ∑ v ∈ U₀, (dout₀ v : ℝ) = C * ∑ u ∈ U₁, (din₁ u : ℝ) := by rw [hedges₀₁]
      _ ≤ ∑ v ∈ U₂, (din₂ v : ℝ) := hedge_forward
      _ = ∑ u ∈ U₁, (dout₁ u : ℝ) := hedges₁₂
  let S₀ := U₁.filter fun u => 0 < dout₁ u
  let T₀ := U₀.filter fun v => 0 < dout₀ v
  have hS₀ : S₀ = U₁ := filter_eq_self.2 fun u hu => (hU₁ u hu).card_pos
  have hT₀ : T₀ = U₀ := filter_eq_self.2 fun v hv => (hU₀ v hv).card_pos
  have hzero : (#S₀ : ℝ) ≤ C * #T₀ := hbackward_threshold 0 (by simp [M])
  have hrest :
      (∑ j ∈ (range M).erase 0, (#{u ∈ U₁ | j < dout₁ u} : ℝ)) ≤
        C * ∑ j ∈ (range M).erase 0, (#{v ∈ U₀ | j < dout₀ v} : ℝ) := by
    rw [mul_sum]
    exact sum_le_sum fun j hj =>
      hbackward_threshold j (mem_range.1 (mem_of_mem_erase hj))
  have hsumU₁ :
      (∑ j ∈ range M, (#{u ∈ U₁ | j < dout₁ u} : ℝ)) =
        ∑ u ∈ U₁, dout₁ u := by
    exact_mod_cast sum_card_filter_lt_eq_sum U₁ dout₁ M hM1out
  have hsumU₀ :
      (∑ j ∈ range M, (#{v ∈ U₀ | j < dout₀ v} : ℝ)) =
        ∑ v ∈ U₀, dout₀ v := by
    exact_mod_cast sum_card_filter_lt_eq_sum U₀ dout₀ M hM0
  have hzero_eq : (#S₀ : ℝ) = C * #T₀ := by
    have h0M : 0 ∈ range M := by simp [M]
    rw [← insert_erase h0M, sum_insert (by simp)] at hsumU₁ hsumU₀
    push_cast at hsumU₁ hsumU₀
    have hraw : (#{u ∈ U₁ | 0 < dout₁ u} : ℝ) =
        C * #{v ∈ U₀ | 0 < dout₀ v} := by
      nlinarith
    simpa only [S₀, T₀] using hraw
  rw [hS₀, hT₀] at hzero_eq
  exact hzero_eq.symm

end RelationCounting

/-! ## Truncated addition paths and separators -/

/-- A single edge in the addition graph, with the endpoint retained by the
cutoff. -/
def AddEdge (n : ℕ) (B : Finset ℕ) (x y : ℕ) : Prop :=
  ∃ b ∈ B, x + b = y ∧ y ≤ n

@[simp] lemma addEdge_iff {n : ℕ} {B : Finset ℕ} {x y : ℕ} :
    AddEdge n B x y ↔ ∃ b ∈ B, x + b = y ∧ y ≤ n := Iff.rfl

/-- A length-`h` path in the truncated addition graph generated from `X`.
The function is intentionally defined on all naturals; only its first
`h + 1` values are constrained.  This makes path splicing arithmetically
transparent. -/
def IsTruncPath (n h : ℕ) (X B : Finset ℕ) (p : ℕ → ℕ) : Prop :=
  p 0 ∈ X ∧
    (∀ i ≤ h, p i ≤ n) ∧
    ∀ i < h, AddEdge n B (p i) (p (i + 1))

/-- Membership in an iterated truncated sumset is equivalent to being the
endpoint of a path in the truncated addition graph. -/
lemma mem_truncIter_iff_exists_path {n i x : ℕ} {X B : Finset ℕ} :
    x ∈ truncIter n X B i ↔
      ∃ p : ℕ → ℕ, IsTruncPath n i X B p ∧ p i = x := by
  induction i generalizing x with
  | zero =>
      constructor
      · intro hx
        obtain ⟨hxX, hxn⟩ := mem_filter.1 hx
        exact ⟨fun _ => x, ⟨hxX, (by intro j hj; simpa using hxn),
          (by intro j hj; omega)⟩, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact mem_filter.2 ⟨hp.1, hp.2.1 0 (by omega)⟩
  | succ i ih =>
      rw [truncIter_succ, mem_truncAdd]
      constructor
      · rintro ⟨y, hy, b, hb, hybx, hxn⟩
        obtain ⟨p, hp, hpi⟩ := ih.1 hy
        let q : ℕ → ℕ := fun t => if t ≤ i then p t else x
        refine ⟨q, ?_, by simp [q]⟩
        refine ⟨by simpa [q] using hp.1, ?_, ?_⟩
        · intro t ht
          by_cases hti : t ≤ i
          · simpa [q, hti] using hp.2.1 t hti
          · simp [q, hti, hxn]
        · intro t ht
          by_cases hti : t < i
          · have hti' : t ≤ i := hti.le
            have hsucc : t + 1 ≤ i := by omega
            simpa [q, hti', hsucc] using hp.2.2 t hti
          · have htiEq : t = i := by omega
            subst t
            simpa [q, hpi] using (show AddEdge n B y x from
              ⟨b, hb, hybx, hxn⟩)
      · rintro ⟨p, hp, hplast⟩
        have hp' : IsTruncPath n i X B p :=
          ⟨hp.1, (fun t ht => hp.2.1 t (by omega)),
            fun t ht => hp.2.2 t (by omega)⟩
        have hprev : p i ∈ truncIter n X B i := ih.2 ⟨p, hp', rfl⟩
        obtain ⟨b, hb, hib, hxn⟩ := hp.2.2 i (by omega)
        exact ⟨p i, hprev, b, hb, hib.trans hplast, hplast ▸ hxn⟩

/-- A finite set of level-tagged vertices separates the bottom from level
`h` when it meets every truncated path. -/
def IsSeparator (n h : ℕ) (X B : Finset ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ p, IsTruncPath n h X B p → ∃ i ≤ h, (i, p i) ∈ S

/-- The vertices of a tagged set lying in one prescribed level. -/
def cutLayer (n : ℕ) (S : Finset (ℕ × ℕ)) (i : ℕ) : Finset ℕ :=
  (range (n + 1)).filter fun x => (i, x) ∈ S

/-- Tag all vertices of a finite set with a prescribed level. -/
def atLayer (i : ℕ) (T : Finset ℕ) : Finset (ℕ × ℕ) :=
  T.map ⟨fun x => (i, x), fun _ _ h => Prod.mk.inj h |>.2⟩

@[simp] lemma mem_cutLayer {n i : ℕ} {S : Finset (ℕ × ℕ)} {x : ℕ} :
    x ∈ cutLayer n S i ↔ x ≤ n ∧ (i, x) ∈ S := by
  simp [cutLayer]

@[simp] lemma mem_atLayer {i : ℕ} {T : Finset ℕ} {q : ℕ × ℕ} :
    q ∈ atLayer i T ↔ ∃ x ∈ T, (i, x) = q := by
  simp only [atLayer, mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

@[simp] lemma pair_mem_atLayer {i x : ℕ} {T : Finset ℕ} :
    (i, x) ∈ atLayer i T ↔ x ∈ T := by
  constructor
  · intro h
    obtain ⟨y, hy, heq⟩ := mem_atLayer.1 h
    have hyx : y = x := congrArg Prod.snd heq
    simpa [hyx] using hy
  · exact fun h => mem_atLayer.2 ⟨x, h, rfl⟩

lemma atLayer_subset_iff {i : ℕ} {T : Finset ℕ} {S : Finset (ℕ × ℕ)} :
    atLayer i T ⊆ S ↔ ∀ x ∈ T, (i, x) ∈ S := by
  constructor
  · intro h x hx
    exact h (pair_mem_atLayer.2 hx)
  · rintro h q hq
    obtain ⟨x, hx, rfl⟩ := mem_atLayer.1 hq
    exact h x hx

/-- Splicing a prefix and suffix across a commuting square produces another
valid path.  Hence a separator avoided by the prefix and suffix must contain
the square's middle vertex. -/
lemma splice_middle_mem {n h j : ℕ} {X B : Finset ℕ} {S : Finset (ℕ × ℕ)}
    (hj₀ : 0 < j) (hsep : IsSeparator n h X B S)
    {p₀ p₂ : ℕ → ℕ} (hp₀ : IsTruncPath n h X B p₀)
    (hp₂ : IsTruncPath n h X B p₂)
    {x x' v : ℕ} (hp₀x : p₀ (j - 1) = x) (hp₂v : p₂ (j + 1) = v)
    (hprefix : ∀ i < j, (i, p₀ i) ∉ S)
    (hsuffix : ∀ i, j < i → i ≤ h → (i, p₂ i) ∉ S)
    (hxx' : AddEdge n B x x') (hx'v : AddEdge n B x' v) :
    (j, x') ∈ S := by
  obtain ⟨b₀, hb₀, hxb₀, hx'n⟩ := hxx'
  have hxx' : AddEdge n B x x' := ⟨b₀, hb₀, hxb₀, hx'n⟩
  let p : ℕ → ℕ := fun i => if i < j then p₀ i else if i = j then x' else p₂ i
  have hp : IsTruncPath n h X B p := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [p, if_pos hj₀] using hp₀.1
    · intro i hi
      by_cases hij : i < j
      · simpa [p, hij] using hp₀.2.1 i hi
      by_cases hij' : i = j
      · subst i
        simpa [p] using hx'n
      · have hji : j < i := by omega
        simpa [p, hij, hij'] using hp₂.2.1 i hi
    · intro i hi
      by_cases hsucc : i + 1 < j
      · have hi' : i < j := by omega
        simpa [p, hi', hsucc, show i + 1 ≠ j by omega] using hp₀.2.2 i hi
      by_cases heq : i + 1 = j
      · have hi' : i < j := by omega
        have hip : p i = x := by
          simp only [p, if_pos hi']
          simpa [show i = j - 1 by omega] using hp₀x
        have his : p (i + 1) = x' := by simp [p, heq]
        simpa [hip, his] using hxx'
      by_cases hij : i = j
      · have hi_not : ¬i < j := by omega
        have hip : p i = x' := by simp [p, hij]
        have his : p (i + 1) = v := by simp [p, hp₂v, hij]
        simpa [hip, his] using hx'v
      · have hji : j < i := by omega
        have hi_not : ¬i < j := by omega
        have his_not : ¬i + 1 < j := by omega
        have his_ne : i + 1 ≠ j := by omega
        simpa [p, hi_not, hij, his_not, his_ne] using hp₂.2.2 i hi
  obtain ⟨i, hi, hiS⟩ := hsep p hp
  by_cases hij : i < j
  · exact False.elim (hprefix i hij (by simpa [p, hij] using hiS))
  by_cases hji : j < i
  · have hi_not : ¬i < j := by omega
    have hi_ne : i ≠ j := by omega
    exact False.elim (hsuffix i hji hi (by simpa [p, hi_not, hi_ne] using hiS))
  · have hij' : i = j := by omega
    subst i
    simpa [p] using hiS

/-- Vertices which occur at level `i` on a full path avoiding the cut up to
and including level `i`. -/
def prefixSet (n h : ℕ) (X B : Finset ℕ) (S : Finset (ℕ × ℕ)) (i : ℕ) : Finset ℕ :=
  (range (n + 1)).filter fun x =>
    ∃ p, IsTruncPath n h X B p ∧ p i = x ∧ ∀ t ≤ i, (t, p t) ∉ S

/-- Vertices which occur at level `i` on a full path avoiding the cut from
level `i` through the top. -/
def suffixSet (n h : ℕ) (X B : Finset ℕ) (S : Finset (ℕ × ℕ)) (i : ℕ) : Finset ℕ :=
  (range (n + 1)).filter fun x =>
    ∃ p, IsTruncPath n h X B p ∧ p i = x ∧
      ∀ t, i ≤ t → t ≤ h → (t, p t) ∉ S

@[simp] lemma mem_prefixSet {n h : ℕ} {X B : Finset ℕ} {S : Finset (ℕ × ℕ)}
    {i x : ℕ} :
    x ∈ prefixSet n h X B S i ↔
      x ≤ n ∧ ∃ p, IsTruncPath n h X B p ∧ p i = x ∧
        ∀ t ≤ i, (t, p t) ∉ S := by
  simp [prefixSet]

@[simp] lemma mem_suffixSet {n h : ℕ} {X B : Finset ℕ} {S : Finset (ℕ × ℕ)}
    {i x : ℕ} :
    x ∈ suffixSet n h X B S i ↔
      x ≤ n ∧ ∃ p, IsTruncPath n h X B p ∧ p i = x ∧
        ∀ t, i ≤ t → t ≤ h → (t, p t) ∉ S := by
  simp [suffixSet]

/-- Inclusion-minimality of a separator makes every one of its vertices
essential: after deleting that vertex there is a path which meets the old
separator exactly there. -/
lemma essential_path_of_erase_not_separator
    {n h j u : ℕ} {X B : Finset ℕ} {S : Finset (ℕ × ℕ)}
    (hsep : IsSeparator n h X B S)
    (hnot : ¬IsSeparator n h X B (S.erase (j, u))) :
    ∃ p, IsTruncPath n h X B p ∧ p j = u ∧
      ∀ i ≤ h, i ≠ j → (i, p i) ∉ S := by
  rw [IsSeparator] at hnot
  push Not at hnot
  obtain ⟨p, hp, havoid⟩ := hnot
  obtain ⟨i, hi, hiS⟩ := hsep p hp
  have hiEq : (i, p i) = (j, u) := by
    by_contra hne
    exact havoid i hi (mem_erase.2 ⟨hne, hiS⟩)
  have hij : i = j := congrArg Prod.fst hiEq
  have hpu : p i = u := congrArg Prod.snd hiEq
  refine ⟨p, hp, ?_, ?_⟩
  · simpa [← hij] using hpu
  · intro t ht htj htS
    apply havoid t ht
    exact mem_erase.2 ⟨by
      intro heq
      exact htj (congrArg Prod.fst heq), htS⟩

/-- The middle layer, reachable predecessor channel, and co-reachable
successor channel associated to an interior cut layer. -/
def separatorMiddle (n j : ℕ) (S : Finset (ℕ × ℕ)) : Finset ℕ :=
  cutLayer n S j

def separatorLower (n h j : ℕ) (X B : Finset ℕ) (S : Finset (ℕ × ℕ)) : Finset ℕ :=
  relPreimage (AddEdge n B) (prefixSet n h X B S (j - 1)) (separatorMiddle n j S)

def separatorUpper (n h j : ℕ) (X B : Finset ℕ) (S : Finset (ℕ × ℕ)) : Finset ℕ :=
  relImage (AddEdge n B) (separatorMiddle n j S) (suffixSet n h X B S (j + 1))

/-- Replace part of an interior separator layer by its forward image in the
co-reachable successor channel. -/
def forwardReplacement (n h j : ℕ) (X B : Finset ℕ) (S : Finset (ℕ × ℕ))
    (Q : Finset ℕ) : Finset (ℕ × ℕ) :=
  (S \ atLayer j Q) ∪
    atLayer (j + 1) (relImage (AddEdge n B) Q (separatorUpper n h j X B S))

/-- Replace part of an interior separator layer by its inverse image in the
reachable predecessor channel. -/
def backwardReplacement (n h j : ℕ) (X B : Finset ℕ) (S : Finset (ℕ × ℕ))
    (Q : Finset ℕ) : Finset (ℕ × ℕ) :=
  (S \ atLayer j Q) ∪
    atLayer (j - 1) (relPreimage (AddEdge n B) (separatorLower n h j X B S) Q)

lemma forwardReplacement_isSeparator
    {n h j : ℕ} {X B : Finset ℕ} {S : Finset (ℕ × ℕ)}
    (hjh : j < h) (hsep : IsSeparator n h X B S)
    {Q : Finset ℕ} (hQ : Q ⊆ separatorMiddle n j S) :
    IsSeparator n h X B (forwardReplacement n h j X B S Q) := by
  intro p hp
  by_contra hhit
  push Not at hhit
  obtain ⟨i, hi, hiS⟩ := hsep p hp
  have hij : i = j := by
    by_contra hij
    have hnotlayer : (i, p i) ∉ atLayer j Q := by
      intro hmem
      obtain ⟨x, hx, heq⟩ := mem_atLayer.1 hmem
      exact hij (congrArg Prod.fst heq).symm
    exact hhit i hi (by
      apply Finset.mem_union_left
      exact mem_sdiff.2 ⟨hiS, hnotlayer⟩)
  subst i
  have hpjQ : p j ∈ Q := by
    by_contra hpjQ
    exact hhit j hi (by
      apply Finset.mem_union_left
      exact mem_sdiff.2 ⟨hiS, fun h => hpjQ (pair_mem_atLayer.1 h)⟩)
  have hstep : AddEdge n B (p j) (p (j + 1)) := hp.2.2 j hjh
  have hsuccSuffix : p (j + 1) ∈ suffixSet n h X B S (j + 1) := by
    refine mem_suffixSet.2 ⟨hp.2.1 (j + 1) (by omega), p, hp, rfl, ?_⟩
    intro t ht hth htS
    have htj : t ≠ j := by omega
    have hnotlayer : (t, p t) ∉ atLayer j Q := by
      intro hmem
      obtain ⟨x, hx, heq⟩ := mem_atLayer.1 hmem
      exact htj (congrArg Prod.fst heq).symm
    exact hhit t hth (by
      apply Finset.mem_union_left
      exact mem_sdiff.2 ⟨htS, hnotlayer⟩)
  have hsuccUpper : p (j + 1) ∈ separatorUpper n h j X B S := by
    rw [separatorUpper]
    exact mem_relImage.2 ⟨hsuccSuffix, p j, hQ hpjQ, hstep⟩
  have hsuccImage : p (j + 1) ∈
      relImage (AddEdge n B) Q (separatorUpper n h j X B S) :=
    mem_relImage.2 ⟨hsuccUpper, p j, hpjQ, hstep⟩
  exact hhit (j + 1) (by omega) (by
    apply Finset.mem_union_right
    exact pair_mem_atLayer.2 hsuccImage)

lemma backwardReplacement_isSeparator
    {n h j : ℕ} {X B : Finset ℕ} {S : Finset (ℕ × ℕ)}
    (hj₀ : 0 < j) (hsep : IsSeparator n h X B S)
    {Q : Finset ℕ} (hQ : Q ⊆ separatorMiddle n j S) :
    IsSeparator n h X B (backwardReplacement n h j X B S Q) := by
  intro p hp
  by_contra hhit
  push Not at hhit
  obtain ⟨i, hi, hiS⟩ := hsep p hp
  have hij : i = j := by
    by_contra hij
    have hnotlayer : (i, p i) ∉ atLayer j Q := by
      intro hmem
      obtain ⟨x, hx, heq⟩ := mem_atLayer.1 hmem
      exact hij (congrArg Prod.fst heq).symm
    exact hhit i hi (by
      apply Finset.mem_union_left
      exact mem_sdiff.2 ⟨hiS, hnotlayer⟩)
  subst i
  have hpjQ : p j ∈ Q := by
    by_contra hpjQ
    exact hhit j hi (by
      apply Finset.mem_union_left
      exact mem_sdiff.2 ⟨hiS, fun h => hpjQ (pair_mem_atLayer.1 h)⟩)
  have hpredPrefix : p (j - 1) ∈ prefixSet n h X B S (j - 1) := by
    refine mem_prefixSet.2 ⟨hp.2.1 (j - 1) (by omega), p, hp, rfl, ?_⟩
    intro t ht htS
    have htj : t ≠ j := by omega
    have hnotlayer : (t, p t) ∉ atLayer j Q := by
      intro hmem
      obtain ⟨x, hx, heq⟩ := mem_atLayer.1 hmem
      exact htj (congrArg Prod.fst heq).symm
    exact hhit t (ht.trans (by omega)) (by
      apply Finset.mem_union_left
      exact mem_sdiff.2 ⟨htS, hnotlayer⟩)
  have hstep : AddEdge n B (p (j - 1)) (p j) := by
    simpa [show j - 1 + 1 = j by omega] using hp.2.2 (j - 1) (by omega)
  have hpredLower : p (j - 1) ∈ separatorLower n h j X B S := by
    rw [separatorLower]
    exact mem_relPreimage.2 ⟨hpredPrefix, p j, hQ hpjQ, hstep⟩
  have hpredImage : p (j - 1) ∈
      relPreimage (AddEdge n B) (separatorLower n h j X B S) Q :=
    mem_relPreimage.2 ⟨hpredLower, p j, hpjQ, hstep⟩
  exact hhit (j - 1) (by omega) (by
    apply Finset.mem_union_right
    exact pair_mem_atLayer.2 hpredImage)

/-! ### Weighted separators -/

/-- All possible tagged vertices of a height-`h`, cutoff-`n` graph. -/
def vertexGrid (n h : ℕ) : Finset (ℕ × ℕ) :=
  (range (h + 1)).product (range (n + 1))

/-- Integer-power version of Petridis's separator weight.  Multiplying the
usual level-`i` weight `C⁻ⁱ` by `Cʰ` gives `C^(h-i)`, avoiding negative
real powers. -/
def separatorWeight (C : ℝ) (h : ℕ) (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ q ∈ S, C ^ (h - q.1)

/-- A secondary natural-valued rank used to choose, among minimum-weight
separators, one with no interior vertices. -/
def separatorRank (S : Finset (ℕ × ℕ)) : ℕ :=
  ∑ q ∈ S, q.1

@[simp] lemma card_atLayer (i : ℕ) (T : Finset ℕ) : #(atLayer i T) = #T := by
  simp [atLayer]

lemma separatorWeight_nonneg {C : ℝ} (hC : 0 ≤ C) (h : ℕ) (S : Finset (ℕ × ℕ)) :
    0 ≤ separatorWeight C h S := by
  exact Finset.sum_nonneg fun _ _ => pow_nonneg hC _

@[simp] lemma separatorWeight_atLayer (C : ℝ) (h i : ℕ) (T : Finset ℕ) :
    separatorWeight C h (atLayer i T) = (#T : ℝ) * C ^ (h - i) := by
  rw [separatorWeight, atLayer, sum_map]
  change (∑ _x ∈ T, C ^ (h - i)) = (#T : ℝ) * C ^ (h - i)
  simp

@[simp] lemma separatorRank_atLayer (i : ℕ) (T : Finset ℕ) :
    separatorRank (atLayer i T) = #T * i := by
  rw [separatorRank, atLayer, sum_map]
  change (∑ _x ∈ T, i) = #T * i
  simp [mul_comm]

lemma sum_union_le_add_sum {α : Type*} [DecidableEq α] (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) (A D : Finset α) :
    ∑ x ∈ A ∪ D, f x ≤ (∑ x ∈ A, f x) + ∑ x ∈ D, f x := by
  have hun : A ∪ D = A ∪ (D \ A) := by
    exact (union_sdiff_self_eq_union (s := A) (t := D)).symm
  have hdis : Disjoint A (D \ A) := by
    rw [Finset.disjoint_left]
    intro x hxA hxD
    exact (mem_sdiff.1 hxD).2 hxA
  rw [hun, sum_union hdis]
  exact add_le_add_right
    (Finset.sum_le_sum_of_subset_of_nonneg (f := f)
      (s := D \ A) (t := D) sdiff_subset (fun _ _ _ => hf _)) _

lemma separatorWeight_union_le {C : ℝ} (hC : 0 ≤ C) (h : ℕ)
    (A D : Finset (ℕ × ℕ)) :
    separatorWeight C h (A ∪ D) ≤ separatorWeight C h A + separatorWeight C h D := by
  exact sum_union_le_add_sum (fun q => C ^ (h - q.1)) (fun _ => pow_nonneg hC _) A D

lemma separatorRank_union_le (A D : Finset (ℕ × ℕ)) :
    separatorRank (A ∪ D) ≤ separatorRank A + separatorRank D := by
  exact_mod_cast sum_union_le_add_sum (fun q => (q.1 : ℝ))
    (fun _ => Nat.cast_nonneg _) A D

lemma separatorWeight_sdiff_add {C : ℝ} (h : ℕ)
    {A S : Finset (ℕ × ℕ)} (hAS : A ⊆ S) :
    separatorWeight C h (S \ A) + separatorWeight C h A = separatorWeight C h S := by
  exact Finset.sum_sdiff hAS

lemma separatorRank_sdiff_add {A S : Finset (ℕ × ℕ)} (hAS : A ⊆ S) :
    separatorRank (S \ A) + separatorRank A = separatorRank S := by
  exact Finset.sum_sdiff hAS

lemma separatorWeight_replacement_balance {C : ℝ} (hC : 0 ≤ C) (h : ℕ)
    {A S D : Finset (ℕ × ℕ)} (hAS : A ⊆ S) :
    separatorWeight C h ((S \ A) ∪ D) + separatorWeight C h A ≤
      separatorWeight C h S + separatorWeight C h D := by
  have hu := separatorWeight_union_le hC h (S \ A) D
  have hs := separatorWeight_sdiff_add (C := C) h hAS
  linarith

lemma separatorRank_replacement_balance {A S D : Finset (ℕ × ℕ)} (hAS : A ⊆ S) :
    separatorRank ((S \ A) ∪ D) + separatorRank A ≤
      separatorRank S + separatorRank D := by
  have hu := separatorRank_union_le (S \ A) D
  have hs := separatorRank_sdiff_add hAS
  omega

lemma forwardReplacement_subset_grid
    {n h j : ℕ} {X B : Finset ℕ} {S : Finset (ℕ × ℕ)}
    (hjh : j < h) (hS : S ⊆ vertexGrid n h)
    {Q : Finset ℕ} :
    forwardReplacement n h j X B S Q ⊆ vertexGrid n h := by
  intro q hq
  rcases mem_union.1 hq with hq | hq
  · exact hS (mem_sdiff.1 hq).1
  · obtain ⟨x, hx, rfl⟩ := mem_atLayer.1 hq
    obtain ⟨hxUpper, y, hyQ, hyx⟩ := mem_relImage.1 hx
    obtain ⟨_, _, _, hxn⟩ := hyx
    simp [vertexGrid, hjh, hxn]

lemma backwardReplacement_subset_grid
    {n h j : ℕ} {X B : Finset ℕ} {S : Finset (ℕ × ℕ)}
    (hjh : j ≤ h) (hS : S ⊆ vertexGrid n h)
    {Q : Finset ℕ} :
    backwardReplacement n h j X B S Q ⊆ vertexGrid n h := by
  intro q hq
  rcases mem_union.1 hq with hq | hq
  · exact hS (mem_sdiff.1 hq).1
  · obtain ⟨x, hx, rfl⟩ := mem_atLayer.1 hq
    obtain ⟨hxLower, y, hyQ, hxy⟩ := mem_relPreimage.1 hx
    obtain ⟨hxPrefix, z, hz, hxz⟩ := mem_relPreimage.1 hxLower
    have hxn : x ≤ n := by
      exact (mem_prefixSet (n := n) (h := h) (X := X) (B := B)
        (S := S) (i := j - 1) (x := x)).1 hxPrefix |>.1
    simp [vertexGrid, hxn]
    omega

lemma separator_channel_down_degree
    {n h j : ℕ} {X B : Finset ℕ} {S : Finset (ℕ × ℕ)}
    (hj₀ : 0 < j) (hsep : IsSeparator n h X B S)
    {u v : ℕ} (hv : v ∈ separatorUpper n h j X B S)
    (huv : AddEdge n B u v) :
    #((separatorLower n h j X B S).bipartiteBelow (AddEdge n B) u) ≤
      #((separatorMiddle n j S).bipartiteBelow (AddEdge n B) v) := by
  obtain ⟨b, hbB, hub, hvn⟩ := huv
  let f : ℕ → ℕ := fun x => x + b
  apply card_le_card_of_injOn f
  · intro x hx
    obtain ⟨hxLower, hxu⟩ := (mem_bipartiteBelow (AddEdge n B)).1 hx
    obtain ⟨hxPrefix, _, _, _⟩ := mem_relPreimage.1 hxLower
    obtain ⟨hxn, p₀, hp₀, hp₀x, hp₀avoid⟩ := mem_prefixSet.1 hxPrefix
    obtain ⟨hvSuffix, _, _, _⟩ := mem_relImage.1 hv
    obtain ⟨_, p₂, hp₂, hp₂v, hp₂avoid⟩ := mem_suffixSet.1 hvSuffix
    obtain ⟨c, hcB, hxc, hun⟩ := hxu
    have hfxv : f x + c = v := by
      dsimp [f]
      omega
    have hfxn : f x ≤ n := by omega
    have hxff : AddEdge n B x (f x) := ⟨b, hbB, rfl, hfxn⟩
    have hfxvEdge : AddEdge n B (f x) v := ⟨c, hcB, hfxv, hvn⟩
    have hfxS : (j, f x) ∈ S := splice_middle_mem hj₀ hsep hp₀ hp₂
      hp₀x hp₂v (fun i hi => hp₀avoid i (by omega))
      (fun i hji hih => hp₂avoid i (by omega) hih) hxff hfxvEdge
    exact (mem_bipartiteBelow (AddEdge n B)).2
      ⟨mem_cutLayer.2 ⟨hfxn, hfxS⟩, hfxvEdge⟩
  · intro x₁ hx₁ x₂ hx₂ hfx
    exact Nat.add_right_cancel hfx

lemma separator_channel_up_degree
    {n h j : ℕ} {X B : Finset ℕ} {S : Finset (ℕ × ℕ)}
    (hj₀ : 0 < j) (hsep : IsSeparator n h X B S)
    {v u : ℕ} (hv : v ∈ separatorLower n h j X B S)
    (hvu : AddEdge n B v u) :
    #((separatorUpper n h j X B S).bipartiteAbove (AddEdge n B) u) ≤
      #((separatorMiddle n j S).bipartiteAbove (AddEdge n B) v) := by
  obtain ⟨c, hcB, hvc, hun⟩ := hvu
  let f : ℕ → ℕ := fun w => v + (w - u)
  apply card_le_card_of_injOn f
  · intro w hw
    obtain ⟨hwUpper, huw⟩ := (mem_bipartiteAbove (AddEdge n B)).1 hw
    obtain ⟨hvPrefix, _, _, _⟩ := mem_relPreimage.1 hv
    obtain ⟨_, p₀, hp₀, hp₀v, hp₀avoid⟩ := mem_prefixSet.1 hvPrefix
    obtain ⟨hwSuffix, _, _, _⟩ := mem_relImage.1 hwUpper
    obtain ⟨_, p₂, hp₂, hp₂w, hp₂avoid⟩ := mem_suffixSet.1 hwSuffix
    obtain ⟨b, hbB, hub, hwn⟩ := huw
    have huble : u ≤ w := by omega
    have hwsub : w - u = b := by omega
    have hfv : AddEdge n B v (f w) := by
      refine ⟨b, hbB, ?_, ?_⟩
      · simp [f, hwsub]
      · dsimp [f]
        omega
    have hfwn : f w ≤ n := by
      dsimp [f]
      omega
    have hfww : AddEdge n B (f w) w := by
      refine ⟨c, hcB, ?_, hwn⟩
      dsimp [f]
      omega
    have hfwS : (j, f w) ∈ S := splice_middle_mem hj₀ hsep hp₀ hp₂
      hp₀v hp₂w (fun i hi => hp₀avoid i (by omega))
      (fun i hji hih => hp₂avoid i (by omega) hih) hfv hfww
    exact (mem_bipartiteAbove (AddEdge n B)).2
      ⟨mem_cutLayer.2 ⟨hfwn, hfwS⟩, hfv⟩
  · intro w₁ hw₁ w₂ hw₂ hfw
    obtain ⟨_, hw₁edge⟩ := (mem_bipartiteAbove (AddEdge n B)).1 hw₁
    obtain ⟨_, hw₂edge⟩ := (mem_bipartiteAbove (AddEdge n B)).1 hw₂
    obtain ⟨b₁, hb₁, hub₁, _⟩ := hw₁edge
    obtain ⟨b₂, hb₂, hub₂, _⟩ := hw₂edge
    have hw₁le : u ≤ w₁ := by omega
    have hw₂le : u ≤ w₂ := by omega
    dsimp [f] at hfw
    have hsub : w₁ - u = w₂ - u := Nat.add_left_cancel hfw
    omega

lemma separatorLower_has_middle_neighbor
    {n h j : ℕ} {X B : Finset ℕ} {S : Finset (ℕ × ℕ)}
    {v : ℕ} (hv : v ∈ separatorLower n h j X B S) :
    ((separatorMiddle n j S).bipartiteAbove (AddEdge n B) v).Nonempty := by
  obtain ⟨_, u, hu, hvu⟩ := mem_relPreimage.1 hv
  exact ⟨u, (mem_bipartiteAbove (AddEdge n B)).2 ⟨hu, hvu⟩⟩

lemma separatorMiddle_has_upper_neighbor
    {n h j : ℕ} {X B : Finset ℕ} {S : Finset (ℕ × ℕ)}
    (hjh : j < h) (hsep : IsSeparator n h X B S)
    (herase : ∀ u ∈ separatorMiddle n j S,
      ¬IsSeparator n h X B (S.erase (j, u)))
    {u : ℕ} (hu : u ∈ separatorMiddle n j S) :
    ((separatorUpper n h j X B S).bipartiteAbove (AddEdge n B) u).Nonempty := by
  have hju : (j, u) ∈ S := (mem_cutLayer.1 hu).2
  obtain ⟨p, hp, hpju, havoid⟩ :=
    essential_path_of_erase_not_separator hsep (herase u hu)
  have hstep : AddEdge n B u (p (j + 1)) := by
    simpa [hpju] using hp.2.2 j hjh
  have hsucc : p (j + 1) ∈ suffixSet n h X B S (j + 1) := by
    refine mem_suffixSet.2 ⟨hp.2.1 (j + 1) (by omega), p, hp, rfl, ?_⟩
    intro t ht hth
    exact havoid t hth (by omega)
  have hupper : p (j + 1) ∈ separatorUpper n h j X B S := by
    rw [separatorUpper]
    exact mem_relImage.2 ⟨hsucc, u, hu, hstep⟩
  exact ⟨p (j + 1), (mem_bipartiteAbove (AddEdge n B)).2 ⟨hupper, hstep⟩⟩

lemma separator_channel_forward_expansion
    {n h j : ℕ} {X B : Finset ℕ} {S : Finset (ℕ × ℕ)}
    {C : ℝ} (hC : 0 < C) (hjh : j < h) (hS : S ⊆ vertexGrid n h)
    (hmin : ∀ T ⊆ vertexGrid n h, IsSeparator n h X B T →
      separatorWeight C h S ≤ separatorWeight C h T)
    (hsep : IsSeparator n h X B S) :
    ∀ Q ⊆ separatorMiddle n j S,
      C * (#Q : ℝ) ≤
        #(relImage (AddEdge n B) Q (separatorUpper n h j X B S)) := by
  intro Q hQ
  let I := relImage (AddEdge n B) Q (separatorUpper n h j X B S)
  let T := forwardReplacement n h j X B S Q
  have hA : atLayer j Q ⊆ S := atLayer_subset_iff.2 fun x hx =>
    (mem_cutLayer.1 (hQ hx)).2
  have hTgrid : T ⊆ vertexGrid n h := forwardReplacement_subset_grid hjh hS
  have hTsep : IsSeparator n h X B T := forwardReplacement_isSeparator hjh hsep hQ
  have hbal := separatorWeight_replacement_balance hC.le h
    (A := atLayer j Q) (S := S) (D := atLayer (j + 1) I) hA
  have hminT := hmin T hTgrid hTsep
  have hminT' : separatorWeight C h S ≤
      separatorWeight C h ((S \ atLayer j Q) ∪ atLayer (j + 1) I) := by
    simpa [T, forwardReplacement] using hminT
  have hw : separatorWeight C h (atLayer j Q) ≤
      separatorWeight C h (atLayer (j + 1) I) := by
    linarith
  rw [separatorWeight_atLayer, separatorWeight_atLayer] at hw
  have hexp : h - j = (h - (j + 1)) + 1 := by omega
  rw [hexp, pow_succ] at hw
  have hp : 0 < C ^ (h - (j + 1)) := pow_pos hC _
  dsimp [I] at hw ⊢
  nlinarith

lemma separator_channel_backward_expansion
    {n h j : ℕ} {X B : Finset ℕ} {S : Finset (ℕ × ℕ)}
    {C : ℝ} (hC : 0 < C) (hj₀ : 0 < j) (hjh : j ≤ h)
    (hS : S ⊆ vertexGrid n h)
    (hmin : ∀ T ⊆ vertexGrid n h, IsSeparator n h X B T →
      separatorWeight C h S ≤ separatorWeight C h T)
    (hsep : IsSeparator n h X B S) :
    ∀ Q ⊆ separatorMiddle n j S,
      (#Q : ℝ) ≤ C *
        #(relPreimage (AddEdge n B) (separatorLower n h j X B S) Q) := by
  intro Q hQ
  let P := relPreimage (AddEdge n B) (separatorLower n h j X B S) Q
  let T := backwardReplacement n h j X B S Q
  have hA : atLayer j Q ⊆ S := atLayer_subset_iff.2 fun x hx =>
    (mem_cutLayer.1 (hQ hx)).2
  have hTgrid : T ⊆ vertexGrid n h := backwardReplacement_subset_grid hjh hS
  have hTsep : IsSeparator n h X B T := backwardReplacement_isSeparator hj₀ hsep hQ
  have hbal := separatorWeight_replacement_balance hC.le h
    (A := atLayer j Q) (S := S) (D := atLayer (j - 1) P) hA
  have hminT := hmin T hTgrid hTsep
  have hminT' : separatorWeight C h S ≤
      separatorWeight C h ((S \ atLayer j Q) ∪ atLayer (j - 1) P) := by
    simpa [T, backwardReplacement] using hminT
  have hw : separatorWeight C h (atLayer j Q) ≤
      separatorWeight C h (atLayer (j - 1) P) := by
    linarith
  rw [separatorWeight_atLayer, separatorWeight_atLayer] at hw
  have hexp : h - (j - 1) = (h - j) + 1 := by omega
  rw [hexp, pow_succ] at hw
  have hp : 0 < C ^ (h - j) := pow_pos hC _
  dsimp [P] at hw ⊢
  nlinarith

lemma erase_not_separator_of_weight_minimal
    {n h : ℕ} {X B : Finset ℕ} {S : Finset (ℕ × ℕ)} {C : ℝ}
    (hC : 0 < C) (hS : S ⊆ vertexGrid n h)
    (hmin : ∀ T ⊆ vertexGrid n h, IsSeparator n h X B T →
      separatorWeight C h S ≤ separatorWeight C h T)
    {q : ℕ × ℕ} (hq : q ∈ S) :
    ¬IsSeparator n h X B (S.erase q) := by
  intro hsep
  have heraseGrid : S.erase q ⊆ vertexGrid n h := (erase_subset _ _).trans hS
  have hle := hmin (S.erase q) heraseGrid hsep
  have hsingle : ({q} : Finset (ℕ × ℕ)) ⊆ S := singleton_subset_iff.2 hq
  have hsumRaw := separatorWeight_sdiff_add (C := C) h hsingle
  rw [sdiff_singleton_eq_erase] at hsumRaw
  have hsum : separatorWeight C h (S.erase q) + C ^ (h - q.1) =
      separatorWeight C h S := by
    simpa [separatorWeight] using hsumRaw
  have hpos : 0 < C ^ (h - q.1) := pow_pos hC _
  linarith

/-- A separator chosen first by minimum weight and then by minimum level rank
has no vertices in an interior layer.  This is Petridis's weighted
"pull-down" lemma specialized to the truncated addition graph. -/
lemma minimum_separator_has_no_interior
    {n h : ℕ} {X B : Finset ℕ} {S : Finset (ℕ × ℕ)} {C : ℝ}
    (hC : 0 < C) (hC₁ : 1 ≤ C) (hS : S ⊆ vertexGrid n h)
    (hsep : IsSeparator n h X B S)
    (hmin : ∀ T ⊆ vertexGrid n h, IsSeparator n h X B T →
      separatorWeight C h S ≤ separatorWeight C h T)
    (hminRank : ∀ T ⊆ vertexGrid n h, IsSeparator n h X B T →
      separatorWeight C h T = separatorWeight C h S →
      separatorRank S ≤ separatorRank T) :
    ∀ j, 0 < j → j < h → separatorMiddle n j S = ∅ := by
  intro j hj₀ hjh
  by_contra hmiddle
  have hU₁ne : (separatorMiddle n j S).Nonempty := nonempty_iff_ne_empty.2 hmiddle
  have herase : ∀ u ∈ separatorMiddle n j S,
      ¬IsSeparator n h X B (S.erase (j, u)) := by
    intro u hu
    exact erase_not_separator_of_weight_minimal hC hS hmin (mem_cutLayer.1 hu).2
  have hforward := separator_channel_forward_expansion hC hjh hS hmin hsep
  have hbackward := separator_channel_backward_expansion hC hj₀ hjh.le hS hmin hsep
  have hcard : C * (#(separatorLower n h j X B S) : ℝ) =
      #(separatorMiddle n j S) := by
    apply levelTwo_middle_card_eq
      (separatorLower n h j X B S) (separatorMiddle n j S)
      (separatorUpper n h j X B S) (AddEdge n B) (AddEdge n B) C hC
    · exact hforward
    · exact hbackward
    · intro u hu v hv huv
      exact separator_channel_down_degree hj₀ hsep hv huv
    · intro v hv u hu hvu
      exact separator_channel_up_degree hj₀ hsep hv hvu
    · intro v hv
      exact separatorLower_has_middle_neighbor hv
    · intro u hu
      exact separatorMiddle_has_upper_neighbor hjh hsep herase hu
  let U₀ := separatorLower n h j X B S
  let U₁ := separatorMiddle n j S
  let T := backwardReplacement n h j X B S U₁
  have hU₁sub : U₁ ⊆ separatorMiddle n j S := by simp [U₁]
  have hTgrid : T ⊆ vertexGrid n h :=
    backwardReplacement_subset_grid hjh.le hS
  have hTsep : IsSeparator n h X B T :=
    backwardReplacement_isSeparator hj₀ hsep hU₁sub
  have hA : atLayer j U₁ ⊆ S := atLayer_subset_iff.2 fun x hx =>
    (mem_cutLayer.1 hx).2
  have hpre : relPreimage (AddEdge n B) U₀ U₁ = U₀ := by
    apply Finset.Subset.antisymm
    · exact filter_subset _ _
    · intro v hv
      obtain ⟨u, hu⟩ := separatorLower_has_middle_neighbor
        (S := S) (X := X) (B := B) (j := j) (v := v) (by simpa [U₀] using hv)
      obtain ⟨huU₁, hvu⟩ := (mem_bipartiteAbove (AddEdge n B)).1 hu
      exact mem_relPreimage.2 ⟨hv, u, (by simpa [U₁] using huU₁), hvu⟩
  have hTdef : T = (S \ atLayer j U₁) ∪ atLayer (j - 1) U₀ := by
    dsimp [T, backwardReplacement]
    rw [hpre]
  have hweights : separatorWeight C h (atLayer (j - 1) U₀) =
      separatorWeight C h (atLayer j U₁) := by
    rw [separatorWeight_atLayer, separatorWeight_atLayer]
    have hexp : h - (j - 1) = (h - j) + 1 := by omega
    rw [hexp, pow_succ]
    dsimp [U₀, U₁]
    nlinarith [pow_pos hC (h - j)]
  have hbal := separatorWeight_replacement_balance hC.le h
    (A := atLayer j U₁) (S := S) (D := atLayer (j - 1) U₀) hA
  have hTle : separatorWeight C h T ≤ separatorWeight C h S := by
    rw [hTdef]
    rw [hweights] at hbal
    linarith
  have hwEq : separatorWeight C h T = separatorWeight C h S :=
    le_antisymm hTle (hmin T hTgrid hTsep)
  have hcardleR : (#U₀ : ℝ) ≤ #U₁ := by
    dsimp [U₀, U₁]
    rw [← hcard]
    have hnonneg : (0 : ℝ) ≤ (#U₀ : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hcardle : #U₀ ≤ #U₁ := by exact_mod_cast hcardleR
  have hU₁pos : 0 < #U₁ := by simpa [U₁] using hU₁ne.card_pos
  have hrankBal := separatorRank_replacement_balance
    (A := atLayer j U₁) (S := S) (D := atLayer (j - 1) U₀) hA
  have hmulLt : #U₀ * (j - 1) < #U₁ * j := by
    have h₁ : #U₀ * (j - 1) ≤ #U₁ * (j - 1) :=
      Nat.mul_le_mul_right (j - 1) hcardle
    have h₂ : #U₁ * (j - 1) < #U₁ * j := by
      exact (Nat.mul_lt_mul_left hU₁pos).2 (by omega)
    exact h₁.trans_lt h₂
  have hrankLt : separatorRank T < separatorRank S := by
    rw [hTdef]
    simp only [separatorRank_atLayer] at hrankBal
    omega
  exact (not_lt_of_ge (hminRank T hTgrid hTsep hwEq)) hrankLt

lemma vertexGrid_isSeparator (n h : ℕ) (X B : Finset ℕ) :
    IsSeparator n h X B (vertexGrid n h) := by
  intro p hp
  refine ⟨0, Nat.zero_le h, ?_⟩
  have hp0n : p 0 ≤ n := hp.2.1 0 (Nat.zero_le h)
  simp [vertexGrid, hp0n]

lemma firstLayer_isSeparator {n h : ℕ} {X B : Finset ℕ} (hh : 0 < h) :
    IsSeparator n h X B (atLayer 1 (truncAdd n X B)) := by
  intro p hp
  obtain ⟨b, hb, hsum, hp1n⟩ := hp.2.2 0 hh
  refine ⟨1, hh, pair_mem_atLayer.2 ?_⟩
  exact mem_truncAdd.2 ⟨p 0, hp.1, b, hb, hsum, hp1n⟩

lemma bottomLayer_subset_source
    {n h : ℕ} {X B : Finset ℕ} {S : Finset (ℕ × ℕ)} {C : ℝ}
    (hC : 0 < C) (hS : S ⊆ vertexGrid n h)
    (hsep : IsSeparator n h X B S)
    (hmin : ∀ T ⊆ vertexGrid n h, IsSeparator n h X B T →
      separatorWeight C h S ≤ separatorWeight C h T) :
    cutLayer n S 0 ⊆ X := by
  intro x hx
  obtain ⟨hxn, hxS⟩ := mem_cutLayer.1 hx
  by_contra hxX
  apply erase_not_separator_of_weight_minimal hC hS hmin hxS
  intro p hp
  obtain ⟨i, hi, hiS⟩ := hsep p hp
  refine ⟨i, hi, mem_erase.2 ⟨?_, hiS⟩⟩
  intro heq
  have hi0 : i = 0 := congrArg Prod.fst heq
  have hpix : p i = x := congrArg Prod.snd heq
  subst i
  exact hxX (hpix ▸ hp.1)

lemma truncIter_avoiding_bottom_subset_top
    {n h : ℕ} {X B : Finset ℕ} {S : Finset (ℕ × ℕ)}
    (hsep : IsSeparator n h X B S)
    (hinterior : ∀ j, 0 < j → j < h → separatorMiddle n j S = ∅) :
    truncIter n (X \ cutLayer n S 0) B h ⊆ cutLayer n S h := by
  intro x hx
  obtain ⟨p, hp, hph⟩ := mem_truncIter_iff_exists_path.1 hx
  obtain ⟨i, hi, hiS⟩ := hsep p
    ⟨(mem_sdiff.1 hp.1).1, hp.2⟩
  by_cases hi0 : i = 0
  · subst i
    have hp0bottom : p 0 ∈ cutLayer n S 0 :=
      mem_cutLayer.2 ⟨hp.2.1 0 (Nat.zero_le h), hiS⟩
    exact ((mem_sdiff.1 hp.1).2 hp0bottom).elim
  by_cases hih : i = h
  · subst i
    exact mem_cutLayer.2 ⟨hph ▸ hp.2.1 h le_rfl, hph ▸ hiS⟩
  · have hiPos : 0 < i := Nat.pos_of_ne_zero hi0
    have hiLt : i < h := lt_of_le_of_ne hi hih
    have himid : p i ∈ separatorMiddle n i S :=
      mem_cutLayer.2 ⟨hp.2.1 i hi, hiS⟩
    rw [hinterior i hiPos hiLt] at himid
    simp at himid

lemma separator_eq_end_layers
    {n h : ℕ} {S : Finset (ℕ × ℕ)}
    (hS : S ⊆ vertexGrid n h)
    (hinterior : ∀ j, 0 < j → j < h → separatorMiddle n j S = ∅) :
    S = atLayer 0 (cutLayer n S 0) ∪ atLayer h (cutLayer n S h) := by
  apply Finset.Subset.antisymm
  · rintro ⟨i, x⟩ hiS
    have hgrid := hS hiS
    have hgrid' : i ≤ h ∧ x ≤ n := by simpa [vertexGrid] using hgrid
    have hi : i ≤ h := hgrid'.1
    have hxn : x ≤ n := hgrid'.2
    by_cases hi0 : i = 0
    · subst i
      exact mem_union_left _ (pair_mem_atLayer.2 (mem_cutLayer.2 ⟨hxn, hiS⟩))
    by_cases hih : i = h
    · subst i
      exact mem_union_right _ (pair_mem_atLayer.2 (mem_cutLayer.2 ⟨hxn, hiS⟩))
    · have himid : x ∈ separatorMiddle n i S := mem_cutLayer.2 ⟨hxn, hiS⟩
      rw [hinterior i (Nat.pos_of_ne_zero hi0) (lt_of_le_of_ne hi hih)] at himid
      simp at himid
  · intro q hq
    rcases mem_union.1 hq with hq | hq
    · obtain ⟨x, hx, rfl⟩ := mem_atLayer.1 hq
      exact (mem_cutLayer.1 hx).2
    · obtain ⟨x, hx, rfl⟩ := mem_atLayer.1 hq
      exact (mem_cutLayer.1 hx).2

lemma separatorWeight_eq_end_layers
    {C : ℝ} {n h : ℕ} {S : Finset (ℕ × ℕ)} (hh : 0 < h)
    (hS : S ⊆ vertexGrid n h)
    (hinterior : ∀ j, 0 < j → j < h → separatorMiddle n j S = ∅) :
    separatorWeight C h S =
      (#(cutLayer n S 0) : ℝ) * C ^ h + #(cutLayer n S h) := by
  conv_lhs => rw [separator_eq_end_layers hS hinterior]
  have hdis : Disjoint (atLayer 0 (cutLayer n S 0))
      (atLayer h (cutLayer n S h)) := by
    rw [Finset.disjoint_left]
    intro q hq0 hqh
    obtain ⟨x, hx, heq0⟩ := mem_atLayer.1 hq0
    obtain ⟨y, hy, heqh⟩ := mem_atLayer.1 hqh
    have : (0 : ℕ) = h := congrArg Prod.fst (heq0.trans heqh.symm)
    omega
  have hwunion : separatorWeight C h
      (atLayer 0 (cutLayer n S 0) ∪ atLayer h (cutLayer n S h)) =
      separatorWeight C h (atLayer 0 (cutLayer n S 0)) +
        separatorWeight C h (atLayer h (cutLayer n S h)) := by
    exact Finset.sum_union hdis
  rw [hwunion, separatorWeight_atLayer, separatorWeight_atLayer]
  simp

/-- Truncated first-step form of Plünnecke's magnification inequality.  If
every subset of the bottom expands by at least `C^h` at the top, then the
whole bottom expands by at least `C` in the first layer. -/
theorem truncated_pluennecke_first_step
    {C : ℝ} {n h : ℕ} {X B : Finset ℕ} (hC : 1 ≤ C) (hh : 0 < h)
    (htop : ∀ Z ⊆ X,
      C ^ h * (#Z : ℝ) ≤ #(truncIter n Z B h)) :
    C * (#X : ℝ) ≤ #(truncAdd n X B) := by
  let cuts := (vertexGrid n h).powerset.filter (IsSeparator n h X B)
  have hgridCut : vertexGrid n h ∈ cuts := by
    simp [cuts, vertexGrid_isSeparator]
  obtain ⟨S₀, hS₀, hS₀min⟩ :=
    exists_min_image cuts (separatorWeight C h) ⟨vertexGrid n h, hgridCut⟩
  have hS₀data : S₀ ⊆ vertexGrid n h ∧ IsSeparator n h X B S₀ := by
    simpa [cuts] using hS₀
  let best := cuts.filter fun T => separatorWeight C h T = separatorWeight C h S₀
  have hS₀best : S₀ ∈ best := by simp [best, hS₀]
  obtain ⟨S, hSbest, hSrank⟩ :=
    exists_min_image best separatorRank ⟨S₀, hS₀best⟩
  have hSdata : S ⊆ vertexGrid n h ∧ IsSeparator n h X B S := by
    have : S ∈ cuts := (mem_filter.1 hSbest).1
    simpa [cuts] using this
  have hSeq : separatorWeight C h S = separatorWeight C h S₀ :=
    (mem_filter.1 hSbest).2
  have hmin : ∀ T ⊆ vertexGrid n h, IsSeparator n h X B T →
      separatorWeight C h S ≤ separatorWeight C h T := by
    intro T hTgrid hTsep
    rw [hSeq]
    exact hS₀min T (by simp [cuts, hTgrid, hTsep])
  have hminRank : ∀ T ⊆ vertexGrid n h, IsSeparator n h X B T →
      separatorWeight C h T = separatorWeight C h S →
      separatorRank S ≤ separatorRank T := by
    intro T hTgrid hTsep hTeq
    apply hSrank T
    simp only [best, mem_filter]
    constructor
    · simp [cuts, hTgrid, hTsep]
    · exact hTeq.trans hSeq
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hinterior : ∀ j, 0 < j → j < h → separatorMiddle n j S = ∅ :=
    minimum_separator_has_no_interior hCpos hC hSdata.1 hSdata.2 hmin hminRank
  let Sbot := cutLayer n S 0
  let Stop := cutLayer n S h
  have hSbotX : Sbot ⊆ X :=
    bottomLayer_subset_source hCpos hSdata.1 hSdata.2 hmin
  have htopSub : truncIter n (X \ Sbot) B h ⊆ Stop := by
    exact truncIter_avoiding_bottom_subset_top hSdata.2 hinterior
  have htopCard : C ^ h * (#(X \ Sbot) : ℝ) ≤ (#Stop : ℝ) :=
    (htop (X \ Sbot) sdiff_subset).trans (by
      exact_mod_cast Finset.card_le_card htopSub)
  have hcardSplit : #(X \ Sbot) + #Sbot = #X :=
    card_sdiff_add_card_eq_card hSbotX
  have hwLower : C ^ h * (#X : ℝ) ≤ separatorWeight C h S := by
    rw [separatorWeight_eq_end_layers hh hSdata.1 hinterior]
    have hcardSplitR : (#(X \ Sbot) : ℝ) + #Sbot = #X := by
      exact_mod_cast hcardSplit
    change C ^ h * (#X : ℝ) ≤ (#Sbot : ℝ) * C ^ h + (#Stop : ℝ)
    calc
      C ^ h * (#X : ℝ) =
          (#Sbot : ℝ) * C ^ h + C ^ h * (#(X \ Sbot) : ℝ) := by
        rw [← hcardSplitR]
        ring
      _ ≤ (#Sbot : ℝ) * C ^ h + (#Stop : ℝ) :=
        by simpa [add_comm] using
          add_le_add_right htopCard ((#Sbot : ℝ) * C ^ h)
  have hfirstGrid : atLayer 1 (truncAdd n X B) ⊆ vertexGrid n h := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := mem_atLayer.1 hq
    obtain ⟨a, ha, b, hb, hab, hxn⟩ := mem_truncAdd.1 hx
    simp [vertexGrid, hh, hxn]
  have hwUpper : separatorWeight C h S ≤
      separatorWeight C h (atLayer 1 (truncAdd n X B)) :=
    hmin _ hfirstGrid (firstLayer_isSeparator hh)
  rw [separatorWeight_atLayer] at hwUpper
  have hmain : C ^ h * (#X : ℝ) ≤
      (#(truncAdd n X B) : ℝ) * C ^ (h - 1) := hwLower.trans hwUpper
  have hexp : h = (h - 1) + 1 := by omega
  have hpow : C ^ h = C ^ (h - 1) * C := by
    calc
      C ^ h = C ^ ((h - 1) + 1) := congrArg (fun e : ℕ => C ^ e) hexp
      _ = C ^ (h - 1) * C := pow_succ _ _
  rw [hpow] at hmain
  have hp : 0 < C ^ (h - 1) := pow_pos hCpos _
  nlinarith

/-! ## From an additive basis to block expansion -/

/-- The part of a (possibly infinite) basis which can occur below the
cutoff `n`. -/
def basisFinset (B : Set ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 0 n).filter (· ∈ B)

@[simp] lemma mem_basisFinset {B : Set ℕ} {n b : ℕ} :
    b ∈ basisFinset B n ↔ b ∈ B ∧ b ≤ n := by
  simp [basisFinset, and_comm]

/-- A representation of `d` as a sum of `k` basis elements gives a
truncated path from `x` to `x+d`, provided the endpoint is below the
cutoff. -/
lemma mem_truncIter_of_mem_nsmul {B : Set ℕ} {k n x d : ℕ}
    (hd : d ∈ k • B) (hxd : x + d ≤ n) :
    x + d ∈ truncIter n {x} (basisFinset B n) k := by
  induction k generalizing d with
  | zero =>
      simp only [zero_nsmul] at hd
      subst d
      exact mem_filter.2 ⟨by simp, by omega⟩
  | succ k ih =>
      rw [succ_nsmul] at hd
      obtain ⟨d', hd', b, hb, hsum⟩ := Set.mem_add.1 hd
      subst d
      have hprefix : x + d' ≤ n := by omega
      have hdIter := ih hd' hprefix
      rw [truncIter_succ]
      exact mem_truncAdd.2 ⟨x + d', hdIter, b,
        mem_basisFinset.2 ⟨hb, by omega⟩, by omega, hxd⟩

lemma truncIter_mono_source {n k : ℕ} {X Y B : Finset ℕ} (hXY : X ⊆ Y) :
    truncIter n X B k ⊆ truncIter n Y B k := by
  induction k with
  | zero =>
      intro x hx
      exact mem_filter.2 ⟨hXY (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩
  | succ k ih =>
      exact truncAdd_mono_left ih

lemma interval_subset_truncIter_of_basis
    {B : Set ℕ} {k n : ℕ} (hBasis : IsAdditiveBasisOfOrder B k)
    {Z : Finset ℕ} (hZ : Z.Nonempty) :
    Finset.Icc (Z.min' hZ) n ⊆ truncIter n Z (basisFinset B n) k := by
  intro y hy
  have hmy : Z.min' hZ ≤ y := (mem_Icc.1 hy).1
  have hyn : y ≤ n := (mem_Icc.1 hy).2
  have hd : y - Z.min' hZ ∈ k • B := by
    rw [hBasis]
    simp
  have hone : Z.min' hZ + (y - Z.min' hZ) ∈
      truncIter n {Z.min' hZ} (basisFinset B n) k :=
    mem_truncIter_of_mem_nsmul hd (by simpa [Nat.add_sub_of_le hmy] using hyn)
  have hmono := truncIter_mono_source (n := n) (k := k)
    (B := basisFinset B n) (singleton_subset_iff.2 (min'_mem Z hZ))
  simpa [Nat.add_sub_of_le hmy] using hmono hone

/-- The elementary exponential estimate used with the integer-power
separator weights. -/
lemma polynomial_factor_pow_le_one {p : ℝ} {k : ℕ}
    (hp : 0 < p) (hp1 : p ≤ 1) (hk : 0 < k) :
    p * (1 + (1 - p) / k) ^ k ≤ 1 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have ht : p - 1 ≤ (k : ℝ) := by linarith
  have hpow : (1 + (1 - p) / k) ^ k ≤ Real.exp (1 - p) := by
    have h := Real.one_sub_div_pow_le_exp_neg (n := k) (t := p - 1) ht
    convert h using 1 <;> ring
  have hexp : Real.exp (1 - p) ≤ 1 / p := by
    have := Real.exp_bound_div_one_sub_of_interval
      (x := 1 - p) (sub_nonneg.mpr hp1) (by linarith)
    simpa using this
  have hpow' : (1 + (1 - p) / k) ^ k ≤ 1 / p := hpow.trans hexp
  have hmul := (le_div_iff₀ hp).1 hpow'
  simpa [mul_comm] using hmul

def blockSet (A : Set ℕ) (a b : ℕ) : Finset ℕ :=
  (Finset.Icc a b).filter (· ∈ A)

@[simp] lemma mem_blockSet {A : Set ℕ} {a b x : ℕ} :
    x ∈ blockSet A a b ↔ a ≤ x ∧ x ≤ b ∧ x ∈ A := by
  simp [blockSet, and_assoc]

@[simp] lemma card_blockSet (A : Set ℕ) (a b : ℕ) :
    #(blockSet A a b) = countOn A a b := rfl

/-- The block ending at `b` has minimum prefix density among all prefixes
starting at `a`, expressed without division. -/
def IsMinPrefixBlock (A : Set ℕ) (a b : ℕ) : Prop :=
  a ≤ b ∧ ∀ c, a ≤ c → c ≤ b →
    countOn A a b * (c - a + 1) ≤ countOn A a c * (b - a + 1)

def IsLeastPrefixDensity (A : Set ℕ) (a b c : ℕ) : Prop :=
  a ≤ c ∧ c ≤ b ∧ ∀ d, a ≤ d → d ≤ b →
    countOn A a c * (d - a + 1) ≤ countOn A a d * (c - a + 1)

lemma minPrefixBlock_suffix_mul_le {A : Set ℕ} {a b : ℕ}
    (hblock : IsMinPrefixBlock A a b) {m : ℕ} (ham : a ≤ m) (hmb : m ≤ b) :
    countOn A m b * (b - a + 1) ≤
      countOn A a b * (b - m + 1) := by
  rcases eq_or_lt_of_le ham with rfl | ham
  · simp
  have hsets : blockSet A a b =
      blockSet A a (m - 1) ∪ blockSet A m b := by
    ext x
    constructor
    · rintro hx
      obtain ⟨hax, hxb, hxA⟩ := mem_blockSet.1 hx
      by_cases hxm : x < m
      · exact Finset.mem_union_left _ (mem_blockSet.2 ⟨hax, by omega, hxA⟩)
      · exact Finset.mem_union_right _ (mem_blockSet.2 ⟨by omega, hxb, hxA⟩)
    · intro hx
      rcases Finset.mem_union.1 hx with hx | hx
      · obtain ⟨hax, hxm, hxA⟩ := mem_blockSet.1 hx
        exact mem_blockSet.2 ⟨hax, by omega, hxA⟩
      · obtain ⟨hmx, hxb, hxA⟩ := mem_blockSet.1 hx
        exact mem_blockSet.2 ⟨ham.le.trans hmx, hxb, hxA⟩
  have hdis : Disjoint (blockSet A a (m - 1)) (blockSet A m b) := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    have hx₁' := (mem_blockSet.1 hx₁).2.1
    have hx₂' := (mem_blockSet.1 hx₂).1
    omega
  have hcard : countOn A a b = countOn A a (m - 1) + countOn A m b := by
    change #(blockSet A a b) =
      #(blockSet A a (m - 1)) + #(blockSet A m b)
    rw [hsets, card_union_of_disjoint hdis]
  have hprefix := hblock.2 (m - 1) (by omega) (by omega)
  have hlen : b - a + 1 = (m - a) + (b - m + 1) := by omega
  have hprefix' : countOn A a b * (m - a) ≤
      countOn A a (m - 1) * (b - a + 1) := by
    simpa [show m - 1 - a + 1 = m - a by omega] using hprefix
  have hsuffixPrefix : countOn A m b * (m - a) ≤
      countOn A a (m - 1) * (b - m + 1) := by
    rw [hcard, hlen, add_mul, mul_add] at hprefix'
    omega
  rw [hlen, hcard, mul_add, add_mul]
  omega


lemma exists_leastPrefixDensity (A : Set ℕ) {a b : ℕ} (hab : a ≤ b) :
    ∃ c, IsLeastPrefixDensity A a b c := by
  let density : ℕ → ℚ := fun c =>
    (countOn A a c : ℚ) / ((c - a + 1 : ℕ) : ℚ)
  have hnonempty : (Finset.Icc a b).Nonempty := ⟨a, by simp [hab]⟩
  obtain ⟨c, hc, hcmin⟩ := exists_min_image (Finset.Icc a b) density hnonempty
  refine ⟨c, (mem_Icc.1 hc).1, (mem_Icc.1 hc).2, ?_⟩
  intro d had hdb
  have hrat := hcmin d (mem_Icc.2 ⟨had, hdb⟩)
  have hcden : (0 : ℚ) < ((c - a + 1 : ℕ) : ℚ) := by positivity
  have hdden : (0 : ℚ) < ((d - a + 1 : ℕ) : ℚ) := by positivity
  dsimp [density] at hrat
  rw [div_le_div_iff₀ hcden hdden] at hrat
  exact_mod_cast hrat

lemma countOn_split {A : Set ℕ} {a c d : ℕ} (hac : a ≤ c) (hcd : c < d) :
    countOn A a d = countOn A a c + countOn A (c + 1) d := by
  have hsets : blockSet A a d = blockSet A a c ∪ blockSet A (c + 1) d := by
    ext x
    constructor
    · rintro hx
      obtain ⟨hax, hxd, hxA⟩ := mem_blockSet.1 hx
      by_cases hxc : x ≤ c
      · exact Finset.mem_union_left _ (mem_blockSet.2 ⟨hax, hxc, hxA⟩)
      · exact Finset.mem_union_right _ (mem_blockSet.2 ⟨by omega, hxd, hxA⟩)
    · intro hx
      rcases Finset.mem_union.1 hx with hx | hx
      · obtain ⟨hax, hxc, hxA⟩ := mem_blockSet.1 hx
        exact mem_blockSet.2 ⟨hax, hxc.trans hcd.le, hxA⟩
      · obtain ⟨hcx, hxd, hxA⟩ := mem_blockSet.1 hx
        exact mem_blockSet.2 ⟨hac.trans (by omega), hxd, hxA⟩
  have hdis : Disjoint (blockSet A a c) (blockSet A (c + 1) d) := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    have hx₁' := (mem_blockSet.1 hx₁).2.1
    have hx₂' := (mem_blockSet.1 hx₂).1
    omega
  change #(blockSet A a d) = #(blockSet A a c) + #(blockSet A (c + 1) d)
  rw [hsets, card_union_of_disjoint hdis]

lemma leastPrefix_suffix_lower {A : Set ℕ} {a b c : ℕ}
    (hleast : IsLeastPrefixDensity A a b c) {d : ℕ}
    (hcd : c < d) (hdb : d ≤ b) :
    countOn A a c * (d - c) ≤ countOn A (c + 1) d * (c - a + 1) := by
  have hmin := hleast.2.2 d (hleast.1.trans hcd.le) hdb
  have hsplit := countOn_split (A := A) hleast.1 hcd
  have hac : a ≤ c := hleast.1
  have hlen : d - a + 1 = (c - a + 1) + (d - c) := by omega
  rw [hlen, hsplit, mul_add, add_mul] at hmin
  exact Nat.le_of_add_le_add_left hmin

lemma leastPrefix_isMinBlock {A : Set ℕ} {a b c : ℕ}
    (hleast : IsLeastPrefixDensity A a b c) : IsMinPrefixBlock A a c := by
  refine ⟨hleast.1, ?_⟩
  intro d had hdc
  exact hleast.2.2 d had (hdc.trans hleast.2.1)

lemma truncAdd_block_subset_sumset {A B : Set ℕ} {a b : ℕ} :
    truncAdd b (blockSet A a b) (basisFinset B b) ⊆ blockSet (A + B) a b := by
  intro y hy
  obtain ⟨x, hx, z, hz, hxyz, hyb⟩ := mem_truncAdd.1 hy
  obtain ⟨hax, hxb, hxA⟩ := mem_blockSet.1 hx
  have hza := mem_basisFinset.1 hz
  exact mem_blockSet.2 ⟨hax.trans (by omega), hyb,
    Set.mem_add.2 ⟨x, hxA, z, hza.1, hxyz⟩⟩

def blockDensity (A : Set ℕ) (a b : ℕ) : ℝ :=
  (countOn A a b : ℝ) / ((b - a + 1 : ℕ) : ℝ)

def expansionFactor (p : ℝ) (k : ℕ) : ℝ :=
  1 + (1 - p) / k

def densityGain (p : ℝ) (k : ℕ) : ℝ :=
  p * expansionFactor p k

lemma densityGain_mono {p q : ℝ} {k : ℕ}
    (hpq : p ≤ q) (hq1 : q ≤ 1) (hk : 0 < k) :
    densityGain p k ≤ densityGain q k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnum : -1 ≤ 1 - p - q := by nlinarith
  have hdiv : -1 ≤ (1 - p - q) / k := by
    rw [le_div_iff₀ hkR]
    nlinarith
  have hfac : 0 ≤ 1 + (1 - p - q) / k := by linarith
  have hid : densityGain q k - densityGain p k =
      (q - p) * (1 + (1 - p - q) / k) := by
    simp [densityGain, expansionFactor]
    ring
  rw [← sub_nonneg, hid]
  positivity

/-- Plünnecke's finite theorem applied to a minimum-prefix-density block. -/
theorem minPrefixBlock_expansion {A B : Set ℕ} {k a b : ℕ}
    (hBasis : IsAdditiveBasisOfOrder B k) (hk : 0 < k)
    (hblock : IsMinPrefixBlock A a b) :
    expansionFactor (blockDensity A a b) k * (#(blockSet A a b) : ℝ) ≤
      countOn (A + B) a b := by
  let X := blockSet A a b
  let p := blockDensity A a b
  let C := expansionFactor p k
  have hlenNat : 0 < b - a + 1 := by omega
  have hlen : (0 : ℝ) < ((b - a + 1 : ℕ) : ℝ) := by exact_mod_cast hlenNat
  have hp0 : 0 ≤ p := by
    dsimp [p, blockDensity]
    exact div_nonneg (Nat.cast_nonneg _) hlen.le
  have hp1 : p ≤ 1 := by
    dsimp [p, blockDensity]
    rw [div_le_one (by positivity)]
    exact_mod_cast countOn_le_length A hblock.1
  have hC : 1 ≤ C := by
    dsimp [C, expansionFactor]
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have : 0 ≤ (1 - p) / (k : ℝ) :=
      div_nonneg (sub_nonneg.mpr hp1) hkR.le
    linarith
  have htop : ∀ Z ⊆ X, C ^ k * (#Z : ℝ) ≤
      #(truncIter b Z (basisFinset B b) k) := by
    intro Z hZX
    obtain rfl | hZ := Z.eq_empty_or_nonempty
    · simp
    let m := Z.min' hZ
    have hmX : m ∈ X := hZX (by exact min'_mem Z hZ)
    have hmA : a ≤ m ∧ m ≤ b ∧ m ∈ A := by
      have hmX' : m ∈ blockSet A a b := by simpa [X] using hmX
      exact mem_blockSet.1 hmX'
    have hZsuffix : Z ⊆ blockSet A m b := by
      intro z hz
      have hzX' : z ∈ blockSet A a b := by simpa [X] using hZX hz
      obtain ⟨haz, hzb, hzA⟩ := mem_blockSet.1 hzX'
      exact mem_blockSet.2 ⟨min'_le Z z hz, hzb, hzA⟩
    have hZmulNat : #Z * (b - a + 1) ≤
        countOn A a b * (b - m + 1) :=
      (Nat.mul_le_mul_right (b - a + 1) (Finset.card_le_card hZsuffix)).trans
        (minPrefixBlock_suffix_mul_le hblock hmA.1 hmA.2.1)
    have hZmul : (#Z : ℝ) * ((b - a + 1 : ℕ) : ℝ) ≤
        (countOn A a b : ℝ) * ((b - m + 1 : ℕ) : ℝ) := by
      exact_mod_cast hZmulNat
    have hpLen : p * ((b - a + 1 : ℕ) : ℝ) = countOn A a b := by
      dsimp [p, blockDensity]
      field_simp
    have hZratio : (#Z : ℝ) ≤ p * ((b - m + 1 : ℕ) : ℝ) := by
      apply le_of_mul_le_mul_right _ hlen
      calc
        (#Z : ℝ) * ((b - a + 1 : ℕ) : ℝ) ≤
            (countOn A a b : ℝ) * ((b - m + 1 : ℕ) : ℝ) := hZmul
        _ = (p * ((b - m + 1 : ℕ) : ℝ)) * ((b - a + 1 : ℕ) : ℝ) := by
          rw [← hpLen]
          ring
    have hpPos : 0 < p := by
      dsimp [p, blockDensity]
      exact div_pos (by
        exact_mod_cast (card_pos.mpr ⟨m, hmX⟩)) hlen
    have hpC : p * C ^ k ≤ 1 := by
      exact polynomial_factor_pow_le_one hpPos hp1 hk
    have hinterval : Finset.Icc m b ⊆
        truncIter b Z (basisFinset B b) k :=
      interval_subset_truncIter_of_basis hBasis hZ
    have hintervalCard : (b - m + 1 : ℕ) ≤
        #(truncIter b Z (basisFinset B b) k) := by
      have hc := Finset.card_le_card hinterval
      rw [Nat.card_Icc] at hc
      omega
    calc
      C ^ k * (#Z : ℝ) ≤ C ^ k * (p * ((b - m + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hZratio (pow_nonneg (zero_le_one.trans hC) _)
      _ = (p * C ^ k) * ((b - m + 1 : ℕ) : ℝ) := by ring
      _ ≤ (1 : ℝ) * ((b - m + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hpC (by positivity)
      _ ≤ #(truncIter b Z (basisFinset B b) k) := by
        norm_num
        exact_mod_cast hintervalCard
  have hpl := truncated_pluennecke_first_step hC hk htop
  have hsub := truncAdd_block_subset_sumset (A := A) (B := B) (a := a) (b := b)
  have hcard : #(truncAdd b X (basisFinset B b)) ≤ countOn (A + B) a b := by
    exact Finset.card_le_card hsub
  have hcardR : (#(truncAdd b X (basisFinset B b)) : ℝ) ≤
      countOn (A + B) a b := by exact_mod_cast hcard
  have hpl' : expansionFactor (blockDensity A a b) k *
      (#(blockSet A a b) : ℝ) ≤ #(truncAdd b X (basisFinset B b)) := by
    simpa [X, p, C] using hpl
  exact hpl'.trans hcardR

lemma interval_density_expansion_aux {A B : Set ℕ} {k : ℕ}
    (hBasis : IsAdditiveBasisOfOrder B k) (hk : 0 < k) :
    ∀ N a b (p : ℝ), b - a + 1 ≤ N → a ≤ b → 0 ≤ p → p ≤ 1 →
      (∀ d, a ≤ d → d ≤ b →
        p * ((d - a + 1 : ℕ) : ℝ) ≤ countOn A a d) →
      densityGain p k * ((b - a + 1 : ℕ) : ℝ) ≤ countOn (A + B) a b := by
  intro N
  induction N with
  | zero =>
      intro a b p hlen hab hp0 hp1 hlower
      omega
  | succ N ih =>
      intro a b p hlen hab hp0 hp1 hlower
      obtain ⟨c, hleast⟩ := exists_leastPrefixDensity A hab
      let q := blockDensity A a c
      have hclenNat : 0 < c - a + 1 := by omega
      have hclen : (0 : ℝ) < ((c - a + 1 : ℕ) : ℝ) := by exact_mod_cast hclenNat
      have hqLen : q * ((c - a + 1 : ℕ) : ℝ) = countOn A a c := by
        dsimp [q, blockDensity]
        field_simp
      have hpq : p ≤ q := by
        apply le_of_mul_le_mul_right _ hclen
        rw [hqLen]
        exact hlower c hleast.1 hleast.2.1
      have hq0 : 0 ≤ q := hp0.trans hpq
      have hq1 : q ≤ 1 := by
        dsimp [q, blockDensity]
        rw [div_le_one (by positivity)]
        exact_mod_cast countOn_le_length A hleast.1
      have hgain : densityGain p k ≤ densityGain q k :=
        densityGain_mono hpq hq1 hk
      have hblockRaw := minPrefixBlock_expansion hBasis hk
        (leastPrefix_isMinBlock hleast)
      have hblock : densityGain q k * ((c - a + 1 : ℕ) : ℝ) ≤
          countOn (A + B) a c := by
        calc
          densityGain q k * ((c - a + 1 : ℕ) : ℝ) =
              expansionFactor q k * countOn A a c := by
            rw [← hqLen]
            simp [densityGain]
            ring
          _ ≤ countOn (A + B) a c := by
            simpa [q] using hblockRaw
      by_cases hcb : c = b
      · subst c
        exact (mul_le_mul_of_nonneg_right hgain (Nat.cast_nonneg _)).trans hblock
      · have hcb' : c < b := lt_of_le_of_ne hleast.2.1 hcb
        have hsuffixLen : b - (c + 1) + 1 = b - c := by omega
        have hsuffixMeasure : b - (c + 1) + 1 ≤ N := by
          rw [hsuffixLen]
          have hba : b - a ≤ N := by omega
          exact (Nat.sub_le_sub_left hleast.1 b).trans hba
        have hsuffixLower : ∀ d, c + 1 ≤ d → d ≤ b →
            q * ((d - (c + 1) + 1 : ℕ) : ℝ) ≤ countOn A (c + 1) d := by
          intro d hcd hdb
          have hcross := leastPrefix_suffix_lower hleast (show c < d by omega) hdb
          dsimp [q, blockDensity]
          rw [show d - (c + 1) + 1 = d - c by omega]
          rw [div_mul_eq_mul_div, div_le_iff₀ hclen]
          exact_mod_cast hcross
        have hsuffix := ih (c + 1) b q hsuffixMeasure (by omega) hq0 hq1 hsuffixLower
        have hcountSplit := countOn_split (A := A + B) hleast.1 hcb'
        calc
          densityGain p k * ((b - a + 1 : ℕ) : ℝ) ≤
              densityGain q k * ((b - a + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right hgain (Nat.cast_nonneg _)
          _ = densityGain q k * ((c - a + 1 : ℕ) : ℝ) +
                densityGain q k * ((b - (c + 1) + 1 : ℕ) : ℝ) := by
            rw [hsuffixLen]
            have hac : a ≤ c := hleast.1
            have : b - a + 1 = (c - a + 1) + (b - c) := by omega
            rw [this, Nat.cast_add, mul_add]
          _ ≤ countOn (A + B) a c + countOn (A + B) (c + 1) b :=
            add_le_add hblock hsuffix
          _ = countOn (A + B) a b := by exact_mod_cast hcountSplit.symm

theorem interval_density_expansion {A B : Set ℕ} {k a b : ℕ}
    (hBasis : IsAdditiveBasisOfOrder B k) (hk : 0 < k) (hab : a ≤ b)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hlower : ∀ d, a ≤ d → d ≤ b →
      p * ((d - a + 1 : ℕ) : ℝ) ≤ countOn A a d) :
    densityGain p k * ((b - a + 1 : ℕ) : ℝ) ≤ countOn (A + B) a b := by
  exact interval_density_expansion_aux hBasis hk (b - a + 1) a b p le_rfl
    hab hp0 hp1 hlower

/-- **Erdős Problem 35.**  If `B` is an additive basis of order `k` and
contains zero, then adding `B` increases Schnirelmann density by at least
`α(1-α)/k`, where `α` is the Schnirelmann density of `A`. -/
theorem erdos_35 (A B : Set ℕ) (k : ℕ) (_hzero : 0 ∈ B)
    (hBasis : IsAdditiveBasisOfOrder B k) :
    schnirelmannDensity A +
        schnirelmannDensity A * (1 - schnirelmannDensity A) / k ≤
      schnirelmannDensity (A + B) := by
  have hk : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hk0
    subst k
    have htwo : 2 ∈ (0 • B : Set ℕ) := by rw [hBasis]; simp
    simp at htwo
  let α := schnirelmannDensity A
  have hα0 : 0 ≤ α := schnirelmannDensity_nonneg
  have hα1 : α ≤ 1 := schnirelmannDensity_le_one
  rw [le_schnirelmannDensity_iff]
  intro n hn
  rw [le_div_iff₀ (by exact_mod_cast hn)]
  have hinterval := interval_density_expansion hBasis hk
    (a := 1) (b := n) (p := α) (by omega) hα0 hα1 (by
      intro d hd1 hdn
      have hdensity := countIn_density A d
      rw [countIn_eq_countOn_one] at hdensity
      simpa [show d - 1 + 1 = d by omega] using hdensity)
  change (α + α * (1 - α) / k) * (n : ℝ) ≤ countIn (A + B) n
  rw [countIn_eq_countOn_one]
  have hnlen : n - 1 + 1 = n := by omega
  rw [hnlen] at hinterval
  calc
    (α + α * (1 - α) / k) * (n : ℝ) = densityGain α k * (n : ℝ) := by
      dsimp [densityGain, expansionFactor]
      ring
    _ ≤ countOn (A + B) 1 n := hinterval

lemma zero_not_basis_order_zero (B : Set ℕ) : ¬IsAdditiveBasisOfOrder B 0 := by
  intro h
  have htwo : 2 ∈ (0 • B : Set ℕ) := by rw [h]; simp
  simp at htwo

/-! ## The analytic comparison

This is the elementary comparison which turns Plünnecke's stronger exponent
bound into the precise estimate asked for by Erdős. -/

/-- For `0 ≤ α ≤ 1` and positive `k`, Plünnecke's exponent bound is at
least the polynomial bound in Problem 35. -/
lemma erdos35_le_rpow {α : ℝ} {k : ℕ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (hk : 0 < k) :
    α + α * (1 - α) / k ≤ α ^ (1 - (k : ℝ)⁻¹) := by
  rcases hα₀.eq_or_lt with rfl | hα
  · simpa only [zero_add, zero_mul, zero_div] using
      Real.zero_rpow_nonneg (1 - (k : ℝ)⁻¹)
  let r : ℝ := (k : ℝ)⁻¹
  let u : ℝ := (1 - α) / k
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hr₀ : 0 ≤ r := by simp [r, hkR.le]
  have hr₁ : r ≤ 1 := by
    dsimp [r]
    rw [inv_le_one₀ hkR]
    exact_mod_cast hk
  have hs : (-1 : ℝ) ≤ α - 1 := by linarith
  have hroot : α ^ r ≤ 1 - u := by
    have h := rpow_one_add_le_one_add_mul_self hs hr₀ hr₁
    dsimp [r, u] at h ⊢
    convert h using 1 <;> field_simp <;> ring
  have hu₀ : 0 ≤ u := div_nonneg (sub_nonneg.mpr hα₁) hkR.le
  have hq₀ : 0 ≤ 1 + u := by positivity
  have hroot_pos : 0 < α ^ r := Real.rpow_pos_of_pos hα r
  have hprod : (1 + u) * α ^ r ≤ 1 := by
    calc
      (1 + u) * α ^ r ≤ (1 + u) * (1 - u) :=
        mul_le_mul_of_nonneg_left hroot hq₀
      _ ≤ 1 := by nlinarith [sq_nonneg u]
  have hquot : 1 + u ≤ 1 / α ^ r := by
    exact (le_div_iff₀ hroot_pos).2 (by simpa [mul_comm] using hprod)
  rw [Real.rpow_sub hα, Real.rpow_one]
  calc
    α + α * (1 - α) / k = α * (1 + u) := by
      dsimp [u]
      ring_nf
    _ ≤ α * (1 / α ^ r) := mul_le_mul_of_nonneg_left hquot hα.le
    _ = α / α ^ (k : ℝ)⁻¹ := by simp [r, div_eq_mul_inv]

end Erdos35

#print axioms Erdos35.erdos_35

alias _root_.Erdos35.erdos35 := _root_.Erdos35.erdos_35
