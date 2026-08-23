/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1025.
https://www.erdosproblems.com/forum/thread/1025

Informal authors:
- David Conlon
- Jacob Fox
- Benny Sudakov

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1025.md
-/
import Mathlib
import ErdosProblems.Erdos202

/-!
# Erdős Problem 1025

For every map from the unordered pairs of an `n`-element set to a point outside the
pair, let an independent set be a set containing no pair together with its image.
This file proves that the largest size which is guaranteed for every such map is
of order `sqrt n`.

The lower bound is the three-uniform case of Spencer's deletion argument.  The
upper bound is the square-grid construction of Conlon--Fox--Sudakov, specialized
to maps from pairs to points.
-/

open scoped BigOperators

namespace Erdos1025

open Filter Finset Function
open Asymptotics

noncomputable section

/-- The type of unordered pairs of distinct elements of `α`. -/
abbrev Pair (α : Type*) := {e : Sym2 α // ¬ e.IsDiag}

namespace Pair

variable {α β : Type*}

/-- The two-element finset underlying an unordered pair. -/
def vertices [DecidableEq α] (e : Pair α) : Finset α := e.1.toFinset

@[simp]
lemma card_vertices [DecidableEq α] (e : Pair α) : e.vertices.card = 2 :=
  Sym2.card_toFinset_of_not_isDiag e.1 e.2

/-- Construct an unordered pair from two distinct elements. -/
def mk {x y : α} (h : x ≠ y) : Pair α :=
  ⟨s(x, y), by simpa [Sym2.isDiag_iff_proj_eq] using h⟩

@[simp]
lemma vertices_mk [DecidableEq α] {x y : α} (h : x ≠ y) :
    (mk h).vertices = {x, y} := by
  simp [vertices, mk, Sym2.toFinset_mk_eq]

@[simp]
lemma left_mem_vertices [DecidableEq α] {x y : α} (h : x ≠ y) :
    x ∈ (mk h).vertices := by simp

@[simp]
lemma right_mem_vertices [DecidableEq α] {x y : α} (h : x ≠ y) :
    y ∈ (mk h).vertices := by simp

/-- Transport unordered pairs along an equivalence. -/
def map (e : α ≃ β) : Pair α ≃ Pair β where
  toFun p := ⟨p.1.map e, by
    rw [Sym2.isDiag_map e.injective]
    exact p.2⟩
  invFun p := ⟨p.1.map e.symm, by
    rw [Sym2.isDiag_map e.symm.injective]
    exact p.2⟩
  left_inv p := by
    apply Subtype.ext
    simp [Sym2.map_map]
  right_inv p := by
    apply Subtype.ext
    simp [Sym2.map_map]

end Pair

/-- The value of a set mapping never equals either endpoint of its input pair. -/
def AvoidsEndpoints {α : Type*} [DecidableEq α] (f : Pair α → α) : Prop :=
  ∀ e, f e ∉ e.vertices

/-- `X` is independent when it contains no input pair together with its image. -/
def Independent {α : Type*} [DecidableEq α] (f : Pair α → α) (X : Finset α) : Prop :=
  ∀ e, e.vertices ⊆ X → f e ∉ X

/-- `k` is universally guaranteed for maps on the canonical `n`-element set. -/
def Guaranteed (n k : ℕ) : Prop :=
  k ≤ n ∧ ∀ f : Pair (Fin n) → Fin n, AvoidsEndpoints f →
    ∃ X : Finset (Fin n), Independent f X ∧ k ≤ X.card

/-- The largest universally guaranteed independent-set size. -/
noncomputable def g (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (Guaranteed n) n

lemma guaranteed_zero (n : ℕ) : Guaranteed n 0 := by
  refine ⟨Nat.zero_le n, ?_⟩
  intro f hf
  exact ⟨∅, by simp [Independent], Nat.zero_le _⟩

lemma g_le (n : ℕ) : g n ≤ n := by
  classical
  exact Nat.findGreatest_le n

lemma g_spec (n : ℕ) : Guaranteed n (g n) := by
  classical
  exact Nat.findGreatest_spec (m := 0) (Nat.zero_le n) (guaranteed_zero n)

lemma le_g_of_guaranteed {n k : ℕ} (h : Guaranteed n k) : k ≤ g n := by
  classical
  exact Nat.le_findGreatest h.1 h

/-! ### Explicit finite Bernoulli averages

These helper lemmas keep the probabilistic argument as finite sums over a
powerset. -/

open Erdos202.ParkPham

lemma sum_bernoulliMass_indicator_superset {V : Type*} [Fintype V] [DecidableEq V]
    (X T : Finset V) (hTX : T ⊆ X) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ W ∈ X.powerset,
        bernoulliMass X W p * (if T ⊆ W then (1 : ℝ) else 0)) = p ^ T.card := by
  calc
    (∑ W ∈ X.powerset,
        bernoulliMass X W p * (if T ⊆ W then (1 : ℝ) else 0)) =
        muP X (upClosureIn X {T}) p := by
          rw [upClosureIn_singleton X T hTX]
          simp only [muP, Finset.mem_filter, Finset.mem_powerset]
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro W hW
          simp [Finset.mem_powerset.mp hW]
    _ = p ^ T.card := muP_upClosure_single X T hTX hp0 hp1

lemma sum_bernoulliMass_contained_count {V : Type*} [Fintype V] [DecidableEq V]
    (X : Finset V) (A : Finset (Finset V)) {k : ℕ}
    (hAX : ∀ T ∈ A, T ⊆ X) (hcard : ∀ T ∈ A, T.card = k)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ W ∈ X.powerset,
        bernoulliMass X W p * ((A.filter (· ⊆ W)).card : ℝ)) =
      p ^ k * A.card := by
  calc
    (∑ W ∈ X.powerset,
        bernoulliMass X W p * ((A.filter (· ⊆ W)).card : ℝ)) =
        ∑ W ∈ X.powerset,
          ∑ T ∈ A, bernoulliMass X W p * (if T ⊆ W then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro W hW
            rw [← Finset.mul_sum, Finset.sum_boole]
    _ = ∑ T ∈ A,
          ∑ W ∈ X.powerset,
            bernoulliMass X W p * (if T ⊆ W then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ T ∈ A, p ^ T.card := by
          apply Finset.sum_congr rfl
          intro T hT
          exact sum_bernoulliMass_indicator_superset X T (hAX T hT) hp0 hp1
    _ = p ^ k * A.card := by
          rw [Finset.sum_congr rfl (fun T hT => by rw [hcard T hT])]
          simp [mul_comm]

lemma sum_bernoulliMass_card {V : Type*} [Fintype V] [DecidableEq V]
    (X : Finset V) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ W ∈ X.powerset, bernoulliMass X W p * (W.card : ℝ)) =
      p * X.card := by
  calc
    (∑ W ∈ X.powerset, bernoulliMass X W p * (W.card : ℝ)) =
        ∑ W ∈ X.powerset,
          ∑ v ∈ X, bernoulliMass X W p * (if v ∈ W then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro W hW
            have hWX : W ⊆ X := Finset.mem_powerset.mp hW
            have hfilter : X.filter (· ∈ W) = W := by
              ext v
              simp only [Finset.mem_filter]
              constructor
              · exact And.right
              · intro hv
                exact ⟨hWX hv, hv⟩
            rw [show (W.card : ℝ) =
                ∑ v ∈ X, if v ∈ W then (1 : ℝ) else 0 by
              rw [Finset.sum_boole]
              rw [hfilter]]
            rw [Finset.mul_sum]
    _ = ∑ v ∈ X,
          ∑ W ∈ X.powerset,
            bernoulliMass X W p * (if ({v} : Finset V) ⊆ W then (1 : ℝ) else 0) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro v hv
          apply Finset.sum_congr rfl
          intro W hW
          simp
    _ = ∑ _v ∈ X, p := by
          apply Finset.sum_congr rfl
          intro v hv
          simpa using sum_bernoulliMass_indicator_superset X ({v} : Finset V)
            (by simpa using hv) hp0 hp1
    _ = p * X.card := by simp [mul_comm]

lemma exists_ge_of_bernoulli_average_ge {V : Type*} [Fintype V] [DecidableEq V]
    (X : Finset V) {p a : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (F : Finset V → ℝ)
    (havg : a ≤ ∑ W ∈ X.powerset, bernoulliMass X W p * F W) :
    ∃ W ∈ X.powerset, a ≤ F W := by
  by_contra hnone
  push_neg at hnone
  have hsum_lt :
      (∑ W ∈ X.powerset, bernoulliMass X W p * F W) <
        ∑ W ∈ X.powerset, bernoulliMass X W p * a := by
    apply Finset.sum_lt_sum
    · intro W hW
      exact mul_le_mul_of_nonneg_left (le_of_lt (hnone W hW))
        (bernoulliMass_nonneg hp0 hp1)
    · have hone : (1 : ℝ) = ∑ W ∈ X.powerset, bernoulliMass X W p := by
        symm
        exact sum_bernoulliMass_eq_one X (by ring)
      have hposmass : ∃ W ∈ X.powerset, 0 < bernoulliMass X W p := by
        by_contra hz
        push_neg at hz
        have hallzero : ∀ W ∈ X.powerset, bernoulliMass X W p = 0 := by
          intro W hW
          exact le_antisymm (hz W hW) (bernoulliMass_nonneg hp0 hp1)
        have : (1 : ℝ) = 0 := by
          calc
            (1 : ℝ) = ∑ W ∈ X.powerset, bernoulliMass X W p := hone
            _ = 0 := by
              apply Finset.sum_eq_zero
              intro W hW
              exact hallzero W hW
        norm_num at this
      rcases hposmass with ⟨W, hW, hmass⟩
      refine ⟨W, hW, ?_⟩
      exact mul_lt_mul_of_pos_left (hnone W hW) hmass
  have hconst :
      (∑ W ∈ X.powerset, bernoulliMass X W p * a) = a := by
    rw [← Finset.sum_mul, sum_bernoulliMass_eq_one X (by ring), one_mul]
  linarith

/-! ## The Spencer lower bound -/

/-- The three-element set generated by a pair and the value of the map. -/
def triple {α : Type*} [DecidableEq α] (f : Pair α → α) (e : Pair α) : Finset α :=
  insert (f e) e.vertices

lemma card_triple {α : Type*} [DecidableEq α] {f : Pair α → α}
    (hf : AvoidsEndpoints f) (e : Pair α) : (triple f e).card = 3 := by
  rw [triple, card_insert_of_notMem (hf e), Pair.card_vertices]

/-- The finite family of all triples generated by a set mapping. -/
def tripleFamily {α : Type*} [Fintype α] [DecidableEq α]
    (f : Pair α → α) : Finset (Finset α) :=
  Finset.univ.image (triple f)

lemma mem_tripleFamily {α : Type*} [Fintype α] [DecidableEq α]
    (f : Pair α → α) (e : Pair α) : triple f e ∈ tripleFamily f := by
  exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩

lemma tripleFamily_card_le_sq {α : Type*} [Fintype α] [DecidableEq α]
    (f : Pair α → α) :
    (tripleFamily f).card ≤ (Fintype.card α) ^ 2 := by
  calc
    (tripleFamily f).card ≤ Fintype.card (Pair α) := by
      simpa [tripleFamily] using Finset.card_image_le (s := (Finset.univ : Finset (Pair α)))
        (f := triple f)
    _ = (Fintype.card α).choose 2 := Sym2.card_subtype_not_diag
    _ ≤ (Fintype.card α) ^ 2 := Nat.choose_le_pow _ _

/-- Bernoulli sampling followed by deleting one vertex from every surviving
three-set.  This is the finite probabilistic core of Spencer's lower bound. -/
lemma exists_threeSetFree_large {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset (Finset α))
    (hAcard : ∀ T ∈ A, T.card = 3)
    (hcount : A.card ≤ (Fintype.card α) ^ 2)
    (hn : 1 ≤ Fintype.card α) :
    ∃ U : Finset α,
      (∀ T ∈ A, ¬ T ⊆ U) ∧
      Real.sqrt (Fintype.card α : ℝ) / 4 ≤ (U.card : ℝ) := by
  classical
  let n : ℕ := Fintype.card α
  let X : Finset α := Finset.univ
  let p : ℝ := 1 / (2 * Real.sqrt n)
  let Y : Finset α → ℝ := fun W =>
    (W.card : ℝ) - ((A.filter (fun T => T ⊆ W)).card : ℝ)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = n := by
    rw [Real.sq_sqrt (le_of_lt hn0)]
  have hp0 : 0 ≤ p := by positivity
  have hp1 : p ≤ 1 := by
    dsimp [p]
    have hsqrt_one : 1 ≤ Real.sqrt (n : ℝ) := by
      rw [Real.one_le_sqrt]
      exact_mod_cast hn
    have hden : 0 < 2 * Real.sqrt (n : ℝ) := by positivity
    rw [div_le_iff₀ hden]
    nlinarith
  have hAX : ∀ T ∈ A, T ⊆ X := by
    intro T hT
    exact Finset.subset_univ T
  have havg_eq :
      (∑ W ∈ X.powerset, bernoulliMass X W p * Y W) =
        p * n - p ^ 3 * A.card := by
    rw [show (∑ W ∈ X.powerset, bernoulliMass X W p * Y W) =
        (∑ W ∈ X.powerset, bernoulliMass X W p * (W.card : ℝ)) -
        ∑ W ∈ X.powerset,
          bernoulliMass X W p * ((A.filter (fun T => T ⊆ W)).card : ℝ) by
      simp only [Y, mul_sub, Finset.sum_sub_distrib]]
    rw [sum_bernoulliMass_card X hp0 hp1,
      sum_bernoulliMass_contained_count X A hAX hAcard hp0 hp1]
    simp [X, n]
  have hcount_real : (A.card : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast hcount
  have havg_lower :
      Real.sqrt (n : ℝ) / 4 ≤ p * n - p ^ 3 * A.card := by
    dsimp [p]
    have hp3 : 0 ≤ (1 / (2 * Real.sqrt (n : ℝ))) ^ 3 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hcount_real hp3
    field_simp
    nlinarith [hsqrt_sq]
  have havg :
      Real.sqrt (n : ℝ) / 4 ≤
        ∑ W ∈ X.powerset, bernoulliMass X W p * Y W := by
    rw [havg_eq]
    exact havg_lower
  obtain ⟨W, hWX, hWY⟩ :=
    exists_ge_of_bernoulli_average_ge X hp0 hp1 Y havg
  let B : Finset (Finset α) := A.filter (fun T => T ⊆ W)
  let pick : {T // T ∈ B} → α := fun T =>
    Classical.choose <| by
      have hTcard : T.1.card = 3 := hAcard T.1 (Finset.mem_filter.mp T.2).1
      exact Finset.card_pos.mp (hTcard.trans_gt (by norm_num))
  have hpick_mem : ∀ T : {T // T ∈ B}, pick T ∈ T.1 := by
    intro T
    exact Classical.choose_spec <| by
      have hTcard : T.1.card = 3 := hAcard T.1 (Finset.mem_filter.mp T.2).1
      exact Finset.card_pos.mp (hTcard.trans_gt (by norm_num))
  let deleted : Finset α := B.attach.image pick
  let U : Finset α := W \ deleted
  have hdeletedW : deleted ⊆ W := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨T, hT, rfl⟩
    exact (Finset.mem_filter.mp T.2).2 (hpick_mem T)
  have hUcard_nat : W.card - B.card ≤ U.card := by
    have hd : deleted.card ≤ B.card := by
      simpa [deleted] using Finset.card_image_le (s := B.attach) (f := pick)
    calc
      W.card - B.card ≤ W.card - deleted.card := Nat.sub_le_sub_left hd _
      _ = U.card := by
        symm
        simpa [U] using Finset.card_sdiff_of_subset hdeletedW
  have hYU : Y W ≤ (U.card : ℝ) := by
    by_cases hBW : B.card ≤ W.card
    · rw [show Y W = ((W.card - B.card : ℕ) : ℝ) by
        simp only [Y, B]
        exact (Nat.cast_sub hBW).symm]
      exact_mod_cast hUcard_nat
    · have hnonpos : Y W ≤ 0 := by
        simp only [Y, B]
        exact sub_nonpos.mpr (by exact_mod_cast Nat.le_of_not_ge hBW)
      exact hnonpos.trans (Nat.cast_nonneg U.card)
  refine ⟨U, ?_, hWY.trans hYU⟩
  intro T hTA hTU
  have hTW : T ⊆ W := hTU.trans Finset.sdiff_subset
  have hTB : T ∈ B := Finset.mem_filter.mpr ⟨hTA, hTW⟩
  let TT : {T // T ∈ B} := ⟨T, hTB⟩
  have hpdel : pick TT ∈ deleted :=
    Finset.mem_image.mpr ⟨TT, by simp, rfl⟩
  have hpU : pick TT ∈ U := hTU (hpick_mem TT)
  exact (Finset.mem_sdiff.mp hpU).2 hpdel

/-- Every admissible set mapping has an independent set of real cardinality
at least one quarter of the square root of the order. -/
lemma exists_independent_sqrt {α : Type*} [Fintype α] [DecidableEq α]
    (f : Pair α → α) (hf : AvoidsEndpoints f)
    (hn : 1 ≤ Fintype.card α) :
    ∃ U : Finset α, Independent f U ∧
      Real.sqrt (Fintype.card α : ℝ) / 4 ≤ (U.card : ℝ) := by
  classical
  let A := tripleFamily f
  obtain ⟨U, hfree, hcard⟩ := exists_threeSetFree_large A
    (fun T hT => by
      rcases Finset.mem_image.mp hT with ⟨e, he, rfl⟩
      exact card_triple hf e)
    (tripleFamily_card_le_sq f) hn
  refine ⟨U, ?_, hcard⟩
  intro e he hfe
  exact hfree (triple f e) (mem_tripleFamily f e) <| by
    intro x hx
    simp only [triple, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hfe
    · exact he hx

/-! ## The square-grid construction -/

/-- A square grid together with some extra vertices. -/
abbrev Padded (q s : ℕ) := (Fin q × Fin q) ⊕ Fin s

lemma exists_outside_pair {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 3 ≤ Fintype.card α) (e : Pair α) : ∃ x : α, x ∉ e.vertices := by
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset α) ⊆ e.vertices := by
    intro x hx
    exact h x
  have := Finset.card_le_card hsub
  simp only [Finset.card_univ, Pair.card_vertices] at this
  omega

/-- A chosen third point outside an unordered pair. -/
def thirdVertex {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 3 ≤ Fintype.card α) (e : Pair α) : α :=
  Classical.choose (exists_outside_pair hcard e)

lemma thirdVertex_not_mem {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 3 ≤ Fintype.card α) (e : Pair α) :
    thirdVertex hcard e ∉ e.vertices :=
  Classical.choose_spec (exists_outside_pair hcard e)

/-- A symmetric fallback value.  Only its off-diagonal behavior is used. -/
def fallbackSym {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 3 ≤ Fintype.card α) (e : Sym2 α) : α :=
  if he : ¬ e.IsDiag then thirdVertex hcard ⟨e, he⟩ else e.out.1

lemma fallbackSym_not_mem {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 3 ≤ Fintype.card α) (e : Pair α) :
    fallbackSym hcard e.1 ∉ e.vertices := by
  simp only [fallbackSym, e.2, dite_true]
  exact thirdVertex_not_mem hcard e

lemma fallbackSym_mk_not_mem {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 3 ≤ Fintype.card α) {a b : α} (hab : a ≠ b) :
    fallbackSym hcard s(a, b) ∉ ({a, b} : Finset α) := by
  simpa [Pair.mk, Pair.vertices, Sym2.toFinset_mk_eq] using
    fallbackSym_not_mem hcard (Pair.mk hab)

/-- The crossed-corner rule, with the symmetric fallback in all other cases. -/
def gridValue {q s : ℕ} (hcard : 3 ≤ Fintype.card (Padded q s))
    (a b : Padded q s) : Padded q s :=
  match a, b with
  | Sum.inl a, Sum.inl b =>
      if a.1 < b.1 ∧ a.2 ≠ b.2 then Sum.inl (a.1, b.2)
      else if b.1 < a.1 ∧ b.2 ≠ a.2 then Sum.inl (b.1, a.2)
      else fallbackSym hcard s((Sum.inl a : Padded q s), Sum.inl b)
  | _, _ => fallbackSym hcard s(a, b)

lemma gridValue_comm {q s : ℕ} (hcard : 3 ≤ Fintype.card (Padded q s))
    (a b : Padded q s) : gridValue hcard a b = gridValue hcard b a := by
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          by_cases h₁ : a.1 < b.1 ∧ a.2 ≠ b.2
          · have h₂ : ¬ (b.1 < a.1 ∧ b.2 ≠ a.2) := by
              intro h₂
              exact (asymm h₁.1 h₂.1)
            rw [gridValue, gridValue, if_pos h₁, if_neg h₂, if_pos h₁]
          · by_cases h₂ : b.1 < a.1 ∧ b.2 ≠ a.2
            · rw [gridValue, gridValue, if_neg h₁, if_pos h₂, if_pos h₂]
            · have heq : s((Sum.inl a : Padded q s), Sum.inl b) =
                  s((Sum.inl b : Padded q s), Sum.inl a) := Sym2.eq_swap
              rw [gridValue, gridValue, if_neg h₁, if_neg h₂, if_neg h₂, if_neg h₁,
                heq]
      | inr b =>
          have heq : s((Sum.inl a : Padded q s), Sum.inr b) =
              s((Sum.inr b : Padded q s), Sum.inl a) := Sym2.eq_swap
          change fallbackSym hcard s((Sum.inl a : Padded q s), Sum.inr b) =
            fallbackSym hcard s((Sum.inr b : Padded q s), Sum.inl a)
          rw [heq]
  | inr a =>
      cases b with
      | inl b =>
          have heq : s((Sum.inr a : Padded q s), Sum.inl b) =
              s((Sum.inl b : Padded q s), Sum.inr a) := Sym2.eq_swap
          change fallbackSym hcard s((Sum.inr a : Padded q s), Sum.inl b) =
            fallbackSym hcard s((Sum.inl b : Padded q s), Sum.inr a)
          rw [heq]
      | inr b =>
          have heq : s((Sum.inr a : Padded q s), Sum.inr b) =
              s((Sum.inr b : Padded q s), Sum.inr a) := Sym2.eq_swap
          change fallbackSym hcard s((Sum.inr a : Padded q s), Sum.inr b) =
            fallbackSym hcard s((Sum.inr b : Padded q s), Sum.inr a)
          rw [heq]

/-- The CFS grid set mapping. -/
def gridMap {q s : ℕ} (hcard : 3 ≤ Fintype.card (Padded q s)) :
    Pair (Padded q s) → Padded q s := fun e =>
  e.1.lift ⟨gridValue hcard, gridValue_comm hcard⟩

@[simp]
lemma gridMap_mk {q s : ℕ} (hcard : 3 ≤ Fintype.card (Padded q s))
    {a b : Padded q s} (hab : a ≠ b) :
    gridMap hcard (Pair.mk hab) = gridValue hcard a b := by
  simp [gridMap, Pair.mk]

lemma gridValue_corner {q s : ℕ} (hcard : 3 ≤ Fintype.card (Padded q s))
    {x x' y z : Fin q} (hxx : x < x') (hzy : z ≠ y) :
    gridValue hcard (Sum.inl (x, z)) (Sum.inl (x', y)) = Sum.inl (x, y) := by
  rw [gridValue, if_pos ⟨hxx, hzy⟩]

lemma gridMap_corner {q s : ℕ} (hcard : 3 ≤ Fintype.card (Padded q s))
    {x x' y z : Fin q} (hxx : x < x') (hzy : z ≠ y) :
    gridMap hcard (Pair.mk (show (Sum.inl (x, z) : Padded q s) ≠ Sum.inl (x', y) by
      intro h
      have hpair : (x, z) = (x', y) := Sum.inl.inj h
      exact (ne_of_lt hxx) (congrArg Prod.fst hpair))) = Sum.inl (x, y) := by
  rw [gridMap_mk]
  exact gridValue_corner hcard hxx hzy

lemma gridValue_not_mem {q s : ℕ} (hcard : 3 ≤ Fintype.card (Padded q s))
    {a b : Padded q s} (hab : a ≠ b) :
    gridValue hcard a b ∉ ({a, b} : Finset (Padded q s)) := by
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          by_cases h₁ : a.1 < b.1 ∧ a.2 ≠ b.2
          · rw [gridValue, if_pos h₁]
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            constructor
            · intro heq
              have hsnd := congrArg Prod.snd (Sum.inl.inj heq)
              exact h₁.2 hsnd.symm
            · intro heq
              have hfst := congrArg Prod.fst (Sum.inl.inj heq)
              exact (ne_of_lt h₁.1) hfst
          · by_cases h₂ : b.1 < a.1 ∧ b.2 ≠ a.2
            · rw [gridValue, if_neg h₁, if_pos h₂]
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
              constructor
              · intro heq
                have hfst := congrArg Prod.fst (Sum.inl.inj heq)
                exact (ne_of_lt h₂.1) hfst
              · intro heq
                have hsnd := congrArg Prod.snd (Sum.inl.inj heq)
                exact h₂.2 hsnd.symm
            · rw [gridValue, if_neg h₁, if_neg h₂]
              exact fallbackSym_mk_not_mem hcard hab
      | inr b =>
          change fallbackSym hcard s((Sum.inl a : Padded q s), Sum.inr b) ∉
            ({Sum.inl a, Sum.inr b} : Finset (Padded q s))
          exact fallbackSym_mk_not_mem hcard hab
  | inr a =>
      cases b with
      | inl b =>
          change fallbackSym hcard s((Sum.inr a : Padded q s), Sum.inl b) ∉
            ({Sum.inr a, Sum.inl b} : Finset (Padded q s))
          exact fallbackSym_mk_not_mem hcard hab
      | inr b =>
          change fallbackSym hcard s((Sum.inr a : Padded q s), Sum.inr b) ∉
            ({Sum.inr a, Sum.inr b} : Finset (Padded q s))
          exact fallbackSym_mk_not_mem hcard hab

lemma gridMap_avoids {q s : ℕ} (hcard : 3 ≤ Fintype.card (Padded q s)) :
    AvoidsEndpoints (gridMap hcard) := by
  rintro ⟨e, he⟩
  induction e using Sym2.ind with
  | h a b =>
      have hab : a ≠ b := by
        rwa [Sym2.isDiag_iff_proj_eq] at he
      simpa [gridMap, Pair.vertices, Sym2.toFinset_mk_eq] using
        gridValue_not_mem hcard hab

/-- A point is the unique selected point in its first-coordinate fibre. -/
def UniqueFirst {q : ℕ} (C : Finset (Fin q × Fin q)) (p : Fin q × Fin q) : Prop :=
  ∀ r ∈ C, r.1 = p.1 → r = p

/-- The specialized CFS pruning argument: the core contributes at most `2q`
points and the padded part contributes at most `s` points. -/
lemma gridMap_independent_card {q s : ℕ}
    (hcard : 3 ≤ Fintype.card (Padded q s))
    (X : Finset (Padded q s)) (hX : Independent (gridMap hcard) X) :
    X.card ≤ 2 * q + s := by
  classical
  let C : Finset (Fin q × Fin q) := X.toLeft
  let U : Finset (Fin q × Fin q) := C.filter (UniqueFirst C)
  let V : Finset (Fin q × Fin q) := C.filter (fun p => ¬ UniqueFirst C p)
  have hU : U.card ≤ q := by
    calc
      U.card ≤ (Finset.univ : Finset (Fin q)).card := by
        apply Finset.card_le_card_of_injOn Prod.fst
        · intro p hp
          exact Finset.mem_univ p.1
        · intro p hp p' hp' heq
          have hp_unique : UniqueFirst C p := (Finset.mem_filter.mp hp).2
          exact (hp_unique p' (Finset.mem_filter.mp hp').1 heq.symm).symm
      _ = q := by simp
  have no_equal_second_of_lt :
      ∀ {p p' : Fin q × Fin q}, p ∈ V → p' ∈ V → p.2 = p'.2 → p.1 < p'.1 → False := by
    intro p p' hp hp' hsnd hfst
    have hp_not_unique : ¬ UniqueFirst C p := (Finset.mem_filter.mp hp).2
    simp only [UniqueFirst] at hp_not_unique
    push_neg at hp_not_unique
    obtain ⟨r, hrC, hrfst, hrne⟩ := hp_not_unique
    have hrsnd : r.2 ≠ p'.2 := by
      intro hrsnd
      apply hrne
      apply Prod.ext
      · exact hrfst
      · exact hrsnd.trans hsnd.symm
    have hr_lt : r.1 < p'.1 := by simpa [hrfst] using hfst
    have hep : (Sum.inl r : Padded q s) ≠ Sum.inl p' := by
      intro heq
      have : r = p' := Sum.inl.inj heq
      exact (ne_of_lt hr_lt) (congrArg Prod.fst this)
    have hrX : (Sum.inl r : Padded q s) ∈ X := by simpa [C] using hrC
    have hp'X : (Sum.inl p' : Padded q s) ∈ X := by
      simpa [C] using (Finset.mem_filter.mp hp').1
    have hpX : (Sum.inl p : Padded q s) ∈ X := by
      simpa [C] using (Finset.mem_filter.mp hp).1
    have hendpoints : (Pair.mk hep).vertices ⊆ X := by
      simp only [Pair.vertices_mk, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hrX, hp'X⟩
    have hout := hX (Pair.mk hep) hendpoints
    have hcorner : gridMap hcard (Pair.mk hep) = (Sum.inl p : Padded q s) := by
      rw [gridMap_mk, gridValue_corner hcard hr_lt hrsnd]
      exact congrArg Sum.inl (Prod.ext hrfst hsnd.symm)
    exact hout (hcorner ▸ hpX)
  have hV : V.card ≤ q := by
    calc
      V.card ≤ (Finset.univ : Finset (Fin q)).card := by
        apply Finset.card_le_card_of_injOn Prod.snd
        · intro p hp
          exact Finset.mem_univ p.2
        · intro p hp p' hp' hsnd
          by_cases hfst : p.1 = p'.1
          · exact Prod.ext hfst hsnd
          · rcases lt_or_gt_of_ne hfst with hlt | hgt
            · exact False.elim (no_equal_second_of_lt hp hp' hsnd hlt)
            · exact False.elim (no_equal_second_of_lt hp' hp hsnd.symm hgt)
      _ = q := by simp
  have hC : C.card ≤ 2 * q := by
    have hpartition := C.card_filter_add_card_filter_not (UniqueFirst C)
    have hUV : U.card + V.card = C.card := by simpa [U, V] using hpartition
    omega
  have hright : X.toRight.card ≤ s := by
    calc
      X.toRight.card ≤ (Finset.univ : Finset (Fin s)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = s := by simp
  have hsplit := Finset.card_toLeft_add_card_toRight (u := X)
  change X.toLeft.card ≤ 2 * q at hC
  omega

/-! ## Transport and padding -/

lemma sym2_toFinset_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (p : Sym2 α) :
    (p.map e).toFinset = p.toFinset.map e.toEmbedding := by
  induction p using Sym2.ind with
  | h x y =>
      simp [Sym2.toFinset_mk_eq, Sym2.map_mk]

@[simp]
lemma Pair.vertices_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (p : Pair α) :
    ((Pair.map e) p).vertices = p.vertices.map e.toEmbedding := by
  exact sym2_toFinset_map e p.1

/-- Transport a set mapping along an equivalence of vertex types. -/
def transportMap {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (f : Pair α → α) : Pair β → β := fun p =>
  e (f ((Pair.map e).symm p))

lemma transportMap_avoids {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) {f : Pair α → α} (hf : AvoidsEndpoints f) :
    AvoidsEndpoints (transportMap e f) := by
  intro p hp
  let p' : Pair α := (Pair.map e).symm p
  have hverts : p.vertices = p'.vertices.map e.toEmbedding := by
    have h := Pair.vertices_map e p'
    simpa [p'] using h
  rw [hverts] at hp
  have : f p' ∈ p'.vertices := by simpa [transportMap, p'] using hp
  exact hf p' this

/-- Pulling an independent set back along an equivalence preserves independence. -/
lemma independent_map_symm {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (f : Pair α → α) (X : Finset β)
    (hX : Independent (transportMap e f) X) :
    Independent f (X.map e.symm.toEmbedding) := by
  intro p hp hfp
  let pe : Pair β := Pair.map e p
  have hpe : pe.vertices ⊆ X := by
    intro x hx
    rw [Pair.vertices_map] at hx
    rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hypre : y ∈ X.map e.symm.toEmbedding := hp hy
    simpa using hypre
  have hout : transportMap e f pe ∉ X := hX pe hpe
  apply hout
  have : e (f p) ∈ X := by simpa using hfp
  simpa [transportMap, pe] using this

lemma padded_card (q s : ℕ) : Fintype.card (Padded q s) = q * q + s := by
  simp [Padded]

/-- For every `n ≥ 4`, the padded square grid supplies an admissible mapping
whose independent sets have size at most `4 * floor(sqrt n)`. -/
lemma upper_witness (n : ℕ) (hn : 4 ≤ n) :
    ∃ f : Pair (Fin n) → Fin n,
      AvoidsEndpoints f ∧
      ∀ X : Finset (Fin n), Independent f X → X.card ≤ 4 * Nat.sqrt n := by
  classical
  let q : ℕ := Nat.sqrt n
  let s : ℕ := n - q * q
  have hsq : q * q ≤ n := by simpa [q] using Nat.sqrt_le n
  have hs : s ≤ 2 * q := by
    have hadd : n ≤ q * q + q + q := by simpa [q] using Nat.sqrt_le_add n
    dsimp [s]
    omega
  have hcard_eq : Fintype.card (Padded q s) = n := by
    rw [padded_card]
    dsimp [s]
    omega
  have hcard : 3 ≤ Fintype.card (Padded q s) := by
    rw [hcard_eq]
    omega
  let e : Padded q s ≃ Fin n := Fintype.equivOfCardEq (by simpa using hcard_eq)
  let f : Pair (Fin n) → Fin n := transportMap e (gridMap hcard)
  refine ⟨f, transportMap_avoids e (gridMap_avoids hcard), ?_⟩
  intro X hX
  let X' : Finset (Padded q s) := X.map e.symm.toEmbedding
  have hX' : Independent (gridMap hcard) X' := by
    exact independent_map_symm e (gridMap hcard) X hX
  have hgrid : X'.card ≤ 2 * q + s := gridMap_independent_card hcard X' hX'
  have hXcard : X'.card = X.card := by simp [X']
  rw [hXcard] at hgrid
  simpa [q] using hgrid.trans (by omega : 2 * q + s ≤ 4 * q)

lemma g_upper (n : ℕ) (hn : 4 ≤ n) : g n ≤ 4 * Nat.sqrt n := by
  obtain ⟨f, hf, hbound⟩ := upper_witness n hn
  obtain ⟨X, hX, hgX⟩ := (g_spec n).2 f hf
  exact hgX.trans (hbound X hX)

/-! ## Packaging the two estimates -/

/-- The integer part of one quarter of the real square root is universally
guaranteed. -/
lemma guaranteed_floor_sqrt (n : ℕ) (hn : 1 ≤ n) :
    Guaranteed n ⌊Real.sqrt (n : ℝ) / 4⌋₊ := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0
  have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨?_, ?_⟩
  · apply Nat.floor_le_of_le
    nlinarith
  · intro f hf
    have hnfin : 1 ≤ Fintype.card (Fin n) := by simpa using hn
    obtain ⟨U, hU, hcard⟩ := exists_independent_sqrt f hf hnfin
    refine ⟨U, hU, ?_⟩
    have hfloor :
        ((⌊Real.sqrt (n : ℝ) / 4⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (n : ℝ) / 4 :=
      Nat.floor_le (by positivity)
    have hcard' : Real.sqrt (n : ℝ) / 4 ≤ (U.card : ℝ) := by
      simpa using hcard
    have hfloor' : ((⌊Real.sqrt (n : ℝ) / 4⌋₊ : ℕ) : ℝ) ≤ (U.card : ℝ) :=
      hfloor.trans hcard'
    exact_mod_cast hfloor'

lemma floor_sqrt_le_g (n : ℕ) (hn : 1 ≤ n) :
    ⌊Real.sqrt (n : ℝ) / 4⌋₊ ≤ g n :=
  le_g_of_guaranteed (guaranteed_floor_sqrt n hn)

lemma sqrt_le_eight_g (n : ℕ) (hn : 64 ≤ n) :
    Real.sqrt (n : ℝ) ≤ 8 * (g n : ℝ) := by
  have hn1 : 1 ≤ n := by omega
  have hsqrt8 : (8 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    norm_num
    exact_mod_cast hn
  have hfloor_lt :
      Real.sqrt (n : ℝ) / 4 <
        (⌊Real.sqrt (n : ℝ) / 4⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hfloor_g :
      (⌊Real.sqrt (n : ℝ) / 4⌋₊ : ℝ) ≤ (g n : ℝ) := by
    exact_mod_cast floor_sqrt_le_g n hn1
  nlinarith

lemma g_real_upper (n : ℕ) (hn : 4 ≤ n) :
    (g n : ℝ) ≤ 4 * Real.sqrt (n : ℝ) := by
  have hnat : (g n : ℝ) ≤ 4 * (Nat.sqrt n : ℝ) := by
    exact_mod_cast g_upper n hn
  have hsqrt : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.nat_sqrt_le_real_sqrt
  exact hnat.trans (mul_le_mul_of_nonneg_left hsqrt (by norm_num))

lemma g_isBigO_sqrt :
    (fun n : ℕ ↦ (g n : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)) := by
  refine IsBigO.of_bound 4 ?_
  filter_upwards [Filter.eventually_ge_atTop 4] with n hn
  have hg0 : 0 ≤ (g n : ℝ) := by positivity
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  simpa [Real.norm_eq_abs, abs_of_nonneg hg0, abs_of_nonneg hs0] using
    g_real_upper n hn

lemma sqrt_isBigO_g :
    (fun n : ℕ ↦ Real.sqrt (n : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ (g n : ℝ)) := by
  refine IsBigO.of_bound 8 ?_
  filter_upwards [Filter.eventually_ge_atTop 64] with n hn
  have hg0 : 0 ≤ (g n : ℝ) := by positivity
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  simpa [Real.norm_eq_abs, abs_of_nonneg hg0, abs_of_nonneg hs0] using
    sqrt_le_eight_g n hn

/-- Erdős Problem 1025: the guaranteed independent-set size is of order
the square root of the number of vertices. -/
theorem erdos_1025 :
    (fun n : ℕ ↦ (g n : ℝ)) =Θ[Filter.atTop]
      (fun n : ℕ ↦ Real.sqrt (n : ℝ)) := by
  exact ⟨g_isBigO_sqrt, sqrt_isBigO_g⟩

#print axioms Erdos1025.erdos_1025

end

end Erdos1025
