/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 748.
https://www.erdosproblems.com/forum/thread/748

Informal authors:
- Ben Green
- Alexander Sapozhenko

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos748.md
-/
/-
Copyright (c) 2026 The Lean community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean community
-/
import ErdosProblems.Erdos748.GraphContainer
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Cayley
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 748

Let `f n` be the number of sum-free subsets of `{1, ..., n}`.  This file proves

`Real.logb 2 (f n) / n ⟶ 1 / 2`,

which is the precise logarithmic meaning of `f(n) = 2^((1 + o(1)) n / 2)`.
The upper bound is the elementary cyclic-link-graph proof, using the deterministic
graph-container lemma in `ErdosProblems.Erdos748.GraphContainer`.
-/

open Filter
open scoped BigOperators Pointwise Topology
open Function

namespace Erdos748

noncomputable section

/-- A finite set of natural numbers is sum-free when it contains no `b`, `c`, and
`b + c`, with repeated summands allowed. -/
def IsSumFree (A : Finset ℕ) : Prop :=
  ∀ ⦃b c : ℕ⦄, b ∈ A → c ∈ A → b + c ∉ A

/-- The family of sum-free subsets of `{1, ..., n}`. -/
def sumFreeSubsets (n : ℕ) : Finset (Finset ℕ) :=
  by
    classical
    exact (Finset.Icc 1 n).powerset.filter IsSumFree

/-- The counting function in Erdős Problem 748. -/
def sumFreeCount (n : ℕ) : ℕ :=
  (sumFreeSubsets n).card

@[simp] theorem mem_sumFreeSubsets_iff {n : ℕ} {A : Finset ℕ} :
    A ∈ sumFreeSubsets n ↔ A ⊆ Finset.Icc 1 n ∧ IsSumFree A := by
  simp [sumFreeSubsets]

theorem IsSumFree.mono {A B : Finset ℕ} (hA : IsSumFree A) (hBA : B ⊆ A) :
    IsSumFree B := by
  intro b c hb hc hbc
  exact hA (hBA hb) (hBA hc) (hBA hbc)

/-- The integer interval strictly above `n / 2`. -/
def upperHalf (n : ℕ) : Finset ℕ :=
  Finset.Icc (n / 2 + 1) n

theorem upperHalf_sumFree (n : ℕ) : IsSumFree (upperHalf n) := by
  intro b c hb hc hbc
  simp only [upperHalf, Finset.mem_Icc] at hb hc hbc
  omega

theorem upperHalf_card (n : ℕ) : (upperHalf n).card = n - n / 2 := by
  simp [upperHalf, Nat.card_Icc]

/-- The elementary lower bound: every subset of the strict upper half is sum-free. -/
theorem pow_upperHalf_le_sumFreeCount (n : ℕ) :
    2 ^ (n - n / 2) ≤ sumFreeCount n := by
  rw [← upperHalf_card, ← Finset.card_powerset]
  apply Finset.card_le_card
  intro A hA
  rw [Finset.mem_powerset] at hA
  rw [mem_sumFreeSubsets_iff]
  constructor
  · intro x hx
    have hxu := hA hx
    simp only [upperHalf, Finset.mem_Icc] at hxu
    exact Finset.mem_Icc.mpr ⟨by omega, hxu.2⟩
  · exact (upperHalf_sumFree n).mono hA

theorem sumFreeCount_pos (n : ℕ) : 0 < sumFreeCount n := by
  have h := pow_upperHalf_le_sumFreeCount n
  exact lt_of_lt_of_le (pow_pos (by decide) _) h

section CyclicLinkGraph

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

lemma neighborFinset_addCayley_of_neg_eq_self
    (T : Finset G) (hzero : 0 ∉ T) (hneg : -T = T) (x : G) :
    (SimpleGraph.addCayley (T : Set G)).neighborFinset x = T.image (x + ·) := by
  ext y
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
  rw [SimpleGraph.addCayley_adj]
  constructor
  · rintro ⟨hxy, h | h⟩
    · exact ⟨-x + y, h, by abel⟩
    · refine ⟨-(-y + x), ?_, by abel⟩
      rw [← hneg]
      simpa using h
  · rintro ⟨g, hg, rfl⟩
    refine ⟨?_, Or.inl ?_⟩
    · intro hx
      have hg0 : g = 0 := by
        have h := congrArg (-x + ·) hx
        simpa using h.symm
      exact hzero (hg0 ▸ hg)
    · simpa

lemma addCayley_isRegularOfDegree_of_neg_eq_self
    (T : Finset G) (hzero : 0 ∉ T) (hneg : -T = T) :
    (SimpleGraph.addCayley (T : Set G)).IsRegularOfDegree T.card := by
  intro x
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_addCayley_of_neg_eq_self T hzero hneg x,
    Finset.card_image_of_injective _ (fun _ _ h ↦ add_left_cancel h)]

lemma neighborFinset_addCayley
    (P : Finset G) (hzero : 0 ∉ P) (x : G) :
    (SimpleGraph.addCayley (P : Set G)).neighborFinset x = (P ∪ -P).image (x + ·) := by
  ext y
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
  rw [SimpleGraph.addCayley_adj]
  constructor
  · rintro ⟨hxy, h | h⟩
    · exact ⟨-x + y, Finset.mem_union_left _ h, by abel⟩
    · refine ⟨-(-y + x), Finset.mem_union_right _ ?_, by abel⟩
      simpa using h
  · rintro ⟨g, hg, rfl⟩
    rw [Finset.mem_union] at hg
    refine ⟨?_, ?_⟩
    · intro hx
      have hg0 : g = 0 := by
        have h := congrArg (-x + ·) hx
        simpa using h.symm
      rcases hg with hg | hg
      · exact hzero (hg0 ▸ hg)
      · have hng : -g ∈ P := by simpa using hg
        exact hzero (by simpa [hg0] using hng)
    · rcases hg with hg | hg
      · exact Or.inl (by simpa using hg)
      · exact Or.inr (by simpa using hg)

/-- Natural-number steps, reduced modulo `n`. -/
def zmodSteps (n : ℕ) (S : Finset ℕ) : Finset (ZMod n) :=
  S.image fun s : ℕ ↦ (s : ZMod n)

/-- The symmetric closure of a set of positive cyclic steps. -/
def symmetricZmodSteps (n : ℕ) (S : Finset ℕ) : Finset (ZMod n) :=
  zmodSteps n S ∪ -(zmodSteps n S)

lemma addCayley_zmodSteps_eq_symmetric {n : ℕ} {S : Finset ℕ} :
    SimpleGraph.addCayley (zmodSteps n S : Set (ZMod n)) =
      SimpleGraph.addCayley (symmetricZmodSteps n S : Set (ZMod n)) := by
  ext x y
  simp [SimpleGraph.addCayley_adj, symmetricZmodSteps]

lemma zmodSteps_card {n : ℕ} {S : Finset ℕ}
    (hhalf : ∀ s ∈ S, 2 * s < n) :
    (zmodSteps n S).card = S.card := by
  unfold zmodSteps
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have ha_lt : a < n := by have := hhalf a ha; omega
  have hb_lt : b < n := by have := hhalf b hb; omega
  have hv := congrArg ZMod.val hab
  simpa [ZMod.val_natCast_of_lt ha_lt, ZMod.val_natCast_of_lt hb_lt] using hv

lemma zero_notMem_zmodSteps {n : ℕ} {S : Finset ℕ}
    (hpos : ∀ s ∈ S, 0 < s) (hhalf : ∀ s ∈ S, 2 * s < n) :
    0 ∉ zmodSteps n S := by
  rw [zmodSteps, Finset.mem_image]
  rintro ⟨a, ha, ha0⟩
  have ha_lt : a < n := by have := hhalf a ha; omega
  have hv := congrArg ZMod.val ha0
  have ha0' : a = 0 := by simpa [ZMod.val_natCast_of_lt ha_lt] using hv
  exact (hpos a ha).ne' ha0'

lemma disjoint_zmodSteps_neg {n : ℕ} {S : Finset ℕ}
    (hpos : ∀ s ∈ S, 0 < s) (hhalf : ∀ s ∈ S, 2 * s < n) :
    Disjoint (zmodSteps n S) (-(zmodSteps n S)) := by
  rw [Finset.disjoint_left]
  intro x hx hxneg
  have hnx : -x ∈ zmodSteps n S := by simpa using hxneg
  rw [zmodSteps, Finset.mem_image] at hx hnx
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, hbcast⟩ := hnx
  have ha_lt : a < n := by have := hhalf a ha; omega
  have hb_lt : b < n := by have := hhalf b hb; omega
  have hab_lt : a + b < n := by
    have ha2 := hhalf a ha
    have hb2 := hhalf b hb
    omega
  have hcast : ((a + b : ℕ) : ZMod n) = 0 := by
    rw [Nat.cast_add, hbcast]
    simp
  have hv := congrArg ZMod.val hcast
  have hab0 : a + b = 0 := by
    rwa [ZMod.val_natCast_of_lt hab_lt, ZMod.val_zero] at hv
  have := hpos a ha
  omega

lemma symmetricZmodSteps_card {n : ℕ} {S : Finset ℕ}
    (hpos : ∀ s ∈ S, 0 < s) (hhalf : ∀ s ∈ S, 2 * s < n) :
    (symmetricZmodSteps n S).card = 2 * S.card := by
  rw [symmetricZmodSteps, Finset.card_union_of_disjoint
    (disjoint_zmodSteps_neg hpos hhalf), Finset.card_neg,
    zmodSteps_card hhalf]
  omega

lemma symmetricZmodSteps_neg {n : ℕ} {S : Finset ℕ} :
    -(symmetricZmodSteps n S) = symmetricZmodSteps n S := by
  ext x
  simp [symmetricZmodSteps, or_comm]

lemma zero_notMem_symmetricZmodSteps {n : ℕ} {S : Finset ℕ}
    (hpos : ∀ s ∈ S, 0 < s) (hhalf : ∀ s ∈ S, 2 * s < n) :
    0 ∉ symmetricZmodSteps n S := by
  simp [symmetricZmodSteps, zero_notMem_zmodSteps hpos hhalf]

theorem zmodCayley_regular {n : ℕ} [NeZero n] {S : Finset ℕ}
    (hpos : ∀ s ∈ S, 0 < s) (hhalf : ∀ s ∈ S, 2 * s < n) :
    (SimpleGraph.addCayley (symmetricZmodSteps n S : Set (ZMod n))).IsRegularOfDegree
      (2 * S.card) := by
  rw [← symmetricZmodSteps_card hpos hhalf]
  apply addCayley_isRegularOfDegree_of_neg_eq_self
  · exact zero_notMem_symmetricZmodSteps hpos hhalf
  · exact symmetricZmodSteps_neg

theorem zmodCayley_regular' {n : ℕ} [NeZero n] {S : Finset ℕ}
    (hpos : ∀ s ∈ S, 0 < s) (hhalf : ∀ s ∈ S, 2 * s < n) :
    (SimpleGraph.addCayley (zmodSteps n S : Set (ZMod n))).IsRegularOfDegree
      (2 * S.card) := by
  intro x
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    neighborFinset_addCayley _ (zero_notMem_zmodSteps hpos hhalf) x,
    Finset.card_image_of_injective _ (fun _ _ h ↦ add_left_cancel h),
    Finset.card_union_of_disjoint (disjoint_zmodSteps_neg hpos hhalf),
    Finset.card_neg, zmodSteps_card hhalf]
  omega

lemma nat_add_eq_of_zmod_eq {n a b s : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (hsa : s < a) (hsb : s < b)
    (h : (a : ZMod n) + (s : ZMod n) = (b : ZMod n)) :
    a + s = b := by
  have hcast : ((a + s : ℕ) : ZMod n) = (b : ZMod n) := by simpa using h
  have hmod : a + s ≡ b [MOD n] :=
    (ZMod.natCast_eq_natCast_iff (a + s) b n).mp hcast
  apply hmod.eq_of_abs_lt
  rw [abs_lt]
  constructor <;> norm_num at * <;> omega

theorem zmodCayley_tail_independent {n : ℕ} [NeZero n] {A S : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 n) (hSA : S ⊆ A) (hfree : IsSumFree A)
    (hsmall : ∀ s ∈ S, ∀ b ∈ A \ S, s < b) :
    (SimpleGraph.addCayley (zmodSteps n S : Set (ZMod n))).IsIndepSet
      (↑((A \ S).image (fun a : ℕ ↦ (a : ZMod n))) : Set (ZMod n)) := by
  rintro x hx y hy hxy hadj
  rw [Finset.mem_coe, Finset.mem_image] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  rw [SimpleGraph.addCayley_adj'] at hadj
  obtain ⟨_, g, hg, hab | hab⟩ := hadj
  · rw [zmodSteps, Finset.mem_coe, Finset.mem_image] at hg
    obtain ⟨s, hs, rfl⟩ := hg
    have haA : a ∈ A := (Finset.mem_sdiff.mp ha).1
    have hbA : b ∈ A := (Finset.mem_sdiff.mp hb).1
    have ha_le : a ≤ n := (Finset.mem_Icc.mp (hA haA)).2
    have hb_le : b ≤ n := (Finset.mem_Icc.mp (hA hbA)).2
    have hsa : s < a := hsmall s hs a ha
    have hsb : s < b := hsmall s hs b hb
    have habN : a + s = b := nat_add_eq_of_zmod_eq ha_le hb_le hsa hsb hab
    exact hfree haA (hSA hs) (habN ▸ hbA)
  · rw [zmodSteps, Finset.mem_coe, Finset.mem_image] at hg
    obtain ⟨s, hs, rfl⟩ := hg
    have haA : a ∈ A := (Finset.mem_sdiff.mp ha).1
    have hbA : b ∈ A := (Finset.mem_sdiff.mp hb).1
    have ha_le : a ≤ n := (Finset.mem_Icc.mp (hA haA)).2
    have hb_le : b ≤ n := (Finset.mem_Icc.mp (hA hbA)).2
    have hsa : s < a := hsmall s hs a ha
    have hsb : s < b := hsmall s hs b hb
    have hbaN : b + s = a := nat_add_eq_of_zmod_eq hb_le ha_le hsb hsa hab.symm
    exact hfree hbA (hSA hs) (hbaN ▸ haA)

end CyclicLinkGraph

section RegularGraphContainers

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private lemma sym2_out_mk (e : Sym2 V) : s(e.out.1, e.out.2) = e := by
  rw [Sym2.mk, e.out_eq]

/-- The number of neighbors of `v` inside `S`. -/
def degreeInto (v : V) (S : Finset V) : ℕ :=
  (G.neighborFinset v ∩ S).card

/-- Edges of `G` whose two endpoints lie in `S`. -/
def edgesInside (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e ↦ e.toFinset ⊆ S

lemma sum_degreeInto_self (S : Finset V) :
    ∑ v ∈ S, degreeInto G v S = 2 * (edgesInside G S).card := by
  classical
  let K : SimpleGraph V := (G.induce (↑S : Set V)).spanningCoe
  letI : DecidableRel K.Adj := Classical.decRel _
  have hneighbor (v : V) : K.neighborFinset v =
      if v ∈ S then G.neighborFinset v ∩ S else ∅ := by
    ext w
    by_cases hv : v ∈ S <;> simp [K, hv]
  have hdegree (v : V) : K.degree v =
      if v ∈ S then degreeInto G v S else 0 := by
    rw [← K.card_neighborFinset_eq_degree, hneighbor]
    by_cases hv : v ∈ S <;> simp [hv, degreeInto]
  have hedge : K.edgeFinset = edgesInside G S := by
    ext e
    obtain ⟨x, y⟩ := e
    simp [K, edgesInside, Sym2.toFinset_mk_eq, Finset.insert_subset_iff]
  have hsum : (∑ v : V, K.degree v) = ∑ v ∈ S, degreeInto G v S := by
    calc
      _ = ∑ v : V, if v ∈ S then degreeInto G v S else 0 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hdegree v
      _ = _ := by
        rw [← Finset.sum_filter]
        simp
  calc
    _ = ∑ v : V, K.degree v := hsum.symm
    _ = 2 * K.edgeFinset.card := K.sum_degrees_eq_twice_card_edges
    _ = 2 * (edgesInside G S).card := by rw [hedge]

private lemma card_darts_fst_mem (B : Finset V) :
    ((Finset.univ : Finset G.Dart).filter fun d ↦ d.fst ∈ B).card =
      ∑ v ∈ B, G.degree v := by
  classical
  calc
    _ = ∑ d : G.Dart, if d.fst ∈ B then 1 else 0 := by
      simpa using (Finset.sum_boole (fun d : G.Dart ↦ d.fst ∈ B) Finset.univ).symm
    _ = ∑ v ∈ B, ∑ d : G.Dart, if d.fst = v then 1 else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : d.fst ∈ B
      · simp [hd]
      · simp [hd]
    _ = ∑ v ∈ B, G.degree v := by
      apply Finset.sum_congr rfl
      intro v _
      rw [← G.dart_fst_fiber_card_eq_degree v]
      simpa using (Finset.sum_boole (fun d : G.Dart ↦ d.fst = v) Finset.univ)

/-- Deleting vertices removes at most the sum of their original degrees. -/
lemma card_edgeFinset_le_card_edgesInside_add_sum_degree (B : Finset V) :
    G.edgeFinset.card ≤ (edgesInside G (Finset.univ \ B)).card +
      ∑ v ∈ B, G.degree v := by
  classical
  let outside := G.edgeFinset \ edgesInside G (Finset.univ \ B)
  let target := (Finset.univ : Finset G.Dart).filter fun d ↦ d.fst ∈ B
  let orient : outside → target := fun e ↦ by
    have heG : e.1 ∈ G.edgeFinset := (Finset.mem_sdiff.mp e.2).1
    have heNot : e.1 ∉ edgesInside G (Finset.univ \ B) :=
      (Finset.mem_sdiff.mp e.2).2
    have hendpoint : e.1.out.1 ∈ B ∨ e.1.out.2 ∈ B := by
      by_contra h
      push Not at h
      apply heNot
      rw [edgesInside, Finset.mem_filter]
      refine ⟨heG, ?_⟩
      intro x hx
      have hx' : x = e.1.out.1 ∨ x = e.1.out.2 := by
        rw [← Sym2.mem_iff, sym2_out_mk]
        exact Sym2.mem_toFinset.mp hx
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hx' with rfl | rfl
      · exact h.1
      · exact h.2
    by_cases hfirst : e.1.out.1 ∈ B
    · let d : G.Dart := ⟨(e.1.out.1, e.1.out.2), by
          rw [← G.mem_edgeSet, sym2_out_mk]
          exact SimpleGraph.mem_edgeFinset.mp heG⟩
      exact ⟨d, by simp [target, d, hfirst]⟩
    · let d : G.Dart := ⟨(e.1.out.2, e.1.out.1), by
          rw [SimpleGraph.adj_comm, ← G.mem_edgeSet, sym2_out_mk]
          exact SimpleGraph.mem_edgeFinset.mp heG⟩
      exact ⟨d, by simp [target, d, hendpoint.resolve_left hfirst]⟩
  have horient_edge (e : outside) : (orient e).1.edge = e.1 := by
    simp only [orient]
    split
    · simp [SimpleGraph.Dart.edge, sym2_out_mk]
    · simp only [SimpleGraph.Dart.edge]
      rw [Sym2.eq_swap, sym2_out_mk]
  have hinj : Function.Injective orient := by
    intro e f hef
    apply Subtype.ext
    rw [← horient_edge e, ← horient_edge f, congr_arg Subtype.val hef]
  have hout : outside.card ≤ target.card :=
    Finset.card_le_card_of_injective (f := orient) hinj
  have hinside : edgesInside G (Finset.univ \ B) ⊆ G.edgeFinset := by
    intro e he
    exact (Finset.mem_filter.mp he).1
  have hsplit := Finset.card_sdiff_add_card_eq_card hinside
  rw [← hsplit, add_comm]
  exact Nat.add_le_add_left (hout.trans_eq (card_darts_fst_mem G B)) _

lemma degreeInto_le_degree_induce (C : Finset V) (v : C) :
    degreeInto G v C ≤ (G.induce (C : Set V)).degree v := by
  rw [degreeInto, ← SimpleGraph.card_neighborFinset_eq_degree]
  let f : ↥(G.neighborFinset (v : V) ∩ C) →
      ↥((G.induce (C : Set V)).neighborFinset v) := fun w ↦
    ⟨⟨w.1, (Finset.mem_inter.mp w.2).2⟩, by
      rw [SimpleGraph.mem_neighborFinset]
      simpa using (Finset.mem_inter.mp w.2).1⟩
  exact Finset.card_le_card_of_injective (f := f) fun x y h ↦ by
    apply Subtype.ext
    exact congrArg (fun z ↦ (z.1 : V)) h

/-- A low-maximum-degree induced set in a regular graph has size close to at most
half of the vertex set. -/
theorem regular_container_card_ineq {d Δ : ℕ} (hreg : G.IsRegularOfDegree d)
    (C : Finset V) (hlow : (G.induce (C : Set V)).maxDegree < Δ) :
    2 * d * C.card ≤ (Δ - 1) * C.card + d * Fintype.card V := by
  classical
  have hCcard : C.card ≤ Fintype.card V := by
    simpa using Finset.card_le_card (show C ⊆ (Finset.univ : Finset V) by simp)
  have hinter : 2 * (edgesInside G C).card ≤ (Δ - 1) * C.card := by
    rw [← sum_degreeInto_self]
    calc
      ∑ v ∈ C, degreeInto G v C
          ≤ ∑ _v ∈ C, (Δ - 1) := by
            apply Finset.sum_le_sum
            intro v hv
            have hvdeg : degreeInto G v C < Δ := by
              exact lt_of_le_of_lt (degreeInto_le_degree_induce G C ⟨v, hv⟩)
                (lt_of_le_of_lt
                  ((G.induce (C : Set V)).degree_le_maxDegree ⟨v, hv⟩) hlow)
            exact Nat.le_pred_of_lt hvdeg
      _ = (Δ - 1) * C.card := by simp [mul_comm]
  have htotal : Fintype.card V * d = 2 * G.edgeFinset.card := by
    calc
      Fintype.card V * d = ∑ v : V, G.degree v := by simp [hreg.degree_eq]
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hdelete := card_edgeFinset_le_card_edgesInside_add_sum_degree
    G (Finset.univ \ C)
  have hdelete' : G.edgeFinset.card ≤ (edgesInside G C).card +
      d * (Fintype.card V - C.card) := by
    simpa [hreg.degree_eq, Finset.card_sdiff, hCcard, mul_comm] using hdelete
  have hpartition :
      d * (Fintype.card V - C.card) + d * C.card = d * Fintype.card V := by
    rw [← mul_add, Nat.sub_add_cancel hCcard]
  have htotal' : d * Fintype.card V = 2 * G.edgeFinset.card := by
    simpa [mul_comm] using htotal
  have hk : d * C.card ≤ (edgesInside G C).card + G.edgeFinset.card := by
    omega
  calc
    2 * d * C.card = 2 * (d * C.card) := by ring
    _ ≤ 2 * ((edgesInside G C).card + G.edgeFinset.card) :=
      Nat.mul_le_mul_left 2 hk
    _ = 2 * (edgesInside G C).card + 2 * G.edgeFinset.card := by ring
    _ ≤ (Δ - 1) * C.card + d * Fintype.card V :=
      Nat.add_le_add hinter htotal'.symm.le

theorem regular_container_card_ineq' {d Δ : ℕ} (hreg : G.IsRegularOfDegree d)
    (hΔ : Δ ≤ 2 * d) (C : Finset V)
    (hlow : (G.induce (C : Set V)).maxDegree < Δ) :
    (2 * d - Δ + 1) * C.card ≤ d * Fintype.card V := by
  have h := regular_container_card_ineq G hreg C hlow
  have hΔpos : 1 ≤ Δ := by omega
  have hid : (2 * d - Δ + 1) + (Δ - 1) = 2 * d := by omega
  have hidmul :
      (2 * d - Δ + 1) * C.card + (Δ - 1) * C.card = 2 * d * C.card := by
    rw [← add_mul, hid]
  omega

/-- All independent vertex finsets of a finite graph. -/
def independentSets : Finset (Finset V) :=
  (Finset.univ : Finset V).powerset.filter fun I ↦ G.IsIndepSet (I : Set V)

/-- The number of independent vertex finsets of a finite graph. -/
def independentSetCount : ℕ :=
  (independentSets G).card

@[simp] lemma mem_independentSets_iff {I : Finset V} :
    I ∈ independentSets G ↔ G.IsIndepSet (I : Set V) := by
  simp [independentSets]

/-- Counting consequence of a deterministic graph-container map. -/
theorem independentSetCount_le_of_containers (q M : ℕ) (f : Finset V → Finset V)
    (hcontainer : ∀ I : Finset V, G.IsIndepSet (I : Set V) →
      ∃ S : Finset V, S ⊆ I ∧ S.card ≤ q ∧ I ⊆ S ∪ f S)
    (hsize : ∀ S : Finset V, S.card ≤ q → (f S).card ≤ M) :
    independentSetCount G ≤
      (∑ s ∈ Finset.range (q + 1), (Fintype.card V).choose s) * 2 ^ M := by
  classical
  let small : Finset (Finset V) :=
    (Finset.range (q + 1)).biUnion fun s ↦
      Finset.powersetCard s (Finset.univ : Finset V)
  let covered : Finset (Finset V) :=
    small.biUnion fun S ↦ (f S).powerset.image fun T ↦ S ∪ T
  have hcover : independentSets G ⊆ covered := by
    intro I hI
    obtain ⟨S, hSI, hSq, hIS⟩ :=
      hcontainer I ((mem_independentSets_iff (G := G)).mp hI)
    have hSsmall : S ∈ small := by
      change S ∈ (Finset.range (q + 1)).biUnion (fun s ↦
        Finset.powersetCard s (Finset.univ : Finset V))
      rw [Finset.mem_biUnion]
      refine ⟨S.card, Finset.mem_range.mpr (by omega), ?_⟩
      exact Finset.mem_powersetCard.mpr ⟨by simp, rfl⟩
    change I ∈ small.biUnion (fun S ↦ (f S).powerset.image fun T ↦ S ∪ T)
    rw [Finset.mem_biUnion]
    refine ⟨S, hSsmall, ?_⟩
    rw [Finset.mem_image]
    refine ⟨I \ S, ?_, ?_⟩
    · rw [Finset.mem_powerset]
      intro x hx
      have hxI : x ∈ I := (Finset.mem_sdiff.mp hx).1
      rcases Finset.mem_union.mp (hIS hxI) with hxS | hxf
      · exact False.elim ((Finset.mem_sdiff.mp hx).2 hxS)
      · exact hxf
    · ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hxS | ⟨hxI, _⟩)
        · exact hSI hxS
        · exact hxI
      · intro hxI
        by_cases hxS : x ∈ S
        · exact Or.inl hxS
        · exact Or.inr ⟨hxI, hxS⟩
  have hsmall : small.card ≤
      ∑ s ∈ Finset.range (q + 1), (Fintype.card V).choose s := by
    calc
      small.card ≤ ∑ s ∈ Finset.range (q + 1),
          (Finset.powersetCard s (Finset.univ : Finset V)).card := by
        exact Finset.card_biUnion_le
      _ = ∑ s ∈ Finset.range (q + 1), (Fintype.card V).choose s := by simp
  have hcovered : covered.card ≤ small.card * 2 ^ M := by
    calc
      covered.card ≤ ∑ S ∈ small, ((f S).powerset.image fun T ↦ S ∪ T).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ _S ∈ small, 2 ^ M := by
        apply Finset.sum_le_sum
        intro S hS
        calc
          ((f S).powerset.image fun T ↦ S ∪ T).card ≤ (f S).powerset.card :=
            Finset.card_image_le
          _ = 2 ^ (f S).card := Finset.card_powerset _
          _ ≤ 2 ^ M := Nat.pow_le_pow_right (by omega) (hsize S (by
            change S ∈ (Finset.range (q + 1)).biUnion (fun s ↦
              Finset.powersetCard s (Finset.univ : Finset V)) at hS
            rw [Finset.mem_biUnion] at hS
            obtain ⟨s, hs, hSpow⟩ := hS
            have hScard := (Finset.mem_powersetCard.mp hSpow).2
            have hs' := Finset.mem_range.mp hs
            omega))
      _ = small.card * 2 ^ M := by simp
  calc
    independentSetCount G ≤ covered.card := Finset.card_le_card hcover
    _ ≤ small.card * 2 ^ M := hcovered
    _ ≤ (∑ s ∈ Finset.range (q + 1), (Fintype.card V).choose s) * 2 ^ M :=
      Nat.mul_le_mul_right _ hsmall

/-- The independent-set bound obtained by combining regularity with the deterministic
graph-container theorem. -/
theorem independentSetCount_le_regular [LinearOrder V] {d Δ : ℕ}
    (hreg : G.IsRegularOfDegree d) (hΔpos : 1 ≤ Δ) (hΔle : Δ ≤ 2 * d) :
    independentSetCount G ≤
      (∑ s ∈ Finset.range (Fintype.card V / (Δ + 1) + 1),
        (Fintype.card V).choose s) *
        2 ^ (d * Fintype.card V / (2 * d - Δ + 1)) := by
  classical
  obtain ⟨f, hf⟩ := GraphContainer.graph_container_lemma G Δ hΔpos
  let M := d * Fintype.card V / (2 * d - Δ + 1)
  let f' : Finset V → Finset V := fun S ↦ if (f S).card ≤ M then f S else ∅
  apply independentSetCount_le_of_containers G (Fintype.card V / (Δ + 1)) M f'
  · intro I hI
    obtain ⟨S, hSI, hScard, hcover, hlow⟩ := hf I hI
    have hmul := regular_container_card_ineq' G hreg hΔle (f S) hlow
    have hcoeff : 0 < 2 * d - Δ + 1 := by omega
    have hcard : (f S).card ≤ M := by
      change (f S).card ≤ d * Fintype.card V / (2 * d - Δ + 1)
      rw [Nat.le_div_iff_mul_le hcoeff]
      simpa [mul_comm] using hmul
    exact ⟨S, hSI, hScard, by simpa [f', hcard] using hcover⟩
  · intro S hS
    simp only [f']
    split_ifs with h
    · exact h
    · simp

end RegularGraphContainers

section InitialSegments

/-- The `K` least elements of a finite linearly ordered set. -/
def leastPart {α : Type*} [LinearOrder α] (K : ℕ) (A : Finset α) : Finset α :=
  ((A.sort (· ≤ ·)).take K).toFinset

theorem leastPart_subset {α : Type*} [LinearOrder α] (K : ℕ) (A : Finset α) :
    leastPart K A ⊆ A := by
  intro x hx
  have hxTake : x ∈ (A.sort (· ≤ ·)).take K := by
    simpa [leastPart] using hx
  exact (Finset.mem_sort (· ≤ ·)).mp (List.mem_of_mem_take hxTake)

theorem leastPart_card {α : Type*} [LinearOrder α] {K : ℕ} {A : Finset α}
    (hK : K ≤ A.card) : (leastPart K A).card = K := by
  rw [leastPart, List.toFinset_card_of_nodup (A.sort_nodup (· ≤ ·)).take,
    List.length_take, A.length_sort]
  exact Nat.min_eq_left hK

theorem leastPart_lt_tail {α : Type*} [LinearOrder α] {K : ℕ} {A : Finset α}
    {a b : α} (ha : a ∈ leastPart K A) (hb : b ∈ A \ leastPart K A) : a < b := by
  let l := A.sort (· ≤ ·)
  have haTake : a ∈ l.take K := by simpa [leastPart, l] using ha
  have hbList : b ∈ l := by
    simpa [l] using (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_sdiff.mp hb).1
  have hbNot : b ∉ l.take K := by
    intro hbTake
    exact (Finset.mem_sdiff.mp hb).2 (by simpa [leastPart, l] using hbTake)
  have hbAppend : b ∈ l.take K ++ l.drop K := by
    simpa only [List.take_append_drop] using hbList
  have hbDrop : b ∈ l.drop K := (List.mem_append.mp hbAppend).resolve_left hbNot
  have hp : (l.take K ++ l.drop K).Pairwise (· ≤ ·) := by
    simpa only [List.take_append_drop] using A.pairwise_sort (· ≤ ·)
  have hab := (List.pairwise_append.mp hp).2.2 a haTake b hbDrop
  exact lt_of_le_of_ne hab fun habEq ↦ hbNot (habEq ▸ haTake)

theorem leastPart_initial {α : Type*} [LinearOrder α] {K : ℕ} {A : Finset α}
    (hK : K ≤ A.card) :
    ∃ S : Finset α, S ⊆ A ∧ S.card = K ∧
      ∀ s ∈ S, ∀ b ∈ A \ S, s < b := by
  exact ⟨leastPart K A, leastPart_subset K A, leastPart_card hK,
    fun _ hs _ hb ↦ leastPart_lt_tail hs hb⟩

end InitialSegments

section CyclicEncoding

/-- The representative in `{1, ..., n}` of a residue modulo a positive `n`, with
the zero residue represented by `n`. -/
def zmodToNat (n : ℕ) (x : ZMod n) : ℕ :=
  if x.val = 0 then n else x.val

lemma zmodToNat_natCast {n a : ℕ} [NeZero n] (ha : 1 ≤ a) (han : a ≤ n) :
    zmodToNat n (a : ZMod n) = a := by
  by_cases hlt : a < n
  · have ha0 : a ≠ 0 := by omega
    simp [zmodToNat, ZMod.val_natCast_of_lt hlt, ha0]
  · have h : a = n := by omega
    subst a
    simp [zmodToNat]

lemma image_zmodToNat_image_natCast {n : ℕ} [NeZero n] {B : Finset ℕ}
    (hB : B ⊆ Finset.Icc 1 n) :
    ((B.image fun a : ℕ ↦ (a : ZMod n)).image (zmodToNat n)) = B := by
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨z, ⟨a, ha, rfl⟩, hzx⟩
    have haI := Finset.mem_Icc.mp (hB ha)
    have hax : a = x := by
      simpa [zmodToNat_natCast haI.1 haI.2] using hzx
    exact hax ▸ ha
  · intro hx
    refine ⟨(x : ZMod n), ⟨x, hx, rfl⟩, ?_⟩
    have hxI := Finset.mem_Icc.mp (hB hx)
    exact zmodToNat_natCast hxI.1 hxI.2

end CyclicEncoding

section SumFreeCover

/-- Subsets of `[n]` having cardinality strictly less than `K`. -/
def smallSubsets (n K : ℕ) : Finset (Finset ℕ) :=
  (Finset.range K).biUnion fun j ↦ Finset.powersetCard j (Finset.Icc 1 n)

/-- Tails contained in the strict upper half, with a fixed initial segment adjoined. -/
def highTailFamily (n : ℕ) (S : Finset ℕ) : Finset (Finset ℕ) :=
  (upperHalf n).powerset.image fun B ↦ S ∪ B

/-- The cyclic link graph associated with a set of positive steps. -/
def linkGraph (n : ℕ) (S : Finset ℕ) : SimpleGraph (ZMod n) :=
  SimpleGraph.addCayley (zmodSteps n S : Set (ZMod n))

/-- Independent cyclic tails, decoded back to `{1, ..., n}`.  If the step set is
not contained strictly below `n / 2`, this family is empty. -/
def lowTailFamily (n : ℕ) [NeZero n] (S : Finset ℕ) : Finset (Finset ℕ) := by
  classical
  exact if ∀ s ∈ S, 2 * s < n then
    (independentSets (SimpleGraph.addCayley
      (zmodSteps n S : Set (ZMod n)))).image fun I ↦ S ∪ I.image (zmodToNat n)
  else ∅

/-- The two possible tail covers attached to an initial segment. -/
def headFamily (n : ℕ) [NeZero n] (S : Finset ℕ) : Finset (Finset ℕ) :=
  highTailFamily n S ∪ lowTailFamily n S

/-- A finite cover of all sum-free subsets, indexed by small sets and `K`-element
initial segments. -/
def sumFreeCover (n K : ℕ) [NeZero n] : Finset (Finset ℕ) :=
  smallSubsets n K ∪
    (Finset.powersetCard K (Finset.Icc 1 n)).biUnion (headFamily n)

theorem sumFreeSubsets_subset_cover {n K : ℕ} (hn : 0 < n) (hK : 1 ≤ K) :
    sumFreeSubsets n ⊆ @sumFreeCover n K ⟨hn.ne'⟩ := by
  letI : NeZero n := ⟨hn.ne'⟩
  classical
  intro A hAfree
  have hAdata := mem_sumFreeSubsets_iff.mp hAfree
  rw [sumFreeCover, Finset.mem_union]
  by_cases hcard : A.card < K
  · left
    rw [smallSubsets, Finset.mem_biUnion]
    exact ⟨A.card, Finset.mem_range.mpr hcard,
      Finset.mem_powersetCard.mpr ⟨hAdata.1, rfl⟩⟩
  · right
    obtain ⟨S, hSA, hScard, hsmall⟩ := leastPart_initial (Nat.le_of_not_gt hcard)
    have hSambient : S ⊆ Finset.Icc 1 n := hSA.trans hAdata.1
    have hShead : S ∈ Finset.powersetCard K (Finset.Icc 1 n) :=
      Finset.mem_powersetCard.mpr ⟨hSambient, hScard⟩
    rw [Finset.mem_biUnion]
    refine ⟨S, hShead, ?_⟩
    rw [headFamily, Finset.mem_union]
    by_cases hlow : ∀ s ∈ S, 2 * s < n
    · right
      rw [lowTailFamily, if_pos hlow, Finset.mem_image]
      let I : Finset (ZMod n) := (A \ S).image fun a : ℕ ↦ (a : ZMod n)
      have hIind : (SimpleGraph.addCayley
          (zmodSteps n S : Set (ZMod n))).IsIndepSet (I : Set (ZMod n)) := by
        exact zmodCayley_tail_independent hAdata.1 hSA hAdata.2 hsmall
      refine ⟨I, (mem_independentSets_iff (G := SimpleGraph.addCayley
        (zmodSteps n S : Set (ZMod n)))).mpr hIind, ?_⟩
      have hBambient : A \ S ⊆ Finset.Icc 1 n :=
        fun _ hx ↦ hAdata.1 (Finset.mem_sdiff.mp hx).1
      have hdecode := image_zmodToNat_image_natCast hBambient
      change S ∪ I.image (zmodToNat n) = A
      rw [show I.image (zmodToNat n) = A \ S by exact hdecode]
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hxS | ⟨hxA, _⟩)
        · exact hSA hxS
        · exact hxA
      · intro hxA
        by_cases hxS : x ∈ S
        · exact Or.inl hxS
        · exact Or.inr ⟨hxA, hxS⟩
    · left
      push_neg at hlow
      obtain ⟨s, hsS, hs⟩ := hlow
      rw [highTailFamily, Finset.mem_image]
      refine ⟨A \ S, ?_, ?_⟩
      · rw [Finset.mem_powerset]
        intro b hb
        have hbA := (Finset.mem_sdiff.mp hb).1
        have hsb : s < b := hsmall s hsS b hb
        have hbI := Finset.mem_Icc.mp (hAdata.1 hbA)
        exact Finset.mem_Icc.mpr ⟨by omega, hbI.2⟩
      · ext x
        simp only [Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro (hxS | ⟨hxA, _⟩)
          · exact hSA hxS
          · exact hxA
        · intro hxA
          by_cases hxS : x ∈ S
          · exact Or.inl hxS
          · exact Or.inr ⟨hxA, hxS⟩

/-- Explicit finite Cameron--Erdős bound.  The first factor counts possible
initial segments, and the second is the regular-graph container estimate. -/
theorem sumFreeCount_le_container {n K Δ : ℕ} (hn : 0 < n) (hK : 1 ≤ K)
    (hΔpos : 1 ≤ Δ) (hΔle : Δ ≤ 4 * K) :
    sumFreeCount n ≤
      (∑ j ∈ Finset.range K, n.choose j) + n.choose K *
        (2 ^ (n - n / 2) +
          (∑ j ∈ Finset.range (n / (Δ + 1) + 1), n.choose j) *
            2 ^ ((2 * K) * n / (2 * (2 * K) - Δ + 1))) := by
  letI : NeZero n := ⟨hn.ne'⟩
  classical
  let R : ℕ :=
    (∑ j ∈ Finset.range (n / (Δ + 1) + 1), n.choose j) *
      2 ^ ((2 * K) * n / (2 * (2 * K) - Δ + 1))
  have hIcc : (Finset.Icc 1 n).card = n := by
    simp [Nat.card_Icc, hn]
  have hsmall : (smallSubsets n K).card ≤ ∑ j ∈ Finset.range K, n.choose j := by
    calc
      (smallSubsets n K).card ≤ ∑ j ∈ Finset.range K,
          (Finset.powersetCard j (Finset.Icc 1 n)).card := by
        exact Finset.card_biUnion_le
      _ = ∑ j ∈ Finset.range K, n.choose j := by simp [hIcc]
  have hhigh (S : Finset ℕ) :
      (highTailFamily n S).card ≤ 2 ^ (n - n / 2) := by
    calc
      (highTailFamily n S).card ≤ (upperHalf n).powerset.card := by
        exact Finset.card_image_le
      _ = 2 ^ (n - n / 2) := by rw [Finset.card_powerset, upperHalf_card]
  have hlow (S : Finset ℕ) (hS : S ∈ Finset.powersetCard K (Finset.Icc 1 n)) :
      (lowTailFamily n S).card ≤ R := by
    have hSdata := Finset.mem_powersetCard.mp hS
    rw [lowTailFamily]
    split_ifs with hhalf
    · calc
        ((independentSets (SimpleGraph.addCayley
            (zmodSteps n S : Set (ZMod n)))).image fun I ↦
            S ∪ I.image (zmodToNat n)).card
            ≤ independentSetCount (SimpleGraph.addCayley
              (zmodSteps n S : Set (ZMod n))) := by
              exact Finset.card_image_le
        _ ≤ R := by
          letI : LinearOrder (ZMod n) := (ZMod.finEquiv n).symm.toEquiv.linearOrder
          have hpos : ∀ s ∈ S, 0 < s := by
            intro s hs
            exact (Finset.mem_Icc.mp (hSdata.1 hs)).1
          have hreg : (SimpleGraph.addCayley
              (zmodSteps n S : Set (ZMod n))).IsRegularOfDegree (2 * K) := by
            simpa [hSdata.2] using zmodCayley_regular' hpos hhalf
          have hbound := independentSetCount_le_regular (SimpleGraph.addCayley
            (zmodSteps n S : Set (ZMod n))) hreg hΔpos (by omega)
          simpa [R, ZMod.card] using hbound
    · simp [R]
  have hhead (S : Finset ℕ) (hS : S ∈ Finset.powersetCard K (Finset.Icc 1 n)) :
      (headFamily n S).card ≤ 2 ^ (n - n / 2) + R := by
    calc
      (headFamily n S).card ≤
          (highTailFamily n S).card + (lowTailFamily n S).card := by
        exact Finset.card_union_le _ _
      _ ≤ 2 ^ (n - n / 2) + R := Nat.add_le_add (hhigh S) (hlow S hS)
  have hheads :
      ((Finset.powersetCard K (Finset.Icc 1 n)).biUnion (headFamily n)).card ≤
        n.choose K * (2 ^ (n - n / 2) + R) := by
    calc
      _ ≤ ∑ S ∈ Finset.powersetCard K (Finset.Icc 1 n), (headFamily n S).card := by
        exact Finset.card_biUnion_le
      _ ≤ ∑ _S ∈ Finset.powersetCard K (Finset.Icc 1 n),
          (2 ^ (n - n / 2) + R) := by
        exact Finset.sum_le_sum fun S hS ↦ hhead S hS
      _ = n.choose K * (2 ^ (n - n / 2) + R) := by simp [hIcc]
  have hcover := sumFreeSubsets_subset_cover hn hK
  calc
    sumFreeCount n ≤ (sumFreeCover n K).card := Finset.card_le_card hcover
    _ ≤ (smallSubsets n K).card +
        ((Finset.powersetCard K (Finset.Icc 1 n)).biUnion (headFamily n)).card := by
      exact Finset.card_union_le _ _
    _ ≤ (∑ j ∈ Finset.range K, n.choose j) +
        n.choose K * (2 ^ (n - n / 2) + R) := Nat.add_le_add hsmall hheads
    _ = (∑ j ∈ Finset.range K, n.choose j) + n.choose K *
        (2 ^ (n - n / 2) +
          (∑ j ∈ Finset.range (n / (Δ + 1) + 1), n.choose j) *
            2 ^ ((2 * K) * n / (2 * (2 * K) - Δ + 1))) := rfl

lemma sum_choose_range_le_mul_pow {n K : ℕ} (hn : 1 ≤ n) :
    (∑ j ∈ Finset.range K, n.choose j) ≤ K * n ^ K := by
  calc
    (∑ j ∈ Finset.range K, n.choose j) ≤ ∑ _j ∈ Finset.range K, n ^ K := by
      apply Finset.sum_le_sum
      intro j hj
      exact (Nat.choose_le_pow n j).trans
        (Nat.pow_le_pow_right hn (Nat.le_of_lt (Finset.mem_range.mp hj)))
    _ = K * n ^ K := by simp

/-- A fixed-base version of the binomial-tail estimate. -/
lemma binom_tail_le_fixedBase {m n : ℕ} (hm : 1 ≤ m) (hn : 2 * (m + 1) ≤ n) :
    (∑ j ∈ Finset.range (n / (m + 1) + 1), n.choose j) ≤
      (6 * (m + 1)) ^ (n / (m + 1)) := by
  let q := n / (m + 1)
  have hm1 : 0 < m + 1 := by omega
  have hq1 : 1 ≤ q := by
    change 1 ≤ n / (m + 1)
    rw [Nat.le_div_iff_mul_le hm1]
    omega
  have hqhalf : q ≤ n / 2 := by
    exact Nat.div_le_div_left (by omega : 2 ≤ m + 1) (by omega)
  have hbinom := GraphContainer.binom_tail_bound n q (by omega) hq1 hqhalf
  have hdivmod := Nat.div_add_mod n (m + 1)
  have hmodlt := Nat.mod_lt n hm1
  have hfactor : m + 1 ≤ (m + 1) * q := by
    simpa only [mul_one] using Nat.mul_le_mul_left (m + 1) hq1
  have hnq : n ≤ 2 * (m + 1) * q := by
    change (m + 1) * q + n % (m + 1) = n at hdivmod
    calc
      n ≤ 2 * ((m + 1) * q) := by omega
      _ = 2 * (m + 1) * q := by ring
  have hqposR : (0 : ℝ) < q := by exact_mod_cast hq1
  have hbase : Real.exp 1 * (n : ℝ) / (q : ℝ) ≤ (6 * (m + 1) : ℕ) := by
    calc
      Real.exp 1 * (n : ℝ) / (q : ℝ) ≤ 3 * (n : ℝ) / (q : ℝ) := by
        gcongr
        exact Real.exp_one_lt_three.le
      _ ≤ 3 * (2 * (m + 1) : ℕ) := by
        rw [div_le_iff₀ hqposR]
        exact_mod_cast (show 3 * n ≤ 3 * (2 * (m + 1)) * q by
          simpa [mul_assoc] using Nat.mul_le_mul_left 3 hnq)
      _ = (6 * (m + 1) : ℕ) := by norm_num; ring
  have hreal :
      ((∑ j ∈ Finset.range (q + 1), n.choose j : ℕ) : ℝ) ≤
        ((6 * (m + 1) : ℕ) : ℝ) ^ q := by
    calc
      ((∑ j ∈ Finset.range (q + 1), n.choose j : ℕ) : ℝ) =
          ∑ j ∈ Finset.range (q + 1), (n.choose j : ℝ) := by norm_num
      _ ≤ (Real.exp 1 * (n : ℝ) / (q : ℝ)) ^ q := hbinom
      _ ≤ ((6 * (m + 1) : ℕ) : ℝ) ^ q := by
        exact pow_le_pow_left₀ (by positivity) hbase _
  change (∑ j ∈ Finset.range (q + 1), n.choose j) ≤ (6 * (m + 1)) ^ q
  exact_mod_cast hreal

lemma half_le_containerExponent {m n : ℕ} (hm : 1 ≤ m) :
    n / 2 ≤ (2 * m ^ 2) * n / (2 * (2 * m ^ 2) - m + 1) := by
  have hden : 0 < 2 * (2 * m ^ 2) - m + 1 := by nlinarith
  rw [Nat.le_div_iff_mul_le hden]
  have hmle : m ≤ 4 * m ^ 2 := by nlinarith
  have hdenle : 2 * (2 * m ^ 2) - m + 1 ≤ 4 * m ^ 2 := by omega
  calc
    n / 2 * (2 * (2 * m ^ 2) - m + 1) ≤ n / 2 * (4 * m ^ 2) :=
      Nat.mul_le_mul_left _ hdenle
    _ = (2 * m ^ 2) * (2 * (n / 2)) := by ring
    _ ≤ (2 * m ^ 2) * n := by
      exact Nat.mul_le_mul_left _ (by simpa [mul_comm] using Nat.div_mul_le_self n 2)

/-- A compact fixed-parameter consequence of the finite container estimate. -/
theorem sumFreeCount_le_crude {m n : ℕ} (hm : 1 ≤ m) (hn : 2 * (m + 1) ≤ n) :
    sumFreeCount n ≤
      (m ^ 2 + 3) * n ^ (m ^ 2) *
        (6 * (m + 1)) ^ (n / (m + 1)) *
          2 ^ ((2 * m ^ 2) * n / (2 * (2 * m ^ 2) - m + 1)) := by
  let K := m ^ 2
  let q := n / (m + 1)
  let B := 6 * (m + 1)
  let M := (2 * m ^ 2) * n / (2 * (2 * m ^ 2) - m + 1)
  have hnpos : 0 < n := by omega
  have hKpos : 1 ≤ K := by dsimp [K]; nlinarith
  have hmaster := sumFreeCount_le_container (n := n) (K := K) (Δ := m)
    hnpos hKpos hm (by dsimp [K]; nlinarith)
  have hsmall := sum_choose_range_le_mul_pow (K := K) (by omega : 1 ≤ n)
  have hchoose : n.choose K ≤ n ^ K := Nat.choose_le_pow n K
  have htail := binom_tail_le_fixedBase hm hn
  have hfloor := half_le_containerExponent (n := n) hm
  have hceil : n - n / 2 ≤ M + 1 := by
    have hparity : n - n / 2 ≤ n / 2 + 1 := by omega
    exact hparity.trans (Nat.add_le_add_right hfloor 1)
  have hhigh : 2 ^ (n - n / 2) ≤ 2 * 2 ^ M := by
    calc
      2 ^ (n - n / 2) ≤ 2 ^ (M + 1) := Nat.pow_le_pow_right (by decide) hceil
      _ = 2 * 2 ^ M := by rw [pow_succ]; omega
  change sumFreeCount n ≤ (K + 3) * n ^ K * B ^ q * 2 ^ M
  change (∑ j ∈ Finset.range K, n.choose j) ≤ K * n ^ K at hsmall
  change (∑ j ∈ Finset.range (q + 1), n.choose j) ≤ B ^ q at htail
  change n.choose K ≤ n ^ K at hchoose
  change 2 ^ (n - n / 2) ≤ 2 * 2 ^ M at hhigh
  change sumFreeCount n ≤ (∑ j ∈ Finset.range K, n.choose j) + n.choose K *
    (2 ^ (n - n / 2) +
      (∑ j ∈ Finset.range (q + 1), n.choose j) * 2 ^ M) at hmaster
  calc
    sumFreeCount n ≤ (∑ j ∈ Finset.range K, n.choose j) + n.choose K *
        (2 ^ (n - n / 2) +
          (∑ j ∈ Finset.range (q + 1), n.choose j) * 2 ^ M) := hmaster
    _ ≤ K * n ^ K + n ^ K * (2 * 2 ^ M + B ^ q * 2 ^ M) := by
      gcongr
    _ ≤ (K + 3) * n ^ K * B ^ q * 2 ^ M := by
      have hB : 1 ≤ B ^ q := by
        have : 0 < B ^ q := pow_pos (by dsimp [B]; omega) _
        omega
      have htwo : 1 ≤ 2 ^ M := by
        have : 0 < 2 ^ M := pow_pos (by decide) _
        omega
      have hKyz : K ≤ K * B ^ q * 2 ^ M := by
        calc
          K = K * 1 * 1 := by ring
          _ ≤ K * B ^ q * 2 ^ M := by gcongr
      have h2yz : 2 * 2 ^ M ≤ 2 * B ^ q * 2 ^ M := by
        calc
          2 * 2 ^ M = 2 * 1 * 2 ^ M := by ring
          _ ≤ 2 * B ^ q * 2 ^ M := by gcongr
      calc
        K * n ^ K + n ^ K * (2 * 2 ^ M + B ^ q * 2 ^ M) =
            n ^ K * (K + 2 * 2 ^ M + B ^ q * 2 ^ M) := by ring
        _ ≤ n ^ K * (K * B ^ q * 2 ^ M +
            2 * B ^ q * 2 ^ M + B ^ q * 2 ^ M) := by
          gcongr
        _ = (K + 3) * n ^ K * B ^ q * 2 ^ M := by ring

end SumFreeCover

section AsymptoticLemmas

lemma tendsto_nat_mul_div_const_div_nat (a d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    Tendsto (fun n : ℕ ↦ (((a * n) / d : ℕ) : ℝ) / (n : ℝ)) atTop
      (𝓝 ((a : ℝ) / (d : ℝ))) := by
  have hcast : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hmul : Tendsto (fun n : ℕ ↦ (a : ℝ) * (n : ℝ)) atTop atTop :=
    hcast.const_mul_atTop (by exact_mod_cast ha)
  have hx : Tendsto (fun n : ℕ ↦ ((a : ℝ) * (n : ℝ)) / (d : ℝ)) atTop atTop :=
    hmul.atTop_div_const (by exact_mod_cast hd)
  have hfloor := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hx
  have hscaled := hfloor.mul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (a : ℝ) / (d : ℝ)) atTop _)
  have heq : (fun n : ℕ ↦
      ((⌊((a : ℝ) * (n : ℝ) / (d : ℝ))⌋₊ : ℝ) /
        (((a : ℝ) * (n : ℝ)) / (d : ℝ))) * ((a : ℝ) / (d : ℝ))) =ᶠ[atTop]
      (fun n : ℕ ↦ (((a * n) / d : ℕ) : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [show ⌊((a : ℝ) * (n : ℝ) / (d : ℝ))⌋₊ = (a * n) / d by
      simpa [Nat.cast_mul] using (Nat.floor_div_eq_div (K := ℝ) (a * n) d)]
    push_cast
    field_simp
  simpa only [one_mul] using hscaled.congr' heq

lemma tendsto_nat_div_const_div_nat (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℕ ↦ ((n / d : ℕ) : ℝ) / (n : ℝ)) atTop
      (𝓝 (1 / (d : ℝ))) := by
  simpa using tendsto_nat_mul_div_const_div_nat 1 d (by decide) hd

/-- The logarithmic rate furnished by the fixed-parameter finite estimate. -/
noncomputable def fixedUpperRate (m n : ℕ) : ℝ :=
  Real.logb 2 (m ^ 2 + 3 : ℕ) / (n : ℝ) +
    (m ^ 2 : ℝ) * (Real.logb 2 (n : ℝ) / (n : ℝ)) +
    (((n / (m + 1) : ℕ) : ℝ) / (n : ℝ)) * Real.logb 2 (6 * (m + 1) : ℕ) +
    ((((2 * m ^ 2) * n / (2 * (2 * m ^ 2) - m + 1) : ℕ) : ℝ) / (n : ℝ))

/-- Limit of `fixedUpperRate`. -/
noncomputable def fixedUpperLimit (m : ℕ) : ℝ :=
  (1 / (m + 1 : ℕ) : ℝ) * Real.logb 2 (6 * (m + 1) : ℕ) +
    (2 * m ^ 2 : ℝ) / (2 * (2 * m ^ 2) - m + 1 : ℕ)

lemma tendsto_fixedUpperRate (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fixedUpperRate m) atTop (𝓝 (fixedUpperLimit m)) := by
  have hconst := tendsto_const_div_atTop_nhds_zero_nat
    (Real.logb 2 (m ^ 2 + 3 : ℕ))
  have hlogReal : Tendsto (fun x : ℝ ↦ Real.logb 2 x / x) atTop (𝓝 0) :=
    Real.isLittleO_logb_id_atTop.tendsto_div_nhds_zero
  have hlog : Tendsto (fun n : ℕ ↦ Real.logb 2 (n : ℝ) / (n : ℝ)) atTop
      (𝓝 0) := hlogReal.comp tendsto_natCast_atTop_atTop
  have hlogScaled := (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (m ^ 2 : ℝ)) atTop _).mul hlog
  have hq := tendsto_nat_div_const_div_nat (m + 1) (by omega)
  have hqScaled := hq.mul (tendsto_const_nhds : Tendsto
    (fun _ : ℕ ↦ Real.logb 2 (6 * (m + 1) : ℕ)) atTop _)
  have hden : 0 < 2 * (2 * m ^ 2) - m + 1 := by nlinarith
  have hM := tendsto_nat_mul_div_const_div_nat (2 * m ^ 2)
    (2 * (2 * m ^ 2) - m + 1) (by nlinarith) hden
  unfold fixedUpperRate fixedUpperLimit
  convert ((hconst.add hlogScaled).add hqScaled).add hM using 1 <;>
    simp [Nat.cast_pow, Nat.cast_mul]

lemma eventually_logb_sumFreeCount_div_le_fixedUpperRate (m : ℕ) (hm : 1 ≤ m) :
    ∀ᶠ n : ℕ in atTop,
      Real.logb 2 (sumFreeCount n : ℝ) / (n : ℝ) ≤ fixedUpperRate m n := by
  filter_upwards [eventually_ge_atTop (2 * (m + 1))] with n hn
  have hnpos : 0 < n := by omega
  let C := m ^ 2 + 3
  let K := m ^ 2
  let B := 6 * (m + 1)
  let q := n / (m + 1)
  let M := (2 * m ^ 2) * n / (2 * (2 * m ^ 2) - m + 1)
  have hcrude := sumFreeCount_le_crude (m := m) (n := n) hm hn
  change sumFreeCount n ≤ C * n ^ K * B ^ q * 2 ^ M at hcrude
  have hcast : (sumFreeCount n : ℝ) ≤
      (C : ℝ) * (n : ℝ) ^ K * (B : ℝ) ^ q * (2 : ℝ) ^ M := by
    exact_mod_cast hcrude
  have hlog := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
    (by exact_mod_cast sumFreeCount_pos n) hcast
  have hC : (C : ℝ) ≠ 0 := by dsimp [C]; positivity
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hB : (B : ℝ) ≠ 0 := by dsimp [B]; positivity
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  rw [Real.logb_mul (mul_ne_zero (mul_ne_zero hC (pow_ne_zero K hn0))
      (pow_ne_zero q hB)) (pow_ne_zero M h2),
    Real.logb_mul (mul_ne_zero hC (pow_ne_zero K hn0)) (pow_ne_zero q hB),
    Real.logb_mul hC (pow_ne_zero K hn0), Real.logb_pow, Real.logb_pow,
    Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlog
  rw [div_le_iff₀ (by exact_mod_cast hnpos)]
  unfold fixedUpperRate
  change Real.logb 2 (sumFreeCount n : ℝ) ≤ _
  calc
    Real.logb 2 (sumFreeCount n : ℝ) ≤
        Real.logb 2 (C : ℝ) + (K : ℝ) * Real.logb 2 (n : ℝ) +
          (q : ℝ) * Real.logb 2 (B : ℝ) + (M : ℝ) := by
      simpa [mul_one] using hlog
    _ = (Real.logb 2 (m ^ 2 + 3 : ℕ) / (n : ℝ) +
          (m ^ 2 : ℝ) * (Real.logb 2 (n : ℝ) / (n : ℝ)) +
          (((n / (m + 1) : ℕ) : ℝ) / (n : ℝ)) *
            Real.logb 2 (6 * (m + 1) : ℕ) +
          ((((2 * m ^ 2) * n / (2 * (2 * m ^ 2) - m + 1) : ℕ) : ℝ) /
            (n : ℝ))) * (n : ℝ) := by
      dsimp [C, K, B, q, M]
      field_simp
      simp only [Nat.cast_pow]
      ac_rfl

lemma tendsto_fixedUpperLogTerm : Tendsto
    (fun m : ℕ ↦ (1 / (m + 1 : ℕ) : ℝ) *
      Real.logb 2 (6 * (m + 1) : ℕ)) atTop (𝓝 0) := by
  have hshift : Tendsto (fun m : ℕ ↦ m + 1) atTop atTop := tendsto_add_atTop_nat 1
  have hx : Tendsto (fun m : ℕ ↦ ((m + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hshift
  have hlogReal : Tendsto (fun x : ℝ ↦ Real.logb 2 x / x) atTop (𝓝 0) :=
    Real.isLittleO_logb_id_atTop.tendsto_div_nhds_zero
  have hlog := hlogReal.comp hx
  have hconst :=
    (tendsto_const_div_atTop_nhds_zero_nat (Real.logb 2 (6 : ℝ))).comp hshift
  have hsum := hconst.add hlog
  convert hsum using 1
  · funext m
    simp only [Function.comp_apply]
    rw [show ((6 * (m + 1) : ℕ) : ℝ) = (6 : ℝ) * ((m + 1 : ℕ) : ℝ) by
      push_cast; ring]
    rw [Real.logb_mul (by norm_num : (6 : ℝ) ≠ 0)
      (by exact_mod_cast (show m + 1 ≠ 0 by omega) : ((m + 1 : ℕ) : ℝ) ≠ 0)]
    field_simp
  · ring

lemma tendsto_fixedUpperRationalTerm : Tendsto
    (fun m : ℕ ↦ (2 * m ^ 2 : ℝ) /
      (2 * (2 * m ^ 2) - m + 1 : ℕ)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hu : Tendsto (fun m : ℕ ↦ ((m : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hden : Tendsto
      (fun m : ℕ ↦ (4 : ℝ) - (m : ℝ)⁻¹ + ((m : ℝ)⁻¹) ^ 2) atTop (𝓝 4) := by
    convert (tendsto_const_nhds.sub hu).add (hu.pow 2) using 1 <;> norm_num
  have hrat : Tendsto
      (fun m : ℕ ↦ (2 : ℝ) / ((4 : ℝ) - (m : ℝ)⁻¹ + ((m : ℝ)⁻¹) ^ 2))
      atTop (𝓝 ((2 : ℝ) / 4)) :=
    tendsto_const_nhds.div hden (by norm_num)
  have heq : (fun m : ℕ ↦ (2 : ℝ) /
      ((4 : ℝ) - (m : ℝ)⁻¹ + ((m : ℝ)⁻¹) ^ 2)) =ᶠ[atTop]
      (fun m : ℕ ↦ (2 * m ^ 2 : ℝ) /
        (2 * (2 * m ^ 2) - m + 1 : ℕ)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hsub : m ≤ 2 * (2 * m ^ 2) := by nlinarith
    rw [Nat.cast_add, Nat.cast_sub hsub]
    push_cast
    field_simp
    ring_nf
  simpa only [show (2 / 4 : ℝ) = 1 / 2 by norm_num] using hrat.congr' heq

lemma tendsto_fixedUpperLimit :
    Tendsto fixedUpperLimit atTop (𝓝 (1 / 2 : ℝ)) := by
  unfold fixedUpperLimit
  convert tendsto_fixedUpperLogTerm.add tendsto_fixedUpperRationalTerm using 1 <;>
    simp [Nat.cast_pow, Nat.cast_mul]

lemma tendsto_nat_half_div_nat :
    Tendsto (fun n : ℕ ↦ ((n / 2 : ℕ) : ℝ) / (n : ℝ)) atTop
      (𝓝 (1 / 2 : ℝ)) := by
  have hbase : Tendsto (fun n : ℕ ↦ (n : ℝ) / 2) atTop atTop := by
    have h := tendsto_natCast_atTop_atTop.const_mul_atTop
      (by norm_num : (0 : ℝ) < 1 / 2)
    convert h using 1 <;> funext n <;> ring
  have hfloor : Tendsto
      (fun n : ℕ ↦ ((⌊((n : ℝ) / 2)⌋₊ : ℕ) : ℝ) / ((n : ℝ) / 2)) atTop
        (𝓝 (1 : ℝ)) :=
    tendsto_nat_floor_div_atTop.comp hbase
  have hscaled := (tendsto_const_nhds.mul hfloor : Tendsto
    (fun n : ℕ ↦ (1 / 2 : ℝ) *
      (((⌊((n : ℝ) / 2)⌋₊ : ℕ) : ℝ) / ((n : ℝ) / 2))) atTop
    (𝓝 ((1 / 2 : ℝ) * 1)))
  have hfun : (fun n : ℕ ↦ (1 / 2 : ℝ) *
      (((⌊((n : ℝ) / 2)⌋₊ : ℕ) : ℝ) / ((n : ℝ) / 2))) =ᶠ[atTop]
      (fun n : ℕ ↦ ((n / 2 : ℕ) : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnfloor : ⌊(n : ℝ) / (2 : ℝ)⌋₊ = n / 2 :=
      Nat.floor_div_eq_div (K := ℝ) n 2
    rw [hnfloor]
    field_simp [Nat.cast_ne_zero.mpr hn.ne']
  simpa only [mul_one] using hscaled.congr' hfun

lemma eventually_natHalf_le_logb_sumFreeCount_div :
    ∀ᶠ n : ℕ in atTop,
      ((n / 2 : ℕ) : ℝ) / (n : ℝ) ≤
        Real.logb 2 (sumFreeCount n : ℝ) / (n : ℝ) := by
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hpow : 2 ^ (n / 2) ≤ sumFreeCount n := by
    calc
      2 ^ (n / 2) ≤ 2 ^ (n - n / 2) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ sumFreeCount n := pow_upperHalf_le_sumFreeCount n
  have hcast : (2 : ℝ) ^ (n / 2) ≤ (sumFreeCount n : ℝ) := by
    exact_mod_cast hpow
  have hlog := Real.logb_le_logb_of_le (b := (2 : ℝ)) (by norm_num)
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ (n / 2)) hcast
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hlog
  exact (div_le_div_iff_of_pos_right (Nat.cast_pos.mpr hn)).2 hlog

/-- **Erdős Problem 748 (Cameron--Erdős conjecture).**  If `f(n)` counts the
sum-free subsets of `{1, ..., n}`, then `log₂ f(n) / n` tends to `1/2`.
Equivalently, `f(n) = 2^((1 + o(1)) n / 2)`. -/
theorem erdos_748 :
    Tendsto (fun n : ℕ ↦ Real.logb 2 (sumFreeCount n : ℝ) / (n : ℝ)) atTop
      (𝓝 (1 / 2 : ℝ)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    have haLower := (tendsto_order.mp tendsto_nat_half_div_nat).1 a ha
    filter_upwards [haLower, eventually_natHalf_le_logb_sumFreeCount_div] with n hna hnle
    exact hna.trans_le hnle
  · intro b hb
    have hmEventually := (tendsto_order.mp tendsto_fixedUpperLimit).2 b hb
    have hmExists : ∃ m : ℕ, 1 ≤ m ∧ fixedUpperLimit m < b := by
      exact (Filter.Eventually.exists (hmEventually.and (eventually_ge_atTop 1))).imp
        (fun m hm ↦ ⟨hm.2, hm.1⟩)
    obtain ⟨m, hm, hmb⟩ := hmExists
    have hrate := (tendsto_order.mp (tendsto_fixedUpperRate m hm)).2 b hmb
    filter_upwards [eventually_logb_sumFreeCount_div_le_fixedUpperRate m hm, hrate]
      with n hnle hnlt
    exact hnle.trans_lt hnlt

end AsymptoticLemmas

end

end Erdos748

#print axioms Erdos748.erdos_748
