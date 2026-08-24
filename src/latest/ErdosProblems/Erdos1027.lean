/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 1027.
https://www.erdosproblems.com/forum/thread/1027

Informal authors:
- Koishi Chan

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1027.md
-/
/-
This file formalizes the affirmative resolution of Erdős Problem 1027.

Informal proof: Koishi Chan's adaptive partial-colouring argument, completed
with the non-uniform Property-B theorem of Beck via the corrected finite
random-greedy proof of Duraj--Gutowski--Kozik.
-/

import ErdosProblems.Erdos1027.Tree
import ErdosProblems.Erdos1027.DGKPropertyB

namespace Erdos1027

open scoped BigOperators
open Finset

universe u

abbrev Hypergraph (α : Type*) [DecidableEq α] := Finset (Finset α)

/-- The vertices which occur in at least one edge. -/
def groundSet {α : Type*} [DecidableEq α] (𝓕 : Hypergraph α) : Finset α :=
  𝓕.biUnion id

/-- All edges of `𝓕` have cardinality `n`. -/
def IsUniform {α : Type*} [DecidableEq α] (𝓕 : Hypergraph α) (n : ℕ) : Prop :=
  ∀ A ∈ 𝓕, A.card = n

/-- `B` meets every edge of `𝓕` but contains no edge of `𝓕`. -/
def IsGood {α : Type*} [DecidableEq α] (𝓕 : Hypergraph α) (B : Finset α) : Prop :=
  B ⊆ groundSet 𝓕 ∧ ∀ A ∈ 𝓕, (A ∩ B).Nonempty ∧ ¬A ⊆ B

/-- The finset of all subsets of the ground set which meet, but do not contain,
every edge. -/
noncomputable def goodSets {α : Type*} [DecidableEq α]
    (𝓕 : Hypergraph α) : Finset (Finset α) := by
  classical
  exact (groundSet 𝓕).powerset.filter fun B ↦
    ∀ A ∈ 𝓕, (A ∩ B).Nonempty ∧ ¬A ⊆ B

/-- A Boolean colouring is proper when every edge contains two vertices of
different colours. -/
def ProperColoring {α : Type*} [DecidableEq α]
    (𝓕 : Hypergraph α) (χ : α → Bool) : Prop :=
  ∀ A ∈ 𝓕, ∃ x ∈ A, ∃ y ∈ A, χ x ≠ χ y

lemma mem_groundSet {α : Type*} [DecidableEq α] {𝓕 : Hypergraph α} {x : α} :
    x ∈ groundSet 𝓕 ↔ ∃ A ∈ 𝓕, x ∈ A := by
  simp [groundSet]

lemma edge_subset_groundSet {α : Type*} [DecidableEq α]
    {𝓕 : Hypergraph α} {A : Finset α} (hA : A ∈ 𝓕) :
    A ⊆ groundSet 𝓕 := by
  intro x hx
  exact mem_groundSet.mpr ⟨A, hA, hx⟩

@[simp] lemma mem_goodSets {α : Type*} [DecidableEq α]
    {𝓕 : Hypergraph α} {B : Finset α} :
    B ∈ goodSets 𝓕 ↔ IsGood 𝓕 B := by
  classical
  simp [goodSets, IsGood]

lemma good_of_properColoring {α : Type*} [DecidableEq α]
    {𝓕 : Hypergraph α} {χ : α → Bool} (hχ : ProperColoring 𝓕 χ) :
    IsGood 𝓕 ((groundSet 𝓕).filter fun x ↦ χ x) := by
  constructor
  · exact filter_subset _ _
  intro A hA
  obtain ⟨x, hxA, y, hyA, hxy⟩ := hχ A hA
  have hxX : x ∈ groundSet 𝓕 := edge_subset_groundSet hA hxA
  have hyX : y ∈ groundSet 𝓕 := edge_subset_groundSet hA hyA
  cases hχx : χ x <;> cases hχy : χ y <;> simp_all
  · exact ⟨⟨y, by simp [hyA, hyX, hχy]⟩, by
      intro hsub
      have := hsub hxA
      simp [hxX, hχx] at this⟩
  · exact ⟨⟨x, by simp [hxA, hxX, hχx]⟩, by
      intro hsub
      have := hsub hyA
      simp [hyX, hχy] at this⟩

lemma properColoring_of_good {α : Type*} [DecidableEq α]
    {𝓕 : Hypergraph α} {B : Finset α} (hB : IsGood 𝓕 B) :
    ProperColoring 𝓕 (fun x ↦ decide (x ∈ B)) := by
  intro A hA
  obtain ⟨⟨x, hx⟩, hnot⟩ := (hB.2 A hA)
  have hxA : x ∈ A := (mem_inter.mp hx).1
  have hxB : x ∈ B := (mem_inter.mp hx).2
  have : ∃ y ∈ A, y ∉ B := by
    simpa [Finset.not_subset] using hnot
  obtain ⟨y, hyA, hyB⟩ := this
  exact ⟨x, hxA, y, hyA, by simp [hxB, hyB]⟩

/-- Property B is exactly the existence of a good subset. -/
theorem exists_good_iff_exists_properColoring
    {α : Type*} [DecidableEq α] (𝓕 : Hypergraph α) :
    (∃ B, IsGood 𝓕 B) ↔ ∃ χ : α → Bool, ProperColoring 𝓕 χ := by
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨fun x ↦ decide (x ∈ B), properColoring_of_good hB⟩
  · rintro ⟨χ, hχ⟩
    exact ⟨(groundSet 𝓕).filter fun x ↦ χ x, good_of_properColoring hχ⟩

/-- Division-free natural-number form of the quantitative assertion. -/
def NatBudgetResolution : Prop :=
  ∀ C : ℕ, 0 < C →
    ∃ K : ℕ, 0 < K ∧ ∃ N : ℕ,
      ∀ (n : ℕ), N ≤ n →
      ∀ (α : Type u) [DecidableEq α] (𝓕 : Hypergraph α),
        IsUniform 𝓕 n → 𝓕.card ≤ C * 2 ^ n →
          2 ^ (groundSet 𝓕).card ≤ K * (goodSets 𝓕).card

/-- Literal interpretation of `≫_c 2^|X|` in Erdős Problem 1027. -/
def RealBudgetResolution : Prop :=
  ∀ c : ℝ, 0 < c →
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (n : ℕ), N ≤ n →
      ∀ (α : Type u) [DecidableEq α] (𝓕 : Hypergraph α),
        IsUniform 𝓕 n →
          (𝓕.card : ℝ) ≤ c * (2 : ℝ) ^ n →
            δ * (2 : ℝ) ^ (groundSet 𝓕).card ≤ (goodSets 𝓕).card

lemma natCeil_pos_of_pos {c : ℝ} (hc : 0 < c) : 0 < ⌈c⌉₊ := by
  exact Nat.ceil_pos.mpr hc

lemma card_le_natCeil_mul_pow_of_cast_le {m n : ℕ} {c : ℝ}
    (hc : (m : ℝ) ≤ c * (2 : ℝ) ^ n) :
    m ≤ ⌈c⌉₊ * 2 ^ n := by
  exact_mod_cast hc.trans
    (mul_le_mul_of_nonneg_right (Nat.le_ceil c) (by positivity : 0 ≤ (2 : ℝ) ^ n))

lemma inv_mul_pow_le_card_of_mul_card_ge {K g x : ℕ} (hK : 0 < K)
    (h : 2 ^ x ≤ K * g) :
    (1 / (K : ℝ)) * (2 : ℝ) ^ x ≤ g := by
  have hR : ((2 ^ x : ℕ) : ℝ) ≤ (K : ℝ) * (g : ℝ) := by
    exact_mod_cast h
  rw [one_div]
  calc
    (K : ℝ)⁻¹ * (2 : ℝ) ^ x = (K : ℝ)⁻¹ * ((2 ^ x : ℕ) : ℝ) := by norm_num
    _ ≤ (K : ℝ)⁻¹ * ((K : ℝ) * (g : ℝ)) :=
      mul_le_mul_of_nonneg_left hR (by positivity)
    _ = (g : ℝ) := by field_simp

theorem realBudgetResolution_of_natBudgetResolution
    (h : NatBudgetResolution.{u}) : RealBudgetResolution.{u} := by
  intro c hc
  obtain ⟨K, hK, N, hN⟩ := h ⌈c⌉₊ (natCeil_pos_of_pos hc)
  refine ⟨1 / (K : ℝ), by positivity, N, ?_⟩
  intro n hn α _ 𝓕 huniform hcard
  apply inv_mul_pow_le_card_of_mul_card_ge hK
  exact hN n hn α 𝓕 huniform (card_le_natCeil_mul_pow_of_cast_le hcard)

/-! The final quantitative argument is assembled below from the decision-tree
theorem and the fixed-budget non-uniform Property-B theorem. -/

lemma goodSets_eq_treeGoodSets {alpha : Type*} [DecidableEq alpha]
    (F : Hypergraph alpha) :
    goodSets F = Tree.goodSets (groundSet F) F := by
  classical
  ext B
  simp [goodSets, Tree.goodSets, Tree.GoodSet]

/-- The public natural-number form follows formally from a uniform
fixed-budget Property-B input.  The latter is supplied below by the corrected
Duraj--Gutowski--Kozik random-greedy argument. -/
theorem natBudgetResolution_of_universalBeck
    (hbeck : ∀ C : ℕ, 0 < C → ∃ r : ℕ, ∀ n : ℕ,
      ∀ ambient : Type u, Tree.UniversalBeckFixedBudget ambient C n r) :
    NatBudgetResolution.{u} := by
  intro C hC
  obtain ⟨r, hr⟩ := hbeck C hC
  let K : ℕ := 2 ^ (C * 2 ^ (r + 3) * (r + 2) + 1)
  refine ⟨K, by positivity, r + 2, ?_⟩
  intro n hn alpha _ F huniform hcard
  have hedges : ∀ A ∈ F, A ⊆ groundSet F ∧ A.card = n := by
    intro A hA
    exact ⟨edge_subset_groundSet hA, huniform A hA⟩
  rw [goodSets_eq_treeGoodSets]
  simpa [K] using
    (Tree.NatBudgetResolution C n r hC hn (groundSet F) F hedges hcard (hr n alpha))

/-- Erdős Problem 1027, in a division-free natural-number formulation. -/
theorem erdos_1027_nat : NatBudgetResolution.{u} := by
  apply natBudgetResolution_of_universalBeck
  intro C hC
  refine ⟨DGKPropertyB.dgkThreshold (8 * C), ?_⟩
  intro n ambient
  exact DGKPropertyB.universalBeckFixedBudget ambient C n hC

/-- Affirmative resolution of Erdős Problem 1027: for every positive real
budget `c`, a positive proportion (depending only on `c`) of all subsets of
the ground set meet every edge without containing an edge, once the common
edge size is sufficiently large. -/
theorem erdos_1027 : (∀ c : ℝ, 0 < c →
  ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
    ∀ (n : ℕ), N ≤ n →
    ∀ (α : Type u) [DecidableEq α] (𝓕 : Erdos1027.Hypergraph α),
      Erdos1027.IsUniform 𝓕 n →
        (𝓕.card : ℝ) ≤ c * (2 : ℝ) ^ n →
          δ * (2 : ℝ) ^ (Erdos1027.groundSet 𝓕).card ≤ (Erdos1027.goodSets 𝓕).card) :=
  realBudgetResolution_of_natBudgetResolution erdos_1027_nat

end Erdos1027

#print axioms Erdos1027.erdos_1027
