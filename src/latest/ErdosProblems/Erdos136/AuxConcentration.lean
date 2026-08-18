/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos136.McDiarmid
import ErdosProblems.Erdos136.PartialConstruction
import ErdosProblems.Erdos136.UpperParameters

/-!
# Concentration for the retained-label auxiliary hypergraph

This file is the finite-probability bridge used in the Joos--Mubayi
construction.  A bit is attached to every vertex/old-colour label and the
bits are independently retained with a common bias.  We define the actual
auxiliary degree, same-colour labelled codegree, and pair-test cardinality
statistics, and prove a simultaneous extraction theorem from the weighted
McDiarmid inequality in `Erdos136.McDiarmid`.

There are two small but important formal details.

* A labelled degree statistic is evaluated after forcibly retaining its root
  coordinate, and a same-colour codegree after forcibly retaining both roots.
  This is the finite product-space version of conditioning on the roots and
  removes their otherwise macroscopic bounded differences.
* Pair tests are split into the nine ordered repeated-apex, repeated-leaf,
  and singleton-leaf role pairs.  This retains all literal common-colour
  witnesses and corrects the constant-factor omission in the printed P5
  expectation calculation.

All hypotheses and conclusions below are literal finite inequalities; no
asymptotic notation is hidden in the statements.
-/

namespace Erdos136
namespace AuxConcentration

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The universal candidate family -/

/-- Proof-free data underlying a triangle block. -/
structure RawTriangleBlock (n k : ℕ) where
  apex : Fin n
  left : Fin n
  right : Fin n
  repeated : Fin k
  singleton : Fin k
  deriving DecidableEq, Fintype

def RawTriangleBlock.Valid {n k : ℕ} (b : RawTriangleBlock n k) : Prop :=
  b.apex ≠ b.left ∧ b.apex ≠ b.right ∧ b.left < b.right ∧
    b.repeated ≠ b.singleton

def RawTriangleBlock.toTriangleBlock {n k : ℕ} (b : RawTriangleBlock n k)
    (h : b.Valid) : TriangleBlock n k where
  apex := b.apex
  left := b.left
  right := b.right
  apex_ne_left := h.1
  apex_ne_right := h.2.1
  left_lt_right := h.2.2.1
  repeated := b.repeated
  singleton := b.singleton
  colors_ne := h.2.2.2

/-- Valid proof-free data are equivalent to the proof-carrying block type. -/
def triangleBlockEquiv (n k : ℕ) :
    TriangleBlock n k ≃ {b : RawTriangleBlock n k // b.Valid} where
  toFun b := ⟨⟨b.apex, b.left, b.right, b.repeated, b.singleton⟩,
    b.apex_ne_left, b.apex_ne_right, b.left_lt_right, b.colors_ne⟩
  invFun b := b.1.toTriangleBlock b.2
  left_inv b := by cases b; rfl
  right_inv b := by rcases b with ⟨b, hb⟩; cases b; rfl

noncomputable instance triangleBlockFintype (n k : ℕ) :
    Fintype (TriangleBlock n k) :=
  Fintype.ofEquiv {b : RawTriangleBlock n k // b.Valid}
    (triangleBlockEquiv n k).symm

/-- Every valid ordered triangle block and ordered pair of distinct colours. -/
def allTriangleBlocks (n k : ℕ) : Finset (TriangleBlock n k) := Finset.univ

@[simp] theorem mem_allTriangleBlocks {n k : ℕ} (b : TriangleBlock n k) :
    b ∈ allTriangleBlocks n k := by simp [allTriangleBlocks]

abbrev OrderedPairLt (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

abbrev AvoidPair {n : ℕ} (p : OrderedPairLt n) :=
  {a : Fin n // a ≠ p.val.1 ∧ a ≠ p.val.2}

abbrev DistinctColorPair (k : ℕ) := {p : Fin k × Fin k // p.1 ≠ p.2}

abbrev TriangleChoice (n k : ℕ) :=
  (Σ p : OrderedPairLt n, AvoidPair p) × DistinctColorPair k

def triangleBlockChoiceEquiv (n k : ℕ) :
    TriangleBlock n k ≃ TriangleChoice n k where
  toFun b :=
    ⟨⟨⟨(b.left, b.right), b.left_lt_right⟩,
       ⟨b.apex, ⟨b.apex_ne_left, b.apex_ne_right⟩⟩⟩,
     ⟨(b.repeated, b.singleton), b.colors_ne⟩⟩
  invFun q :=
    { apex := q.1.2.1
      left := q.1.1.val.1
      right := q.1.1.val.2
      apex_ne_left := q.1.2.2.1
      apex_ne_right := q.1.2.2.2
      left_lt_right := q.1.1.2
      repeated := q.2.val.1
      singleton := q.2.val.2
      colors_ne := q.2.2 }
  left_inv b := by cases b; rfl
  right_inv q := by
    rcases q with
      ⟨⟨⟨⟨l, r⟩, hlr⟩, ⟨a, ha⟩⟩,
       ⟨⟨i, j⟩, hij⟩⟩
    rfl

def avoidPairEquivFinset {n : ℕ} (p : OrderedPairLt n) :
    AvoidPair p ≃ {a : Fin n // a ∈ ((Finset.univ.erase p.val.1).erase p.val.2)} where
  toFun a := ⟨a.1, by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨a.2.2, a.2.1⟩⟩
  invFun a := ⟨a.1, ⟨
    (Finset.mem_erase.1 (Finset.mem_erase.1 a.2).2).1,
    (Finset.mem_erase.1 a.2).1⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem card_avoidPair {n : ℕ} (p : OrderedPairLt n) :
    Fintype.card (AvoidPair p) = n - 2 := by
  rw [Fintype.card_congr (avoidPairEquivFinset p), Fintype.card_coe]
  calc
    ((Finset.univ.erase p.val.1).erase p.val.2).card =
        (Finset.univ.erase p.val.1).card - 1 :=
      Finset.card_erase_of_mem (by simp [ne_of_gt p.2])
    _ = (Finset.univ.card - 1) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ p.val.1)]
    _ = n - 2 := by simp; omega

def distinctColorPairEquivFinset (k : ℕ) :
    DistinctColorPair k ≃ {p : Fin k × Fin k // p ∈ Finset.univ.offDiag} where
  toFun p := ⟨p.1, Finset.mem_offDiag.2
    ⟨Finset.mem_univ _, Finset.mem_univ _, p.2⟩⟩
  invFun p := ⟨p.1, (Finset.mem_offDiag.1 p.2).2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem card_distinctColorPair (k : ℕ) :
    Fintype.card (DistinctColorPair k) = k * (k - 1) := by
  rw [Fintype.card_congr (distinctColorPairEquivFinset k),
    Fintype.card_coe, Finset.offDiag_card]
  simp only [Finset.card_univ, Fintype.card_fin]
  calc
    k * k - k = k * k - k * 1 := by simp
    _ = k * (k - 1) := (Nat.mul_sub_left_distrib k k 1).symm

def orderedPairLtEquivFinset (n : ℕ) :
    OrderedPairLt n ≃
      {p : Fin n × Fin n //
        p ∈ ((Finset.univ ×ˢ Finset.univ).filter fun q ↦ q.1 < q.2)} where
  toFun p := ⟨p.1, by simp [p.2]⟩
  invFun p := ⟨p.1, (Finset.mem_filter.1 p.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem card_orderedPairLt (n : ℕ) :
    Fintype.card (OrderedPairLt n) = n.choose 2 := by
  rw [Fintype.card_congr (orderedPairLtEquivFinset n), Fintype.card_coe]
  simpa using
    (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin n))))

theorem card_triangleBlock (n k : ℕ) :
    Fintype.card (TriangleBlock n k) =
      (n.choose 2 * (n - 2)) * (k * (k - 1)) := by
  rw [Fintype.card_congr (triangleBlockChoiceEquiv n k),
    Fintype.card_prod, Fintype.card_sigma]
  rw [show (∑ i : OrderedPairLt n, Fintype.card (AvoidPair i)) =
      Fintype.card (OrderedPairLt n) * (n - 2) by simp [card_avoidPair]]
  rw [card_orderedPairLt, card_distinctColorPair]

@[simp] theorem card_allTriangleBlocks (n k : ℕ) :
    (allTriangleBlocks n k).card =
      (n.choose 2 * (n - 2)) * (k * (k - 1)) := by
  simp only [allTriangleBlocks, Finset.card_univ, card_triangleBlock]

theorem auxSupport_injective {n k : ℕ} :
    Function.Injective (@TriangleBlock.auxSupport n k) := by
  classical
  intro b c h
  have hp : b.positiveLabels = c.positiveLabels := by
    ext z
    have hz := Finset.ext_iff.mp h (Sum.inr z)
    simpa [TriangleBlock.auxSupport] using hz
  have ha : (b.apex, b.repeated) ∈ c.positiveLabels := by
    rw [← hp]; simp [TriangleBlock.positiveLabels]
  have hl : (b.left, b.repeated) ∈ c.positiveLabels := by
    rw [← hp]; simp [TriangleBlock.positiveLabels]
  have hright : (b.right, b.repeated) ∈ c.positiveLabels := by
    rw [← hp]; simp [TriangleBlock.positiveLabels]
  have hr : b.repeated = c.repeated := by
    simp only [TriangleBlock.positiveLabels, mem_insert, mem_singleton,
      Prod.mk.injEq] at ha hl hright
    by_contra hne
    have ha' : b.apex = c.left ∨ b.apex = c.right := by
      rcases ha with ⟨-, hac⟩ | ⟨-, hac⟩ | ⟨-, hac⟩ |
          ⟨hav, -⟩ | ⟨hav, -⟩
      · exact (hne hac).elim
      · exact (hne hac).elim
      · exact (hne hac).elim
      · exact Or.inl hav
      · exact Or.inr hav
    have hl' : b.left = c.left ∨ b.left = c.right := by
      rcases hl with ⟨-, hlc⟩ | ⟨-, hlc⟩ | ⟨-, hlc⟩ |
          ⟨hlv, -⟩ | ⟨hlv, -⟩
      · exact (hne hlc).elim
      · exact (hne hlc).elim
      · exact (hne hlc).elim
      · exact Or.inl hlv
      · exact Or.inr hlv
    have hh' : b.right = c.left ∨ b.right = c.right := by
      rcases hright with ⟨-, hhc⟩ | ⟨-, hhc⟩ | ⟨-, hhc⟩ |
          ⟨hhv, -⟩ | ⟨hhv, -⟩
      · exact (hne hhc).elim
      · exact (hne hhc).elim
      · exact (hne hhc).elim
      · exact Or.inl hhv
      · exact Or.inr hhv
    rcases ha' with ha' | ha' <;>
      rcases hl' with hl' | hl' <;>
      rcases hh' with hh' | hh'
    all_goals
      first
      | exact b.apex_ne_left (ha'.trans hl'.symm)
      | exact b.apex_ne_right (ha'.trans hh'.symm)
      | exact b.left_ne_right (hl'.trans hh'.symm)
  have hs_mem : (b.left, b.singleton) ∈ c.positiveLabels := by
    rw [← hp]; simp [TriangleBlock.positiveLabels]
  have hs : b.singleton = c.singleton := by
    simp only [TriangleBlock.positiveLabels, mem_insert, mem_singleton,
      Prod.mk.injEq] at hs_mem
    rcases hs_mem with ⟨-, hcol⟩ | ⟨-, hcol⟩ | ⟨-, hcol⟩ |
        ⟨-, hcol⟩ | ⟨-, hcol⟩
    · exact (b.colors_ne (hr.trans hcol.symm)).elim
    · exact (b.colors_ne (hr.trans hcol.symm)).elim
    · exact (b.colors_ne (hr.trans hcol.symm)).elim
    · exact hcol
    · exact hcol
  have hleft_mem : (b.left, b.singleton) ∈ c.positiveLabels := by
    rw [← hp]; simp [TriangleBlock.positiveLabels]
  have hright_mem : (b.right, b.singleton) ∈ c.positiveLabels := by
    rw [← hp]; simp [TriangleBlock.positiveLabels]
  have hleft_cases : b.left = c.left ∨ b.left = c.right := by
    simp only [TriangleBlock.positiveLabels, mem_insert, mem_singleton,
      Prod.mk.injEq] at hleft_mem
    rcases hleft_mem with ⟨-, hcol⟩ | ⟨-, hcol⟩ | ⟨-, hcol⟩ |
        ⟨hv, -⟩ | ⟨hv, -⟩
    · exact (b.colors_ne (hr.trans hcol.symm)).elim
    · exact (b.colors_ne (hr.trans hcol.symm)).elim
    · exact (b.colors_ne (hr.trans hcol.symm)).elim
    · exact Or.inl hv
    · exact Or.inr hv
  have hright_cases : b.right = c.left ∨ b.right = c.right := by
    simp only [TriangleBlock.positiveLabels, mem_insert, mem_singleton,
      Prod.mk.injEq] at hright_mem
    rcases hright_mem with ⟨-, hcol⟩ | ⟨-, hcol⟩ | ⟨-, hcol⟩ |
        ⟨hv, -⟩ | ⟨hv, -⟩
    · exact (b.colors_ne (hr.trans hcol.symm)).elim
    · exact (b.colors_ne (hr.trans hcol.symm)).elim
    · exact (b.colors_ne (hr.trans hcol.symm)).elim
    · exact Or.inl hv
    · exact Or.inr hv
  have hlr : b.left = c.left ∧ b.right = c.right := by
    rcases hleft_cases with hleft | hleft <;>
      rcases hright_cases with hright | hright
    · exact (b.left_ne_right (hleft.trans hright.symm)).elim
    · exact ⟨hleft, hright⟩
    · have hcontra : c.right < c.left := by
        simpa only [hleft, hright] using b.left_lt_right
      exact (not_lt_of_ge (le_of_lt c.left_lt_right) hcontra).elim
    · exact (b.left_ne_right (hleft.trans hright.symm)).elim
  have hapex_mem : (b.apex, b.repeated) ∈ c.positiveLabels := by
    rw [← hp]; simp [TriangleBlock.positiveLabels]
  have hapex_cases :
      b.apex = c.apex ∨ b.apex = c.left ∨ b.apex = c.right := by
    simp only [TriangleBlock.positiveLabels, mem_insert, mem_singleton,
      Prod.mk.injEq] at hapex_mem
    rcases hapex_mem with ⟨hv, -⟩ | ⟨hv, -⟩ | ⟨hv, -⟩ |
        ⟨-, hcol⟩ | ⟨-, hcol⟩
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr hv)
    · exact (c.colors_ne (hr.symm.trans hcol)).elim
    · exact (c.colors_ne (hr.symm.trans hcol)).elim
  have hapex : b.apex = c.apex := by
    rcases hapex_cases with hapex | hapex | hapex
    · exact hapex
    · exact (b.apex_ne_left (hapex.trans hlr.1.symm)).elim
    · exact (b.apex_ne_right (hapex.trans hlr.2.symm)).elim
  cases b
  cases c
  simp_all

/-! ## Retention coordinates -/

/-- The number of independent retention coordinates. -/
abbrev labelCount (n k : ℕ) := Fintype.card (Fin n × Fin k)

/-- A fixed enumeration of the vertex/colour labels. -/
noncomputable def labelEquiv (n k : ℕ) :
    Fin (labelCount n k) ≃ (Fin n × Fin k) :=
  (Fintype.equivFin (Fin n × Fin k)).symm

/-- Turn a Boolean retention vector into the corresponding finite label set. -/
def retainedOfBits {n k : ℕ} (bits : Fin (labelCount n k) → Bool) :
    RetainedLabels n k :=
  Finset.univ.filter fun z ↦ bits ((labelEquiv n k).symm z) = true

@[simp] theorem mem_retainedOfBits {n k : ℕ}
    (bits : Fin (labelCount n k) → Bool) (z : Fin n × Fin k) :
    z ∈ retainedOfBits bits ↔ bits ((labelEquiv n k).symm z) = true := by
  simp [retainedOfBits]

/-- Constant Bernoulli retention probability. -/
def retentionProbability {n k : ℕ} (q : ℝ) :
    Fin (labelCount n k) → ℝ := fun _ ↦ q

/-- Indicator monomial for a cylinder event: coordinates in `P` are forced
present and coordinates in `A` are forced absent. -/
def cylinderMonomial {N : ℕ} (P A : Finset (Fin N))
    (bits : Fin N → Bool) : ℝ :=
  ∏ i, if i ∈ P then (if bits i then 1 else 0)
    else if i ∈ A then (if bits i then 0 else 1) else 1

/-- Exact mass of a finite Bernoulli cylinder. -/
theorem weightedMean_cylinderMonomial {N : ℕ} (q : ℝ)
    (P A : Finset (Fin N)) (hPA : Disjoint P A) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (fun _ : Fin N ↦ q))
        (cylinderMonomial P A) = q ^ P.card * (1 - q) ^ A.card := by
  classical
  let g : Fin N → Bool → ℝ := fun i b ↦
    McDiarmid.bernoulliWeight (fun _ : Fin N ↦ q) i b *
      (if i ∈ P then (if b then 1 else 0)
       else if i ∈ A then (if b then 0 else 1) else 1)
  have hpoint (bits : Fin N → Bool) :
      McDiarmid.productMass
          (McDiarmid.bernoulliWeight (fun _ : Fin N ↦ q)) bits *
          cylinderMonomial P A bits = ∏ i, g i (bits i) := by
    simp only [McDiarmid.productMass, cylinderMonomial, g]
    rw [← Finset.prod_mul_distrib]
  rw [McDiarmid.weightedMean]
  simp_rw [hpoint]
  rw [← Fintype.prod_sum]
  have hcoord (i : Fin N) : ∑ b, g i b =
      if i ∈ P then q else if i ∈ A then 1 - q else 1 := by
    rw [Fintype.sum_bool]
    by_cases hiP : i ∈ P
    · have hiA : i ∉ A := Finset.disjoint_left.mp hPA hiP
      simp [g, McDiarmid.bernoulliWeight, hiP]
    · by_cases hiA : i ∈ A <;>
        simp [g, McDiarmid.bernoulliWeight, hiP, hiA]
  simp_rw [hcoord]
  calc
    (∏ i : Fin N, if i ∈ P then q else if i ∈ A then 1 - q else 1) =
        (∏ i : Fin N, (if i ∈ P then q else 1) *
          (if i ∈ A then 1 - q else 1)) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hiP : i ∈ P
      · have hiA : i ∉ A := Finset.disjoint_left.mp hPA hiP
        simp [hiP, hiA]
      · by_cases hiA : i ∈ A <;> simp [hiP, hiA]
    _ = (∏ i : Fin N, if i ∈ P then q else 1) *
        (∏ i : Fin N, if i ∈ A then 1 - q else 1) := by
      rw [Finset.prod_mul_distrib]
    _ = q ^ P.card * (1 - q) ^ A.card := by
      rw [Fintype.prod_ite_mem, Fintype.prod_ite_mem]
      simp

/-- Retention coordinates required to be present by one block. -/
def positiveCoordinates {n k : ℕ} (b : TriangleBlock n k) :
    Finset (Fin (labelCount n k)) :=
  b.positiveLabels.image (labelEquiv n k).symm

/-- The single retention coordinate required to be absent by one block. -/
def absentCoordinates {n k : ℕ} (b : TriangleBlock n k) :
    Finset (Fin (labelCount n k)) :=
  {((labelEquiv n k).symm (b.apex, b.singleton))}

@[simp] theorem mem_positiveCoordinates_iff {n k : ℕ}
    (b : TriangleBlock n k) (i : Fin (labelCount n k)) :
    i ∈ positiveCoordinates b ↔ (labelEquiv n k i) ∈ b.positiveLabels := by
  classical
  constructor
  · intro hi
    obtain ⟨z, hz, hzi⟩ := Finset.mem_image.mp hi
    simpa only [← hzi, Equiv.apply_symm_apply] using hz
  · intro hi
    exact Finset.mem_image.mpr
      ⟨labelEquiv n k i, hi, (labelEquiv n k).symm_apply_apply i⟩

@[simp] theorem mem_absentCoordinates_iff {n k : ℕ}
    (b : TriangleBlock n k) (i : Fin (labelCount n k)) :
    i ∈ absentCoordinates b ↔ labelEquiv n k i = (b.apex, b.singleton) := by
  classical
  constructor
  · intro hi
    have hi' : i = (labelEquiv n k).symm (b.apex, b.singleton) := by
      simpa [absentCoordinates] using hi
    simpa [hi']
  · intro hi
    have : i = (labelEquiv n k).symm (b.apex, b.singleton) := by
      rw [← hi]
      exact (labelEquiv n k).symm_apply_apply i |>.symm
    simpa [absentCoordinates, this]

@[simp] theorem card_positiveCoordinates {n k : ℕ}
    (b : TriangleBlock n k) : (positiveCoordinates b).card = 5 := by
  classical
  rw [positiveCoordinates,
    Finset.card_image_of_injective _ (labelEquiv n k).symm.injective]
  exact b.positiveLabels_card

@[simp] theorem card_absentCoordinates {n k : ℕ}
    (b : TriangleBlock n k) : (absentCoordinates b).card = 1 := by
  simp [absentCoordinates]

theorem absent_label_not_mem_positiveLabels {n k : ℕ}
    (b : TriangleBlock n k) :
    (b.apex, b.singleton) ∉ b.positiveLabels := by
  simp [TriangleBlock.positiveLabels, b.colors_ne, b.colors_ne.symm,
    b.apex_ne_left, b.apex_ne_right]

theorem positiveCoordinates_disjoint_absentCoordinates {n k : ℕ}
    (b : TriangleBlock n k) :
    Disjoint (positiveCoordinates b) (absentCoordinates b) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiP hiA
  have hp : labelEquiv n k i ∈ b.positiveLabels :=
    (mem_positiveCoordinates_iff b i).mp hiP
  have ha : labelEquiv n k i = (b.apex, b.singleton) :=
    (mem_absentCoordinates_iff b i).mp hiA
  exact absent_label_not_mem_positiveLabels b (ha ▸ hp)

/-- The zero-one indicator of block eligibility in Boolean coordinates. -/
def eligibilityIndicator {n k : ℕ}
    (bits : Fin (labelCount n k) → Bool) (b : TriangleBlock n k) : ℝ :=
  if Eligible (retainedOfBits bits) b then 1 else 0

theorem eligibilityIndicator_eq_cylinderMonomial {n k : ℕ}
    (bits : Fin (labelCount n k) → Bool) (b : TriangleBlock n k) :
    eligibilityIndicator bits b =
      cylinderMonomial (positiveCoordinates b) (absentCoordinates b) bits := by
  classical
  by_cases hE : Eligible (retainedOfBits bits) b
  · rw [eligibilityIndicator, if_pos hE]
    symm
    apply Finset.prod_eq_one
    intro i hi
    by_cases hiP : i ∈ positiveCoordinates b
    · have hret : labelEquiv n k i ∈ retainedOfBits bits :=
        hE.1 ((mem_positiveCoordinates_iff b i).mp hiP)
      have hbit : bits i = true := by
        simpa using (mem_retainedOfBits bits (labelEquiv n k i)).mp hret
      simp [cylinderMonomial, hiP, hbit]
    · by_cases hiA : i ∈ absentCoordinates b
      · have hlabel : labelEquiv n k i = (b.apex, b.singleton) :=
          (mem_absentCoordinates_iff b i).mp hiA
        have hnot : labelEquiv n k i ∉ retainedOfBits bits := by
          simpa [hlabel] using hE.2
        have hbit : bits i = false := by
          cases hbi : bits i with
          | false => rfl
          | true =>
              exfalso
              apply hnot
              exact (mem_retainedOfBits bits (labelEquiv n k i)).mpr (by
                simpa using hbi)
        simp [cylinderMonomial, hiP, hiA, hbit]
      · simp [cylinderMonomial, hiP, hiA]
  · rw [eligibilityIndicator, if_neg hE]
    by_cases hP : b.positiveLabels ⊆ retainedOfBits bits
    · have hA : (b.apex, b.singleton) ∈ retainedOfBits bits := by
        by_contra hnot
        exact hE ⟨hP, hnot⟩
      let i := (labelEquiv n k).symm (b.apex, b.singleton)
      symm
      unfold cylinderMonomial
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      have hiA : i ∈ absentCoordinates b := by
        simp [i, absentCoordinates]
      have hiP : i ∉ positiveCoordinates b := by
        intro hi
        exact Finset.disjoint_left.mp
          (positiveCoordinates_disjoint_absentCoordinates b) hi hiA
      have hbit : bits i = true := by
        simpa [i] using
          (mem_retainedOfBits bits (b.apex, b.singleton)).mp hA
      simp [cylinderMonomial, hiP, hiA, hbit]
    · obtain ⟨z, hzP, hznot⟩ := Finset.not_subset.mp hP
      let i := (labelEquiv n k).symm z
      symm
      unfold cylinderMonomial
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      have hiP : i ∈ positiveCoordinates b := by
        simp [i, hzP]
      have hbit : bits i = false := by
        cases hbi : bits i with
        | false => rfl
        | true =>
            exfalso
            apply hznot
            exact (mem_retainedOfBits bits z).mpr (by simpa [i] using hbi)
      simp [cylinderMonomial, hiP, hbit]

/-- Every universal block has eligibility probability `q^5(1-q)`. -/
theorem weightedMean_eligibilityIndicator {n k : ℕ} (q : ℝ)
    (b : TriangleBlock n k) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ eligibilityIndicator bits b) = q ^ 5 * (1 - q) := by
  change McDiarmid.weightedMean
      (McDiarmid.bernoulliWeight (fun _ : Fin (labelCount n k) ↦ q))
      (fun bits ↦ eligibilityIndicator bits b) = q ^ 5 * (1 - q)
  simp_rw [eligibilityIndicator_eq_cylinderMonomial]
  simpa using
    weightedMean_cylinderMonomial q (positiveCoordinates b) (absentCoordinates b)
      (positiveCoordinates_disjoint_absentCoordinates b)

/-! ## Concrete statistics -/

/-- Graph-edge vertices are active off the diagonal; a labelled vertex is
active precisely when its label was retained. -/
def ActiveAuxVertex {n k : ℕ} (R : RetainedLabels n k) :
    AuxVertex n k → Prop
  | Sum.inl e => ¬e.IsDiag
  | Sum.inr z => z ∈ R

/-- A vertex occurs in the auxiliary hypergraph exactly when it occurs in
the support of an eligible candidate block.  This formulation is convenient
because the ambient sum type also contains diagonal graph pairs and absent
labels, neither of which is part of the actual vertex set. -/
theorem mem_vertexFinset_auxiliaryHypergraph_iff {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {v : AuxVertex n k} :
    v ∈ vertexFinset (auxiliaryHypergraph candidates R) ↔
      ∃ b ∈ candidates, Eligible R b ∧ v ∈ b.auxSupport := by
  classical
  rw [mem_vertexFinset]
  simp only [auxiliaryHypergraph, mem_image, mem_filter]
  constructor
  · rintro ⟨e, ⟨b, ⟨hbc, hbR⟩, rfl⟩, hve⟩
    exact ⟨b, hbc, hbR, hve⟩
  · rintro ⟨b, hbc, hbR, hvb⟩
    exact ⟨b.auxSupport, ⟨b, ⟨hbc, hbR⟩, rfl⟩, hvb⟩

/-- Every vertex of the actual auxiliary hypergraph is active.  Thus the
conditional degree estimates below are stronger than the degree hypotheses
needed by the conflict-free matching theorem, which quantify only over
`vertexFinset H`. -/
theorem active_of_mem_vertexFinset_auxiliaryHypergraph {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {v : AuxVertex n k}
    (hv : v ∈ vertexFinset (auxiliaryHypergraph candidates R)) :
    ActiveAuxVertex R v := by
  classical
  obtain ⟨b, -, hbR, hvb⟩ :=
    mem_vertexFinset_auxiliaryHypergraph_iff.mp hv
  rcases v with e | z
  · simp only [ActiveAuxVertex]
    have he : e ∈ b.graphEdges := by
      simpa [TriangleBlock.auxSupport] using hvb
    simp only [TriangleBlock.graphEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · exact Sym2.mk_isDiag_iff.not.mpr b.apex_ne_left
    · exact Sym2.mk_isDiag_iff.not.mpr b.apex_ne_right
    · exact Sym2.mk_isDiag_iff.not.mpr b.left_ne_right
  · simp only [ActiveAuxVertex]
    apply hbR.1
    simpa [TriangleBlock.auxSupport] using hvb

/-- A literal finite support-size bound.  It is intentionally stated using
the actual `vertexFinset`, while the right side is the cardinality of the
ambient graph-pair/label sum type. -/
theorem card_vertexFinset_auxiliaryHypergraph_le {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k) :
    (vertexFinset (auxiliaryHypergraph candidates R)).card ≤
      (n + 1).choose 2 + n * k := by
  calc
    (vertexFinset (auxiliaryHypergraph candidates R)).card ≤
        Fintype.card (AuxVertex n k) := Finset.card_le_univ _
    _ = (n + 1).choose 2 + n * k := by
      simp [AuxVertex, Fintype.card_sum, Fintype.card_prod, Sym2.card]

/-- An index for a same-old-colour pair of labelled vertices. -/
structure SameColorIndex (n k : ℕ) where
  color : Fin k
  left : Fin n
  right : Fin n
  deriving DecidableEq, Fintype

/-- An index for one of the four multiplicity choices
`(j_x,j_y) ∈ {1,2}²`, based at an ordered pair `(x,y)`. -/
structure PairTestIndex (n : ℕ) where
  x : Fin n
  y : Fin n
  jx : Fin 2
  jy : Fin 2
  deriving DecidableEq, Fintype

namespace PairTestIndex

def leftMultiplicity {n : ℕ} (a : PairTestIndex n) : ℕ := a.jx.1 + 1

def rightMultiplicity {n : ℕ} (a : PairTestIndex n) : ℕ := a.jy.1 + 1

theorem leftMultiplicity_mem {n : ℕ} (a : PairTestIndex n) :
    a.leftMultiplicity = 1 ∨ a.leftMultiplicity = 2 := by
  unfold leftMultiplicity
  omega

theorem rightMultiplicity_mem {n : ℕ} (a : PairTestIndex n) :
    a.rightMultiplicity = 1 ∨ a.rightMultiplicity = 2 := by
  unfold rightMultiplicity
  omega

end PairTestIndex

/-- Degree of a graph vertex in one colour inside one triangle block. -/
def blockColorDegree {n k : ℕ} (b : TriangleBlock n k)
    (x : Fin n) (c : Fin k) : ℕ :=
  (Finset.univ.filter fun y ↦ y ≠ x ∧ b.Paints x y c).card

/-- A block uses a colour on at least one of its three graph edges. -/
def TriangleBlockUsesColor {n k : ℕ} (b : TriangleBlock n k)
    (c : Fin k) : Prop :=
  ∃ x y, b.Paints x y c

/-! ### The three rooted colour roles used by the P5 pair tests -/

/-- The three ways in which a colour can be incident with a rooted triangle. -/
inductive RootRole
  | repeatedApex
  | repeatedLeaf
  | singletonLeaf
  deriving DecidableEq

instance : Fintype RootRole where
  elems := {RootRole.repeatedApex, RootRole.repeatedLeaf,
    RootRole.singletonLeaf}
  complete r := by cases r <;> simp

namespace RootRole

def multiplicity : RootRole → ℕ
  | repeatedApex => 2
  | repeatedLeaf | singletonLeaf => 1

theorem multiplicity_eq_one_or_two (r : RootRole) :
    r.multiplicity = 1 ∨ r.multiplicity = 2 := by
  cases r <;> simp [multiplicity]

end RootRole

/-- A role records both the colour role and the location of the root. -/
def RoleFits {n k : ℕ} (r : RootRole) (b : TriangleBlock n k)
    (root : Fin n) (colour : Fin k) : Prop :=
  match r with
  | .repeatedApex => b.repeated = colour ∧ b.apex = root
  | .repeatedLeaf =>
      b.repeated = colour ∧ (b.left = root ∨ b.right = root)
  | .singletonLeaf =>
      b.singleton = colour ∧ (b.left = root ∨ b.right = root)

/-- A rooted and common-colour witness for the literal Joos--Mubayi pair
test.  Keeping the common colour and the two roles makes this an
integer-valued test weight and removes the lower-order ambiguity when one
block pair has two common colours. -/
structure PairWitness (n k : ℕ) where
  common : Fin k
  leftBlock : TriangleBlock n k
  rightBlock : TriangleBlock n k
  leftRole : RootRole
  rightRole : RootRole
  deriving DecidableEq, Fintype

namespace PairWitness

variable {n k : ℕ}

def support (w : PairWitness n k) : Hypergraph (AuxVertex n k) :=
  {w.leftBlock.auxSupport, w.rightBlock.auxSupport}

def positiveLabels (w : PairWitness n k) : Finset (Fin n × Fin k) :=
  w.leftBlock.positiveLabels ∪ w.rightBlock.positiveLabels

def negativeLabels (w : PairWitness n k) : Finset (Fin n × Fin k) :=
  {(w.leftBlock.apex, w.leftBlock.singleton),
    (w.rightBlock.apex, w.rightBlock.singleton)}

def Geometry (candidates : Finset (TriangleBlock n k))
    (a : PairTestIndex n) (w : PairWitness n k) : Prop :=
  a.x ≠ a.y ∧
    w.leftBlock ∈ candidates ∧ w.rightBlock ∈ candidates ∧
    w.leftBlock ≠ w.rightBlock ∧
    Disjoint w.leftBlock.auxSupport w.rightBlock.auxSupport ∧
    w.leftRole.multiplicity = a.leftMultiplicity ∧
    w.rightRole.multiplicity = a.rightMultiplicity ∧
    RoleFits w.leftRole w.leftBlock a.x w.common ∧
    RoleFits w.rightRole w.rightBlock a.y w.common

def RetentionValid (R : RetainedLabels n k) (w : PairWitness n k) : Prop :=
  w.positiveLabels ⊆ R ∧ Disjoint w.negativeLabels R

def Valid (candidates : Finset (TriangleBlock n k))
    (R : RetainedLabels n k) (a : PairTestIndex n) (w : PairWitness n k) : Prop :=
  w.Geometry candidates a ∧ w.RetentionValid R

def Touches (w : PairWitness n k) (z : Fin n × Fin k) : Prop :=
  z ∈ w.positiveLabels ∨ z ∈ w.negativeLabels

end PairWitness

def geometricWitnesses {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (a : PairTestIndex n) :
    Finset (PairWitness n k) :=
  Finset.univ.filter (PairWitness.Geometry candidates a)

def pairWitnesses {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : PairTestIndex n) : Finset (PairWitness n k) :=
  (geometricWitnesses candidates a).filter (PairWitness.RetentionValid R)

/-- An index for the nine literal root-role pairs.  Splitting the test this
way repairs the omitted singleton-colour roles in the printed P5 count while
keeping every test an ordinary indicator weight. -/
structure PairRoleIndex (n : ℕ) where
  x : Fin n
  y : Fin n
  x_ne_y : x ≠ y
  leftRole : RootRole
  rightRole : RootRole
  deriving DecidableEq, Fintype

def RootRole.multiplicityIndex : RootRole → Fin 2
  | .repeatedApex => 1
  | .repeatedLeaf | .singletonLeaf => 0

@[simp] theorem RootRole.multiplicityIndex_val_add_one (r : RootRole) :
    r.multiplicityIndex.1 + 1 = r.multiplicity := by
  cases r <;> rfl

def PairRoleIndex.toPairTestIndex {n : ℕ} (a : PairRoleIndex n) :
    PairTestIndex n where
  x := a.x
  y := a.y
  jx := a.leftRole.multiplicityIndex
  jy := a.rightRole.multiplicityIndex

def PairRoleIndex.leftCoefficient {n : ℕ} (a : PairRoleIndex n) : ℝ :=
  match a.leftRole with
  | .repeatedApex => 1 / 2
  | .repeatedLeaf | .singletonLeaf => 1

def PairRoleIndex.rightCoefficient {n : ℕ} (a : PairRoleIndex n) : ℝ :=
  match a.rightRole with
  | .repeatedApex => 1 / 2
  | .repeatedLeaf | .singletonLeaf => 1

def geometricRoleWitnesses {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (a : PairRoleIndex n) :
    Finset (PairWitness n k) :=
  (geometricWitnesses candidates a.toPairTestIndex).filter fun w ↦
    w.leftRole = a.leftRole ∧ w.rightRole = a.rightRole

def pairRoleWitnesses {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : PairRoleIndex n) : Finset (PairWitness n k) :=
  (geometricRoleWitnesses candidates a).filter (PairWitness.RetentionValid R)

/-- Neighbours joined to `root` by an edge painted `colour` in `b`. -/
def paintedNeighbors {n k : ℕ} (b : TriangleBlock n k)
    (root : Fin n) (colour : Fin k) : Finset (Fin n) :=
  Finset.univ.filter fun z ↦ z ≠ root ∧ b.Paints root z colour

@[simp] theorem mem_paintedNeighbors_iff {n k : ℕ}
    (b : TriangleBlock n k) (root z : Fin n) (colour : Fin k) :
    z ∈ paintedNeighbors b root colour ↔ z ≠ root ∧ b.Paints root z colour := by
  simp [paintedNeighbors]

theorem card_paintedNeighbors_of_roleFits {n k : ℕ}
    (r : RootRole) (b : TriangleBlock n k) (root : Fin n) (colour : Fin k)
    (hfit : RoleFits r b root colour) :
    (paintedNeighbors b root colour).card = r.multiplicity := by
  cases r with
  | repeatedApex =>
      rcases hfit with ⟨rfl, rfl⟩
      rw [show paintedNeighbors b b.apex b.repeated = {b.left, b.right} by
        ext z
        simp [paintedNeighbors, TriangleBlock.Paints, b.apex_ne_left,
          b.apex_ne_right, b.colors_ne]
        rintro (rfl | rfl)
        · exact b.apex_ne_left.symm
        · exact b.apex_ne_right.symm]
      simp [RootRole.multiplicity, b.left_ne_right]
  | repeatedLeaf =>
      rcases hfit with ⟨rfl, rfl | rfl⟩
      · rw [show paintedNeighbors b b.left b.repeated = {b.apex} by
          ext z
          simp [paintedNeighbors, TriangleBlock.Paints, b.apex_ne_left.symm,
            b.left_ne_right, b.colors_ne]
          rintro rfl
          exact b.apex_ne_left]
        rfl
      · rw [show paintedNeighbors b b.right b.repeated = {b.apex} by
          ext z
          simp [paintedNeighbors, TriangleBlock.Paints, b.apex_ne_right.symm,
            b.left_ne_right.symm, b.colors_ne]
          rintro rfl
          exact b.apex_ne_right]
        rfl
  | singletonLeaf =>
      rcases hfit with ⟨rfl, rfl | rfl⟩
      · rw [show paintedNeighbors b b.left b.singleton = {b.right} by
          ext z
          simp [paintedNeighbors, TriangleBlock.Paints, b.apex_ne_left.symm,
            b.left_ne_right, b.colors_ne.symm]
          rintro rfl
          exact b.left_ne_right.symm]
        rfl
      · rw [show paintedNeighbors b b.right b.singleton = {b.left} by
          ext z
          simp [paintedNeighbors, TriangleBlock.Paints, b.apex_ne_right.symm,
            b.left_ne_right.symm, b.colors_ne.symm]
          rintro rfl
          exact b.left_ne_right]
        rfl

def PairWitness.leftPaintedNeighbors {n k : ℕ}
    (w : PairWitness n k) (a : PairRoleIndex n) : Finset (Fin n) :=
  paintedNeighbors w.leftBlock a.x w.common

def PairWitness.rightPaintedNeighbors {n k : ℕ}
    (w : PairWitness n k) (a : PairRoleIndex n) : Finset (Fin n) :=
  paintedNeighbors w.rightBlock a.y w.common

theorem PairWitness.leftPaintedNeighbors_card_of_roleFits {n k : ℕ}
    (w : PairWitness n k) (a : PairRoleIndex n)
    (hfit : RoleFits a.leftRole w.leftBlock a.x w.common) :
    (w.leftPaintedNeighbors a).card = a.leftRole.multiplicity := by
  exact card_paintedNeighbors_of_roleFits _ _ _ _ hfit

theorem PairWitness.rightPaintedNeighbors_card_of_roleFits {n k : ℕ}
    (w : PairWitness n k) (a : PairRoleIndex n)
    (hfit : RoleFits a.rightRole w.rightBlock a.y w.common) :
    (w.rightPaintedNeighbors a).card = a.rightRole.multiplicity := by
  exact card_paintedNeighbors_of_roleFits _ _ _ _ hfit

theorem PairWitness.disjoint_left_rightPaintedNeighbors
    {n k : ℕ} (w : PairWitness n k) (a : PairRoleIndex n)
    (hdisj : Disjoint w.leftBlock.auxSupport w.rightBlock.auxSupport) :
    Disjoint (w.leftPaintedNeighbors a) (w.rightPaintedNeighbors a) := by
  rw [Finset.disjoint_left]
  intro z hzL hzR
  have hpL : w.leftBlock.Paints a.x z w.common :=
    (mem_paintedNeighbors_iff _ _ _ _).mp hzL |>.2
  have hpR : w.rightBlock.Paints a.y z w.common :=
    (mem_paintedNeighbors_iff _ _ _ _).mp hzR |>.2
  exact Finset.disjoint_left.mp hdisj
    (w.leftBlock.paints_other_label_mem hpL)
    (w.rightBlock.paints_other_label_mem hpR)

theorem PairWitness.leftPaintedNeighbors_card_of_mem_geometricRoleWitnesses
    {n k : ℕ} {candidates : Finset (TriangleBlock n k)}
    (w : PairWitness n k) (a : PairRoleIndex n)
    (hw : w ∈ geometricRoleWitnesses candidates a) :
    (w.leftPaintedNeighbors a).card = a.leftRole.multiplicity := by
  have hwm := Finset.mem_filter.mp hw
  have hg := (Finset.mem_filter.mp hwm.1).2
  rcases hwm.2 with ⟨hrl, hrr⟩
  have hfit : RoleFits a.leftRole w.leftBlock a.x w.common := by
    simpa [PairRoleIndex.toPairTestIndex, hrl] using hg.2.2.2.2.2.2.2.1
  exact w.leftPaintedNeighbors_card_of_roleFits a hfit

theorem PairWitness.rightPaintedNeighbors_card_of_mem_geometricRoleWitnesses
    {n k : ℕ} {candidates : Finset (TriangleBlock n k)}
    (w : PairWitness n k) (a : PairRoleIndex n)
    (hw : w ∈ geometricRoleWitnesses candidates a) :
    (w.rightPaintedNeighbors a).card = a.rightRole.multiplicity := by
  have hwm := Finset.mem_filter.mp hw
  have hg := (Finset.mem_filter.mp hwm.1).2
  rcases hwm.2 with ⟨hrl, hrr⟩
  have hfit : RoleFits a.rightRole w.rightBlock a.y w.common := by
    simpa [PairRoleIndex.toPairTestIndex, hrr] using hg.2.2.2.2.2.2.2.2
  exact w.rightPaintedNeighbors_card_of_roleFits a hfit

theorem PairWitness.disjoint_left_rightPaintedNeighbors_of_mem_geometricRoleWitnesses
    {n k : ℕ} {candidates : Finset (TriangleBlock n k)}
    (w : PairWitness n k) (a : PairRoleIndex n)
    (hw : w ∈ geometricRoleWitnesses candidates a) :
    Disjoint (w.leftPaintedNeighbors a) (w.rightPaintedNeighbors a) := by
  have hwm := Finset.mem_filter.mp hw
  have hg := (Finset.mem_filter.mp hwm.1).2
  exact w.disjoint_left_rightPaintedNeighbors a hg.2.2.2.2.1

/-- The eligible block representatives before quotienting by auxiliary
support. -/
def eligibleBlocks {n k : ℕ} (candidates : Finset (TriangleBlock n k))
    (R : RetainedLabels n k) : Finset (TriangleBlock n k) :=
  candidates.filter (Eligible R)

/-- The literal geometric predicate defining a pair test.  The pair consists
of two different, disjoint auxiliary edges with a common colour.  One
oriented member supplies its prescribed incidence at `x`, and the other
supplies its prescribed incidence at `y`. -/
def IsPairTest {n k : ℕ} (candidates : Finset (TriangleBlock n k))
    (R : RetainedLabels n k) (a : PairTestIndex n)
    (S : Finset (TriangleBlock n k)) : Prop :=
  let H := auxiliaryHypergraph candidates R
  let Q : Hypergraph (AuxVertex n k) := S.image TriangleBlock.auxSupport
  Q.card = 2 ∧ IsMatching H Q ∧
    ∃ bx bz : TriangleBlock n k, bx ∈ S ∧ bz ∈ S ∧ bx ≠ bz ∧
      ∃ c : Fin k, TriangleBlockUsesColor bx c ∧ TriangleBlockUsesColor bz c ∧
        blockColorDegree bx a.x c = a.leftMultiplicity ∧
        blockColorDegree bz a.y c = a.rightMultiplicity

/-- Pairs of eligible block representatives satisfying a pair test. -/
def pairTestBlockPairs {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : PairTestIndex n) : Finset (Finset (TriangleBlock n k)) :=
  ((eligibleBlocks candidates R).powersetCard 2).filter
    (IsPairTest candidates R a)

/-- The actual set of auxiliary-edge pairs counted by a pair test.  The
image is intentional: it removes duplicate block descriptions of the same
pair of auxiliary edges. -/
def pairTestAuxPairs {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : PairTestIndex n) : Finset (Hypergraph (AuxVertex n k)) :=
  (pairTestBlockPairs candidates R a).image
    (fun S ↦ S.image TriangleBlock.auxSupport)

theorem pairTestAuxPairs_spec {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : PairTestIndex n) {Q : Hypergraph (AuxVertex n k)}
    (hQ : Q ∈ pairTestAuxPairs candidates R a) :
    Q.card = 2 ∧ IsMatching (auxiliaryHypergraph candidates R) Q := by
  classical
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hQ
  have htest := (Finset.mem_filter.mp hS).2
  exact ⟨htest.1, htest.2.1⟩

/-- The raw auxiliary degree as a real-valued random variable. -/
def auxDegreeStatistic {n k : ℕ}
    (candidates : Finset (TriangleBlock n k))
    (bits : Fin (labelCount n k) → Bool) (v : AuxVertex n k) : ℝ :=
  degree (auxiliaryHypergraph candidates (retainedOfBits bits)) v

/-- The raw same-colour labelled codegree. -/
def sameColorCodegreeStatistic {n k : ℕ}
    (candidates : Finset (TriangleBlock n k))
    (bits : Fin (labelCount n k) → Bool) (a : SameColorIndex n k) : ℝ :=
  codegree (auxiliaryHypergraph candidates (retainedOfBits bits))
    {Sum.inr (a.left, a.color), Sum.inr (a.right, a.color)}

/-- The exact cardinality of the geometric auxiliary-edge pair test. -/
def pairTestStatistic {n k : ℕ}
    (candidates : Finset (TriangleBlock n k))
    (bits : Fin (labelCount n k) → Bool) (a : PairTestIndex n) : ℝ :=
  (pairTestAuxPairs candidates (retainedOfBits bits) a).card

/-- The exact cardinality of the three-role common-colour witness test. -/
def pairWitnessStatistic {n k : ℕ}
    (candidates : Finset (TriangleBlock n k))
    (bits : Fin (labelCount n k) → Bool) (a : PairTestIndex n) : ℝ :=
  (pairWitnesses candidates (retainedOfBits bits) a).card

/-- The multiplicity of an auxiliary-edge pair in the witness-weighted
test.  This is the test function passed to the conflict-free matching
theorem. -/
def pairWitnessWeight {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : PairTestIndex n) (Q : Hypergraph (AuxVertex n k)) : ℝ :=
  ((pairWitnesses candidates R a).filter fun w => w.support = Q).card

def pairRoleWitnessStatistic {n k : ℕ}
    (candidates : Finset (TriangleBlock n k))
    (bits : Fin (labelCount n k) → Bool) (a : PairRoleIndex n) : ℝ :=
  (pairRoleWitnesses candidates (retainedOfBits bits) a).card

def pairRoleWitnessWeight {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (a : PairRoleIndex n) (Q : Hypergraph (AuxVertex n k)) : ℝ :=
  ((pairRoleWitnesses candidates R a).filter fun w => w.support = Q).card

/-! The explicit centres occurring in the Joos--Mubayi calculation. -/

/-- The common auxiliary-degree scale
`(5/2) n² k q⁴ (1-q)`, where `q` is the retention probability. -/
def joosMubayiDegreeTarget (n k : ℕ) (q : ℝ) : ℝ :=
  (5 / 2 : ℝ) * (n : ℝ) ^ 2 * (k : ℝ) * q ^ 4 * (1 - q)

/-- The natural same-colour labelled-codegree scale `(1-q)n²`.  The
application uses a fixed explicit multiple of this quantity as an upper
error allowance. -/
def joosMubayiSameColorScale (n : ℕ) (q : ℝ) : ℝ :=
  (1 - q) * (n : ℝ) ^ 2

/-- The exact main term for the `(j_x,j_y)` pair-test cardinality,
`(1-q)² q¹⁰ k³ n⁴/(j_x j_y)`. -/
def joosMubayiPairTarget {n : ℕ} (k : ℕ) (q : ℝ)
    (a : PairTestIndex n) : ℝ :=
  ((1 - q) ^ 2 * q ^ 10 * (k : ℝ) ^ 3 * (n : ℝ) ^ 4) /
    ((a.leftMultiplicity : ℝ) * (a.rightMultiplicity : ℝ))

/-- Corrected leading term for the literal three-role pair test.  The
printed expression in Joos--Mubayi counts only the repeated-colour roles;
the singleton-colour roles needed for P5 give the factor
`4/(j_x^2 j_y^2)`. -/
def correctedPairTarget {n : ℕ} (k : ℕ) (q : ℝ)
    (a : PairTestIndex n) : ℝ :=
  (4 * (1 - q) ^ 2 * q ^ 10 * (k : ℝ) ^ 3 * (n : ℝ) ^ 4) /
    ((a.leftMultiplicity : ℝ) ^ 2 * (a.rightMultiplicity : ℝ) ^ 2)

/-- Role-by-role leading centre.  The nine centres sum, after grouping roles
of the same multiplicity, to `correctedPairTarget`. -/
def pairRoleTarget {n : ℕ} (k : ℕ) (q : ℝ)
    (a : PairRoleIndex n) : ℝ :=
  a.leftCoefficient * a.rightCoefficient * (1 - q) ^ 2 * q ^ 10 *
    (k : ℝ) ^ 3 * (n : ℝ) ^ 4

theorem correctedPairTarget_denominator_pos {n : ℕ} (a : PairTestIndex n) :
    0 < (a.leftMultiplicity : ℝ) ^ 2 *
      (a.rightMultiplicity : ℝ) ^ 2 := by
  have hx : 0 < a.leftMultiplicity := by
    rcases a.leftMultiplicity_mem with h | h <;> omega
  have hy : 0 < a.rightMultiplicity := by
    rcases a.rightMultiplicity_mem with h | h <;> omega
  positivity

/-- Exact local role count before the common and other colours are selected.
The argument is the number of available non-root vertices. -/
def rootRoleChoices (m : ℕ) (j : Fin 2) : ℕ :=
  if j.1 = 0 then 2 * m * (m - 1) else m.choose 2

/-- Vertex-disjoint witness count in the universal block family. -/
def disjointWitnessCount (n k : ℕ) (a : PairTestIndex n) : ℕ :=
  k * (k - 1) ^ 2 * rootRoleChoices (n - 2) a.jx *
    rootRoleChoices (n - 4) a.jy

/-- The exceptional eligible witnesses in which two singleton-role blocks
share their deleted apex copy. -/
def sharedApexWitnessCount (n k : ℕ) (a : PairTestIndex n) : ℕ :=
  if a.leftMultiplicity = 1 ∧ a.rightMultiplicity = 1 then
    k * (k - 1) * (k - 2) * (n - 2) * (n - 3) * (n - 4)
  else 0

/-- Closed finite-product expectation of the witness statistic. -/
def exactWitnessMean {n : ℕ} (k : ℕ) (q : ℝ)
    (a : PairTestIndex n) : ℝ :=
  q ^ 10 * ((1 - q) ^ 2 * disjointWitnessCount n k a +
    (1 - q) * sharedApexWitnessCount n k a)

def rootRoleChoiceCount (m : ℕ) : RootRole → ℕ
  | .repeatedApex => m.choose 2
  | .repeatedLeaf | .singletonLeaf => m * (m - 1)

def pairRoleDisjointCount {n : ℕ} (k : ℕ) (a : PairRoleIndex n) : ℕ :=
  k * (k - 1) ^ 2 * rootRoleChoiceCount (n - 2) a.leftRole *
    rootRoleChoiceCount (n - 4) a.rightRole

def pairRoleSharedApexCount {n : ℕ} (k : ℕ) (a : PairRoleIndex n) : ℕ :=
  if a.leftRole = .singletonLeaf ∧ a.rightRole = .singletonLeaf then
    k * (k - 1) * (k - 2) * (n - 2) * (n - 3) * (n - 4)
  else 0

def pairRoleExactMean {n : ℕ} (k : ℕ) (q : ℝ)
    (a : PairRoleIndex n) : ℝ :=
  q ^ 10 * ((1 - q) ^ 2 * pairRoleDisjointCount k a +
    (1 - q) * pairRoleSharedApexCount k a)

noncomputable def roleLeadingCoefficient : RootRole → ℝ
  | .repeatedApex => 1 / 2
  | .repeatedLeaf | .singletonLeaf => 1

theorem leftCoefficient_eq_roleLeadingCoefficient {n : ℕ}
    (a : PairRoleIndex n) :
    a.leftCoefficient = roleLeadingCoefficient a.leftRole := by
  cases h : a.leftRole <;>
    simp [PairRoleIndex.leftCoefficient, roleLeadingCoefficient, h]

theorem rightCoefficient_eq_roleLeadingCoefficient {n : ℕ}
    (a : PairRoleIndex n) :
    a.rightCoefficient = roleLeadingCoefficient a.rightRole := by
  cases h : a.rightRole <;>
    simp [PairRoleIndex.rightCoefficient, roleLeadingCoefficient, h]

theorem cast_rootRoleChoiceCount_sub_two {n : ℕ} (hn : 6 ≤ n)
    (r : RootRole) :
    (rootRoleChoiceCount (n - 2) r : ℝ) =
      roleLeadingCoefficient r * (n - 2) * (n - 3) := by
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have h21 : 1 ≤ n - 2 := by omega
  cases r with
  | repeatedApex =>
      rw [rootRoleChoiceCount, Nat.cast_choose_two, Nat.cast_sub h2]
      simp only [roleLeadingCoefficient]
      ring
  | repeatedLeaf =>
      rw [rootRoleChoiceCount, Nat.cast_mul, Nat.cast_sub h21,
        Nat.cast_sub h2]
      simp only [roleLeadingCoefficient]
      ring
  | singletonLeaf =>
      rw [rootRoleChoiceCount, Nat.cast_mul, Nat.cast_sub h21,
        Nat.cast_sub h2]
      simp only [roleLeadingCoefficient]
      ring

theorem cast_rootRoleChoiceCount_sub_four {n : ℕ} (hn : 6 ≤ n)
    (r : RootRole) :
    (rootRoleChoiceCount (n - 4) r : ℝ) =
      roleLeadingCoefficient r * (n - 4) * (n - 5) := by
  have h4 : 4 ≤ n := by omega
  have h5 : 5 ≤ n := by omega
  have h41 : 1 ≤ n - 4 := by omega
  cases r with
  | repeatedApex =>
      rw [rootRoleChoiceCount, Nat.cast_choose_two, Nat.cast_sub h4]
      simp only [roleLeadingCoefficient]
      ring
  | repeatedLeaf =>
      rw [rootRoleChoiceCount, Nat.cast_mul, Nat.cast_sub h41,
        Nat.cast_sub h4]
      simp only [roleLeadingCoefficient]
      ring
  | singletonLeaf =>
      rw [rootRoleChoiceCount, Nat.cast_mul, Nat.cast_sub h41,
        Nat.cast_sub h4]
      simp only [roleLeadingCoefficient]
      ring

theorem roleLeadingCoefficient_mem_Icc (r : RootRole) :
    roleLeadingCoefficient r ∈ Set.Icc (1 / 2 : ℝ) 1 := by
  cases r <;> norm_num [roleLeadingCoefficient]

theorem rootRoleChoiceCount_sub_two_bounds {n : ℕ} (hn : 6 ≤ n)
    (r : RootRole) :
    0 ≤ (rootRoleChoiceCount (n - 2) r : ℝ) ∧
      (rootRoleChoiceCount (n - 2) r : ℝ) ≤ (n : ℝ) ^ 2 ∧
      0 ≤ roleLeadingCoefficient r * (n : ℝ) ^ 2 -
        (rootRoleChoiceCount (n - 2) r : ℝ) ∧
      roleLeadingCoefficient r * (n : ℝ) ^ 2 -
        (rootRoleChoiceCount (n - 2) r : ℝ) ≤ 5 * n := by
  rw [cast_rootRoleChoiceCount_sub_two hn]
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  cases r <;> simp only [roleLeadingCoefficient]
  all_goals repeat' apply And.intro
  all_goals norm_num <;> nlinarith

theorem rootRoleChoiceCount_sub_four_bounds {n : ℕ} (hn : 6 ≤ n)
    (r : RootRole) :
    0 ≤ (rootRoleChoiceCount (n - 4) r : ℝ) ∧
      (rootRoleChoiceCount (n - 4) r : ℝ) ≤ (n : ℝ) ^ 2 ∧
      0 ≤ roleLeadingCoefficient r * (n : ℝ) ^ 2 -
        (rootRoleChoiceCount (n - 4) r : ℝ) ∧
      roleLeadingCoefficient r * (n : ℝ) ^ 2 -
        (rootRoleChoiceCount (n - 4) r : ℝ) ≤ 9 * n := by
  rw [cast_rootRoleChoiceCount_sub_four hn]
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  cases r <;> simp only [roleLeadingCoefficient]
  all_goals repeat' apply And.intro
  all_goals norm_num <;> nlinarith

theorem colourSelectionCount_bounds {k : ℕ} (hk : 1 ≤ k) :
    0 ≤ ((k * (k - 1) ^ 2 : ℕ) : ℝ) ∧
      ((k * (k - 1) ^ 2 : ℕ) : ℝ) ≤ (k : ℝ) ^ 3 ∧
      0 ≤ (k : ℝ) ^ 3 - ((k * (k - 1) ^ 2 : ℕ) : ℝ) ∧
      (k : ℝ) ^ 3 - ((k * (k - 1) ^ 2 : ℕ) : ℝ) ≤
        2 * (k : ℝ) ^ 2 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hcast : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
    simpa only [Nat.cast_one] using (Nat.cast_sub hk :
      (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - (1 : ℕ))
  push_cast
  rw [hcast]
  repeat' apply And.intro
  all_goals nlinarith [sq_nonneg ((k : ℝ) - 1)]

theorem pairRoleRootProduct_bounds {n : ℕ} (hn : 6 ≤ n)
    (r s : RootRole) :
    let L := (rootRoleChoiceCount (n - 2) r : ℝ)
    let R := (rootRoleChoiceCount (n - 4) s : ℝ)
    let T := roleLeadingCoefficient r * roleLeadingCoefficient s * (n : ℝ) ^ 4
    0 ≤ T - L * R ∧ T - L * R ≤ 14 * (n : ℝ) ^ 3 ∧
      0 ≤ T ∧ T ≤ (n : ℝ) ^ 4 := by
  dsimp only
  have hL := rootRoleChoiceCount_sub_two_bounds hn r
  have hR := rootRoleChoiceCount_sub_four_bounds hn s
  have hcL := roleLeadingCoefficient_mem_Icc r
  have hcR := roleLeadingCoefficient_mem_Icc s
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  let L : ℝ := rootRoleChoiceCount (n - 2) r
  let R : ℝ := rootRoleChoiceCount (n - 4) s
  let A : ℝ := roleLeadingCoefficient r * (n : ℝ) ^ 2
  let B : ℝ := roleLeadingCoefficient s * (n : ℝ) ^ 2
  have hA0 : 0 ≤ A := mul_nonneg (le_trans (by norm_num) hcL.1) hn2
  have hB0 : 0 ≤ B := mul_nonneg (le_trans (by norm_num) hcR.1) hn2
  have hAle : A ≤ (n : ℝ) ^ 2 := by
    dsimp [A]
    simpa using mul_le_mul_of_nonneg_right hcL.2 hn2
  have hBle : B ≤ (n : ℝ) ^ 2 := by
    dsimp [B]
    simpa using mul_le_mul_of_nonneg_right hcR.2 hn2
  have hgapL0 : 0 ≤ A - L := hL.2.2.1
  have hgapR0 : 0 ≤ B - R := hR.2.2.1
  have ht1 : (A - L) * B ≤ (5 * (n : ℝ)) * (n : ℝ) ^ 2 :=
    mul_le_mul hL.2.2.2 hBle hB0 (by positivity)
  have ht2 : L * (B - R) ≤ (n : ℝ) ^ 2 * (9 * (n : ℝ)) :=
    mul_le_mul hL.2.1 hR.2.2.2 hgapR0 hn2
  have hgap0 : 0 ≤ A * B - L * R := by
    rw [show A * B - L * R = (A - L) * B + L * (B - R) by ring]
    positivity
  have hgaple : A * B - L * R ≤ 14 * (n : ℝ) ^ 3 := by
    calc
      _ = (A - L) * B + L * (B - R) := by ring
      _ ≤ (5 * (n : ℝ)) * (n : ℝ) ^ 2 +
          (n : ℝ) ^ 2 * (9 * (n : ℝ)) := add_le_add ht1 ht2
      _ = 14 * (n : ℝ) ^ 3 := by ring
  have hT : roleLeadingCoefficient r * roleLeadingCoefficient s * (n : ℝ) ^ 4 =
      A * B := by dsimp [A, B]; ring
  rw [hT]
  refine ⟨hgap0, hgaple, mul_nonneg hA0 hB0, ?_⟩
  calc
    A * B ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ 2 :=
      mul_le_mul hAle hBle hB0 hn2
    _ = (n : ℝ) ^ 4 := by ring

theorem pairRoleDisjointCount_leading_error {n k : ℕ}
    (hn : 6 ≤ n) (hk : 1 ≤ k) (hkn : k ≤ n) (a : PairRoleIndex n) :
    let T := roleLeadingCoefficient a.leftRole *
      roleLeadingCoefficient a.rightRole * (k : ℝ) ^ 3 * (n : ℝ) ^ 4
    0 ≤ T - (pairRoleDisjointCount k a : ℝ) ∧
      T - (pairRoleDisjointCount k a : ℝ) ≤ 16 * (n : ℝ) ^ 6 := by
  dsimp only
  have hC := colourSelectionCount_bounds hk
  have hP := pairRoleRootProduct_bounds hn a.leftRole a.rightRole
  let C : ℝ := ((k * (k - 1) ^ 2 : ℕ) : ℝ)
  let P : ℝ := (rootRoleChoiceCount (n - 2) a.leftRole : ℝ) *
    (rootRoleChoiceCount (n - 4) a.rightRole : ℝ)
  let Troot : ℝ := roleLeadingCoefficient a.leftRole *
    roleLeadingCoefficient a.rightRole * (n : ℝ) ^ 4
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hkn
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hk3 : (k : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 :=
    pow_le_pow_left₀ hk0 hkR 3
  have hk2 : (k : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
    pow_le_pow_left₀ hk0 hkR 2
  have hgapC : (k : ℝ) ^ 3 - C ≤ 2 * (n : ℝ) ^ 2 := by
    dsimp [C]
    exact hC.2.2.2.trans (mul_le_mul_of_nonneg_left hk2 (by norm_num))
  have ht1 : ((k : ℝ) ^ 3 - C) * Troot ≤
      2 * (n : ℝ) ^ 2 * (n : ℝ) ^ 4 :=
    mul_le_mul hgapC hP.2.2.2 hP.2.2.1 (by positivity)
  have hCle : C ≤ (n : ℝ) ^ 3 := by
    dsimp [C]
    exact hC.2.1.trans hk3
  have ht2 : C * (Troot - P) ≤
      (n : ℝ) ^ 3 * (14 * (n : ℝ) ^ 3) :=
    mul_le_mul hCle hP.2.1 hP.1 (by positivity)
  have hcast : (pairRoleDisjointCount k a : ℝ) = C * P := by
    dsimp [C, P, pairRoleDisjointCount]
    push_cast
    ring
  rw [hcast]
  constructor
  · rw [show roleLeadingCoefficient a.leftRole * roleLeadingCoefficient a.rightRole *
        (k : ℝ) ^ 3 * (n : ℝ) ^ 4 - C * P =
      ((k : ℝ) ^ 3 - C) * Troot + C * (Troot - P) by
        dsimp [Troot]; ring]
    exact add_nonneg (mul_nonneg hC.2.2.1 hP.2.2.1)
      (mul_nonneg hC.1 hP.1)
  · calc
      _ = ((k : ℝ) ^ 3 - C) * Troot + C * (Troot - P) := by
        dsimp [Troot]; ring
      _ ≤ 2 * (n : ℝ) ^ 2 * (n : ℝ) ^ 4 +
          (n : ℝ) ^ 3 * (14 * (n : ℝ) ^ 3) := add_le_add ht1 ht2
      _ = 16 * (n : ℝ) ^ 6 := by ring

/-- Exact coordinate influence: the number of geometric witnesses whose
retention predicate reads that coordinate. -/
def pairWitnessExactInfluence {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (a : PairTestIndex n)
    (i : Fin (labelCount n k)) : ℝ :=
  ((geometricWitnesses candidates a).filter fun w =>
    w.Touches (labelEquiv n k i)).card

def pairRoleExactInfluence {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (a : PairRoleIndex n)
    (i : Fin (labelCount n k)) : ℝ :=
  ((geometricRoleWitnesses candidates a).filter fun w =>
    w.Touches (labelEquiv n k i)).card

theorem pairWitness_retentionValid_iff_of_untouched {n k : ℕ}
    (x y : Fin (labelCount n k) → Bool) (i : Fin (labelCount n k))
    (hxy : ∀ j, j ≠ i → x j = y j) (w : PairWitness n k)
    (hw : ¬w.Touches (labelEquiv n k i)) :
    w.RetentionValid (retainedOfBits x) ↔
      w.RetentionValid (retainedOfBits y) := by
  have hmem (u : Fin n × Fin k) (hu : u ≠ labelEquiv n k i) :
      u ∈ retainedOfBits x ↔ u ∈ retainedOfBits y := by
    rw [mem_retainedOfBits, mem_retainedOfBits]
    have hi : (labelEquiv n k).symm u ≠ i := by
      intro heq
      apply hu
      have := congrArg (labelEquiv n k) heq
      simpa using this
    rw [hxy _ hi]
  have hpos : labelEquiv n k i ∉ w.positiveLabels := by
    intro hz
    exact hw (Or.inl hz)
  have hneg : labelEquiv n k i ∉ w.negativeLabels := by
    intro hz
    exact hw (Or.inr hz)
  constructor
  · rintro ⟨hp, hn⟩
    constructor
    · intro u hu
      exact (hmem u (fun h => hpos (h ▸ hu))).1 (hp hu)
    · rw [Finset.disjoint_left] at hn ⊢
      intro u hu huR
      exact hn hu ((hmem u (fun h => hneg (h ▸ hu))).2 huR)
  · rintro ⟨hp, hn⟩
    constructor
    · intro u hu
      exact (hmem u (fun h => hpos (h ▸ hu))).2 (hp hu)
    · rw [Finset.disjoint_left] at hn ⊢
      intro u hu huR
      exact hn hu ((hmem u (fun h => hneg (h ▸ hu))).1 huR)

theorem pairWitnessStatistic_boundedDifference {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (a : PairTestIndex n)
    (i : Fin (labelCount n k)) (x y : Fin (labelCount n k) → Bool)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    |pairWitnessStatistic candidates x a -
        pairWitnessStatistic candidates y a| ≤
      pairWitnessExactInfluence candidates a i := by
  let G := geometricWitnesses candidates a
  let P := G.filter (PairWitness.RetentionValid (retainedOfBits x))
  let Q := G.filter (PairWitness.RetentionValid (retainedOfBits y))
  let T := G.filter fun w => w.Touches (labelEquiv n k i)
  have hPQ : P ⊆ Q ∪ T := by
    intro w hwP
    have hwG := (Finset.mem_filter.1 hwP).1
    have hwV := (Finset.mem_filter.1 hwP).2
    by_cases ht : w.Touches (labelEquiv n k i)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hwG, ht⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.2
        ⟨hwG, (pairWitness_retentionValid_iff_of_untouched x y i hxy w ht).1 hwV⟩)
  have hQP : Q ⊆ P ∪ T := by
    intro w hwQ
    have hwG := (Finset.mem_filter.1 hwQ).1
    have hwV := (Finset.mem_filter.1 hwQ).2
    by_cases ht : w.Touches (labelEquiv n k i)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hwG, ht⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.2
        ⟨hwG, (pairWitness_retentionValid_iff_of_untouched x y i hxy w ht).2 hwV⟩)
  have hp : P.card ≤ Q.card + T.card :=
    (Finset.card_le_card hPQ).trans (Finset.card_union_le Q T)
  have hq : Q.card ≤ P.card + T.card :=
    (Finset.card_le_card hQP).trans (Finset.card_union_le P T)
  have hpR : (P.card : ℝ) ≤ Q.card + T.card := by exact_mod_cast hp
  have hqR : (Q.card : ℝ) ≤ P.card + T.card := by exact_mod_cast hq
  change |(P.card : ℝ) - Q.card| ≤ (T.card : ℝ)
  rw [abs_le]
  constructor <;> linarith

theorem pairRoleWitnessStatistic_boundedDifference {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (a : PairRoleIndex n)
    (i : Fin (labelCount n k)) (x y : Fin (labelCount n k) → Bool)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    |pairRoleWitnessStatistic candidates x a -
        pairRoleWitnessStatistic candidates y a| ≤
      pairRoleExactInfluence candidates a i := by
  let G := geometricRoleWitnesses candidates a
  let P := G.filter (PairWitness.RetentionValid (retainedOfBits x))
  let Q := G.filter (PairWitness.RetentionValid (retainedOfBits y))
  let T := G.filter fun w => w.Touches (labelEquiv n k i)
  have hPQ : P ⊆ Q ∪ T := by
    intro w hwP
    have hwG := (Finset.mem_filter.1 hwP).1
    have hwV := (Finset.mem_filter.1 hwP).2
    by_cases ht : w.Touches (labelEquiv n k i)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hwG, ht⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.2
        ⟨hwG, (pairWitness_retentionValid_iff_of_untouched x y i hxy w ht).1 hwV⟩)
  have hQP : Q ⊆ P ∪ T := by
    intro w hwQ
    have hwG := (Finset.mem_filter.1 hwQ).1
    have hwV := (Finset.mem_filter.1 hwQ).2
    by_cases ht : w.Touches (labelEquiv n k i)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hwG, ht⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.2
        ⟨hwG, (pairWitness_retentionValid_iff_of_untouched x y i hxy w ht).2 hwV⟩)
  have hp : P.card ≤ Q.card + T.card :=
    (Finset.card_le_card hPQ).trans (Finset.card_union_le Q T)
  have hq : Q.card ≤ P.card + T.card :=
    (Finset.card_le_card hQP).trans (Finset.card_union_le P T)
  have hpR : (P.card : ℝ) ≤ Q.card + T.card := by exact_mod_cast hp
  have hqR : (Q.card : ℝ) ≤ P.card + T.card := by exact_mod_cast hq
  change |(P.card : ℝ) - Q.card| ≤ (T.card : ℝ)
  rw [abs_le]
  constructor <;> linarith

/-- Exact finite mean of the repeated--repeated, vertex-disjoint subfamily of
the universal pair test.  It is useful as one explicitly countable part of
the full pair statistic; singleton and one-shared-vertex roles contribute
the finite mean-error term in the application. -/
def universalRepeatedPairExactMean {n : ℕ} (k : ℕ) (q : ℝ)
    (a : PairTestIndex n) : ℝ :=
  ((k * (k - 1) ^ 2 * (n - 2) * (n - 3) * (n - 4) * (n - 5) : ℕ) : ℝ) /
      ((a.leftMultiplicity : ℝ) * (a.rightMultiplicity : ℝ)) *
    q ^ 10 * (1 - q) ^ 2

theorem joosMubayiPairTarget_denominator_pos {n : ℕ} (a : PairTestIndex n) :
    0 < (a.leftMultiplicity : ℝ) * (a.rightMultiplicity : ℝ) := by
  have hx : 0 < a.leftMultiplicity := by
    rcases a.leftMultiplicity_mem with h | h <;> omega
  have hy : 0 < a.rightMultiplicity := by
    rcases a.rightMultiplicity_mem with h | h <;> omega
  positivity

/-- Exact mean of an off-diagonal graph-edge degree for the universal block
family. -/
def universalGraphDegreeTarget (n k : ℕ) (q : ℝ) : ℝ :=
  (3 * (n - 2) * k * (k - 1) : ℕ) * q ^ 5 * (1 - q)

/-- Exact conditional mean of a retained labelled-vertex degree for the
universal block family. -/
def universalLabelDegreeTarget (n k : ℕ) (q : ℝ) : ℝ :=
  (5 * (n - 1).choose 2 * (k - 1) : ℕ) * q ^ 4 * (1 - q)

/-- Piecewise exact degree centre, including the irrelevant diagonal graph
pairs. -/
def universalDegreeTarget (n k : ℕ) (q : ℝ) : AuxVertex n k → ℝ
  | Sum.inl e => if e.IsDiag then 0 else universalGraphDegreeTarget n k q
  | Sum.inr _ => universalLabelDegreeTarget n k q

/-- Exact conditional mean for two distinct retained labels having the same
old colour.  Three apex choices arise when that colour is repeated and one
when it is the singleton colour. -/
def universalSameColorTarget (n k : ℕ) (q : ℝ) :
    SameColorIndex n k → ℝ := fun a ↦
  if a.left = a.right then universalLabelDegreeTarget n k q
  else (4 * (n - 2) * (k - 1) : ℕ) * q ^ 3 * (1 - q)

def universalDegreeDeviation (n : ℕ) : AuxVertex n k → ℝ :=
  fun _ ↦ (n : ℝ) ^ (8 / 3 : ℝ)

def universalCodegreeDeviation (n : ℕ) : SameColorIndex n k → ℝ :=
  fun _ ↦ (n : ℝ) ^ (5 / 3 : ℝ)

def universalPairRoleDeviation (n : ℕ) : PairRoleIndex n → ℝ :=
  fun _ ↦ (n : ℝ) ^ (20 / 3 : ℝ)

def universalPairRoleMeanError (n : ℕ) : PairRoleIndex n → ℝ :=
  fun _ ↦ 65 * (n : ℝ) ^ 6

/-- A single upper degree parameter for the retained auxiliary host.  Taking
the larger of the two exact degree means and adding the concentration
deviation makes the upper half of the CFM near-regularity window literal. -/
def universalHostDegree (n k : ℕ) (q : ℝ) : ℝ :=
  max (universalGraphDegreeTarget n k q)
      (universalLabelDegreeTarget n k q) +
    (n : ℝ) ^ (8 / 3 : ℝ)

/-- The exact additive loss in the common degree window: the spread between
the graph-edge and labelled-vertex means, plus two concentration deviations. -/
def universalHostDegreeError (n k : ℕ) (q : ℝ) : ℝ :=
  max (universalGraphDegreeTarget n k q)
      (universalLabelDegreeTarget n k q) -
    min (universalGraphDegreeTarget n k q)
      (universalLabelDegreeTarget n k q) +
    2 * (n : ℝ) ^ (8 / 3 : ℝ)

/-! ## The explicit simultaneous tail budget -/

/-- A common upper bound for the complete degree, codegree, and pair-test
union bound after inserting the squared-influence estimates. -/
def universalTailBound (n : ℕ) : ℝ :=
  32 * (n : ℝ) ^ 3 *
    Real.exp (-((n : ℝ) ^ (1 / 3 : ℝ)) / 1000000)

theorem universalTailBound_tendsto_zero :
    Filter.Tendsto universalTailBound Filter.atTop (nhds 0) := by
  have hx : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (1 / 3 : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
      tendsto_natCast_atTop_atTop
  have h :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (9 : ℝ) (1 / 1000000 : ℝ) (by norm_num)).comp hx
  have h32 := h.const_mul (32 : ℝ)
  simpa only [mul_zero] using h32.congr' (by
    filter_upwards with n
    have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hp : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ (9 : ℝ) = (n : ℝ) ^ 3 := by
      rw [← Real.rpow_mul hn]
      norm_num
    dsimp [universalTailBound]
    rw [hp]
    rw [show -(1 / 1000000 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) =
      -((n : ℝ) ^ (1 / 3 : ℝ)) / 1000000 by ring]
    ring)

/-- A concrete finite threshold exists beyond which the whole simultaneous
tail budget is strictly below one. -/
theorem eventually_universalTailBound_lt_one :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → universalTailBound n < 1 := by
  have hev : ∀ᶠ n : ℕ in Filter.atTop, universalTailBound n < 1 :=
    universalTailBound_tendsto_zero.eventually (Metric.ball_mem_nhds (0 : ℝ) zero_lt_one) |>.mono
      (by
        intro n hn
        have habs : |universalTailBound n| < 1 := by
          simpa [Real.dist_eq] using hn
        exact lt_of_abs_lt habs)
  exact Filter.eventually_atTop.1 hev

theorem eventually_jmOldColors_le_n {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in Filter.atTop, jmOldColors delta n ≤ n := by
  have hrho : ∀ᶠ n : ℕ in Filter.atTop, jmRho delta n ≤ (1 / 10 : ℝ) :=
    (jmRho_tendsto_zero hdelta).eventually_le_const (by norm_num)
  filter_upwards [hrho, Filter.eventually_ge_atTop (6 : ℕ)] with n hrho hn
  have hnR : (0 : ℝ) ≤ n := by positivity
  have hold : jmOldPaletteReal delta n ≤ (n : ℝ) := by
    unfold jmOldPaletteReal
    have hone : 1 + jmRho delta n ≤ (6 / 5 : ℝ) := by linarith
    calc
      (5 / 6 : ℝ) * n * (1 + jmRho delta n) ≤
          (5 / 6 : ℝ) * n * (6 / 5 : ℝ) := by gcongr
      _ = n := by ring
  have hceil := jmOldColors_lt_add_one delta n
  have hkR : (jmOldColors delta n : ℝ) < (n : ℝ) + 1 :=
    hceil.trans_le (by linarith)
  exact_mod_cast (Nat.lt_add_one_iff.mp (by exact_mod_cast hkR))

theorem eventually_one_le_jmOldColors (delta : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ jmOldColors delta n := by
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hrnonneg : 0 ≤ jmRho delta n := Real.rpow_nonneg (by positivity) _
  have holdpos : 0 < jmOldPaletteReal delta n := by
    unfold jmOldPaletteReal
    positivity
  exact Nat.one_le_ceil_iff.mpr holdpos

theorem jmDeletion_mem_Icc {delta : ℝ} {n : ℕ} (hn : 0 < n) :
    jmDeletion delta n ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨(jmDeletion_pos hn).le, (jmDeletion_lt_one hn).le⟩

/-- Force one labelled retention coordinate to be present. -/
def forceLabel {n k : ℕ} (z : Fin n × Fin k)
    (bits : Fin (labelCount n k) → Bool) : Fin (labelCount n k) → Bool :=
  Function.update bits ((labelEquiv n k).symm z) true

theorem forceLabel_eq_of_retained {n k : ℕ} {z : Fin n × Fin k}
    {bits : Fin (labelCount n k) → Bool} (hz : z ∈ retainedOfBits bits) :
    forceLabel z bits = bits := by
  funext i
  by_cases hi : i = (labelEquiv n k).symm z
  · subst i
    simp [forceLabel, (mem_retainedOfBits bits z).mp hz]
  · simp [forceLabel, hi]

/-- Force both roots of a same-colour codegree to be retained. -/
def forceSameColorRoots {n k : ℕ} (a : SameColorIndex n k)
    (bits : Fin (labelCount n k) → Bool) : Fin (labelCount n k) → Bool :=
  forceLabel (a.right, a.color) (forceLabel (a.left, a.color) bits)

theorem forceSameColorRoots_eq_of_retained {n k : ℕ} {a : SameColorIndex n k}
    {bits : Fin (labelCount n k) → Bool}
    (hl : (a.left, a.color) ∈ retainedOfBits bits)
    (hr : (a.right, a.color) ∈ retainedOfBits bits) :
    forceSameColorRoots a bits = bits := by
  rw [forceSameColorRoots, forceLabel_eq_of_retained hl,
    forceLabel_eq_of_retained hr]

/-- A graph-edge degree is sampled directly.  A labelled degree is sampled
in the conditional product law obtained by forcing its own root label to be
retained.  Diagonal graph pairs, which are not auxiliary vertices of the
construction, are stabilized at the target. -/
def stabilizedDegreeStatistic {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (target : AuxVertex n k → ℝ)
    (bits : Fin (labelCount n k) → Bool) (v : AuxVertex n k) : ℝ :=
  match v with
  | Sum.inl e =>
      if e.IsDiag then target v else auxDegreeStatistic candidates bits v
  | Sum.inr z => auxDegreeStatistic candidates (forceLabel z bits) v

/-- Sample a same-colour codegree in its conditional product law by forcing
both labelled roots to be retained.  The degenerate equal-root case is
stabilized at its target. -/
def stabilizedSameColorStatistic {n k : ℕ}
    (candidates : Finset (TriangleBlock n k))
    (target : SameColorIndex n k → ℝ)
    (bits : Fin (labelCount n k) → Bool) (a : SameColorIndex n k) : ℝ :=
  if a.left = a.right then target a
  else sameColorCodegreeStatistic candidates (forceSameColorRoots a bits) a

/-- Degenerate pair-test indices with equal base vertices are assigned their
target.  Genuine indices retain the exact pair-test cardinality statistic. -/
def stabilizedPairStatistic {n k : ℕ}
    (candidates : Finset (TriangleBlock n k))
    (target : PairTestIndex n → ℝ)
    (bits : Fin (labelCount n k) → Bool) (a : PairTestIndex n) : ℝ :=
  if a.x = a.y then target a else pairTestStatistic candidates bits a

/-- Stabilized version of the three-role witness statistic. -/
def stabilizedPairWitnessStatistic {n k : ℕ}
    (candidates : Finset (TriangleBlock n k))
    (target : PairTestIndex n → ℝ)
    (bits : Fin (labelCount n k) → Bool) (a : PairTestIndex n) : ℝ :=
  if a.x = a.y then target a else pairWitnessStatistic candidates bits a

def stabilizedPairRoleStatistic {n k : ℕ}
    (candidates : Finset (TriangleBlock n k))
    (target : PairRoleIndex n → ℝ)
    (bits : Fin (labelCount n k) → Bool) (a : PairRoleIndex n) : ℝ :=
  if a.x = a.y then target a else pairRoleWitnessStatistic candidates bits a

/-! ## Coordinate influences for the universal auxiliary hypergraph -/

/-- The six retention coordinates on which eligibility of a block depends. -/
def dependencyLabels {n k : ℕ} (b : TriangleBlock n k) : Finset (Fin n × Fin k) :=
  b.positiveLabels ∪ {(b.apex, b.singleton)}

@[simp] theorem dependencyLabels_card {n k : ℕ} (b : TriangleBlock n k) :
    (dependencyLabels b).card = 6 := by
  rw [dependencyLabels, card_union_of_disjoint]
  · simp
  · simp only [Finset.disjoint_singleton_right]
    simp [TriangleBlock.positiveLabels, Ne.symm b.colors_ne,
      b.apex_ne_left, b.apex_ne_right]

@[simp] theorem mem_dependencyLabels {n k : ℕ} (b : TriangleBlock n k)
    (z : Fin n × Fin k) :
    z ∈ dependencyLabels b ↔
      z ∈ b.positiveLabels ∨ z = (b.apex, b.singleton) := by
  simp [dependencyLabels, or_comm]

theorem retained_membership_eq_of_coordinate_eq {n k : ℕ}
    {x y : Fin (labelCount n k) → Bool} {i : Fin (labelCount n k)}
    (hxy : ∀ j, j ≠ i → x j = y j)
    {z : Fin n × Fin k} (hz : z ≠ labelEquiv n k i) :
    (z ∈ retainedOfBits x ↔ z ∈ retainedOfBits y) := by
  rw [mem_retainedOfBits, mem_retainedOfBits, hxy]
  intro hi
  apply hz
  have := congrArg (labelEquiv n k) hi
  simpa using this

theorem eligible_congr_outside {n k : ℕ}
    {x y : Fin (labelCount n k) → Bool} {i : Fin (labelCount n k)}
    (hxy : ∀ j, j ≠ i → x j = y j) (b : TriangleBlock n k)
    (hbi : labelEquiv n k i ∉ dependencyLabels b) :
    Eligible (retainedOfBits x) b ↔ Eligible (retainedOfBits y) b := by
  have hmem (z : Fin n × Fin k) (hz : z ∈ dependencyLabels b) :
      (z ∈ retainedOfBits x ↔ z ∈ retainedOfBits y) :=
    retained_membership_eq_of_coordinate_eq hxy (fun h ↦ hbi (h ▸ hz))
  constructor
  · rintro ⟨hpos, hneg⟩
    refine ⟨?_, ?_⟩
    · intro z hz
      exact (hmem z (by simp [dependencyLabels, hz])).mp (hpos hz)
    · intro hz
      apply hneg
      exact (hmem (b.apex, b.singleton) (by simp [dependencyLabels])).mpr hz
  · rintro ⟨hpos, hneg⟩
    refine ⟨?_, ?_⟩
    · intro z hz
      exact (hmem z (by simp [dependencyLabels, hz])).mpr (hpos hz)
    · intro hz
      apply hneg
      exact (hmem (b.apex, b.singleton) (by simp [dependencyLabels])).mp hz

theorem forceLabel_coordinate_eq {n k : ℕ}
    {x y : Fin (labelCount n k) → Bool} {i : Fin (labelCount n k)}
    (hxy : ∀ j, j ≠ i → x j = y j) (root : Fin n × Fin k) :
    ∀ j, j ≠ i → forceLabel root x j = forceLabel root y j := by
  intro j hj
  by_cases hr : j = (labelEquiv n k).symm root
  · simp [forceLabel, hr]
  · simp [forceLabel, hr, hxy j hj]

theorem forceSameColorRoots_coordinate_eq {n k : ℕ}
    {x y : Fin (labelCount n k) → Bool} {i : Fin (labelCount n k)}
    (hxy : ∀ j, j ≠ i → x j = y j) (a : SameColorIndex n k) :
    ∀ j, j ≠ i → forceSameColorRoots a x j = forceSameColorRoots a y j := by
  exact forceLabel_coordinate_eq
    (forceLabel_coordinate_eq hxy (a.left, a.color)) (a.right, a.color)

/-- Universal blocks containing one specified auxiliary vertex. -/
def blocksThrough {n k : ℕ} (v : AuxVertex n k) : Finset (TriangleBlock n k) :=
  (allTriangleBlocks n k).filter fun b ↦ v ∈ b.auxSupport

/-- Universal blocks containing both roots of a same-colour codegree. -/
def blocksThroughPair {n k : ℕ} (a : SameColorIndex n k) :
    Finset (TriangleBlock n k) :=
  (allTriangleBlocks n k).filter fun b ↦
    Sum.inr (a.left, a.color) ∈ b.auxSupport ∧
      Sum.inr (a.right, a.color) ∈ b.auxSupport

def degreeInfluenceNat {n k : ℕ} (v : AuxVertex n k)
    (i : Fin (labelCount n k)) : ℕ :=
  match v with
  | Sum.inl e =>
      if e.IsDiag then 0 else
        ((blocksThrough v).filter fun b ↦
          labelEquiv n k i ∈ dependencyLabels b).card
  | Sum.inr root =>
      if labelEquiv n k i = root then 0 else
        ((blocksThrough v).filter fun b ↦
          labelEquiv n k i ∈ dependencyLabels b).card

def degreeInfluence {n k : ℕ} (v : AuxVertex n k)
    (i : Fin (labelCount n k)) : ℝ := degreeInfluenceNat v i

def codegreeInfluenceNat {n k : ℕ} (a : SameColorIndex n k)
    (i : Fin (labelCount n k)) : ℕ :=
  if a.left = a.right ∨ labelEquiv n k i = (a.left, a.color) ∨
      labelEquiv n k i = (a.right, a.color) then 0 else
    ((blocksThroughPair a).filter fun b ↦
      labelEquiv n k i ∈ dependencyLabels b).card

def codegreeInfluence {n k : ℕ} (a : SameColorIndex n k)
    (i : Fin (labelCount n k)) : ℝ := codegreeInfluenceNat a i

theorem card_filter_abs_sub_le_affected {α : Type*} [DecidableEq α]
    (S : Finset α) (p q affected : α → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred affected]
    (hout : ∀ a ∈ S, ¬affected a → (p a ↔ q a)) :
    |(((S.filter p).card : ℝ) - ((S.filter q).card : ℝ))| ≤
      ((S.filter affected).card : ℝ) := by
  let P := S.filter p
  let Q := S.filter q
  let A := S.filter affected
  have hPA : P ⊆ Q ∪ A := by
    intro a ha
    by_cases haf : affected a
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, haf⟩)
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,
        (hout a (Finset.mem_filter.mp ha).1 haf).mp (Finset.mem_filter.mp ha).2⟩
  have hQA : Q ⊆ P ∪ A := by
    intro a ha
    by_cases haf : affected a
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1, haf⟩)
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,
        (hout a (Finset.mem_filter.mp ha).1 haf).mpr (Finset.mem_filter.mp ha).2⟩
  have hp : P.card ≤ Q.card + A.card :=
    (Finset.card_le_card hPA).trans (Finset.card_union_le Q A)
  have hq : Q.card ≤ P.card + A.card :=
    (Finset.card_le_card hQA).trans (Finset.card_union_le P A)
  have hpR : (P.card : ℝ) ≤ Q.card + A.card := by exact_mod_cast hp
  have hqR : (Q.card : ℝ) ≤ P.card + A.card := by exact_mod_cast hq
  rw [abs_sub_le_iff]
  constructor <;> dsimp only [P, Q, A] at hpR hqR ⊢ <;> linarith

theorem degree_auxiliary_eq_blocks {n k : ℕ} (R : RetainedLabels n k)
    (v : AuxVertex n k) :
    degree (auxiliaryHypergraph (allTriangleBlocks n k) R) v =
      ((blocksThrough v).filter (Eligible R)).card := by
  classical
  unfold degree auxiliaryHypergraph blocksThrough
  rw [show
      (((allTriangleBlocks n k).filter (Eligible R)).image
          TriangleBlock.auxSupport).filter (fun e ↦ v ∈ e) =
        (((allTriangleBlocks n k).filter fun b ↦
          Eligible R b ∧ v ∈ b.auxSupport).image TriangleBlock.auxSupport) by
    ext e
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨⟨b, ⟨hb, he⟩, rfl⟩, hv⟩
      exact ⟨b, ⟨hb, he, hv⟩, rfl⟩
    · rintro ⟨b, ⟨hb, he, hv⟩, rfl⟩
      exact ⟨⟨b, ⟨hb, he⟩, rfl⟩, hv⟩]
  rw [card_image_of_injective _ auxSupport_injective]
  congr 1
  ext b
  simp only [mem_filter]
  aesop

theorem codegree_auxiliary_eq_blocks {n k : ℕ} (R : RetainedLabels n k)
    (a : SameColorIndex n k) :
    codegree (auxiliaryHypergraph (allTriangleBlocks n k) R)
        {Sum.inr (a.left, a.color), Sum.inr (a.right, a.color)} =
      ((blocksThroughPair a).filter (Eligible R)).card := by
  classical
  unfold codegree auxiliaryHypergraph blocksThroughPair
  rw [show
      (((allTriangleBlocks n k).filter (Eligible R)).image
          TriangleBlock.auxSupport).filter
          (fun e ↦ {Sum.inr (a.left, a.color), Sum.inr (a.right, a.color)} ⊆ e) =
        (((allTriangleBlocks n k).filter fun b ↦ Eligible R b ∧
          Sum.inr (a.left, a.color) ∈ b.auxSupport ∧
          Sum.inr (a.right, a.color) ∈ b.auxSupport).image
            TriangleBlock.auxSupport) by
    ext e
    simp only [mem_filter, mem_image, insert_subset_iff, singleton_subset_iff]
    aesop]
  rw [card_image_of_injective _ auxSupport_injective]
  congr 1
  ext b
  simp only [mem_filter]
  aesop

theorem degree_boundedDiff {n k : ℕ}
    (target : AuxVertex n k → ℝ) (v : AuxVertex n k)
    (i : Fin (labelCount n k)) (x y : Fin (labelCount n k) → Bool)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    |stabilizedDegreeStatistic (allTriangleBlocks n k) target x v -
      stabilizedDegreeStatistic (allTriangleBlocks n k) target y v| ≤
        degreeInfluence v i := by
  classical
  rcases v with e | root
  · by_cases he : e.IsDiag
    · simp [stabilizedDegreeStatistic, degreeInfluence, degreeInfluenceNat, he]
    · simp only [stabilizedDegreeStatistic, he, ↓reduceIte, auxDegreeStatistic]
      rw [degree_auxiliary_eq_blocks, degree_auxiliary_eq_blocks]
      simpa [degreeInfluence, degreeInfluenceNat, he] using
        (card_filter_abs_sub_le_affected (blocksThrough (Sum.inl e)) _ _ _
          (fun b hb hbi ↦ eligible_congr_outside hxy b hbi))
  · by_cases hi : labelEquiv n k i = root
    · have hforce : forceLabel root x = forceLabel root y := by
        funext j
        by_cases hj : j = i
        · subst j
          have hr : i = (labelEquiv n k).symm root := by
            apply (labelEquiv n k).injective
            simpa using hi
          simp [forceLabel, hr]
        · exact forceLabel_coordinate_eq hxy root j hj
      simp [stabilizedDegreeStatistic, degreeInfluence, degreeInfluenceNat, hi,
        hforce]
    · simp only [stabilizedDegreeStatistic, auxDegreeStatistic]
      rw [degree_auxiliary_eq_blocks, degree_auxiliary_eq_blocks]
      simpa [degreeInfluence, degreeInfluenceNat, hi] using
        (card_filter_abs_sub_le_affected (blocksThrough (Sum.inr root)) _ _ _
          (fun b hb hbi ↦ eligible_congr_outside
            (forceLabel_coordinate_eq hxy root) b hbi))

theorem codegree_boundedDiff {n k : ℕ}
    (target : SameColorIndex n k → ℝ) (a : SameColorIndex n k)
    (i : Fin (labelCount n k)) (x y : Fin (labelCount n k) → Bool)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    |stabilizedSameColorStatistic (allTriangleBlocks n k) target x a -
      stabilizedSameColorStatistic (allTriangleBlocks n k) target y a| ≤
        codegreeInfluence a i := by
  classical
  by_cases haa : a.left = a.right
  · simp [stabilizedSameColorStatistic, codegreeInfluence, codegreeInfluenceNat, haa]
  by_cases hil : labelEquiv n k i = (a.left, a.color)
  · have hf : forceSameColorRoots a x = forceSameColorRoots a y := by
      funext j
      by_cases hj : j = i
      · subst j
        have hidx : i = (labelEquiv n k).symm (a.left, a.color) := by
          apply (labelEquiv n k).injective
          simpa using hil
        have hneidx : (labelEquiv n k).symm (a.right, a.color) ≠
            (labelEquiv n k).symm (a.left, a.color) := by
          intro h
          have hp := congrArg (labelEquiv n k) h
          apply haa
          simpa using (congrArg Prod.fst hp).symm
        have hneidx' : (labelEquiv n k).symm (a.left, a.color) ≠
            (labelEquiv n k).symm (a.right, a.color) := Ne.symm hneidx
        simp [forceSameColorRoots, forceLabel, hidx, hneidx, hneidx']
      · exact forceSameColorRoots_coordinate_eq hxy a j hj
    simp [stabilizedSameColorStatistic, codegreeInfluence, codegreeInfluenceNat,
      haa, hil, hf]
  by_cases hir : labelEquiv n k i = (a.right, a.color)
  · have hf : forceSameColorRoots a x = forceSameColorRoots a y := by
      funext j
      by_cases hj : j = i
      · subst j
        have hidx : i = (labelEquiv n k).symm (a.right, a.color) := by
          apply (labelEquiv n k).injective
          simpa using hir
        simp [forceSameColorRoots, forceLabel, hidx]
      · exact forceSameColorRoots_coordinate_eq hxy a j hj
    simp [stabilizedSameColorStatistic, codegreeInfluence, codegreeInfluenceNat,
      haa, hil, hir, hf]
  simp only [stabilizedSameColorStatistic, haa, ↓reduceIte,
    sameColorCodegreeStatistic]
  rw [codegree_auxiliary_eq_blocks, codegree_auxiliary_eq_blocks]
  simpa [codegreeInfluence, codegreeInfluenceNat, haa, hil, hir] using
    (card_filter_abs_sub_le_affected (blocksThroughPair a) _ _ _
      (fun b hb hbi ↦ eligible_congr_outside
        (forceSameColorRoots_coordinate_eq hxy a) b hbi))

theorem card_coordinate_filter {n k : ℕ} (D : Finset (Fin n × Fin k)) :
    ((Finset.univ : Finset (Fin (labelCount n k))).filter fun i ↦
      labelEquiv n k i ∈ D).card = D.card := by
  classical
  rw [← card_image_of_injective _ (labelEquiv n k).injective]
  congr 1
  ext z
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hz
    exact ⟨(labelEquiv n k).symm z, by simpa, by simp⟩

theorem sum_dependency_filter_card {n k : ℕ}
    (S : Finset (TriangleBlock n k)) :
    (∑ i : Fin (labelCount n k),
      (S.filter fun b ↦ labelEquiv n k i ∈ dependencyLabels b).card) =
      ∑ b ∈ S, (dependencyLabels b).card := by
  classical
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (Finset.univ : Finset (Fin (labelCount n k))))
    (t := S) (r := fun i b ↦ labelEquiv n k i ∈ dependencyLabels b)
  simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow,
    card_coordinate_filter] using hdc

theorem sum_family_filter_card {n k : ℕ} (S : Finset (TriangleBlock n k))
    (D : TriangleBlock n k → Finset (Fin n × Fin k)) :
    (∑ i : Fin (labelCount n k),
      (S.filter fun b ↦ labelEquiv n k i ∈ D b).card) =
      ∑ b ∈ S, (D b).card := by
  classical
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (Finset.univ : Finset (Fin (labelCount n k))))
    (t := S) (r := fun i b ↦ labelEquiv n k i ∈ D b)
  simpa only [Finset.bipartiteAbove, Finset.bipartiteBelow,
    card_coordinate_filter] using hdc

theorem sum_degreeInfluenceNat_graph {n k : ℕ} (e : Sym2 (Fin n))
    (he : ¬e.IsDiag) :
    ∑ i, degreeInfluenceNat (Sum.inl e : AuxVertex n k) i =
      6 * (blocksThrough (Sum.inl e : AuxVertex n k)).card := by
  simp only [degreeInfluenceNat, he, ↓reduceIte]
  rw [sum_dependency_filter_card]
  simp [Nat.mul_comm]

theorem sum_degreeInfluenceNat_label {n k : ℕ} (root : Fin n × Fin k) :
    ∑ i, degreeInfluenceNat (Sum.inr root : AuxVertex n k) i =
      5 * (blocksThrough (Sum.inr root : AuxVertex n k)).card := by
  classical
  let S := blocksThrough (Sum.inr root : AuxVertex n k)
  calc
    ∑ i, degreeInfluenceNat (Sum.inr root : AuxVertex n k) i =
        ∑ i, (S.filter fun b ↦ labelEquiv n k i ∈
          (dependencyLabels b).erase root).card := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [degreeInfluenceNat]
      by_cases hir : labelEquiv n k i = root
      · simp [hir]
      · simp [hir, S]
    _ = ∑ b ∈ S, ((dependencyLabels b).erase root).card :=
      sum_family_filter_card S (fun b ↦ (dependencyLabels b).erase root)
    _ = 5 * S.card := by
      calc
        ∑ b ∈ S, ((dependencyLabels b).erase root).card =
            ∑ _b ∈ S, 5 := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [Finset.card_erase_of_mem]
          · simp
          · have hs := (Finset.mem_filter.mp hb).2
            exact (mem_dependencyLabels b root).2 <| Or.inl <| by
              simpa [TriangleBlock.auxSupport] using hs
        _ = 5 * S.card := by simp [Nat.mul_comm]

theorem sum_codegreeInfluenceNat {n k : ℕ} (a : SameColorIndex n k)
    (haa : a.left ≠ a.right) :
    ∑ i, codegreeInfluenceNat a i = 4 * (blocksThroughPair a).card := by
  classical
  let l : Fin n × Fin k := (a.left, a.color)
  let r : Fin n × Fin k := (a.right, a.color)
  let S := blocksThroughPair a
  have hlr : l ≠ r := by
    intro h
    apply haa
    simpa [l, r] using congrArg Prod.fst h
  calc
    ∑ i, codegreeInfluenceNat a i =
        ∑ i, (S.filter fun b ↦ labelEquiv n k i ∈
          ((dependencyLabels b).erase l).erase r).card := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [codegreeInfluenceNat, haa, false_or]
      by_cases hil : labelEquiv n k i = l
      · simp [hil, l]
      · by_cases hir : labelEquiv n k i = r
        · simp [hir, r]
        · simp [hil, hir, l, r, S]
    _ = ∑ b ∈ S, (((dependencyLabels b).erase l).erase r).card :=
      sum_family_filter_card S
        (fun b ↦ ((dependencyLabels b).erase l).erase r)
    _ = 4 * S.card := by
      calc
        ∑ b ∈ S, (((dependencyLabels b).erase l).erase r).card =
            ∑ _b ∈ S, 4 := by
          apply Finset.sum_congr rfl
          intro b hb
          have hs := (Finset.mem_filter.mp hb).2
          have hleft : l ∈ dependencyLabels b := by
            exact (mem_dependencyLabels b l).2 <| Or.inl <| by
              simpa [TriangleBlock.auxSupport, l] using hs.1
          have hright : r ∈ dependencyLabels b := by
            exact (mem_dependencyLabels b r).2 <| Or.inl <| by
              simpa [TriangleBlock.auxSupport, r] using hs.2
          rw [Finset.card_erase_of_mem]
          · rw [Finset.card_erase_of_mem hleft]
            simp
          · exact Finset.mem_erase.mpr ⟨Ne.symm hlr, hright⟩
        _ = 4 * S.card := by simp [Nat.mul_comm]

theorem sum_natCast_sq_le_of_max_sum {N M T : ℕ} (f : Fin N → ℕ)
    (hmax : ∀ i, f i ≤ M) (hsum : ∑ i, f i ≤ T) :
    ∑ i, ((f i : ℝ) ^ 2) ≤ (M : ℝ) * T := by
  calc
    ∑ i, ((f i : ℝ) ^ 2) ≤ ∑ i, (M : ℝ) * f i := by
      apply Finset.sum_le_sum
      intro i hi
      have hiM : (f i : ℝ) ≤ M := by exact_mod_cast hmax i
      have hi0 : (0 : ℝ) ≤ f i := by positivity
      nlinarith
    _ = (M : ℝ) * ∑ i, (f i : ℝ) := by rw [Finset.mul_sum]
    _ ≤ (M : ℝ) * T := by
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast hsum
      · positivity

theorem degreeInfluence_sq_sum_graph_of_counts {n k : ℕ}
    (e : Sym2 (Fin n)) (he : ¬e.IsDiag) (hk : k ≤ n)
    (hmax : ∀ i, degreeInfluenceNat (Sum.inl e : AuxVertex n k) i ≤ 6 * n * k)
    (hcard : (blocksThrough (Sum.inl e : AuxVertex n k)).card ≤
      3 * n * k ^ 2) :
    ∑ i, degreeInfluence (Sum.inl e : AuxVertex n k) i ^ 2 ≤
      (108 : ℝ) * n ^ 5 := by
  have hsum : ∑ i, degreeInfluenceNat (Sum.inl e : AuxVertex n k) i ≤
      18 * n * k ^ 2 := by
    rw [sum_degreeInfluenceNat_graph e he]
    calc
      6 * (blocksThrough (Sum.inl e : AuxVertex n k)).card ≤
          6 * (3 * n * k ^ 2) := Nat.mul_le_mul_left 6 hcard
      _ = 18 * n * k ^ 2 := by ring
  have h := sum_natCast_sq_le_of_max_sum
    (degreeInfluenceNat (n := n) (k := k) (Sum.inl e)) hmax hsum
  simp only [degreeInfluence] at h ⊢
  calc
    ∑ i, (degreeInfluenceNat (Sum.inl e : AuxVertex n k) i : ℝ) ^ 2 ≤
        ((6 * n * k : ℕ) : ℝ) * ((18 * n * k ^ 2 : ℕ) : ℝ) := h
    _ = (108 : ℝ) * n ^ 2 * k ^ 3 := by push_cast; ring
    _ ≤ (108 : ℝ) * n ^ 2 * n ^ 3 := by
      have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
      gcongr
    _ = (108 : ℝ) * n ^ 5 := by ring

theorem degreeInfluence_sq_sum_label_of_counts {n k : ℕ}
    (root : Fin n × Fin k) (hn : 1 ≤ n) (hk : k ≤ n)
    (hmax : ∀ i, degreeInfluenceNat (Sum.inr root : AuxVertex n k) i ≤ 4 * n ^ 2)
    (hcard : (blocksThrough (Sum.inr root : AuxVertex n k)).card ≤
      5 * n ^ 2 * k) :
    ∑ i, degreeInfluence (Sum.inr root : AuxVertex n k) i ^ 2 ≤
      (108 : ℝ) * n ^ 5 := by
  have hsum : ∑ i, degreeInfluenceNat (Sum.inr root : AuxVertex n k) i ≤
      25 * n ^ 2 * k := by
    rw [sum_degreeInfluenceNat_label root]
    calc
      5 * (blocksThrough (Sum.inr root : AuxVertex n k)).card ≤
          5 * (5 * n ^ 2 * k) := Nat.mul_le_mul_left 5 hcard
      _ = 25 * n ^ 2 * k := by ring
  have h := sum_natCast_sq_le_of_max_sum
    (degreeInfluenceNat (n := n) (k := k) (Sum.inr root)) hmax hsum
  simp only [degreeInfluence] at h ⊢
  calc
    ∑ i, (degreeInfluenceNat (Sum.inr root : AuxVertex n k) i : ℝ) ^ 2 ≤
        ((4 * n ^ 2 : ℕ) : ℝ) * ((25 * n ^ 2 * k : ℕ) : ℝ) := h
    _ = (100 : ℝ) * n ^ 4 * k := by push_cast; ring
    _ ≤ (108 : ℝ) * n ^ 4 * n := by
      have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
      calc
        (100 : ℝ) * n ^ 4 * k ≤ (100 : ℝ) * n ^ 4 * n := by gcongr
        _ ≤ (108 : ℝ) * n ^ 4 * n := by
          have hnonneg : (0 : ℝ) ≤ n ^ 4 * n := by positivity
          nlinarith
    _ = (108 : ℝ) * n ^ 5 := by ring

theorem codegreeInfluence_sq_sum_of_counts {n k : ℕ}
    (a : SameColorIndex n k) (haa : a.left ≠ a.right) (hk : k ≤ n)
    (hmax : ∀ i, codegreeInfluenceNat a i ≤ 6 * n)
    (hcard : (blocksThroughPair a).card ≤ 6 * n * k) :
    ∑ i, codegreeInfluence a i ^ 2 ≤ (144 : ℝ) * n ^ 3 := by
  have hsum : ∑ i, codegreeInfluenceNat a i ≤ 24 * n * k := by
    rw [sum_codegreeInfluenceNat a haa]
    calc
      4 * (blocksThroughPair a).card ≤ 4 * (6 * n * k) :=
        Nat.mul_le_mul_left 4 hcard
      _ = 24 * n * k := by ring
  have h := sum_natCast_sq_le_of_max_sum
    (codegreeInfluenceNat (n := n) (k := k) a) hmax hsum
  simp only [codegreeInfluence] at h ⊢
  calc
    ∑ i, (codegreeInfluenceNat a i : ℝ) ^ 2 ≤
        ((6 * n : ℕ) : ℝ) * ((24 * n * k : ℕ) : ℝ) := h
    _ = (144 : ℝ) * n ^ 2 * k := by push_cast; ring
    _ ≤ (144 : ℝ) * n ^ 2 * n := by
      have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
      gcongr
    _ = (144 : ℝ) * n ^ 3 := by ring

/-- Add a harmless unit floor to every coordinate influence.  This avoids
the zero-denominator convention in the McDiarmid display for stabilized
constant indices; it costs only the number of retention coordinates in the
squared budget. -/
def safeInfluence {I : Type*} (f : I → ℝ) (i : I) : ℝ := max 1 (f i)

theorem safeInfluence_nonneg {I : Type*} (f : I → ℝ) (i : I) :
    0 ≤ safeInfluence f i := by simp [safeInfluence]

theorem le_safeInfluence {I : Type*} (f : I → ℝ) (i : I) :
    f i ≤ safeInfluence f i := by exact le_max_right _ _

theorem sum_safeInfluence_sq_le {N : ℕ} (f : Fin N → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    ∑ i, safeInfluence f i ^ 2 ≤ (∑ i, f i ^ 2) + N := by
  calc
    ∑ i, safeInfluence f i ^ 2 ≤ ∑ i, (f i ^ 2 + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases h : f i ≤ 1
      · rw [safeInfluence, max_eq_left h]
        nlinarith [sq_nonneg (f i)]
      · rw [safeInfluence, max_eq_right (le_of_not_ge h)]
        linarith
    _ = (∑ i, f i ^ 2) + N := by simp [Finset.sum_add_distrib]

def safeDegreeInfluence {n k : ℕ} (v : AuxVertex n k)
    (i : Fin (labelCount n k)) : ℝ := safeInfluence (degreeInfluence v) i

def safeCodegreeInfluence {n k : ℕ} (a : SameColorIndex n k)
    (i : Fin (labelCount n k)) : ℝ := safeInfluence (codegreeInfluence a) i

def safePairRoleInfluence {n k : ℕ} (a : PairRoleIndex n)
    (i : Fin (labelCount n k)) : ℝ :=
  safeInfluence (pairRoleExactInfluence (allTriangleBlocks n k) a) i

theorem safeDegree_boundedDiff {n k : ℕ}
    (target : AuxVertex n k → ℝ) (v : AuxVertex n k)
    (i : Fin (labelCount n k)) (x y : Fin (labelCount n k) → Bool)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    |stabilizedDegreeStatistic (allTriangleBlocks n k) target x v -
      stabilizedDegreeStatistic (allTriangleBlocks n k) target y v| ≤
        safeDegreeInfluence v i :=
  (degree_boundedDiff target v i x y hxy).trans (le_safeInfluence _ _)

theorem safeCodegree_boundedDiff {n k : ℕ}
    (target : SameColorIndex n k → ℝ) (a : SameColorIndex n k)
    (i : Fin (labelCount n k)) (x y : Fin (labelCount n k) → Bool)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    |stabilizedSameColorStatistic (allTriangleBlocks n k) target x a -
      stabilizedSameColorStatistic (allTriangleBlocks n k) target y a| ≤
        safeCodegreeInfluence a i :=
  (codegree_boundedDiff target a i x y hxy).trans (le_safeInfluence _ _)

theorem safePairRole_boundedDiff {n k : ℕ}
    (target : PairRoleIndex n → ℝ) (a : PairRoleIndex n)
    (i : Fin (labelCount n k)) (x y : Fin (labelCount n k) → Bool)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    |stabilizedPairRoleStatistic (allTriangleBlocks n k) target x a -
      stabilizedPairRoleStatistic (allTriangleBlocks n k) target y a| ≤
        safePairRoleInfluence a i := by
  by_cases hxyroot : a.x = a.y
  · simp only [stabilizedPairRoleStatistic, hxyroot, if_pos, sub_self, abs_zero]
    exact safeInfluence_nonneg _ _
  · simp only [stabilizedPairRoleStatistic, hxyroot, if_neg]
    exact (pairRoleWitnessStatistic_boundedDifference
      (allTriangleBlocks n k) a i x y hxy).trans (le_safeInfluence _ _)

/-! ## Exact output predicates -/

/-- Conditional near-regularity of all active auxiliary vertices. -/
def DegreesNear {n k : ℕ} (candidates : Finset (TriangleBlock n k))
    (R : RetainedLabels n k) (target error : AuxVertex n k → ℝ) : Prop :=
  ∀ v, ActiveAuxVertex R v →
    |(degree (auxiliaryHypergraph candidates R) v : ℝ) - target v| < error v

/-- The two exact universal degree centres give one common host-degree
window.  This is the form directly used by the near-regularity clause of the
specialized conflict-free matching theorem. -/
theorem degreesNear_universal_common_window {n k : ℕ} {q : ℝ}
    {R : RetainedLabels n k}
    (hnear : DegreesNear (allTriangleBlocks n k) R
      (universalDegreeTarget n k q) (universalDegreeDeviation n))
    {v : AuxVertex n k} (hv : ActiveAuxVertex R v) :
    universalHostDegree n k q - universalHostDegreeError n k q <
        (degree (auxiliaryHypergraph (allTriangleBlocks n k) R) v : ℝ) ∧
      (degree (auxiliaryHypergraph (allTriangleBlocks n k) R) v : ℝ) ≤
        universalHostDegree n k q := by
  have h := hnear v hv
  have ht : universalDegreeTarget n k q v =
      universalGraphDegreeTarget n k q ∨
      universalDegreeTarget n k q v = universalLabelDegreeTarget n k q := by
    rcases v with e | z
    · simp only [ActiveAuxVertex] at hv
      simp only [universalDegreeTarget]
      rw [if_neg hv]
      exact Or.inl rfl
    · exact Or.inr rfl
  have hmin : min (universalGraphDegreeTarget n k q)
      (universalLabelDegreeTarget n k q) ≤ universalDegreeTarget n k q v := by
    rcases ht with ht | ht <;> rw [ht]
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hmax : universalDegreeTarget n k q v ≤
      max (universalGraphDegreeTarget n k q)
        (universalLabelDegreeTarget n k q) := by
    rcases ht with ht | ht <;> rw [ht]
    · exact le_max_left _ _
    · exact le_max_right _ _
  rw [abs_lt] at h
  simp only [universalDegreeDeviation] at h
  constructor
  · unfold universalHostDegree universalHostDegreeError
    linarith
  · unfold universalHostDegree
    linarith

/-- Conditional estimates for pairs of retained labels in one colour. -/
def SameColorCodegreesNear {n k : ℕ}
    (candidates : Finset (TriangleBlock n k)) (R : RetainedLabels n k)
    (target error : SameColorIndex n k → ℝ) : Prop :=
  ∀ a, a.left ≠ a.right →
    (a.left, a.color) ∈ R → (a.right, a.color) ∈ R →
    |(codegree (auxiliaryHypergraph candidates R)
        {Sum.inr (a.left, a.color), Sum.inr (a.right, a.color)} : ℝ) - target a| <
      error a

/-- Exact pair-test cardinality estimates for all ordered base pairs and all
four multiplicity choices. -/
def PairTestsNear {n k : ℕ} (candidates : Finset (TriangleBlock n k))
    (R : RetainedLabels n k) (target error : PairTestIndex n → ℝ) : Prop :=
  ∀ a, a.x ≠ a.y →
    |((pairTestAuxPairs candidates R a).card : ℝ) - target a| < error a

/-- Exact estimates for the three-role, common-colour witness-weighted pair
tests.  Unlike `PairTestsNear`, this predicate retains the common-colour and
role multiplicity needed to cover all P5 obstructions. -/
def PairWitnessesNear {n k : ℕ} (candidates : Finset (TriangleBlock n k))
    (R : RetainedLabels n k) (target error : PairTestIndex n → ℝ) : Prop :=
  ∀ a, a.x ≠ a.y →
    |((pairWitnesses candidates R a).card : ℝ) - target a| < error a

def PairRoleWitnessesNear {n k : ℕ}
    (candidates : Finset (TriangleBlock n k))
    (R : RetainedLabels n k) (target error : PairRoleIndex n → ℝ) : Prop :=
  ∀ a, a.x ≠ a.y →
    |((pairRoleWitnesses candidates R a).card : ℝ) - target a| < error a

/-- The complete retained-host certificate produced by the universal
Bernoulli construction.  Besides the three simultaneous concentration
families, it records the actual-support size and the single common degree
window consumed by the specialized conflict-free matching interface. -/
def UniversalRetainedHostEstimates {n k : ℕ} (q : ℝ)
    (R : RetainedLabels n k) : Prop :=
  DegreesNear (allTriangleBlocks n k) R
      (universalDegreeTarget n k q) (universalDegreeDeviation n) ∧
  SameColorCodegreesNear (allTriangleBlocks n k) R
      (universalSameColorTarget n k q) (universalCodegreeDeviation n) ∧
  PairRoleWitnessesNear (allTriangleBlocks n k) R
      (pairRoleTarget k q)
      (fun a ↦ universalPairRoleDeviation n a +
        universalPairRoleMeanError n a) ∧
  (∀ v ∈ vertexFinset (auxiliaryHypergraph (allTriangleBlocks n k) R),
    universalHostDegree n k q - universalHostDegreeError n k q <
        (degree (auxiliaryHypergraph (allTriangleBlocks n k) R) v : ℝ) ∧
      (degree (auxiliaryHypergraph (allTriangleBlocks n k) R) v : ℝ) ≤
        universalHostDegree n k q) ∧
  (vertexFinset (auxiliaryHypergraph (allTriangleBlocks n k) R)).card ≤
    (n + 1).choose 2 + n * k

theorem universalRetainedHostEstimates_of_near {n k : ℕ} {q : ℝ}
    {R : RetainedLabels n k}
    (hdegree : DegreesNear (allTriangleBlocks n k) R
      (universalDegreeTarget n k q) (universalDegreeDeviation n))
    (hcodegree : SameColorCodegreesNear (allTriangleBlocks n k) R
      (universalSameColorTarget n k q) (universalCodegreeDeviation n))
    (hpair : PairRoleWitnessesNear (allTriangleBlocks n k) R
      (pairRoleTarget k q)
      (fun a ↦ universalPairRoleDeviation n a +
        universalPairRoleMeanError n a)) :
    UniversalRetainedHostEstimates q R := by
  refine ⟨hdegree, hcodegree, hpair, ?_,
    card_vertexFinset_auxiliaryHypergraph_le _ _⟩
  intro v hv
  exact degreesNear_universal_common_window hdegree
    (active_of_mem_vertexFinset_auxiliaryHypergraph hv)

/-- If the lower edge of a degree window is positive, every active vertex
really occurs in the auxiliary hypergraph.  In the application this supplies
the converse to `active_of_mem_vertexFinset_auxiliaryHypergraph`, and in
particular shows that every retained label belongs to the actual support. -/
theorem active_mem_vertexFinset_of_degreesNear {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {target error : AuxVertex n k → ℝ}
    (hnear : DegreesNear candidates R target error)
    {v : AuxVertex n k} (hv : ActiveAuxVertex R v)
    (hgap : error v < target v) :
    v ∈ vertexFinset (auxiliaryHypergraph candidates R) := by
  have hwindow := hnear v hv
  have hlower : target v - error v <
      (degree (auxiliaryHypergraph candidates R) v : ℝ) := by
    rw [abs_lt] at hwindow
    linarith [hwindow.1]
  have hdegreeReal : 0 <
      (degree (auxiliaryHypergraph candidates R) v : ℝ) := by
    linarith
  exact degree_pos_iff_mem_vertexFinset.mp (by exact_mod_cast hdegreeReal)

/-- Under a positive degree window the actual vertex set is exactly the
active part of the ambient auxiliary type. -/
theorem mem_vertexFinset_iff_active_of_degreesNear {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {R : RetainedLabels n k}
    {target error : AuxVertex n k → ℝ}
    (hnear : DegreesNear candidates R target error)
    (hgap : ∀ v, ActiveAuxVertex R v → error v < target v)
    (v : AuxVertex n k) :
    v ∈ vertexFinset (auxiliaryHypergraph candidates R) ↔
      ActiveAuxVertex R v := by
  constructor
  · exact active_of_mem_vertexFinset_auxiliaryHypergraph
  · intro hv
    exact active_mem_vertexFinset_of_degreesNear hnear hv (hgap v hv)

/-- Once the common degree window has positive lower endpoint, the actual
hypergraph support is exactly the intended active vertex set.  In particular,
every retained labelled root then occurs in an eligible auxiliary edge. -/
theorem mem_vertexFinset_iff_active_of_universalRetainedHostEstimates
    {n k : ℕ} {q : ℝ} {R : RetainedLabels n k}
    (hhost : UniversalRetainedHostEstimates q R)
    (hgap : universalHostDegreeError n k q < universalHostDegree n k q)
    (v : AuxVertex n k) :
    v ∈ vertexFinset (auxiliaryHypergraph (allTriangleBlocks n k) R) ↔
      ActiveAuxVertex R v := by
  constructor
  · exact active_of_mem_vertexFinset_auxiliaryHypergraph
  · intro hv
    apply active_mem_vertexFinset_of_degreesNear hhost.1 hv
    have ht : universalDegreeTarget n k q v =
        universalGraphDegreeTarget n k q ∨
        universalDegreeTarget n k q v = universalLabelDegreeTarget n k q := by
      rcases v with e | z
      · simp only [ActiveAuxVertex] at hv
        simp only [universalDegreeTarget]
        rw [if_neg hv]
        exact Or.inl rfl
      · exact Or.inr rfl
    have hmin : min (universalGraphDegreeTarget n k q)
        (universalLabelDegreeTarget n k q) ≤
          universalDegreeTarget n k q v := by
      rcases ht with ht | ht <;> rw [ht]
      · exact min_le_left _ _
      · exact min_le_right _ _
    have hpos : 0 <
        min (universalGraphDegreeTarget n k q)
            (universalLabelDegreeTarget n k q) -
          (n : ℝ) ^ (8 / 3 : ℝ) := by
      unfold universalHostDegreeError universalHostDegree at hgap
      linarith
    simp only [universalDegreeDeviation]
    linarith

/-! ## Exact universal incidence counts -/

abbrev TripleSet (n : ℕ) := {S : Finset (Fin n) // S.card = 3}

abbrev MarkedTriple (n : ℕ) := Σ S : TripleSet n, {a : Fin n // a ∈ S.1}

abbrev TriangleSetChoice (n k : ℕ) := MarkedTriple n × DistinctColorPair k

theorem exists_unique_orderedPairLt_of_card_two {n : ℕ}
    (S : Finset (Fin n)) (hS : S.card = 2) :
    ∃! p : OrderedPairLt n, S = {p.1.1, p.1.2} := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hS
  rcases lt_trichotomy x y with hlt | heq | hgt
  · refine ⟨⟨(x, y), hlt⟩, rfl, ?_⟩
    intro p hp
    have hpl : p.1.1 = x ∨ p.1.1 = y := by
      have : p.1.1 ∈ ({p.1.1, p.1.2} : Finset (Fin n)) := by simp
      rw [← hp] at this
      simpa [eq_comm] using this
    have hpr : p.1.2 = x ∨ p.1.2 = y := by
      have : p.1.2 ∈ ({p.1.1, p.1.2} : Finset (Fin n)) := by simp
      rw [← hp] at this
      simpa [eq_comm] using this
    rcases hpl with hpl | hpl <;> rcases hpr with hpr | hpr
    · exact (ne_of_lt p.2 (hpl.trans hpr.symm)).elim
    · exact Subtype.ext (Prod.ext hpl hpr)
    · have : y < x := by simpa [hpl, hpr] using p.2
      exact (not_lt_of_ge (le_of_lt hlt) this).elim
    · exact (ne_of_lt p.2 (hpl.trans hpr.symm)).elim
  · exact (hxy heq).elim
  · refine ⟨⟨(y, x), hgt⟩, by simp [Finset.pair_comm], ?_⟩
    intro p hp
    have hpl : p.1.1 = x ∨ p.1.1 = y := by
      have : p.1.1 ∈ ({p.1.1, p.1.2} : Finset (Fin n)) := by simp
      rw [← hp] at this
      simpa [eq_comm] using this
    have hpr : p.1.2 = x ∨ p.1.2 = y := by
      have : p.1.2 ∈ ({p.1.1, p.1.2} : Finset (Fin n)) := by simp
      rw [← hp] at this
      simpa [eq_comm] using this
    rcases hpl with hpl | hpl <;> rcases hpr with hpr | hpr
    · exact (ne_of_lt p.2 (hpl.trans hpr.symm)).elim
    · have : x < y := by simpa [hpl, hpr] using p.2
      exact (not_lt_of_ge (le_of_lt hgt) this).elim
    · exact Subtype.ext (Prod.ext hpl hpr)
    · exact (ne_of_lt p.2 (hpl.trans hpr.symm)).elim

noncomputable def orderedPairLtOfCardTwo {n : ℕ}
    (S : Finset (Fin n)) (hS : S.card = 2) : OrderedPairLt n :=
  Classical.choose (exists_unique_orderedPairLt_of_card_two S hS)

theorem orderedPairLtOfCardTwo_spec {n : ℕ}
    (S : Finset (Fin n)) (hS : S.card = 2) :
    S = {(orderedPairLtOfCardTwo S hS).1.1,
      (orderedPairLtOfCardTwo S hS).1.2} :=
  (Classical.choose_spec (exists_unique_orderedPairLt_of_card_two S hS)).1

theorem orderedPairLtOfCardTwo_unique {n : ℕ}
    (S : Finset (Fin n)) (hS : S.card = 2) (p : OrderedPairLt n)
    (hp : S = {p.1.1, p.1.2}) : orderedPairLtOfCardTwo S hS = p :=
  ((Classical.choose_spec (exists_unique_orderedPairLt_of_card_two S hS)).2 p hp).symm

noncomputable def triangleSetChoiceEquiv (n k : ℕ) :
    TriangleBlock n k ≃ TriangleSetChoice n k where
  toFun b :=
    ⟨⟨⟨{b.apex, b.left, b.right}, by
          simp [b.apex_ne_left, b.apex_ne_right, b.left_ne_right]⟩,
        ⟨b.apex, by simp⟩⟩,
      ⟨(b.repeated, b.singleton), b.colors_ne⟩⟩
  invFun q := by
    let S := q.1.1.1
    let a := q.1.2.1
    have ha : a ∈ S := q.1.2.2
    have hrest : (S.erase a).card = 2 := by
      rw [Finset.card_erase_of_mem ha]
      simpa [S] using q.1.1.2
    let p := orderedPairLtOfCardTwo (S.erase a) hrest
    exact
      { apex := a
        left := p.1.1
        right := p.1.2
        apex_ne_left := by
          intro h
          have : p.1.1 ∈ S.erase a := by
            have hp : S.erase a = {p.1.1, p.1.2} := by
              dsimp [p]
              exact orderedPairLtOfCardTwo_spec (S.erase a) hrest
            exact hp.symm ▸ (by simp)
          exact (Finset.mem_erase.mp this).1 h.symm
        apex_ne_right := by
          intro h
          have : p.1.2 ∈ S.erase a := by
            have hp : S.erase a = {p.1.1, p.1.2} := by
              dsimp [p]
              exact orderedPairLtOfCardTwo_spec (S.erase a) hrest
            exact hp.symm ▸ (by simp)
          exact (Finset.mem_erase.mp this).1 h.symm
        left_lt_right := p.2
        repeated := q.2.1.1
        singleton := q.2.1.2
        colors_ne := q.2.2 }
  left_inv b := by
    dsimp
    have herase : ({b.apex, b.left, b.right} : Finset (Fin n)).erase b.apex =
        {b.left, b.right} := by
      ext z
      simp [b.apex_ne_left, b.apex_ne_right]
    have hrest : (({b.apex, b.left, b.right} : Finset (Fin n)).erase b.apex).card = 2 := by
      rw [herase]
      simp [b.left_ne_right]
    have hp : orderedPairLtOfCardTwo
        (({b.apex, b.left, b.right} : Finset (Fin n)).erase b.apex) hrest =
        ⟨(b.left, b.right), b.left_lt_right⟩ := by
      apply orderedPairLtOfCardTwo_unique
      exact herase
    cases b
    simp_all
  right_inv q := by
    rcases q with ⟨⟨S, a⟩, colors⟩
    apply Prod.ext
    · apply Sigma.ext
      · apply Subtype.ext
        dsimp
        have ha : a.1 ∈ S.1 := a.2
        have hrest : (S.1.erase a.1).card = 2 := by
          rw [Finset.card_erase_of_mem ha]
          simpa using S.2
        have hp := orderedPairLtOfCardTwo_spec (S.1.erase a.1) hrest
        exact (congrArg (insert a.1) hp).symm.trans
          (Finset.insert_erase ha)
      · have ha : a.1 ∈ S.1 := a.2
        have hrest : (S.1.erase a.1).card = 2 := by
          rw [Finset.card_erase_of_mem ha]
          simpa using S.2
        have hp := orderedPairLtOfCardTwo_spec (S.1.erase a.1) hrest
        have hsets :
            {a.1, (orderedPairLtOfCardTwo (S.1.erase a.1) hrest).1.1,
                (orderedPairLtOfCardTwo (S.1.erase a.1) hrest).1.2} = S.1 :=
          (congrArg (insert a.1) hp).symm.trans (Finset.insert_erase ha)
        apply (Subtype.heq_iff_coe_eq (fun x ↦ Finset.ext_iff.mp hsets x)).2
        rfl
    · rfl

theorem graph_mem_auxSupport_iff_vertices {n k : ℕ}
    (b : TriangleBlock n k) (x y : Fin n) (hxy : x ≠ y) :
    Sum.inl s(x, y) ∈ b.auxSupport ↔
      x ∈ ({b.apex, b.left, b.right} : Finset (Fin n)) ∧
      y ∈ ({b.apex, b.left, b.right} : Finset (Fin n)) := by
  have hinl : (Sum.inl s(x, y) : AuxVertex n k) ∈
      b.graphEdges.image Sum.inl ↔
      s(x, y) ∈ b.graphEdges := by simp
  have hinr : (Sum.inl s(x, y) : AuxVertex n k) ∉
      b.positiveLabels.image Sum.inr := by simp
  rw [TriangleBlock.auxSupport, Finset.mem_union, hinl]
  simp only [hinr, or_false, TriangleBlock.graphEdges, Finset.mem_insert,
    Finset.mem_singleton, Sym2.eq_iff]
  constructor
  · aesop
  · rintro ⟨hx, hy⟩
    rcases hx with (rfl | rfl | rfl) <;> rcases hy with (rfl | rfl | rfl)
    all_goals simp_all [Sym2.eq_iff]

abbrev AvoidTwo {n : ℕ} (x y : Fin n) :=
  {z : Fin n // z ≠ x ∧ z ≠ y}

def avoidTwoEquivFinset {n : ℕ} (x y : Fin n) :
    AvoidTwo x y ≃
      {z : Fin n // z ∈ ((Finset.univ.erase x).erase y)} where
  toFun z := ⟨z.1, by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨z.2.2, z.2.1⟩⟩
  invFun z := ⟨z.1, by
    have hz := z.2
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hz
    exact ⟨hz.2, hz.1⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem card_avoidTwo {n : ℕ} (x y : Fin n) (hxy : x ≠ y) :
    Fintype.card (AvoidTwo x y) = n - 2 := by
  rw [Fintype.card_congr (avoidTwoEquivFinset x y), Fintype.card_coe]
  calc
    ((Finset.univ.erase x).erase y).card =
        (Finset.univ.erase x).card - 1 :=
      Finset.card_erase_of_mem (by simp [hxy.symm])
    _ = (Finset.univ.card - 1) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ x)]
    _ = n - 2 := by simp; omega

def tripleSetOfThird {n : ℕ} (x y : Fin n) (hxy : x ≠ y)
    (z : AvoidTwo x y) : TripleSet n :=
  ⟨{x, y, z.1}, by
    simp [hxy, hxy.symm, z.2.1, z.2.1.symm, z.2.2, z.2.2.symm]⟩

theorem tripleSetOfThird_injective {n : ℕ} (x y : Fin n) (hxy : x ≠ y) :
    Function.Injective (tripleSetOfThird x y hxy) := by
  intro z w h
  apply Subtype.ext
  have hz : z.1 ∈ (tripleSetOfThird x y hxy w).1 := by
    rw [← congrArg Subtype.val h]
    simp [tripleSetOfThird]
  simp only [tripleSetOfThird, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with hz | hz | hz
  · exact (z.2.1 hz).elim
  · exact (z.2.2 hz).elim
  · exact hz

theorem tripleSetOfThird_surjective {n : ℕ} (x y : Fin n) (hxy : x ≠ y) :
    Function.Surjective (fun z : AvoidTwo x y ↦
      (⟨tripleSetOfThird x y hxy z,
        by simp [tripleSetOfThird]⟩ :
      {S : TripleSet n // x ∈ S.1 ∧ y ∈ S.1})) := by
  rintro ⟨S, hx, hy⟩
  have hyerase : y ∈ S.1.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  have hcardx : (S.1.erase x).card = 2 := by
    rw [Finset.card_erase_of_mem hx]
    simpa using S.2
  have hcardxy : ((S.1.erase x).erase y).card = 1 := by
    rw [Finset.card_erase_of_mem hyerase, hcardx]
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcardxy
  have hzmem : z ∈ (S.1.erase x).erase y := by rw [hz]; simp
  have hzx : z ≠ x := by
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hzmem).2).1
  have hzy : z ≠ y := (Finset.mem_erase.mp hzmem).1
  refine ⟨⟨z, hzx, hzy⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  dsimp [tripleSetOfThird]
  have hrecover : insert x (insert y ((S.1.erase x).erase y)) = S.1 := by
    rw [Finset.insert_erase hyerase, Finset.insert_erase hx]
  rw [hz] at hrecover
  simpa using hrecover

def tripleContainingPairEquiv {n : ℕ} (x y : Fin n) (hxy : x ≠ y) :
    AvoidTwo x y ≃ {S : TripleSet n // x ∈ S.1 ∧ y ∈ S.1} :=
  Equiv.ofBijective
    (fun z ↦ ⟨tripleSetOfThird x y hxy z, by simp [tripleSetOfThird]⟩)
    ⟨by
      intro z w h
      exact tripleSetOfThird_injective x y hxy (congrArg Subtype.val h),
      tripleSetOfThird_surjective x y hxy⟩

@[simp] theorem card_tripleContainingPair {n : ℕ}
    (x y : Fin n) (hxy : x ≠ y) :
    Fintype.card {S : TripleSet n // x ∈ S.1 ∧ y ∈ S.1} = n - 2 := by
  rw [← Fintype.card_congr (tripleContainingPairEquiv x y hxy)]
  exact card_avoidTwo x y hxy

abbrev MarkedTripleContainingPair {n : ℕ} (x y : Fin n) :=
  Σ S : {S : TripleSet n // x ∈ S.1 ∧ y ∈ S.1},
    {a : Fin n // a ∈ S.1.1}

def incidentBlockChoiceSubtypeEquiv {n k : ℕ}
    (x y : Fin n) (hxy : x ≠ y) :
    {b : TriangleBlock n k // Sum.inl s(x, y) ∈ b.auxSupport} ≃
      {q : TriangleSetChoice n k // x ∈ q.1.1.1 ∧ y ∈ q.1.1.1} :=
  Equiv.subtypeEquiv (triangleSetChoiceEquiv n k) (fun b ↦ by
    simpa [triangleSetChoiceEquiv] using
      (graph_mem_auxSupport_iff_vertices b x y hxy))

def incidentChoiceReassocEquiv {n k : ℕ}
    (x y : Fin n) :
    {q : TriangleSetChoice n k // x ∈ q.1.1.1 ∧ y ∈ q.1.1.1} ≃
      MarkedTripleContainingPair x y × DistinctColorPair k where
  toFun q :=
    ⟨⟨⟨q.1.1.1, q.2⟩, q.1.1.2⟩, q.1.2⟩
  invFun q :=
    ⟨⟨⟨q.1.1.1, q.1.2⟩, q.2⟩, q.1.1.2⟩
  left_inv q := by rcases q with ⟨⟨⟨S, a⟩, c⟩, h⟩; rfl
  right_inv q := by rcases q with ⟨⟨⟨S, hS⟩, a⟩, c⟩; rfl

def incidentBlockEquiv {n k : ℕ} (x y : Fin n) (hxy : x ≠ y) :
    {b : TriangleBlock n k // Sum.inl s(x, y) ∈ b.auxSupport} ≃
      MarkedTripleContainingPair x y × DistinctColorPair k :=
  (incidentBlockChoiceSubtypeEquiv x y hxy).trans
    (incidentChoiceReassocEquiv x y)

theorem card_markedTripleContainingPair {n : ℕ}
    (x y : Fin n) (hxy : x ≠ y) :
    Fintype.card (MarkedTripleContainingPair x y) = (n - 2) * 3 := by
  rw [Fintype.card_sigma]
  calc
    (∑ S : {S : TripleSet n // x ∈ S.1 ∧ y ∈ S.1},
        Fintype.card {a : Fin n // a ∈ S.1.1}) =
        ∑ _S : {S : TripleSet n // x ∈ S.1 ∧ y ∈ S.1}, 3 := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [Fintype.card_coe]
      exact S.1.2
    _ = Fintype.card {S : TripleSet n // x ∈ S.1 ∧ y ∈ S.1} * 3 := by
      simp
    _ = (n - 2) * 3 := by rw [card_tripleContainingPair x y hxy]

theorem card_universal_graph_incident_blocks {n k : ℕ}
    (x y : Fin n) (hxy : x ≠ y) :
    ((allTriangleBlocks n k).filter fun b ↦
      Sum.inl s(x, y) ∈ b.auxSupport).card =
        3 * (n - 2) * k * (k - 1) := by
  have hsub :
      Fintype.card {b : TriangleBlock n k //
        Sum.inl s(x, y) ∈ b.auxSupport} =
        ((allTriangleBlocks n k).filter fun b ↦
          Sum.inl s(x, y) ∈ b.auxSupport).card := by
    simpa [allTriangleBlocks] using
      (Fintype.card_subtype (fun b : TriangleBlock n k ↦
        Sum.inl s(x, y) ∈ b.auxSupport))
  rw [← hsub, Fintype.card_congr (incidentBlockEquiv x y hxy),
    Fintype.card_prod, card_markedTripleContainingPair x y hxy,
    card_distinctColorPair]
  ac_rfl

theorem label_mem_positiveLabels_iff {n k : ℕ}
    (b : TriangleBlock n k) (x : Fin n) (c : Fin k) :
    (x, c) ∈ b.positiveLabels ↔
      x ∈ ({b.apex, b.left, b.right} : Finset (Fin n)) ∧
        (c = b.repeated ∨ (c = b.singleton ∧ x ≠ b.apex)) := by
  simp only [TriangleBlock.positiveLabels, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨by simp, Or.inl rfl⟩
    · exact ⟨by simp, Or.inl rfl⟩
    · exact ⟨by simp, Or.inl rfl⟩
    · exact ⟨by simp, Or.inr ⟨rfl, b.apex_ne_left.symm⟩⟩
    · exact ⟨by simp, Or.inr ⟨rfl, b.apex_ne_right.symm⟩⟩
  · rintro ⟨hx, hc | ⟨hc, hxa⟩⟩
    · rcases hx with rfl | rfl | rfl <;> simp [hc]
    · rcases hx with rfl | rfl | rfl
      · exact (hxa rfl).elim
      · simp [hc]
      · simp [hc]

abbrev PairAwayFrom {n : ℕ} (x : Fin n) :=
  {T : Finset (Fin n) // T ∈ (Finset.univ.erase x).powersetCard 2}

def pairAwayFromToTriple {n : ℕ} (x : Fin n)
    (T : PairAwayFrom x) : TripleSet n := by
  refine ⟨insert x T.1, ?_⟩
  have hTx : x ∉ T.1 := by
    have hsub := (Finset.mem_powersetCard.mp T.2).1
    intro hx
    exact (Finset.mem_erase.mp (hsub hx)).1 rfl
  rw [Finset.card_insert_of_notMem hTx]
  rw [(Finset.mem_powersetCard.mp T.2).2]

theorem pairAwayFromToTriple_injective {n : ℕ} (x : Fin n) :
    Function.Injective (pairAwayFromToTriple x) := by
  intro T U h
  apply Subtype.ext
  have hxT : x ∉ T.1 := by
    have hsub := (Finset.mem_powersetCard.mp T.2).1
    intro hx
    exact (Finset.mem_erase.mp (hsub hx)).1 rfl
  have hxU : x ∉ U.1 := by
    have hsub := (Finset.mem_powersetCard.mp U.2).1
    intro hx
    exact (Finset.mem_erase.mp (hsub hx)).1 rfl
  have hv := congrArg Subtype.val h
  dsimp [pairAwayFromToTriple] at hv
  simpa [hxT, hxU] using congrArg (fun V ↦ V.erase x) hv

theorem pairAwayFromToTriple_surjective {n : ℕ} (x : Fin n) :
    Function.Surjective (fun T : PairAwayFrom x ↦
      (⟨pairAwayFromToTriple x T, by simp [pairAwayFromToTriple]⟩ :
        {S : TripleSet n // x ∈ S.1})) := by
  rintro ⟨S, hx⟩
  have hcard : (S.1.erase x).card = 2 := by
    rw [Finset.card_erase_of_mem hx]
    simpa using S.2
  have hmem : S.1.erase x ∈ (Finset.univ.erase x).powersetCard 2 := by
    apply Finset.mem_powersetCard.mpr
    refine ⟨?_, hcard⟩
    intro z hz
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hz).1, Finset.mem_univ z⟩
  refine ⟨⟨S.1.erase x, hmem⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  dsimp [pairAwayFromToTriple]
  exact Finset.insert_erase hx

def tripleContainingVertexEquiv {n : ℕ} (x : Fin n) :
    PairAwayFrom x ≃ {S : TripleSet n // x ∈ S.1} :=
  Equiv.ofBijective
    (fun T ↦ ⟨pairAwayFromToTriple x T, by simp [pairAwayFromToTriple]⟩)
    ⟨by
      intro T U h
      exact pairAwayFromToTriple_injective x (congrArg Subtype.val h),
      pairAwayFromToTriple_surjective x⟩

@[simp] theorem card_tripleContainingVertex {n : ℕ} (x : Fin n) :
    Fintype.card {S : TripleSet n // x ∈ S.1} = (n - 1).choose 2 := by
  rw [← Fintype.card_congr (tripleContainingVertexEquiv x),
    Fintype.card_coe, Finset.card_powersetCard]
  simp

abbrev ApexIn {n : ℕ} (S : TripleSet n) := {a : Fin n // a ∈ S.1}

abbrev ApexAway {n : ℕ} (S : TripleSet n) (x : Fin n) :=
  {a : Fin n // a ∈ S.1 ∧ a ≠ x}

abbrev OtherColor {k : ℕ} (c : Fin k) := {d : Fin k // d ≠ c}

@[simp] theorem card_apexIn {n : ℕ} (S : TripleSet n) :
    Fintype.card (ApexIn S) = 3 := by
  rw [Fintype.card_coe]
  exact S.2

@[simp] theorem card_apexAway {n : ℕ} (S : TripleSet n)
    (x : Fin n) (hx : x ∈ S.1) :
    Fintype.card (ApexAway S x) = 2 := by
  let e : ApexAway S x ≃ {a : Fin n // a ∈ S.1.erase x} :=
    { toFun := fun a ↦ ⟨a.1, Finset.mem_erase.mpr ⟨a.2.2, a.2.1⟩⟩
      invFun := fun a ↦ ⟨a.1,
        ⟨(Finset.mem_erase.mp a.2).2, (Finset.mem_erase.mp a.2).1⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Fintype.card_congr e, Fintype.card_coe,
    Finset.card_erase_of_mem hx, S.2]

@[simp] theorem card_otherColor {k : ℕ} (c : Fin k) :
    Fintype.card (OtherColor c) = k - 1 := by
  let e : OtherColor c ≃ {d : Fin k // d ∈ Finset.univ.erase c} :=
    { toFun := fun d ↦ ⟨d.1, by simp [d.2]⟩
      invFun := fun d ↦ ⟨d.1, by simpa using (Finset.mem_erase.mp d.2).1⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Fintype.card_congr e, Fintype.card_coe,
    Finset.card_erase_of_mem (Finset.mem_univ c)]
  simp

abbrev LabelLocalChoice {n k : ℕ} (S : TripleSet n)
    (x : Fin n) (c : Fin k) :=
  {q : ApexIn S × DistinctColorPair k //
    c = q.2.1.1 ∨ (c = q.2.1.2 ∧ x ≠ q.1.1)}

def labelLocalChoiceRoleEquiv {n k : ℕ} (S : TripleSet n)
    (x : Fin n) (c : Fin k) :
    LabelLocalChoice S x c ≃
      (ApexIn S × OtherColor c) ⊕ (ApexAway S x × OtherColor c) where
  toFun q := by
    by_cases hrep : c = q.1.2.1.1
    · exact Sum.inl ⟨q.1.1,
        ⟨q.1.2.1.2, by
          intro h
          exact q.1.2.2 (hrep.symm.trans h.symm)⟩⟩
    · have hsing := q.2.resolve_left hrep
      exact Sum.inr
        ⟨⟨q.1.1.1, q.1.1.2, hsing.2.symm⟩,
          ⟨q.1.2.1.1, by simpa [hsing.1] using q.1.2.2⟩⟩
  invFun q := by
    rcases q with q | q
    · exact ⟨⟨q.1, ⟨(c, q.2.1), q.2.2.symm⟩⟩, Or.inl rfl⟩
    · exact ⟨⟨⟨q.1.1, q.1.2.1⟩, ⟨(q.2.1, c), q.2.2⟩⟩,
        Or.inr ⟨rfl, q.1.2.2.symm⟩⟩
  left_inv q := by
    rcases q with ⟨⟨a, ⟨⟨r, s⟩, hrs⟩⟩, hq⟩
    apply Subtype.ext
    by_cases hrep : c = r
    · simp [hrep]
    · have hsing := hq.resolve_left hrep
      have hsr : s ≠ r := by
        intro hsr
        exact hrep (hsing.1.trans hsr)
      simp [hsing.1, hsr]
  right_inv q := by
    rcases q with q | q
    · rcases q with ⟨a, d⟩
      simp
    · rcases q with ⟨a, d⟩
      simp [d.2.symm]

theorem card_labelLocalChoice {n k : ℕ} (S : TripleSet n)
    (x : Fin n) (c : Fin k) (hx : x ∈ S.1) :
    Fintype.card (LabelLocalChoice S x c) = 5 * (k - 1) := by
  rw [Fintype.card_congr (labelLocalChoiceRoleEquiv S x c),
    Fintype.card_sum, Fintype.card_prod, Fintype.card_prod,
    card_apexIn, card_apexAway S x hx]
  simp only [card_otherColor]
  omega

def labelIncidentBlockChoiceSubtypeEquiv {n k : ℕ}
    (x : Fin n) (c : Fin k) :
    {b : TriangleBlock n k // (x, c) ∈ b.positiveLabels} ≃
      {q : TriangleSetChoice n k //
        x ∈ q.1.1.1 ∧
          (c = q.2.1.1 ∨ (c = q.2.1.2 ∧ x ≠ q.1.2.1))} :=
  Equiv.subtypeEquiv (triangleSetChoiceEquiv n k) (fun b ↦ by
    simpa [triangleSetChoiceEquiv] using label_mem_positiveLabels_iff b x c)

abbrev LabelMarkedTripleChoice {n k : ℕ} (x : Fin n) (c : Fin k) :=
  Σ S : {S : TripleSet n // x ∈ S.1}, LabelLocalChoice S.1 x c

def labelIncidentChoiceReassocEquiv {n k : ℕ}
    (x : Fin n) (c : Fin k) :
    {q : TriangleSetChoice n k //
      x ∈ q.1.1.1 ∧
        (c = q.2.1.1 ∨ (c = q.2.1.2 ∧ x ≠ q.1.2.1))} ≃
      LabelMarkedTripleChoice x c where
  toFun q :=
    ⟨⟨q.1.1.1, q.2.1⟩, ⟨⟨q.1.1.2, q.1.2⟩, q.2.2⟩⟩
  invFun q :=
    ⟨⟨⟨q.1.1, q.2.1.1⟩, q.2.1.2⟩, ⟨q.1.2, q.2.2⟩⟩
  left_inv q := by rcases q with ⟨⟨⟨S, a⟩, colors⟩, h⟩; rfl
  right_inv q := by
    rcases q with ⟨⟨S, hS⟩, ⟨⟨a, colors⟩, hlocal⟩⟩
    rfl

def labelIncidentBlockEquiv {n k : ℕ} (x : Fin n) (c : Fin k) :
    {b : TriangleBlock n k // (x, c) ∈ b.positiveLabels} ≃
      LabelMarkedTripleChoice x c :=
  (labelIncidentBlockChoiceSubtypeEquiv x c).trans
    (labelIncidentChoiceReassocEquiv x c)

theorem card_labelMarkedTripleChoice {n k : ℕ}
    (x : Fin n) (c : Fin k) :
    Fintype.card (LabelMarkedTripleChoice x c) =
      (n - 1).choose 2 * (5 * (k - 1)) := by
  rw [Fintype.card_sigma]
  calc
    (∑ S : {S : TripleSet n // x ∈ S.1},
        Fintype.card (LabelLocalChoice S.1 x c)) =
        ∑ _S : {S : TripleSet n // x ∈ S.1}, 5 * (k - 1) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact card_labelLocalChoice S.1 x c S.2
    _ = Fintype.card {S : TripleSet n // x ∈ S.1} * (5 * (k - 1)) := by
      simp
    _ = (n - 1).choose 2 * (5 * (k - 1)) := by
      rw [card_tripleContainingVertex]

theorem card_universal_label_incident_blocks {n k : ℕ}
    (x : Fin n) (c : Fin k) :
    ((allTriangleBlocks n k).filter fun b ↦
      (x, c) ∈ b.positiveLabels).card =
        5 * (n - 1).choose 2 * (k - 1) := by
  have hsub :
      Fintype.card {b : TriangleBlock n k // (x, c) ∈ b.positiveLabels} =
        ((allTriangleBlocks n k).filter fun b ↦
          (x, c) ∈ b.positiveLabels).card := by
    simpa [allTriangleBlocks] using
      (Fintype.card_subtype (fun b : TriangleBlock n k ↦
        (x, c) ∈ b.positiveLabels))
  rw [← hsub, Fintype.card_congr (labelIncidentBlockEquiv x c),
    card_labelMarkedTripleChoice]
  ac_rfl

abbrev ApexAwayPair {n : ℕ} (S : TripleSet n) (x y : Fin n) :=
  {a : Fin n // a ∈ S.1 ∧ a ≠ x ∧ a ≠ y}

@[simp] theorem card_apexAwayPair {n : ℕ} (S : TripleSet n)
    (x y : Fin n) (hx : x ∈ S.1) (hy : y ∈ S.1) (hxy : x ≠ y) :
    Fintype.card (ApexAwayPair S x y) = 1 := by
  let e : ApexAwayPair S x y ≃
      {a : Fin n // a ∈ (S.1.erase x).erase y} :=
    { toFun := fun a ↦ ⟨a.1, Finset.mem_erase.mpr
        ⟨a.2.2.2, Finset.mem_erase.mpr ⟨a.2.2.1, a.2.1⟩⟩⟩
      invFun := fun a ↦ ⟨a.1,
        ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp a.2).2).2,
          (Finset.mem_erase.mp (Finset.mem_erase.mp a.2).2).1,
          (Finset.mem_erase.mp a.2).1⟩⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hyerase : y ∈ S.1.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  rw [Fintype.card_congr e, Fintype.card_coe,
    Finset.card_erase_of_mem hyerase, Finset.card_erase_of_mem hx, S.2]

abbrev SameColorLocalChoice {n k : ℕ} (S : TripleSet n)
    (x y : Fin n) (c : Fin k) :=
  {q : ApexIn S × DistinctColorPair k //
    (c = q.2.1.1 ∨ (c = q.2.1.2 ∧ x ≠ q.1.1)) ∧
    (c = q.2.1.1 ∨ (c = q.2.1.2 ∧ y ≠ q.1.1))}

def sameColorLocalChoiceRoleEquiv {n k : ℕ} (S : TripleSet n)
    (x y : Fin n) (c : Fin k) :
    SameColorLocalChoice S x y c ≃
      (ApexIn S × OtherColor c) ⊕
        (ApexAwayPair S x y × OtherColor c) where
  toFun q := by
    by_cases hrep : c = q.1.2.1.1
    · exact Sum.inl ⟨q.1.1,
        ⟨q.1.2.1.2, by
          intro h
          exact q.1.2.2 (hrep.symm.trans h.symm)⟩⟩
    · have hsx := q.2.1.resolve_left hrep
      have hsy := q.2.2.resolve_left hrep
      exact Sum.inr
        ⟨⟨q.1.1.1, q.1.1.2, hsx.2.symm, hsy.2.symm⟩,
          ⟨q.1.2.1.1, by simpa [hsx.1] using q.1.2.2⟩⟩
  invFun q := by
    rcases q with q | q
    · exact ⟨⟨q.1, ⟨(c, q.2.1), q.2.2.symm⟩⟩,
        ⟨Or.inl rfl, Or.inl rfl⟩⟩
    · exact ⟨⟨⟨q.1.1, q.1.2.1⟩, ⟨(q.2.1, c), q.2.2⟩⟩,
        ⟨Or.inr ⟨rfl, q.1.2.2.1.symm⟩,
          Or.inr ⟨rfl, q.1.2.2.2.symm⟩⟩⟩
  left_inv q := by
    rcases q with ⟨⟨a, ⟨⟨r, s⟩, hrs⟩⟩, hq⟩
    apply Subtype.ext
    by_cases hrep : c = r
    · simp [hrep]
    · have hsx := hq.1.resolve_left hrep
      have hsy := hq.2.resolve_left hrep
      have hsr : s ≠ r := by
        intro hsr
        exact hrep (hsx.1.trans hsr)
      simp [hsx.1, hsy.1, hsr]
  right_inv q := by
    rcases q with q | q
    · rcases q with ⟨a, d⟩
      simp
    · rcases q with ⟨a, d⟩
      simp [d.2.symm]

theorem card_sameColorLocalChoice {n k : ℕ} (S : TripleSet n)
    (x y : Fin n) (c : Fin k) (hx : x ∈ S.1) (hy : y ∈ S.1)
    (hxy : x ≠ y) :
    Fintype.card (SameColorLocalChoice S x y c) = 4 * (k - 1) := by
  rw [Fintype.card_congr (sameColorLocalChoiceRoleEquiv S x y c),
    Fintype.card_sum, Fintype.card_prod, Fintype.card_prod,
    card_apexIn, card_apexAwayPair S x y hx hy hxy]
  simp only [card_otherColor]
  omega

def sameColorIncidentBlockChoiceSubtypeEquiv {n k : ℕ}
    (x y : Fin n) (c : Fin k) :
    {b : TriangleBlock n k //
      (x, c) ∈ b.positiveLabels ∧ (y, c) ∈ b.positiveLabels} ≃
      {q : TriangleSetChoice n k //
        x ∈ q.1.1.1 ∧ y ∈ q.1.1.1 ∧
        (c = q.2.1.1 ∨ (c = q.2.1.2 ∧ x ≠ q.1.2.1)) ∧
        (c = q.2.1.1 ∨ (c = q.2.1.2 ∧ y ≠ q.1.2.1))} :=
  Equiv.subtypeEquiv (triangleSetChoiceEquiv n k) (fun b ↦ by
    have hx := label_mem_positiveLabels_iff b x c
    have hy := label_mem_positiveLabels_iff b y c
    constructor
    · rintro ⟨hbx, hby⟩
      have px := hx.mp hbx
      have py := hy.mp hby
      change x ∈ ({b.apex, b.left, b.right} : Finset (Fin n)) ∧
          y ∈ ({b.apex, b.left, b.right} : Finset (Fin n)) ∧
          (c = b.repeated ∨ (c = b.singleton ∧ x ≠ b.apex)) ∧
          (c = b.repeated ∨ (c = b.singleton ∧ y ≠ b.apex))
      exact ⟨px.1, py.1, px.2, py.2⟩
    · intro h
      change x ∈ ({b.apex, b.left, b.right} : Finset (Fin n)) ∧
          y ∈ ({b.apex, b.left, b.right} : Finset (Fin n)) ∧
          (c = b.repeated ∨ (c = b.singleton ∧ x ≠ b.apex)) ∧
          (c = b.repeated ∨ (c = b.singleton ∧ y ≠ b.apex)) at h
      exact ⟨hx.mpr ⟨h.1, h.2.2.1⟩, hy.mpr ⟨h.2.1, h.2.2.2⟩⟩)

abbrev SameColorMarkedTripleChoice {n k : ℕ}
    (x y : Fin n) (c : Fin k) :=
  Σ S : {S : TripleSet n // x ∈ S.1 ∧ y ∈ S.1},
    SameColorLocalChoice S.1 x y c

def sameColorIncidentChoiceReassocEquiv {n k : ℕ}
    (x y : Fin n) (c : Fin k) :
    {q : TriangleSetChoice n k //
      x ∈ q.1.1.1 ∧ y ∈ q.1.1.1 ∧
      (c = q.2.1.1 ∨ (c = q.2.1.2 ∧ x ≠ q.1.2.1)) ∧
      (c = q.2.1.1 ∨ (c = q.2.1.2 ∧ y ≠ q.1.2.1))} ≃
      SameColorMarkedTripleChoice x y c where
  toFun q :=
    ⟨⟨q.1.1.1, q.2.1, q.2.2.1⟩,
      ⟨⟨q.1.1.2, q.1.2⟩, q.2.2.2.1, q.2.2.2.2⟩⟩
  invFun q :=
    ⟨⟨⟨q.1.1, q.2.1.1⟩, q.2.1.2⟩,
      ⟨q.1.2.1, q.1.2.2, q.2.2.1, q.2.2.2⟩⟩
  left_inv q := by rcases q with ⟨⟨⟨S, a⟩, colors⟩, h⟩; rfl
  right_inv q := by
    rcases q with ⟨⟨S, hx, hy⟩, ⟨⟨a, colors⟩, hlx, hly⟩⟩
    rfl

def sameColorIncidentBlockEquiv {n k : ℕ}
    (x y : Fin n) (c : Fin k) :
    {b : TriangleBlock n k //
      (x, c) ∈ b.positiveLabels ∧ (y, c) ∈ b.positiveLabels} ≃
      SameColorMarkedTripleChoice x y c :=
  (sameColorIncidentBlockChoiceSubtypeEquiv x y c).trans
    (sameColorIncidentChoiceReassocEquiv x y c)

theorem card_sameColorMarkedTripleChoice {n k : ℕ}
    (x y : Fin n) (c : Fin k) (hxy : x ≠ y) :
    Fintype.card (SameColorMarkedTripleChoice x y c) =
      (n - 2) * (4 * (k - 1)) := by
  rw [Fintype.card_sigma]
  calc
    (∑ S : {S : TripleSet n // x ∈ S.1 ∧ y ∈ S.1},
        Fintype.card (SameColorLocalChoice S.1 x y c)) =
        ∑ _S : {S : TripleSet n // x ∈ S.1 ∧ y ∈ S.1},
          4 * (k - 1) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact card_sameColorLocalChoice S.1 x y c S.2.1 S.2.2 hxy
    _ = Fintype.card {S : TripleSet n // x ∈ S.1 ∧ y ∈ S.1} *
        (4 * (k - 1)) := by simp
    _ = (n - 2) * (4 * (k - 1)) := by
      rw [card_tripleContainingPair x y hxy]

theorem card_universal_sameColor_incident_blocks {n k : ℕ}
    (x y : Fin n) (c : Fin k) (hxy : x ≠ y) :
    ((allTriangleBlocks n k).filter fun b ↦
      (x, c) ∈ b.positiveLabels ∧ (y, c) ∈ b.positiveLabels).card =
        4 * (n - 2) * (k - 1) := by
  have hsub :
      Fintype.card {b : TriangleBlock n k //
        (x, c) ∈ b.positiveLabels ∧ (y, c) ∈ b.positiveLabels} =
        ((allTriangleBlocks n k).filter fun b ↦
          (x, c) ∈ b.positiveLabels ∧ (y, c) ∈ b.positiveLabels).card := by
    simpa [allTriangleBlocks] using
      (Fintype.card_subtype (fun b : TriangleBlock n k ↦
        (x, c) ∈ b.positiveLabels ∧ (y, c) ∈ b.positiveLabels))
  rw [← hsub, Fintype.card_congr (sameColorIncidentBlockEquiv x y c),
    card_sameColorMarkedTripleChoice x y c hxy]
  ac_rfl

/-! ## Explicit universal influence bounds -/

theorem mem_dependencyLabels_iff_vertex_and_color {n k : ℕ}
    (b : TriangleBlock n k) (z : Fin n × Fin k) :
    z ∈ dependencyLabels b ↔
      z.1 ∈ ({b.apex, b.left, b.right} : Finset (Fin n)) ∧
        (z.2 = b.repeated ∨ z.2 = b.singleton) := by
  rw [mem_dependencyLabels]
  constructor
  · rintro (hpos | rfl)
    · have h := (label_mem_positiveLabels_iff b z.1 z.2).mp hpos
      exact ⟨h.1, h.2.elim Or.inl (fun hs ↦ Or.inr hs.1)⟩
    · exact ⟨by simp, Or.inr rfl⟩
  · rintro ⟨hv, hc | hc⟩
    · exact Or.inl <| (label_mem_positiveLabels_iff b z.1 z.2).mpr
        ⟨hv, Or.inl hc⟩
    · by_cases hza : z.1 = b.apex
      · exact Or.inr <| Prod.ext hza hc
      · exact Or.inl <| (label_mem_positiveLabels_iff b z.1 z.2).mpr
          ⟨hv, Or.inr ⟨hc, hza⟩⟩

abbrev ColorPairContaining (k : ℕ) (c : Fin k) :=
  {p : DistinctColorPair k // c = p.1.1 ∨ c = p.1.2}

def colorPairContainingEquiv (k : ℕ) (c : Fin k) :
    ColorPairContaining k c ≃ OtherColor c ⊕ OtherColor c where
  toFun p := by
    by_cases h : c = p.1.1.1
    · exact Sum.inl ⟨p.1.1.2, by
        intro heq
        exact p.1.2 (h.symm.trans heq.symm)⟩
    · exact Sum.inr ⟨p.1.1.1, Ne.symm h⟩
  invFun q := by
    rcases q with d | d
    · exact ⟨⟨(c, d.1), d.2.symm⟩, Or.inl rfl⟩
    · exact ⟨⟨(d.1, c), d.2⟩, Or.inr rfl⟩
  left_inv p := by
    rcases p with ⟨⟨⟨r, s⟩, hrs⟩, hp⟩
    apply Subtype.ext
    by_cases h : c = r
    · simp [h]
    · have hs : c = s := hp.resolve_left h
      have hsr : s ≠ r := by
        intro hsr
        exact h (hs.trans hsr)
      simp [h, hs, hsr]
  right_inv q := by
    rcases q with d | d
    · simp
    · simp [Ne.symm d.2]

@[simp] theorem card_colorPairContaining (k : ℕ) (c : Fin k) :
    Fintype.card (ColorPairContaining k c) = 2 * (k - 1) := by
  rw [Fintype.card_congr (colorPairContainingEquiv k c), Fintype.card_sum]
  simp only [card_otherColor]
  omega

theorem card_labelLocalChoice_with_other_color_le {n k : ℕ}
    (S : TripleSet n) (x : Fin n) (c d : Fin k) (hx : x ∈ S.1)
    (hdc : d ≠ c) :
    Fintype.card {q : LabelLocalChoice S x c //
      d = q.1.2.1.1 ∨ d = q.1.2.1.2} ≤ 5 := by
  let T := ApexIn S ⊕ ApexAway S x
  let fixedOther : OtherColor c := ⟨d, hdc⟩
  let f : {q : LabelLocalChoice S x c //
      d = q.1.2.1.1 ∨ d = q.1.2.1.2} → T := fun q ↦
    match labelLocalChoiceRoleEquiv S x c q.1 with
    | Sum.inl p => Sum.inl p.1
    | Sum.inr p => Sum.inr p.1
  let g : T → LabelLocalChoice S x c := fun t ↦
    (labelLocalChoiceRoleEquiv S x c).symm <|
      match t with
      | Sum.inl a => Sum.inl (a, fixedOther)
      | Sum.inr a => Sum.inr (a, fixedOther)
  have hleft : ∀ q, g (f q) = q.1 := by
    rintro ⟨⟨⟨a, ⟨⟨r, s⟩, hrs⟩⟩, hroot⟩, hdep⟩
    by_cases hcr : c = r
    · have hds : d = s := hdep.resolve_left (fun hdr ↦ hdc (hdr.trans hcr.symm))
      subst r
      subst s
      simp [f, g, fixedOther, labelLocalChoiceRoleEquiv]
    · have hcs : c = s := (hroot.resolve_left hcr).1
      have hdr : d = r := hdep.resolve_right (fun hds ↦ hdc (hds.trans hcs.symm))
      subst r
      subst s
      simp [f, g, fixedOther, labelLocalChoiceRoleEquiv, hdc, hcr]
  have hf : Function.Injective f := by
    intro q r hqr
    apply Subtype.ext
    exact (hleft q).symm.trans ((congrArg g hqr).trans (hleft r))
  calc
    Fintype.card {q : LabelLocalChoice S x c //
        d = q.1.2.1.1 ∨ d = q.1.2.1.2} ≤ Fintype.card T :=
      Fintype.card_le_of_injective f hf
    _ = Fintype.card (ApexIn S) + Fintype.card (ApexAway S x) := by
      simp [T, Fintype.card_sum]
    _ ≤ 3 + 2 := by rw [card_apexIn, card_apexAway S x hx]
    _ = 5 := by omega

theorem card_graph_dependency_blocks_le {n k : ℕ}
    (x y : Fin n) (hxy : x ≠ y) (z : Fin n × Fin k) :
    (((allTriangleBlocks n k).filter fun b ↦
      Sum.inl s(x, y) ∈ b.auxSupport).filter fun b ↦
        z ∈ dependencyLabels b).card ≤ 6 * n * k := by
  let A := {b : TriangleBlock n k //
    Sum.inl s(x, y) ∈ b.auxSupport ∧ z ∈ dependencyLabels b}
  let B := MarkedTripleContainingPair x y × ColorPairContaining k z.2
  let f : A → B := fun b ↦ by
    let q := incidentBlockEquiv (k := k) x y hxy ⟨b.1, b.2.1⟩
    exact ⟨q.1, ⟨q.2, by
      have hz := (mem_dependencyLabels_iff_vertex_and_color b.1 z).mp b.2.2
      exact hz.2⟩⟩
  have hf : Function.Injective f := by
    intro b c hbc
    have hq : incidentBlockEquiv (k := k) x y hxy ⟨b.1, b.2.1⟩ =
        incidentBlockEquiv (k := k) x y hxy ⟨c.1, c.2.1⟩ := by
      apply Prod.ext
      · exact congrArg (fun q ↦ q.1) hbc
      · exact congrArg (fun q ↦ q.2.1) hbc
    have hinc := (incidentBlockEquiv (k := k) x y hxy).injective hq
    have hval : b.1 = c.1 := congrArg
      (fun q : {b : TriangleBlock n k //
        Sum.inl s(x, y) ∈ b.auxSupport} ↦ q.1) hinc
    exact @Subtype.ext _
      (fun b : TriangleBlock n k ↦
        Sum.inl s(x, y) ∈ b.auxSupport ∧ z ∈ dependencyLabels b)
      b c hval
  have hA : Fintype.card A =
      (((allTriangleBlocks n k).filter fun b ↦
        Sum.inl s(x, y) ∈ b.auxSupport).filter fun b ↦
          z ∈ dependencyLabels b).card := by
    simpa [A, allTriangleBlocks, Finset.filter_filter, and_assoc] using
      (Fintype.card_subtype (fun b : TriangleBlock n k ↦
        Sum.inl s(x, y) ∈ b.auxSupport ∧ z ∈ dependencyLabels b))
  rw [← hA]
  calc
    Fintype.card A ≤ Fintype.card B := Fintype.card_le_of_injective f hf
    _ = (3 * (n - 2)) * (2 * (k - 1)) := by
      dsimp only [B]
      rw [Fintype.card_prod, card_markedTripleContainingPair x y hxy,
        card_colorPairContaining]
      ring
    _ ≤ 6 * n * k := by
      nlinarith [Nat.sub_le n 2, Nat.sub_le k 1,
        Nat.zero_le (n - 2), Nat.zero_le (k - 1)]

theorem card_label_dependency_blocks_le {n k : ℕ}
    (x : Fin n) (c : Fin k) (z : Fin n × Fin k)
    (hne : z ≠ (x, c)) (hk : k ≤ n) :
    (((allTriangleBlocks n k).filter fun b ↦
      (x, c) ∈ b.positiveLabels).filter fun b ↦
        z ∈ dependencyLabels b).card ≤ 5 * n ^ 2 := by
  let A := {b : TriangleBlock n k //
    (x, c) ∈ b.positiveLabels ∧ z ∈ dependencyLabels b}
  have hA : Fintype.card A =
      (((allTriangleBlocks n k).filter fun b ↦
        (x, c) ∈ b.positiveLabels).filter fun b ↦
          z ∈ dependencyLabels b).card := by
    simpa [A, allTriangleBlocks, Finset.filter_filter, and_assoc] using
      (Fintype.card_subtype (fun b : TriangleBlock n k ↦
        (x, c) ∈ b.positiveLabels ∧ z ∈ dependencyLabels b))
  rw [← hA]
  by_cases hzc : z.2 = c
  · have hzx : z.1 ≠ x := by
      intro h
      apply hne
      exact Prod.ext h hzc
    let B := Σ S : {S : TripleSet n // x ∈ S.1 ∧ z.1 ∈ S.1},
      LabelLocalChoice S.1 x c
    let f : A → B := fun b ↦ by
      let q := labelIncidentBlockEquiv x c ⟨b.1, b.2.1⟩
      have hz := (mem_dependencyLabels_iff_vertex_and_color b.1 z).mp b.2.2
      exact ⟨⟨q.1.1, q.1.2, hz.1⟩, q.2⟩
    let forget : B → LabelMarkedTripleChoice x c := fun q ↦
      ⟨⟨q.1.1, q.1.2.1⟩, q.2⟩
    have hforget (b : A) : forget (f b) =
        labelIncidentBlockEquiv x c ⟨b.1, b.2.1⟩ := by
      rfl
    have hf : Function.Injective f := by
      intro b d hbd
      have hq : labelIncidentBlockEquiv x c ⟨b.1, b.2.1⟩ =
          labelIncidentBlockEquiv x c ⟨d.1, d.2.1⟩ := by
        rw [← hforget b, ← hforget d, hbd]
      have hinc := (labelIncidentBlockEquiv x c).injective hq
      have hval : b.1 = d.1 := congrArg
        (fun q : {b : TriangleBlock n k // (x, c) ∈ b.positiveLabels} ↦ q.1) hinc
      exact @Subtype.ext _
        (fun b : TriangleBlock n k ↦
          (x, c) ∈ b.positiveLabels ∧ z ∈ dependencyLabels b)
        b d hval
    calc
      Fintype.card A ≤ Fintype.card B := Fintype.card_le_of_injective f hf
      _ = (n - 2) * (5 * (k - 1)) := by
        dsimp only [B]
        rw [Fintype.card_sigma]
        calc
          (∑ S : {S : TripleSet n // x ∈ S.1 ∧ z.1 ∈ S.1},
              Fintype.card (LabelLocalChoice S.1 x c)) =
              ∑ _S : {S : TripleSet n // x ∈ S.1 ∧ z.1 ∈ S.1},
                5 * (k - 1) := by
            apply Finset.sum_congr rfl
            intro S hS
            exact card_labelLocalChoice S.1 x c S.2.1
          _ = Fintype.card {S : TripleSet n // x ∈ S.1 ∧ z.1 ∈ S.1} *
              (5 * (k - 1)) := by simp
          _ = (n - 2) * (5 * (k - 1)) := by
            rw [card_tripleContainingPair x z.1 (Ne.symm hzx)]
      _ ≤ 5 * n ^ 2 := by
        nlinarith [Nat.sub_le n 2, Nat.sub_le k 1,
          Nat.zero_le (n - 2), Nat.zero_le (k - 1)]
  · let B := Σ S : {S : TripleSet n // x ∈ S.1},
      {q : LabelLocalChoice S.1 x c //
        z.2 = q.1.2.1.1 ∨ z.2 = q.1.2.1.2}
    let f : A → B := fun b ↦ by
      let q := labelIncidentBlockEquiv x c ⟨b.1, b.2.1⟩
      have hz := (mem_dependencyLabels_iff_vertex_and_color b.1 z).mp b.2.2
      exact ⟨q.1, ⟨q.2, hz.2⟩⟩
    let forget : B → LabelMarkedTripleChoice x c := fun q ↦
      ⟨q.1, q.2.1⟩
    have hforget (b : A) : forget (f b) =
        labelIncidentBlockEquiv x c ⟨b.1, b.2.1⟩ := by
      rfl
    have hf : Function.Injective f := by
      intro b d hbd
      have hq : labelIncidentBlockEquiv x c ⟨b.1, b.2.1⟩ =
          labelIncidentBlockEquiv x c ⟨d.1, d.2.1⟩ := by
        rw [← hforget b, ← hforget d, hbd]
      have hinc := (labelIncidentBlockEquiv x c).injective hq
      have hval : b.1 = d.1 := congrArg
        (fun q : {b : TriangleBlock n k // (x, c) ∈ b.positiveLabels} ↦ q.1) hinc
      exact @Subtype.ext _
        (fun b : TriangleBlock n k ↦
          (x, c) ∈ b.positiveLabels ∧ z ∈ dependencyLabels b)
        b d hval
    have hchoose : (n - 1).choose 2 ≤ n ^ 2 := by
      calc
        (n - 1).choose 2 ≤ (n - 1) ^ 2 := Nat.choose_le_pow (n - 1) 2
        _ ≤ n ^ 2 := by gcongr <;> omega
    calc
      Fintype.card A ≤ Fintype.card B := Fintype.card_le_of_injective f hf
      _ ≤ (n - 1).choose 2 * 5 := by
        dsimp only [B]
        rw [Fintype.card_sigma]
        calc
          (∑ S : {S : TripleSet n // x ∈ S.1},
              Fintype.card {q : LabelLocalChoice S.1 x c //
                z.2 = q.1.2.1.1 ∨ z.2 = q.1.2.1.2}) ≤
              ∑ _S : {S : TripleSet n // x ∈ S.1}, 5 := by
            apply Finset.sum_le_sum
            intro S hS
            exact card_labelLocalChoice_with_other_color_le
              S.1 x c z.2 S.2 hzc
          _ = Fintype.card {S : TripleSet n // x ∈ S.1} * 5 := by simp
          _ = (n - 1).choose 2 * 5 := by rw [card_tripleContainingVertex]
      _ ≤ 5 * n ^ 2 := by nlinarith

theorem card_blocksThrough_graph_le {n k : ℕ}
    (e : Sym2 (Fin n)) (he : ¬e.IsDiag) :
    (blocksThrough (Sum.inl e : AuxVertex n k)).card ≤ 3 * n * k ^ 2 := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : x ≠ y := by
        simpa [Sym2.mk_isDiag_iff] using he
      rw [show (blocksThrough (Sum.inl s(x, y) : AuxVertex n k)).card =
          3 * (n - 2) * k * (k - 1) by
        simpa [blocksThrough] using
          (card_universal_graph_incident_blocks (k := k) x y hxy)]
      calc
        3 * (n - 2) * k * (k - 1) ≤ 3 * n * k * k := by
          gcongr <;> omega
        _ = 3 * n * k ^ 2 := by ring

theorem card_blocksThrough_label_le {n k : ℕ}
    (root : Fin n × Fin k) :
    (blocksThrough (Sum.inr root : AuxVertex n k)).card ≤
      5 * n ^ 2 * k := by
  rcases root with ⟨x, c⟩
  rw [show (blocksThrough (Sum.inr (x, c) : AuxVertex n k)).card =
      5 * (n - 1).choose 2 * (k - 1) by
    simpa [blocksThrough, TriangleBlock.auxSupport] using
      (card_universal_label_incident_blocks (n := n) x c)]
  have hchoose : (n - 1).choose 2 ≤ n ^ 2 := by
    calc
      (n - 1).choose 2 ≤ (n - 1) ^ 2 := Nat.choose_le_pow (n - 1) 2
      _ ≤ n ^ 2 := by gcongr <;> omega
  calc
    5 * (n - 1).choose 2 * (k - 1) ≤ 5 * n ^ 2 * k := by
      gcongr <;> omega

theorem degreeInfluenceNat_graph_le {n k : ℕ}
    (e : Sym2 (Fin n)) (he : ¬e.IsDiag) :
    ∀ i, degreeInfluenceNat (Sum.inl e : AuxVertex n k) i ≤ 6 * n * k := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : x ≠ y := by
        simpa [Sym2.mk_isDiag_iff] using he
      intro i
      simpa only [degreeInfluenceNat, he, ↓reduceIte, blocksThrough] using
        (card_graph_dependency_blocks_le x y hxy (labelEquiv n k i))

theorem degreeInfluence_sq_sum_graph {n k : ℕ}
    (e : Sym2 (Fin n)) (he : ¬e.IsDiag) (hk : k ≤ n) :
    ∑ i, degreeInfluence (Sum.inl e : AuxVertex n k) i ^ 2 ≤
      (108 : ℝ) * n ^ 5 := by
  exact degreeInfluence_sq_sum_graph_of_counts e he hk
    (degreeInfluenceNat_graph_le e he) (card_blocksThrough_graph_le e he)

theorem degreeInfluenceNat_label_le {n k : ℕ}
    (root : Fin n × Fin k) (hk : k ≤ n) :
    ∀ i, degreeInfluenceNat (Sum.inr root : AuxVertex n k) i ≤ 5 * n ^ 2 := by
  rcases root with ⟨x, c⟩
  intro i
  by_cases hi : labelEquiv n k i = (x, c)
  · simp [degreeInfluenceNat, hi]
  · simpa [degreeInfluenceNat, hi, blocksThrough,
      TriangleBlock.auxSupport] using
      (card_label_dependency_blocks_le x c (labelEquiv n k i) hi hk)

theorem degreeInfluence_sq_sum_label_of_counts125 {n k : ℕ}
    (root : Fin n × Fin k) (hk : k ≤ n)
    (hmax : ∀ i,
      degreeInfluenceNat (Sum.inr root : AuxVertex n k) i ≤ 5 * n ^ 2)
    (hcard : (blocksThrough (Sum.inr root : AuxVertex n k)).card ≤
      5 * n ^ 2 * k) :
    ∑ i, degreeInfluence (Sum.inr root : AuxVertex n k) i ^ 2 ≤
      (125 : ℝ) * n ^ 5 := by
  have hsum : ∑ i, degreeInfluenceNat (Sum.inr root : AuxVertex n k) i ≤
      25 * n ^ 2 * k := by
    rw [sum_degreeInfluenceNat_label root]
    calc
      5 * (blocksThrough (Sum.inr root : AuxVertex n k)).card ≤
          5 * (5 * n ^ 2 * k) := Nat.mul_le_mul_left 5 hcard
      _ = 25 * n ^ 2 * k := by ring
  have h := sum_natCast_sq_le_of_max_sum
    (degreeInfluenceNat (n := n) (k := k) (Sum.inr root)) hmax hsum
  simp only [degreeInfluence] at h ⊢
  calc
    ∑ i, (degreeInfluenceNat (Sum.inr root : AuxVertex n k) i : ℝ) ^ 2 ≤
        ((5 * n ^ 2 : ℕ) : ℝ) * ((25 * n ^ 2 * k : ℕ) : ℝ) := h
    _ = (125 : ℝ) * n ^ 4 * k := by push_cast; ring
    _ ≤ (125 : ℝ) * n ^ 4 * n := by
      have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
      gcongr
    _ = (125 : ℝ) * n ^ 5 := by ring

theorem degreeInfluence_sq_sum_label {n k : ℕ}
    (root : Fin n × Fin k) (hk : k ≤ n) :
    ∑ i, degreeInfluence (Sum.inr root : AuxVertex n k) i ^ 2 ≤
      (125 : ℝ) * n ^ 5 := by
  exact degreeInfluence_sq_sum_label_of_counts125 root hk
    (degreeInfluenceNat_label_le root hk) (card_blocksThrough_label_le root)

theorem degreeInfluence_sq_sum {n k : ℕ} (hk : k ≤ n)
    (v : AuxVertex n k) :
    ∑ i, degreeInfluence v i ^ 2 ≤ (125 : ℝ) * n ^ 5 := by
  rcases v with e | root
  · by_cases he : e.IsDiag
    · simp [degreeInfluence, degreeInfluenceNat, he]
    · calc
        ∑ i, degreeInfluence (Sum.inl e : AuxVertex n k) i ^ 2 ≤
            (108 : ℝ) * n ^ 5 := degreeInfluence_sq_sum_graph e he hk
        _ ≤ (125 : ℝ) * n ^ 5 := by
          have hn : (0 : ℝ) ≤ n ^ 5 := by positivity
          nlinarith
  · exact degreeInfluence_sq_sum_label root hk

theorem card_sameColorLocalChoice_with_other_color_le {n k : ℕ}
    (S : TripleSet n) (x y : Fin n) (c d : Fin k)
    (hx : x ∈ S.1) (hy : y ∈ S.1) (hxy : x ≠ y) (hdc : d ≠ c) :
    Fintype.card {q : SameColorLocalChoice S x y c //
      d = q.1.2.1.1 ∨ d = q.1.2.1.2} ≤ 4 := by
  let T := ApexIn S ⊕ ApexAwayPair S x y
  let fixedOther : OtherColor c := ⟨d, hdc⟩
  let f : {q : SameColorLocalChoice S x y c //
      d = q.1.2.1.1 ∨ d = q.1.2.1.2} → T := fun q ↦
    match sameColorLocalChoiceRoleEquiv S x y c q.1 with
    | Sum.inl p => Sum.inl p.1
    | Sum.inr p => Sum.inr p.1
  let g : T → SameColorLocalChoice S x y c := fun t ↦
    (sameColorLocalChoiceRoleEquiv S x y c).symm <|
      match t with
      | Sum.inl a => Sum.inl (a, fixedOther)
      | Sum.inr a => Sum.inr (a, fixedOther)
  have hleft : ∀ q, g (f q) = q.1 := by
    rintro ⟨⟨⟨a, ⟨⟨r, s⟩, hrs⟩⟩, hroot⟩, hdep⟩
    by_cases hcr : c = r
    · have hds : d = s := hdep.resolve_left (fun hdr ↦ hdc (hdr.trans hcr.symm))
      subst r
      subst s
      simp [f, g, fixedOther, sameColorLocalChoiceRoleEquiv]
    · have hcs : c = s := (hroot.1.resolve_left hcr).1
      have hdr : d = r := hdep.resolve_right (fun hds ↦ hdc (hds.trans hcs.symm))
      subst r
      subst s
      simp [f, g, fixedOther, sameColorLocalChoiceRoleEquiv, hdc, hcr]
  have hf : Function.Injective f := by
    intro q r hqr
    apply Subtype.ext
    exact (hleft q).symm.trans ((congrArg g hqr).trans (hleft r))
  calc
    Fintype.card {q : SameColorLocalChoice S x y c //
        d = q.1.2.1.1 ∨ d = q.1.2.1.2} ≤ Fintype.card T :=
      Fintype.card_le_of_injective f hf
    _ = Fintype.card (ApexIn S) + Fintype.card (ApexAwayPair S x y) := by
      simp [T, Fintype.card_sum]
    _ = 3 + 1 := by rw [card_apexIn, card_apexAwayPair S x y hx hy hxy]
    _ = 4 := by omega

theorem tripleContainingThree_card_le_one {n : ℕ}
    (x y z : Fin n) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    Fintype.card {S : TripleSet n // x ∈ S.1 ∧ y ∈ S.1 ∧ z ∈ S.1} ≤ 1 := by
  let f : {S : TripleSet n // x ∈ S.1 ∧ y ∈ S.1 ∧ z ∈ S.1} → Fin 1 :=
    fun _ ↦ 0
  have hset (S : {S : TripleSet n //
      x ∈ S.1 ∧ y ∈ S.1 ∧ z ∈ S.1}) :
      ({x, y, z} : Finset (Fin n)) = S.1.1 := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact S.2.1
      · exact S.2.2.1
      · exact S.2.2.2
    · rw [S.1.2]
      simp [hxy, hxz, hyz]
  have hf : Function.Injective f := by
    intro S T h
    apply Subtype.ext
    apply Subtype.ext
    exact (hset S).symm.trans (hset T)
  calc
    Fintype.card {S : TripleSet n //
        x ∈ S.1 ∧ y ∈ S.1 ∧ z ∈ S.1} ≤ Fintype.card (Fin 1) :=
      Fintype.card_le_of_injective f hf
    _ = 1 := by simp

theorem card_sameColor_dependency_blocks_le {n k : ℕ}
    (x y : Fin n) (c : Fin k) (z : Fin n × Fin k)
    (hxy : x ≠ y) (hzx : z ≠ (x, c)) (hzy : z ≠ (y, c))
    (hk : k ≤ n) :
    (((allTriangleBlocks n k).filter fun b ↦
      (x, c) ∈ b.positiveLabels ∧ (y, c) ∈ b.positiveLabels).filter
        fun b ↦ z ∈ dependencyLabels b).card ≤ 6 * n := by
  let A := {b : TriangleBlock n k //
    ((x, c) ∈ b.positiveLabels ∧ (y, c) ∈ b.positiveLabels) ∧
      z ∈ dependencyLabels b}
  have hA : Fintype.card A =
      (((allTriangleBlocks n k).filter fun b ↦
        (x, c) ∈ b.positiveLabels ∧ (y, c) ∈ b.positiveLabels).filter
          fun b ↦ z ∈ dependencyLabels b).card := by
    simpa [A, allTriangleBlocks, Finset.filter_filter, and_assoc] using
      (Fintype.card_subtype (fun b : TriangleBlock n k ↦
        (((x, c) ∈ b.positiveLabels ∧ (y, c) ∈ b.positiveLabels) ∧
          z ∈ dependencyLabels b)))
  rw [← hA]
  by_cases hzc : z.2 = c
  · have hzxn : x ≠ z.1 := by
      intro h
      apply hzx
      exact Prod.ext h.symm hzc
    have hzyn : y ≠ z.1 := by
      intro h
      apply hzy
      exact Prod.ext h.symm hzc
    let B := Σ S : {S : TripleSet n //
      x ∈ S.1 ∧ y ∈ S.1 ∧ z.1 ∈ S.1},
        SameColorLocalChoice S.1 x y c
    let f : A → B := fun b ↦ by
      let q := sameColorIncidentBlockEquiv x y c ⟨b.1, b.2.1⟩
      have hz := (mem_dependencyLabels_iff_vertex_and_color b.1 z).mp b.2.2
      exact ⟨⟨q.1.1, q.1.2.1, q.1.2.2, hz.1⟩, q.2⟩
    let forget : B → SameColorMarkedTripleChoice x y c := fun q ↦
      ⟨⟨q.1.1, q.1.2.1, q.1.2.2.1⟩, q.2⟩
    have hforget (b : A) : forget (f b) =
        sameColorIncidentBlockEquiv x y c ⟨b.1, b.2.1⟩ := by
      rfl
    have hf : Function.Injective f := by
      intro b d hbd
      have hq : sameColorIncidentBlockEquiv x y c ⟨b.1, b.2.1⟩ =
          sameColorIncidentBlockEquiv x y c ⟨d.1, d.2.1⟩ := by
        rw [← hforget b, ← hforget d, hbd]
      have hinc := (sameColorIncidentBlockEquiv x y c).injective hq
      have hval : b.1 = d.1 := congrArg
        (fun q : {b : TriangleBlock n k //
          (x, c) ∈ b.positiveLabels ∧ (y, c) ∈ b.positiveLabels} ↦ q.1) hinc
      exact @Subtype.ext _
        (fun b : TriangleBlock n k ↦
          ((x, c) ∈ b.positiveLabels ∧ (y, c) ∈ b.positiveLabels) ∧
            z ∈ dependencyLabels b)
        b d hval
    calc
      Fintype.card A ≤ Fintype.card B := Fintype.card_le_of_injective f hf
      _ = Fintype.card {S : TripleSet n //
          x ∈ S.1 ∧ y ∈ S.1 ∧ z.1 ∈ S.1} * (4 * (k - 1)) := by
        dsimp only [B]
        rw [Fintype.card_sigma]
        apply Finset.sum_const_nat
        intro S hS
        exact card_sameColorLocalChoice S.1 x y c
          S.2.1 S.2.2.1 hxy
      _ ≤ 1 * (4 * (k - 1)) := by
        gcongr
        exact tripleContainingThree_card_le_one x y z.1 hxy hzxn hzyn
      _ ≤ 6 * n := by nlinarith [Nat.sub_le k 1]
  · let B := Σ S : {S : TripleSet n // x ∈ S.1 ∧ y ∈ S.1},
      {q : SameColorLocalChoice S.1 x y c //
        z.2 = q.1.2.1.1 ∨ z.2 = q.1.2.1.2}
    let f : A → B := fun b ↦ by
      let q := sameColorIncidentBlockEquiv x y c ⟨b.1, b.2.1⟩
      have hz := (mem_dependencyLabels_iff_vertex_and_color b.1 z).mp b.2.2
      exact ⟨q.1, ⟨q.2, hz.2⟩⟩
    let forget : B → SameColorMarkedTripleChoice x y c := fun q ↦
      ⟨q.1, q.2.1⟩
    have hforget (b : A) : forget (f b) =
        sameColorIncidentBlockEquiv x y c ⟨b.1, b.2.1⟩ := by
      rfl
    have hf : Function.Injective f := by
      intro b d hbd
      have hq : sameColorIncidentBlockEquiv x y c ⟨b.1, b.2.1⟩ =
          sameColorIncidentBlockEquiv x y c ⟨d.1, d.2.1⟩ := by
        rw [← hforget b, ← hforget d, hbd]
      have hinc := (sameColorIncidentBlockEquiv x y c).injective hq
      have hval : b.1 = d.1 := congrArg
        (fun q : {b : TriangleBlock n k //
          (x, c) ∈ b.positiveLabels ∧ (y, c) ∈ b.positiveLabels} ↦ q.1) hinc
      exact @Subtype.ext _
        (fun b : TriangleBlock n k ↦
          ((x, c) ∈ b.positiveLabels ∧ (y, c) ∈ b.positiveLabels) ∧
            z ∈ dependencyLabels b)
        b d hval
    calc
      Fintype.card A ≤ Fintype.card B := Fintype.card_le_of_injective f hf
      _ ≤ (n - 2) * 4 := by
        dsimp only [B]
        rw [Fintype.card_sigma]
        calc
          (∑ S : {S : TripleSet n // x ∈ S.1 ∧ y ∈ S.1},
              Fintype.card {q : SameColorLocalChoice S.1 x y c //
                z.2 = q.1.2.1.1 ∨ z.2 = q.1.2.1.2}) ≤
              ∑ _S : {S : TripleSet n // x ∈ S.1 ∧ y ∈ S.1}, 4 := by
            apply Finset.sum_le_sum
            intro S hS
            exact card_sameColorLocalChoice_with_other_color_le
              S.1 x y c z.2 S.2.1 S.2.2 hxy hzc
          _ = Fintype.card {S : TripleSet n // x ∈ S.1 ∧ y ∈ S.1} * 4 := by
            simp
          _ = (n - 2) * 4 := by rw [card_tripleContainingPair x y hxy]
      _ ≤ 6 * n := by nlinarith [Nat.sub_le n 2]

theorem card_blocksThroughPair_le {n k : ℕ}
    (a : SameColorIndex n k) (haa : a.left ≠ a.right) :
    (blocksThroughPair a).card ≤ 6 * n * k := by
  rw [show (blocksThroughPair a).card =
      4 * (n - 2) * (k - 1) by
    simpa [blocksThroughPair, TriangleBlock.auxSupport] using
      (card_universal_sameColor_incident_blocks
        a.left a.right a.color haa)]
  calc
    4 * (n - 2) * (k - 1) ≤ 6 * n * k := by
      nlinarith [Nat.sub_le n 2, Nat.sub_le k 1,
        Nat.zero_le (n - 2), Nat.zero_le (k - 1)]

def blocksThroughAuxPair {n k : ℕ} (v w : AuxVertex n k) :
    Finset (TriangleBlock n k) :=
  (allTriangleBlocks n k).filter fun b ↦ v ∈ b.auxSupport ∧ w ∈ b.auxSupport

theorem codegree_pair_eq_blocks {n k : ℕ} (R : RetainedLabels n k)
    (v w : AuxVertex n k) :
    codegree (auxiliaryHypergraph (allTriangleBlocks n k) R) {v, w} =
      ((blocksThroughAuxPair v w).filter (Eligible R)).card := by
  classical
  unfold codegree auxiliaryHypergraph blocksThroughAuxPair
  rw [show
      (((allTriangleBlocks n k).filter (Eligible R)).image
          TriangleBlock.auxSupport).filter
          (fun e ↦ {v, w} ⊆ e) =
        (((allTriangleBlocks n k).filter fun b ↦ Eligible R b ∧
          v ∈ b.auxSupport ∧ w ∈ b.auxSupport).image
            TriangleBlock.auxSupport) by
    ext e
    simp only [mem_filter, mem_image, insert_subset_iff, singleton_subset_iff]
    aesop]
  rw [card_image_of_injective _ auxSupport_injective]
  congr 1
  ext b
  simp only [mem_filter]
  aesop

def auxPairBlockVertices {n k : ℕ} (b : TriangleBlock n k) : Finset (Fin n) :=
  {b.apex, b.left, b.right}

@[simp] theorem auxPairBlockVertices_card {n k : ℕ} (b : TriangleBlock n k) :
    (auxPairBlockVertices b).card = 3 := by
  simp [auxPairBlockVertices, b.apex_ne_left, b.apex_ne_right, b.left_ne_right]

theorem triangleBlock_ext_of_vertices_apex_colors {n k : ℕ}
    {b c : TriangleBlock n k} (hV : auxPairBlockVertices b = auxPairBlockVertices c)
    (ha : b.apex = c.apex) (hr : b.repeated = c.repeated)
    (hs : b.singleton = c.singleton) : b = c := by
  apply (triangleSetChoiceEquiv n k).injective
  ext <;> simp_all [triangleSetChoiceEquiv, auxPairBlockVertices]

def blockTriple {n k : ℕ} (b : TriangleBlock n k) : TripleSet n :=
  ⟨auxPairBlockVertices b, auxPairBlockVertices_card b⟩

@[simp] theorem blockTriple_val {n k : ℕ} (b : TriangleBlock n k) :
    (blockTriple b).1 = auxPairBlockVertices b := rfl

@[simp] theorem apex_mem_blockTriple {n k : ℕ} (b : TriangleBlock n k) :
    b.apex ∈ (blockTriple b).1 := by simp [blockTriple, auxPairBlockVertices]

theorem label_mem_of_inr_mem_auxSupport {n k : ℕ} (b : TriangleBlock n k)
    (z : Fin n × Fin k) (hz : (Sum.inr z : AuxVertex n k) ∈ b.auxSupport) :
    z ∈ b.positiveLabels := by
  simpa [TriangleBlock.auxSupport] using hz

def graphLabelPairCode {n k : ℕ} (x y z : Fin n) (c : Fin k)
    (hxy : x ≠ y) :
    {b : TriangleBlock n k //
      b ∈ blocksThroughAuxPair
        (Sum.inl s(x, y) : AuxVertex n k) (Sum.inr (z, c))} →
      MarkedTripleContainingPair x y × ColorPairContaining k c :=
  fun b ↦ by
    have hb := (Finset.mem_filter.mp b.2).2
    have hgraph := (graph_mem_auxSupport_iff_vertices b.1 x y hxy).mp hb.1
    have hlabel := label_mem_of_inr_mem_auxSupport b.1 (z, c) hb.2
    have hcolor := (label_mem_positiveLabels_iff b.1 z c).mp hlabel |>.2
    exact
      ⟨⟨⟨blockTriple b.1, hgraph⟩,
          ⟨b.1.apex, apex_mem_blockTriple b.1⟩⟩,
        ⟨⟨(b.1.repeated, b.1.singleton), b.1.colors_ne⟩,
          hcolor.elim Or.inl (fun h ↦ Or.inr h.1)⟩⟩

theorem graphLabelPairCode_injective {n k : ℕ} (x y z : Fin n) (c : Fin k)
    (hxy : x ≠ y) : Function.Injective (graphLabelPairCode x y z c hxy) := by
  intro b d h
  apply Subtype.ext
  apply triangleBlock_ext_of_vertices_apex_colors
  · exact congrArg (fun q ↦ q.1.1.1.1) h
  · exact congrArg (fun q ↦ q.1.2.1) h
  · exact congrArg (fun q ↦ q.2.1.1.1) h
  · exact congrArg (fun q ↦ q.2.1.1.2) h

theorem card_blocksThroughAuxPair_graph_label_le {n k : ℕ}
    (x y z : Fin n) (c : Fin k) (hxy : x ≠ y) :
    (blocksThroughAuxPair
      (Sum.inl s(x, y) : AuxVertex n k) (Sum.inr (z, c))).card ≤
        6 * n * k := by
  rw [← Fintype.card_coe]
  apply (Fintype.card_le_of_injective _
    (graphLabelPairCode_injective x y z c hxy)).trans
  rw [Fintype.card_prod, card_markedTripleContainingPair x y hxy,
    card_colorPairContaining]
  calc
    (n - 2) * 3 * (2 * (k - 1)) ≤ n * 3 * (2 * k) :=
      Nat.mul_le_mul
        (Nat.mul_le_mul_right 3 (Nat.sub_le n 2))
        (Nat.mul_le_mul_left 2 (Nat.sub_le k 1))
    _ = 6 * n * k := by ring

abbrev TwoColorPair {k : ℕ} (c d : Fin k) :=
  {p : Fin k × Fin k // p.1 ≠ p.2 ∧
    (c = p.1 ∨ c = p.2) ∧ (d = p.1 ∨ d = p.2)}

def twoColorPairCode {k : ℕ} (c d : Fin k) (p : TwoColorPair c d) : Fin 2 :=
  if p.val.1 = c then 0 else 1

theorem twoColorPairCode_injective {k : ℕ} (c d : Fin k) (hcd : c ≠ d) :
    Function.Injective (twoColorPairCode c d) := by
  intro p q hpq
  apply Subtype.ext
  rcases p with ⟨⟨pr, ps⟩, hprs, hpc, hpd⟩
  rcases q with ⟨⟨qr, qs⟩, hqrs, hqc, hqd⟩
  have hp : (pr = c ∧ ps = d) ∨ (pr = d ∧ ps = c) := by
    rcases hpc with hpc | hpc <;> rcases hpd with hpd | hpd
    · exact (hcd (hpc.trans hpd.symm)).elim
    · exact Or.inl ⟨hpc.symm, hpd.symm⟩
    · exact Or.inr ⟨hpd.symm, hpc.symm⟩
    · exact (hcd (hpc.trans hpd.symm)).elim
  have hq : (qr = c ∧ qs = d) ∨ (qr = d ∧ qs = c) := by
    rcases hqc with hqc | hqc <;> rcases hqd with hqd | hqd
    · exact (hcd (hqc.trans hqd.symm)).elim
    · exact Or.inl ⟨hqc.symm, hqd.symm⟩
    · exact Or.inr ⟨hqd.symm, hqc.symm⟩
    · exact (hcd (hqc.trans hqd.symm)).elim
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact Prod.ext (hp.1.trans hq.1.symm) (hp.2.trans hq.2.symm)
  · exfalso
    have hdc : d = c := by
      simpa [twoColorPairCode, hp.1, hq.1, hcd] using hpq
    exact hcd hdc.symm
  · exfalso
    have hdc : d = c := by
      simpa [twoColorPairCode, hp.1, hq.1, hcd] using hpq
    exact hcd hdc.symm
  · exact Prod.ext (hp.1.trans hq.1.symm) (hp.2.trans hq.2.symm)

theorem card_twoColorPair_le_two {k : ℕ} (c d : Fin k) (hcd : c ≠ d) :
    Fintype.card (TwoColorPair c d) ≤ 2 := by
  simpa using Fintype.card_le_of_injective (twoColorPairCode c d)
    (twoColorPairCode_injective c d hcd)

abbrev MarkedTripleContainingVertex {n : ℕ} (x : Fin n) :=
  Σ S : {S : TripleSet n // x ∈ S.1}, ApexIn S.1

theorem card_markedTripleContainingVertex {n : ℕ} (x : Fin n) :
    Fintype.card (MarkedTripleContainingVertex x) =
      (n - 1).choose 2 * 3 := by
  rw [Fintype.card_sigma]
  calc
    (∑ S : {S : TripleSet n // x ∈ S.1},
        Fintype.card (ApexIn S.1)) =
        ∑ _S : {S : TripleSet n // x ∈ S.1}, 3 := by
          apply Finset.sum_congr rfl
          intro S hS
          exact card_apexIn S.1
    _ = Fintype.card {S : TripleSet n // x ∈ S.1} * 3 := by simp
    _ = (n - 1).choose 2 * 3 := by
      rw [card_tripleContainingVertex]

def distinctVertexTwoColorPairCode {n k : ℕ}
    (x y : Fin n) (c d : Fin k) (hxy : x ≠ y) :
    {b : TriangleBlock n k //
      b ∈ blocksThroughAuxPair
        (Sum.inr (x, c) : AuxVertex n k) (Sum.inr (y, d))} →
      MarkedTripleContainingPair x y × TwoColorPair c d :=
  fun b ↦ by
    have hb := (Finset.mem_filter.mp b.2).2
    have hxc := label_mem_of_inr_mem_auxSupport b.1 (x, c) hb.1
    have hyd := label_mem_of_inr_mem_auxSupport b.1 (y, d) hb.2
    have hx := (label_mem_positiveLabels_iff b.1 x c).mp hxc
    have hy := (label_mem_positiveLabels_iff b.1 y d).mp hyd
    exact
      ⟨⟨⟨blockTriple b.1, hx.1, hy.1⟩,
          ⟨b.1.apex, apex_mem_blockTriple b.1⟩⟩,
        ⟨(b.1.repeated, b.1.singleton), b.1.colors_ne,
          hx.2.elim Or.inl (fun h ↦ Or.inr h.1),
          hy.2.elim Or.inl (fun h ↦ Or.inr h.1)⟩⟩

theorem distinctVertexTwoColorPairCode_injective {n k : ℕ}
    (x y : Fin n) (c d : Fin k) (hxy : x ≠ y) :
    Function.Injective (distinctVertexTwoColorPairCode x y c d hxy) := by
  intro b e h
  apply Subtype.ext
  apply triangleBlock_ext_of_vertices_apex_colors
  · simpa [distinctVertexTwoColorPairCode] using
      congrArg (fun q ↦ q.1.1.val.val) h
  · simpa [distinctVertexTwoColorPairCode] using
      congrArg (fun q ↦ q.1.2.val) h
  · simpa [distinctVertexTwoColorPairCode] using
      congrArg (fun q ↦ q.2.val.1) h
  · simpa [distinctVertexTwoColorPairCode] using
      congrArg (fun q ↦ q.2.val.2) h

theorem card_blocksThroughAuxPair_labels_distinct_le {n k : ℕ}
    (x y : Fin n) (c d : Fin k) (hxy : x ≠ y) (hcd : c ≠ d) :
    (blocksThroughAuxPair
      (Sum.inr (x, c) : AuxVertex n k) (Sum.inr (y, d))).card ≤
        6 * n := by
  rw [← Fintype.card_coe]
  apply (Fintype.card_le_of_injective _
    (distinctVertexTwoColorPairCode_injective x y c d hxy)).trans
  rw [Fintype.card_prod, card_markedTripleContainingPair x y hxy]
  have hc := card_twoColorPair_le_two c d hcd
  calc
    (n - 2) * 3 * Fintype.card (TwoColorPair c d) ≤
        (n - 2) * 3 * 2 := Nat.mul_le_mul_left _ hc
    _ ≤ n * 3 * 2 := Nat.mul_le_mul_right 2
      (Nat.mul_le_mul_right 3 (Nat.sub_le n 2))
    _ = 6 * n := by ring

def sameVertexTwoColorPairCode {n k : ℕ}
    (x : Fin n) (c d : Fin k) :
    {b : TriangleBlock n k //
      b ∈ blocksThroughAuxPair
        (Sum.inr (x, c) : AuxVertex n k) (Sum.inr (x, d))} →
      MarkedTripleContainingVertex x × TwoColorPair c d :=
  fun b ↦ by
    have hb := (Finset.mem_filter.mp b.2).2
    have hxc := label_mem_of_inr_mem_auxSupport b.1 (x, c) hb.1
    have hxd := label_mem_of_inr_mem_auxSupport b.1 (x, d) hb.2
    have hc := (label_mem_positiveLabels_iff b.1 x c).mp hxc
    have hd := (label_mem_positiveLabels_iff b.1 x d).mp hxd
    exact
      ⟨⟨⟨blockTriple b.1, hc.1⟩,
          ⟨b.1.apex, apex_mem_blockTriple b.1⟩⟩,
        ⟨(b.1.repeated, b.1.singleton), b.1.colors_ne,
          hc.2.elim Or.inl (fun h ↦ Or.inr h.1),
          hd.2.elim Or.inl (fun h ↦ Or.inr h.1)⟩⟩

theorem sameVertexTwoColorPairCode_injective {n k : ℕ}
    (x : Fin n) (c d : Fin k) :
    Function.Injective (sameVertexTwoColorPairCode x c d) := by
  intro b e h
  apply Subtype.ext
  apply triangleBlock_ext_of_vertices_apex_colors
  · simpa [sameVertexTwoColorPairCode] using
      congrArg (fun q ↦ q.1.1.val.val) h
  · simpa [sameVertexTwoColorPairCode] using
      congrArg (fun q ↦ q.1.2.val) h
  · simpa [sameVertexTwoColorPairCode] using
      congrArg (fun q ↦ q.2.val.1) h
  · simpa [sameVertexTwoColorPairCode] using
      congrArg (fun q ↦ q.2.val.2) h

theorem card_blocksThroughAuxPair_labels_sameVertex_le {n k : ℕ}
    (x : Fin n) (c d : Fin k) (hcd : c ≠ d) :
    (blocksThroughAuxPair
      (Sum.inr (x, c) : AuxVertex n k) (Sum.inr (x, d))).card ≤
        6 * n ^ 2 := by
  rw [← Fintype.card_coe]
  apply (Fintype.card_le_of_injective _
    (sameVertexTwoColorPairCode_injective x c d)).trans
  rw [Fintype.card_prod, card_markedTripleContainingVertex]
  have hc := card_twoColorPair_le_two c d hcd
  have hchoose : (n - 1).choose 2 ≤ n ^ 2 :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le n 1) 2)
  calc
    (n - 1).choose 2 * 3 * Fintype.card (TwoColorPair c d) ≤
        (n - 1).choose 2 * 3 * 2 := Nat.mul_le_mul_left _ hc
    _ ≤ n ^ 2 * 3 * 2 := Nat.mul_le_mul_right 2
      (Nat.mul_le_mul_right 3 hchoose)
    _ = 6 * n ^ 2 := by ring

theorem pair_union_card_ge_three {α : Type*} [DecidableEq α]
    {x y u v : α} (hxy : x ≠ y) (huv : u ≠ v)
    (hpairs : ({x, y} : Finset α) ≠ {u, v}) :
    3 ≤ (({x, y} : Finset α) ∪ {u, v}).card := by
  let U : Finset α := {x, y} ∪ {u, v}
  have hA : ({x, y} : Finset α).card = 2 := by simp [hxy]
  have hB : ({u, v} : Finset α).card = 2 := by simp [huv]
  have hAsub : ({x, y} : Finset α) ⊆ U := by
    exact Finset.subset_union_left
  have hBsub : ({u, v} : Finset α) ⊆ U := by
    exact Finset.subset_union_right
  change 3 ≤ U.card
  by_contra h3
  have hUle : U.card ≤ 2 := by omega
  have hAU : ({x, y} : Finset α) = U :=
    Finset.eq_of_subset_of_card_le hAsub (by omega)
  have hBU : ({u, v} : Finset α) = U :=
    Finset.eq_of_subset_of_card_le hBsub (by omega)
  exact hpairs (hAU.trans hBU.symm)

theorem auxPairBlockVertices_eq_of_two_graph_roots {n k : ℕ}
    {x y u v : Fin n} (hxy : x ≠ y) (huv : u ≠ v)
    (hedges : s(x, y) ≠ s(u, v)) {b d : TriangleBlock n k}
    (hbx : (Sum.inl s(x, y) : AuxVertex n k) ∈ b.auxSupport)
    (hbu : (Sum.inl s(u, v) : AuxVertex n k) ∈ b.auxSupport)
    (hdx : (Sum.inl s(x, y) : AuxVertex n k) ∈ d.auxSupport)
    (hdu : (Sum.inl s(u, v) : AuxVertex n k) ∈ d.auxSupport) :
    auxPairBlockVertices b = auxPairBlockVertices d := by
  have hpairsets : ({x, y} : Finset (Fin n)) ≠ {u, v} := by
    intro h
    apply hedges
    rw [Sym2.eq_iff]
    have hx : x = u ∨ x = v := by
      have hxmem : x ∈ ({u, v} : Finset (Fin n)) := by rw [← h]; simp
      simpa using hxmem
    have hy : y = u ∨ y = v := by
      have hymem : y ∈ ({u, v} : Finset (Fin n)) := by rw [← h]; simp
      simpa using hymem
    rcases hx with hxu | hxv
    · exact Or.inl ⟨hxu, hy.resolve_left (fun hyu ↦ hxy (hxu.trans hyu.symm))⟩
    · exact Or.inr ⟨hxv, hy.resolve_right (fun hyv ↦ hxy (hxv.trans hyv.symm))⟩
  let U : Finset (Fin n) := {x, y} ∪ {u, v}
  have hU3 : 3 ≤ U.card := pair_union_card_ge_three hxy huv hpairsets
  have hbxy := (graph_mem_auxSupport_iff_vertices b x y hxy).mp hbx
  have hbuv := (graph_mem_auxSupport_iff_vertices b u v huv).mp hbu
  have hdxy := (graph_mem_auxSupport_iff_vertices d x y hxy).mp hdx
  have hduv := (graph_mem_auxSupport_iff_vertices d u v huv).mp hdu
  have hUb : U ⊆ auxPairBlockVertices b := by
    intro z hz
    simp only [U, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hz
    rcases hz with (rfl | rfl) | (rfl | rfl)
    · exact hbxy.1
    · exact hbxy.2
    · exact hbuv.1
    · exact hbuv.2
  have hUd : U ⊆ auxPairBlockVertices d := by
    intro z hz
    simp only [U, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hz
    rcases hz with (rfl | rfl) | (rfl | rfl)
    · exact hdxy.1
    · exact hdxy.2
    · exact hduv.1
    · exact hduv.2
  have hUbEq : U = auxPairBlockVertices b :=
    Finset.eq_of_subset_of_card_le hUb (by simp; omega)
  have hUdEq : U = auxPairBlockVertices d :=
    Finset.eq_of_subset_of_card_le hUd (by simp; omega)
  exact hUbEq.symm.trans hUdEq

def graphGraphPairCode {n k : ℕ}
    (x y u v : Fin n) (hxy : x ≠ y) (huv : u ≠ v)
    (hedges : s(x, y) ≠ s(u, v))
    (b0 : TriangleBlock n k)
    (hb0 : b0 ∈ blocksThroughAuxPair
      (Sum.inl s(x, y) : AuxVertex n k) (Sum.inl s(u, v))) :
    {b : TriangleBlock n k //
      b ∈ blocksThroughAuxPair
        (Sum.inl s(x, y) : AuxVertex n k) (Sum.inl s(u, v))} →
      ApexIn (blockTriple b0) × DistinctColorPair k :=
  fun b ↦ by
    have hb := (Finset.mem_filter.mp b.2).2
    have hb0' := (Finset.mem_filter.mp hb0).2
    have hV := auxPairBlockVertices_eq_of_two_graph_roots hxy huv hedges
      hb.1 hb.2 hb0'.1 hb0'.2
    exact
      ⟨⟨b.1.apex, by
          change b.1.apex ∈ auxPairBlockVertices b0
          rw [← hV]
          exact apex_mem_blockTriple b.1⟩,
        ⟨(b.1.repeated, b.1.singleton), b.1.colors_ne⟩⟩

theorem graphGraphPairCode_injective {n k : ℕ}
    (x y u v : Fin n) (hxy : x ≠ y) (huv : u ≠ v)
    (hedges : s(x, y) ≠ s(u, v))
    (b0 : TriangleBlock n k)
    (hb0 : b0 ∈ blocksThroughAuxPair
      (Sum.inl s(x, y) : AuxVertex n k) (Sum.inl s(u, v))) :
    Function.Injective
      (graphGraphPairCode x y u v hxy huv hedges b0 hb0) := by
  intro b d h
  apply Subtype.ext
  apply triangleBlock_ext_of_vertices_apex_colors
  · have hb := (Finset.mem_filter.mp b.2).2
    have hd := (Finset.mem_filter.mp d.2).2
    exact auxPairBlockVertices_eq_of_two_graph_roots hxy huv hedges
      hb.1 hb.2 hd.1 hd.2
  · simpa [graphGraphPairCode] using congrArg (fun q ↦ q.1.val) h
  · simpa [graphGraphPairCode] using congrArg (fun q ↦ q.2.val.1) h
  · simpa [graphGraphPairCode] using congrArg (fun q ↦ q.2.val.2) h

theorem card_blocksThroughAuxPair_graph_graph_le {n k : ℕ}
    (x y u v : Fin n) (hxy : x ≠ y) (huv : u ≠ v)
    (hedges : s(x, y) ≠ s(u, v)) :
    (blocksThroughAuxPair
      (Sum.inl s(x, y) : AuxVertex n k) (Sum.inl s(u, v))).card ≤
        3 * k ^ 2 := by
  let S := blocksThroughAuxPair
      (Sum.inl s(x, y) : AuxVertex n k) (Sum.inl s(u, v))
  by_cases hS : S.Nonempty
  · obtain ⟨b0, hb0⟩ := hS
    change S.card ≤ _
    rw [← Fintype.card_coe]
    apply (Fintype.card_le_of_injective _
      (graphGraphPairCode_injective x y u v hxy huv hedges b0 hb0)).trans
    rw [Fintype.card_prod, card_apexIn, card_distinctColorPair]
    calc
      3 * (k * (k - 1)) ≤ 3 * (k * k) :=
        Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left k (Nat.sub_le k 1))
      _ = 3 * k ^ 2 := by ring
  · have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change S.card ≤ _
    rw [this]
    simp

theorem card_blocksThroughAuxPair_labels_sameColor_le {n k : ℕ}
    (x y : Fin n) (c : Fin k) (hxy : x ≠ y) :
    (blocksThroughAuxPair
      (Sum.inr (x, c) : AuxVertex n k) (Sum.inr (y, c))).card ≤
        6 * n * k := by
  let a : SameColorIndex n k := ⟨c, x, y⟩
  simpa [blocksThroughAuxPair, blocksThroughPair, a,
    TriangleBlock.auxSupport] using card_blocksThroughPair_le a hxy

theorem diag_graph_not_mem_auxSupport {n k : ℕ} (b : TriangleBlock n k)
    (x : Fin n) :
    (Sum.inl s(x, x) : AuxVertex n k) ∉ b.auxSupport := by
  intro h
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨e, he, heq⟩ := Finset.mem_image.mp h
    have he' : e = s(x, x) := Sum.inl.inj heq
    subst e
    simp only [TriangleBlock.graphEdges, Finset.mem_insert,
      Finset.mem_singleton, Sym2.eq_iff] at he
    rcases he with (⟨h1, h2⟩ | ⟨h1, h2⟩) |
        (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact b.apex_ne_left (h1.symm.trans h2)
    · exact b.apex_ne_left (h2.symm.trans h1)
    · exact b.apex_ne_right (h1.symm.trans h2)
    · exact b.apex_ne_right (h2.symm.trans h1)
    · exact b.left_ne_right (h1.symm.trans h2)
    · exact b.left_ne_right (h2.symm.trans h1)
  · obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp h
    cases heq

theorem blocksThroughAuxPair_swap {n k : ℕ} (v w : AuxVertex n k) :
    blocksThroughAuxPair v w = blocksThroughAuxPair w v := by
  ext b
  simp [blocksThroughAuxPair, and_comm]

theorem card_blocksThroughAuxPair_le_six_sq {n k : ℕ}
    (hk : k ≤ n) {v w : AuxVertex n k} (hvw : v ≠ w) :
    (blocksThroughAuxPair v w).card ≤ 6 * n ^ 2 := by
  rcases v with e | ⟨x, c⟩
  · induction e using Sym2.inductionOn with
    | _ a b =>
      rcases w with f | ⟨z, d⟩
      · induction f using Sym2.inductionOn with
        | _ u t =>
          by_cases hab : a = b
          · subst b
            have hempty : blocksThroughAuxPair
                (Sum.inl s(a, a) : AuxVertex n k) (Sum.inl s(u, t)) = ∅ := by
              ext q
              simp [blocksThroughAuxPair, diag_graph_not_mem_auxSupport]
            simp [hempty]
          · by_cases hut : u = t
            · subst t
              have hempty : blocksThroughAuxPair
                  (Sum.inl s(a, b) : AuxVertex n k) (Sum.inl s(u, u)) = ∅ := by
                ext q
                simp [blocksThroughAuxPair, diag_graph_not_mem_auxSupport]
              simp [hempty]
            · have hedges : s(a, b) ≠ s(u, t) := by
                intro h
                apply hvw
                exact congrArg
                  (fun z : Sym2 (Fin n) ↦ (Sum.inl z : AuxVertex n k)) h
              calc
                (blocksThroughAuxPair
                    (Sum.inl s(a, b) : AuxVertex n k)
                    (Sum.inl s(u, t))).card ≤ 3 * k ^ 2 :=
                  card_blocksThroughAuxPair_graph_graph_le a b u t hab hut hedges
                _ ≤ 6 * n ^ 2 := by nlinarith [Nat.pow_le_pow_left hk 2]
      · by_cases hab : a = b
        · subst b
          have hempty : blocksThroughAuxPair
              (Sum.inl s(a, a) : AuxVertex n k) (Sum.inr (z, d)) = ∅ := by
            ext q
            simp [blocksThroughAuxPair, diag_graph_not_mem_auxSupport]
          simp [hempty]
        · calc
            (blocksThroughAuxPair
                (Sum.inl s(a, b) : AuxVertex n k) (Sum.inr (z, d))).card ≤
                6 * n * k := card_blocksThroughAuxPair_graph_label_le a b z d hab
            _ ≤ 6 * n ^ 2 := by nlinarith
  · rcases w with f | ⟨y, d⟩
    · rw [blocksThroughAuxPair_swap]
      induction f using Sym2.inductionOn with
      | _ a b =>
        by_cases hab : a = b
        · subst b
          have hempty : blocksThroughAuxPair
              (Sum.inl s(a, a) : AuxVertex n k) (Sum.inr (x, c)) = ∅ := by
            ext q
            simp [blocksThroughAuxPair, diag_graph_not_mem_auxSupport]
          simp [hempty]
        · calc
            (blocksThroughAuxPair
                (Sum.inl s(a, b) : AuxVertex n k) (Sum.inr (x, c))).card ≤
                6 * n * k := card_blocksThroughAuxPair_graph_label_le a b x c hab
            _ ≤ 6 * n ^ 2 := by nlinarith
    · by_cases hcd : c = d
      · subst d
        have hxy : x ≠ y := by
          intro h
          subst y
          exact hvw rfl
        exact (card_blocksThroughAuxPair_labels_sameColor_le x y c hxy).trans
          (by nlinarith)
      · by_cases hxy : x = y
        · subst y
          exact card_blocksThroughAuxPair_labels_sameVertex_le x c d hcd
        · have hn : 1 ≤ n := Nat.succ_le_iff.mpr (Nat.zero_lt_of_lt x.isLt)
          exact (card_blocksThroughAuxPair_labels_distinct_le x y c d hxy hcd).trans
            (by nlinarith)

theorem universal_auxiliary_maxCodegree {n k : ℕ} (hk : k ≤ n)
    (R : RetainedLabels n k) :
    MaxCodegreeLE (auxiliaryHypergraph (allTriangleBlocks n k) R) 2
      (6 * n ^ 2) := by
  intro s hs
  obtain ⟨v, w, hvw, rfl⟩ := Finset.card_eq_two.mp hs
  rw [codegree_pair_eq_blocks]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (card_blocksThroughAuxPair_le_six_sq hk hvw)

theorem sameColor_codegree_le_ceiling_of_host
    {n k : ℕ} {q delta : ℝ} {R : RetainedLabels n k}
    (hhost : UniversalRetainedHostEstimates q R)
    (a : SameColorIndex n k) (haa : a.left ≠ a.right)
    (hleft : (a.left, a.color) ∈ R)
    (hright : (a.right, a.color) ∈ R)
    (hscale : universalSameColorTarget n k q a +
        universalCodegreeDeviation n a ≤
      5 * (n : ℝ) ^ (2 - delta)) :
    codegree (auxiliaryHypergraph (allTriangleBlocks n k) R)
        {Sum.inr (a.left, a.color), Sum.inr (a.right, a.color)} ≤
      jmPairCodegreeCeil 5 0 delta n := by
  have hnear := hhost.2.1 a haa hleft hright
  rw [abs_lt] at hnear
  have hreal :
      (codegree (auxiliaryHypergraph (allTriangleBlocks n k) R)
          {Sum.inr (a.left, a.color), Sum.inr (a.right, a.color)} : ℝ) ≤
        (jmPairCodegreeCeil 5 0 delta n : ℝ) := by
    have hupper :
        (codegree (auxiliaryHypergraph (allTriangleBlocks n k) R)
            {Sum.inr (a.left, a.color), Sum.inr (a.right, a.color)} : ℝ) ≤
          universalSameColorTarget n k q a +
            universalCodegreeDeviation n a := by
      linarith [hnear.2]
    apply (hupper.trans hscale).trans
    change 5 * (n : ℝ) ^ (2 - delta) ≤
      (⌈5 * (n : ℝ) ^ (2 - delta) + 0⌉₊ : ℕ)
    simpa using Nat.le_ceil (5 * (n : ℝ) ^ (2 - delta))
  exact_mod_cast hreal


theorem universalSameColorTarget_jm_le {n k : ℕ} {delta : ℝ}
    (hn : 0 < n) (hk : k ≤ n) (a : SameColorIndex n k)
    (haa : a.left ≠ a.right) :
    universalSameColorTarget n k (jmDeletion delta n) a ≤
      4 * (n : ℝ) ^ (2 - delta) := by
  rw [universalSameColorTarget, if_neg haa]
  have hq0 : 0 ≤ jmDeletion delta n := (jmDeletion_pos hn).le
  have hq1 : jmDeletion delta n ≤ 1 := (jmDeletion_lt_one hn).le
  have hq3 : (jmDeletion delta n) ^ 3 ≤ 1 := pow_le_one₀ hq0 hq1
  have hrho0 : 0 ≤ jmRho delta n := Real.rpow_nonneg (by positivity) _
  have hret : jmRetention delta n ≤ jmRho delta n := by
    unfold jmRetention
    exact div_le_self hrho0 (by linarith)
  have hret0 : 0 ≤ jmRetention delta n := (jmRetention_pos hn).le
  have hcomp : 1 - jmDeletion delta n = jmRetention delta n := by
    linarith [jmRetention_add_deletion (delta := delta) hn]
  have hnat : 4 * (n - 2) * (k - 1) ≤ 4 * n * n := by
    nlinarith [Nat.sub_le n 2, Nat.sub_le k 1]
  have hfactor : ((4 * (n - 2) * (k - 1) : ℕ) : ℝ) ≤ 4 * n * n := by
    exact_mod_cast hnat
  have hnonneg : 0 ≤ (jmDeletion delta n) ^ 3 := pow_nonneg hq0 3
  calc
    ((4 * (n - 2) * (k - 1) : ℕ) : ℝ) *
          (jmDeletion delta n) ^ 3 * (1 - jmDeletion delta n) ≤
        (4 * (n : ℝ) * n) * 1 * jmRho delta n := by
      rw [hcomp]
      gcongr
    _ = 4 * (n : ℝ) ^ (2 - delta) := by
      unfold jmRho
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      rw [show 4 * (n : ℝ) * n * 1 * (n : ℝ) ^ (-delta) =
          4 * ((n : ℝ) ^ (2 : ℕ) * (n : ℝ) ^ (-delta)) by ring,
        ← Real.rpow_natCast, ← Real.rpow_add hnR]
      congr 1

theorem eventually_universal_sameColor_codegree_le_ceiling
    {delta : ℝ} (hdelta0 : 0 < delta) (hdeltaThird : delta < 1 / 3) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (R : RetainedLabels n (jmOldColors delta n)),
        UniversalRetainedHostEstimates (jmDeletion delta n) R →
        ∀ (a : SameColorIndex n (jmOldColors delta n)),
          a.left ≠ a.right →
          (a.left, a.color) ∈ R → (a.right, a.color) ∈ R →
          codegree
              (auxiliaryHypergraph
                (allTriangleBlocks n (jmOldColors delta n)) R)
              {Sum.inr (a.left, a.color), Sum.inr (a.right, a.color)} ≤
            jmPairCodegreeCeil 5 0 delta n := by
  have hgap : (5 / 3 : ℝ) < 2 - delta := by linarith
  have hdevEventually : ∀ᶠ n : ℕ in Filter.atTop,
      (1 : ℝ) * (n : ℝ) ^ (5 / 3 : ℝ) ≤
        (n : ℝ) ^ (2 - delta) :=
    eventually_const_mul_rpow_le_rpow
      (C := (1 : ℝ)) (a := (5 / 3 : ℝ)) (b := 2 - delta)
      (by norm_num) hgap
  have hcol : ∀ᶠ n : ℕ in Filter.atTop,
      jmOldColors delta n ≤ n := eventually_jmOldColors_le hdelta0
  have hpair : ∀ᶠ n : ℕ in Filter.atTop,
      jmOldColors delta n ≤ n ∧
        (1 : ℝ) * (n : ℝ) ^ (5 / 3 : ℝ) ≤
          (n : ℝ) ^ (2 - delta) :=
    Filter.Eventually.and hcol hdevEventually
  have hall : ∀ᶠ n : ℕ in Filter.atTop,
      1 ≤ n ∧ (jmOldColors delta n ≤ n ∧
        (1 : ℝ) * (n : ℝ) ^ (5 / 3 : ℝ) ≤
          (n : ℝ) ^ (2 - delta)) :=
    Filter.Eventually.and (Filter.eventually_ge_atTop (1 : ℕ)) hpair
  apply hall.mono
  intro n hnAll
  rcases hnAll with ⟨hn, hk, hdev⟩
  intro R hhost a haa hleft hright
  apply sameColor_codegree_le_ceiling_of_host hhost a haa hleft hright
  have htarget := universalSameColorTarget_jm_le
    (delta := delta) (Nat.zero_lt_of_lt hn) hk a haa
  have hdev' : universalCodegreeDeviation n a ≤
      (n : ℝ) ^ (2 - delta) := by
    simpa [universalCodegreeDeviation] using hdev
  calc
    universalSameColorTarget n (jmOldColors delta n)
          (jmDeletion delta n) a + universalCodegreeDeviation n a ≤
        4 * (n : ℝ) ^ (2 - delta) + (n : ℝ) ^ (2 - delta) :=
      add_le_add htarget hdev'
    _ = 5 * (n : ℝ) ^ (2 - delta) := by ring

theorem codegreeInfluenceNat_le {n k : ℕ}
    (a : SameColorIndex n k) (haa : a.left ≠ a.right) (hk : k ≤ n) :
    ∀ i, codegreeInfluenceNat a i ≤ 6 * n := by
  intro i
  by_cases hil : labelEquiv n k i = (a.left, a.color)
  · simp [codegreeInfluenceNat, hil]
  by_cases hir : labelEquiv n k i = (a.right, a.color)
  · simp [codegreeInfluenceNat, hir]
  simpa [codegreeInfluenceNat, haa, hil, hir, blocksThroughPair,
    TriangleBlock.auxSupport] using
    (card_sameColor_dependency_blocks_le a.left a.right a.color
      (labelEquiv n k i) haa hil hir hk)

theorem codegreeInfluence_sq_sum {n k : ℕ}
    (a : SameColorIndex n k) (haa : a.left ≠ a.right) (hk : k ≤ n) :
    ∑ i, codegreeInfluence a i ^ 2 ≤ (144 : ℝ) * n ^ 3 := by
  exact codegreeInfluence_sq_sum_of_counts a haa hk
    (codegreeInfluenceNat_le a haa hk) (card_blocksThroughPair_le a haa)

theorem codegreeInfluence_sq_sum_all {n k : ℕ} (hk : k ≤ n)
    (a : SameColorIndex n k) :
    ∑ i, codegreeInfluence a i ^ 2 ≤ (144 : ℝ) * n ^ 3 := by
  by_cases haa : a.left = a.right
  · simp [codegreeInfluence, codegreeInfluenceNat, haa]
  · exact codegreeInfluence_sq_sum a haa hk

theorem labelCount_cast_le_pow {n k r : ℕ} (hn : 1 ≤ n) (hk : k ≤ n)
    (hr : 2 ≤ r) :
    (labelCount n k : ℝ) ≤ (n : ℝ) ^ r := by
  have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    (labelCount n k : ℝ) = (n : ℝ) * k := by simp [labelCount]
    _ ≤ (n : ℝ) * n := by gcongr
    _ = (n : ℝ) ^ 2 := by ring
    _ ≤ (n : ℝ) ^ r := pow_le_pow_right₀ hnR hr

theorem safeDegreeInfluence_sq_sum {n k : ℕ} (hn : 1 ≤ n) (hk : k ≤ n)
    (v : AuxVertex n k) :
    ∑ i, safeDegreeInfluence v i ^ 2 ≤ (126 : ℝ) * n ^ 5 := by
  have hs := sum_safeInfluence_sq_le (degreeInfluence v)
    (fun i ↦ by simp [degreeInfluence])
  have hraw := degreeInfluence_sq_sum hk v
  have hcount := labelCount_cast_le_pow hn hk (r := 5) (by norm_num)
  unfold safeDegreeInfluence
  calc
    ∑ i, safeInfluence (degreeInfluence v) i ^ 2 ≤
        (∑ i, degreeInfluence v i ^ 2) + labelCount n k := hs
    _ ≤ (125 : ℝ) * n ^ 5 + n ^ 5 := add_le_add hraw hcount
    _ = (126 : ℝ) * n ^ 5 := by ring

theorem safeCodegreeInfluence_sq_sum {n k : ℕ}
    (hn : 1 ≤ n) (hk : k ≤ n) (a : SameColorIndex n k) :
    ∑ i, safeCodegreeInfluence a i ^ 2 ≤ (145 : ℝ) * n ^ 3 := by
  have hs := sum_safeInfluence_sq_le (codegreeInfluence a)
    (fun i ↦ by simp [codegreeInfluence])
  have hraw := codegreeInfluence_sq_sum_all hk a
  have hcount := labelCount_cast_le_pow hn hk (r := 3) (by norm_num)
  unfold safeCodegreeInfluence
  calc
    ∑ i, safeInfluence (codegreeInfluence a) i ^ 2 ≤
        (∑ i, codegreeInfluence a i ^ 2) + labelCount n k := hs
    _ ≤ (144 : ℝ) * n ^ 3 + n ^ 3 := add_le_add hraw hcount
    _ = (145 : ℝ) * n ^ 3 := by ring

/-! ## Pair-role influence counts -/

def otherLeaf {n k : ℕ} (b : TriangleBlock n k) (root : Fin n) : Fin n :=
  if b.left = root then b.right else b.left

theorem orderedLeaves_eq_of_otherLeaf_eq {n k : ℕ}
    {b b' : TriangleBlock n k} {root : Fin n}
    (hb : b.left = root ∨ b.right = root)
    (hb' : b'.left = root ∨ b'.right = root)
    (ho : otherLeaf b root = otherLeaf b' root) :
    b.left = b'.left ∧ b.right = b'.right := by
  rcases hb with hl | hr <;> rcases hb' with hl' | hr'
  · simp [otherLeaf, hl, hl'] at ho
    exact ⟨hl.trans hl'.symm, ho⟩
  · have hnl' : b'.left ≠ root := by
      intro h
      exact (ne_of_lt b'.left_lt_right) (h.trans hr'.symm)
    simp [otherLeaf, hl, hnl'] at ho
    have h₁ : root < b'.left := by simpa [hl, ho] using b.left_lt_right
    have h₂ : b'.left < root := by simpa [hr'] using b'.left_lt_right
    exact False.elim (lt_asymm h₁ h₂)
  · have hnl : b.left ≠ root := by
      intro h
      exact (ne_of_lt b.left_lt_right) (h.trans hr.symm)
    simp [otherLeaf, hnl, hl'] at ho
    have h₁ : b.left < root := by simpa [hr] using b.left_lt_right
    have h₂ : root < b.left := by simpa [hl', ho] using b'.left_lt_right
    exact False.elim (lt_asymm h₁ h₂)
  · have hnl : b.left ≠ root := by
      intro h
      have : b.left = b.right := h.trans hr.symm
      exact (ne_of_lt b.left_lt_right) this
    have hnl' : b'.left ≠ root := by
      intro h
      have : b'.left = b'.right := h.trans hr'.symm
      exact (ne_of_lt b'.left_lt_right) this
    simp [otherLeaf, hnl, hnl'] at ho
    exact ⟨ho, hr.trans hr'.symm⟩

abbrev RootBlockCode (n k : ℕ) := Fin n × (Fin n × Fin k)

def rootBlockCode {n k : ℕ} (r : RootRole) (root : Fin n)
    (b : TriangleBlock n k) : RootBlockCode n k :=
  match r with
  | .repeatedApex => (b.left, (b.right, b.singleton))
  | .repeatedLeaf => (b.apex, (otherLeaf b root, b.singleton))
  | .singletonLeaf => (b.apex, (otherLeaf b root, b.repeated))

theorem rootBlockCode_inj {n k : ℕ} {r : RootRole} {root : Fin n}
    {colour : Fin k} {b b' : TriangleBlock n k}
    (hb : RoleFits r b root colour) (hb' : RoleFits r b' root colour)
    (hc : rootBlockCode r root b = rootBlockCode r root b') : b = b' := by
  cases r with
  | repeatedApex =>
      simp only [RoleFits] at hb hb'
      simp only [rootBlockCode, Prod.mk.injEq] at hc
      rcases hb with ⟨hrep, hapex⟩
      rcases hb' with ⟨hrep', hapex'⟩
      rcases hc with ⟨hleft, hright, hsingle⟩
      cases b
      cases b'
      simp_all

  | repeatedLeaf =>
      simp only [RoleFits] at hb hb'
      simp only [rootBlockCode, Prod.mk.injEq] at hc
      rcases hb with ⟨hrep, hleaf⟩
      rcases hb' with ⟨hrep', hleaf'⟩
      rcases hc with ⟨hapex, hother, hsingle⟩
      have hleaves := orderedLeaves_eq_of_otherLeaf_eq hleaf hleaf' hother
      cases b
      cases b'
      simp_all
  | singletonLeaf =>
      simp only [RoleFits] at hb hb'
      simp only [rootBlockCode, Prod.mk.injEq] at hc
      rcases hb with ⟨hsingle, hleaf⟩
      rcases hb' with ⟨hsingle', hleaf'⟩
      rcases hc with ⟨hapex, hother, hrep⟩
      have hleaves := orderedLeaves_eq_of_otherLeaf_eq hleaf hleaf' hother
      cases b
      cases b'
      simp_all

abbrev RoleWitnessCode (n k : ℕ) :=
  RootBlockCode n k × (RootBlockCode n k × Fin k)

def roleWitnessCode {n k : ℕ} (a : PairRoleIndex n)
    (w : PairWitness n k) : RoleWitnessCode n k :=
  (rootBlockCode a.leftRole a.x w.leftBlock,
    (rootBlockCode a.rightRole a.y w.rightBlock, w.common))

theorem roleWitnessCode_inj_of_mem {n k : ℕ} {a : PairRoleIndex n}
    {w w' : PairWitness n k}
    (hw : w ∈ geometricRoleWitnesses (allTriangleBlocks n k) a)
    (hw' : w' ∈ geometricRoleWitnesses (allTriangleBlocks n k) a)
    (hc : roleWitnessCode a w = roleWitnessCode a w') : w = w' := by
  have hwm := Finset.mem_filter.mp hw
  have hwm' := Finset.mem_filter.mp hw'
  have hg := (Finset.mem_filter.mp hwm.1).2
  have hg' := (Finset.mem_filter.mp hwm'.1).2
  rcases hwm.2 with ⟨hrl, hrr⟩
  rcases hwm'.2 with ⟨hrl', hrr'⟩
  rcases hg with ⟨_, _, _, _, _, _, _, hfl, hfr⟩
  rcases hg' with ⟨_, _, _, _, _, _, _, hfl', hfr'⟩
  simp only [roleWitnessCode, Prod.mk.injEq] at hc
  rcases hc with ⟨hcl, hcr, hcc⟩
  have hfl0 : RoleFits a.leftRole w.leftBlock a.x w.common := by
    simpa [PairRoleIndex.toPairTestIndex, hrl] using hfl
  have hfl0' : RoleFits a.leftRole w'.leftBlock a.x w.common := by
    simpa [PairRoleIndex.toPairTestIndex, hrl', hcc] using hfl'
  have hfr0 : RoleFits a.rightRole w.rightBlock a.y w.common := by
    simpa [PairRoleIndex.toPairTestIndex, hrr] using hfr
  have hfr0' : RoleFits a.rightRole w'.rightBlock a.y w.common := by
    simpa [PairRoleIndex.toPairTestIndex, hrr', hcc] using hfr'
  have hbl : w.leftBlock = w'.leftBlock :=
    rootBlockCode_inj hfl0 hfl0' hcl
  have hbr : w.rightBlock = w'.rightBlock :=
    rootBlockCode_inj hfr0 hfr0' hcr
  cases w
  cases w'
  simp_all

abbrev RolePalette (k : ℕ) := Fin k × (Fin k × Fin k)

def roleWitnessPalette {n k : ℕ} (a : PairRoleIndex n)
    (w : PairWitness n k) : RolePalette k :=
  (w.common,
    ((rootBlockCode a.leftRole a.x w.leftBlock).2.2,
      (rootBlockCode a.rightRole a.y w.rightBlock).2.2))

def RolePalette.Touches {k : ℕ} (c : Fin k) (p : RolePalette k) : Prop :=
  p.1 = c ∨ p.2.1 = c ∨ p.2.2 = c

theorem roleWitness_touch_colour {n k : ℕ} {a : PairRoleIndex n}
    {w : PairWitness n k} {z : Fin n × Fin k}
    (hw : w ∈ geometricRoleWitnesses (allTriangleBlocks n k) a)
    (hz : w.Touches z) : (roleWitnessPalette a w).Touches z.2 := by
  rcases a with ⟨ax, ay, hxy, rl, rr⟩
  have hwm := Finset.mem_filter.mp hw
  have hg := (Finset.mem_filter.mp hwm.1).2
  rcases hwm.2 with ⟨hrl, hrr⟩
  rcases hg with ⟨_, _, _, _, _, _, _, hfl, hfr⟩
  cases rl <;> cases rr <;>
    simp_all [PairRoleIndex.toPairTestIndex, RoleFits,
      PairWitness.Touches, PairWitness.positiveLabels,
      PairWitness.negativeLabels, TriangleBlock.positiveLabels,
      RolePalette.Touches, roleWitnessPalette, rootBlockCode, otherLeaf] <;>
    aesop

abbrev RoleVertices (n : ℕ) := Fin n × (Fin n × (Fin n × Fin n))

def roleWitnessVertices {n k : ℕ} (a : PairRoleIndex n)
    (w : PairWitness n k) : RoleVertices n :=
  let l := rootBlockCode a.leftRole a.x w.leftBlock
  let r := rootBlockCode a.rightRole a.y w.rightBlock
  (l.1, (l.2.1, (r.1, r.2.1)))

def RoleVertices.Contains {n : ℕ} (v : Fin n) (t : RoleVertices n) : Prop :=
  t.1 = v ∨ t.2.1 = v ∨ t.2.2.1 = v ∨ t.2.2.2 = v

theorem roleWitness_touch_vertex {n k : ℕ} {a : PairRoleIndex n}
    {w : PairWitness n k} {z : Fin n × Fin k}
    (hw : w ∈ geometricRoleWitnesses (allTriangleBlocks n k) a)
    (hz : w.Touches z) (hx : z.1 ≠ a.x) (hy : z.1 ≠ a.y) :
    (roleWitnessVertices a w).Contains z.1 := by
  rcases a with ⟨ax, ay, hxy, rl, rr⟩
  have hwm := Finset.mem_filter.mp hw
  have hg := (Finset.mem_filter.mp hwm.1).2
  rcases hwm.2 with ⟨hrl, hrr⟩
  rcases hg with ⟨_, _, _, _, _, _, _, hfl, hfr⟩
  cases rl <;> cases rr <;>
    simp_all [PairRoleIndex.toPairTestIndex, RoleFits,
      PairWitness.Touches, PairWitness.positiveLabels,
      PairWitness.negativeLabels, TriangleBlock.positiveLabels,
      RoleVertices.Contains, roleWitnessVertices, rootBlockCode, otherLeaf] <;>
    aesop

def rolePaletteTouchCode {k : ℕ} (c : Fin k)
    (p : {p : RolePalette k // p.Touches c}) :
    Fin 3 × (Fin k × Fin k) :=
  if p.1.1 = c then (0, (p.1.2.1, p.1.2.2))
  else if p.1.2.1 = c then (1, (p.1.1, p.1.2.2))
  else (2, (p.1.1, p.1.2.1))

theorem rolePaletteTouchCode_injective {k : ℕ} (c : Fin k) :
    Function.Injective (rolePaletteTouchCode c) := by
  intro p q hpq
  have hpT := p.2
  have hqT := q.2
  by_cases hp0 : p.1.1 = c
  all_goals by_cases hp1 : p.1.2.1 = c
  all_goals by_cases hq0 : q.1.1 = c
  all_goals by_cases hq1 : q.1.2.1 = c
  all_goals
    simp_all [rolePaletteTouchCode, RolePalette.Touches, Prod.ext_iff]
  all_goals ext <;> simp_all [RolePalette.Touches]

theorem card_rolePaletteTouches_le {k : ℕ} (c : Fin k) :
    Fintype.card {p : RolePalette k // p.Touches c} ≤ 3 * k ^ 2 := by
  calc
    Fintype.card {p : RolePalette k // p.Touches c} ≤
        Fintype.card (Fin 3 × (Fin k × Fin k)) :=
      Fintype.card_le_of_injective (rolePaletteTouchCode c)
        (rolePaletteTouchCode_injective c)
    _ = 3 * k ^ 2 := by simp [pow_two]

def touchedRoleWitnessCode {n k : ℕ} (a : PairRoleIndex n)
    (z : Fin n × Fin k)
    (w : {w : PairWitness n k //
      w ∈ (geometricRoleWitnesses (allTriangleBlocks n k) a).filter
        (fun w ↦ w.Touches z)}) :
    RoleVertices n × {p : RolePalette k // p.Touches z.2} :=
  (roleWitnessVertices a w.1,
    ⟨roleWitnessPalette a w.1,
      roleWitness_touch_colour (Finset.mem_filter.mp w.2).1
        (Finset.mem_filter.mp w.2).2⟩)

theorem touchedRoleWitnessCode_injective {n k : ℕ} (a : PairRoleIndex n)
    (z : Fin n × Fin k) : Function.Injective (touchedRoleWitnessCode a z) := by
  intro w w' h
  apply Subtype.ext
  apply roleWitnessCode_inj_of_mem
    (Finset.mem_filter.mp w.2).1 (Finset.mem_filter.mp w'.2).1
  have hv := congrArg Prod.fst h
  have hp := congrArg (fun u ↦ u.2.1) h
  have hv1 := congrArg (fun t : RoleVertices n ↦ t.1) hv
  have hv2 := congrArg (fun t : RoleVertices n ↦ t.2.1) hv
  have hv3 := congrArg (fun t : RoleVertices n ↦ t.2.2.1) hv
  have hv4 := congrArg (fun t : RoleVertices n ↦ t.2.2.2) hv
  have hc := congrArg (fun p : RolePalette k ↦ p.1) hp
  have hcl := congrArg (fun p : RolePalette k ↦ p.2.1) hp
  have hcr := congrArg (fun p : RolePalette k ↦ p.2.2) hp
  simp only [touchedRoleWitnessCode, roleWitnessVertices,
    roleWitnessPalette] at hv1 hv2 hv3 hv4 hc hcl hcr
  simp only [roleWitnessCode]
  apply Prod.ext
  · apply Prod.ext
    · exact hv1
    · apply Prod.ext
      · exact hv2
      · exact hcl
  · apply Prod.ext
    · apply Prod.ext
      · exact hv3
      · apply Prod.ext
        · exact hv4
        · exact hcr
    · exact hc

theorem pairRoleExactInfluence_le {n k : ℕ} (a : PairRoleIndex n)
    (i : Fin (labelCount n k)) :
    pairRoleExactInfluence (allTriangleBlocks n k) a i ≤
      3 * (n : ℝ) ^ 4 * (k : ℝ) ^ 2 := by
  let z := labelEquiv n k i
  have hinj := touchedRoleWitnessCode_injective a z
  have hcard :
      ((geometricRoleWitnesses (allTriangleBlocks n k) a).filter
        (fun w ↦ w.Touches z)).card ≤
        Fintype.card (RoleVertices n) *
          Fintype.card {p : RolePalette k // p.Touches z.2} := by
    simpa only [Fintype.card_prod, Fintype.card_coe] using
      Fintype.card_le_of_injective (touchedRoleWitnessCode a z) hinj
  have hpal := card_rolePaletteTouches_le z.2
  have hnat :
      ((geometricRoleWitnesses (allTriangleBlocks n k) a).filter
        (fun w ↦ w.Touches z)).card ≤ n ^ 4 * (3 * k ^ 2) := by
    calc
      _ ≤ Fintype.card (RoleVertices n) *
          Fintype.card {p : RolePalette k // p.Touches z.2} := hcard
      _ ≤ Fintype.card (RoleVertices n) * (3 * k ^ 2) :=
        Nat.mul_le_mul_left _ hpal
      _ = n ^ 4 * (3 * k ^ 2) := by
        simp only [RoleVertices, Fintype.card_prod, Fintype.card_fin]
        ring
  unfold pairRoleExactInfluence
  change (((geometricRoleWitnesses (allTriangleBlocks n k) a).filter
    (fun w ↦ w.Touches z)).card : ℝ) ≤ _
  have hnatR :
      (((geometricRoleWitnesses (allTriangleBlocks n k) a).filter
        (fun w ↦ w.Touches z)).card : ℝ) ≤
        ((n ^ 4 * (3 * k ^ 2) : ℕ) : ℝ) := by exact_mod_cast hnat
  calc
    _ ≤ ((n ^ 4 * (3 * k ^ 2) : ℕ) : ℝ) := hnatR
    _ = 3 * (n : ℝ) ^ 4 * (k : ℝ) ^ 2 := by push_cast; ring

def geometricRoleCode {n k : ℕ} (a : PairRoleIndex n)
    (w : {w : PairWitness n k //
      w ∈ geometricRoleWitnesses (allTriangleBlocks n k) a}) :
    RoleWitnessCode n k := roleWitnessCode a w.1

theorem geometricRoleCode_injective {n k : ℕ} (a : PairRoleIndex n) :
    Function.Injective (geometricRoleCode (k := k) a) := by
  intro w w' h
  apply Subtype.ext
  exact roleWitnessCode_inj_of_mem w.2 w'.2 h

theorem card_geometricRoleWitnesses_le {n k : ℕ} (a : PairRoleIndex n) :
    (geometricRoleWitnesses (allTriangleBlocks n k) a).card ≤
      n ^ 4 * k ^ 3 := by
  calc
    _ = Fintype.card {w : PairWitness n k //
        w ∈ geometricRoleWitnesses (allTriangleBlocks n k) a} := by simp
    _ ≤ Fintype.card (RoleWitnessCode n k) :=
      Fintype.card_le_of_injective (geometricRoleCode (k := k) a)
        (geometricRoleCode_injective (k := k) a)
    _ = n ^ 4 * k ^ 3 := by
      simp only [RoleWitnessCode, RootBlockCode,
        Fintype.card_prod, Fintype.card_fin]
      ring

def PairWitness.touchLabels {n k : ℕ} (w : PairWitness n k) :
    Finset (Fin n × Fin k) := w.positiveLabels ∪ w.negativeLabels

@[simp] theorem PairWitness.mem_touchLabels {n k : ℕ} (w : PairWitness n k)
    (z : Fin n × Fin k) : z ∈ w.touchLabels ↔ w.Touches z := by
  simp [PairWitness.touchLabels, PairWitness.Touches]

theorem PairWitness.touchLabels_card_le {n k : ℕ} (w : PairWitness n k) :
    w.touchLabels.card ≤ 12 := by
  calc
    w.touchLabels.card ≤ w.positiveLabels.card + w.negativeLabels.card :=
      Finset.card_union_le _ _
    _ ≤ (w.leftBlock.positiveLabels.card +
          w.rightBlock.positiveLabels.card) + 2 := by
      apply Nat.add_le_add
      · exact Finset.card_union_le _ _
      · simpa [PairWitness.negativeLabels] using
          (Finset.card_insert_le (w.leftBlock.apex, w.leftBlock.singleton)
            {(w.rightBlock.apex, w.rightBlock.singleton)})
    _ = 12 := by simp

theorem sum_pairRoleInfluence_cards {n k : ℕ} (a : PairRoleIndex n) :
    (∑ i : Fin (labelCount n k),
      ((geometricRoleWitnesses (allTriangleBlocks n k) a).filter fun w ↦
        w.Touches (labelEquiv n k i)).card) =
      ∑ w ∈ geometricRoleWitnesses (allTriangleBlocks n k) a,
        w.touchLabels.card := by
  classical
  let G := geometricRoleWitnesses (allTriangleBlocks n k) a
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (Finset.univ : Finset (Fin (labelCount n k))))
    (t := G) (r := fun i w ↦ w.Touches (labelEquiv n k i))
  calc
    _ = ∑ w ∈ G,
        ((Finset.univ : Finset (Fin (labelCount n k))).filter fun i ↦
          w.Touches (labelEquiv n k i)).card := by
      simpa only [G, Finset.bipartiteAbove, Finset.bipartiteBelow] using hdc
    _ = ∑ w ∈ G, w.touchLabels.card := by
      apply Finset.sum_congr rfl
      intro w hw
      simpa only [PairWitness.mem_touchLabels] using
        (card_coordinate_filter w.touchLabels)

theorem sum_pairRoleInfluence_cards_le {n k : ℕ} (a : PairRoleIndex n) :
    (∑ i : Fin (labelCount n k),
      ((geometricRoleWitnesses (allTriangleBlocks n k) a).filter fun w ↦
        w.Touches (labelEquiv n k i)).card) ≤
      12 * (n ^ 4 * k ^ 3) := by
  rw [sum_pairRoleInfluence_cards]
  calc
    _ ≤ ∑ _w ∈ geometricRoleWitnesses (allTriangleBlocks n k) a, 12 := by
      apply Finset.sum_le_sum
      intro w hw
      exact w.touchLabels_card_le
    _ = 12 * (geometricRoleWitnesses (allTriangleBlocks n k) a).card := by
      simp [Nat.mul_comm]
    _ ≤ 12 * (n ^ 4 * k ^ 3) :=
      Nat.mul_le_mul_left 12 (card_geometricRoleWitnesses_le a)

theorem pairRoleExactInfluence_sq_sum_le {n k : ℕ}
    (a : PairRoleIndex n) (hk : k ≤ n) :
    ∑ i : Fin (labelCount n k),
        pairRoleExactInfluence (allTriangleBlocks n k) a i ^ 2 ≤
      (36 : ℝ) * (n : ℝ) ^ 13 := by
  have hsumNat := sum_pairRoleInfluence_cards_le (k := k) a
  have hsum :
      ∑ i : Fin (labelCount n k),
          pairRoleExactInfluence (allTriangleBlocks n k) a i ≤
        (12 : ℝ) * (n : ℝ) ^ 4 * (k : ℝ) ^ 3 := by
    unfold pairRoleExactInfluence
    have hcast :
        ((∑ i : Fin (labelCount n k),
          ((geometricRoleWitnesses (allTriangleBlocks n k) a).filter fun w ↦
            w.Touches (labelEquiv n k i)).card : ℕ) : ℝ) ≤
          ((12 * (n ^ 4 * k ^ 3) : ℕ) : ℝ) := by
      exact_mod_cast hsumNat
    simpa only [Nat.cast_sum] using (hcast.trans_eq (by push_cast; ring))
  calc
    ∑ i : Fin (labelCount n k),
        pairRoleExactInfluence (allTriangleBlocks n k) a i ^ 2 ≤
      ∑ i : Fin (labelCount n k),
        (3 * (n : ℝ) ^ 4 * (k : ℝ) ^ 2) *
          pairRoleExactInfluence (allTriangleBlocks n k) a i := by
      apply Finset.sum_le_sum
      intro i hi
      have hmax := pairRoleExactInfluence_le a i
      have hnonneg : 0 ≤ pairRoleExactInfluence
          (allTriangleBlocks n k) a i := by
        unfold pairRoleExactInfluence
        positivity
      nlinarith
    _ = (3 * (n : ℝ) ^ 4 * (k : ℝ) ^ 2) *
        ∑ i : Fin (labelCount n k),
          pairRoleExactInfluence (allTriangleBlocks n k) a i := by
      rw [Finset.mul_sum]
    _ ≤ (3 * (n : ℝ) ^ 4 * (k : ℝ) ^ 2) *
        ((12 : ℝ) * (n : ℝ) ^ 4 * (k : ℝ) ^ 3) := by
      gcongr
    _ = (36 : ℝ) * (n : ℝ) ^ 8 * (k : ℝ) ^ 5 := by ring
    _ ≤ (36 : ℝ) * (n : ℝ) ^ 8 * (n : ℝ) ^ 5 := by
      have hkR : (k : ℝ) ≤ n := by exact_mod_cast hk
      gcongr
    _ = (36 : ℝ) * (n : ℝ) ^ 13 := by ring

theorem safePairRoleInfluence_sq_sum_le {n k : ℕ}
    (hn : 1 ≤ n) (hk : k ≤ n) (a : PairRoleIndex n) :
    ∑ i : Fin (labelCount n k), safePairRoleInfluence a i ^ 2 ≤
      (37 : ℝ) * (n : ℝ) ^ 13 := by
  have hs := sum_safeInfluence_sq_le
    (pairRoleExactInfluence (allTriangleBlocks n k) a)
    (fun i ↦ by unfold pairRoleExactInfluence; positivity)
  have hraw := pairRoleExactInfluence_sq_sum_le a hk
  have hcount := labelCount_cast_le_pow hn hk (r := 13) (by norm_num)
  unfold safePairRoleInfluence
  calc
    ∑ i : Fin (labelCount n k),
        safeInfluence (pairRoleExactInfluence
          (allTriangleBlocks n k) a) i ^ 2 ≤
      (∑ i : Fin (labelCount n k),
        pairRoleExactInfluence (allTriangleBlocks n k) a i ^ 2) +
          labelCount n k := hs
    _ ≤ (36 : ℝ) * (n : ℝ) ^ 13 + (n : ℝ) ^ 13 :=
      add_le_add hraw hcount
    _ = (37 : ℝ) * (n : ℝ) ^ 13 := by ring

/-! ## Explicit simultaneous tail budget -/

theorem common_scale_mul_le_twice_deviation_sq
    {n C p : ℕ} {a : ℝ} (hn : 1 ≤ n) (hC : C ≤ 2000000)
    (ha : (1 / 3 : ℝ) + p = 2 * a) :
    ((n : ℝ) ^ (1 / 3 : ℝ) / 1000000) *
        ((C : ℝ) * (n : ℝ) ^ p) ≤
      2 * ((n : ℝ) ^ a) ^ 2 := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hCR0 : (C : ℝ) ≤ 2000000 := by exact_mod_cast hC
  have hCR : (C : ℝ) / 1000000 ≤ 2 := by linarith
  calc
    ((n : ℝ) ^ (1 / 3 : ℝ) / 1000000) *
          ((C : ℝ) * (n : ℝ) ^ p) =
        ((C : ℝ) / 1000000) *
          ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ p) := by ring
    _ = ((C : ℝ) / 1000000) *
          (n : ℝ) ^ ((1 / 3 : ℝ) + p) := by
      rw [← Real.rpow_natCast, Real.rpow_add hnpos]
    _ ≤ 2 * (n : ℝ) ^ ((1 / 3 : ℝ) + p) := by
      gcongr
    _ = 2 * ((n : ℝ) ^ a) ^ 2 := by
      rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hn0]
      ring_nf

theorem two_exp_tail_le_common {n : ℕ} {t S B : ℝ}
    (hS : 0 < S) (hSB : S ≤ B)
    (hscale : ((n : ℝ) ^ (1 / 3 : ℝ) / 1000000) * B ≤ 2 * t ^ 2) :
    2 * Real.exp (-2 * t ^ 2 / S) ≤
      2 * Real.exp (-((n : ℝ) ^ (1 / 3 : ℝ)) / 1000000) := by
  have hcommon : 0 ≤ (n : ℝ) ^ (1 / 3 : ℝ) / 1000000 := by positivity
  have hratio : (n : ℝ) ^ (1 / 3 : ℝ) / 1000000 ≤
      2 * t ^ 2 / S := by
    apply (le_div_iff₀ hS).2
    calc
      ((n : ℝ) ^ (1 / 3 : ℝ) / 1000000) * S ≤
          ((n : ℝ) ^ (1 / 3 : ℝ) / 1000000) * B := by gcongr
      _ ≤ 2 * t ^ 2 := hscale
  have hexp : -2 * t ^ 2 / S ≤
      -((n : ℝ) ^ (1 / 3 : ℝ)) / 1000000 := by
    calc
      -2 * t ^ 2 / S = -(2 * t ^ 2 / S) := by ring
      _ ≤ -((n : ℝ) ^ (1 / 3 : ℝ) / 1000000) := neg_le_neg hratio
      _ = -((n : ℝ) ^ (1 / 3 : ℝ)) / 1000000 := by ring
  gcongr

theorem safeInfluence_sq_sum_pos {N : ℕ} (hN : 0 < N)
    (f : Fin N → ℝ) :
    0 < ∑ i, safeInfluence f i ^ 2 := by
  let i : Fin N := ⟨0, hN⟩
  have hi : 0 < safeInfluence f i ^ 2 := by
    have hone : (1 : ℝ) ≤ safeInfluence f i := le_max_left _ _
    nlinarith
  exact hi.trans_le (Finset.single_le_sum
    (fun j hj ↦ sq_nonneg (safeInfluence f j)) (Finset.mem_univ i))

theorem degree_tail_le_common {n k : ℕ}
    (hn : 1 ≤ n) (hk0 : 1 ≤ k) (hk : k ≤ n) (v : AuxVertex n k) :
    2 * Real.exp (-2 * (universalDegreeDeviation n v) ^ 2 /
        ∑ i, safeDegreeInfluence v i ^ 2) ≤
      2 * Real.exp (-((n : ℝ) ^ (1 / 3 : ℝ)) / 1000000) := by
  apply two_exp_tail_le_common
  · unfold safeDegreeInfluence
    apply safeInfluence_sq_sum_pos
    simp [labelCount, Nat.mul_pos hn hk0]
  · exact safeDegreeInfluence_sq_sum hn hk v
  · unfold universalDegreeDeviation
    exact common_scale_mul_le_twice_deviation_sq hn (by norm_num) (by norm_num)

theorem codegree_tail_le_common {n k : ℕ}
    (hn : 1 ≤ n) (hk0 : 1 ≤ k) (hk : k ≤ n) (a : SameColorIndex n k) :
    2 * Real.exp (-2 * (universalCodegreeDeviation n a) ^ 2 /
        ∑ i, safeCodegreeInfluence a i ^ 2) ≤
      2 * Real.exp (-((n : ℝ) ^ (1 / 3 : ℝ)) / 1000000) := by
  apply two_exp_tail_le_common
  · unfold safeCodegreeInfluence
    apply safeInfluence_sq_sum_pos
    simp [labelCount, Nat.mul_pos hn hk0]
  · exact safeCodegreeInfluence_sq_sum hn hk a
  · unfold universalCodegreeDeviation
    exact common_scale_mul_le_twice_deviation_sq hn (by norm_num) (by norm_num)

theorem pair_tail_le_common {n k : ℕ}
    (hn : 1 ≤ n) (hk0 : 1 ≤ k) (hk : k ≤ n) (a : PairRoleIndex n) :
    2 * Real.exp (-2 * (universalPairRoleDeviation n a) ^ 2 /
        ∑ i, safePairRoleInfluence (k := k) a i ^ 2) ≤
      2 * Real.exp (-((n : ℝ) ^ (1 / 3 : ℝ)) / 1000000) := by
  apply two_exp_tail_le_common
  · unfold safePairRoleInfluence
    apply safeInfluence_sq_sum_pos
    simp [labelCount, Nat.mul_pos hn hk0]
  · exact safePairRoleInfluence_sq_sum_le hn hk a
  · unfold universalPairRoleDeviation
    exact common_scale_mul_le_twice_deviation_sq hn (by norm_num) (by norm_num)

theorem card_auxVertex_le_two_mul_sq {n k : ℕ} (hk : k ≤ n) :
    Fintype.card (AuxVertex n k) ≤ 2 * n ^ 2 := by
  have hsym : Fintype.card (Sym2 (Fin n)) ≤ n ^ 2 := by
    simpa [Fintype.card_prod, pow_two] using
      (Fintype.card_le_of_surjective
        ((Sym2.mk (α := Fin n)).uncurry) Sym2.mk_surjective)
  rw [show Fintype.card (AuxVertex n k) =
      Fintype.card (Sym2 (Fin n)) + n * k by
    simp [AuxVertex, Fintype.card_sum, Fintype.card_prod]]
  calc
    Fintype.card (Sym2 (Fin n)) + n * k ≤ n ^ 2 + n * n := by gcongr
    _ = 2 * n ^ 2 := by ring

theorem card_sameColorIndex_le_cube {n k : ℕ} (hk : k ≤ n) :
    Fintype.card (SameColorIndex n k) ≤ n ^ 3 := by
  let e : SameColorIndex n k ≃ Fin k × Fin n × Fin n :=
    { toFun := fun a : SameColorIndex n k => (a.color, a.left, a.right)
      invFun := fun a : Fin k × Fin n × Fin n =>
        SameColorIndex.mk a.1 a.2.1 a.2.2
      left_inv := by intro a; cases a; rfl
      right_inv := by intro a; rcases a with ⟨a, b, c⟩; rfl }
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod, Fintype.card_fin]
  calc
    k * (n * n) ≤ n * (n * n) := Nat.mul_le_mul_right _ hk
    _ = n ^ 3 := by ring

@[simp] theorem card_rootRole : Fintype.card RootRole = 3 := by
  decide

theorem card_pairRoleIndex_le (n : ℕ) :
    Fintype.card (PairRoleIndex n) ≤ 9 * n ^ 2 := by
  let f : PairRoleIndex n → Fin n × Fin n × RootRole × RootRole :=
    fun a ↦ (a.x, a.y, a.leftRole, a.rightRole)
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with ⟨ax, ay, haxy, al, ar⟩
    rcases b with ⟨bx, byy, hbxy, bl, br⟩
    simp only [f, Prod.mk.injEq] at hab
    simp_all
  calc
    Fintype.card (PairRoleIndex n) ≤
        Fintype.card (Fin n × Fin n × RootRole × RootRole) :=
      Fintype.card_le_of_injective f hf
    _ = 9 * n ^ 2 := by
      simp only [Fintype.card_prod, Fintype.card_fin, card_rootRole]
      ring

theorem universal_union_tail_le {n k : ℕ}
    (hn : 1 ≤ n) (hk0 : 1 ≤ k) (hk : k ≤ n) :
    (∑ v : AuxVertex n k,
        2 * Real.exp (-2 * (universalDegreeDeviation n v) ^ 2 /
          ∑ i, safeDegreeInfluence v i ^ 2)) +
      (∑ a : SameColorIndex n k,
        2 * Real.exp (-2 * (universalCodegreeDeviation n a) ^ 2 /
          ∑ i, safeCodegreeInfluence a i ^ 2)) +
      (∑ a : PairRoleIndex n,
        2 * Real.exp (-2 * (universalPairRoleDeviation n a) ^ 2 /
          ∑ i, safePairRoleInfluence (k := k) a i ^ 2)) ≤
        universalTailBound n := by
  let E := Real.exp (-((n : ℝ) ^ (1 / 3 : ℝ)) / 1000000)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hd : (∑ v : AuxVertex n k,
        2 * Real.exp (-2 * (universalDegreeDeviation n v) ^ 2 /
          ∑ i, safeDegreeInfluence v i ^ 2)) ≤
      (2 * n ^ 2 : ℕ) * (2 * E) := by
    calc
      _ ≤ ∑ _v : AuxVertex n k, 2 * E := Finset.sum_le_sum fun v _ ↦
        degree_tail_le_common hn hk0 hk v
      _ = Fintype.card (AuxVertex n k) * (2 * E) := by simp
      _ ≤ (2 * n ^ 2 : ℕ) * (2 * E) := by
        gcongr
        exact card_auxVertex_le_two_mul_sq hk
  have hc : (∑ a : SameColorIndex n k,
        2 * Real.exp (-2 * (universalCodegreeDeviation n a) ^ 2 /
          ∑ i, safeCodegreeInfluence a i ^ 2)) ≤
      (n ^ 3 : ℕ) * (2 * E) := by
    calc
      _ ≤ ∑ _a : SameColorIndex n k, 2 * E := Finset.sum_le_sum fun a _ ↦
        codegree_tail_le_common hn hk0 hk a
      _ = Fintype.card (SameColorIndex n k) * (2 * E) := by simp
      _ ≤ (n ^ 3 : ℕ) * (2 * E) := by
        gcongr
        exact card_sameColorIndex_le_cube hk
  have hp : (∑ a : PairRoleIndex n,
        2 * Real.exp (-2 * (universalPairRoleDeviation n a) ^ 2 /
          ∑ i, safePairRoleInfluence (k := k) a i ^ 2)) ≤
      (9 * n ^ 2 : ℕ) * (2 * E) := by
    calc
      _ ≤ ∑ _a : PairRoleIndex n, 2 * E := Finset.sum_le_sum fun a _ ↦
        pair_tail_le_common hn hk0 hk a
      _ = Fintype.card (PairRoleIndex n) * (2 * E) := by simp
      _ ≤ (9 * n ^ 2 : ℕ) * (2 * E) := by
        gcongr
        exact card_pairRoleIndex_le n
  calc
    _ ≤ (2 * n ^ 2 : ℕ) * (2 * E) +
        (n ^ 3 : ℕ) * (2 * E) + (9 * n ^ 2 : ℕ) * (2 * E) := by
      gcongr
    _ ≤ (32 : ℝ) * n ^ 3 * E := by
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      push_cast
      nlinarith [sq_nonneg ((n : ℝ) - 1), mul_nonneg hE (sq_nonneg (n : ℝ))]
    _ = universalTailBound n := by simp [universalTailBound, E]

theorem exists_threshold_universal_union_tail_lt_one :
    ∃ n₀ : ℕ, ∀ n k : ℕ, n₀ ≤ n → 1 ≤ k → k ≤ n →
      (∑ v : AuxVertex n k,
          2 * Real.exp (-2 * (universalDegreeDeviation n v) ^ 2 /
            ∑ i, safeDegreeInfluence v i ^ 2)) +
        (∑ a : SameColorIndex n k,
          2 * Real.exp (-2 * (universalCodegreeDeviation n a) ^ 2 /
            ∑ i, safeCodegreeInfluence a i ^ 2)) +
        (∑ a : PairRoleIndex n,
          2 * Real.exp (-2 * (universalPairRoleDeviation n a) ^ 2 /
            ∑ i, safePairRoleInfluence (k := k) a i ^ 2)) < 1 := by
  obtain ⟨n₀, htail⟩ := eventually_universalTailBound_lt_one
  refine ⟨max n₀ 1, ?_⟩
  intro n k hn hk0 hk
  have hn0 : n₀ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (Nat.le_max_right _ _) hn
  exact (universal_union_tail_le hn1 hk0 hk).trans_lt (htail n hn0)


/-! ## Exact universal degree and codegree means -/

theorem weightedMean_eligible_filter_card {n k : ℕ} (q : ℝ)
    (S : Finset (TriangleBlock n k)) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ (((S.filter (Eligible (retainedOfBits bits))).card : ℕ) : ℝ)) =
      (S.card : ℝ) * q ^ 5 * (1 - q) := by
  classical
  have hpoint (bits : Fin (labelCount n k) → Bool) :
      (((S.filter (Eligible (retainedOfBits bits))).card : ℕ) : ℝ) =
        ∑ b ∈ S, eligibilityIndicator bits b := by
    rw [Finset.card_filter]
    push_cast
    simp [eligibilityIndicator]
  calc
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ (((S.filter (Eligible (retainedOfBits bits))).card : ℕ) : ℝ)) =
        ∑ b ∈ S,
          McDiarmid.weightedMean
            (McDiarmid.bernoulliWeight
              (retentionProbability (n := n) (k := k) q))
            (fun bits ↦ eligibilityIndicator bits b) := by
      simp only [McDiarmid.weightedMean, hpoint, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ _b ∈ S, q ^ 5 * (1 - q) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact weightedMean_eligibilityIndicator q b
    _ = (S.card : ℝ) * q ^ 5 * (1 - q) := by simp; ring

theorem cylinderMonomial_force_present {N : ℕ}
    (P A : Finset (Fin N)) (i : Fin N) (bits : Fin N → Bool)
    (hiP : i ∈ P) (hPA : Disjoint P A) :
    cylinderMonomial P A (Function.update bits i true) =
      cylinderMonomial (P.erase i) A bits := by
  classical
  unfold cylinderMonomial
  apply Finset.prod_congr rfl
  intro j hj
  by_cases hji : j = i
  · subst j
    have hiA : i ∉ A := Finset.disjoint_left.mp hPA hiP
    simp [hiP, hiA]
  · simp [hji]

theorem weightedMean_eligibilityIndicator_forceLabel {n k : ℕ} (q : ℝ)
    (b : TriangleBlock n k) (z : Fin n × Fin k)
    (hz : z ∈ b.positiveLabels) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ eligibilityIndicator (forceLabel z bits) b) =
      q ^ 4 * (1 - q) := by
  classical
  let i := (labelEquiv n k).symm z
  have hiP : i ∈ positiveCoordinates b := by
    simp [i, hz]
  have hPA := positiveCoordinates_disjoint_absentCoordinates b
  have hcard : ((positiveCoordinates b).erase i).card = 4 := by
    rw [Finset.card_erase_of_mem hiP, card_positiveCoordinates]
  have hdisj : Disjoint ((positiveCoordinates b).erase i) (absentCoordinates b) :=
    hPA.mono_left (Finset.erase_subset _ _)
  simp_rw [eligibilityIndicator_eq_cylinderMonomial]
  change McDiarmid.weightedMean
      (McDiarmid.bernoulliWeight (fun _ : Fin (labelCount n k) ↦ q))
      (fun bits ↦ cylinderMonomial (positiveCoordinates b) (absentCoordinates b)
        (Function.update bits i true)) = _
  simp_rw [cylinderMonomial_force_present _ _ i _ hiP hPA]
  rw [weightedMean_cylinderMonomial q _ _ hdisj, hcard, card_absentCoordinates]
  simp

theorem weightedMean_eligible_filter_card_forceLabel {n k : ℕ} (q : ℝ)
    (S : Finset (TriangleBlock n k)) (z : Fin n × Fin k)
    (hz : ∀ b ∈ S, z ∈ b.positiveLabels) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦
          (((S.filter (Eligible (retainedOfBits (forceLabel z bits)))).card : ℕ) : ℝ)) =
      (S.card : ℝ) * q ^ 4 * (1 - q) := by
  classical
  have hpoint (bits : Fin (labelCount n k) → Bool) :
      (((S.filter (Eligible (retainedOfBits (forceLabel z bits)))).card : ℕ) : ℝ) =
        ∑ b ∈ S, eligibilityIndicator (forceLabel z bits) b := by
    rw [Finset.card_filter]
    push_cast
    simp [eligibilityIndicator]
  calc
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦
          (((S.filter (Eligible (retainedOfBits (forceLabel z bits)))).card : ℕ) : ℝ)) =
        ∑ b ∈ S,
          McDiarmid.weightedMean
            (McDiarmid.bernoulliWeight
              (retentionProbability (n := n) (k := k) q))
            (fun bits ↦ eligibilityIndicator (forceLabel z bits) b) := by
      simp only [McDiarmid.weightedMean, hpoint, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ _b ∈ S, q ^ 4 * (1 - q) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact weightedMean_eligibilityIndicator_forceLabel q b z (hz b hb)
    _ = (S.card : ℝ) * q ^ 4 * (1 - q) := by simp; ring

theorem weightedMean_eligibilityIndicator_forceTwo {n k : ℕ} (q : ℝ)
    (b : TriangleBlock n k) (z w : Fin n × Fin k)
    (hz : z ∈ b.positiveLabels) (hw : w ∈ b.positiveLabels) (hzw : z ≠ w) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ eligibilityIndicator (forceLabel w (forceLabel z bits)) b) =
      q ^ 3 * (1 - q) := by
  classical
  let iz := (labelEquiv n k).symm z
  let iw := (labelEquiv n k).symm w
  have hizP : iz ∈ positiveCoordinates b := by simp [iz, hz]
  have hiwP : iw ∈ positiveCoordinates b := by simp [iw, hw]
  have hziw : iz ≠ iw := by
    intro h
    apply hzw
    simpa [iz, iw] using congrArg (labelEquiv n k) h
  have hizErase : iz ∈ (positiveCoordinates b).erase iw := by
    simp [hziw, hizP]
  have hPA := positiveCoordinates_disjoint_absentCoordinates b
  have hPA' : Disjoint ((positiveCoordinates b).erase iw) (absentCoordinates b) :=
    hPA.mono_left (Finset.erase_subset _ _)
  have hcard : (((positiveCoordinates b).erase iw).erase iz).card = 3 := by
    rw [Finset.card_erase_of_mem hizErase,
      Finset.card_erase_of_mem hiwP, card_positiveCoordinates]
  have hdisj : Disjoint (((positiveCoordinates b).erase iw).erase iz)
      (absentCoordinates b) :=
    hPA'.mono_left (Finset.erase_subset _ _)
  simp_rw [eligibilityIndicator_eq_cylinderMonomial]
  change McDiarmid.weightedMean
      (McDiarmid.bernoulliWeight (fun _ : Fin (labelCount n k) ↦ q))
      (fun bits ↦ cylinderMonomial (positiveCoordinates b) (absentCoordinates b)
        (Function.update (Function.update bits iz true) iw true)) = _
  simp_rw [cylinderMonomial_force_present _ _ iw _ hiwP hPA]
  simp_rw [cylinderMonomial_force_present _ _ iz _ hizErase hPA']
  rw [weightedMean_cylinderMonomial q _ _ hdisj, hcard, card_absentCoordinates]
  simp

theorem weightedMean_eligible_filter_card_forceTwo {n k : ℕ} (q : ℝ)
    (S : Finset (TriangleBlock n k)) (z w : Fin n × Fin k)
    (hzw : z ≠ w)
    (hz : ∀ b ∈ S, z ∈ b.positiveLabels)
    (hw : ∀ b ∈ S, w ∈ b.positiveLabels) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦
          (((S.filter (Eligible
            (retainedOfBits (forceLabel w (forceLabel z bits))))).card : ℕ) : ℝ)) =
      (S.card : ℝ) * q ^ 3 * (1 - q) := by
  classical
  have hpoint (bits : Fin (labelCount n k) → Bool) :
      (((S.filter (Eligible
          (retainedOfBits (forceLabel w (forceLabel z bits))))).card : ℕ) : ℝ) =
        ∑ b ∈ S, eligibilityIndicator (forceLabel w (forceLabel z bits)) b := by
    rw [Finset.card_filter]
    push_cast
    simp [eligibilityIndicator]
  calc
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦
          (((S.filter (Eligible
            (retainedOfBits (forceLabel w (forceLabel z bits))))).card : ℕ) : ℝ)) =
        ∑ b ∈ S,
          McDiarmid.weightedMean
            (McDiarmid.bernoulliWeight
              (retentionProbability (n := n) (k := k) q))
            (fun bits ↦ eligibilityIndicator (forceLabel w (forceLabel z bits)) b) := by
      simp only [McDiarmid.weightedMean, hpoint, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = ∑ _b ∈ S, q ^ 3 * (1 - q) := by
      apply Finset.sum_congr rfl
      intro b hb
      exact weightedMean_eligibilityIndicator_forceTwo q b z w (hz b hb) (hw b hb) hzw
    _ = (S.card : ℝ) * q ^ 3 * (1 - q) := by simp; ring

theorem weightedMean_const_bernoulli {n k : ℕ} (q c : ℝ) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun _bits : Fin (labelCount n k) → Bool ↦ c) = c := by
  rw [McDiarmid.weightedMean, ← Finset.sum_mul]
  rw [McDiarmid.sum_productMass_eq_one _ _
    (McDiarmid.bernoulliWeight_sum_one (retentionProbability q))]
  simp

theorem weightedMean_stabilizedDegree_graph_universal {n k : ℕ} (q : ℝ)
    (x y : Fin n) (hxy : x ≠ y) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ stabilizedDegreeStatistic (allTriangleBlocks n k)
          (universalDegreeTarget n k q) bits
          (Sum.inl s(x, y) : AuxVertex n k)) =
      universalGraphDegreeTarget n k q := by
  have hcard :
      (blocksThrough (Sum.inl s(x, y) : AuxVertex n k)).card =
        3 * (n - 2) * k * (k - 1) :=
    card_universal_graph_incident_blocks x y hxy
  simp only [stabilizedDegreeStatistic, Sym2.mk_isDiag_iff, hxy, ↓reduceIte,
    auxDegreeStatistic]
  simp_rw [degree_auxiliary_eq_blocks]
  rw [weightedMean_eligible_filter_card, hcard]
  rfl

theorem weightedMean_stabilizedDegree_label_universal {n k : ℕ} (q : ℝ)
    (x : Fin n) (c : Fin k) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ stabilizedDegreeStatistic (allTriangleBlocks n k)
          (universalDegreeTarget n k q) bits
          (Sum.inr (x, c) : AuxVertex n k)) =
      universalLabelDegreeTarget n k q := by
  let z : Fin n × Fin k := (x, c)
  have hz (b : TriangleBlock n k)
      (hb : b ∈ blocksThrough (Sum.inr z : AuxVertex n k)) :
      z ∈ b.positiveLabels := by
    have hb' := (Finset.mem_filter.mp hb).2
    simpa [TriangleBlock.auxSupport] using hb'
  have hcard :
      (blocksThrough (Sum.inr z : AuxVertex n k)).card =
        5 * (n - 1).choose 2 * (k - 1) := by
    simpa [z, blocksThrough, TriangleBlock.auxSupport] using
      card_universal_label_incident_blocks x c
  simp only [stabilizedDegreeStatistic, auxDegreeStatistic]
  simp_rw [degree_auxiliary_eq_blocks]
  rw [weightedMean_eligible_filter_card_forceLabel q _ z hz, hcard]
  rfl

theorem weightedMean_stabilizedSameColor_universal_of_ne {n k : ℕ} (q : ℝ)
    (a : SameColorIndex n k) (haa : a.left ≠ a.right) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ stabilizedSameColorStatistic (allTriangleBlocks n k)
          (universalSameColorTarget n k q) bits a) =
      (4 * (n - 2) * (k - 1) : ℕ) * q ^ 3 * (1 - q) := by
  let z : Fin n × Fin k := (a.left, a.color)
  let w : Fin n × Fin k := (a.right, a.color)
  have hzw : z ≠ w := by
    intro h
    apply haa
    exact congrArg Prod.fst h
  have hz (b : TriangleBlock n k) (hb : b ∈ blocksThroughPair a) :
      z ∈ b.positiveLabels := by
    have hb' := (Finset.mem_filter.mp hb).2.1
    simpa [TriangleBlock.auxSupport, z] using hb'
  have hw (b : TriangleBlock n k) (hb : b ∈ blocksThroughPair a) :
      w ∈ b.positiveLabels := by
    have hb' := (Finset.mem_filter.mp hb).2.2
    simpa [TriangleBlock.auxSupport, w] using hb'
  have hcard : (blocksThroughPair a).card =
      4 * (n - 2) * (k - 1) := by
    simpa [blocksThroughPair, TriangleBlock.auxSupport] using
      card_universal_sameColor_incident_blocks a.left a.right a.color haa
  simp only [stabilizedSameColorStatistic, haa, ↓reduceIte,
    sameColorCodegreeStatistic, forceSameColorRoots]
  simp_rw [codegree_auxiliary_eq_blocks]
  rw [weightedMean_eligible_filter_card_forceTwo q _ z w hzw hz hw, hcard]

theorem weightedMean_stabilizedDegree_universal {n k : ℕ} (q : ℝ)
    (v : AuxVertex n k) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ stabilizedDegreeStatistic (allTriangleBlocks n k)
          (universalDegreeTarget n k q) bits v) =
      universalDegreeTarget n k q v := by
  rcases v with e | z
  · induction e using Sym2.inductionOn with
    | _ x y =>
      by_cases hxy : x = y
      · subst y
        simpa [stabilizedDegreeStatistic, universalDegreeTarget,
          Sym2.mk_isDiag_iff] using
            (weightedMean_const_bernoulli (n := n) (k := k) q 0)
      · simpa [universalDegreeTarget, Sym2.mk_isDiag_iff, hxy] using
          weightedMean_stabilizedDegree_graph_universal q x y hxy
  · rcases z with ⟨x, c⟩
    simpa [universalDegreeTarget] using
      weightedMean_stabilizedDegree_label_universal q x c

theorem weightedMean_stabilizedSameColor_universal {n k : ℕ} (q : ℝ)
    (a : SameColorIndex n k) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ stabilizedSameColorStatistic (allTriangleBlocks n k)
          (universalSameColorTarget n k q) bits a) =
      universalSameColorTarget n k q a := by
  by_cases haa : a.left = a.right
  · simp only [stabilizedSameColorStatistic, haa, ↓reduceIte]
    exact weightedMean_const_bernoulli q (universalSameColorTarget n k q a)
  · rw [universalSameColorTarget, if_neg haa]
    exact weightedMean_stabilizedSameColor_universal_of_ne q a haa

/-! ## Simultaneous finite extraction -/

/-- If the total weighted mass of three finite families of bad events is
strictly below one, some outcome avoids every bad event. -/
theorem exists_avoiding_three_families
    {N : ℕ} {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J] [DecidableEq K]
    (w : Fin N → Bool → ℝ)
    (hw0 : ∀ i b, 0 ≤ w i b) (hw1 : ∀ i, ∑ b, w i b = 1)
    (A : I → Set (Fin N → Bool))
    (B : J → Set (Fin N → Bool))
    (C : K → Set (Fin N → Bool))
    (hbudget :
      (∑ i, McDiarmid.eventMass w (A i)) +
        (∑ j, McDiarmid.eventMass w (B j)) +
          (∑ k, McDiarmid.eventMass w (C k)) < 1) :
    ∃ bits,
      (∀ i, bits ∉ A i) ∧ (∀ j, bits ∉ B j) ∧ (∀ k, bits ∉ C k) := by
  classical
  let UA : Set (Fin N → Bool) := ⋃ i ∈ (Finset.univ : Finset I), A i
  let UB : Set (Fin N → Bool) := ⋃ j ∈ (Finset.univ : Finset J), B j
  let UC : Set (Fin N → Bool) := ⋃ k ∈ (Finset.univ : Finset K), C k
  let U := UA ∪ UB ∪ UC
  have hmassA : McDiarmid.eventMass w UA ≤
      ∑ i, McDiarmid.eventMass w (A i) := by
    simpa [UA] using McDiarmid.eventMass_biUnion_le_sum w hw0
      (Finset.univ : Finset I) A
  have hmassB : McDiarmid.eventMass w UB ≤
      ∑ j, McDiarmid.eventMass w (B j) := by
    simpa [UB] using McDiarmid.eventMass_biUnion_le_sum w hw0
      (Finset.univ : Finset J) B
  have hmassC : McDiarmid.eventMass w UC ≤
      ∑ k, McDiarmid.eventMass w (C k) := by
    simpa [UC] using McDiarmid.eventMass_biUnion_le_sum w hw0
      (Finset.univ : Finset K) C
  have hmass : McDiarmid.eventMass w U < 1 := by
    calc
      McDiarmid.eventMass w U
          ≤ McDiarmid.eventMass w UA + McDiarmid.eventMass w UB +
              McDiarmid.eventMass w UC := by
            dsimp [U]
            exact (McDiarmid.eventMass_union_le w hw0 (UA ∪ UB) UC).trans
              (add_le_add
                (McDiarmid.eventMass_union_le w hw0 UA UB) (le_refl _))
      _ ≤ (∑ i, McDiarmid.eventMass w (A i)) +
              (∑ j, McDiarmid.eventMass w (B j)) +
                (∑ k, McDiarmid.eventMass w (C k)) := by
            gcongr
      _ < 1 := hbudget
  have hnotuniv : U ≠ Set.univ := by
    intro hU
    have hone := McDiarmid.eventMass_univ w hw1
    rw [hU, hone] at hmass
    exact (lt_irrefl (1 : ℝ)) hmass
  have hex : ∃ bits, bits ∉ U := by
    by_contra h
    apply hnotuniv
    apply Set.eq_univ_of_forall
    intro bits
    by_contra hbits
    exact h ⟨bits, hbits⟩
  obtain ⟨bits, hbits⟩ := hex
  refine ⟨bits, ?_, ?_, ?_⟩
  · intro i hi
    apply hbits
    apply Or.inl
    apply Or.inl
    exact Set.mem_iUnion_of_mem i
      (Set.mem_iUnion_of_mem (Finset.mem_univ i) hi)
  · intro j hj
    apply hbits
    apply Or.inl
    apply Or.inr
    exact Set.mem_iUnion_of_mem j
      (Set.mem_iUnion_of_mem (Finset.mem_univ j) hj)
  · intro k hk
    apply hbits
    apply Or.inr
    exact Set.mem_iUnion_of_mem k
      (Set.mem_iUnion_of_mem (Finset.mem_univ k) hk)

/-- Simultaneous biased-retention concentration for all auxiliary degrees,
all same-colour label codegrees, and all geometric pair-test cardinalities.

The three bounded-difference arrays are allowed to depend on the statistic
being controlled.  The last hypothesis is the exact union-bound inequality
obtained by summing the McDiarmid tails over the finite index types.  Mean
errors are separated from random deviations, which is the form needed after
the elementary expectation calculations in the auxiliary construction. -/
theorem exists_retainedLabels_with_estimates {n k : ℕ}
    (candidates : Finset (TriangleBlock n k))
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (degreeTarget degreeMeanError degreeDeviation : AuxVertex n k → ℝ)
    (codegreeTarget codegreeMeanError codegreeDeviation :
      SameColorIndex n k → ℝ)
    (pairTarget pairMeanError pairDeviation : PairRoleIndex n → ℝ)
    (degreeInfluence : AuxVertex n k → Fin (labelCount n k) → ℝ)
    (codegreeInfluence : SameColorIndex n k → Fin (labelCount n k) → ℝ)
    (pairInfluence : PairRoleIndex n → Fin (labelCount n k) → ℝ)
    (hdegreeMean : ∀ v,
      |McDiarmid.weightedMean
          (McDiarmid.bernoulliWeight (retentionProbability q))
          (fun bits ↦ stabilizedDegreeStatistic candidates degreeTarget bits v) -
        degreeTarget v| ≤ degreeMeanError v)
    (hcodegreeMean : ∀ a,
      |McDiarmid.weightedMean
          (McDiarmid.bernoulliWeight (retentionProbability q))
          (fun bits ↦
            stabilizedSameColorStatistic candidates codegreeTarget bits a) -
        codegreeTarget a| ≤ codegreeMeanError a)
    (hpairMean : ∀ a,
      |McDiarmid.weightedMean
          (McDiarmid.bernoulliWeight (retentionProbability q))
          (fun bits ↦ stabilizedPairRoleStatistic candidates pairTarget bits a) -
        pairTarget a| ≤
        pairMeanError a)
    (hdegreeInfluence0 : ∀ v i, 0 ≤ degreeInfluence v i)
    (hcodegreeInfluence0 : ∀ a i, 0 ≤ codegreeInfluence a i)
    (hpairInfluence0 : ∀ a i, 0 ≤ pairInfluence a i)
    (hdegreeBD : ∀ v i (x y : Fin (labelCount n k) → Bool),
      (∀ j, j ≠ i → x j = y j) →
      |stabilizedDegreeStatistic candidates degreeTarget x v -
        stabilizedDegreeStatistic candidates degreeTarget y v| ≤
          degreeInfluence v i)
    (hcodegreeBD : ∀ a i (x y : Fin (labelCount n k) → Bool),
      (∀ j, j ≠ i → x j = y j) →
      |stabilizedSameColorStatistic candidates codegreeTarget x a -
        stabilizedSameColorStatistic candidates codegreeTarget y a| ≤
          codegreeInfluence a i)
    (hpairBD : ∀ a i (x y : Fin (labelCount n k) → Bool),
      (∀ j, j ≠ i → x j = y j) →
      |stabilizedPairRoleStatistic candidates pairTarget x a -
        stabilizedPairRoleStatistic candidates pairTarget y a| ≤
          pairInfluence a i)
    (hdegreeDeviation0 : ∀ v, 0 ≤ degreeDeviation v)
    (hcodegreeDeviation0 : ∀ a, 0 ≤ codegreeDeviation a)
    (hpairDeviation0 : ∀ a, 0 ≤ pairDeviation a)
    (hbudget :
      (∑ v : AuxVertex n k,
          2 * Real.exp (-2 * degreeDeviation v ^ 2 /
            ∑ i, degreeInfluence v i ^ 2)) +
        (∑ a : SameColorIndex n k,
          2 * Real.exp (-2 * codegreeDeviation a ^ 2 /
            ∑ i, codegreeInfluence a i ^ 2)) +
        (∑ a : PairRoleIndex n,
          2 * Real.exp (-2 * pairDeviation a ^ 2 /
            ∑ i, pairInfluence a i ^ 2)) < 1) :
    ∃ R : RetainedLabels n k,
      DegreesNear candidates R degreeTarget
          (fun v ↦ degreeDeviation v + degreeMeanError v) ∧
      SameColorCodegreesNear candidates R codegreeTarget
          (fun a ↦ codegreeDeviation a + codegreeMeanError a) ∧
      PairRoleWitnessesNear candidates R pairTarget
          (fun a ↦ pairDeviation a + pairMeanError a) := by
  classical
  let p : Fin (labelCount n k) → ℝ := retentionProbability q
  let w := McDiarmid.bernoulliWeight p
  let degreeBad : AuxVertex n k → Set (Fin (labelCount n k) → Bool) :=
    fun v ↦ {bits | degreeDeviation v ≤
      |stabilizedDegreeStatistic candidates degreeTarget bits v -
        McDiarmid.weightedMean w
          (fun z ↦ stabilizedDegreeStatistic candidates degreeTarget z v)|}
  let codegreeBad : SameColorIndex n k →
      Set (Fin (labelCount n k) → Bool) :=
    fun a ↦ {bits | codegreeDeviation a ≤
      |stabilizedSameColorStatistic candidates codegreeTarget bits a -
        McDiarmid.weightedMean w
          (fun z ↦ stabilizedSameColorStatistic candidates codegreeTarget z a)|}
  let pairBad : PairRoleIndex n → Set (Fin (labelCount n k) → Bool) :=
    fun a ↦ {bits | pairDeviation a ≤
      |stabilizedPairRoleStatistic candidates pairTarget bits a -
        McDiarmid.weightedMean w
          (fun z ↦ stabilizedPairRoleStatistic candidates pairTarget z a)|}
  have hp : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1 := fun _ ↦ hq
  have hw0 : ∀ i b, 0 ≤ w i b := McDiarmid.bernoulliWeight_nonneg p hp
  have hw1 : ∀ i, ∑ b, w i b = 1 := McDiarmid.bernoulliWeight_sum_one p
  have hdegreeTail (v : AuxVertex n k) :
      McDiarmid.eventMass w (degreeBad v) ≤
        2 * Real.exp (-2 * degreeDeviation v ^ 2 /
          ∑ i, degreeInfluence v i ^ 2) := by
    simpa [degreeBad, w] using
      McDiarmid.bernoulli_mcdiarmid_two_sided (labelCount n k) p
        (fun bits ↦ stabilizedDegreeStatistic candidates degreeTarget bits v)
        (degreeInfluence v) hp (hdegreeInfluence0 v) (hdegreeBD v)
        (degreeDeviation v) (hdegreeDeviation0 v)
  have hcodegreeTail (a : SameColorIndex n k) :
      McDiarmid.eventMass w (codegreeBad a) ≤
        2 * Real.exp (-2 * codegreeDeviation a ^ 2 /
          ∑ i, codegreeInfluence a i ^ 2) := by
    simpa [codegreeBad, w] using
      McDiarmid.bernoulli_mcdiarmid_two_sided (labelCount n k) p
        (fun bits ↦
          stabilizedSameColorStatistic candidates codegreeTarget bits a)
        (codegreeInfluence a) hp (hcodegreeInfluence0 a) (hcodegreeBD a)
        (codegreeDeviation a) (hcodegreeDeviation0 a)
  have hpairTail (a : PairRoleIndex n) :
      McDiarmid.eventMass w (pairBad a) ≤
        2 * Real.exp (-2 * pairDeviation a ^ 2 /
          ∑ i, pairInfluence a i ^ 2) := by
    simpa [pairBad, w] using
      McDiarmid.bernoulli_mcdiarmid_two_sided (labelCount n k) p
        (fun bits ↦ stabilizedPairRoleStatistic candidates pairTarget bits a)
        (pairInfluence a) hp (hpairInfluence0 a) (hpairBD a)
        (pairDeviation a) (hpairDeviation0 a)
  have hmassBudget :
      (∑ v, McDiarmid.eventMass w (degreeBad v)) +
        (∑ a, McDiarmid.eventMass w (codegreeBad a)) +
          (∑ a, McDiarmid.eventMass w (pairBad a)) < 1 := by
    calc
      (∑ v, McDiarmid.eventMass w (degreeBad v)) +
          (∑ a, McDiarmid.eventMass w (codegreeBad a)) +
            (∑ a, McDiarmid.eventMass w (pairBad a))
          ≤ (∑ v : AuxVertex n k,
                2 * Real.exp (-2 * degreeDeviation v ^ 2 /
                  ∑ i, degreeInfluence v i ^ 2)) +
              (∑ a : SameColorIndex n k,
                2 * Real.exp (-2 * codegreeDeviation a ^ 2 /
                  ∑ i, codegreeInfluence a i ^ 2)) +
              (∑ a : PairRoleIndex n,
                2 * Real.exp (-2 * pairDeviation a ^ 2 /
                  ∑ i, pairInfluence a i ^ 2)) := by
            apply add_le_add
            · apply add_le_add
              · exact Finset.sum_le_sum fun v _ ↦ hdegreeTail v
              · exact Finset.sum_le_sum fun a _ ↦ hcodegreeTail a
            · exact Finset.sum_le_sum fun a _ ↦ hpairTail a
      _ < 1 := hbudget
  obtain ⟨bits, hdegreeGood, hcodegreeGood, hpairGood⟩ :=
    exists_avoiding_three_families w hw0 hw1 degreeBad codegreeBad pairBad hmassBudget
  refine ⟨retainedOfBits bits, ?_, ?_, ?_⟩
  · intro v hv
    have hdev :
        |stabilizedDegreeStatistic candidates degreeTarget bits v -
          McDiarmid.weightedMean w
            (fun z ↦ stabilizedDegreeStatistic candidates degreeTarget z v)| <
          degreeDeviation v := by
      exact lt_of_not_ge (hdegreeGood v)
    have hstab : stabilizedDegreeStatistic candidates degreeTarget bits v =
        auxDegreeStatistic candidates bits v := by
      cases v with
      | inl e =>
          simp only [ActiveAuxVertex] at hv
          simp [stabilizedDegreeStatistic, hv]
      | inr z =>
          simp only [ActiveAuxVertex] at hv
          simp [stabilizedDegreeStatistic, forceLabel_eq_of_retained hv]
    rw [hstab] at hdev
    change |auxDegreeStatistic candidates bits v - degreeTarget v| <
      degreeDeviation v + degreeMeanError v
    calc
      |auxDegreeStatistic candidates bits v - degreeTarget v|
          = |(auxDegreeStatistic candidates bits v -
                McDiarmid.weightedMean w
                  (fun z ↦ stabilizedDegreeStatistic candidates degreeTarget z v)) +
              (McDiarmid.weightedMean w
                  (fun z ↦ stabilizedDegreeStatistic candidates degreeTarget z v) -
                degreeTarget v)| := by congr 1 <;> ring
      _
          ≤ |auxDegreeStatistic candidates bits v -
                McDiarmid.weightedMean w
                  (fun z ↦ stabilizedDegreeStatistic candidates degreeTarget z v)| +
              |McDiarmid.weightedMean w
                  (fun z ↦ stabilizedDegreeStatistic candidates degreeTarget z v) -
                degreeTarget v| :=
            abs_add_le _ _
      _ < degreeDeviation v + degreeMeanError v :=
        add_lt_add_of_lt_of_le hdev (hdegreeMean v)
  · intro a hne hleft hright
    have hdev :
        |stabilizedSameColorStatistic candidates codegreeTarget bits a -
          McDiarmid.weightedMean w
            (fun z ↦ stabilizedSameColorStatistic candidates codegreeTarget z a)| <
          codegreeDeviation a := by
      exact lt_of_not_ge (hcodegreeGood a)
    have hstab : stabilizedSameColorStatistic candidates codegreeTarget bits a =
        sameColorCodegreeStatistic candidates bits a := by
      simp [stabilizedSameColorStatistic, hne,
        forceSameColorRoots_eq_of_retained hleft hright]
    rw [hstab] at hdev
    change |sameColorCodegreeStatistic candidates bits a - codegreeTarget a| <
      codegreeDeviation a + codegreeMeanError a
    calc
      |sameColorCodegreeStatistic candidates bits a - codegreeTarget a|
          = |(sameColorCodegreeStatistic candidates bits a -
                McDiarmid.weightedMean w
                  (fun z ↦ stabilizedSameColorStatistic candidates codegreeTarget z a)) +
              (McDiarmid.weightedMean w
                  (fun z ↦ stabilizedSameColorStatistic candidates codegreeTarget z a) -
                codegreeTarget a)| := by congr 1 <;> ring
      _
          ≤ |sameColorCodegreeStatistic candidates bits a -
                McDiarmid.weightedMean w
                  (fun z ↦ stabilizedSameColorStatistic candidates codegreeTarget z a)| +
              |McDiarmid.weightedMean w
                  (fun z ↦ stabilizedSameColorStatistic candidates codegreeTarget z a) -
                codegreeTarget a| :=
            abs_add_le _ _
      _ < codegreeDeviation a + codegreeMeanError a :=
        add_lt_add_of_lt_of_le hdev (hcodegreeMean a)
  · intro a hxy
    have hdev :
        |stabilizedPairRoleStatistic candidates pairTarget bits a -
          McDiarmid.weightedMean w
            (fun z ↦ stabilizedPairRoleStatistic candidates pairTarget z a)| <
          pairDeviation a := by
      exact lt_of_not_ge (hpairGood a)
    have hstab : stabilizedPairRoleStatistic candidates pairTarget bits a =
        pairRoleWitnessStatistic candidates bits a := by
      simp [stabilizedPairRoleStatistic, hxy]
    rw [hstab] at hdev
    change |pairRoleWitnessStatistic candidates bits a - pairTarget a| <
      pairDeviation a + pairMeanError a
    calc
      |pairRoleWitnessStatistic candidates bits a - pairTarget a|
          = |(pairRoleWitnessStatistic candidates bits a -
                McDiarmid.weightedMean w
                  (fun z ↦ stabilizedPairRoleStatistic candidates pairTarget z a)) +
              (McDiarmid.weightedMean w
                  (fun z ↦ stabilizedPairRoleStatistic candidates pairTarget z a) -
                pairTarget a)| := by
                congr 1 <;> ring
      _
          ≤ |pairRoleWitnessStatistic candidates bits a -
                McDiarmid.weightedMean w
                  (fun z ↦ stabilizedPairRoleStatistic candidates pairTarget z a)| +
              |McDiarmid.weightedMean w
                  (fun z ↦ stabilizedPairRoleStatistic candidates pairTarget z a) -
                pairTarget a| :=
            abs_add_le _ _
      _ < pairDeviation a + pairMeanError a :=
        add_lt_add_of_lt_of_le hdev (hpairMean a)

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

def pairPositiveCoordinates {n k : ℕ} (w : PairWitness n k) :
    Finset (Fin (labelCount n k)) :=
  w.positiveLabels.image (labelEquiv n k).symm

def pairNegativeCoordinates {n k : ℕ} (w : PairWitness n k) :
    Finset (Fin (labelCount n k)) :=
  w.negativeLabels.image (labelEquiv n k).symm

@[simp] theorem mem_pairPositiveCoordinates_iff {n k : ℕ}
    (w : PairWitness n k) (i : Fin (labelCount n k)) :
    i ∈ pairPositiveCoordinates w ↔ labelEquiv n k i ∈ w.positiveLabels := by
  classical
  constructor
  · intro hi
    obtain ⟨z, hz, hzi⟩ := Finset.mem_image.mp hi
    simpa only [← hzi, Equiv.apply_symm_apply] using hz
  · intro hi
    exact Finset.mem_image.mpr
      ⟨labelEquiv n k i, hi, (labelEquiv n k).symm_apply_apply i⟩

@[simp] theorem mem_pairNegativeCoordinates_iff {n k : ℕ}
    (w : PairWitness n k) (i : Fin (labelCount n k)) :
    i ∈ pairNegativeCoordinates w ↔ labelEquiv n k i ∈ w.negativeLabels := by
  classical
  constructor
  · intro hi
    obtain ⟨z, hz, hzi⟩ := Finset.mem_image.mp hi
    simpa only [← hzi, Equiv.apply_symm_apply] using hz
  · intro hi
    exact Finset.mem_image.mpr
      ⟨labelEquiv n k i, hi, (labelEquiv n k).symm_apply_apply i⟩

@[simp] theorem card_pairPositiveCoordinates {n k : ℕ} (w : PairWitness n k) :
    (pairPositiveCoordinates w).card = w.positiveLabels.card := by
  classical
  exact Finset.card_image_of_injective _ (labelEquiv n k).symm.injective

@[simp] theorem card_pairNegativeCoordinates {n k : ℕ} (w : PairWitness n k) :
    (pairNegativeCoordinates w).card = w.negativeLabels.card := by
  classical
  exact Finset.card_image_of_injective _ (labelEquiv n k).symm.injective

def pairRetentionIndicator {n k : ℕ}
    (bits : Fin (labelCount n k) → Bool) (w : PairWitness n k) : ℝ :=
  if w.RetentionValid (retainedOfBits bits) then 1 else 0

theorem pairRetentionIndicator_eq_cylinderMonomial {n k : ℕ}
    (bits : Fin (labelCount n k) → Bool) (w : PairWitness n k)
    (hdisj : Disjoint w.positiveLabels w.negativeLabels) :
    pairRetentionIndicator bits w =
      cylinderMonomial (pairPositiveCoordinates w) (pairNegativeCoordinates w) bits := by
  classical
  by_cases hV : w.RetentionValid (retainedOfBits bits)
  · rw [pairRetentionIndicator, if_pos hV]
    symm
    apply Finset.prod_eq_one
    intro i hi
    by_cases hiP : i ∈ pairPositiveCoordinates w
    · have hret : labelEquiv n k i ∈ retainedOfBits bits :=
        hV.1 ((mem_pairPositiveCoordinates_iff w i).mp hiP)
      have hbit : bits i = true := by
        simpa using (mem_retainedOfBits bits (labelEquiv n k i)).mp hret
      simp [cylinderMonomial, hiP, hbit]
    · by_cases hiA : i ∈ pairNegativeCoordinates w
      · have hneg : labelEquiv n k i ∈ w.negativeLabels :=
          (mem_pairNegativeCoordinates_iff w i).mp hiA
        have hnot : labelEquiv n k i ∉ retainedOfBits bits := by
          exact Finset.disjoint_left.mp hV.2 hneg
        have hbit : bits i = false := by
          cases hbi : bits i with
          | false => rfl
          | true =>
              exfalso
              apply hnot
              exact (mem_retainedOfBits bits (labelEquiv n k i)).mpr (by
                simpa using hbi)
        simp [cylinderMonomial, hiP, hiA, hbit]
      · simp [cylinderMonomial, hiP, hiA]
  · rw [pairRetentionIndicator, if_neg hV]
    by_cases hP : w.positiveLabels ⊆ retainedOfBits bits
    · have hND : ¬Disjoint w.negativeLabels (retainedOfBits bits) := by
        intro hD
        exact hV ⟨hP, hD⟩
      rw [Finset.not_disjoint_iff] at hND
      obtain ⟨z, hzN, hzR⟩ := hND
      let i := (labelEquiv n k).symm z
      symm
      unfold cylinderMonomial
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      have hiA : i ∈ pairNegativeCoordinates w := by simp [i, hzN]
      have hbit : bits i = true := by
        simpa [i] using (mem_retainedOfBits bits z).mp hzR
      by_cases hiP : i ∈ pairPositiveCoordinates w
      · have hzP : z ∈ w.positiveLabels := by simpa [i] using hiP
        exact (Finset.disjoint_left.mp hdisj hzP hzN).elim
      · simp [hiP, hiA, hbit]
    · obtain ⟨z, hzP, hznot⟩ := Finset.not_subset.mp hP
      let i := (labelEquiv n k).symm z
      symm
      unfold cylinderMonomial
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      have hiP : i ∈ pairPositiveCoordinates w := by simp [i, hzP]
      have hbit : bits i = false := by
        cases hbi : bits i with
        | false => rfl
        | true =>
            exfalso
            apply hznot
            exact (mem_retainedOfBits bits z).mpr (by simpa [i] using hbi)
      simp [hiP, hbit]

theorem weightedMean_pairRetentionIndicator {n k : ℕ} (q : ℝ)
    (w : PairWitness n k)
    (hdisj : Disjoint w.positiveLabels w.negativeLabels) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ pairRetentionIndicator bits w) =
      q ^ w.positiveLabels.card * (1 - q) ^ w.negativeLabels.card := by
  have hcoord : Disjoint (pairPositiveCoordinates w) (pairNegativeCoordinates w) := by
    rw [Finset.disjoint_left]
    intro i hiP hiN
    exact Finset.disjoint_left.mp hdisj
      ((mem_pairPositiveCoordinates_iff w i).mp hiP)
      ((mem_pairNegativeCoordinates_iff w i).mp hiN)
  change McDiarmid.weightedMean
      (McDiarmid.bernoulliWeight (fun _ : Fin (labelCount n k) ↦ q))
      (fun bits ↦ pairRetentionIndicator bits w) = _
  simp_rw [pairRetentionIndicator_eq_cylinderMonomial _ _ hdisj]
  rw [weightedMean_cylinderMonomial q _ _ hcoord,
    card_pairPositiveCoordinates, card_pairNegativeCoordinates]

theorem pairWitness_positiveLabels_card_of_geometry {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {a : PairTestIndex n}
    {w : PairWitness n k} (hw : w.Geometry candidates a) :
    w.positiveLabels.card = 10 := by
  have hpos : Disjoint w.leftBlock.positiveLabels w.rightBlock.positiveLabels := by
    rw [Finset.disjoint_left]
    intro z hzL hzR
    exact Finset.disjoint_left.mp hw.2.2.2.2.1
      (show (Sum.inr z : AuxVertex n k) ∈ w.leftBlock.auxSupport by
        simp [TriangleBlock.auxSupport, hzL])
      (show (Sum.inr z : AuxVertex n k) ∈ w.rightBlock.auxSupport by
        simp [TriangleBlock.auxSupport, hzR])
  rw [PairWitness.positiveLabels, Finset.card_union_of_disjoint hpos,
    w.leftBlock.positiveLabels_card, w.rightBlock.positiveLabels_card]

theorem weightedMean_pairRetentionIndicator_of_geometry {n k : ℕ} (q : ℝ)
    {candidates : Finset (TriangleBlock n k)} {a : PairTestIndex n}
    (w : PairWitness n k) (hw : w.Geometry candidates a)
    (hdisj : Disjoint w.positiveLabels w.negativeLabels) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ pairRetentionIndicator bits w) =
      q ^ 10 * (1 - q) ^ w.negativeLabels.card := by
  rw [weightedMean_pairRetentionIndicator q w hdisj,
    pairWitness_positiveLabels_card_of_geometry hw]

theorem pairRetentionIndicator_eq_zero_of_not_disjoint {n k : ℕ}
    (bits : Fin (labelCount n k) → Bool) (w : PairWitness n k)
    (hnd : ¬Disjoint w.positiveLabels w.negativeLabels) :
    pairRetentionIndicator bits w = 0 := by
  rw [pairRetentionIndicator]
  split_ifs with hV
  · exfalso
    apply hnd
    rw [Finset.disjoint_left]
    intro z hzP hzN
    exact Finset.disjoint_left.mp hV.2 hzN (hV.1 hzP)
  · rfl

theorem weightedMean_pairRetentionIndicator_eq_zero_of_not_disjoint {n k : ℕ}
    (q : ℝ) (w : PairWitness n k)
    (hnd : ¬Disjoint w.positiveLabels w.negativeLabels) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ pairRetentionIndicator bits w) = 0 := by
  simp_rw [pairRetentionIndicator_eq_zero_of_not_disjoint _ w hnd]
  simp [McDiarmid.weightedMean]

theorem weightedMean_pairRoleWitnessStatistic_as_sum {n k : ℕ} (q : ℝ)
    (a : PairRoleIndex n) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ pairRoleWitnessStatistic (allTriangleBlocks n k) bits a) =
      ∑ w ∈ geometricRoleWitnesses (allTriangleBlocks n k) a,
        McDiarmid.weightedMean
          (McDiarmid.bernoulliWeight
            (retentionProbability (n := n) (k := k) q))
          (fun bits ↦ pairRetentionIndicator bits w) := by
  classical
  have hpoint (bits : Fin (labelCount n k) → Bool) :
      pairRoleWitnessStatistic (allTriangleBlocks n k) bits a =
        ∑ w ∈ geometricRoleWitnesses (allTriangleBlocks n k) a,
          pairRetentionIndicator bits w := by
    rw [pairRoleWitnessStatistic, pairRoleWitnesses, Finset.card_filter]
    push_cast
    simp [pairRetentionIndicator]
  simp only [McDiarmid.weightedMean, hpoint, Finset.mul_sum]
  rw [Finset.sum_comm]

def blockVertices {n k : ℕ} (b : TriangleBlock n k) : Finset (Fin n) :=
  {b.apex, b.left, b.right}

theorem roleFits_common_positive_or_singleton_apex {n k : ℕ}
    (r : RootRole) (b : TriangleBlock n k) (root z : Fin n) (c : Fin k)
    (hfit : RoleFits r b root c) (hz : z ∈ blockVertices b) :
    (z, c) ∈ b.positiveLabels ∨ (r = .singletonLeaf ∧ z = b.apex) := by
  cases r with
  | repeatedApex =>
      left
      simp only [RoleFits] at hfit
      rcases hfit with ⟨rfl, rfl⟩
      simp [blockVertices, TriangleBlock.positiveLabels] at hz ⊢
      aesop
  | repeatedLeaf =>
      left
      simp only [RoleFits] at hfit
      rcases hfit with ⟨rfl, hroot⟩
      simp [blockVertices, TriangleBlock.positiveLabels] at hz ⊢
      aesop
  | singletonLeaf =>
      simp only [RoleFits] at hfit
      rcases hfit with ⟨rfl, hroot⟩
      simp [blockVertices, TriangleBlock.positiveLabels] at hz ⊢
      aesop

theorem compatible_geometry_vertexDisjoint_or_sharedSingletonApex {n k : ℕ}
    {candidates : Finset (TriangleBlock n k)} {a : PairTestIndex n}
    (w : PairWitness n k) (hw : w.Geometry candidates a)
    (hcompat : Disjoint w.positiveLabels w.negativeLabels) :
    Disjoint (blockVertices w.leftBlock) (blockVertices w.rightBlock) ∨
      (w.leftRole = .singletonLeaf ∧ w.rightRole = .singletonLeaf ∧
        w.leftBlock.apex = w.rightBlock.apex) := by
  classical
  by_cases hvertex : Disjoint (blockVertices w.leftBlock) (blockVertices w.rightBlock)
  · exact Or.inl hvertex
  · right
    rw [Finset.not_disjoint_iff] at hvertex
    obtain ⟨z, hzL, hzR⟩ := hvertex
    have hfitL : RoleFits w.leftRole w.leftBlock a.x w.common :=
      hw.2.2.2.2.2.2.2.1
    have hfitR : RoleFits w.rightRole w.rightBlock a.y w.common :=
      hw.2.2.2.2.2.2.2.2
    have hdL := roleFits_common_positive_or_singleton_apex
      w.leftRole w.leftBlock a.x z w.common hfitL hzL
    have hdR := roleFits_common_positive_or_singleton_apex
      w.rightRole w.rightBlock a.y z w.common hfitR hzR
    rcases hdL with hposL | ⟨hroleL, hapexL⟩
    · rcases hdR with hposR | ⟨hroleR, hapexR⟩
      · exfalso
        exact Finset.disjoint_left.mp hw.2.2.2.2.1
          (show (Sum.inr (z, w.common) : AuxVertex n k) ∈
              w.leftBlock.auxSupport by
            simp [TriangleBlock.auxSupport, hposL])
          (show (Sum.inr (z, w.common) : AuxVertex n k) ∈
              w.rightBlock.auxSupport by
            simp [TriangleBlock.auxSupport, hposR])
      · exfalso
        have hfitR' : w.rightBlock.singleton = w.common ∧
            (w.rightBlock.left = a.y ∨ w.rightBlock.right = a.y) := by
          simpa [hroleR, RoleFits] using hfitR
        exact Finset.disjoint_left.mp hcompat
          (show (z, w.common) ∈ w.positiveLabels by
            simp [PairWitness.positiveLabels, hposL])
          (show (z, w.common) ∈ w.negativeLabels by
            simp [PairWitness.negativeLabels, hapexR, hfitR'.1])
    · rcases hdR with hposR | ⟨hroleR, hapexR⟩
      · exfalso
        have hfitL' : w.leftBlock.singleton = w.common ∧
            (w.leftBlock.left = a.x ∨ w.leftBlock.right = a.x) := by
          simpa [hroleL, RoleFits] using hfitL
        exact Finset.disjoint_left.mp hcompat
          (show (z, w.common) ∈ w.positiveLabels by
            simp [PairWitness.positiveLabels, hposR])
          (show (z, w.common) ∈ w.negativeLabels by
            simp [PairWitness.negativeLabels, hapexL, hfitL'.1])
      · exact ⟨hroleL, hroleR, hapexL.symm.trans hapexR⟩

def meanOtherLeaf {n k : ℕ} (b : TriangleBlock n k) (root : Fin n) : Fin n :=
  if b.left = root then b.right else b.left

theorem meanOtherLeaf_spec {n k : ℕ} (b : TriangleBlock n k) (root : Fin n)
    (hroot : b.left = root ∨ b.right = root) :
    meanOtherLeaf b root ≠ root ∧
      (b.left = root ∧ b.right = meanOtherLeaf b root ∨
        b.left = meanOtherLeaf b root ∧ b.right = root) := by
  rcases hroot with hl | hr
  · have hne : b.right ≠ root := by
      intro h
      exact b.left_ne_right (hl.trans h.symm)
    simp [meanOtherLeaf, hl, hne]
  · have hnl : b.left ≠ root := by
      intro h
      exact b.left_ne_right (h.trans hr.symm)
    simp [meanOtherLeaf, hnl, hr]

abbrev MeanRootBlockCode (n k : ℕ) := Fin n × Fin n × Fin k

def meanRootBlockCode {n k : ℕ} (r : RootRole) (root : Fin n)
    (b : TriangleBlock n k) : MeanRootBlockCode n k :=
  match r with
  | .repeatedApex => (b.left, b.right, b.singleton)
  | .repeatedLeaf => (b.apex, meanOtherLeaf b root, b.singleton)
  | .singletonLeaf => (b.apex, meanOtherLeaf b root, b.repeated)

def MeanRootCodeValid {n k : ℕ} (r : RootRole) (root : Fin n)
    (common : Fin k) (A : Finset (Fin n)) (code : MeanRootBlockCode n k) : Prop :=
  code.1 ∈ A ∧ code.2.1 ∈ A ∧
    (match r with
      | .repeatedApex => code.1 < code.2.1
      | .repeatedLeaf | .singletonLeaf => code.1 ≠ code.2.1) ∧
    code.2.2 ≠ common

abbrev MeanAllowedRootBlock {n k : ℕ} (r : RootRole) (root : Fin n)
    (common : Fin k) (A : Finset (Fin n)) :=
  {b : TriangleBlock n k //
    RoleFits r b root common ∧ MeanRootCodeValid r root common A
      (meanRootBlockCode r root b)}

def meanLeafBlock {n k : ℕ} (apex root other : Fin n)
    (har : apex ≠ root) (hao : apex ≠ other) (hro : root ≠ other)
    (repeated singleton : Fin k) (hc : repeated ≠ singleton) :
    TriangleBlock n k :=
  if h : root < other then
    { apex := apex
      left := root
      right := other
      apex_ne_left := har
      apex_ne_right := hao
      left_lt_right := h
      repeated := repeated
      singleton := singleton
      colors_ne := hc }
  else
    { apex := apex
      left := other
      right := root
      apex_ne_left := hao
      apex_ne_right := har
      left_lt_right := lt_of_le_of_ne (not_lt.mp h) hro.symm
      repeated := repeated
      singleton := singleton
      colors_ne := hc }

@[simp] theorem meanLeafBlock_apex {n k : ℕ} (apex root other : Fin n)
    (har : apex ≠ root) (hao : apex ≠ other) (hro : root ≠ other)
    (repeated singleton : Fin k) (hc : repeated ≠ singleton) :
    (meanLeafBlock apex root other har hao hro repeated singleton hc).apex = apex := by
  unfold meanLeafBlock
  split <;> rfl

@[simp] theorem meanLeafBlock_repeated {n k : ℕ} (apex root other : Fin n)
    (har : apex ≠ root) (hao : apex ≠ other) (hro : root ≠ other)
    (repeated singleton : Fin k) (hc : repeated ≠ singleton) :
    (meanLeafBlock apex root other har hao hro repeated singleton hc).repeated = repeated := by
  unfold meanLeafBlock
  split <;> rfl

@[simp] theorem meanLeafBlock_singleton {n k : ℕ} (apex root other : Fin n)
    (har : apex ≠ root) (hao : apex ≠ other) (hro : root ≠ other)
    (repeated singleton : Fin k) (hc : repeated ≠ singleton) :
    (meanLeafBlock apex root other har hao hro repeated singleton hc).singleton = singleton := by
  unfold meanLeafBlock
  split <;> rfl

theorem meanLeafBlock_root_mem_leaves {n k : ℕ} (apex root other : Fin n)
    (har : apex ≠ root) (hao : apex ≠ other) (hro : root ≠ other)
    (repeated singleton : Fin k) (hc : repeated ≠ singleton) :
    (meanLeafBlock apex root other har hao hro repeated singleton hc).left = root ∨
      (meanLeafBlock apex root other har hao hro repeated singleton hc).right = root := by
  simp only [meanLeafBlock]
  split_ifs <;> simp

@[simp] theorem meanOtherLeaf_meanLeafBlock {n k : ℕ} (apex root other : Fin n)
    (har : apex ≠ root) (hao : apex ≠ other) (hro : root ≠ other)
    (repeated singleton : Fin k) (hc : repeated ≠ singleton) :
    meanOtherLeaf (meanLeafBlock apex root other har hao hro repeated singleton hc) root =
      other := by
  simp only [meanLeafBlock]
  split_ifs with h
  · simp [meanOtherLeaf]
  · simp [meanOtherLeaf, hro, hro.symm]

theorem meanOrderedLeaves_eq_of_otherLeaf_eq {n k : ℕ}
    {b b' : TriangleBlock n k} {root : Fin n}
    (hb : b.left = root ∨ b.right = root)
    (hb' : b'.left = root ∨ b'.right = root)
    (ho : meanOtherLeaf b root = meanOtherLeaf b' root) :
    b.left = b'.left ∧ b.right = b'.right := by
  rcases hb with hl | hr <;> rcases hb' with hl' | hr'
  · simp [meanOtherLeaf, hl, hl'] at ho
    exact ⟨hl.trans hl'.symm, ho⟩
  · have hnl' : b'.left ≠ root := by
      intro h
      exact b'.left_ne_right (h.trans hr'.symm)
    simp [meanOtherLeaf, hl, hnl'] at ho
    exfalso
    have hbad : b'.right < b'.left := by
      simpa [hl, hr', ho] using b.left_lt_right
    exact (not_lt_of_ge (le_of_lt b'.left_lt_right) hbad).elim
  · have hnl : b.left ≠ root := by
      intro h
      exact b.left_ne_right (h.trans hr.symm)
    simp [meanOtherLeaf, hnl, hl'] at ho
    exfalso
    have hbad : b.right < b.left := by
      simpa [hr, hl', ho] using b'.left_lt_right
    exact (not_lt_of_ge (le_of_lt b.left_lt_right) hbad).elim
  · have hnl : b.left ≠ root := by
      intro h
      exact b.left_ne_right (h.trans hr.symm)
    have hnl' : b'.left ≠ root := by
      intro h
      exact b'.left_ne_right (h.trans hr'.symm)
    simp [meanOtherLeaf, hnl, hnl'] at ho
    exact ⟨ho, hr.trans hr'.symm⟩

theorem meanRootBlockCode_injective_on_role {n k : ℕ}
    (r : RootRole) (root : Fin n) (common : Fin k)
    {b b' : TriangleBlock n k} (hb : RoleFits r b root common)
    (hb' : RoleFits r b' root common)
    (hcode : meanRootBlockCode r root b = meanRootBlockCode r root b') :
    b = b' := by
  cases r with
  | repeatedApex =>
      simp only [RoleFits] at hb hb'
      simp only [meanRootBlockCode, Prod.mk.injEq] at hcode
      rcases hb with ⟨hrep, hapex⟩
      rcases hb' with ⟨hrep', hapex'⟩
      cases b
      cases b'
      simp_all
  | repeatedLeaf =>
      simp only [RoleFits] at hb hb'
      rcases hb with ⟨hrep, hleaf⟩
      rcases hb' with ⟨hrep', hleaf'⟩
      simp only [meanRootBlockCode, Prod.mk.injEq] at hcode
      rcases hcode with ⟨hapex, hother, hsingleton⟩
      have hleaves := meanOrderedLeaves_eq_of_otherLeaf_eq hleaf hleaf' hother
      cases b
      cases b'
      simp_all
  | singletonLeaf =>
      simp only [RoleFits] at hb hb'
      rcases hb with ⟨hsingle, hleaf⟩
      rcases hb' with ⟨hsingle', hleaf'⟩
      simp only [meanRootBlockCode, Prod.mk.injEq] at hcode
      rcases hcode with ⟨hapex, hother, hrepeated⟩
      have hleaves := meanOrderedLeaves_eq_of_otherLeaf_eq hleaf hleaf' hother
      cases b
      cases b'
      simp_all

noncomputable def meanBlockOfValidCode {n k : ℕ} (r : RootRole)
    (root : Fin n) (common : Fin k) (A : Finset (Fin n))
    (hroot : root ∉ A)
    (q : {code : MeanRootBlockCode n k // MeanRootCodeValid r root common A code}) :
    TriangleBlock n k := by
  let u := q.1.1
  let v := q.1.2.1
  let d := q.1.2.2
  have huA : u ∈ A := q.2.1
  have hvA : v ∈ A := q.2.2.1
  have hru : root ≠ u := fun h ↦ hroot (h ▸ huA)
  have hrv : root ≠ v := fun h ↦ hroot (h ▸ hvA)
  cases r with
  | repeatedApex =>
      exact
        { apex := root
          left := u
          right := v
          apex_ne_left := hru
          apex_ne_right := hrv
          left_lt_right := q.2.2.2.1
          repeated := common
          singleton := d
          colors_ne := q.2.2.2.2.symm }
  | repeatedLeaf =>
      exact meanLeafBlock u root v hru.symm q.2.2.2.1 hrv common d
        q.2.2.2.2.symm
  | singletonLeaf =>
      exact meanLeafBlock u root v hru.symm q.2.2.2.1 hrv d common
        q.2.2.2.2

theorem meanBlockOfValidCode_roleFits {n k : ℕ} (r : RootRole)
    (root : Fin n) (common : Fin k) (A : Finset (Fin n))
    (hroot : root ∉ A)
    (q : {code : MeanRootBlockCode n k // MeanRootCodeValid r root common A code}) :
    RoleFits r (meanBlockOfValidCode r root common A hroot q) root common := by
  cases r with
  | repeatedApex => simp [meanBlockOfValidCode, RoleFits]
  | repeatedLeaf =>
      simp [meanBlockOfValidCode, RoleFits,
        meanLeafBlock_root_mem_leaves]
  | singletonLeaf =>
      simp [meanBlockOfValidCode, RoleFits,
        meanLeafBlock_root_mem_leaves]

theorem meanBlockOfValidCode_code {n k : ℕ} (r : RootRole)
    (root : Fin n) (common : Fin k) (A : Finset (Fin n))
    (hroot : root ∉ A)
    (q : {code : MeanRootBlockCode n k // MeanRootCodeValid r root common A code}) :
    meanRootBlockCode r root (meanBlockOfValidCode r root common A hroot q) = q.1 := by
  cases r with
  | repeatedApex => simp [meanBlockOfValidCode, meanRootBlockCode]
  | repeatedLeaf => simp [meanBlockOfValidCode, meanRootBlockCode]
  | singletonLeaf => simp [meanBlockOfValidCode, meanRootBlockCode]

noncomputable def meanAllowedRootBlockEquivCode {n k : ℕ} (r : RootRole)
    (root : Fin n) (common : Fin k) (A : Finset (Fin n))
    (hroot : root ∉ A) :
    MeanAllowedRootBlock r root common A ≃
      {code : MeanRootBlockCode n k // MeanRootCodeValid r root common A code} where
  toFun b := ⟨meanRootBlockCode r root b.1, b.2.2⟩
  invFun q :=
    ⟨meanBlockOfValidCode r root common A hroot q,
      meanBlockOfValidCode_roleFits r root common A hroot q,
      meanBlockOfValidCode_code r root common A hroot q ▸ q.2⟩
  left_inv b := by
    apply Subtype.ext
    symm
    apply meanRootBlockCode_injective_on_role r root common b.2.1
      (meanBlockOfValidCode_roleFits r root common A hroot
        ⟨meanRootBlockCode r root b.1, b.2.2⟩)
    symm
    simpa using meanBlockOfValidCode_code r root common A hroot
      ⟨meanRootBlockCode r root b.1, b.2.2⟩
  right_inv q := by
    apply Subtype.ext
    exact meanBlockOfValidCode_code r root common A hroot q

abbrev MeanLtChoice {n : ℕ} (A : Finset (Fin n)) :=
  {p : Fin n × Fin n // p ∈ (A ×ˢ A).filter fun p ↦ p.1 < p.2}

abbrev MeanNeChoice {n : ℕ} (A : Finset (Fin n)) :=
  {p : Fin n × Fin n // p ∈ A.offDiag}

def meanValidCodeEquivChoice {n k : ℕ} (r : RootRole) (root : Fin n)
    (common : Fin k) (A : Finset (Fin n)) :
    {code : MeanRootBlockCode n k // MeanRootCodeValid r root common A code} ≃
      (match r with
        | .repeatedApex => MeanLtChoice A × OtherColor common
        | .repeatedLeaf | .singletonLeaf => MeanNeChoice A × OtherColor common) := by
  cases r with
  | repeatedApex =>
      exact
        { toFun := fun q ↦
            ⟨⟨(q.1.1, q.1.2.1), by simp [MeanRootCodeValid, q.2.1,
              q.2.2.1, q.2.2.2.1]⟩,
              ⟨q.1.2.2, q.2.2.2.2⟩⟩
          invFun := fun q ↦ by
            rcases q with ⟨⟨p, hp⟩, d⟩
            have hp' := Finset.mem_filter.mp hp
            have hmem := Finset.mem_product.mp hp'.1
            exact ⟨(p.1, p.2, d.1), by
              exact ⟨hmem.1, hmem.2, hp'.2, d.2⟩⟩
          left_inv := by intro q; apply Subtype.ext; rfl
          right_inv := by intro q; rcases q with ⟨⟨p, hp⟩, d⟩; rfl }
  | repeatedLeaf =>
      exact
        { toFun := fun q ↦
            ⟨⟨(q.1.1, q.1.2.1), by simp [MeanRootCodeValid, q.2.1,
              q.2.2.1, q.2.2.2.1]⟩,
              ⟨q.1.2.2, q.2.2.2.2⟩⟩
          invFun := fun q ↦ by
            rcases q with ⟨⟨p, hp⟩, d⟩
            have hp' := Finset.mem_offDiag.mp hp
            exact ⟨(p.1, p.2, d.1), by
              exact ⟨hp'.1, hp'.2.1, hp'.2.2, d.2⟩⟩
          left_inv := by intro q; apply Subtype.ext; rfl
          right_inv := by intro q; rcases q with ⟨⟨p, hp⟩, d⟩; rfl }
  | singletonLeaf =>
      exact
        { toFun := fun q ↦
            ⟨⟨(q.1.1, q.1.2.1), by simp [MeanRootCodeValid, q.2.1,
              q.2.2.1, q.2.2.2.1]⟩,
              ⟨q.1.2.2, q.2.2.2.2⟩⟩
          invFun := fun q ↦ by
            rcases q with ⟨⟨p, hp⟩, d⟩
            have hp' := Finset.mem_offDiag.mp hp
            exact ⟨(p.1, p.2, d.1), by
              exact ⟨hp'.1, hp'.2.1, hp'.2.2, d.2⟩⟩
          left_inv := by intro q; apply Subtype.ext; rfl
          right_inv := by intro q; rcases q with ⟨⟨p, hp⟩, d⟩; rfl }

@[simp] theorem card_meanLtChoice {n : ℕ} (A : Finset (Fin n)) :
    Fintype.card (MeanLtChoice A) = A.card.choose 2 := by
  rw [Fintype.card_coe]
  exact Finset.card_product_filter_lt

@[simp] theorem card_meanNeChoice {n : ℕ} (A : Finset (Fin n)) :
    Fintype.card (MeanNeChoice A) = A.card * (A.card - 1) := by
  rw [Fintype.card_coe, Finset.offDiag_card]
  calc
    A.card * A.card - A.card = A.card * A.card - A.card * 1 := by simp
    _ = A.card * (A.card - 1) :=
      (Nat.mul_sub_left_distrib A.card A.card 1).symm

@[simp] theorem card_meanValidCode {n k : ℕ} (r : RootRole) (root : Fin n)
    (common : Fin k) (A : Finset (Fin n)) :
    Fintype.card
        {code : MeanRootBlockCode n k // MeanRootCodeValid r root common A code} =
      rootRoleChoiceCount A.card r * (k - 1) := by
  cases r with
  | repeatedApex =>
      rw [Fintype.card_congr (meanValidCodeEquivChoice .repeatedApex root common A),
        Fintype.card_prod, card_meanLtChoice, card_otherColor]
      rfl
  | repeatedLeaf =>
      rw [Fintype.card_congr (meanValidCodeEquivChoice .repeatedLeaf root common A),
        Fintype.card_prod, card_meanNeChoice, card_otherColor]
      rfl
  | singletonLeaf =>
      rw [Fintype.card_congr (meanValidCodeEquivChoice .singletonLeaf root common A),
        Fintype.card_prod, card_meanNeChoice, card_otherColor]
      rfl

@[simp] theorem card_meanAllowedRootBlock {n k : ℕ} (r : RootRole)
    (root : Fin n) (common : Fin k) (A : Finset (Fin n))
    (hroot : root ∉ A) :
    Fintype.card (MeanAllowedRootBlock r root common A) =
      rootRoleChoiceCount A.card r * (k - 1) := by
  rw [Fintype.card_congr (meanAllowedRootBlockEquivCode r root common A hroot),
    card_meanValidCode]

theorem meanRootBlockCode_shape {n k : ℕ} (r : RootRole) (root : Fin n)
    (common : Fin k) (b : TriangleBlock n k) (hfit : RoleFits r b root common) :
    root ≠ (meanRootBlockCode r root b).1 ∧
      root ≠ (meanRootBlockCode r root b).2.1 ∧
      (meanRootBlockCode r root b).1 ≠ (meanRootBlockCode r root b).2.1 ∧
      blockVertices b =
        {root, (meanRootBlockCode r root b).1,
          (meanRootBlockCode r root b).2.1} := by
  cases r with
  | repeatedApex =>
      simp only [RoleFits] at hfit
      rcases hfit with ⟨hrep, hapex⟩
      simp only [meanRootBlockCode]
      subst root
      refine ⟨b.apex_ne_left, b.apex_ne_right, b.left_ne_right, ?_⟩
      rfl
  | repeatedLeaf =>
      simp only [RoleFits] at hfit
      rcases hfit with ⟨hrep, hleaf⟩
      have hs := meanOtherLeaf_spec b root hleaf
      simp only [meanRootBlockCode]
      refine ⟨?_, hs.1.symm, ?_, ?_⟩
      · rcases hleaf with rfl | rfl
        · exact b.apex_ne_left.symm
        · exact b.apex_ne_right.symm
      · rcases hs.2 with hs | hs
        · exact fun h ↦ b.apex_ne_right (h.trans hs.2.symm)
        · exact fun h ↦ b.apex_ne_left (h.trans hs.1.symm)
      · rcases hs.2 with hs | hs
        · ext z; simp [blockVertices, hs.1, hs.2, or_comm, or_left_comm]
        · ext z; simp [blockVertices, hs.1, hs.2, or_comm, or_left_comm]
  | singletonLeaf =>
      simp only [RoleFits] at hfit
      rcases hfit with ⟨hsingle, hleaf⟩
      have hs := meanOtherLeaf_spec b root hleaf
      simp only [meanRootBlockCode]
      refine ⟨?_, hs.1.symm, ?_, ?_⟩
      · rcases hleaf with rfl | rfl
        · exact b.apex_ne_left.symm
        · exact b.apex_ne_right.symm
      · rcases hs.2 with hs | hs
        · exact fun h ↦ b.apex_ne_right (h.trans hs.2.symm)
        · exact fun h ↦ b.apex_ne_left (h.trans hs.1.symm)
      · rcases hs.2 with hs | hs
        · ext z; simp [blockVertices, hs.1, hs.2, or_comm, or_left_comm]
        · ext z; simp [blockVertices, hs.1, hs.2, or_comm, or_left_comm]

theorem auxSupport_disjoint_of_blockVertices_disjoint {n k : ℕ}
    (b c : TriangleBlock n k) (h : Disjoint (blockVertices b) (blockVertices c)) :
    Disjoint b.auxSupport c.auxSupport := by
  rw [Finset.disjoint_left]
  intro u huB huC
  have hbaseB :
      (∃ x y : Fin n, u = Sum.inl s(x, y) ∧ x ∈ blockVertices b) ∨
        ∃ z : Fin n × Fin k, u = Sum.inr z ∧ z.1 ∈ blockVertices b := by
    simp only [TriangleBlock.auxSupport, Finset.mem_union, Finset.mem_image] at huB
    rcases huB with ⟨e, he, rfl⟩ | ⟨z, hz, rfl⟩
    · simp only [TriangleBlock.graphEdges, Finset.mem_insert,
        Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact Or.inl ⟨b.apex, b.left, rfl, by simp [blockVertices]⟩
      · exact Or.inl ⟨b.apex, b.right, rfl, by simp [blockVertices]⟩
      · exact Or.inl ⟨b.left, b.right, rfl, by simp [blockVertices]⟩
    · exact Or.inr ⟨z, rfl, by
        simp only [TriangleBlock.positiveLabels, Finset.mem_insert,
          Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp [blockVertices]⟩
  have hbaseC :
      (∀ x y : Fin n, u = Sum.inl s(x, y) → x ∈ blockVertices c) ∧
        (∀ z : Fin n × Fin k, u = Sum.inr z → z.1 ∈ blockVertices c) := by
    constructor
    · intro x y hu
      subst u
      simp only [TriangleBlock.auxSupport, Finset.mem_union, Finset.mem_image] at huC
      rcases huC with ⟨e, he, hes⟩ | ⟨z, hz, hbad⟩
      · have hes' : e = s(x, y) := Sum.inl.inj hes
        subst e
        simp only [TriangleBlock.graphEdges, Finset.mem_insert,
          Finset.mem_singleton] at he
        rcases he with he | he | he
        all_goals simp only [Sym2.eq_iff] at he
        all_goals rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        all_goals simp [blockVertices, h1, h2]
      · cases hbad
    · intro z hu
      subst u
      simp only [TriangleBlock.auxSupport, Finset.mem_union, Finset.mem_image] at huC
      rcases huC with ⟨e, he, hbad⟩ | ⟨z', hz', hzz⟩
      · cases hbad
      · have heq : z' = z := Sum.inr.inj hzz
        subst z'
        simp only [TriangleBlock.positiveLabels, Finset.mem_insert,
          Finset.mem_singleton] at hz'
        rcases hz' with hz' | hz' | hz' | hz' | hz' <;>
          simp [blockVertices] at hz' ⊢ <;> aesop
  rcases hbaseB with ⟨x, y, hu, hx⟩ | ⟨z, hu, hz⟩
  · exact Finset.disjoint_left.mp h hx (hbaseC.1 x y hu)
  · exact Finset.disjoint_left.mp h hz (hbaseC.2 z hu)

def meanBaseAvailable {n : ℕ} (x y : Fin n) : Finset (Fin n) :=
  (Finset.univ.erase x).erase y

def meanRemainingAvailable {n k : ℕ} (r : RootRole) (root : Fin n)
    (A : Finset (Fin n)) (b : TriangleBlock n k) : Finset (Fin n) :=
  (A.erase (meanRootBlockCode r root b).1).erase
    (meanRootBlockCode r root b).2.1

@[simp] theorem card_meanBaseAvailable {n : ℕ} (x y : Fin n) (hxy : x ≠ y) :
    (meanBaseAvailable x y).card = n - 2 := by
  rw [meanBaseAvailable, Finset.card_erase_of_mem (by simp [hxy.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ x)]
  simp
  omega

theorem card_meanRemainingAvailable {n k : ℕ} (r : RootRole) (root : Fin n)
    (common : Fin k) (A : Finset (Fin n))
    (b : MeanAllowedRootBlock r root common A) :
    (meanRemainingAvailable r root A b.1).card = A.card - 2 := by
  have hu := b.2.2.1
  have hv := b.2.2.2.1
  have huv : (meanRootBlockCode r root b.1).1 ≠
      (meanRootBlockCode r root b.1).2.1 := by
    cases r with
    | repeatedApex => exact ne_of_lt b.2.2.2.2.1
    | repeatedLeaf => exact b.2.2.2.2.1
    | singletonLeaf => exact b.2.2.2.2.1
  rw [meanRemainingAvailable,
    Finset.card_erase_of_mem (by simp [hv, huv.symm]),
    Finset.card_erase_of_mem hu]
  omega

abbrev MeanDisjointRoleCode {n : ℕ} (k : ℕ) (a : PairRoleIndex n) :=
  Σ common : Fin k,
    Σ left : MeanAllowedRootBlock a.leftRole a.x common
      (meanBaseAvailable a.x a.y),
      MeanAllowedRootBlock a.rightRole a.y common
        (meanRemainingAvailable a.leftRole a.x
          (meanBaseAvailable a.x a.y) left.1)

theorem card_meanDisjointRoleCode {n : ℕ} (k : ℕ) (a : PairRoleIndex n)
    (hxy : a.x ≠ a.y) :
    Fintype.card (MeanDisjointRoleCode k a) = pairRoleDisjointCount k a := by
  rw [Fintype.card_sigma]
  calc
    (∑ common : Fin k,
        Fintype.card
          (Σ left : MeanAllowedRootBlock a.leftRole a.x common
              (meanBaseAvailable a.x a.y),
            MeanAllowedRootBlock a.rightRole a.y common
              (meanRemainingAvailable a.leftRole a.x
                (meanBaseAvailable a.x a.y) left.1))) =
        ∑ _common : Fin k,
          (rootRoleChoiceCount (n - 2) a.leftRole * (k - 1)) *
            (rootRoleChoiceCount (n - 4) a.rightRole * (k - 1)) := by
      apply Finset.sum_congr rfl
      intro common hcommon
      rw [Fintype.card_sigma]
      calc
        (∑ left : MeanAllowedRootBlock a.leftRole a.x common
            (meanBaseAvailable a.x a.y),
          Fintype.card
            (MeanAllowedRootBlock a.rightRole a.y common
              (meanRemainingAvailable a.leftRole a.x
                (meanBaseAvailable a.x a.y) left.1))) =
            ∑ _left : MeanAllowedRootBlock a.leftRole a.x common
                (meanBaseAvailable a.x a.y),
              rootRoleChoiceCount (n - 4) a.rightRole * (k - 1) := by
          apply Finset.sum_congr rfl
          intro left hleft
          rw [card_meanAllowedRootBlock]
          · rw [card_meanRemainingAvailable,
              card_meanBaseAvailable a.x a.y hxy]
            congr 2
          · intro hy
            have hyA : a.y ∈ meanBaseAvailable a.x a.y := by
              exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
            simp [meanBaseAvailable] at hyA
        _ = Fintype.card
              (MeanAllowedRootBlock a.leftRole a.x common
                (meanBaseAvailable a.x a.y)) *
              (rootRoleChoiceCount (n - 4) a.rightRole * (k - 1)) := by simp
        _ = (rootRoleChoiceCount (n - 2) a.leftRole * (k - 1)) *
              (rootRoleChoiceCount (n - 4) a.rightRole * (k - 1)) := by
          rw [card_meanAllowedRootBlock,
            card_meanBaseAvailable a.x a.y hxy]
          simp [meanBaseAvailable]
    _ = k * ((rootRoleChoiceCount (n - 2) a.leftRole * (k - 1)) *
          (rootRoleChoiceCount (n - 4) a.rightRole * (k - 1))) := by simp
    _ = pairRoleDisjointCount k a := by
      simp [pairRoleDisjointCount]
      ring

theorem meanRootBlockCode_otherColor_ne {n k : ℕ} (r : RootRole)
    (root : Fin n) (common : Fin k) (b : TriangleBlock n k)
    (hfit : RoleFits r b root common) :
    (meanRootBlockCode r root b).2.2 ≠ common := by
  cases r with
  | repeatedApex =>
      simp only [RoleFits] at hfit
      intro hs
      apply b.colors_ne
      exact hfit.1.trans hs.symm
  | repeatedLeaf =>
      simp only [RoleFits] at hfit
      intro hs
      apply b.colors_ne
      exact hfit.1.trans hs.symm
  | singletonLeaf =>
      simp only [RoleFits] at hfit
      intro hr
      apply b.colors_ne
      exact hr.trans hfit.1.symm

theorem meanLeftCodeValid_of_vertexDisjoint {n k : ℕ} (a : PairRoleIndex n)
    (common : Fin k) (left right : TriangleBlock n k)
    (hfitL : RoleFits a.leftRole left a.x common)
    (hfitR : RoleFits a.rightRole right a.y common)
    (hdisj : Disjoint (blockVertices left) (blockVertices right)) :
    MeanRootCodeValid a.leftRole a.x common (meanBaseAvailable a.x a.y)
      (meanRootBlockCode a.leftRole a.x left) := by
  let u := (meanRootBlockCode a.leftRole a.x left).1
  let v := (meanRootBlockCode a.leftRole a.x left).2.1
  have hsL := meanRootBlockCode_shape a.leftRole a.x common left hfitL
  have hsR := meanRootBlockCode_shape a.rightRole a.y common right hfitR
  have huL : u ∈ blockVertices left := by rw [hsL.2.2.2]; simp [u]
  have hvL : v ∈ blockVertices left := by rw [hsL.2.2.2]; simp [v]
  have hyR : a.y ∈ blockVertices right := by rw [hsR.2.2.2]; simp
  have huy : u ≠ a.y := fun h ↦
    Finset.disjoint_left.mp hdisj huL (h ▸ hyR)
  have hvy : v ≠ a.y := fun h ↦
    Finset.disjoint_left.mp hdisj hvL (h ▸ hyR)
  refine ⟨?_, ?_, ?_, meanRootBlockCode_otherColor_ne _ _ _ _ hfitL⟩
  · simp [meanBaseAvailable, u, hsL.1.symm, huy]
  · simp [meanBaseAvailable, v, hsL.2.1.symm, hvy]
  · cases hrole : a.leftRole with
    | repeatedApex => simpa [hrole, meanRootBlockCode] using left.left_lt_right
    | repeatedLeaf => simpa [hrole] using hsL.2.2.1
    | singletonLeaf => simpa [hrole] using hsL.2.2.1

theorem meanRightCodeValid_of_vertexDisjoint {n k : ℕ} (a : PairRoleIndex n)
    (common : Fin k) (left right : TriangleBlock n k)
    (hfitL : RoleFits a.leftRole left a.x common)
    (hfitR : RoleFits a.rightRole right a.y common)
    (hdisj : Disjoint (blockVertices left) (blockVertices right)) :
    MeanRootCodeValid a.rightRole a.y common
      (meanRemainingAvailable a.leftRole a.x (meanBaseAvailable a.x a.y) left)
      (meanRootBlockCode a.rightRole a.y right) := by
  let lu := (meanRootBlockCode a.leftRole a.x left).1
  let lv := (meanRootBlockCode a.leftRole a.x left).2.1
  let ru := (meanRootBlockCode a.rightRole a.y right).1
  let rv := (meanRootBlockCode a.rightRole a.y right).2.1
  have hsL := meanRootBlockCode_shape a.leftRole a.x common left hfitL
  have hsR := meanRootBlockCode_shape a.rightRole a.y common right hfitR
  have hruR : ru ∈ blockVertices right := by rw [hsR.2.2.2]; simp [ru]
  have hrvR : rv ∈ blockVertices right := by rw [hsR.2.2.2]; simp [rv]
  have hxL : a.x ∈ blockVertices left := by rw [hsL.2.2.2]; simp
  have hluL : lu ∈ blockVertices left := by rw [hsL.2.2.2]; simp [lu]
  have hlvL : lv ∈ blockVertices left := by rw [hsL.2.2.2]; simp [lv]
  have hrux : ru ≠ a.x := fun h ↦
    Finset.disjoint_left.mp hdisj (h ▸ hxL) hruR
  have hrvx : rv ≠ a.x := fun h ↦
    Finset.disjoint_left.mp hdisj (h ▸ hxL) hrvR
  have hrulu : ru ≠ lu := fun h ↦
    Finset.disjoint_left.mp hdisj (h ▸ hluL) hruR
  have hrulv : ru ≠ lv := fun h ↦
    Finset.disjoint_left.mp hdisj (h ▸ hlvL) hruR
  have hrvlu : rv ≠ lu := fun h ↦
    Finset.disjoint_left.mp hdisj (h ▸ hluL) hrvR
  have hrvLlv : rv ≠ lv := fun h ↦
    Finset.disjoint_left.mp hdisj (h ▸ hlvL) hrvR
  refine ⟨?_, ?_, ?_, meanRootBlockCode_otherColor_ne _ _ _ _ hfitR⟩
  · simp [meanRemainingAvailable, meanBaseAvailable, ru, lu, lv,
      hsR.1.symm, hrux, hrulu, hrulv]
  · simp [meanRemainingAvailable, meanBaseAvailable, rv, lu, lv,
      hsR.2.1.symm, hrvx, hrvlu, hrvLlv]
  · cases hrole : a.rightRole with
    | repeatedApex => simpa [hrole, meanRootBlockCode] using right.left_lt_right
    | repeatedLeaf => simpa [hrole] using hsR.2.2.1
    | singletonLeaf => simpa [hrole] using hsR.2.2.1

theorem meanAllowedPair_vertexDisjoint {n k : ℕ} (a : PairRoleIndex n)
    (common : Fin k)
    (hxy : a.x ≠ a.y)
    (left : MeanAllowedRootBlock a.leftRole a.x common
      (meanBaseAvailable a.x a.y))
    (right : MeanAllowedRootBlock a.rightRole a.y common
      (meanRemainingAvailable a.leftRole a.x
        (meanBaseAvailable a.x a.y) left.1)) :
    Disjoint (blockVertices left.1) (blockVertices right.1) := by
  have hsL := meanRootBlockCode_shape a.leftRole a.x common left.1 left.2.1
  have hsR := meanRootBlockCode_shape a.rightRole a.y common right.1 right.2.1
  rw [hsL.2.2.2, hsR.2.2.2, Finset.disjoint_left]
  intro z hzL hzR
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzL hzR
  have hluA := left.2.2.1
  have hlvA := left.2.2.2.1
  have hruA := right.2.2.1
  have hrvA := right.2.2.2.1
  simp only [meanRemainingAvailable, Finset.mem_erase] at hruA hrvA
  have hxA : a.x ∉ meanBaseAvailable a.x a.y := by simp [meanBaseAvailable]
  have hyA : a.y ∉ meanBaseAvailable a.x a.y := by simp [meanBaseAvailable]
  rcases hzL with hx | hu | hv <;> rcases hzR with hy | hru | hrv
  · exact hxy (hx.symm.trans hy)
  · have heq := hru.symm.trans hx
    rw [heq] at hruA
    exact hxA hruA.2.2
  · have heq := hrv.symm.trans hx
    rw [heq] at hrvA
    exact hxA hrvA.2.2
  · have heq := hu.symm.trans hy
    rw [heq] at hluA
    exact hyA hluA
  · exact hruA.2.1 (hru.symm.trans hu)
  · exact hrvA.2.1 (hrv.symm.trans hu)
  · have heq := hv.symm.trans hy
    rw [heq] at hlvA
    exact hyA hlvA
  · exact hruA.1 (hru.symm.trans hv)
  · exact hrvA.1 (hrv.symm.trans hv)

abbrev MeanVertexDisjointRoleWitness {n : ℕ} (k : ℕ) (a : PairRoleIndex n) :=
  {w : PairWitness n k //
    w.Geometry (allTriangleBlocks n k) a.toPairTestIndex ∧
      w.leftRole = a.leftRole ∧ w.rightRole = a.rightRole ∧
      Disjoint (blockVertices w.leftBlock) (blockVertices w.rightBlock)}

noncomputable def meanDisjointCodeToWitness {n : ℕ} {k : ℕ}
    (a : PairRoleIndex n) (hxy : a.x ≠ a.y) :
    MeanDisjointRoleCode k a → MeanVertexDisjointRoleWitness k a := fun q ↦ by
  rcases q with ⟨common, left, right⟩
  let w : PairWitness n k :=
    { common := common
      leftBlock := left.1
      rightBlock := right.1
      leftRole := a.leftRole
      rightRole := a.rightRole }
  have hvdisj := meanAllowedPair_vertexDisjoint a common hxy left right
  have hsdisj := auxSupport_disjoint_of_blockVertices_disjoint left.1 right.1 hvdisj
  have hneq : left.1 ≠ right.1 := by
    intro heq
    have hapexL : left.1.apex ∈ blockVertices left.1 := by simp [blockVertices]
    have hapexR : left.1.apex ∈ blockVertices right.1 := by
      rw [← heq]
      exact hapexL
    exact Finset.disjoint_left.mp hvdisj hapexL hapexR
  refine ⟨w, ?_, rfl, rfl, hvdisj⟩
  refine ⟨hxy, by simp, by simp, hneq, hsdisj, ?_, ?_, left.2.1, right.2.1⟩
  · simp [w, PairRoleIndex.toPairTestIndex, PairTestIndex.leftMultiplicity]
  · simp [w, PairRoleIndex.toPairTestIndex, PairTestIndex.rightMultiplicity]

noncomputable def meanWitnessToDisjointCode {n : ℕ} {k : ℕ}
    (a : PairRoleIndex n) :
    MeanVertexDisjointRoleWitness k a → MeanDisjointRoleCode k a := fun q ↦ by
  let w := q.1
  have hg := q.2.1
  have hrL := q.2.2.1
  have hrR := q.2.2.2.1
  have hvdisj := q.2.2.2.2
  have hfitL0 := hg.2.2.2.2.2.2.2.1
  have hfitR0 := hg.2.2.2.2.2.2.2.2
  have hfitL : RoleFits a.leftRole w.leftBlock a.x w.common := by
    simpa [w, PairRoleIndex.toPairTestIndex, hrL] using hfitL0
  have hfitR : RoleFits a.rightRole w.rightBlock a.y w.common := by
    simpa [w, PairRoleIndex.toPairTestIndex, hrR] using hfitR0
  exact ⟨w.common,
    ⟨w.leftBlock, hfitL,
      meanLeftCodeValid_of_vertexDisjoint a w.common w.leftBlock w.rightBlock
        hfitL hfitR hvdisj⟩,
    ⟨w.rightBlock, hfitR,
      meanRightCodeValid_of_vertexDisjoint a w.common w.leftBlock w.rightBlock
        hfitL hfitR hvdisj⟩⟩

noncomputable def meanDisjointRoleCodeEquivWitness {n : ℕ} {k : ℕ}
    (a : PairRoleIndex n) (hxy : a.x ≠ a.y) :
    MeanDisjointRoleCode k a ≃ MeanVertexDisjointRoleWitness k a where
  toFun := meanDisjointCodeToWitness a hxy
  invFun := meanWitnessToDisjointCode a
  left_inv q := by
    rcases q with ⟨common, left, right⟩
    rfl
  right_inv q := by
    apply Subtype.ext
    rcases q with ⟨⟨common, leftBlock, rightBlock, leftRole, rightRole⟩,
      hg, hrL, hrR, hv⟩
    simp only at hrL hrR
    subst leftRole
    subst rightRole
    rfl

theorem card_meanVertexDisjointRoleWitness {n : ℕ} (k : ℕ)
    (a : PairRoleIndex n) (hxy : a.x ≠ a.y) :
    Fintype.card (MeanVertexDisjointRoleWitness k a) =
      pairRoleDisjointCount k a := by
  rw [← card_meanDisjointRoleCode k a hxy,
    Fintype.card_congr (meanDisjointRoleCodeEquivWitness a hxy)]

def vertexDisjointRoleWitnesses {n k : ℕ} (a : PairRoleIndex n) :
    Finset (PairWitness n k) :=
  (geometricRoleWitnesses (allTriangleBlocks n k) a).filter fun w ↦
    Disjoint (blockVertices w.leftBlock) (blockVertices w.rightBlock)

def overlappingRoleWitnesses {n k : ℕ} (a : PairRoleIndex n) :
    Finset (PairWitness n k) :=
  (geometricRoleWitnesses (allTriangleBlocks n k) a).filter fun w ↦
    ¬Disjoint (blockVertices w.leftBlock) (blockVertices w.rightBlock)

theorem card_vertexDisjointRoleWitnesses {n k : ℕ} (a : PairRoleIndex n)
    (hxy : a.x ≠ a.y) :
    (vertexDisjointRoleWitnesses (k := k) a).card =
      pairRoleDisjointCount k a := by
  have hsub :
      Fintype.card (MeanVertexDisjointRoleWitness k a) =
        (vertexDisjointRoleWitnesses (k := k) a).card := by
    have hfin : vertexDisjointRoleWitnesses (k := k) a =
        Finset.univ.filter (fun w : PairWitness n k ↦
          w.Geometry (allTriangleBlocks n k) a.toPairTestIndex ∧
            w.leftRole = a.leftRole ∧ w.rightRole = a.rightRole ∧
            Disjoint (blockVertices w.leftBlock) (blockVertices w.rightBlock)) := by
      ext w
      simp only [vertexDisjointRoleWitnesses, geometricRoleWitnesses,
        geometricWitnesses, Finset.mem_filter, Finset.mem_univ, true_and]
      tauto
    rw [hfin]
    exact Fintype.card_subtype (fun w : PairWitness n k ↦
        w.Geometry (allTriangleBlocks n k) a.toPairTestIndex ∧
          w.leftRole = a.leftRole ∧ w.rightRole = a.rightRole ∧
          Disjoint (blockVertices w.leftBlock) (blockVertices w.rightBlock))
  rw [← hsub, card_meanVertexDisjointRoleWitness k a hxy]

theorem positiveLabel_fst_mem_blockVertices {n k : ℕ} (b : TriangleBlock n k)
    (z : Fin n × Fin k) (hz : z ∈ b.positiveLabels) :
    z.1 ∈ blockVertices b := by
  simp only [TriangleBlock.positiveLabels, Finset.mem_insert,
    Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp [blockVertices]

theorem pairWitness_positive_negative_disjoint_of_vertexDisjoint {n k : ℕ}
    (w : PairWitness n k)
    (hv : Disjoint (blockVertices w.leftBlock) (blockVertices w.rightBlock)) :
    Disjoint w.positiveLabels w.negativeLabels := by
  rw [Finset.disjoint_left]
  intro z hzP hzN
  simp only [PairWitness.positiveLabels, Finset.mem_union] at hzP
  simp only [PairWitness.negativeLabels, Finset.mem_insert,
    Finset.mem_singleton] at hzN
  rcases hzP with hzL | hzR <;> rcases hzN with rfl | rfl
  · exact absent_label_not_mem_positiveLabels w.leftBlock hzL
  · have hzLV : w.rightBlock.apex ∈ blockVertices w.leftBlock := by
      exact positiveLabel_fst_mem_blockVertices w.leftBlock _ hzL
    exact Finset.disjoint_left.mp hv hzLV (by simp [blockVertices])
  · have hzRV : w.leftBlock.apex ∈ blockVertices w.rightBlock := by
      exact positiveLabel_fst_mem_blockVertices w.rightBlock _ hzR
    exact Finset.disjoint_left.mp hv (by simp [blockVertices]) hzRV
  · exact absent_label_not_mem_positiveLabels w.rightBlock hzR

theorem pairWitness_negativeLabels_card_of_vertexDisjoint {n k : ℕ}
    (w : PairWitness n k)
    (hv : Disjoint (blockVertices w.leftBlock) (blockVertices w.rightBlock)) :
    w.negativeLabels.card = 2 := by
  have hne : (w.leftBlock.apex, w.leftBlock.singleton) ≠
      (w.rightBlock.apex, w.rightBlock.singleton) := by
    intro h
    have ha : w.leftBlock.apex = w.rightBlock.apex := congrArg Prod.fst h
    exact Finset.disjoint_left.mp hv
      (show w.leftBlock.apex ∈ blockVertices w.leftBlock by simp [blockVertices])
      (show w.leftBlock.apex ∈ blockVertices w.rightBlock by
        rw [ha]
        simp [blockVertices])
  simp [PairWitness.negativeLabels, hne]

theorem weightedMean_pairRetentionIndicator_of_vertexDisjoint {n k : ℕ}
    (q : ℝ) (a : PairRoleIndex n) (w : PairWitness n k)
    (hw : w ∈ vertexDisjointRoleWitnesses (k := k) a) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ pairRetentionIndicator bits w) =
      q ^ 10 * (1 - q) ^ 2 := by
  have hmem := Finset.mem_filter.mp hw
  have hgmem := (Finset.mem_filter.mp hmem.1).1
  have hg := (Finset.mem_filter.mp hgmem).2
  rw [weightedMean_pairRetentionIndicator_of_geometry q w hg
    (pairWitness_positive_negative_disjoint_of_vertexDisjoint w hmem.2),
    pairWitness_negativeLabels_card_of_vertexDisjoint w hmem.2]

theorem sum_weightedMean_vertexDisjointRoleWitnesses {n k : ℕ}
    (q : ℝ) (a : PairRoleIndex n) (hxy : a.x ≠ a.y) :
    (∑ w ∈ vertexDisjointRoleWitnesses (k := k) a,
      McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ pairRetentionIndicator bits w)) =
      (pairRoleDisjointCount k a : ℝ) * q ^ 10 * (1 - q) ^ 2 := by
  calc
    _ = ∑ _w ∈ vertexDisjointRoleWitnesses (k := k) a,
        q ^ 10 * (1 - q) ^ 2 := by
      apply Finset.sum_congr rfl
      intro w hw
      exact weightedMean_pairRetentionIndicator_of_vertexDisjoint q a w hw
    _ = (pairRoleDisjointCount k a : ℝ) * q ^ 10 * (1 - q) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul,
        card_vertexDisjointRoleWitnesses a hxy]
      push_cast
      ring

theorem weightedMean_pairRetentionIndicator_mem_Icc {n k : ℕ}
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (w : PairWitness n k) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ pairRetentionIndicator bits w) ∈ Set.Icc (0 : ℝ) 1 := by
  have hw0 : ∀ i b,
      0 ≤ McDiarmid.bernoulliWeight
        (retentionProbability (n := n) (k := k) q) i b :=
    McDiarmid.bernoulliWeight_nonneg _ (fun _ ↦ hq)
  have hmass0 (bits : Fin (labelCount n k) → Bool) :
      0 ≤ McDiarmid.productMass
        (McDiarmid.bernoulliWeight (retentionProbability q)) bits :=
    McDiarmid.productMass_nonneg _ hw0 bits
  constructor
  · rw [McDiarmid.weightedMean]
    exact Finset.sum_nonneg fun bits hbits ↦
      mul_nonneg (hmass0 bits) (by
        by_cases h : w.RetentionValid (retainedOfBits bits) <;>
          simp [pairRetentionIndicator, h])
  · calc
      McDiarmid.weightedMean
          (McDiarmid.bernoulliWeight (retentionProbability q))
          (fun bits ↦ pairRetentionIndicator bits w) ≤
          McDiarmid.weightedMean
            (McDiarmid.bernoulliWeight (retentionProbability q))
            (fun _bits ↦ (1 : ℝ)) := by
        rw [McDiarmid.weightedMean, McDiarmid.weightedMean]
        apply Finset.sum_le_sum
        intro bits hbits
        exact mul_le_mul_of_nonneg_left (by
          by_cases h : w.RetentionValid (retainedOfBits bits) <;>
            simp [pairRetentionIndicator, h]) (hmass0 bits)
      _ = 1 := weightedMean_const_bernoulli q 1

theorem weightedMean_pairRoleWitnessStatistic_split {n k : ℕ}
    (q : ℝ) (a : PairRoleIndex n) :
    McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ pairRoleWitnessStatistic (allTriangleBlocks n k) bits a) =
      (∑ w ∈ vertexDisjointRoleWitnesses (k := k) a,
        McDiarmid.weightedMean
          (McDiarmid.bernoulliWeight (retentionProbability q))
          (fun bits ↦ pairRetentionIndicator bits w)) +
      ∑ w ∈ overlappingRoleWitnesses (k := k) a,
        McDiarmid.weightedMean
          (McDiarmid.bernoulliWeight (retentionProbability q))
          (fun bits ↦ pairRetentionIndicator bits w) := by
  rw [weightedMean_pairRoleWitnessStatistic_as_sum]
  rw [← Finset.sum_filter_add_sum_filter_not
    (geometricRoleWitnesses (allTriangleBlocks n k) a)
    (fun w ↦ Disjoint (blockVertices w.leftBlock) (blockVertices w.rightBlock))
    (fun w ↦ McDiarmid.weightedMean
      (McDiarmid.bernoulliWeight (retentionProbability q))
      (fun bits ↦ pairRetentionIndicator bits w))]
  rfl

/-! ### A compressed code for witnesses whose two triangles overlap -/

def leftRoleVertexSlot {n k : ℕ} (a : PairRoleIndex n)
    (w : PairWitness n k) (i : Fin 3) : Fin n :=
  if i = 0 then a.x else if i = 1 then
    (rootBlockCode a.leftRole a.x w.leftBlock).1
  else (rootBlockCode a.leftRole a.x w.leftBlock).2.1

def rightRoleVertexSlot {n k : ℕ} (a : PairRoleIndex n)
    (w : PairWitness n k) (i : Fin 3) : Fin n :=
  if i = 0 then a.y else if i = 1 then
    (rootBlockCode a.rightRole a.y w.rightBlock).1
  else (rootBlockCode a.rightRole a.y w.rightBlock).2.1

theorem meanRootBlockCode_eq_rootBlockCode {n k : ℕ} (r : RootRole)
    (root : Fin n) (b : TriangleBlock n k) :
    meanRootBlockCode r root b = rootBlockCode r root b := by
  cases r <;> rfl

theorem exists_roleVertexSlots_eq_of_overlap {n k : ℕ}
    (a : PairRoleIndex n) (w : PairWitness n k)
    (hw : w ∈ geometricRoleWitnesses (allTriangleBlocks n k) a)
    (hov : ¬Disjoint (blockVertices w.leftBlock) (blockVertices w.rightBlock)) :
    ∃ i j : Fin 3, leftRoleVertexSlot a w i = rightRoleVertexSlot a w j := by
  classical
  simp only [geometricRoleWitnesses, Finset.mem_filter] at hw
  rcases hw with ⟨hw, hrL, hrR⟩
  simp only [geometricWitnesses, Finset.mem_filter, Finset.mem_univ,
    true_and] at hw
  rcases hw with ⟨_, _, _, _, _, _, _, hfitL, hfitR⟩
  have hfitL' : RoleFits a.leftRole w.leftBlock a.x w.common := by
    simpa [PairRoleIndex.toPairTestIndex, hrL] using hfitL
  have hfitR' : RoleFits a.rightRole w.rightBlock a.y w.common := by
    simpa [PairRoleIndex.toPairTestIndex, hrR] using hfitR
  have hsL := meanRootBlockCode_shape a.leftRole a.x w.common w.leftBlock hfitL'
  have hsR := meanRootBlockCode_shape a.rightRole a.y w.common w.rightBlock hfitR'
  rw [meanRootBlockCode_eq_rootBlockCode] at hsL hsR
  rw [Finset.not_disjoint_iff] at hov
  rcases hov with ⟨z, hzL, hzR⟩
  rw [hsL.2.2.2] at hzL
  rw [hsR.2.2.2] at hzR
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzL hzR
  rcases hzL with rfl | hzL | hzL <;>
    rcases hzR with hzR | hzR | hzR
  · exact ⟨0, 0, by simpa [leftRoleVertexSlot, rightRoleVertexSlot] using hzR⟩
  · exact ⟨0, 1, by simpa [leftRoleVertexSlot, rightRoleVertexSlot] using hzR⟩
  · exact ⟨0, 2, by simpa [leftRoleVertexSlot, rightRoleVertexSlot] using hzR⟩
  · exact ⟨1, 0, by simpa [leftRoleVertexSlot, rightRoleVertexSlot] using hzL.symm.trans hzR⟩
  · exact ⟨1, 1, by simpa [leftRoleVertexSlot, rightRoleVertexSlot] using hzL.symm.trans hzR⟩
  · exact ⟨1, 2, by simpa [leftRoleVertexSlot, rightRoleVertexSlot] using hzL.symm.trans hzR⟩
  · exact ⟨2, 0, by simpa [leftRoleVertexSlot, rightRoleVertexSlot] using hzL.symm.trans hzR⟩
  · exact ⟨2, 1, by simpa [leftRoleVertexSlot, rightRoleVertexSlot] using hzL.symm.trans hzR⟩
  · exact ⟨2, 2, by simpa [leftRoleVertexSlot, rightRoleVertexSlot] using hzL.symm.trans hzR⟩

abbrev OverlapCompressedCode (n k : ℕ) :=
  (Fin n × (Fin n × Fin n)) × (Fin k × (Fin k × Fin k))

def overlapCompressedVertices {n k : ℕ} (i j : Fin 3)
    (a : PairRoleIndex n) (w : PairWitness n k) : Fin n × (Fin n × Fin n) :=
  let l := rootBlockCode a.leftRole a.x w.leftBlock
  let r := rootBlockCode a.rightRole a.y w.rightBlock
  if i = 0 then
    if j = 1 then (l.1, (l.2.1, r.2.1)) else (l.1, (l.2.1, r.1))
  else if j = 0 then
    if i = 1 then (l.2.1, (r.1, r.2.1)) else (l.1, (r.1, r.2.1))
  else if i = 1 then
    if j = 1 then (l.1, (l.2.1, r.2.1)) else (l.1, (l.2.1, r.1))
  else
    if j = 1 then (l.1, (l.2.1, r.2.1)) else (l.1, (l.2.1, r.1))

def overlapCompressedCode {n k : ℕ} (i j : Fin 3)
    (a : PairRoleIndex n) (w : PairWitness n k) : OverlapCompressedCode n k :=
  (overlapCompressedVertices i j a w,
    ((rootBlockCode a.leftRole a.x w.leftBlock).2.2,
      ((rootBlockCode a.rightRole a.y w.rightBlock).2.2, w.common)))

theorem overlapCompressedCode_inj_of_slot {n k : ℕ} {a : PairRoleIndex n}
    (hxy : a.x ≠ a.y) (i j : Fin 3) {w w' : PairWitness n k}
    (hw : w ∈ geometricRoleWitnesses (allTriangleBlocks n k) a)
    (hw' : w' ∈ geometricRoleWitnesses (allTriangleBlocks n k) a)
    (hs : leftRoleVertexSlot a w i = rightRoleVertexSlot a w j)
    (hs' : leftRoleVertexSlot a w' i = rightRoleVertexSlot a w' j)
    (hc : overlapCompressedCode i j a w = overlapCompressedCode i j a w') :
    w = w' := by
  apply roleWitnessCode_inj_of_mem hw hw'
  have hv1 := congrArg (fun z ↦ z.1.1) hc
  have hv2 := congrArg (fun z ↦ z.1.2.1) hc
  have hv3 := congrArg (fun z ↦ z.1.2.2) hc
  have hleftColour := congrArg (fun z ↦ z.2.1) hc
  have hrightColour := congrArg (fun z ↦ z.2.2.1) hc
  have hcommon := congrArg (fun z ↦ z.2.2.2) hc
  simp only [overlapCompressedCode] at hleftColour hrightColour hcommon
  have mkCodeEq (c c' : RootBlockCode n k)
      (h1 : c.1 = c'.1) (h2 : c.2.1 = c'.2.1)
      (h3 : c.2.2 = c'.2.2) : c = c' := by
    rcases c with ⟨u, v, d⟩
    rcases c' with ⟨u', v', d'⟩
    simp_all
  simp only [roleWitnessCode, Prod.mk.injEq]
  fin_cases i <;> fin_cases j <;>
    simp only [leftRoleVertexSlot, rightRoleVertexSlot, Fin.zero_eta,
      OfNat.ofNat, ↓reduceIte] at hs hs' <;>
    simp only [overlapCompressedCode, overlapCompressedVertices, Fin.zero_eta,
      OfNat.ofNat, ↓reduceIte] at hv1 hv2 hv3
  · exact False.elim (hxy hs)
  · exact ⟨mkCodeEq _ _ hv1 hv2 hleftColour,
      mkCodeEq _ _ (hs.symm.trans hs') hv3 hrightColour, hcommon⟩
  · exact ⟨mkCodeEq _ _ hv1 hv2 hleftColour,
      mkCodeEq _ _ hv3 (hs.symm.trans hs') hrightColour, hcommon⟩
  · exact ⟨mkCodeEq _ _ (hs.trans hs'.symm) hv1 hleftColour,
      mkCodeEq _ _ hv2 hv3 hrightColour, hcommon⟩
  · exact ⟨mkCodeEq _ _ hv1 hv2 hleftColour,
      mkCodeEq _ _ (hs.symm.trans (hv1.trans hs')) hv3 hrightColour, hcommon⟩
  · exact ⟨mkCodeEq _ _ hv1 hv2 hleftColour,
      mkCodeEq _ _ hv3 (hs.symm.trans (hv1.trans hs')) hrightColour, hcommon⟩
  · exact ⟨mkCodeEq _ _ hv1 (hs.trans hs'.symm) hleftColour,
      mkCodeEq _ _ hv2 hv3 hrightColour, hcommon⟩
  · exact ⟨mkCodeEq _ _ hv1 hv2 hleftColour,
      mkCodeEq _ _ (hs.symm.trans (hv2.trans hs')) hv3 hrightColour, hcommon⟩
  · exact ⟨mkCodeEq _ _ hv1 hv2 hleftColour,
      mkCodeEq _ _ hv3 (hs.symm.trans (hv2.trans hs')) hrightColour, hcommon⟩

noncomputable def overlapSlotPair {n k : ℕ} (a : PairRoleIndex n)
    (w : {w : PairWitness n k // w ∈ overlappingRoleWitnesses (k := k) a}) :
    Fin 3 × Fin 3 := by
  have hm := (Finset.mem_filter.mp w.2)
  let hex := exists_roleVertexSlots_eq_of_overlap a w.1 hm.1 hm.2
  let i := Classical.choose hex
  let j := Classical.choose (Classical.choose_spec hex)
  exact (i, j)

theorem overlapSlotPair_spec {n k : ℕ} (a : PairRoleIndex n)
    (w : {w : PairWitness n k // w ∈ overlappingRoleWitnesses (k := k) a}) :
    leftRoleVertexSlot a w.1 (overlapSlotPair a w).1 =
      rightRoleVertexSlot a w.1 (overlapSlotPair a w).2 := by
  classical
  have hm := (Finset.mem_filter.mp w.2)
  let hex := exists_roleVertexSlots_eq_of_overlap a w.1 hm.1 hm.2
  exact Classical.choose_spec (Classical.choose_spec hex)

abbrev MarkedOverlapCode (n k : ℕ) :=
  (Fin 3 × Fin 3) × OverlapCompressedCode n k

noncomputable def markedOverlapCode {n k : ℕ} (a : PairRoleIndex n)
    (w : {w : PairWitness n k // w ∈ overlappingRoleWitnesses (k := k) a}) :
    MarkedOverlapCode n k :=
  (overlapSlotPair a w,
    overlapCompressedCode (overlapSlotPair a w).1 (overlapSlotPair a w).2 a w.1)

theorem markedOverlapCode_injective {n k : ℕ} (a : PairRoleIndex n)
    (hxy : a.x ≠ a.y) : Function.Injective (markedOverlapCode (k := k) a) := by
  intro w w' hc
  apply Subtype.ext
  have hp : overlapSlotPair a w = overlapSlotPair a w' := congrArg Prod.fst hc
  have hc' : overlapCompressedCode (overlapSlotPair a w).1
      (overlapSlotPair a w).2 a w.1 =
      overlapCompressedCode (overlapSlotPair a w').1
        (overlapSlotPair a w').2 a w'.1 := congrArg Prod.snd hc
  rw [← hp] at hc'
  apply overlapCompressedCode_inj_of_slot hxy
      (overlapSlotPair a w).1 (overlapSlotPair a w).2
      (Finset.mem_filter.mp w.2).1 (Finset.mem_filter.mp w'.2).1
      (overlapSlotPair_spec a w)
      (by simpa [hp] using overlapSlotPair_spec a w') hc'

theorem card_overlappingRoleWitnesses_le {n k : ℕ} (a : PairRoleIndex n)
    (hxy : a.x ≠ a.y) :
    (overlappingRoleWitnesses (k := k) a).card ≤ 9 * n ^ 3 * k ^ 3 := by
  calc
    _ = Fintype.card {w : PairWitness n k //
        w ∈ overlappingRoleWitnesses (k := k) a} := by simp
    _ ≤ Fintype.card (MarkedOverlapCode n k) :=
      Fintype.card_le_of_injective (markedOverlapCode (k := k) a)
        (markedOverlapCode_injective (k := k) a hxy)
    _ = 9 * n ^ 3 * k ^ 3 := by
      simp only [MarkedOverlapCode, OverlapCompressedCode,
        Fintype.card_prod, Fintype.card_fin]
      ring

/-- Retained witnesses whose two underlying triangles share a vertex.  This
is the complete lower-order family that must be discarded when a tracked
cross slot additionally requires its prospective covering key to be fresh
from the two-edge owner. -/
def retainedOverlappingRoleWitnesses {n k : ℕ}
    (R : RetainedLabels n k) (a : PairRoleIndex n) :
    Finset (PairWitness n k) :=
  (pairRoleWitnesses (allTriangleBlocks n k) R a).filter fun w ↦
    ¬Disjoint (blockVertices w.leftBlock) (blockVertices w.rightBlock)

theorem retainedOverlappingRoleWitnesses_subset {n k : ℕ}
    (R : RetainedLabels n k) (a : PairRoleIndex n) :
    retainedOverlappingRoleWitnesses R a ⊆
      overlappingRoleWitnesses (k := k) a := by
  classical
  intro w hw
  have hw' := Finset.mem_filter.mp hw
  have hrole := Finset.mem_filter.mp hw'.1
  exact Finset.mem_filter.mpr ⟨hrole.1, hw'.2⟩

theorem card_retainedOverlappingRoleWitnesses_le {n k : ℕ}
    (R : RetainedLabels n k) (a : PairRoleIndex n) :
    (retainedOverlappingRoleWitnesses R a).card ≤
      9 * n ^ 3 * k ^ 3 := by
  exact (Finset.card_le_card
    (retainedOverlappingRoleWitnesses_subset R a)).trans
      (card_overlappingRoleWitnesses_le a a.x_ne_y)

theorem card_retainedOverlappingRoleWitnesses_le_n6 {n k : ℕ}
    (R : RetainedLabels n k) (a : PairRoleIndex n) (hk : k ≤ n) :
    (retainedOverlappingRoleWitnesses R a).card ≤ 9 * n ^ 6 := by
  exact (card_retainedOverlappingRoleWitnesses_le R a).trans (by
    calc
      9 * n ^ 3 * k ^ 3 = 9 * (n ^ 3 * k ^ 3) := by ring
      _ ≤ 9 * (n ^ 3 * n ^ 3) :=
        Nat.mul_le_mul_left 9
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk 3))
      _ = 9 * n ^ 6 := by ring)

theorem sum_weightedMean_overlappingRoleWitnesses_mem_Icc {n k : ℕ}
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (a : PairRoleIndex n) :
    (∑ w ∈ overlappingRoleWitnesses (k := k) a,
      McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability q))
        (fun bits ↦ pairRetentionIndicator bits w)) ∈
      Set.Icc (0 : ℝ) (overlappingRoleWitnesses (k := k) a).card := by
  constructor
  · exact Finset.sum_nonneg fun w hw ↦
      (weightedMean_pairRetentionIndicator_mem_Icc q hq w).1
  · calc
      _ ≤ ∑ _w ∈ overlappingRoleWitnesses (k := k) a, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro w hw
        exact (weightedMean_pairRetentionIndicator_mem_Icc q hq w).2
      _ = (overlappingRoleWitnesses (k := k) a).card := by simp

theorem sum_weightedMean_overlappingRoleWitnesses_le {n k : ℕ}
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (a : PairRoleIndex n)
    (hxy : a.x ≠ a.y) (hkn : k ≤ n) :
    (∑ w ∈ overlappingRoleWitnesses (k := k) a,
      McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability q))
        (fun bits ↦ pairRetentionIndicator bits w)) ≤ 9 * (n : ℝ) ^ 6 := by
  have hcard := card_overlappingRoleWitnesses_le (k := k) a hxy
  have hcardR : ((overlappingRoleWitnesses (k := k) a).card : ℝ) ≤
      ((9 * n ^ 3 * k ^ 3 : ℕ) : ℝ) := by exact_mod_cast hcard
  calc
    _ ≤ ((overlappingRoleWitnesses (k := k) a).card : ℝ) :=
      (sum_weightedMean_overlappingRoleWitnesses_mem_Icc q hq a).2
    _ ≤ ((9 * n ^ 3 * k ^ 3 : ℕ) : ℝ) := hcardR
    _ ≤ 9 * (n : ℝ) ^ 6 := by
      push_cast
      have hkR : (k : ℝ) ≤ n := by exact_mod_cast hkn
      have hk0 : (0 : ℝ) ≤ k := by positivity
      have hk3 := pow_le_pow_left₀ hk0 hkR 3
      calc
        9 * (n : ℝ) ^ 3 * (k : ℝ) ^ 3 ≤
            9 * (n : ℝ) ^ 3 * (n : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_left hk3 (by positivity)
        _ = 9 * (n : ℝ) ^ 6 := by ring

theorem pairRoleDisjointCount_leading_error_all {n k : ℕ}
    (hn : 6 ≤ n) (hkn : k ≤ n) (a : PairRoleIndex n) :
    let T := roleLeadingCoefficient a.leftRole *
      roleLeadingCoefficient a.rightRole * (k : ℝ) ^ 3 * (n : ℝ) ^ 4
    0 ≤ T - (pairRoleDisjointCount k a : ℝ) ∧
      T - (pairRoleDisjointCount k a : ℝ) ≤ 16 * (n : ℝ) ^ 6 := by
  by_cases hk0 : k = 0
  · subst k
    simp [pairRoleDisjointCount]
  · exact pairRoleDisjointCount_leading_error hn
      (Nat.one_le_iff_ne_zero.mpr hk0) hkn a

theorem weightedMean_stabilizedPairRole_universal_error {n k : ℕ}
    (hn : 6 ≤ n) (hkn : k ≤ n) (q : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (a : PairRoleIndex n) :
    |McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ stabilizedPairRoleStatistic (allTriangleBlocks n k)
          (pairRoleTarget k q) bits a) - pairRoleTarget k q a| ≤
      65 * (n : ℝ) ^ 6 := by
  let main : ℝ := (pairRoleDisjointCount k a : ℝ) * q ^ 10 * (1 - q) ^ 2
  let rem : ℝ := ∑ w ∈ overlappingRoleWitnesses (k := k) a,
    McDiarmid.weightedMean
      (McDiarmid.bernoulliWeight (retentionProbability q))
      (fun bits ↦ pairRetentionIndicator bits w)
  let leading : ℝ := roleLeadingCoefficient a.leftRole *
    roleLeadingCoefficient a.rightRole * (k : ℝ) ^ 3 * (n : ℝ) ^ 4
  let factor : ℝ := q ^ 10 * (1 - q) ^ 2
  have hq10_0 : 0 ≤ q ^ 10 := pow_nonneg hq.1 _
  have hq10_1 : q ^ 10 ≤ 1 := by
    simpa using pow_le_pow_left₀ hq.1 hq.2 10
  have hp0 : 0 ≤ 1 - q := sub_nonneg.mpr hq.2
  have hp1 : 1 - q ≤ 1 := sub_le_self 1 hq.1
  have hp2_0 : 0 ≤ (1 - q) ^ 2 := pow_nonneg hp0 _
  have hp2_1 : (1 - q) ^ 2 ≤ 1 := by
    simpa using pow_le_pow_left₀ hp0 hp1 2
  have hfactor0 : 0 ≤ factor := mul_nonneg hq10_0 hp2_0
  have hfactor1 : factor ≤ 1 := by
    dsimp [factor]
    calc
      q ^ 10 * (1 - q) ^ 2 ≤ 1 * 1 :=
        mul_le_mul hq10_1 hp2_1 hp2_0 (by norm_num)
      _ = 1 := by ring
  have hlead := pairRoleDisjointCount_leading_error_all hn hkn a
  have htarget : pairRoleTarget k q a = leading * factor := by
    rw [pairRoleTarget, leftCoefficient_eq_roleLeadingCoefficient,
      rightCoefficient_eq_roleLeadingCoefficient]
    dsimp [leading, factor]
    ring
  have hmain : main = (pairRoleDisjointCount k a : ℝ) * factor := by
    dsimp [main, factor]
    ring
  have hmainGap0 : 0 ≤ pairRoleTarget k q a - main := by
    rw [htarget, hmain]
    rw [show leading * factor - (pairRoleDisjointCount k a : ℝ) * factor =
      (leading - (pairRoleDisjointCount k a : ℝ)) * factor by ring]
    exact mul_nonneg hlead.1 hfactor0
  have hmainGapLe : pairRoleTarget k q a - main ≤ 16 * (n : ℝ) ^ 6 := by
    rw [htarget, hmain]
    rw [show leading * factor - (pairRoleDisjointCount k a : ℝ) * factor =
      (leading - (pairRoleDisjointCount k a : ℝ)) * factor by ring]
    calc
      _ ≤ (16 * (n : ℝ) ^ 6) * 1 :=
        mul_le_mul hlead.2 hfactor1 hfactor0 (by positivity)
      _ = 16 * (n : ℝ) ^ 6 := by ring
  have hrem0 : 0 ≤ rem :=
    (sum_weightedMean_overlappingRoleWitnesses_mem_Icc q hq a).1
  have hremLe : rem ≤ 9 * (n : ℝ) ^ 6 :=
    sum_weightedMean_overlappingRoleWitnesses_le q hq a a.x_ne_y hkn
  have hraw :
      McDiarmid.weightedMean
        (McDiarmid.bernoulliWeight (retentionProbability (n := n) (k := k) q))
        (fun bits ↦ pairRoleWitnessStatistic (allTriangleBlocks n k) bits a) =
      main + rem := by
    rw [weightedMean_pairRoleWitnessStatistic_split,
      sum_weightedMean_vertexDisjointRoleWitnesses q a a.x_ne_y]
  rw [show (fun bits ↦ stabilizedPairRoleStatistic (allTriangleBlocks n k)
      (pairRoleTarget k q) bits a) =
      (fun bits ↦ pairRoleWitnessStatistic (allTriangleBlocks n k) bits a) by
        funext bits
        simp [stabilizedPairRoleStatistic, a.x_ne_y]]
  rw [hraw]
  calc
    |main + rem - pairRoleTarget k q a| =
        |rem - (pairRoleTarget k q a - main)| := by congr 1 <;> ring
    _ ≤ |rem| + |pairRoleTarget k q a - main| := abs_sub _ _
    _ = rem + (pairRoleTarget k q a - main) := by
      rw [abs_of_nonneg hrem0, abs_of_nonneg hmainGap0]
    _ ≤ 9 * (n : ℝ) ^ 6 + 16 * (n : ℝ) ^ 6 :=
      add_le_add hremLe hmainGapLe
    _ ≤ 65 * (n : ℝ) ^ 6 := by
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ n by positivity) 6]

/-! ## Closed universal extraction and Joos--Mubayi specialization -/

/-- The universal candidate family admits a retained-label outcome satisfying
all degree, same-colour codegree, and distinct-root role-test estimates once
the explicit finite tail bound is below one.  Unlike the generic extraction
lemma, this statement has no mean, influence, or union-array hypotheses. -/
theorem exists_universal_retained_host {n k : ℕ}
    (hn : 6 ≤ n) (hk0 : 1 ≤ k) (hk : k ≤ n)
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (htail : universalTailBound n < 1) :
    ∃ R : RetainedLabels n k, UniversalRetainedHostEstimates q R := by
  have hbudget :=
    (universal_union_tail_le (show 1 ≤ n by omega) hk0 hk).trans_lt htail
  obtain ⟨R, hdegree, hcodegree, hpair⟩ :=
    exists_retainedLabels_with_estimates
      (allTriangleBlocks n k) q hq
      (universalDegreeTarget n k q) (fun _ ↦ 0)
        (universalDegreeDeviation n)
      (universalSameColorTarget n k q) (fun _ ↦ 0)
        (universalCodegreeDeviation n)
      (pairRoleTarget k q) (universalPairRoleMeanError n)
        (universalPairRoleDeviation n)
      safeDegreeInfluence safeCodegreeInfluence safePairRoleInfluence
      (fun v ↦ by
        rw [weightedMean_stabilizedDegree_universal]
        simp)
      (fun a ↦ by
        rw [weightedMean_stabilizedSameColor_universal]
        simp)
      (weightedMean_stabilizedPairRole_universal_error hn hk q hq)
      (fun v i ↦ safeInfluence_nonneg _ _)
      (fun a i ↦ safeInfluence_nonneg _ _)
      (fun a i ↦ safeInfluence_nonneg _ _)
      (fun v i x y hxy ↦ safeDegree_boundedDiff _ v i x y hxy)
      (fun a i x y hxy ↦ safeCodegree_boundedDiff _ a i x y hxy)
      (fun a i x y hxy ↦ safePairRole_boundedDiff _ a i x y hxy)
      (fun _ ↦ by unfold universalDegreeDeviation; positivity)
      (fun _ ↦ by unfold universalCodegreeDeviation; positivity)
      (fun _ ↦ by unfold universalPairRoleDeviation; positivity)
      hbudget
  refine ⟨R, universalRetainedHostEstimates_of_near ?_ ?_ ?_⟩
  · simpa using hdegree
  · simpa using hcodegree
  · simpa using hpair

/-- Closed large-`n` biased-retention theorem at the paper's actual present
bit probability `jmDeletion = 1/(1+rho)` and ceiling-rounded old palette.
Every finite expectation, influence, and tail estimate is discharged inside
the theorem. -/
theorem eventually_exists_joosMubayi_retained_host
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ R : RetainedLabels n (jmOldColors delta n),
        UniversalRetainedHostEstimates (jmDeletion delta n) R := by
  obtain ⟨n₀, htail⟩ := eventually_universalTailBound_lt_one
  filter_upwards [eventually_jmOldColors_le_n hdelta,
    eventually_one_le_jmOldColors delta,
    Filter.eventually_ge_atTop (max n₀ 6)] with n hk hk0 hn
  have hn0 : n₀ ≤ n := (Nat.le_max_left _ _).trans hn
  have hn6 : 6 ≤ n := (Nat.le_max_right _ _).trans hn
  exact exists_universal_retained_host hn6 hk0 hk
    (jmDeletion delta n)
    (jmDeletion_mem_Icc (lt_of_lt_of_le (by omega) hn6))
    (htail n hn0)

/-- The two pair-codegree scales needed downstream are deliberately kept
separate.  Arbitrary pairs of auxiliary vertices have the deterministic
ambient bound `6 n²`, whereas pairs of retained labels in one old colour
enjoy the sharper `5 n^(2-δ)` ceiling supplied by concentration. -/
def UniversalRetainedHostCodegreeBounds {n : ℕ} (delta : ℝ)
    (R : RetainedLabels n (jmOldColors delta n)) : Prop :=
  MaxCodegreeLE
      (auxiliaryHypergraph (allTriangleBlocks n (jmOldColors delta n)) R)
      2 (6 * n ^ 2) ∧
    ∀ (a : SameColorIndex n (jmOldColors delta n)),
      a.left ≠ a.right →
      (a.left, a.color) ∈ R → (a.right, a.color) ∈ R →
      codegree
          (auxiliaryHypergraph
            (allTriangleBlocks n (jmOldColors delta n)) R)
          {Sum.inr (a.left, a.color), Sum.inr (a.right, a.color)} ≤
        jmPairCodegreeCeil 5 0 delta n

/-- Closed retained-host extraction with both the ambient host codegree and
the sharper same-colour paint-fibre input.  The upper restriction
`δ < 1/3` is exactly what absorbs the `n^(5/3)` concentration deviation
into `n^(2-δ)`; the Joos--Mubayi parameter `jmDelta` satisfies it. -/
theorem eventually_exists_joosMubayi_retained_host_with_codegree_bounds
    {delta : ℝ} (hdelta0 : 0 < delta) (hdeltaThird : delta < 1 / 3) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ R : RetainedLabels n (jmOldColors delta n),
        UniversalRetainedHostEstimates (jmDeletion delta n) R ∧
          UniversalRetainedHostCodegreeBounds delta R := by
  filter_upwards [eventually_exists_joosMubayi_retained_host hdelta0,
    eventually_universal_sameColor_codegree_le_ceiling hdelta0 hdeltaThird,
    eventually_jmOldColors_le hdelta0] with n hexists hlocal hk
  obtain ⟨R, hhost⟩ := hexists
  refine ⟨R, hhost, universal_auxiliary_maxCodegree hk R, ?_⟩
  exact hlocal R hhost

/-! ## Arithmetic for the common retained-host degree -/

/-- The real old-palette size and the Bernoulli present probability cancel
exactly.  This identity is the finite source of the `5n/6` leading term. -/
theorem jmOldPaletteReal_mul_deletion (delta : ℝ) (n : ℕ) :
    jmOldPaletteReal delta n * jmDeletion delta n = (5 / 6 : ℝ) * n := by
  have hr : 0 ≤ jmRho delta n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hden : 1 + jmRho delta n ≠ 0 := by positivity
  unfold jmOldPaletteReal jmDeletion
  field_simp [hden]

/-- Algebraic form of the difference between the two universal degree
centres. -/
theorem universalGraph_sub_label_formula {n k : ℕ} {q : ℝ}
    (hn : 2 ≤ n) (hk : 1 ≤ k) :
    universalGraphDegreeTarget n k q - universalLabelDegreeTarget n k q =
      ((k - 1 : ℕ) : ℝ) * q ^ 4 * (1 - q) * (n - 2 : ℕ) *
        (3 * (k : ℝ) * q - (5 / 2 : ℝ) * (n - 1 : ℕ)) := by
  unfold universalGraphDegreeTarget universalLabelDegreeTarget
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_choose_two]
  rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub hn,
    Nat.cast_sub hk]
  ring

/-- Ceiling the old palette perturbs its cancellation with the present-bit
probability by at most one. -/
theorem abs_jmOldColors_mul_deletion_sub (delta : ℝ) (n : ℕ) :
    |(jmOldColors delta n : ℝ) * jmDeletion delta n -
        (5 / 6 : ℝ) * n| ≤ 1 := by
  have hq0 : 0 ≤ jmDeletion delta n := by
    unfold jmDeletion
    have hr : 0 ≤ jmRho delta n := Real.rpow_nonneg (Nat.cast_nonneg n) _
    positivity
  have hlower : (5 / 6 : ℝ) * n ≤
      (jmOldColors delta n : ℝ) * jmDeletion delta n := by
    rw [← jmOldPaletteReal_mul_deletion]
    exact mul_le_mul_of_nonneg_right
      (jmOldPaletteReal_le_colors delta n) hq0
  have hupper : (jmOldColors delta n : ℝ) * jmDeletion delta n ≤
      (5 / 6 : ℝ) * n + 1 := by
    have hk := jmOldColors_lt_add_one delta n
    have hmul := mul_le_mul_of_nonneg_right hk.le hq0
    rw [add_mul, jmOldPaletteReal_mul_deletion] at hmul
    have hq1 : jmDeletion delta n ≤ 1 := by
      unfold jmDeletion
      have hr : 0 ≤ jmRho delta n := Real.rpow_nonneg (Nat.cast_nonneg n) _
      exact (div_le_one (by positivity)).2 (by linarith)
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- The two exact universal degree centres differ only by a quadratic
ceiling error. -/
theorem universalGraph_label_difference_le {delta : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hk : jmOldColors delta n ≤ n) :
    |universalGraphDegreeTarget n (jmOldColors delta n) (jmDeletion delta n) -
        universalLabelDegreeTarget n (jmOldColors delta n) (jmDeletion delta n)| ≤
      6 * (n : ℝ) ^ 2 := by
  let k := jmOldColors delta n
  let q := jmDeletion delta n
  have hk0 : 1 ≤ k := by
    dsimp [k]
    have holdpos : 0 < jmOldPaletteReal delta n := by
      unfold jmOldPaletteReal
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hr : 0 ≤ jmRho delta n := Real.rpow_nonneg (Nat.cast_nonneg n) _
      positivity
    exact Nat.one_le_ceil_iff.mpr holdpos
  have hq0 : 0 ≤ q := by
    dsimp [q, jmDeletion]
    have hr : 0 ≤ jmRho delta n := Real.rpow_nonneg (Nat.cast_nonneg n) _
    positivity
  have hq1 : q ≤ 1 := by
    dsimp [q, jmDeletion]
    have hr : 0 ≤ jmRho delta n := Real.rpow_nonneg (Nat.cast_nonneg n) _
    exact (div_le_one (by positivity)).2 (by linarith)
  have hq4 : q ^ 4 ≤ 1 := pow_le_one₀ hq0 hq1
  have h1mq : 1 - q ≤ 1 := by linarith
  have hkR : ((k - 1 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast (Nat.sub_le k 1 |>.trans hk)
  have hn2R : ((n - 2 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast Nat.sub_le n 2
  have hA0 : 0 ≤ ((k - 1 : ℕ) : ℝ) * q ^ 4 * (1 - q) * (n - 2 : ℕ) := by
    positivity
  have hA : ((k - 1 : ℕ) : ℝ) * q ^ 4 * (1 - q) * (n - 2 : ℕ) ≤
      (n : ℝ) ^ 2 := by
    calc
      ((k - 1 : ℕ) : ℝ) * q ^ 4 * (1 - q) * (n - 2 : ℕ) ≤
          (n : ℝ) * 1 * 1 * n := by gcongr
      _ = (n : ℝ) ^ 2 := by ring
  have hbase := abs_jmOldColors_mul_deletion_sub delta n
  change |(k : ℝ) * q - (5 / 6 : ℝ) * n| ≤ 1 at hbase
  have hB : |3 * (k : ℝ) * q - (5 / 2 : ℝ) * (n - 1 : ℕ)| ≤ 6 := by
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [hn1]
    have heq : 3 * (k : ℝ) * q - (5 / 2 : ℝ) * ((n : ℝ) - 1) =
        3 * ((k : ℝ) * q - (5 / 6 : ℝ) * n) + 5 / 2 := by ring
    rw [heq]
    calc
      |3 * ((k : ℝ) * q - (5 / 6 : ℝ) * n) + 5 / 2| ≤
          |3 * ((k : ℝ) * q - (5 / 6 : ℝ) * n)| + |(5 / 2 : ℝ)| :=
        abs_add_le _ _
      _ = 3 * |(k : ℝ) * q - (5 / 6 : ℝ) * n| + 5 / 2 := by
        rw [abs_mul]
        norm_num
      _ ≤ 6 := by nlinarith
  rw [universalGraph_sub_label_formula hn hk0]
  rw [abs_mul, abs_of_nonneg hA0]
  calc
    ((k - 1 : ℕ) : ℝ) * q ^ 4 * (1 - q) * (n - 2 : ℕ) *
        |3 * (k : ℝ) * q - 5 / 2 * (n - 1 : ℕ)| ≤
        (n : ℝ) ^ 2 * 6 := by gcongr
    _ = 6 * (n : ℝ) ^ 2 := by ring

/-- The spread-and-deviation loss in the common host-degree window is at
most `8 n^(8/3)`. -/
theorem universalHostDegreeError_le_eight_rpow {delta : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hk : jmOldColors delta n ≤ n) :
    universalHostDegreeError n (jmOldColors delta n) (jmDeletion delta n) ≤
      8 * (n : ℝ) ^ (8 / 3 : ℝ) := by
  have hdiff := universalGraph_label_difference_le (delta := delta) hn hk
  have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (8 / 3 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
  unfold universalHostDegreeError
  rw [max_sub_min_eq_abs, abs_sub_comm]
  linarith

private theorem mul_factor_le_add {A B E t : ℝ}
    (hAB : A ≤ B + E) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hE0 : 0 ≤ E) :
    A * t ≤ B * t + E := by
  calc
    A * t ≤ (B + E) * t := mul_le_mul_of_nonneg_right hAB ht0
    _ = B * t + E * t := by ring
    _ ≤ B * t + E := add_le_add_right (mul_le_of_le_one_right hE0 ht1) _

/-- The paper's analytic degree centre is below the exact labelled-vertex
centre up to an explicit quadratic ceiling error. -/
theorem jmAuxDegreeReal_le_label_add_ten_sq {delta : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hk : jmOldColors delta n ≤ n) :
    jmAuxDegreeReal delta n ≤
      universalLabelDegreeTarget n (jmOldColors delta n) (jmDeletion delta n) +
        10 * (n : ℝ) ^ 2 := by
  let k := jmOldColors delta n
  let q := jmDeletion delta n
  let r := jmOldPaletteReal delta n
  let m : ℝ := (k - 1 : ℕ)
  have hk0 : 1 ≤ k := by
    dsimp [k]
    have holdpos : 0 < jmOldPaletteReal delta n := by
      unfold jmOldPaletteReal
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hrho : 0 ≤ jmRho delta n := Real.rpow_nonneg (Nat.cast_nonneg n) _
      positivity
    exact Nat.one_le_ceil_iff.mpr holdpos
  have hk_eq : (k : ℝ) = m + 1 := by
    dsimp [m]
    rw [Nat.cast_sub hk0]
    norm_num
  have hrle : r ≤ m + 1 := by
    rw [← hk_eq]
    exact jmOldPaletteReal_le_colors delta n
  have hm0 : 0 ≤ m := by positivity
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact jmOldPaletteReal_nonneg delta n
  have hmle : m ≤ n := by
    dsimp [m]
    exact_mod_cast (Nat.sub_le k 1 |>.trans hk)
  have hcoef :
      (5 / 2 : ℝ) * (n : ℝ) ^ 2 * r ≤
        5 * ((n - 1).choose 2 : ℕ) * m + 10 * (n : ℝ) ^ 2 := by
    let N : ℝ := n
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    have hn2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
      rw [Nat.cast_sub hn]
      norm_num
    have hN0 : 0 ≤ N := by positivity
    have hnm : N * m ≤ N ^ 2 := by
      calc
        N * m ≤ N * N := mul_le_mul_of_nonneg_left hmle hN0
        _ = N ^ 2 := by ring
    have hbase : N ^ 2 ≤ (N - 1) * (N - 2) + 3 * N := by
      nlinarith [sq_nonneg (N - 1)]
    have hmul := mul_le_mul_of_nonneg_right hbase hm0
    have hthree : 3 * (N * m) ≤ 3 * N ^ 2 :=
      mul_le_mul_of_nonneg_left hnm (by norm_num)
    have hgap : N ^ 2 * m ≤
        (N - 1) * (N - 2) * m + 3 * N ^ 2 := by
      calc
        N ^ 2 * m ≤ ((N - 1) * (N - 2) + 3 * N) * m := hmul
        _ = (N - 1) * (N - 2) * m + 3 * (N * m) := by ring
        _ ≤ (N - 1) * (N - 2) * m + 3 * N ^ 2 :=
          add_le_add_right hthree _
    have hrscaled : (5 / 2 : ℝ) * N ^ 2 * r ≤
        (5 / 2 : ℝ) * N ^ 2 * (m + 1) := by gcongr
    have hchoose : (5 : ℝ) * ((n - 1).choose 2 : ℕ) * m =
        (5 / 2 : ℝ) * (N - 1) * (N - 2) * m := by
      norm_num only [Nat.cast_choose_two]
      rw [hn1]
      dsimp [N]
      ring
    calc
      (5 / 2 : ℝ) * N ^ 2 * r ≤
          (5 / 2 : ℝ) * N ^ 2 * (m + 1) := hrscaled
      _ = (5 / 2 : ℝ) * (N ^ 2 * m + N ^ 2) := by ring
      _ ≤ (5 / 2 : ℝ) *
          ((N - 1) * (N - 2) * m + 3 * N ^ 2 + N ^ 2) := by
        gcongr
      _ = 5 * ((n - 1).choose 2 : ℕ) * m + 10 * N ^ 2 := by
        rw [hchoose]
        ring
  have hq0 : 0 ≤ q := by
    dsimp [q, jmDeletion]
    have hrho : 0 ≤ jmRho delta n := Real.rpow_nonneg (Nat.cast_nonneg n) _
    positivity
  have hq1 : q ≤ 1 := by
    dsimp [q, jmDeletion]
    have hrho : 0 ≤ jmRho delta n := Real.rpow_nonneg (Nat.cast_nonneg n) _
    exact (div_le_one (by positivity)).2 (by linarith)
  have ht0 : 0 ≤ q ^ 4 * (1 - q) := by positivity
  have ht1 : q ^ 4 * (1 - q) ≤ 1 := by
    have hq4 : q ^ 4 ≤ 1 := pow_le_one₀ hq0 hq1
    have h1mq : 1 - q ≤ 1 := by linarith
    calc
      q ^ 4 * (1 - q) ≤ 1 * 1 := by gcongr
      _ = 1 := by ring
  have hproduct := mul_factor_le_add hcoef ht0 ht1
    (by positivity : 0 ≤ 10 * (n : ℝ) ^ 2)
  dsimp only [r, q, m] at hproduct
  have hret : jmRetention delta n = 1 - jmDeletion delta n := by
    linarith [jmRetention_add_deletion (delta := delta) (by omega : 0 < n)]
  unfold jmAuxDegreeReal universalLabelDegreeTarget
  rw [hret]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  simpa only [mul_assoc] using hproduct

/-- Eventually the analytic central degree is below the common degree used
for the retained host. -/
theorem eventually_jmAuxDegreeReal_le_universalHostDegree
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in Filter.atTop,
      jmAuxDegreeReal delta n ≤
        universalHostDegree n (jmOldColors delta n) (jmDeletion delta n) := by
  filter_upwards [eventually_jmOldColors_le hdelta,
    eventually_const_mul_rpow_le_rpow (C := (10 : ℝ))
      (a := (2 : ℝ)) (b := (8 / 3 : ℝ)) (by norm_num) (by norm_num),
    Filter.eventually_ge_atTop (2 : ℕ)] with n hk hpow hn
  have hbase := jmAuxDegreeReal_le_label_add_ten_sq hn hk
  have hpow' : 10 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (8 / 3 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact hpow
  unfold universalHostDegree
  calc
    jmAuxDegreeReal delta n ≤
        universalLabelDegreeTarget n (jmOldColors delta n) (jmDeletion delta n) +
          10 * (n : ℝ) ^ 2 := hbase
    _ ≤ universalLabelDegreeTarget n (jmOldColors delta n) (jmDeletion delta n) +
          (n : ℝ) ^ (8 / 3 : ℝ) := add_le_add_right hpow' _
    _ ≤ max
          (universalGraphDegreeTarget n (jmOldColors delta n) (jmDeletion delta n))
          (universalLabelDegreeTarget n (jmOldColors delta n) (jmDeletion delta n)) +
          (n : ℝ) ^ (8 / 3 : ℝ) := by gcongr; exact le_max_right _ _

/-- The common retained-host degree eventually dominates any prescribed
finite threshold. -/
theorem eventually_universalHostDegree_ge {delta d₀ : ℝ}
    (hdelta0 : 0 < delta) (hdelta3 : delta < 3) :
    ∀ᶠ n : ℕ in Filter.atTop,
      d₀ ≤ universalHostDegree n (jmOldColors delta n) (jmDeletion delta n) := by
  filter_upwards [eventually_jmAuxDegreeReal_ge (d0 := d₀) hdelta0 hdelta3,
    eventually_jmAuxDegreeReal_le_universalHostDegree hdelta0] with n hge hle
  exact hge.trans hle

theorem jm_host_error_exponent_gap {eta₀ : ℝ} (heta₀ : 0 < eta₀) :
    (8 / 3 : ℝ) <
      (3 - jmDelta eta₀) * (1 - jmEta eta₀) := by
  have hd0 := (jmDelta_pos heta₀).le
  have hd := jmDelta_le_one_ten_thousandth eta₀
  have he0 := (jmEta_pos heta₀).le
  have he : jmEta eta₀ ≤ (1 / 100 : ℝ) := min_le_right _ _
  nlinarith [mul_nonneg hd0 he0]

/-- The entire common degree-window loss is eventually swallowed by the
`d^(1-eta)` error permitted by conflict-free matching. -/
theorem eventually_universalHostDegreeError_le_rpow
    {eta₀ : ℝ} (heta₀ : 0 < eta₀) :
    ∀ᶠ n : ℕ in Filter.atTop,
      universalHostDegreeError n (jmOldColors (jmDelta eta₀) n)
          (jmDeletion (jmDelta eta₀) n) ≤
        (universalHostDegree n (jmOldColors (jmDelta eta₀) n)
          (jmDeletion (jmDelta eta₀) n)) ^ (1 - jmEta eta₀) := by
  have hb : 0 ≤ 1 - jmEta eta₀ := (jmEta_lt_one heta₀).le |> sub_nonneg.mpr
  filter_upwards [eventually_jmOldColors_le (jmDelta_pos heta₀),
    eventually_const_mul_rpow_le_auxDegree_rpow heta₀
      (C := (8 : ℝ)) (a := (8 / 3 : ℝ))
      (b := 1 - jmEta eta₀) (by norm_num) (sub_pos.mpr (jmEta_lt_one heta₀))
      (jm_host_error_exponent_gap heta₀),
    eventually_jmAuxDegreeReal_le_universalHostDegree (jmDelta_pos heta₀),
    Filter.eventually_ge_atTop (2 : ℕ)] with n hk hgrowth haux hn
  calc
    universalHostDegreeError n (jmOldColors (jmDelta eta₀) n)
        (jmDeletion (jmDelta eta₀) n) ≤ 8 * (n : ℝ) ^ (8 / 3 : ℝ) :=
      universalHostDegreeError_le_eight_rpow hn hk
    _ ≤ (jmAuxDegreeReal (jmDelta eta₀) n) ^ (1 - jmEta eta₀) := hgrowth
    _ ≤ (universalHostDegree n (jmOldColors (jmDelta eta₀) n)
        (jmDeletion (jmDelta eta₀) n)) ^ (1 - jmEta eta₀) :=
      Real.rpow_le_rpow (jmAuxDegreeReal_nonneg _ _) haux hb

/-- The exact labelled-vertex centre is no larger than the paper's analytic
central degree.  Both the falling factorial in `n` and the rounded quantity
`k - 1` lie below their unrounded counterparts. -/
theorem universalLabelDegreeTarget_le_jmAuxDegreeReal {delta : ℝ} {n : ℕ}
    (hn : 2 ≤ n) :
    universalLabelDegreeTarget n (jmOldColors delta n) (jmDeletion delta n) ≤
      jmAuxDegreeReal delta n := by
  let k := jmOldColors delta n
  let q := jmDeletion delta n
  let r := jmOldPaletteReal delta n
  let m : ℝ := (k - 1 : ℕ)
  have hk0 : 1 ≤ k := by
    dsimp [k]
    have holdpos : 0 < jmOldPaletteReal delta n := by
      unfold jmOldPaletteReal
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hrho : 0 ≤ jmRho delta n := Real.rpow_nonneg (Nat.cast_nonneg n) _
      positivity
    exact Nat.one_le_ceil_iff.mpr holdpos
  have hmle : m ≤ r := by
    have hceil := jmOldColors_lt_add_one delta n
    change (k : ℝ) < r + 1 at hceil
    dsimp [m]
    rw [Nat.cast_sub hk0]
    norm_num
    linarith
  have hm0 : 0 ≤ m := by positivity
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact jmOldPaletteReal_nonneg delta n
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hn2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub hn]
    norm_num
  have hn1le : ((n - 1 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast Nat.sub_le n 1
  have hn2le : ((n - 2 : ℕ) : ℝ) ≤ n := by
    exact_mod_cast Nat.sub_le n 2
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1nonneg : 0 ≤ (n : ℝ) - 1 := by linarith
  have hn2nonneg : 0 ≤ (n : ℝ) - 2 := by linarith
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  have hcoef :
      (5 : ℝ) * ((n - 1).choose 2 : ℕ) * m ≤
        (5 / 2 : ℝ) * (n : ℝ) ^ 2 * r := by
    norm_num only [Nat.cast_choose_two]
    rw [hn1]
    calc
      5 * (((n : ℝ) - 1) * ((n : ℝ) - 1 - 1) / 2) * m =
          5 * (((n : ℝ) - 1) * ((n : ℝ) - 2) / 2) * m := by ring
      _ =
          (5 / 2 : ℝ) * (((n : ℝ) - 1) * ((n : ℝ) - 2) * m) := by ring
      _ ≤ (5 / 2 : ℝ) * ((n : ℝ) * n * r) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul
          (mul_le_mul (by linarith) (by linarith) hn2nonneg hnnonneg)
          hmle hm0 (mul_nonneg hnnonneg hnnonneg)
      _ = (5 / 2 : ℝ) * (n : ℝ) ^ 2 * r := by ring
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact (jmDeletion_pos (by omega : 0 < n)).le
  have hret : jmRetention delta n = 1 - q := by
    dsimp [q]
    linarith [jmRetention_add_deletion (delta := delta) (by omega : 0 < n)]
  have ht0 : 0 ≤ q ^ 4 * (1 - q) := by
    have hq1 : q ≤ 1 := by
      dsimp [q]
      exact (jmDeletion_lt_one (by omega : 0 < n)).le
    positivity
  unfold universalLabelDegreeTarget jmAuxDegreeReal
  rw [hret]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hcoef ht0

/-- A finite comparison of the common host degree with the analytic central
degree and explicit polynomial errors. -/
theorem universalHostDegree_le_aux_add_errors {delta : ℝ} {n : ℕ}
    (hn : 2 ≤ n) (hk : jmOldColors delta n ≤ n) :
    universalHostDegree n (jmOldColors delta n) (jmDeletion delta n) ≤
      jmAuxDegreeReal delta n + 6 * (n : ℝ) ^ 2 +
        (n : ℝ) ^ (8 / 3 : ℝ) := by
  let G := universalGraphDegreeTarget n (jmOldColors delta n) (jmDeletion delta n)
  let L := universalLabelDegreeTarget n (jmOldColors delta n) (jmDeletion delta n)
  have hdiff : |G - L| ≤ 6 * (n : ℝ) ^ 2 :=
    universalGraph_label_difference_le hn hk
  have hG : G ≤ L + 6 * (n : ℝ) ^ 2 := by
    have := le_abs_self (G - L)
    linarith
  have hL : L ≤ L + 6 * (n : ℝ) ^ 2 :=
    le_add_of_nonneg_right (by positivity)
  have hmax : max G L ≤ L + 6 * (n : ℝ) ^ 2 := max_le hG hL
  have hcentre : L ≤ jmAuxDegreeReal delta n :=
    universalLabelDegreeTarget_le_jmAuxDegreeReal hn
  unfold universalHostDegree
  change max G L + (n : ℝ) ^ (8 / 3 : ℝ) ≤ _
  linarith

/-- The common retained-host degree remains within a fixed factor of the
paper's analytic degree.  This direction transfers the role-test lower
bounds, which are normalized using the analytic centre, to the single CFM
degree parameter. -/
theorem eventually_universalHostDegree_le_two_jmAuxDegreeReal
    {eta₀ : ℝ} (heta₀ : 0 < eta₀) :
    ∀ᶠ n : ℕ in Filter.atTop,
      universalHostDegree n (jmOldColors (jmDelta eta₀) n)
          (jmDeletion (jmDelta eta₀) n) ≤
        2 * jmAuxDegreeReal (jmDelta eta₀) n := by
  have hgap : (8 / 3 : ℝ) < (3 - jmDelta eta₀) * 1 := by
    have hd := jmDelta_le_one_ten_thousandth eta₀
    nlinarith
  filter_upwards [eventually_jmOldColors_le (jmDelta_pos heta₀),
    eventually_const_mul_rpow_le_auxDegree_rpow heta₀
      (C := (7 : ℝ)) (a := (8 / 3 : ℝ)) (b := (1 : ℝ))
      (by norm_num) (by norm_num) hgap,
    Filter.eventually_ge_atTop (2 : ℕ)] with n hk hgrowth hn
  have hfinite := universalHostDegree_le_aux_add_errors hn hk
  have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (8 / 3 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
  have herr : 6 * (n : ℝ) ^ 2 + (n : ℝ) ^ (8 / 3 : ℝ) ≤
      7 * (n : ℝ) ^ (8 / 3 : ℝ) := by linarith
  rw [Real.rpow_one] at hgrowth
  linarith

/-- The complete arithmetic contract for selecting the one common degree
parameter used by the conflict-free matching theorem. -/
def UniversalHostDegreeArithmetic (eta₀ d₀ : ℝ) (n : ℕ) : Prop :=
  let d := universalHostDegree n (jmOldColors (jmDelta eta₀) n)
    (jmDeletion (jmDelta eta₀) n)
  d₀ ≤ d ∧
    jmAuxDegreeReal (jmDelta eta₀) n ≤ d ∧
    d ≤ 2 * jmAuxDegreeReal (jmDelta eta₀) n ∧
    universalHostDegreeError n (jmOldColors (jmDelta eta₀) n)
        (jmDeletion (jmDelta eta₀) n) ≤ d ^ (1 - jmEta eta₀)

theorem eventually_universalHostDegreeArithmetic {eta₀ : ℝ}
    (heta₀ : 0 < eta₀) (d₀ : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop, UniversalHostDegreeArithmetic eta₀ d₀ n := by
  have hdelta3 : jmDelta eta₀ < 3 :=
    (jmDelta_le_one_ten_thousandth eta₀).trans_lt (by norm_num)
  filter_upwards [eventually_universalHostDegree_ge
      (delta := jmDelta eta₀) (d₀ := d₀) (jmDelta_pos heta₀) hdelta3,
    eventually_jmAuxDegreeReal_le_universalHostDegree (jmDelta_pos heta₀),
    eventually_universalHostDegree_le_two_jmAuxDegreeReal heta₀,
    eventually_universalHostDegreeError_le_rpow heta₀] with n hd0 hlower hupper herr
  exact ⟨hd0, hlower, hupper, herr⟩

/-- Strengthened retained-host extraction in the exact form needed before
the deterministic conflict and tracked-test adapters are applied.  It has no
certificate, expectation, influence, or numerical-growth premises. -/
theorem eventually_exists_joosMubayi_retained_host_for_cfm
    {eta₀ : ℝ} (heta₀ : 0 < eta₀) (d₀ : ℝ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ R : RetainedLabels n (jmOldColors (jmDelta eta₀) n),
        UniversalRetainedHostEstimates (jmDeletion (jmDelta eta₀) n) R ∧
        UniversalRetainedHostCodegreeBounds (jmDelta eta₀) R ∧
        UniversalHostDegreeArithmetic eta₀ d₀ n := by
  have hdeltaThird : jmDelta eta₀ < 1 / 3 :=
    (jmDelta_le_one_ten_thousandth eta₀).trans_lt (by norm_num)
  filter_upwards [eventually_exists_joosMubayi_retained_host_with_codegree_bounds
      (jmDelta_pos heta₀) hdeltaThird,
    eventually_universalHostDegreeArithmetic heta₀ d₀] with n hexists harith
  obtain ⟨R, hhost, hcodeg⟩ := hexists
  exact ⟨R, hhost, hcodeg, harith⟩


end
end
end AuxConcentration
end Erdos136
