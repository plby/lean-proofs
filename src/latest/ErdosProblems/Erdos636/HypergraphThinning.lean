/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos636.Sunflower
import ErdosProblems.Erdos636.Turan
import Mathlib.Combinatorics.Pigeonhole

/-!
# Finite hypergraph thinning for Erdős Problem 636

This file packages the purely finite part of the Kwan--Sudakov structural
argument.  A uniform family is first thinned to one fibre of a finite
colouring (in the application, the colour is the triple of degree sums into
`W⁻`, `W⁺`, and `U₀`).  The elementary sunflower lemma is then applied and
the common core is deleted.  Deleting the core is injective, produces a
uniform matching of nonempty petals, and preserves differences of all
additive scores.  Finally a generic conflict graph and the coarse Turán
bound retain a large pairwise-compatible subfamily.

All estimates are exact natural-number inequalities.  In particular, the
main theorem at the end exposes every loss: the number of colours, the
sunflower factorial/power loss, and the conflict-degree factor `b + 1`.
-/

open Classical

namespace Erdos636

universe u v w

noncomputable section

variable {α : Type u} [DecidableEq α]

/-! ## A quantitative finite fibre -/

/-- Some fibre of a map to a nonempty finite type contains at least the
average number of elements, with division cleared from the statement. -/
theorem exists_fiber_card_mul_ge
    {β : Type v} [Fintype β] [DecidableEq β] [Nonempty β]
    (𝒜 : Finset α) (color : α → β) :
    ∃ q : β,
      𝒜.card ≤ (𝒜.filter fun A => color A = q).card * Fintype.card β := by
  obtain ⟨q, _hq, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset β)
      (fun q => (𝒜.filter fun A => color A = q).card)
      Finset.univ_nonempty
  refine ⟨q, ?_⟩
  calc
    𝒜.card = ∑ y : β, (𝒜.filter fun A => color A = y).card := by
      symm
      simpa using
        (Finset.sum_card_fiberwise_eq_card_filter
          𝒜 (Finset.univ : Finset β) color)
    _ ≤ ∑ _y : β, (𝒜.filter fun A => color A = q).card := by
      exact Finset.sum_le_sum fun y _hy => hmax y (Finset.mem_univ y)
    _ = (𝒜.filter fun A => color A = q).card * Fintype.card β := by
      simp [Nat.mul_comm]

/-- Truncate a natural-valued colour into the finite interval `0, ..., B`.
On a family on which `value ≤ B`, no information is lost. -/
def boundedNatColor {γ : Type*} (B : ℕ) (value : γ → ℕ) (x : γ) :
    Fin (B + 1) :=
  ⟨min (value x) B, by omega⟩

/-- The finite colour used for the three degree sums in the structural
argument.  Its cardinality is exactly `(B + 1)^3`. -/
def boundedTripleColor {γ : Type*} (B : ℕ)
    (d₁ d₂ d₃ : γ → ℕ) (x : γ) :
    Fin (B + 1) × Fin (B + 1) × Fin (B + 1) :=
  (boundedNatColor B d₁ x, boundedNatColor B d₂ x,
    boundedNatColor B d₃ x)

/-- Pigeonhole three bounded natural-valued statistics simultaneously.
This is the exact finite version of the `(Kn+1)^3` degree-triple loss. -/
theorem exists_bounded_triple_fiber_card_mul_ge
    {γ : Type*} [DecidableEq γ] (𝒜 : Finset γ)
    (d₁ d₂ d₃ : γ → ℕ) (B : ℕ)
    (hbounded : ∀ A ∈ 𝒜, d₁ A ≤ B ∧ d₂ A ≤ B ∧ d₃ A ≤ B) :
    ∃ q₁ q₂ q₃ : ℕ,
      q₁ ≤ B ∧ q₂ ≤ B ∧ q₃ ≤ B ∧
      𝒜.card ≤
        (𝒜.filter fun A => d₁ A = q₁ ∧ d₂ A = q₂ ∧ d₃ A = q₃).card *
          (B + 1) ^ 3 := by
  let color := boundedTripleColor B d₁ d₂ d₃
  obtain ⟨q, hq⟩ := exists_fiber_card_mul_ge 𝒜 color
  refine ⟨q.1.val, q.2.1.val, q.2.2.val, Nat.le_of_lt_succ q.1.isLt,
    Nat.le_of_lt_succ q.2.1.isLt, Nat.le_of_lt_succ q.2.2.isLt, ?_⟩
  have hfiber :
      (𝒜.filter fun A => color A = q) =
        𝒜.filter fun A =>
          d₁ A = q.1.val ∧ d₂ A = q.2.1.val ∧ d₃ A = q.2.2.val := by
    ext A
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hA, hcolor⟩
      have h₁ := congrArg (fun z => z.1.val) hcolor
      have h₂ := congrArg (fun z => z.2.1.val) hcolor
      have h₃ := congrArg (fun z => z.2.2.val) hcolor
      rcases hbounded A hA with ⟨hd₁, hd₂, hd₃⟩
      simp only [color, boundedTripleColor, boundedNatColor,
        Nat.min_eq_left hd₁] at h₁
      simp only [color, boundedTripleColor, boundedNatColor,
        Nat.min_eq_left hd₂] at h₂
      simp only [color, boundedTripleColor, boundedNatColor,
        Nat.min_eq_left hd₃] at h₃
      exact ⟨hA, h₁, h₂, h₃⟩
    · rintro ⟨hA, h₁, h₂, h₃⟩
      refine ⟨hA, ?_⟩
      rcases hbounded A hA with ⟨hd₁, hd₂, hd₃⟩
      apply Prod.ext
      · apply Fin.ext
        simpa [color, boundedTripleColor, boundedNatColor,
          Nat.min_eq_left hd₁] using h₁
      · apply Prod.ext <;> apply Fin.ext
        · simpa [color, boundedTripleColor, boundedNatColor,
            Nat.min_eq_left hd₂] using h₂
        · simpa [color, boundedTripleColor, boundedNatColor,
            Nat.min_eq_left hd₃] using h₃
  rw [hfiber] at hq
  simpa [color, boundedTripleColor, pow_succ, Nat.mul_assoc] using hq

/-! ## Deleting the core of a sunflower -/

/-- The family of petals obtained by deleting `C` from every member. -/
def petalFamily (𝒜 : Finset (Finset α)) (C : Finset α) :
    Finset (Finset α) :=
  𝒜.image fun A => A \ C

/-- In a sunflower with at least two members, the core lies in every
member.  The cardinality hypothesis is essential for the one-member case. -/
theorem IsSunflower.core_subset_of_two_le_card
    {𝒜 : Finset (Finset α)} {C A : Finset α}
    (hsun : IsSunflower 𝒜 C) (hcard : 2 ≤ 𝒜.card) (hA : A ∈ 𝒜) :
    C ⊆ A := by
  obtain ⟨B, hB, hBA⟩ := Finset.exists_mem_ne (by omega : 1 < 𝒜.card) A
  rw [← hsun hB hA hBA]
  exact Finset.inter_subset_right

/-- Core deletion is injective on a sunflower with at least two members. -/
theorem IsSunflower.sdiff_injOn_of_two_le_card
    {𝒜 : Finset (Finset α)} {C : Finset α}
    (hsun : IsSunflower 𝒜 C) (hcard : 2 ≤ 𝒜.card) :
    Set.InjOn (fun A : Finset α => A \ C) 𝒜 := by
  intro A hA B hB hpetal
  have hCA := hsun.core_subset_of_two_le_card hcard hA
  have hCB := hsun.core_subset_of_two_le_card hcard hB
  calc
    A = (A \ C) ∪ C := (Finset.sdiff_union_of_subset hCA).symm
    _ = (B \ C) ∪ C := congrArg (fun P : Finset α => P ∪ C) hpetal
    _ = B := Finset.sdiff_union_of_subset hCB

/-- Core deletion preserves the number of members. -/
theorem card_petalFamily_eq
    {𝒜 : Finset (Finset α)} {C : Finset α}
    (hsun : IsSunflower 𝒜 C) (hcard : 2 ≤ 𝒜.card) :
    (petalFamily 𝒜 C).card = 𝒜.card := by
  exact Finset.card_image_of_injOn
    (hsun.sdiff_injOn_of_two_le_card hcard)

/-- The image formulation of the usual fact that sunflower petals are
pairwise disjoint. -/
theorem IsSunflower.petalFamily_pairwiseDisjoint
    {𝒜 : Finset (Finset α)} {C : Finset α}
    (hsun : IsSunflower 𝒜 C) :
    (petalFamily 𝒜 C : Set (Finset α)).PairwiseDisjoint id := by
  intro P hP Q hQ hPQ
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hP
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hQ
  apply hsun.pairwiseDisjoint_sdiff hA hB
  intro hAB
  subst B
  exact hPQ rfl

/-- A uniform sunflower gives a uniform family of petals. -/
theorem IsSunflower.card_eq_sub_core_of_mem_petalFamily
    {𝒜 : Finset (Finset α)} {C P : Finset α} {k : ℕ}
    (hsun : IsSunflower 𝒜 C) (hcard : 2 ≤ 𝒜.card)
    (huniform : ∀ A ∈ 𝒜, A.card = k)
    (hP : P ∈ petalFamily 𝒜 C) :
    P.card = k - C.card := by
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hP
  rw [Finset.card_sdiff_of_subset
    (hsun.core_subset_of_two_le_card hcard hA), huniform A hA]

/-- The common core of a uniform sunflower with two distinct members is
strictly smaller than an edge; equivalently, every petal is nonempty. -/
theorem IsSunflower.core_card_lt_uniform_card
    {𝒜 : Finset (Finset α)} {C : Finset α} {k : ℕ}
    (hsun : IsSunflower 𝒜 C) (hcard : 2 ≤ 𝒜.card)
    (huniform : ∀ A ∈ 𝒜, A.card = k) :
    C.card < k := by
  obtain ⟨A, hA, B, hB, hAB⟩ := Finset.one_lt_card.mp (by omega : 1 < 𝒜.card)
  have hCA := hsun.core_subset_of_two_le_card hcard hA
  have hCneA : C ≠ A := by
    intro hCAeq
    have hABsub : A ⊆ B := by
      rw [← hCAeq, ← hsun hA hB hAB]
      exact Finset.inter_subset_right
    have hBAcard : B.card ≤ A.card := by rw [huniform A hA, huniform B hB]
    exact hAB (Finset.eq_of_subset_of_card_le hABsub hBAcard)
  calc
    C.card < A.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hCA, hCneA⟩)
    _ = k := huniform A hA

/-- A uniform sunflower with at least two members produces a nonempty
uniform matching of exactly the same size. -/
theorem exists_uniform_petal_family
    {𝒜 : Finset (Finset α)} {C : Finset α} {k : ℕ}
    (hsun : IsSunflower 𝒜 C) (hcard : 2 ≤ 𝒜.card)
    (huniform : ∀ A ∈ 𝒜, A.card = k) :
    ∃ k' : ℕ,
      1 ≤ k' ∧ k' ≤ k ∧
      (petalFamily 𝒜 C).card = 𝒜.card ∧
      (petalFamily 𝒜 C : Set (Finset α)).PairwiseDisjoint id ∧
      ∀ P ∈ petalFamily 𝒜 C, P.card = k' := by
  refine ⟨k - C.card, ?_, Nat.sub_le _ _,
    card_petalFamily_eq hsun hcard,
    hsun.petalFamily_pairwiseDisjoint, ?_⟩
  · have hcore := hsun.core_card_lt_uniform_card hcard huniform
    omega
  · intro P hP
    exact hsun.card_eq_sub_core_of_mem_petalFamily hcard huniform hP

/-! ## Additive scores and removal of the core -/

/-- An additive score of a finite vertex set.  The three degree sums in the
structural argument are instances of this definition. -/
def finsetScore {M : Type w} [AddCommMonoid M]
    (weight : α → M) (A : Finset α) : M :=
  ∑ a ∈ A, weight a

theorem finsetScore_sdiff_add_core
    {M : Type w} [AddCommMonoid M] (weight : α → M)
    {C A : Finset α} (hCA : C ⊆ A) :
    finsetScore weight (A \ C) + finsetScore weight C =
      finsetScore weight A := by
  exact Finset.sum_sdiff hCA

/-- Equal additive scores on two sunflower edges remain equal after the
common core is removed. -/
theorem IsSunflower.finsetScore_sdiff_eq_of_eq
    {M : Type w} [AddCancelCommMonoid M] (weight : α → M)
    {𝒜 : Finset (Finset α)} {C A B : Finset α}
    (hsun : IsSunflower 𝒜 C) (hcard : 2 ≤ 𝒜.card)
    (hA : A ∈ 𝒜) (hB : B ∈ 𝒜)
    (hscore : finsetScore weight A = finsetScore weight B) :
    finsetScore weight (A \ C) = finsetScore weight (B \ C) := by
  apply add_right_cancel (b := finsetScore weight C)
  rw [finsetScore_sdiff_add_core weight
      (hsun.core_subset_of_two_le_card hcard hA),
    finsetScore_sdiff_add_core weight
      (hsun.core_subset_of_two_le_card hcard hB), hscore]

/-- Removing the common core preserves differences of additive scores. -/
theorem IsSunflower.finsetScore_sub_eq_sdiff_sub
    {M : Type w} [AddCommGroup M] (weight : α → M)
    {𝒜 : Finset (Finset α)} {C A B : Finset α}
    (hsun : IsSunflower 𝒜 C) (hcard : 2 ≤ 𝒜.card)
    (hA : A ∈ 𝒜) (hB : B ∈ 𝒜) :
    finsetScore weight A - finsetScore weight B =
      finsetScore weight (A \ C) - finsetScore weight (B \ C) := by
  have hscoreA := finsetScore_sdiff_add_core weight
    (hsun.core_subset_of_two_le_card hcard hA)
  have hscoreB := finsetScore_sdiff_add_core weight
    (hsun.core_subset_of_two_le_card hcard hB)
  rw [← hscoreA, ← hscoreB]
  abel

/-! ## Fibre followed by sunflower -/

/-- Exact fibre-and-sunflower thinning.  The hypothesis clears the finite
colour loss, so the chosen monochromatic fibre still exceeds the elementary
sunflower threshold. -/
theorem exists_monochromatic_sunflower_petals
    {β : Type v} [Fintype β] [DecidableEq β] [Nonempty β]
    (𝒜 : Finset (Finset α)) (color : Finset α → β)
    (k r : ℕ) (hr : 2 ≤ r)
    (huniform : ∀ A ∈ 𝒜, A.card = k)
    (hlarge :
      k.factorial * (r - 1) ^ k * Fintype.card β < 𝒜.card) :
    ∃ q : β, ∃ ℬ : Finset (Finset α), ∃ C : Finset α, ∃ k' : ℕ,
      ℬ ⊆ 𝒜 ∧
      ℬ.card = r ∧
      IsSunflower ℬ C ∧
      (∀ A ∈ ℬ, color A = q) ∧
      1 ≤ k' ∧ k' ≤ k ∧
      (petalFamily ℬ C).card = r ∧
      (petalFamily ℬ C : Set (Finset α)).PairwiseDisjoint id ∧
      ∀ P ∈ petalFamily ℬ C, P.card = k' := by
  obtain ⟨q, hfiber⟩ := exists_fiber_card_mul_ge 𝒜 color
  let 𝒜q := 𝒜.filter fun A => color A = q
  have hsunLarge : k.factorial * (r - 1) ^ k < 𝒜q.card := by
    apply Nat.lt_of_mul_lt_mul_right (a := Fintype.card β)
    calc
      (k.factorial * (r - 1) ^ k) * Fintype.card β < 𝒜.card := hlarge
      _ ≤ 𝒜q.card * Fintype.card β := by simpa [𝒜q] using hfiber
  have h𝒜qUniform : ∀ A ∈ 𝒜q, A.card = k := by
    intro A hA
    exact huniform A (Finset.mem_filter.mp hA).1
  obtain ⟨ℬ, hℬsubq, hℬcard, C, hsun⟩ :=
    exists_sunflower_of_factorial_mul_pow_lt_card
      k r (by omega) 𝒜q h𝒜qUniform hsunLarge
  have hℬsub : ℬ ⊆ 𝒜 := fun A hA =>
    (Finset.mem_filter.mp (hℬsubq hA)).1
  have hmono : ∀ A ∈ ℬ, color A = q := fun A hA =>
    (Finset.mem_filter.mp (hℬsubq hA)).2
  obtain ⟨k', hk'pos, hk'le, hpetCard, hpetDisj, hpetUniform⟩ :=
    exists_uniform_petal_family hsun (by omega) (fun A hA => huniform A (hℬsub hA))
  refine ⟨q, ℬ, C, k', hℬsub, hℬcard, hsun, hmono,
    hk'pos, hk'le, ?_, hpetDisj, hpetUniform⟩
  rw [hpetCard, hℬcard]

/-! ## Generic low-conflict graph and Turán thinning -/

/-- The graph on `P` whose edges are the conflicting pairs. -/
def conflictGraph (P : Finset α) (Conflict : α → α → Prop)
    (hsymm : Std.Symm Conflict) (hirr : Std.Irrefl Conflict) :
    SimpleGraph {x // x ∈ P} :=
  SimpleGraph.mk
    (fun x y => Conflict x.1 y.1)
    (symm := ⟨fun x y h => hsymm.symm x.1 y.1 h⟩)
    (loopless := ⟨fun x h => hirr.irrefl x.1 h⟩)

@[simp] theorem conflictGraph_adj
    {P : Finset α} {Conflict : α → α → Prop}
    {hsymm : Std.Symm Conflict} {hirr : Std.Irrefl Conflict}
    {x y : {x // x ∈ P}} :
    (conflictGraph P Conflict hsymm hirr).Adj x y ↔ Conflict x.1 y.1 :=
  Iff.rfl

/-- If every member of a finite family conflicts with at most `b` other
members, Turán thinning retains a `1/(b+1)` fraction with no conflicting
pair.  Pairwise disjointness of the input is retained verbatim. -/
theorem exists_pairwise_compatible_subfamily
    (P : Finset α) (Conflict : α → α → Prop)
    (hsymm : Std.Symm Conflict) (hirr : Std.Irrefl Conflict) (b : ℕ)
    (hdegree : ∀ x ∈ P, (P.filter fun y => Conflict x y).card ≤ b) :
    ∃ M : Finset α,
      M ⊆ P ∧
      (∀ x ∈ M, ∀ y ∈ M, x ≠ y → ¬ Conflict x y) ∧
      P.card ≤ M.card * (b + 1) := by
  let H := conflictGraph P Conflict hsymm hirr
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hHdegree : ∀ x : {x // x ∈ P}, H.degree x ≤ b := by
    intro x
    let N : Finset α := (H.neighborFinset x).image Subtype.val
    have hNcard : N.card = H.degree x := by
      dsimp [N]
      rw [Finset.card_image_of_injective _ Subtype.val_injective]
      exact H.card_neighborFinset_eq_degree x
    have hNsub : N ⊆ P.filter fun y => Conflict x.1 y := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      have hadj : H.Adj x z := (H.mem_neighborFinset x z).mp hz
      exact Finset.mem_filter.mpr ⟨z.property, hadj⟩
    rw [← hNcard]
    exact (Finset.card_le_card hNsub).trans (hdegree x.1 x.2)
  have hmax : H.maxDegree ≤ b := H.maxDegree_le_of_forall_degree_le b hHdegree
  obtain ⟨S, hSind, hScard⟩ := exists_indepSet_card_mul_maxDegree_add_one H
  let M : Finset α := S.image Subtype.val
  have hMcard : M.card = S.card :=
    Finset.card_image_of_injective S Subtype.val_injective
  have hMsub : M ⊆ P := by
    intro x hx
    obtain ⟨sx, _hsx, rfl⟩ := Finset.mem_image.mp hx
    exact sx.property
  have hMcompatible : ∀ x ∈ M, ∀ y ∈ M, x ≠ y → ¬ Conflict x y := by
    intro x hx y hy hxy hconflict
    obtain ⟨sx, hsx, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨sy, hsy, rfl⟩ := Finset.mem_image.mp hy
    have hsxy : sx ≠ sy := fun h => hxy (congrArg Subtype.val h)
    exact (H.isIndepSet_iff.mp hSind) hsx hsy hsxy hconflict
  refine ⟨M, hMsub, hMcompatible, ?_⟩
  rw [hMcard]
  calc
    P.card = Fintype.card {x // x ∈ P} := by simp
    _ ≤ S.card * (H.maxDegree + 1) := hScard
    _ ≤ S.card * (b + 1) := by gcongr

/-- Complete finite thinning pipeline.  The condition `hdegree` is stated
for every possible output of the fibre/sunflower stage, which makes the
theorem independent of how the application proves its low-diversity degree
bound. -/
theorem exists_monochromatic_sunflower_turan_thinning
    {β : Type v} [Fintype β] [DecidableEq β] [Nonempty β]
    (𝒜 : Finset (Finset α)) (color : Finset α → β)
    (Conflict : Finset α → Finset α → Prop)
    (hsymm : Std.Symm Conflict) (hirr : Std.Irrefl Conflict)
    (k r b : ℕ) (hr : 2 ≤ r)
    (huniform : ∀ A ∈ 𝒜, A.card = k)
    (hlarge : k.factorial * (r - 1) ^ k * Fintype.card β < 𝒜.card)
    (hdegree : ∀ (ℬ : Finset (Finset α)) (C : Finset α),
      ℬ ⊆ 𝒜 → ℬ.card = r → IsSunflower ℬ C →
      ∀ P ∈ petalFamily ℬ C,
        ((petalFamily ℬ C).filter fun Q => Conflict P Q).card ≤ b) :
    ∃ q : β, ∃ ℬ : Finset (Finset α), ∃ C : Finset α,
      ∃ P M : Finset (Finset α), ∃ k' : ℕ,
      ℬ ⊆ 𝒜 ∧ ℬ.card = r ∧ IsSunflower ℬ C ∧
      (∀ A ∈ ℬ, color A = q) ∧
      P = petalFamily ℬ C ∧
      P.card = r ∧
      1 ≤ k' ∧ k' ≤ k ∧
      (∀ x ∈ P, x.card = k') ∧
      (P : Set (Finset α)).PairwiseDisjoint id ∧
      M ⊆ P ∧
      (M : Set (Finset α)).PairwiseDisjoint id ∧
      (∀ x ∈ M, x.card = k') ∧
      (∀ x ∈ M, ∀ y ∈ M, x ≠ y → ¬ Conflict x y) ∧
      r ≤ M.card * (b + 1) := by
  obtain ⟨q, ℬ, C, k', hℬsub, hℬcard, hsun, hmono,
    hk'pos, hk'le, hPcard, hPdisj, hPuniform⟩ :=
    exists_monochromatic_sunflower_petals 𝒜 color k r hr huniform hlarge
  let P := petalFamily ℬ C
  obtain ⟨M, hMsub, hMcompatible, hMcard⟩ :=
    exists_pairwise_compatible_subfamily P Conflict hsymm hirr b
      (hdegree ℬ C hℬsub hℬcard hsun)
  have hMdisj : (M : Set (Finset α)).PairwiseDisjoint id := by
    intro x hx y hy hxy
    exact hPdisj (hMsub hx) (hMsub hy) hxy
  have hMuniform : ∀ x ∈ M, x.card = k' := fun x hx =>
    hPuniform x (hMsub hx)
  refine ⟨q, ℬ, C, P, M, k', hℬsub, hℬcard, hsun, hmono, rfl,
    ?_, hk'pos, hk'le, hPuniform, hPdisj, hMsub, hMdisj,
    hMuniform, hMcompatible, ?_⟩
  · exact hPcard
  · rw [← hPcard]
    exact hMcard

/-- Degree-triple specialization of the complete pipeline.  This is the
form consumed by the structural argument: `d₁`, `d₂`, and `d₃` are the
degree sums into its three fixed base sets.  The output matching consists of
positive uniform petals, the original sunflower edges have one common raw
degree triple, and deleting the core preserves the corresponding degree
differences by `IsSunflower.finsetScore_sub_eq_sdiff_sub`. -/
theorem exists_bounded_triple_sunflower_turan_thinning
    (𝒜 : Finset (Finset α)) (d₁ d₂ d₃ : Finset α → ℕ) (B : ℕ)
    (Conflict : Finset α → Finset α → Prop)
    (hsymm : Std.Symm Conflict) (hirr : Std.Irrefl Conflict)
    (k r b : ℕ) (hr : 2 ≤ r)
    (huniform : ∀ A ∈ 𝒜, A.card = k)
    (hbounded : ∀ A ∈ 𝒜, d₁ A ≤ B ∧ d₂ A ≤ B ∧ d₃ A ≤ B)
    (hlarge : k.factorial * (r - 1) ^ k * (B + 1) ^ 3 < 𝒜.card)
    (hdegree : ∀ (ℬ : Finset (Finset α)) (C : Finset α),
      ℬ ⊆ 𝒜 → ℬ.card = r → IsSunflower ℬ C →
      ∀ P ∈ petalFamily ℬ C,
        ((petalFamily ℬ C).filter fun Q => Conflict P Q).card ≤ b) :
    ∃ q₁ q₂ q₃ : ℕ, ∃ ℬ : Finset (Finset α), ∃ C : Finset α,
      ∃ P M : Finset (Finset α), ∃ k' : ℕ,
      q₁ ≤ B ∧ q₂ ≤ B ∧ q₃ ≤ B ∧
      ℬ ⊆ 𝒜 ∧ ℬ.card = r ∧ IsSunflower ℬ C ∧
      (∀ A ∈ ℬ, d₁ A = q₁ ∧ d₂ A = q₂ ∧ d₃ A = q₃) ∧
      P = petalFamily ℬ C ∧
      P.card = r ∧
      1 ≤ k' ∧ k' ≤ k ∧
      (∀ x ∈ P, x.card = k') ∧
      (P : Set (Finset α)).PairwiseDisjoint id ∧
      M ⊆ P ∧
      (M : Set (Finset α)).PairwiseDisjoint id ∧
      (∀ x ∈ M, x.card = k') ∧
      (∀ x ∈ M, ∀ y ∈ M, x ≠ y → ¬ Conflict x y) ∧
      r ≤ M.card * (b + 1) := by
  let color := boundedTripleColor B d₁ d₂ d₃
  have hlarge' :
      k.factorial * (r - 1) ^ k *
          Fintype.card (Fin (B + 1) × Fin (B + 1) × Fin (B + 1)) <
        𝒜.card := by
    simpa [pow_succ, Nat.mul_assoc] using hlarge
  obtain ⟨q, ℬ, C, P, M, k', hℬsub, hℬcard, hsun, hmono,
    hPdef, hPcard, hk'pos, hk'le, hPuniform, hPdisj, hMsub,
    hMdisj, hMuniform, hMcompatible, hMcard⟩ :=
    exists_monochromatic_sunflower_turan_thinning
      𝒜 color Conflict hsymm hirr k r b hr huniform hlarge' hdegree
  let q₁ := q.1.val
  let q₂ := q.2.1.val
  let q₃ := q.2.2.val
  have hq₁ : q₁ ≤ B := Nat.le_of_lt_succ q.1.isLt
  have hq₂ : q₂ ≤ B := Nat.le_of_lt_succ q.2.1.isLt
  have hq₃ : q₃ ≤ B := Nat.le_of_lt_succ q.2.2.isLt
  have hmonoRaw : ∀ A ∈ ℬ,
      d₁ A = q₁ ∧ d₂ A = q₂ ∧ d₃ A = q₃ := by
    intro A hA
    have hcolor := hmono A hA
    have h₁ := congrArg (fun z => z.1.val) hcolor
    have h₂ := congrArg (fun z => z.2.1.val) hcolor
    have h₃ := congrArg (fun z => z.2.2.val) hcolor
    rcases hbounded A (hℬsub hA) with ⟨hd₁, hd₂, hd₃⟩
    simp only [color, boundedTripleColor, boundedNatColor,
      Nat.min_eq_left hd₁] at h₁
    simp only [color, boundedTripleColor, boundedNatColor,
      Nat.min_eq_left hd₂] at h₂
    simp only [color, boundedTripleColor, boundedNatColor,
      Nat.min_eq_left hd₃] at h₃
    exact ⟨h₁, h₂, h₃⟩
  exact ⟨q₁, q₂, q₃, ℬ, C, P, M, k', hq₁, hq₂, hq₃,
    hℬsub, hℬcard, hsun, hmonoRaw, hPdef, hPcard, hk'pos, hk'le,
    hPuniform, hPdisj, hMsub, hMdisj, hMuniform, hMcompatible, hMcard⟩

end

end Erdos636
