/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 772.
https://www.erdosproblems.com/forum/thread/772

Informal authors:
- Noga Alon
- Paul Erdős

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos772.md
-/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-!
# Erdős Problem 772

Alon and Erdős proved that a finite set whose ordered two-sum representation
function is bounded by `k` has a Sidon subset of size `≫ₖ |A|^(2/3)`.

This file formalizes the ordered-convolution version of their alteration
argument.  Unlike the distinct-pair convention in the original paper, ordered
convolution also has bad three-point supports `x + x = y + z`; these are
counted separately from the four-point supports.
-/

namespace Erdos772

open scoped BigOperators
open Filter Asymptotics

section Definitions

/-- The number of ordered representations of `t` as a sum of two labels. -/
def representationCount {α : Type*} [Fintype α] (a : α → ℕ) (t : ℕ) : ℕ :=
  ((Finset.univ.product Finset.univ).filter (fun p => a p.1 + a p.2 = t)).card

/-- The finite ordered-convolution bound `‖1_A * 1_A‖_∞ ≤ k`. -/
def BoundedRepresentation {α : Type*} [Fintype α] (a : α → ℕ) (k : ℕ) : Prop :=
  ∀ t, representationCount a t ≤ k

/-- A labelled finite set is Sidon when every equality of two sums is trivial. -/
def IsSidon {α : Type*} [DecidableEq α] (a : α → ℕ) (S : Finset α) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ∀ u ∈ S, ∀ v ∈ S,
    a i + a j = a u + a v → ({i, j} : Finset α) = {u, v}

/-- The extremal guarantee occurring in the definition of `H`. -/
def Guarantees (k n r : ℕ) : Prop :=
  ∀ (A : Finset ℕ), A.card = n →
    (∀ t, ((A.product A).filter (fun p => p.1 + p.2 = t)).card ≤ k) →
    ∃ S : Finset ℕ, S ⊆ A ∧ IsSidon id S ∧ r ≤ S.card

/-- The candidate guaranteed sizes, explicitly truncated at `n`. -/
noncomputable def guaranteedSizes (k n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n + 1)).filter (Guarantees k n)

lemma guaranteedSizes_nonempty (k n : ℕ) : (guaranteedSizes k n).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  simp [guaranteedSizes, Guarantees]
  intro A hA hrep
  exact ⟨∅, by simp [IsSidon]⟩

/-- `H k n` is the largest `r ≤ n` guaranteed for every admissible `n`-set.

The explicit cutoff `r ≤ n` gives the natural value `n` when no admissible
set exists (for example, for ordered convolution with `k = 1` and `n ≥ 2`). -/
noncomputable def H (k n : ℕ) : ℕ :=
  (guaranteedSizes k n).max' (guaranteedSizes_nonempty k n)

end Definitions

section Counting

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A generic bound for a filtered Cartesian product from uniform bounds on
its fibers. -/
lemma card_filter_product_le (s : Finset α) {β : Type*} [DecidableEq β]
    (t : Finset β) (R : α → β → Prop) [DecidableRel R] (k : ℕ)
    (h : ∀ x ∈ s, (t.filter (R x)).card ≤ k) :
    ((s.product t).filter (fun p => R p.1 p.2)).card ≤ s.card * k := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      have hprod : (insert x s).product t =
          (({x} : Finset α).product t) ∪ (s.product t) := by
        ext p
        constructor
        · intro hp
          obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
          rcases Finset.mem_insert.mp hp1 with hp1 | hp1
          · apply Finset.mem_union_left
            apply Finset.mem_product.mpr
            exact ⟨by simpa using hp1, hp2⟩
          · apply Finset.mem_union_right
            exact Finset.mem_product.mpr ⟨hp1, hp2⟩
        · intro hp
          rcases Finset.mem_union.mp hp with hp | hp
          · obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
            apply Finset.mem_product.mpr
            exact ⟨Finset.mem_insert.mpr (Or.inl (by simpa using hp1)), hp2⟩
          · obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
            exact Finset.mem_product.mpr ⟨Finset.mem_insert_of_mem hp1, hp2⟩
      rw [hprod, Finset.filter_union]
      have hdisj : Disjoint (({x} : Finset α).product t) (s.product t) := by
        simp [Finset.disjoint_left, hx]
      have hsub1 :
          ((({x} : Finset α).product t).filter (fun p => R p.1 p.2)) ⊆
            (({x} : Finset α).product t) :=
        Finset.filter_subset _ _
      have hsub2 :
          ((s.product t).filter (fun p => R p.1 p.2)) ⊆ (s.product t) :=
        Finset.filter_subset _ _
      rw [Finset.card_union_of_disjoint (hdisj.mono hsub1 hsub2)]
      have hfirst :
          ((({x} : Finset α).product t).filter (fun p => R p.1 p.2)).card =
            (t.filter (R x)).card := by
        have heq :
            ((({x} : Finset α).product t).filter (fun p => R p.1 p.2)) =
              (t.filter (R x)).map ⟨Prod.mk x, Prod.mk_right_injective x⟩ := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton,
            Finset.mem_map]
          aesop
        rw [heq, Finset.card_map]
      rw [hfirst, Finset.card_insert_of_notMem hx, Nat.add_mul]
      have hxbound := h x (by simp)
      have hsbound := ih (fun y hy => h y (by simp [hy]))
      omega

/-- Ordered diagonal relations `x+x=y+z` with three distinct vertices. -/
def diagonalRelations (a : α → ℕ) : Finset (α × (α × α)) :=
  (Finset.univ.product (Finset.univ.product Finset.univ)).filter fun p =>
    a p.1 + a p.1 = a p.2.1 + a p.2.2 ∧
      ({p.1, p.2.1, p.2.2} : Finset α).card = 3

/-- Three-element supports of nontrivial additive relations. -/
def badTriples (a : α → ℕ) : Finset (Finset α) :=
  (diagonalRelations a).image fun p => {p.1, p.2.1, p.2.2}

/-- Ordered additive quadruples having four distinct vertices. -/
def fourRelations (a : α → ℕ) : Finset ((α × α) × (α × α)) :=
  ((Finset.univ.product Finset.univ).product
      (Finset.univ.product Finset.univ)).filter fun p =>
    a p.1.1 + a p.1.2 = a p.2.1 + a p.2.2 ∧
      ({p.1.1, p.1.2, p.2.1, p.2.2} : Finset α).card = 4

/-- Four-element supports of nontrivial additive relations. -/
def badQuads (a : α → ℕ) : Finset (Finset α) :=
  (fourRelations a).image fun p => {p.1.1, p.1.2, p.2.1, p.2.2}

lemma card_diagonalRelations_le (a : α → ℕ) (k : ℕ)
    (hrep : BoundedRepresentation a k) :
    (diagonalRelations a).card ≤ Fintype.card α * k := by
  calc
    (diagonalRelations a).card ≤
        ((Finset.univ.product (Finset.univ.product Finset.univ)).filter
          (fun p => a p.1 + a p.1 = a p.2.1 + a p.2.2)).card := by
      apply Finset.card_le_card
      intro p hp
      simp only [diagonalRelations, Finset.mem_filter, Finset.mem_product,
        Finset.mem_univ, true_and] at hp ⊢
      exact ⟨hp.1, hp.2.1⟩
    _ ≤ Fintype.card α * k := by
      apply card_filter_product_le Finset.univ
        (Finset.univ.product Finset.univ)
        (fun x p => a x + a x = a p.1 + a p.2) k
      intro x hx
      simpa [representationCount, eq_comm] using hrep (a x + a x)

lemma card_badTriples_le (a : α → ℕ) (k : ℕ)
    (hrep : BoundedRepresentation a k) :
    (badTriples a).card ≤ Fintype.card α * k :=
  (Finset.card_image_le.trans (card_diagonalRelations_le a k hrep))

lemma card_fourRelations_le (a : α → ℕ) (k : ℕ)
    (hrep : BoundedRepresentation a k) :
    (fourRelations a).card ≤ Fintype.card α ^ 2 * k := by
  calc
    (fourRelations a).card ≤
        (((Finset.univ.product Finset.univ).product
          (Finset.univ.product Finset.univ)).filter
          (fun p => a p.1.1 + a p.1.2 = a p.2.1 + a p.2.2)).card := by
      apply Finset.card_le_card
      intro p hp
      simp only [fourRelations, Finset.mem_filter, Finset.mem_product,
        Finset.mem_univ, true_and] at hp ⊢
      exact ⟨hp.1, hp.2.1⟩
    _ ≤ Fintype.card α ^ 2 * k := by
      have h := card_filter_product_le
        (Finset.univ.product (Finset.univ : Finset α))
        (Finset.univ.product (Finset.univ : Finset α))
        (fun p q => a p.1 + a p.2 = a q.1 + a q.2) k
        (fun p hp => by
          simpa [representationCount, eq_comm] using hrep (a p.1 + a p.2))
      simpa [pow_two] using h

lemma card_badQuads_le (a : α → ℕ) (k : ℕ)
    (hrep : BoundedRepresentation a k) :
    (badQuads a).card ≤ Fintype.card α ^ 2 * k :=
  Finset.card_image_le.trans (card_fourRelations_le a k hrep)

end Counting

section BadSupports

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- No edge of `E` is wholly contained in `S`. -/
def EdgeFree (E : Finset (Finset α)) (S : Finset α) : Prop :=
  ∀ e ∈ E, ¬e ⊆ S

lemma badTriple_card (a : α → ℕ) {e : Finset α} (he : e ∈ badTriples a) :
    e.card = 3 := by
  rcases Finset.mem_image.mp he with ⟨p, hp, rfl⟩
  exact (Finset.mem_filter.mp hp).2.2

lemma badQuad_card (a : α → ℕ) {e : Finset α} (he : e ∈ badQuads a) :
    e.card = 4 := by
  rcases Finset.mem_image.mp he with ⟨p, hp, rfl⟩
  exact (Finset.mem_filter.mp hp).2.2

/-- Every nontrivial additive equality has a bad three- or four-point support. -/
lemma nontrivial_support_mem (a : α → ℕ) (hinj : Function.Injective a)
    {i j u v : α} (hsum : a i + a j = a u + a v)
    (hne : ({i, j} : Finset α) ≠ {u, v}) :
    ({i, j, u, v} : Finset α) ∈ badQuads a ∨
      ∃ e ∈ badTriples a, e ⊆ ({i, j, u, v} : Finset α) := by
  have hiu : i ≠ u := by
    intro hiu
    apply hne
    have hju : j = v := by
      apply hinj
      subst u
      omega
    subst u
    subst v
    rfl
  have hiv : i ≠ v := by
    intro hiv
    apply hne
    have hju : j = u := by
      apply hinj
      subst v
      omega
    subst v
    subst u
    simp [Finset.pair_comm]
  have hju : j ≠ u := by
    intro hju
    apply hne
    have hiv' : i = v := by
      apply hinj
      subst u
      omega
    subst u
    subst v
    simp [Finset.pair_comm]
  have hjv : j ≠ v := by
    intro hjv
    apply hne
    have hiu' : i = u := by
      apply hinj
      subst v
      omega
    subst v
    subst u
    rfl
  by_cases hij : i = j
  · subst j
    have huv : u ≠ v := by
      intro huv
      have hiu' : i = u := by
        apply hinj
        subst v
        omega
      exact hiu hiu'
    have hcard : ({i, u, v} : Finset α).card = 3 := by
      simp [hiu, hiv, huv, Ne.symm]
    right
    refine ⟨{i, u, v}, ?_, by simp⟩
    apply Finset.mem_image.mpr
    refine ⟨(i, (u, v)), ?_, rfl⟩
    simp [diagonalRelations, hsum, hcard]
  · by_cases huv : u = v
    · subst v
      have hij' : i ≠ j := hij
      have hcard : ({u, i, j} : Finset α).card = 3 := by
        simp [hiu, hju, hij', Ne.symm]
      right
      refine ⟨{u, i, j}, ?_, ?_⟩
      swap
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        aesop
      apply Finset.mem_image.mpr
      refine ⟨(u, (i, j)), ?_, rfl⟩
      simp [diagonalRelations, hsum.symm, hcard]
    · left
      apply Finset.mem_image.mpr
      refine ⟨((i, j), (u, v)), ?_, rfl⟩
      have hcard : ({i, j, u, v} : Finset α).card = 4 := by
        simp [hij, hiu, hiv, hju, hjv, huv, Ne.symm]
      simp [fourRelations, hsum, hcard]

/-- Avoiding the bad supports is exactly the implication needed for the Sidon
property. -/
lemma isSidon_of_edgeFree (a : α → ℕ) (hinj : Function.Injective a)
    (S : Finset α) (h3 : EdgeFree (badTriples a) S)
    (h4 : EdgeFree (badQuads a) S) : IsSidon a S := by
  intro i hi j hj u hu v hv hsum
  by_contra hne
  rcases nontrivial_support_mem a hinj hsum hne with hq | ⟨e, he, hes⟩
  · apply h4 _ hq
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hi
    · exact hj
    · exact hu
    · exact hv
  · apply h3 e he
    apply hes.trans
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hi
    · exact hj
    · exact hu
    · exact hv

end BadSupports

section Alteration

variable {α : Type*} [DecidableEq α]

/-- Delete at most one vertex for every nonempty edge. -/
lemma exists_edgeFree_subset (U : Finset α) (E : Finset (Finset α))
    (hne : ∀ e ∈ E, e.Nonempty) :
    ∃ S : Finset α, S ⊆ U ∧ EdgeFree E S ∧ U.card ≤ S.card + E.card := by
  induction E using Finset.induction_on generalizing U with
  | empty =>
      exact ⟨U, Finset.Subset.rfl, by simp [EdgeFree]⟩
  | @insert e E he ih =>
      have hneE : ∀ f ∈ E, f.Nonempty := fun f hf => hne f (Finset.mem_insert_of_mem hf)
      by_cases heU : e ⊆ U
      · have he_nonempty : e.Nonempty := hne e (by simp)
        obtain ⟨x, hx⟩ := he_nonempty
        obtain ⟨S, hSU, hfree, hcard⟩ := ih (U.erase x) hneE
        refine ⟨S, hSU.trans (Finset.erase_subset _ _), ?_, ?_⟩
        · intro f hf
          rcases Finset.mem_insert.mp hf with rfl | hf
          · intro heS
            have hxS := heS hx
            have hxErase := hSU hxS
            exact (Finset.notMem_erase x U) hxErase
          · exact hfree f hf
        · have hxU : x ∈ U := heU hx
          rw [Finset.card_insert_of_notMem he]
          rw [← Finset.card_erase_add_one hxU]
          omega
      · obtain ⟨S, hSU, hfree, hcard⟩ := ih U hneE
        refine ⟨S, hSU, ?_, ?_⟩
        · intro f hf
          rcases Finset.mem_insert.mp hf with rfl | hf
          · exact fun heS => heU (heS.trans hSU)
          · exact hfree f hf
        · rw [Finset.card_insert_of_notMem he]
          omega

end Alteration

section Averaging

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The vertices receiving colour zero.  The definition uses `.val = 0`, so it
also makes sense before a proof that the number of colours is positive is in
scope. -/
def zeroClass {q : ℕ} (f : α → Fin q) : Finset α :=
  Finset.univ.filter fun x => (f x).val = 0

/-- The number of edges from `E` surviving inside `U`. -/
def survivingEdges (E : Finset (Finset α)) (U : Finset α) : ℕ :=
  (E.filter fun e => e ⊆ U).card

lemma card_colorings_containing (q : ℕ) (hq : 0 < q) (e : Finset α) :
    ((Finset.univ : Finset (α → Fin q)).filter
      (fun f => e ⊆ zeroClass f)).card = q ^ (Fintype.card α - e.card) := by
  let z : Fin q := ⟨0, hq⟩
  let choices : α → Finset (Fin q) := fun x => if x ∈ e then {z} else Finset.univ
  have heq :
      (Finset.univ : Finset (α → Fin q)).filter (fun f => e ⊆ zeroClass f) =
        Fintype.piFinset choices := by
    ext f
    constructor
    · intro hf
      have hfsub := (Finset.mem_filter.mp hf).2
      apply Fintype.mem_piFinset.mpr
      intro x
      change f x ∈ (if x ∈ e then {z} else Finset.univ)
      split_ifs with hx
      · simp only [Finset.mem_singleton]
        apply Fin.ext
        have := hfsub hx
        simpa [zeroClass, z] using this
      · simp
    · intro hf
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro x hx
      have hx' := (Fintype.mem_piFinset.mp hf) x
      change f x ∈ (if x ∈ e then {z} else Finset.univ) at hx'
      simp [hx, z] at hx'
      have hval := congrArg Fin.val hx'
      simpa [zeroClass, z] using hval
  rw [heq, Fintype.card_piFinset]
  change (∏ x : α, (if x ∈ e then {z} else Finset.univ).card) = _
  calc
    (∏ x : α, (if x ∈ e then {z} else Finset.univ).card) =
        ∏ x : α, if x ∈ e then 1 else q := by
      congr 1 with x
      by_cases hx : x ∈ e <;> simp [hx]
    _ =
        ∏ x : α, if x ∈ (Finset.univ \ e) then q else 1 := by
      congr 1 with x
      by_cases hx : x ∈ e <;> simp [hx]
    _ = ∏ x ∈ (Finset.univ \ e), q := Finset.prod_ite_mem_eq _ _
    _ = q ^ (Finset.univ \ e).card := by simp
    _ = q ^ (Fintype.card α - e.card) := by
      rw [Finset.card_sdiff, Finset.card_univ]
      simp

lemma sum_zeroClass_card (q : ℕ) (hq : 0 < q) :
    ∑ f : α → Fin q, (zeroClass f).card =
      Fintype.card α * q ^ (Fintype.card α - 1) := by
  calc
    ∑ f : α → Fin q, (zeroClass f).card =
        ∑ f : α → Fin q, ∑ x : α, if x ∈ zeroClass f then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      simpa using
        (Finset.sum_boole (R := ℕ) (fun x => x ∈ zeroClass f) Finset.univ).symm
    _ = ∑ x : α, ∑ f : α → Fin q, if x ∈ zeroClass f then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x : α, q ^ (Fintype.card α - 1) := by
      apply Finset.sum_congr rfl
      intro x hx
      calc
        (∑ f : α → Fin q, if x ∈ zeroClass f then 1 else 0) =
            ((Finset.univ : Finset (α → Fin q)).filter
              (fun f => ({x} : Finset α) ⊆ zeroClass f)).card := by
          simpa using Finset.sum_boole
            (fun f : α → Fin q => ({x} : Finset α) ⊆ zeroClass f) Finset.univ
        _ = q ^ (Fintype.card α - ({x} : Finset α).card) :=
          card_colorings_containing q hq {x}
        _ = q ^ (Fintype.card α - 1) := by simp
    _ = Fintype.card α * q ^ (Fintype.card α - 1) := by simp

lemma sum_survivingEdges (q : ℕ) (hq : 0 < q) (E : Finset (Finset α))
    (r : ℕ) (hcard : ∀ e ∈ E, e.card = r) :
    ∑ f : α → Fin q, survivingEdges E (zeroClass f) =
      E.card * q ^ (Fintype.card α - r) := by
  calc
    ∑ f : α → Fin q, survivingEdges E (zeroClass f) =
        ∑ f : α → Fin q, ∑ e ∈ E, if e ⊆ zeroClass f then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      unfold survivingEdges
      exact (Finset.sum_boole (fun e => e ⊆ zeroClass f) E).symm
    _ = ∑ e ∈ E, ∑ f : α → Fin q, if e ⊆ zeroClass f then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ e ∈ E, q ^ (Fintype.card α - e.card) := by
      apply Finset.sum_congr rfl
      intro e he
      calc
        (∑ f : α → Fin q, if e ⊆ zeroClass f then 1 else 0) =
            ((Finset.univ : Finset (α → Fin q)).filter
              (fun f => e ⊆ zeroClass f)).card := by
          simpa using Finset.sum_boole
            (fun f : α → Fin q => e ⊆ zeroClass f) Finset.univ
        _ = q ^ (Fintype.card α - e.card) := card_colorings_containing q hq e
    _ = E.card * q ^ (Fintype.card α - r) := by
      apply Finset.sum_const_nat
      intro e he
      rw [hcard e he]

/-- The division-free finite averaging inequality for three- and four-uniform
edge families. -/
lemma exists_good_zeroClass (q : ℕ) (hq : 0 < q)
    (hn : 4 ≤ Fintype.card α) (E3 E4 : Finset (Finset α))
    (h3 : ∀ e ∈ E3, e.card = 3) (h4 : ∀ e ∈ E4, e.card = 4) :
    ∃ f : α → Fin q,
      q ^ 4 * (zeroClass f).card + q * E3.card + E4.card ≥
        q ^ 3 * Fintype.card α +
          q ^ 4 * (survivingEdges E3 (zeroClass f) +
            survivingEdges E4 (zeroClass f)) := by
  let n := Fintype.card α
  have hn1 : 1 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hpow1 : q ^ 4 * q ^ (n - 1) = q ^ 3 * q ^ n := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hpow3 : q * q ^ n = q ^ 4 * q ^ (n - 3) := by
    calc
      q * q ^ n = q ^ 1 * q ^ n := by rw [pow_one]
      _ = q ^ (1 + n) := by rw [pow_add]
      _ = q ^ (4 + (n - 3)) := by congr 1; omega
      _ = q ^ 4 * q ^ (n - 3) := by rw [pow_add]
  have hpow4 : q ^ n = q ^ 4 * q ^ (n - 4) := by
    nth_rewrite 1 [show n = 4 + (n - 4) by omega]
    rw [pow_add]
  have hsum_eq :
      ∑ f : α → Fin q,
          (q ^ 4 * (zeroClass f).card + q * E3.card + E4.card) =
        ∑ f : α → Fin q,
          (q ^ 3 * Fintype.card α +
            q ^ 4 * (survivingEdges E3 (zeroClass f) +
              survivingEdges E4 (zeroClass f))) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul]
    rw [sum_zeroClass_card q hq,
      sum_survivingEdges q hq E3 3 h3,
      sum_survivingEdges q hq E4 4 h4]
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
    dsimp [n] at hpow1 hpow3 hpow4 ⊢
    nlinarith
  by_contra hex
  push Not at hex
  have hlt :
      (∑ f : α → Fin q,
          (q ^ 4 * (zeroClass f).card + q * E3.card + E4.card)) <
        ∑ f : α → Fin q,
          (q ^ 3 * Fintype.card α +
            q ^ 4 * (survivingEdges E3 (zeroClass f) +
              survivingEdges E4 (zeroClass f))) := by
    have hfun : (Finset.univ : Finset (α → Fin q)).Nonempty :=
      ⟨fun _ => ⟨0, hq⟩, Finset.mem_univ _⟩
    apply Finset.sum_lt_sum_of_nonempty hfun
    intro f hf
    exact hex f
  exact (lt_irrefl _ (hsum_eq ▸ hlt))

/-- Averaging followed by deleting one vertex from every surviving edge. -/
lemma exists_large_edgeFree (q : ℕ) (hq : 0 < q)
    (hn : 4 ≤ Fintype.card α) (E3 E4 : Finset (Finset α))
    (h3 : ∀ e ∈ E3, e.card = 3) (h4 : ∀ e ∈ E4, e.card = 4) :
    ∃ S : Finset α, EdgeFree E3 S ∧ EdgeFree E4 S ∧
      q ^ 3 * Fintype.card α ≤ q ^ 4 * S.card + q * E3.card + E4.card := by
  obtain ⟨f, hf⟩ := exists_good_zeroClass q hq hn E3 E4 h3 h4
  let U := zeroClass f
  let F3 := E3.filter fun e => e ⊆ U
  let F4 := E4.filter fun e => e ⊆ U
  let E := F3 ∪ F4
  have hne : ∀ e ∈ E, e.Nonempty := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · have he3 := h3 e (Finset.mem_filter.mp he).1
      exact Finset.card_pos.mp (by omega)
    · have he4 := h4 e (Finset.mem_filter.mp he).1
      exact Finset.card_pos.mp (by omega)
  obtain ⟨S, hSU, hfree, hcard⟩ := exists_edgeFree_subset U E hne
  have hfree3 : EdgeFree E3 S := by
    intro e he heS
    apply hfree e
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨he, heS.trans hSU⟩
    · exact heS
  have hfree4 : EdgeFree E4 S := by
    intro e he heS
    apply hfree e
    · apply Finset.mem_union_right
      exact Finset.mem_filter.mpr ⟨he, heS.trans hSU⟩
    · exact heS
  have hEcard : E.card ≤ survivingEdges E3 U + survivingEdges E4 U := by
    dsimp [E, F3, F4, survivingEdges]
    exact Finset.card_union_le _ _
  refine ⟨S, hfree3, hfree4, ?_⟩
  dsimp [U] at hcard hEcard
  have hU : (zeroClass f).card ≤
      S.card + (survivingEdges E3 (zeroClass f) + survivingEdges E4 (zeroClass f)) :=
    hcard.trans (Nat.add_le_add_left hEcard S.card)
  have hmul := Nat.mul_le_mul_left (q ^ 4) hU
  nlinarith

end Averaging

section Scale

private lemma le_succ_cube (n : ℕ) : n ≤ (n + 1) ^ 3 := by
  calc
    n ≤ n + 1 := by omega
    _ ≤ (n + 1) * (n + 1) := Nat.le_mul_of_pos_right (n + 1) (by omega)
    _ ≤ ((n + 1) * (n + 1)) * (n + 1) :=
      Nat.le_mul_of_pos_right ((n + 1) * (n + 1)) (by omega)
    _ = (n + 1) ^ 3 := by ring

/-- The least positive natural number whose cube is at least `n`. -/
noncomputable def cubeCeil (n : ℕ) : ℕ :=
  Nat.find (show ∃ r : ℕ, 0 < r ∧ n ≤ r ^ 3 by
    exact ⟨n + 1, by omega, le_succ_cube n⟩)

lemma cubeCeil_pos (n : ℕ) : 0 < cubeCeil n := by
  exact (Nat.find_spec (show ∃ r : ℕ, 0 < r ∧ n ≤ r ^ 3 by
    exact ⟨n + 1, by omega, le_succ_cube n⟩)).1

lemma le_cubeCeil_cube (n : ℕ) : n ≤ cubeCeil n ^ 3 := by
  exact (Nat.find_spec (show ∃ r : ℕ, 0 < r ∧ n ≤ r ^ 3 by
    exact ⟨n + 1, by omega, le_succ_cube n⟩)).2

lemma cubeCeil_cube_le (n : ℕ) (hn : 0 < n) : cubeCeil n ^ 3 ≤ 8 * n := by
  let hex : ∃ r : ℕ, 0 < r ∧ n ≤ r ^ 3 := by
    exact ⟨n + 1, by omega, le_succ_cube n⟩
  change (Nat.find hex) ^ 3 ≤ 8 * n
  have hrpos : 0 < Nat.find hex := (Nat.find_spec hex).1
  by_cases hr : Nat.find hex = 1
  · rw [hr]
    norm_num
    omega
  · have hr2 : 2 ≤ Nat.find hex := by omega
    have hpredlt : Nat.find hex - 1 < Nat.find hex := by omega
    have hnot := Nat.find_min hex hpredlt
    have hpredpos : 0 < Nat.find hex - 1 := by omega
    have hpredcube : (Nat.find hex - 1) ^ 3 < n := by
      by_contra h
      apply hnot
      exact ⟨hpredpos, by omega⟩
    have hrle : Nat.find hex ≤ 2 * (Nat.find hex - 1) := by omega
    have hcub := Nat.pow_le_pow_left hrle 3
    nlinarith

end Scale

section FiniteBound

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The quantitative Alon--Erdős bound in a form avoiding roots: every
injectively labelled finite set with representation multiplicity at most `k`
has a Sidon subset `S` satisfying `|α|² ≤ 4096 (k+1)³ |S|³`. -/
theorem exists_sidon_cubic (a : α → ℕ) (hinj : Function.Injective a) (k : ℕ)
    (hrep : BoundedRepresentation a k) :
    ∃ S : Finset α, IsSidon a S ∧
      Fintype.card α ^ 2 ≤ 4096 * (k + 1) ^ 3 * S.card ^ 3 := by
  by_cases hn : 4 ≤ Fintype.card α
  · let r := cubeCeil (Fintype.card α)
    let q := 4 * (k + 1) * r
    have hq : 0 < q := by
      dsimp [q, r]
      have := cubeCeil_pos (Fintype.card α)
      positivity
    obtain ⟨S, hfree3, hfree4, hmain⟩ :=
      exists_large_edgeFree q hq hn (badTriples a) (badQuads a)
        (fun e he => badTriple_card a he) (fun e he => badQuad_card a he)
    refine ⟨S, isSidon_of_edgeFree a hinj S hfree3 hfree4, ?_⟩
    have htrip := card_badTriples_le a k hrep
    have hquad := card_badQuads_le a k hrep
    have hrpos : 0 < r := by
      dsimp [r]
      exact cubeCeil_pos (Fintype.card α)
    have hnle : Fintype.card α ≤ r ^ 3 := by
      dsimp [r]
      exact le_cubeCeil_cube (Fintype.card α)
    have hqbase : 4 * (k + 1) ≤ q := by
      dsimp [q]
      exact Nat.le_mul_of_pos_right (4 * (k + 1)) hrpos
    have hcoef3 : 4 * q * k ≤ q ^ 3 := by
      have hkq : 4 * k ≤ q ^ 2 := by
        calc
          4 * k ≤ 4 * (k + 1) := by omega
          _ ≤ q := hqbase
          _ ≤ q ^ 2 := by
            simpa [pow_two] using Nat.le_mul_of_pos_right q hq
      calc
        4 * q * k = q * (4 * k) := by ring
        _ ≤ q * q ^ 2 := by gcongr
        _ = q ^ 3 := by ring
    have hcoef4 : 4 * Fintype.card α * k ≤ q ^ 3 := by
      have hkpow : 4 * k ≤ 64 * (k + 1) ^ 3 := by
        have hm : k + 1 ≤ (k + 1) ^ 3 := by
          calc
            k + 1 ≤ (k + 1) * (k + 1) :=
              Nat.le_mul_of_pos_right (k + 1) (by omega)
            _ ≤ ((k + 1) * (k + 1)) * (k + 1) :=
              Nat.le_mul_of_pos_right ((k + 1) * (k + 1)) (by omega)
            _ = (k + 1) ^ 3 := by ring
        omega
      calc
        4 * Fintype.card α * k = Fintype.card α * (4 * k) := by ring
        _ ≤ r ^ 3 * (4 * k) := by gcongr
        _ ≤ r ^ 3 * (64 * (k + 1) ^ 3) := by gcongr
        _ = q ^ 3 := by dsimp [q]; ring
    have hloss3 :
        4 * (q * (badTriples a).card) ≤ q ^ 3 * Fintype.card α := by
      calc
        4 * (q * (badTriples a).card) ≤
            4 * (q * (Fintype.card α * k)) := by gcongr
        _ = Fintype.card α * (4 * q * k) := by ring
        _ ≤ Fintype.card α * q ^ 3 := by gcongr
        _ = q ^ 3 * Fintype.card α := by ring
    have hloss4 :
        4 * (badQuads a).card ≤ q ^ 3 * Fintype.card α := by
      calc
        4 * (badQuads a).card ≤ 4 * (Fintype.card α ^ 2 * k) := by gcongr
        _ = Fintype.card α * (4 * Fintype.card α * k) := by ring
        _ ≤ Fintype.card α * q ^ 3 := by gcongr
        _ = q ^ 3 * Fintype.card α := by ring
    have hloss :
        2 * (q * (badTriples a).card + (badQuads a).card) ≤
          q ^ 3 * Fintype.card α := by
      omega
    have htwice :
        q ^ 3 * Fintype.card α ≤ 2 * (q ^ 4 * S.card) := by
      nlinarith
    have hmul :
        q ^ 3 * Fintype.card α ≤ q ^ 3 * (2 * q * S.card) := by
      calc
        q ^ 3 * Fintype.card α ≤ 2 * (q ^ 4 * S.card) := htwice
        _ = q ^ 3 * (2 * q * S.card) := by ring
    have hnS : Fintype.card α ≤ 2 * q * S.card := by
      exact Nat.le_of_mul_le_mul_left hmul (by positivity : 0 < q ^ 3)
    have hrcube : r ^ 3 ≤ 8 * Fintype.card α := by
      dsimp [r]
      exact cubeCeil_cube_le (Fintype.card α) (by omega)
    have hqcube : q ^ 3 ≤ 512 * (k + 1) ^ 3 * Fintype.card α := by
      calc
        q ^ 3 = 64 * (k + 1) ^ 3 * r ^ 3 := by dsimp [q]; ring
        _ ≤ 64 * (k + 1) ^ 3 * (8 * Fintype.card α) := by gcongr
        _ = 512 * (k + 1) ^ 3 * Fintype.card α := by ring
    have hcubed := Nat.pow_le_pow_left hnS 3
    have hcubic :
        Fintype.card α ^ 3 ≤
          Fintype.card α * (4096 * (k + 1) ^ 3 * S.card ^ 3) := by
      calc
        Fintype.card α ^ 3 ≤ (2 * q * S.card) ^ 3 := hcubed
        _ = 8 * q ^ 3 * S.card ^ 3 := by ring
        _ ≤ 8 * (512 * (k + 1) ^ 3 * Fintype.card α) * S.card ^ 3 := by
          gcongr
        _ = Fintype.card α * (4096 * (k + 1) ^ 3 * S.card ^ 3) := by ring
    have hcubic' :
        Fintype.card α * Fintype.card α ^ 2 ≤
          Fintype.card α * (4096 * (k + 1) ^ 3 * S.card ^ 3) := by
      simpa [pow_succ, mul_assoc] using hcubic
    exact Nat.le_of_mul_le_mul_left hcubic' (by omega)
  · by_cases hzero : Fintype.card α = 0
    · refine ⟨∅, by simp [IsSidon], ?_⟩
      simp [hzero]
    · have huniv : (Finset.univ : Finset α).Nonempty :=
        Finset.card_pos.mp (by simpa using (Nat.pos_of_ne_zero hzero))
      obtain ⟨x, hx⟩ := huniv
      refine ⟨{x}, ?_, ?_⟩
      · intro i hi j hj u hu v hv hsum
        simp only [Finset.mem_singleton] at hi hj hu hv
        subst i
        subst j
        subst u
        subst v
        rfl
      · simp only [Finset.card_singleton, one_pow]
        have hcard : Fintype.card α ≤ 3 := by omega
        have hkpos : 0 < (k + 1) ^ 3 := by positivity
        have hk : 1 ≤ (k + 1) ^ 3 := by omega
        nlinarith

end FiniteBound

section FinsetTransfer

/-- Passing from a finset to its subtype does not change its ordered
representation counts. -/
lemma representationCount_subtype (A : Finset ℕ) (t : ℕ) :
    representationCount (fun x : ↥A => (x : ℕ)) t =
      ((A.product A).filter (fun p => p.1 + p.2 = t)).card := by
  classical
  let emb : (↥A × ↥A) ↪ (ℕ × ℕ) :=
    ⟨fun p => ((p.1 : ℕ), (p.2 : ℕ)), fun p q h => by
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst h)
      · exact Subtype.ext (congrArg Prod.snd h)⟩
  have hmap :
      (((Finset.univ.product Finset.univ).filter
          (fun p : ↥A × ↥A => (p.1 : ℕ) + (p.2 : ℕ) = t)).map emb) =
        (A.product A).filter (fun p => p.1 + p.2 = t) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_map.mp hp with ⟨w, hw, rfl⟩
      have hsum := (Finset.mem_filter.mp hw).2
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨w.1.property, w.2.property⟩, hsum⟩
    · intro hp
      obtain ⟨hpA, hsum⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpA
      apply Finset.mem_map.mpr
      refine ⟨(⟨p.1, hp1⟩, ⟨p.2, hp2⟩), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨by simp, by simp⟩, hsum⟩
  unfold representationCount
  rw [← hmap, Finset.card_map]

/-- The cubic Sidon bound stated directly for a finite set of naturals. -/
theorem exists_sidon_finset_cubic (A : Finset ℕ) (k : ℕ)
    (hrep : ∀ t, ((A.product A).filter (fun p => p.1 + p.2 = t)).card ≤ k) :
    ∃ S : Finset ℕ, S ⊆ A ∧ IsSidon id S ∧
      A.card ^ 2 ≤ 4096 * (k + 1) ^ 3 * S.card ^ 3 := by
  classical
  let emb : ↥A ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
  have hrep' : BoundedRepresentation (fun x : ↥A => (x : ℕ)) k := by
    intro t
    rw [representationCount_subtype]
    exact hrep t
  obtain ⟨S, hsid, hcubic⟩ :=
    exists_sidon_cubic (fun x : ↥A => (x : ℕ)) Subtype.val_injective k hrep'
  refine ⟨S.map emb, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact y.property
  · intro i hi j hj u hu v hv hsum
    simp only [Finset.mem_map] at hi hj hu hv
    obtain ⟨i', hi', rfl⟩ := hi
    obtain ⟨j', hj', rfl⟩ := hj
    obtain ⟨u', hu', rfl⟩ := hu
    obtain ⟨v', hv', rfl⟩ := hv
    have hpairs := hsid i' hi' j' hj' u' hu' v' hv' hsum
    have hmapped := congrArg (fun T : Finset ↥A => T.map emb) hpairs
    simpa [emb] using hmapped
  · simpa [emb] using hcubic

end FinsetTransfer

section ExtremalFunction

private lemma threshold_at_self (k n : ℕ) :
    n ^ 2 ≤ 4096 * (k + 1) ^ 3 * n ^ 3 := by
  by_cases hn : n = 0
  · simp [hn]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hcoefpos : 0 < 4096 * (k + 1) ^ 3 := by positivity
    have hcoef : 1 ≤ 4096 * (k + 1) ^ 3 := by omega
    calc
      n ^ 2 = n ^ 2 * 1 := by simp
      _ ≤ n ^ 2 * n := Nat.mul_le_mul_left (n ^ 2) hnpos
      _ = n ^ 3 := by ring
      _ ≤ 4096 * (k + 1) ^ 3 * n ^ 3 := by
        simpa using Nat.mul_le_mul_right (n ^ 3) hcoef

private lemma threshold_exists (k n : ℕ) :
    ∃ r : ℕ, n ^ 2 ≤ 4096 * (k + 1) ^ 3 * r ^ 3 :=
  ⟨n, threshold_at_self k n⟩

/-- The least integer size whose cube meets the quantitative bound. -/
noncomputable def sidonThreshold (k n : ℕ) : ℕ :=
  Nat.find (threshold_exists k n)

lemma sidonThreshold_spec (k n : ℕ) :
    n ^ 2 ≤ 4096 * (k + 1) ^ 3 * sidonThreshold k n ^ 3 :=
  Nat.find_spec (threshold_exists k n)

lemma sidonThreshold_min (k n r : ℕ)
    (hr : n ^ 2 ≤ 4096 * (k + 1) ^ 3 * r ^ 3) :
    sidonThreshold k n ≤ r :=
  Nat.find_min' (threshold_exists k n) hr

lemma sidonThreshold_le (k n : ℕ) : sidonThreshold k n ≤ n :=
  sidonThreshold_min k n n (threshold_at_self k n)

lemma H_guarantees (k n : ℕ) : Guarantees k n (H k n) := by
  classical
  have hmem : H k n ∈ guaranteedSizes k n := by
    exact Finset.max'_mem (guaranteedSizes k n) (guaranteedSizes_nonempty k n)
  have hparts : H k n ≤ n ∧ Guarantees k n (H k n) := by
    simpa [guaranteedSizes] using hmem
  exact hparts.2

lemma H_le (k n : ℕ) : H k n ≤ n := by
  classical
  have hmem : H k n ∈ guaranteedSizes k n := by
    exact Finset.max'_mem (guaranteedSizes k n) (guaranteedSizes_nonempty k n)
  have hparts : H k n ≤ n ∧ Guarantees k n (H k n) := by
    simpa [guaranteedSizes] using hmem
  exact hparts.1

lemma le_H (k n r : ℕ) (hrn : r ≤ n) (hr : Guarantees k n r) : r ≤ H k n := by
  classical
  apply Finset.le_max'
  simpa [guaranteedSizes] using And.intro hrn hr

/-- The threshold supplied by the alteration theorem really is guaranteed
for every admissible finite set. -/
theorem sidonThreshold_guaranteed (k n : ℕ) :
    Guarantees k n (sidonThreshold k n) := by
  intro A hA hrep
  obtain ⟨S, hSA, hsid, hcubic⟩ := exists_sidon_finset_cubic A k hrep
  refine ⟨S, hSA, hsid, ?_⟩
  apply sidonThreshold_min k n S.card
  simpa [hA] using hcubic

/-- The established `n^(2/3)` resolution, expressed as an exact cubic
natural-number inequality for the extremal function from the problem. -/
theorem H_cubic_lower_bound (k n : ℕ) :
    n ^ 2 ≤ 4096 * (k + 1) ^ 3 * H k n ^ 3 := by
  have hthreshold : sidonThreshold k n ≤ H k n :=
    le_H k n (sidonThreshold k n) (sidonThreshold_le k n)
      (sidonThreshold_guaranteed k n)
  calc
    n ^ 2 ≤ 4096 * (k + 1) ^ 3 * sidonThreshold k n ^ 3 :=
      sidonThreshold_spec k n
    _ ≤ 4096 * (k + 1) ^ 3 * H k n ^ 3 := by gcongr

/-- The same bound in the conventional real-power notation:
`n^(2/3) ≤ 16 (k+1) H_k(n)`. -/
theorem H_real_rpow_lower_bound (k n : ℕ) :
    (n : ℝ) ^ ((2 : ℝ) / 3) ≤ 16 * (k + 1) * H k n := by
  have hcubic :
      (n : ℝ) ^ 2 ≤ (16 * (k + 1) * H k n : ℝ) ^ 3 := by
    have hcast :
        (n : ℝ) ^ 2 ≤ 4096 * (k + 1) ^ 3 * (H k n : ℝ) ^ 3 := by
      exact_mod_cast H_cubic_lower_bound k n
    calc
      (n : ℝ) ^ 2 ≤ 4096 * (k + 1) ^ 3 * (H k n : ℝ) ^ 3 := hcast
      _ = (16 * (k + 1) * H k n : ℝ) ^ 3 := by ring
  have hroot := Real.rpow_le_rpow (sq_nonneg (n : ℝ)) hcubic
    (by positivity : 0 ≤ (3 : ℝ)⁻¹)
  have hlhs :
      (((n : ℝ) ^ 2) ^ (3 : ℝ)⁻¹) = (n : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg n) 2 (3 : ℝ)⁻¹]
    norm_num [div_eq_mul_inv]
  have hrhs :
      (((16 * (k + 1) * H k n : ℝ) ^ 3) ^ (3 : ℝ)⁻¹) =
        (16 * (k + 1) * H k n : ℝ) := by
    exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
  rw [hlhs, hrhs] at hroot
  exact hroot

/-- An explicit pointwise comparison used to answer the first question. -/
private lemma ratio_lower_bound (k n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ ((1 : ℝ) / 6) / (16 * (k + 1)) ≤
      (H k n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 2) := by
  let C : ℝ := 16 * (k + 1)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hC : 0 < C := by dsimp [C]; positivity
  have hden : 0 < (n : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hnreal _
  change (n : ℝ) ^ ((1 : ℝ) / 6) / C ≤
    (H k n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 2)
  apply (le_div_iff₀ hden).2
  have hmul :
      C * ((n : ℝ) ^ ((1 : ℝ) / 6) / C * (n : ℝ) ^ ((1 : ℝ) / 2)) ≤
        C * (H k n : ℝ) := by
    calc
      C * ((n : ℝ) ^ ((1 : ℝ) / 6) / C * (n : ℝ) ^ ((1 : ℝ) / 2)) =
          (n : ℝ) ^ ((1 : ℝ) / 6) * (n : ℝ) ^ ((1 : ℝ) / 2) := by
        field_simp
      _ = (n : ℝ) ^ ((1 : ℝ) / 6 + (1 : ℝ) / 2) := by
        rw [Real.rpow_add hnreal]
      _ = (n : ℝ) ^ ((2 : ℝ) / 3) := by norm_num
      _ ≤ C * H k n := by
        simpa [C] using H_real_rpow_lower_bound k n
  exact le_of_mul_le_mul_left hmul hC

/-- The answer to the first question in Problem 772: for every fixed `k`,
`H_k(n) / n^(1/2)` tends to infinity. -/
theorem erdos772_ratio_tendsto_atTop (k : ℕ) :
    Tendsto (fun n : ℕ =>
      (H k n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 2)) atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hscaled : Tendsto (fun n : ℕ =>
      (n : ℝ) ^ ((1 : ℝ) / 6) / (16 * (k + 1))) atTop atTop :=
    Tendsto.atTop_div_const (by positivity) hpow
  refine tendsto_atTop_mono' atTop ?_ hscaled
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact ratio_lower_bound k n hn

/-- The stronger question also has a positive answer.  The explicit choice
`c = 1/12` stays strictly below the proved exponent `2/3`; the fixed
`k`-dependent constant is absorbed for sufficiently large `n`. -/
theorem erdos772_eventually_power_improvement (k : ℕ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ ((1 : ℝ) / 2 + c) < H k n := by
  refine ⟨(1 : ℝ) / 12, by norm_num, ?_⟩
  let C : ℝ := 16 * (k + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 12)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop, C < (n : ℝ) ^ ((1 : ℝ) / 12) :=
    (tendsto_atTop.1 hpow (C + 1)).mono fun n hn => by linarith
  filter_upwards [hlarge, eventually_ge_atTop 1] with n hnlarge hn
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hpowerpos : 0 < (n : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 12) :=
    Real.rpow_pos_of_pos hnreal _
  have hmul :
      C * (n : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 12) <
        C * (H k n : ℝ) := by
    calc
      C * (n : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 12) <
          (n : ℝ) ^ ((1 : ℝ) / 12) *
            (n : ℝ) ^ ((1 : ℝ) / 2 + (1 : ℝ) / 12) :=
        mul_lt_mul_of_pos_right hnlarge hpowerpos
      _ = (n : ℝ) ^ ((1 : ℝ) / 12 +
          ((1 : ℝ) / 2 + (1 : ℝ) / 12)) := by
        exact (Real.rpow_add hnreal ((1 : ℝ) / 12)
          ((1 : ℝ) / 2 + (1 : ℝ) / 12)).symm
      _ = (n : ℝ) ^ ((2 : ℝ) / 3) := by norm_num
      _ ≤ C * H k n := by
        simpa [C] using H_real_rpow_lower_bound k n
  exact lt_of_mul_lt_mul_left hmul hC.le

/-- Erdős Problem 772, with the original hypothesis `k ≥ 1`: both the
ratio statement and the explicit positive-exponent improvement. -/
theorem erdos_772 (k : ℕ) (_hk : 1 ≤ k) :
    Tendsto (fun n : ℕ =>
      (H k n : ℝ) / (n : ℝ) ^ ((1 : ℝ) / 2)) atTop atTop ∧
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop,
        (n : ℝ) ^ ((1 : ℝ) / 2 + c) < H k n :=
  ⟨erdos772_ratio_tendsto_atTop k, erdos772_eventually_power_improvement k⟩

end ExtremalFunction

#print axioms erdos_772

end Erdos772
