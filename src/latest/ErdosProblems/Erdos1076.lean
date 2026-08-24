/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 1076.
https://www.erdosproblems.com/forum/thread/1076

Informal authors:
- Stefan Glock

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos1076.md
-/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Nat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Erdős Problem 1076

The displayed assertion in Problem 1076 is false as written.  Already for
`k = 5`, Glock proved that the true asymptotic constant is `1 / 5`, rather
than `1 / 6`.

This file gives a self-contained disproof, not relying on Glock's approximate
packing theorem.  On `23 * 23^d` vertices we construct a `(5,3)`-free
three-uniform hypergraph with `92 * (23^d)^2` triples.  Its normalized density
is `92 / 529 > 1 / 6`.

The construction replaces every block in an explicit packing of an
eleven-edge support graph by four triples.  The packing is obtained from a
cyclic graceful labeling over `ZMod 23` and a two-column orthogonal array.
The detailed mathematical proof and source audit are in `tex/1076.tex`.
-/

namespace Erdos1076

open Filter Finset
open scoped BigOperators Topology

noncomputable section

/-! ## The finite extremal problem -/

/-- A triple on a finite vertex type. -/
abbrev TripleOn (V : Type*) [DecidableEq V] := {s : Finset V // s.card = 3}

/-- A finite three-uniform hypergraph. -/
abbrev TripleSystemOn (V : Type*) [DecidableEq V] := Finset (TripleOn V)

/-- A three-uniform hypergraph on `Fin n`. -/
abbrev TripleSystem (n : ℕ) := TripleSystemOn (Fin n)

/-- The vertices spanned by a finite family of triples. -/
def verticesOn {V : Type*} [DecidableEq V]
    (C : TripleSystemOn V) : Finset V :=
  C.biUnion fun e ↦ e.1

/-- `FkFree k G` means that no `k - 2` triples of `G` span at most `k`
vertices.  For ambient order at least `k`, this is equivalent to avoiding the
family of all three-uniform hypergraphs with `k` vertices and `k - 2` edges
(isolated vertices may be added to a configuration spanning fewer vertices). -/
def FkFree {V : Type*} [DecidableEq V] (k : ℕ)
    (G : TripleSystemOn V) : Prop :=
  ∀ C : TripleSystemOn V, C ⊆ G → C.card = k - 2 →
    k < (verticesOn C).card

/-- The extremal number from Problem 1076, as a finite maximum. -/
noncomputable def extremalNumber (k n : ℕ) : ℕ :=
  by
    classical
    exact (Finset.univ : Finset (TripleSystem n)).sup fun G ↦
      if FkFree k G then G.card else 0

lemma card_le_extremalNumber {k n : ℕ} {G : TripleSystem n}
    (hG : FkFree k G) : G.card ≤ extremalNumber k n := by
  classical
  unfold extremalNumber
  have hs := Finset.le_sup
    (s := (Finset.univ : Finset (TripleSystem n)))
    (f := fun H ↦ if FkFree k H then H.card else 0)
    (Finset.mem_univ G)
  simpa [hG] using hs

/-! ## The six-role support pattern -/

abbrev Role := Fin 6
abbrev Pattern := Fin 4
abbrev F23 := ZMod 23

local instance primeTwentyThree : Fact (Nat.Prime 23) := ⟨by norm_num⟩

/-- The eleven edges of the support graph `H₂` from `tex/1076.tex`. -/
def Support (r s : Role) : Prop :=
  r ≠ s ∧
    (r = 0 ∨ s = 0 ∨
      (r = 1 ∧ 2 ≤ s.1) ∨ (s = 1 ∧ 2 ≤ r.1) ∨
      (r = 2 ∧ s = 3) ∨ (r = 3 ∧ s = 2) ∨
      (r = 4 ∧ s = 5) ∨ (r = 5 ∧ s = 4))

instance decidableSupport (r s : Role) : Decidable (Support r s) := by
  unfold Support
  infer_instance

/-- The four triples replacing one support block. -/
def roleTriple (i : Pattern) : Finset Role :=
  ![{0, 2, 3}, {1, 2, 3}, {0, 4, 5}, {1, 4, 5}] i

/-- A support pair contained in every role triple; used to recover its block. -/
def anchor₁ (i : Pattern) : Role := ![2, 2, 4, 4] i
def anchor₂ (i : Pattern) : Role := ![3, 3, 5, 5] i

/-- The graceful cyclic labeling of the six roles. -/
def baseLabel (r : Role) : F23 := ![0, 1, 3, 17, 5, 13] r

/-- Six distinct orthogonal-array coefficients. -/
def coefficient (r : Role) : F23 := ![0, 1, 2, 3, 4, 5] r

lemma roleTriple_card : ∀ i : Pattern, (roleTriple i).card = 3 := by
  decide

lemma roleTriple_injective : Function.Injective roleTriple := by
  decide

lemma anchor₁_mem : ∀ i : Pattern, anchor₁ i ∈ roleTriple i := by
  decide

lemma anchor₂_mem : ∀ i : Pattern, anchor₂ i ∈ roleTriple i := by
  decide

lemma anchor_ne : ∀ i : Pattern, anchor₁ i ≠ anchor₂ i := by
  decide

lemma support_anchor : ∀ i : Pattern, Support (anchor₁ i) (anchor₂ i) := by
  decide

lemma support_of_mem_roleTriple : ∀ (i : Pattern) (r s : Role),
    r ∈ roleTriple i → s ∈ roleTriple i → r ≠ s → Support r s := by
  decide

lemma baseLabel_injective : Function.Injective baseLabel := by
  decide

lemma coefficient_ne_of_support : ∀ {r s : Role}, Support r s →
    coefficient r ≠ coefficient s := by
  decide

abbrev DirectedSupportEdge := Fin 22

def edgeSource (e : DirectedSupportEdge) : Role :=
  ![0, 1, 0, 2, 0, 3, 0, 4, 0, 5, 1, 2, 1, 3, 1, 4, 1, 5, 2, 3, 4, 5] e

def edgeTarget (e : DirectedSupportEdge) : Role :=
  ![1, 0, 2, 0, 3, 0, 4, 0, 5, 0, 2, 1, 3, 1, 4, 1, 5, 1, 3, 2, 5, 4] e

lemma support_edge_index : ∀ (r s : Role), Support r s →
    ∃! e : DirectedSupportEdge, edgeSource e = r ∧ edgeTarget e = s := by
  unfold ExistsUnique
  decide

/-- The finite graceful-labeling check.  The cyclic directed differences of
the eleven support edges and their reversals are all distinct. -/
lemma edge_difference_injective : Function.Injective
    (fun e : DirectedSupportEdge ↦
      baseLabel (edgeTarget e) - baseLabel (edgeSource e)) := by
  decide

lemma base_difference_unique (r s r' s' : Role)
    (hrs : Support r s) (hrs' : Support r' s')
    (h : baseLabel s - baseLabel r = baseLabel s' - baseLabel r') :
    r = r' ∧ s = s' := by
  obtain ⟨e, he, _⟩ := support_edge_index r s hrs
  obtain ⟨e', he', _⟩ := support_edge_index r' s' hrs'
  have heq : e = e' := edge_difference_injective (by simpa [he, he'] using h)
  subst e'
  exact ⟨he.1.symm.trans he'.1, he.2.symm.trans he'.2⟩

/-- The cyclic distances of the eleven support edges are, in order,
`1,3,6,5,10,2,7,4,11,9,8`; hence their translates partition the ordered pairs
of distinct elements of `ZMod 23`. -/
lemma base_ordered_pair_unique (t u : F23) (r s r' s' : Role)
    (hrs : Support r s) (hrs' : Support r' s')
    (h₁ : t + baseLabel r = u + baseLabel r')
    (h₂ : t + baseLabel s = u + baseLabel s') :
    t = u ∧ r = r' ∧ s = s' := by
  have hdiff : baseLabel s - baseLabel r =
      baseLabel s' - baseLabel r' := by
    calc
      baseLabel s - baseLabel r =
          (t + baseLabel s) - (t + baseLabel r) := by ring
      _ = (u + baseLabel s') - (u + baseLabel r') := by rw [h₁, h₂]
      _ = baseLabel s' - baseLabel r' := by ring
  obtain ⟨hr, hs⟩ := base_difference_unique r s r' s' hrs hrs' hdiff
  subst r'
  subst s'
  exact ⟨add_right_cancel h₁, rfl, rfl⟩

/-! ## Orthogonal-array blow-up -/

/-- The growing vector-space coordinate. -/
abbrev W (d : ℕ) := Fin d → F23

/-- Vertices in the `d`th counterexample. -/
abbrev Vertex (d : ℕ) := F23 × W d

/-- Parameters for one support block. -/
structure BlockParam (d : ℕ) where
  shift : F23
  offset : W d
  slope : W d
deriving DecidableEq, Fintype

/-- The vertex playing role `r` in a parameterized support block. -/
def blockVertex {d : ℕ} (P : BlockParam d) (r : Role) : Vertex d :=
  (P.shift + baseLabel r, P.offset + coefficient r • P.slope)

lemma blockVertex_injective {d : ℕ} (P : BlockParam d) :
    Function.Injective (blockVertex P) := by
  intro r s hrs
  apply baseLabel_injective
  have h := congrArg Prod.fst hrs
  simpa [blockVertex] using add_left_cancel h

/-- Two distinct coefficient columns determine the offset and slope. -/
lemma oa_pair_injective {𝕜 M : Type*} [Field 𝕜] [AddCommGroup M] [Module 𝕜 M]
    {a b : 𝕜} (hab : a ≠ b) :
    Function.Injective
      (fun z : M × M ↦ (z.1 + a • z.2, z.1 + b • z.2)) := by
  rintro ⟨p, q⟩ ⟨p', q'⟩ h
  have h₁ : p + a • q = p' + a • q' := congrArg Prod.fst h
  have h₂ : p + b • q = p' + b • q' := congrArg Prod.snd h
  have hqsmul : (b - a) • q = (b - a) • q' := by
    calc
      (b - a) • q = (p + b • q) - (p + a • q) := by module
      _ = (p' + b • q') - (p' + a • q') := by rw [h₁, h₂]
      _ = (b - a) • q' := by module
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hq : q = q' := by
    have h := congrArg (fun z : M ↦ (b - a)⁻¹ • z) hqsmul
    simpa [smul_smul, hba] using h
  have hp : p = p' := by
    simpa [hq] using h₁
  exact Prod.ext hp hq

/-- A support pair uniquely determines its block parameter. -/
lemma blockParam_eq_of_pair_eq {d : ℕ} {P Q : BlockParam d}
    {r s r' s' : Role} (hrs : Support r s) (hrs' : Support r' s')
    (h₁ : blockVertex P r = blockVertex Q r')
    (h₂ : blockVertex P s = blockVertex Q s') :
    P = Q := by
  have hbase := base_ordered_pair_unique P.shift Q.shift r s r' s' hrs hrs'
    (congrArg Prod.fst h₁) (congrArg Prod.fst h₂)
  rcases hbase with ⟨hshift, hr, hs⟩
  subst r'
  subst s'
  have hmicro₁ : P.offset + coefficient r • P.slope =
      Q.offset + coefficient r • Q.slope := congrArg Prod.snd h₁
  have hmicro₂ : P.offset + coefficient s • P.slope =
      Q.offset + coefficient s • Q.slope := congrArg Prod.snd h₂
  have hpair :
      (P.offset + coefficient r • P.slope,
        P.offset + coefficient s • P.slope) =
      (Q.offset + coefficient r • Q.slope,
        Q.offset + coefficient s • Q.slope) :=
    Prod.ext hmicro₁ hmicro₂
  have hpq : (P.offset, P.slope) = (Q.offset, Q.slope) :=
    oa_pair_injective (coefficient_ne_of_support hrs) hpair
  cases P
  cases Q
  simp_all

/-! ## The constructed hypergraph -/

/-- One of the four triples belonging to a support block. -/
def constructionTriple {d : ℕ} (P : BlockParam d) (i : Pattern) :
    TripleOn (Vertex d) := by
  refine ⟨(roleTriple i).image (blockVertex P), ?_⟩
  rw [Finset.card_image_of_injective _ (blockVertex_injective P)]
  exact roleTriple_card i

@[simp] lemma mem_constructionTriple_iff {d : ℕ} {P : BlockParam d}
    {i : Pattern} {v : Vertex d} :
    v ∈ (constructionTriple P i).1 ↔
      ∃ r ∈ roleTriple i, blockVertex P r = v := by
  simp [constructionTriple]

lemma constructionTriple_injective {d : ℕ} :
    Function.Injective
      (fun z : BlockParam d × Pattern ↦ constructionTriple z.1 z.2) := by
  rintro ⟨P, i⟩ ⟨Q, j⟩ h
  change constructionTriple P i = constructionTriple Q j at h
  have ha₁ : blockVertex P (anchor₁ i) ∈ (constructionTriple Q j).1 := by
    rw [← h]
    exact mem_constructionTriple_iff.mpr
      ⟨anchor₁ i, anchor₁_mem i, rfl⟩
  have ha₂ : blockVertex P (anchor₂ i) ∈ (constructionTriple Q j).1 := by
    rw [← h]
    exact mem_constructionTriple_iff.mpr
      ⟨anchor₂ i, anchor₂_mem i, rfl⟩
  obtain ⟨r', hr'j, hr'⟩ := mem_constructionTriple_iff.mp ha₁
  obtain ⟨s', hs'j, hs'⟩ := mem_constructionTriple_iff.mp ha₂
  have hrs' : r' ≠ s' := by
    intro hrs
    apply anchor_ne i
    apply blockVertex_injective P
    rw [← hr', ← hs', hrs]
  have hPQ : P = Q := blockParam_eq_of_pair_eq (support_anchor i)
    (support_of_mem_roleTriple j r' s' hr'j hs'j hrs') hr'.symm hs'.symm
  subst Q
  change constructionTriple P i = constructionTriple P j at h
  have hrole : roleTriple i = roleTriple j := by
    ext r
    constructor
    · intro hri
      have hv : blockVertex P r ∈ (constructionTriple P j).1 := by
        rw [← h]
        exact mem_constructionTriple_iff.mpr ⟨r, hri, rfl⟩
      obtain ⟨s, hsj, hs⟩ := mem_constructionTriple_iff.mp hv
      have : r = s := blockVertex_injective P hs.symm
      simpa [this] using hsj
    · intro hrj
      have hv : blockVertex P r ∈ (constructionTriple P i).1 := by
        rw [h]
        exact mem_constructionTriple_iff.mpr ⟨r, hrj, rfl⟩
      obtain ⟨s, hsi, hs⟩ := mem_constructionTriple_iff.mp hv
      have : r = s := blockVertex_injective P hs.symm
      simpa [this] using hsi
  have hij : i = j := roleTriple_injective hrole
  exact Prod.ext rfl hij

/-- The explicit counterexample on `23 * 23^d` vertices. -/
def construction (d : ℕ) : TripleSystemOn (Vertex d) :=
  (Finset.univ : Finset (BlockParam d × Pattern)).image
    (fun z ↦ constructionTriple z.1 z.2)

/-- The parameter structure is the evident three-fold product. -/
def blockParamEquiv (d : ℕ) : BlockParam d ≃ F23 × (W d × W d) where
  toFun P := (P.shift, P.offset, P.slope)
  invFun z := ⟨z.1, z.2.1, z.2.2⟩
  left_inv P := by cases P; rfl
  right_inv z := by cases z; rfl

lemma card_construction (d : ℕ) :
    (construction d).card = 92 * (23 ^ d) ^ 2 := by
  classical
  rw [construction, Finset.card_image_of_injective _ constructionTriple_injective]
  rw [Finset.card_univ]
  rw [Fintype.card_prod, Fintype.card_fin]
  have hparam : Fintype.card (BlockParam d) = 23 * (23 ^ d * 23 ^ d) := by
    rw [Fintype.card_congr (blockParamEquiv d)]
    simp [W]
  rw [hparam]
  ring

/-! ## The `(5,3)`-free property -/

lemma image_inter_of_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) (A B : Finset α) :
    A.image f ∩ B.image f = (A ∩ B).image f := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩
    have hab : a = b := hf (hax.trans hbx.symm)
    subst b
    exact ⟨a, ⟨ha, hb⟩, hax⟩
  · rintro ⟨a, ⟨ha, hb⟩, hax⟩
    exact ⟨⟨a, ha, hax⟩, ⟨a, hb, hax⟩⟩

lemma card_inter_constructionTriple {d : ℕ} (P : BlockParam d) (i j : Pattern) :
    ((constructionTriple P i).1 ∩ (constructionTriple P j).1).card =
      (roleTriple i ∩ roleTriple j).card := by
  change (((roleTriple i).image (blockVertex P)) ∩
      ((roleTriple j).image (blockVertex P))).card = _
  rw [image_inter_of_injective (blockVertex_injective P),
    Finset.card_image_of_injective _ (blockVertex_injective P)]

lemma card_union_constructionTriple {d : ℕ} (P : BlockParam d) (i j : Pattern) :
    ((constructionTriple P i).1 ∪ (constructionTriple P j).1).card =
      (roleTriple i ∪ roleTriple j).card := by
  change (((roleTriple i).image (blockVertex P)) ∪
      ((roleTriple j).image (blockVertex P))).card = _
  rw [← Finset.image_union,
    Finset.card_image_of_injective _ (blockVertex_injective P)]

lemma card_inter_union_constructionTriple {d : ℕ} (P : BlockParam d)
    (i j k : Pattern) :
    ((constructionTriple P k).1 ∩
        ((constructionTriple P i).1 ∪ (constructionTriple P j).1)).card =
      (roleTriple k ∩ (roleTriple i ∪ roleTriple j)).card := by
  change (((roleTriple k).image (blockVertex P)) ∩
      (((roleTriple i).image (blockVertex P)) ∪
        ((roleTriple j).image (blockVertex P)))).card = _
  rw [← Finset.image_union,
    image_inter_of_injective (blockVertex_injective P),
    Finset.card_image_of_injective _ (blockVertex_injective P)]

@[simp] lemma mem_union_constructionTriple_iff {d : ℕ} {P : BlockParam d}
    {i j : Pattern} {v : Vertex d} :
    v ∈ (constructionTriple P i).1 ∪ (constructionTriple P j).1 ↔
      ∃ r ∈ roleTriple i ∪ roleTriple j, blockVertex P r = v := by
  simp only [Finset.mem_union, mem_constructionTriple_iff]
  aesop

lemma blockParam_eq_of_common_pair {d : ℕ} {P Q : BlockParam d}
    {i j : Pattern} {x y : Vertex d}
    (hxP : x ∈ (constructionTriple P i).1)
    (hyP : y ∈ (constructionTriple P i).1)
    (hxQ : x ∈ (constructionTriple Q j).1)
    (hyQ : y ∈ (constructionTriple Q j).1)
    (hxy : x ≠ y) : P = Q := by
  obtain ⟨r, hri, hr⟩ := mem_constructionTriple_iff.mp hxP
  obtain ⟨s, hsi, hs⟩ := mem_constructionTriple_iff.mp hyP
  obtain ⟨r', hr'j, hr'⟩ := mem_constructionTriple_iff.mp hxQ
  obtain ⟨s', hs'j, hs'⟩ := mem_constructionTriple_iff.mp hyQ
  have hrs : r ≠ s := by
    intro h
    apply hxy
    rw [← hr, ← hs, h]
  have hrs' : r' ≠ s' := by
    intro h
    apply hxy
    rw [← hr', ← hs', h]
  exact blockParam_eq_of_pair_eq
    (support_of_mem_roleTriple i r s hri hsi hrs)
    (support_of_mem_roleTriple j r' s' hr'j hs'j hrs')
    (hr.trans hr'.symm) (hs.trans hs'.symm)

lemma role_union_card_of_large_inter : ∀ (i j : Pattern), i ≠ j →
    2 ≤ (roleTriple i ∩ roleTriple j).card →
    (roleTriple i ∪ roleTriple j).card = 4 := by
  decide

lemma support_of_mem_paired_union : ∀ (i j : Pattern), i ≠ j →
    2 ≤ (roleTriple i ∩ roleTriple j).card →
    ∀ (r s : Role), r ∈ roleTriple i ∪ roleTriple j →
    s ∈ roleTriple i ∪ roleTriple j → r ≠ s → Support r s := by
  decide

lemma no_third_pattern : ∀ (i j k : Pattern),
    i ≠ j → i ≠ k → j ≠ k →
    2 ≤ (roleTriple i ∩ roleTriple j).card →
    2 ≤ (roleTriple k ∩ (roleTriple i ∪ roleTriple j)).card → False := by
  decide

lemma blockParam_eq_of_common_pair_with_union {d : ℕ}
    {P Q : BlockParam d} {i j k : Pattern} {x y : Vertex d}
    (hij : i ≠ j)
    (hinter : 2 ≤ (roleTriple i ∩ roleTriple j).card)
    (hxP : x ∈ (constructionTriple P i).1 ∪ (constructionTriple P j).1)
    (hyP : y ∈ (constructionTriple P i).1 ∪ (constructionTriple P j).1)
    (hxQ : x ∈ (constructionTriple Q k).1)
    (hyQ : y ∈ (constructionTriple Q k).1)
    (hxy : x ≠ y) : P = Q := by
  obtain ⟨r, hrP, hr⟩ := mem_union_constructionTriple_iff.mp hxP
  obtain ⟨s, hsP, hs⟩ := mem_union_constructionTriple_iff.mp hyP
  obtain ⟨r', hr'k, hr'⟩ := mem_constructionTriple_iff.mp hxQ
  obtain ⟨s', hs'k, hs'⟩ := mem_constructionTriple_iff.mp hyQ
  have hrs : r ≠ s := by
    intro h
    apply hxy
    rw [← hr, ← hs, h]
  have hrs' : r' ≠ s' := by
    intro h
    apply hxy
    rw [← hr', ← hs', h]
  exact blockParam_eq_of_pair_eq
    (support_of_mem_paired_union i j hij hinter r s hrP hsP hrs)
    (support_of_mem_roleTriple k r' s' hr'k hs'k hrs')
    (hr.trans hr'.symm) (hs.trans hs'.symm)

lemma three_triples_have_large_intersection {V : Type*} [DecidableEq V]
    {A B C : Finset V} (hA : A.card = 3) (hB : B.card = 3) (hC : C.card = 3)
    (hsmall : (A ∪ B ∪ C).card ≤ 5) :
    2 ≤ (A ∩ B).card ∨ 2 ≤ (A ∩ C).card ∨ 2 ≤ (B ∩ C).card := by
  by_contra h
  push Not at h
  have hAB : (A ∩ B).card ≤ 1 := by omega
  have hAC : (A ∩ C).card ≤ 1 := by omega
  have hBC : (B ∩ C).card ≤ 1 := by omega
  have hABcard := Finset.card_union_add_card_inter A B
  have hABlower : 5 ≤ (A ∪ B).card := by omega
  have hinter_subset : (A ∪ B) ∩ C ⊆ (A ∩ C) ∪ (B ∩ C) := by
    intro x hx
    simp only [Finset.mem_inter, Finset.mem_union] at hx ⊢
    rcases hx.1 with hxA | hxB
    · exact Or.inl ⟨hxA, hx.2⟩
    · exact Or.inr ⟨hxB, hx.2⟩
  have hinter_le : ((A ∪ B) ∩ C).card ≤ 2 := by
    calc
      ((A ∪ B) ∩ C).card ≤ ((A ∩ C) ∪ (B ∩ C)).card :=
        Finset.card_le_card hinter_subset
      _ ≤ (A ∩ C).card + (B ∩ C).card := Finset.card_union_le _ _
      _ ≤ 2 := by omega
  have htotal := Finset.card_union_add_card_inter (A ∪ B) C
  omega

lemma no_small_union_of_first_large_intersection {d : ℕ}
    {P Q R : BlockParam d} {i j k : Pattern}
    (hPQedge : constructionTriple P i ≠ constructionTriple Q j)
    (hPRedge : constructionTriple P i ≠ constructionTriple R k)
    (hQRedge : constructionTriple Q j ≠ constructionTriple R k)
    (hinter : 2 ≤
      ((constructionTriple P i).1 ∩ (constructionTriple Q j).1).card) :
    5 < ((constructionTriple P i).1 ∪ (constructionTriple Q j).1 ∪
      (constructionTriple R k).1).card := by
  by_contra hspan
  have hspan' : ((constructionTriple P i).1 ∪ (constructionTriple Q j).1 ∪
      (constructionTriple R k).1).card ≤ 5 := by omega
  have hinter_pos : 1 <
      ((constructionTriple P i).1 ∩ (constructionTriple Q j).1).card := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hinter_pos
  have hxmem := Finset.mem_inter.mp hx
  have hymem := Finset.mem_inter.mp hy
  have hPQ : P = Q :=
    blockParam_eq_of_common_pair hxmem.1 hymem.1 hxmem.2 hymem.2 hxy
  subst Q
  have hij : i ≠ j := by
    intro hij
    exact hPQedge (by subst j; rfl)
  have hinterRole : 2 ≤ (roleTriple i ∩ roleTriple j).card := by
    rw [← card_inter_constructionTriple P i j]
    exact hinter
  have hunionCard :
      ((constructionTriple P i).1 ∪ (constructionTriple P j).1).card = 4 := by
    rw [card_union_constructionTriple]
    exact role_union_card_of_large_inter i j hij hinterRole
  have hthirdInter : 2 ≤
      ((constructionTriple R k).1 ∩
        ((constructionTriple P i).1 ∪ (constructionTriple P j).1)).card := by
    rw [Finset.inter_comm]
    have hcount := Finset.card_union_add_card_inter
      ((constructionTriple P i).1 ∪ (constructionTriple P j).1)
      (constructionTriple R k).1
    have hthirdCard := (constructionTriple R k).2
    rw [Finset.union_assoc] at hspan'
    omega
  have hthirdInterPos : 1 <
      ((constructionTriple R k).1 ∩
        ((constructionTriple P i).1 ∪ (constructionTriple P j).1)).card := by omega
  obtain ⟨x', hx', y', hy', hxy'⟩ := Finset.one_lt_card.mp hthirdInterPos
  have hx'mem := Finset.mem_inter.mp hx'
  have hy'mem := Finset.mem_inter.mp hy'
  have hPR : P = R := blockParam_eq_of_common_pair_with_union hij hinterRole
    hx'mem.2 hy'mem.2 hx'mem.1 hy'mem.1 hxy'
  subst R
  have hik : i ≠ k := by
    intro hik
    exact hPRedge (by subst k; rfl)
  have hjk : j ≠ k := by
    intro hjk
    exact hQRedge (by subst k; rfl)
  have hthirdRole : 2 ≤
      (roleTriple k ∩ (roleTriple i ∪ roleTriple j)).card := by
    rw [← card_inter_union_constructionTriple P i j k]
    exact hthirdInter
  exact no_third_pattern i j k hij hik hjk hinterRole hthirdRole

lemma three_construction_triples_span_gt_five {d : ℕ}
    {P Q R : BlockParam d} {i j k : Pattern}
    (hPQ : constructionTriple P i ≠ constructionTriple Q j)
    (hPR : constructionTriple P i ≠ constructionTriple R k)
    (hQR : constructionTriple Q j ≠ constructionTriple R k) :
    5 < ((constructionTriple P i).1 ∪ (constructionTriple Q j).1 ∪
      (constructionTriple R k).1).card := by
  by_contra h
  have hsmall : ((constructionTriple P i).1 ∪ (constructionTriple Q j).1 ∪
      (constructionTriple R k).1).card ≤ 5 := by omega
  rcases three_triples_have_large_intersection
      (constructionTriple P i).2 (constructionTriple Q j).2
      (constructionTriple R k).2 hsmall with hPQinter | hPRinter | hQRinter
  · exact (not_lt_of_ge hsmall)
      (no_small_union_of_first_large_intersection hPQ hPR hQR hPQinter)
  · have hlarge := no_small_union_of_first_large_intersection hPR hPQ hQR.symm hPRinter
    apply (not_lt_of_ge hsmall)
    simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hlarge
  · have hlarge := no_small_union_of_first_large_intersection hQR hPQ.symm hPR.symm hQRinter
    apply (not_lt_of_ge hsmall)
    simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using hlarge

@[simp] lemma mem_construction_iff {d : ℕ} {e : TripleOn (Vertex d)} :
    e ∈ construction d ↔ ∃ P : BlockParam d, ∃ i : Pattern,
      constructionTriple P i = e := by
  simp [construction]

/-- The explicit construction contains no three triples spanning at most five
vertices. -/
theorem construction_F5Free (d : ℕ) : FkFree 5 (construction d) := by
  intro C hC hcard
  have hcard3 : C.card = 3 := by omega
  obtain ⟨A, B, D, hAB, hAD, hBD, rfl⟩ := Finset.card_eq_three.mp hcard3
  have hA : A ∈ construction d := hC (by simp)
  have hB : B ∈ construction d := hC (by simp)
  have hD : D ∈ construction d := hC (by simp)
  obtain ⟨P, i, rfl⟩ := mem_construction_iff.mp hA
  obtain ⟨Q, j, rfl⟩ := mem_construction_iff.mp hB
  obtain ⟨R, k, rfl⟩ := mem_construction_iff.mp hD
  have hvertices : verticesOn
      ({constructionTriple P i, constructionTriple Q j, constructionTriple R k} :
        TripleSystemOn (Vertex d)) =
      (constructionTriple P i).1 ∪ (constructionTriple Q j).1 ∪
        (constructionTriple R k).1 := by
    simp [verticesOn, Finset.union_assoc]
  rw [hvertices]
  exact three_construction_triples_span_gt_five hAB hAD hBD

/-! ## Transport to the canonical vertex type `Fin n` -/

/-- An equivalence of vertex types induces an equivalence of triples. -/
def tripleEquiv {V X : Type*} [DecidableEq V] [DecidableEq X]
    (e : V ≃ X) : TripleOn V ≃ TripleOn X where
  toFun T := ⟨T.1.map e.toEmbedding, by simpa using T.2⟩
  invFun T := ⟨T.1.map e.symm.toEmbedding, by simpa using T.2⟩
  left_inv T := by
    apply Subtype.ext
    ext v
    simp
  right_inv T := by
    apply Subtype.ext
    ext v
    simp

/-- Transport of triple systems along a vertex equivalence. -/
def systemEquiv {V X : Type*} [DecidableEq V] [DecidableEq X]
    (e : V ≃ X) : TripleSystemOn V ≃ TripleSystemOn X :=
  (tripleEquiv e).finsetCongr

@[simp] lemma card_systemEquiv {V X : Type*} [DecidableEq V] [DecidableEq X]
    (e : V ≃ X) (G : TripleSystemOn V) :
    (systemEquiv e G).card = G.card := by
  simp [systemEquiv]

lemma verticesOn_systemEquiv {V X : Type*} [DecidableEq V] [DecidableEq X]
    (e : V ≃ X) (G : TripleSystemOn V) :
    verticesOn (systemEquiv e G) = (verticesOn G).map e.toEmbedding := by
  ext x
  simp only [verticesOn, Finset.mem_biUnion, systemEquiv,
    Equiv.finsetCongr_apply, Finset.mem_map]
  constructor
  · rintro ⟨T', ⟨T, hTG, hT⟩, hxT'⟩
    subst T'
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    refine ⟨T, hTG, ?_⟩
    simpa [tripleEquiv] using hxT'
  · rintro ⟨y, ⟨T, hTG, hyT⟩, hyx⟩
    subst x
    refine ⟨tripleEquiv e T, ?_, ?_⟩
    · exact ⟨T, hTG, rfl⟩
    · simpa [tripleEquiv] using hyT

@[simp] lemma card_verticesOn_systemEquiv {V X : Type*}
    [DecidableEq V] [DecidableEq X] (e : V ≃ X) (G : TripleSystemOn V) :
    (verticesOn (systemEquiv e G)).card = (verticesOn G).card := by
  rw [verticesOn_systemEquiv]
  exact Finset.card_map _

lemma FkFree_systemEquiv {V X : Type*} [DecidableEq V] [DecidableEq X]
    {k : ℕ} (e : V ≃ X) {G : TripleSystemOn V} (hG : FkFree k G) :
    FkFree k (systemEquiv e G) := by
  intro C hCG hcard
  let D : TripleSystemOn V := (systemEquiv e).symm C
  have hback : systemEquiv e D = C := by
    exact (systemEquiv e).apply_symm_apply C
  have hDG : D ⊆ G := by
    intro T hTD
    have hTC : tripleEquiv e T ∈ C := by
      rw [← hback]
      simpa [systemEquiv] using hTD
    have hmap : tripleEquiv e T ∈ systemEquiv e G := hCG hTC
    simpa [systemEquiv] using hmap
  have hDcard : D.card = k - 2 := by
    rw [← card_systemEquiv e D, hback]
    exact hcard
  have hsparse := hG D hDG hDcard
  have hvcard : (verticesOn D).card = (verticesOn C).card := by
    rw [← card_verticesOn_systemEquiv e D, hback]
  omega

lemma card_Vertex (d : ℕ) : Fintype.card (Vertex d) = 23 * 23 ^ d := by
  simp [Vertex, W]

/-- The construction transported to `Fin (23 * 23^d)`. -/
noncomputable def finConstruction (d : ℕ) : TripleSystem (23 * 23 ^ d) :=
  let e : Vertex d ≃ Fin (23 * 23 ^ d) :=
    Fintype.equivOfCardEq (by simp)
  systemEquiv e (construction d)

lemma card_finConstruction (d : ℕ) :
    (finConstruction d).card = 92 * (23 ^ d) ^ 2 := by
  simp [finConstruction, card_construction]

lemma finConstruction_F5Free (d : ℕ) : FkFree 5 (finConstruction d) := by
  unfold finConstruction
  exact FkFree_systemEquiv _ (construction_F5Free d)

/-- The extremal function at `k = 5` is bounded below by the explicit family. -/
theorem extremalNumber_five_lower (d : ℕ) :
    92 * (23 ^ d) ^ 2 ≤ extremalNumber 5 (23 * 23 ^ d) := by
  rw [← card_finConstruction d]
  exact card_le_extremalNumber (finConstruction_F5Free d)

lemma self_le_pow_twentyThree (n : ℕ) : n ≤ 23 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hpos : 0 < 23 ^ n := pow_pos (by decide) _
      nlinarith

/-- The literal universal assertion asked in Problem 1076. -/
def Problem1076Claim : Prop :=
  ∀ k : ℕ, 5 ≤ k →
    Tendsto
      (fun n : ℕ ↦ (extremalNumber k n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (1 / 6 : ℝ))

/-- **Resolution of Erdős Problem 1076.**  The displayed assertion is false:
the case `k = 5` has density bounded below by `92 / 529`, strictly exceeding
`1 / 6`, along the unbounded sequence `23 * 23^d`. -/
theorem not_erdos_1076 : ¬ (∀ k : ℕ, 5 ≤ k →
  Filter.Tendsto
    (fun n : ℕ ↦ (Erdos1076.extremalNumber k n : ℝ) / (n : ℝ) ^ 2)
    Filter.atTop (nhds (1 / 6 : ℝ))) := by
  intro hclaim
  have hfive := hclaim 5 (by omega)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hfive (1 / 276 : ℝ) (by norm_num)
  let m : ℕ := 23 ^ N
  let n : ℕ := 23 * m
  have hmpos : 0 < m := by positivity
  have hnN : N ≤ n := by
    have hNm : N ≤ m := by simpa [m] using self_le_pow_twentyThree N
    dsimp [n]
    nlinarith
  have hclose := hN n hnN
  rw [Real.dist_eq] at hclose
  have hupper :
      (extremalNumber 5 n : ℝ) / (n : ℝ) ^ 2 <
        (1 / 6 : ℝ) + 1 / 276 := by
    linarith [abs_lt.mp hclose]
  have hlowerNat : 92 * m ^ 2 ≤ extremalNumber 5 n := by
    simpa [m, n] using extremalNumber_five_lower N
  have hlowerCast : (92 : ℝ) * (m : ℝ) ^ 2 ≤ extremalNumber 5 n := by
    exact_mod_cast hlowerNat
  have hnpos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hlower : (92 / 529 : ℝ) ≤
      (extremalNumber 5 n : ℝ) / (n : ℝ) ^ 2 := by
    apply (le_div_iff₀ hnpos).2
    calc
      (92 / 529 : ℝ) * (n : ℝ) ^ 2 = 92 * (m : ℝ) ^ 2 := by
        norm_num [n]
        ring
      _ ≤ (extremalNumber 5 n : ℝ) := hlowerCast
  norm_num at hupper hlower
  linarith

end

end Erdos1076

#print axioms Erdos1076.not_erdos_1076

alias _root_.Erdos1076.erdos_1076 := _root_.Erdos1076.not_erdos_1076
