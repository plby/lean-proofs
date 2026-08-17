/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
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

import ErdosProblems.Erdos636.External.Erdos88.Foundations
import ErdosProblems.Erdos636.External.Erdos88.FiniteES
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Rich induced subgraphs in Ramsey graphs

This file formalizes Definition 4.3 of
Kwan--Sah--Sauermann--Sawhney and elementary finite tools used in their
proof of Lemma 4.4.  All cardinal inequalities are stated over `ℝ`; this
keeps the real parameters and the rounding in the published statement
visible.
-/

open SimpleGraph

namespace Erdos88

universe u

noncomputable section

section Richness

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The neighbours of `v` which lie in `W`.  This formulation uses only the
finite ambient type; unlike `SimpleGraph.neighborFinset`, it does not require
a separate local-finiteness instance. -/
def neighborsIn (G : SimpleGraph V) (v : V) (W : Finset V) : Finset V :=
  letI := Classical.decPred fun w ↦ G.Adj v w
  W.filter fun w ↦ G.Adj v w

@[simp] lemma mem_neighborsIn {G : SimpleGraph V} {v w : V} {W : Finset V} :
    w ∈ neighborsIn G v W ↔ w ∈ W ∧ G.Adj v w := by
  simp [neighborsIn]

/-- The vertices whose neighbourhood in `W` is unusually small or unusually
large.  This is the exceptional set in KSSS Definition 4.3. -/
def exceptionalVertices (G : SimpleGraph V) (W : Finset V) (ρ : ℝ) : Finset V :=
  Finset.univ.filter fun v ↦
    ((neighborsIn G v W).card : ℝ) ≤ ρ * W.card ∨
      ((W \ neighborsIn G v W).card : ℝ) ≤ ρ * W.card

/-- KSSS Definition 4.3.  An `M`-vertex graph is `(δ,ρ,α)`-rich when
every set of at least `δ M` vertices has at most `M^α` exceptional
vertices. -/
def Rich (G : SimpleGraph V) (δ ρ α : ℝ) : Prop :=
  ∀ W : Finset V,
    δ * Fintype.card V ≤ W.card →
      ((exceptionalVertices G W ρ).card : ℝ) ≤
        (Fintype.card V : ℝ) ^ α

@[simp] lemma mem_exceptionalVertices {G : SimpleGraph V} {W : Finset V}
    {ρ : ℝ} {v : V} :
    v ∈ exceptionalVertices G W ρ ↔
      ((neighborsIn G v W).card : ℝ) ≤ ρ * W.card ∨
        ((W \ neighborsIn G v W).card : ℝ) ≤ ρ * W.card := by
  simp [exceptionalVertices]

lemma exceptionalVertices_subset_univ (G : SimpleGraph V) (W : Finset V) (ρ : ℝ) :
    exceptionalVertices G W ρ ⊆ Finset.univ := by
  exact Finset.subset_univ _

/-- Increasing the minimum permitted size of the test set preserves
richness. -/
lemma Rich.mono_delta {G : SimpleGraph V} {δ₁ δ₂ ρ α : ℝ}
    (h : Rich G δ₁ ρ α) (hδ : δ₁ ≤ δ₂) : Rich G δ₂ ρ α := by
  intro W hW
  exact h W (le_trans (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)) hW)

/-- Decreasing the exceptional-neighbourhood threshold preserves
richness. -/
lemma Rich.anti_rho {G : SimpleGraph V} {δ ρ₁ ρ₂ α : ℝ}
    (h : Rich G δ ρ₂ α) (hρ : ρ₁ ≤ ρ₂) : Rich G δ ρ₁ α := by
  intro W hW
  refine le_trans ?_ (h W hW)
  norm_cast
  apply Finset.card_le_card
  intro v hv
  simp only [mem_exceptionalVertices] at hv ⊢
  rcases hv with hv | hv
  · exact Or.inl (le_trans hv (mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg _)))
  · exact Or.inr (le_trans hv (mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg _)))

/-- On a nonempty vertex type, increasing the exponent preserves richness. -/
lemma Rich.mono_alpha [Nonempty V] {G : SimpleGraph V} {δ ρ α₁ α₂ : ℝ}
    (h : Rich G δ ρ α₁) (hα : α₁ ≤ α₂) : Rich G δ ρ α₂ := by
  intro W hW
  refine le_trans (h W hW) ?_
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Fintype.card_pos) hα

/-- For exponent at least one, the exceptional-vertex bound is automatic. -/
lemma rich_of_one_le_alpha [Nonempty V] (G : SimpleGraph V) (δ ρ : ℝ)
    {α : ℝ} (hα : 1 ≤ α) : Rich G δ ρ α := by
  intro W _hW
  have hcard :
      ((exceptionalVertices G W ρ).card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Finset.card_le_univ (exceptionalVertices G W ρ)
  refine hcard.trans ?_
  have hbase : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos
  simpa using Real.rpow_le_rpow_of_exponent_le hbase hα

/-- If the size cutoff exceeds the whole vertex set, richness is vacuous. -/
lemma rich_of_one_lt_delta (G : SimpleGraph V) (ρ α : ℝ) { δ : ℝ }
    (hδ : 1 < δ) : Rich G δ ρ α := by
  intro W hW
  have hcard : (W.card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Finset.card_le_univ W
  have hzero : Fintype.card V = 0 := by
    by_contra hn
    have hpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    nlinarith
  haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hzero
  simpa [exceptionalVertices] using Real.rpow_nonneg (show (0 : ℝ) ≤ 0 by rfl) α

/-- A cardinal form of failure of richness, useful for the nested-set
construction in the proof of KSSS Lemma 4.4. -/
lemma not_rich_iff (G : SimpleGraph V) (δ ρ α : ℝ) :
    ¬ Rich G δ ρ α ↔
      ∃ W : Finset V,
        δ * Fintype.card V ≤ W.card ∧
          (Fintype.card V : ℝ) ^ α <
            (exceptionalVertices G W ρ).card := by
  constructor
  · intro h
    simp only [Rich, Classical.not_forall, Classical.not_imp, not_le] at h
    obtain ⟨W, hW, hbad⟩ := h
    exact ⟨W, hW, hbad⟩
  · rintro ⟨W, hW, hbad⟩ hrich
    exact (not_lt_of_ge (hrich W hW)) hbad

/-- The low-neighbour and high-neighbour portions of the exceptional set. -/
def lowExceptionalVertices (G : SimpleGraph V) (W : Finset V) (ρ : ℝ) : Finset V :=
  Finset.univ.filter fun v ↦
    ((neighborsIn G v W).card : ℝ) ≤ ρ * W.card

def highExceptionalVertices (G : SimpleGraph V) (W : Finset V) (ρ : ℝ) : Finset V :=
  Finset.univ.filter fun v ↦
    ((W \ neighborsIn G v W).card : ℝ) ≤ ρ * W.card

lemma exceptionalVertices_eq_union (G : SimpleGraph V) (W : Finset V) (ρ : ℝ) :
    exceptionalVertices G W ρ =
      lowExceptionalVertices G W ρ ∪ highExceptionalVertices G W ρ := by
  ext v
  simp [exceptionalVertices, lowExceptionalVertices, highExceptionalVertices, or_comm]

lemma exceptionalVertices_inter_eq_union (G : SimpleGraph V) (U W : Finset V) (ρ : ℝ) :
    exceptionalVertices G W ρ ∩ U =
      (lowExceptionalVertices G W ρ ∩ U) ∪
        (highExceptionalVertices G W ρ ∩ U) := by
  rw [exceptionalVertices_eq_union, Finset.union_inter_distrib_right]

/-- If there are more than `2k` exceptional vertices, then one of the two
one-sided exceptional sets has more than `k` vertices. -/
lemma exists_large_oneSided_exceptional {G : SimpleGraph V} {W : Finset V}
    {ρ : ℝ} {k : ℕ} (h : 2 * k < (exceptionalVertices G W ρ).card) :
    k < (lowExceptionalVertices G W ρ).card ∨
      k < (highExceptionalVertices G W ρ).card := by
  rw [exceptionalVertices_eq_union] at h
  have hu := Finset.card_union_le (lowExceptionalVertices G W ρ)
    (highExceptionalVertices G W ρ)
  omega

/-- Pigeonhole the exceptional vertices inside an ambient set and extract an
exactly sized one-sided exceptional block.  This is the selection step for
the sets `Sᵢ` in KSSS Lemma 4.4. -/
lemma exists_oneSided_exceptional_block {G : SimpleGraph V} {U W : Finset V}
    {ρ : ℝ} {q : ℕ} (h : 2 * q < (exceptionalVertices G W ρ ∩ U).card) :
    ∃ S : Finset V,
      S ⊆ U ∧ S.card = q ∧
        ((∀ v ∈ S, ((neighborsIn G v W).card : ℝ) ≤ ρ * W.card) ∨
          (∀ v ∈ S,
            ((W \ neighborsIn G v W).card : ℝ) ≤ ρ * W.card)) := by
  rw [exceptionalVertices_inter_eq_union] at h
  have hu := Finset.card_union_le
    (lowExceptionalVertices G W ρ ∩ U) (highExceptionalVertices G W ρ ∩ U)
  have hone :
      q < (lowExceptionalVertices G W ρ ∩ U).card ∨
        q < (highExceptionalVertices G W ρ ∩ U).card := by
    omega
  rcases hone with hlo | hhi
  · obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (Nat.le_of_lt hlo)
    refine ⟨S, hSsub.trans Finset.inter_subset_right, hScard, Or.inl ?_⟩
    intro v hv
    have hmem := hSsub hv
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      lowExceptionalVertices] at hmem
    exact hmem.1
  · obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (Nat.le_of_lt hhi)
    refine ⟨S, hSsub.trans Finset.inter_subset_right, hScard, Or.inr ?_⟩
    intro v hv
    have hmem := hSsub hv
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
      highExceptionalVertices] at hmem
    exact hmem.1

/-- Neighbourhoods in an induced graph are obtained by transporting the
corresponding ambient neighbourhood to the subtype. -/
lemma neighborsIn_induce_image {G : SimpleGraph V} {U : Finset V}
    (v : U) (W : Finset U) :
    (neighborsIn (G.induce (U : Set V)) v W).image Subtype.val =
      neighborsIn G v.1 (W.image Subtype.val) := by
  ext w
  simp [and_left_comm, and_comm]

lemma card_neighborsIn_induce {G : SimpleGraph V} {U : Finset V}
    (v : U) (W : Finset U) :
    (neighborsIn (G.induce (U : Set V)) v W).card =
      (neighborsIn G v.1 (W.image Subtype.val)).card := by
  rw [← neighborsIn_induce_image (G := G) v W, Finset.card_image_iff.mpr]
  exact Subtype.val_injective.injOn

lemma sdiff_neighborsIn_induce_image {G : SimpleGraph V} {U : Finset V}
    (v : U) (W : Finset U) :
    (W \ neighborsIn (G.induce (U : Set V)) v W).image Subtype.val =
      W.image Subtype.val \ neighborsIn G v.1 (W.image Subtype.val) := by
  rw [Finset.image_sdiff _ _ Subtype.val_injective,
    neighborsIn_induce_image]

lemma card_sdiff_neighborsIn_induce {G : SimpleGraph V} {U : Finset V}
    (v : U) (W : Finset U) :
    (W \ neighborsIn (G.induce (U : Set V)) v W).card =
      (W.image Subtype.val \ neighborsIn G v.1 (W.image Subtype.val)).card := by
  rw [← sdiff_neighborsIn_induce_image (G := G) v W, Finset.card_image_iff.mpr]
  exact Subtype.val_injective.injOn

/-- Ambient form of richness for an induced graph on `U`. -/
def RichOn (G : SimpleGraph V) (U : Finset V) (δ ρ α : ℝ) : Prop :=
  ∀ W : Finset V,
    W ⊆ U →
      δ * U.card ≤ W.card →
        (((exceptionalVertices G W ρ) ∩ U).card : ℝ) ≤ (U.card : ℝ) ^ α

/-- Failure of the ambient induced-graph formulation exposes a large test
set and too many exceptional vertices. -/
lemma not_richOn_iff (G : SimpleGraph V) (U : Finset V) (δ ρ α : ℝ) :
    ¬ RichOn G U δ ρ α ↔
      ∃ W : Finset V,
        W ⊆ U ∧ δ * U.card ≤ W.card ∧
          (U.card : ℝ) ^ α < (exceptionalVertices G W ρ ∩ U).card := by
  constructor
  · intro h
    simp only [RichOn, Classical.not_forall, Classical.not_imp, not_le] at h
    obtain ⟨W, hWU, hW, hbad⟩ := h
    exact ⟨W, hWU, hW, hbad⟩
  · rintro ⟨W, hWU, hW, hbad⟩ hrich
    exact (not_lt_of_ge (hrich W hWU hW)) hbad

/-- A failed richness test produces the next one-sided block of the KSSS
nested construction, once the desired block size is below half of the
exceptional-set lower bound. -/
lemma failure_produces_oneSided_block {G : SimpleGraph V} {U : Finset V}
    {δ ρ α : ℝ} {q : ℕ} (hfail : ¬ RichOn G U δ ρ α)
    (hq : (2 : ℝ) * q ≤ (U.card : ℝ) ^ α) :
    ∃ (W S : Finset V),
      W ⊆ U ∧ δ * U.card ≤ W.card ∧
        S ⊆ U ∧ S.card = q ∧
          ((∀ v ∈ S, ((neighborsIn G v W).card : ℝ) ≤ ρ * W.card) ∨
            (∀ v ∈ S,
              ((W \ neighborsIn G v W).card : ℝ) ≤ ρ * W.card)) := by
  obtain ⟨W, hWU, hW, hbad⟩ := (not_richOn_iff G U δ ρ α).mp hfail
  have hq' : 2 * q < (exceptionalVertices G W ρ ∩ U).card := by
    exact_mod_cast lt_of_le_of_lt hq hbad
  obtain ⟨S, hSU, hScard, hside⟩ := exists_oneSided_exceptional_block hq'
  exact ⟨W, S, hWU, hW, hSU, hScard, hside⟩

/-- `RichOn` is exactly Definition 4.3 applied to the induced graph. -/
lemma rich_induce_iff_richOn (G : SimpleGraph V) (U : Finset V) (δ ρ α : ℝ) :
    Rich (G.induce (U : Set V)) δ ρ α ↔ RichOn G U δ ρ α := by
  classical
  constructor
  · intro h W hWU hW
    let W' : Finset U := W.preimage Subtype.val Subtype.val_injective.injOn
    have himage : W'.image Subtype.val = W := by
      ext w
      constructor
      · simp only [W', Finset.mem_image, Finset.mem_preimage]
        rintro ⟨v, hv, rfl⟩
        exact hv
      · intro hw
        simp only [W', Finset.mem_image, Finset.mem_preimage]
        exact ⟨⟨w, hWU hw⟩, hw, rfl⟩
    have hcardW : W'.card = W.card := by
      rw [← himage, Finset.card_image_iff.mpr Subtype.val_injective.injOn]
    have hbound := h W' (by simpa [hcardW] using hW)
    have hexceptional :
        (exceptionalVertices (G.induce (U : Set V)) W' ρ).image Subtype.val =
          exceptionalVertices G W ρ ∩ U := by
      ext w
      simp only [Finset.mem_image, mem_exceptionalVertices, Finset.mem_inter]
      constructor
      · rintro ⟨v, hv, rfl⟩
        have hvU : (v.1 : V) ∈ U := v.2
        rw [card_neighborsIn_induce, card_sdiff_neighborsIn_induce, himage, hcardW] at hv
        exact ⟨hv, hvU⟩
      · rintro ⟨hw, hwU⟩
        let v : U := ⟨w, hwU⟩
        refine ⟨v, ?_, rfl⟩
        rw [card_neighborsIn_induce, card_sdiff_neighborsIn_induce, himage, hcardW]
        exact hw
    rw [← hexceptional, Finset.card_image_iff.mpr Subtype.val_injective.injOn]
    convert hbound using 1 <;> simp

  · intro h W hW
    let WI : Finset V := W.image Subtype.val
    have hWIU : WI ⊆ U := by
      intro w hw
      simp only [WI, Finset.mem_image] at hw
      obtain ⟨v, _hv, rfl⟩ := hw
      exact v.2
    have hcard : WI.card = W.card :=
      Finset.card_image_iff.mpr Subtype.val_injective.injOn
    have hbound := h WI hWIU (by simpa [hcard] using hW)
    have hexceptional :
        (exceptionalVertices (G.induce (U : Set V)) W ρ).image Subtype.val =
          exceptionalVertices G WI ρ ∩ U := by
      ext w
      simp only [Finset.mem_image, mem_exceptionalVertices, Finset.mem_inter]
      constructor
      · rintro ⟨v, hv, rfl⟩
        rw [card_neighborsIn_induce, card_sdiff_neighborsIn_induce] at hv
        refine ⟨?_, v.2⟩
        change
          ((neighborsIn G v.1 WI).card : ℝ) ≤ ρ * W.card ∨
            ((WI \ neighborsIn G v.1 WI).card : ℝ) ≤ ρ * W.card at hv
        rw [hcard]
        exact hv
      · rintro ⟨hw, hwU⟩
        let v : U := ⟨w, hwU⟩
        refine ⟨v, ?_, rfl⟩
        rw [card_neighborsIn_induce, card_sdiff_neighborsIn_induce]
        change
          ((neighborsIn G v.1 WI).card : ℝ) ≤ ρ * WI.card ∨
            ((WI \ neighborsIn G v.1 WI).card : ℝ) ≤ ρ * WI.card at hw
        rw [hcard] at hw
        exact hw
    rw [← hexceptional] at hbound
    rw [Finset.card_image_iff.mpr Subtype.val_injective.injOn] at hbound
    convert hbound using 1 <;> simp

/-- Arithmetic endpoint of the KSSS Lemma 4.4 density contradiction.
Once the nested blocks give density at most `4ρ + 1/K`, this contradicts
an Erdős--Szemerédi lower density constant `a` as soon as the former is
strictly smaller than `a`. -/
lemma richness_density_contradiction_endpoint
    {a ρ invK : ℝ} {q E : ℕ} (hq : 0 < q)
    (hgap : 4 * ρ + invK < a)
    (hlower : a * (q : ℝ) ^ 2 ≤ E)
    (hupper : (E : ℝ) ≤ (4 * ρ + invK) * (q : ℝ) ^ 2) : False := by
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  nlinarith [sq_pos_of_pos hqreal]

/-- Finite Markov-counting lemma in the exact form used in the nested-set
construction: if the total mass is at most half of `T |U|`, then at least
half the elements have mass at most `T`. -/
lemma half_le_card_filter_of_sum_le (U : Finset V) (f : V → ℝ) (T : ℝ)
    (hT : 0 < T) (hf : ∀ v ∈ U, 0 ≤ f v)
    (hsum : ∑ v ∈ U, f v ≤ T * U.card / 2) :
    (U.card : ℝ) / 2 ≤ (U.filter fun v ↦ f v ≤ T).card := by
  classical
  let bad := U.filter fun v ↦ ¬ f v ≤ T
  have hlower : (bad.card : ℝ) * T ≤ ∑ v ∈ bad, f v := by
    have hraw := Finset.card_nsmul_le_sum bad f T (by
      intro v hv
      simp only [bad, Finset.mem_filter] at hv
      exact le_of_lt (lt_of_not_ge hv.2))
    simpa [nsmul_eq_mul, mul_comm] using hraw
  have hsubsum : ∑ v ∈ bad, f v ≤ ∑ v ∈ U, f v := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun v hvU _ ↦ hf v hvU)
  have hcards := Finset.card_filter_add_card_filter_not (s := U) (p := fun v ↦ f v ≤ T)
  change (U.card : ℝ) / 2 ≤ ((U.filter fun v ↦ f v ≤ T).card : ℝ)
  have hcardsReal :
      ((U.filter fun v ↦ f v ≤ T).card : ℝ) + bad.card = U.card := by
    exact_mod_cast hcards
  nlinarith

/-- Neighbours in an arbitrary finite relation. -/
def relNeighbors (r : V → V → Prop) (v : V) (W : Finset V) : Finset V :=
  letI := Classical.decPred (r v)
  W.filter (r v)

@[simp] lemma mem_relNeighbors {r : V → V → Prop} {v w : V} {W : Finset V} :
    w ∈ relNeighbors r v W ↔ w ∈ W ∧ r v w := by
  simp [relNeighbors]

/-- Double counting a symmetric relation between two finite sets. -/
lemma sum_card_relNeighbors_comm (r : V → V → Prop)
    (hsymm : ∀ v w, r v w ↔ r w v) (S W : Finset V) :
    ∑ v ∈ S, (relNeighbors r v W).card =
      ∑ w ∈ W, (relNeighbors r w S).card := by
  classical
  calc
    ∑ v ∈ S, (relNeighbors r v W).card =
        ∑ v ∈ S, (W.bipartiteAbove r v).card := by
      apply Finset.sum_congr rfl
      intro v _hv
      simp [relNeighbors, Finset.bipartiteAbove]
    _ = ∑ w ∈ W, (S.bipartiteBelow r w).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (r := r) (s := S) (t := W)
    _ = ∑ w ∈ W, (relNeighbors r w S).card := by
      apply Finset.sum_congr rfl
      intro w _hw
      congr 1
      ext v
      simp [hsymm]

/-- One step of the nested-set construction in KSSS Lemma 4.4, uniformly
for adjacency or non-adjacency. -/
lemma oneSided_block_retains_quarter (r : V → V → Prop)
    (hsymm : ∀ v w, r v w ↔ r w v)
    {W S : Finset V} {ρ : ℝ} (hρ : 0 < ρ) (hS : 0 < S.card)
    (hsmall : ∀ v ∈ S,
      ((relNeighbors r v W).card : ℝ) ≤ ρ * W.card)
    (hhalf : (2 : ℝ) * S.card ≤ W.card) :
    ∃ U : Finset V,
      U ⊆ W \ S ∧ (W.card : ℝ) / 4 ≤ U.card ∧
        ∀ u ∈ U,
          ((relNeighbors r u S).card : ℝ) ≤ 4 * ρ * S.card := by
  classical
  let T := W \ S
  have hTcard : (W.card : ℝ) / 2 ≤ T.card := by
    have hinter : (S ∩ W).card ≤ S.card := Finset.card_le_card Finset.inter_subset_left
    have hdiff : T.card = W.card - (S ∩ W).card := by
      simpa [T] using (Finset.card_sdiff (s := S) (t := W))
    have hhalfNat : 2 * S.card ≤ W.card := by exact_mod_cast hhalf
    have hWTNat : W.card ≤ 2 * T.card := by omega
    have hWTReal : (W.card : ℝ) ≤ 2 * T.card := by exact_mod_cast hWTNat
    linarith
  have hWT : (W.card : ℝ) ≤ 2 * T.card := by linarith
  have hdouble :
      ∑ v ∈ S, (relNeighbors r v T).card =
        ∑ u ∈ T, (relNeighbors r u S).card :=
    sum_card_relNeighbors_comm r hsymm S T
  have hsumST :
      ∑ v ∈ S, ((relNeighbors r v T).card : ℝ) ≤
        ρ * S.card * W.card := by
    calc
      ∑ v ∈ S, ((relNeighbors r v T).card : ℝ) ≤
          ∑ _v ∈ S, ρ * W.card := by
        apply Finset.sum_le_sum
        intro v hv
        exact (Nat.cast_le.mpr (Finset.card_le_card
          (show relNeighbors r v T ⊆ relNeighbors r v W by
            intro w hw
            simp only [mem_relNeighbors] at hw ⊢
            exact ⟨Finset.sdiff_subset hw.1, hw.2⟩))).trans (hsmall v hv)
      _ = ρ * S.card * W.card := by
        simp [mul_assoc, mul_comm, mul_left_comm]
  have hsumT :
      ∑ u ∈ T, ((relNeighbors r u S).card : ℝ) ≤
        (4 * ρ * S.card) * T.card / 2 := by
    have hcast :
        ∑ v ∈ S, ((relNeighbors r v T).card : ℝ) =
          ∑ u ∈ T, ((relNeighbors r u S).card : ℝ) := by
      exact_mod_cast hdouble
    rw [← hcast]
    refine hsumST.trans ?_
    have hnonneg : 0 ≤ ρ * S.card := mul_nonneg hρ.le (Nat.cast_nonneg _)
    nlinarith
  let U := T.filter fun u ↦
    ((relNeighbors r u S).card : ℝ) ≤ 4 * ρ * S.card
  have hthreshold : 0 < 4 * ρ * (S.card : ℝ) := by positivity
  have hmarkov := half_le_card_filter_of_sum_le T
    (fun u ↦ ((relNeighbors r u S).card : ℝ)) (4 * ρ * S.card)
    hthreshold (fun _ _ ↦ Nat.cast_nonneg _) hsumT
  refine ⟨U, Finset.filter_subset _ _, ?_, ?_⟩
  · change (W.card : ℝ) / 4 ≤ U.card
    change (T.card : ℝ) / 2 ≤ U.card at hmarkov
    linarith
  · intro u hu
    exact (Finset.mem_filter.mp hu).2

@[simp] lemma relNeighbors_adj (G : SimpleGraph V) (v : V) (W : Finset V) :
    relNeighbors G.Adj v W = neighborsIn G v W := by
  ext w
  simp

@[simp] lemma relNeighbors_not_adj (G : SimpleGraph V) (v : V) (W : Finset V) :
    relNeighbors (fun x y ↦ ¬ G.Adj x y) v W = W \ neighborsIn G v W := by
  ext w
  simp only [mem_relNeighbors, Finset.mem_sdiff, mem_neighborsIn]
  constructor
  · rintro ⟨hw, hn⟩
    exact ⟨hw, by rintro ⟨_hw, ha⟩; exact hn ha⟩
  · rintro ⟨hw, hn⟩
    exact ⟨hw, fun ha ↦ hn ⟨hw, ha⟩⟩

/-- The complete one-step form used in the iteration for KSSS Lemma 4.4.
If the induced graph on `U` is not rich, an exceptional block `S` can be
removed while retaining a quarter of the witnessing set.  All vertices of
the residual set see `S` sparsely, either in the graph or in its complement.
-/
lemma failed_richness_nested_step {G : SimpleGraph V} {U : Finset V}
    {δ ρ α : ℝ} {q : ℕ} (hρ : 0 < ρ) (hqpos : 0 < q)
    (hfail : ¬ RichOn G U δ ρ α)
    (hqpow : (2 : ℝ) * q ≤ (U.card : ℝ) ^ α)
    (hqW : (2 : ℝ) * q ≤ δ * U.card) :
    ∃ (U' S : Finset V),
      U' ⊆ U ∧ S ⊆ U ∧ Disjoint U' S ∧ S.card = q ∧
        δ * U.card / 4 ≤ U'.card ∧
          ((∀ u ∈ U',
              ((neighborsIn G u S).card : ℝ) ≤ 4 * ρ * S.card) ∨
            (∀ u ∈ U',
              ((S \ neighborsIn G u S).card : ℝ) ≤ 4 * ρ * S.card)) := by
  classical
  obtain ⟨W, S, hWU, hWcard, hSU, hScard, hside⟩ :=
    failure_produces_oneSided_block hfail hqpow
  have hhalf : (2 : ℝ) * S.card ≤ W.card := by
    rw [hScard]
    exact hqW.trans hWcard
  rcases hside with hlo | hhi
  · have hsmall : ∀ v ∈ S,
        ((relNeighbors G.Adj v W).card : ℝ) ≤ ρ * W.card := by
      simpa using hlo
    obtain ⟨U', hU'WS, hU'card, hU'small⟩ :=
      oneSided_block_retains_quarter G.Adj G.adj_comm hρ
        (by simpa [hScard] using hqpos) hsmall hhalf
    refine ⟨U', S, (hU'WS.trans Finset.sdiff_subset).trans hWU, hSU,
      ?_, hScard, ?_, Or.inl ?_⟩
    · rw [Finset.disjoint_left]
      intro v hvU hvS
      exact (Finset.mem_sdiff.mp (hU'WS hvU)).2 hvS
    · exact (div_le_div_of_nonneg_right hWcard (by norm_num)).trans hU'card
    · simpa using hU'small
  · have hsmall : ∀ v ∈ S,
        ((relNeighbors (fun x y ↦ ¬ G.Adj x y) v W).card : ℝ) ≤ ρ * W.card := by
      simpa using hhi
    have hsymm : ∀ v w, (¬ G.Adj v w) ↔ ¬ G.Adj w v := by
      intro v w
      rw [G.adj_comm]
    obtain ⟨U', hU'WS, hU'card, hU'small⟩ :=
      oneSided_block_retains_quarter (fun x y ↦ ¬ G.Adj x y) hsymm hρ
        (by simpa [hScard] using hqpos) hsmall hhalf
    refine ⟨U', S, (hU'WS.trans Finset.sdiff_subset).trans hWU, hSU,
      ?_, hScard, ?_, Or.inr ?_⟩
    · rw [Finset.disjoint_left]
      intro v hvU hvS
      exact (Finset.mem_sdiff.mp (hU'WS hvU)).2 hvS
    · exact (div_le_div_of_nonneg_right hWcard (by norm_num)).trans hU'card
    · simpa using hU'small

/-- The two colours used in the nested construction record whether a block
is sparse towards the next residual set in `G` or in its complement. -/
def blockDegree (G : SimpleGraph V) (inGraph : Bool) (u : V)
    (S : Finset V) : ℕ :=
  if inGraph then (neighborsIn G u S).card else (S \ neighborsIn G u S).card

/-- A single, data-carrying step of the KSSS nested construction. -/
structure NestedRichnessStep (G : SimpleGraph V) (δ ρ : ℝ) (q : ℕ)
    (U U' : Finset V) (S : Finset V) (inGraph : Bool) : Prop where
  residual_subset : U' ⊆ U
  block_subset : S ⊆ U
  disjoint : Disjoint U' S
  block_card : S.card = q
  residual_card : δ * U.card / 4 ≤ U'.card
  sparse : ∀ u ∈ U',
    (blockDegree G inGraph u S : ℝ) ≤ 4 * ρ * S.card

/-- A finite chain of nested residual sets and equally sized sparse blocks.
This is data (rather than merely a proposition), so later lemmas can fold its
blocks into the sparse induced subgraph used for the density contradiction. -/
inductive NestedRichnessChain (G : SimpleGraph V) (δ ρ : ℝ) (q : ℕ) :
    (K : ℕ) → Finset V → Type u
  | nil (U : Finset V) : NestedRichnessChain G δ ρ q 0 U
  | cons {K : ℕ} {U U' S : Finset V} {inGraph : Bool}
      (step : NestedRichnessStep G δ ρ q U U' S inGraph)
      (tail : NestedRichnessChain G δ ρ q K U') :
        NestedRichnessChain G δ ρ q (K + 1) U

/-- The blocks in a nested chain, in construction order. -/
def NestedRichnessChain.blocks {G : SimpleGraph V} {δ ρ : ℝ} {q K : ℕ}
    {U : Finset V} : NestedRichnessChain G δ ρ q K U →
      List (Bool × Finset V)
  | .nil _ => []
  | .cons (inGraph := inGraph) (S := S) _ tail =>
      (inGraph, S) :: tail.blocks

/-- Number of blocks of one colour in a nested chain. -/
def NestedRichnessChain.colorCount {G : SimpleGraph V} {δ ρ : ℝ} {q K : ℕ}
    {U : Finset V} (chain : NestedRichnessChain G δ ρ q K U)
    (inGraph : Bool) : ℕ :=
  (chain.blocks.filter fun p ↦ p.1 = inGraph).length

/-- Union of all blocks of one colour in a nested chain. -/
def NestedRichnessChain.colorUnion {G : SimpleGraph V} {δ ρ : ℝ} {q K : ℕ}
    {U : Finset V} : NestedRichnessChain G δ ρ q K U → Bool → Finset V
  | .nil _, _ => ∅
  | .cons (inGraph := direction) (S := S) _ tail, inGraph =>
      if direction = inGraph then S ∪ tail.colorUnion inGraph
      else tail.colorUnion inGraph

@[simp] lemma NestedRichnessChain.blocks_length {G : SimpleGraph V}
    {δ ρ : ℝ} {q K : ℕ} {U : Finset V}
    (chain : NestedRichnessChain G δ ρ q K U) :
    chain.blocks.length = K := by
  induction chain with
  | nil => simp [NestedRichnessChain.blocks]
  | cons step tail ih => simp [NestedRichnessChain.blocks, ih]

@[simp] lemma NestedRichnessChain.colorCount_true_add_false
    {G : SimpleGraph V} {δ ρ : ℝ} {q K : ℕ} {U : Finset V}
    (chain : NestedRichnessChain G δ ρ q K U) :
    chain.colorCount true + chain.colorCount false = K := by
  induction chain with
  | nil => simp [NestedRichnessChain.colorCount, NestedRichnessChain.blocks]
  | @cons K U U' S direction step tail ih =>
      cases direction <;>
        simpa [NestedRichnessChain.colorCount, NestedRichnessChain.blocks,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using congrArg Nat.succ ih

lemma NestedRichnessChain.colorUnion_subset
    {G : SimpleGraph V} {δ ρ : ℝ} {q K : ℕ} {U : Finset V}
    (chain : NestedRichnessChain G δ ρ q K U) (inGraph : Bool) :
    chain.colorUnion inGraph ⊆ U := by
  induction chain with
  | nil => simp [NestedRichnessChain.colorUnion]
  | @cons K U U' S direction step tail ih =>
      simp only [NestedRichnessChain.colorUnion]
      split_ifs
      · exact Finset.union_subset step.block_subset (ih.trans step.residual_subset)
      · exact ih.trans step.residual_subset

@[simp] lemma NestedRichnessChain.card_colorUnion
    {G : SimpleGraph V} {δ ρ : ℝ} {q K : ℕ} {U : Finset V}
    (chain : NestedRichnessChain G δ ρ q K U) (inGraph : Bool) :
    (chain.colorUnion inGraph).card = chain.colorCount inGraph * q := by
  induction chain with
  | nil => simp [NestedRichnessChain.colorUnion, NestedRichnessChain.colorCount,
      NestedRichnessChain.blocks]
  | @cons K U U' S direction step tail ih =>
      have htail : tail.colorUnion inGraph ⊆ U' := tail.colorUnion_subset inGraph
      have hdisj : Disjoint S (tail.colorUnion inGraph) := by
        exact step.disjoint.symm.mono_right htail
      by_cases hdir : direction = inGraph
      · simp [NestedRichnessChain.colorUnion, NestedRichnessChain.colorCount,
          NestedRichnessChain.blocks, hdir, Finset.card_union_of_disjoint hdisj,
          step.block_card, ih, Nat.add_mul, Nat.add_comm]
      · simp [NestedRichnessChain.colorUnion, NestedRichnessChain.colorCount,
          NestedRichnessChain.blocks, hdir, ih]

/-- The symmetric relation encoded by a block colour.  In the complement
colour this includes diagonal pairs; this only enlarges the ordered mass and
is therefore convenient for the upper bound. -/
def colorRelation (G : SimpleGraph V) (inGraph : Bool) : V → V → Prop :=
  if inGraph then G.Adj else fun v w ↦ ¬ G.Adj v w

lemma colorRelation_symm (G : SimpleGraph V) (inGraph : Bool) :
    ∀ v w, colorRelation G inGraph v w ↔ colorRelation G inGraph w v := by
  intro v w
  cases inGraph <;> simp [colorRelation, G.adj_comm]

@[simp] lemma card_relNeighbors_colorRelation (G : SimpleGraph V)
    (inGraph : Bool) (u : V) (S : Finset V) :
    (relNeighbors (colorRelation G inGraph) u S).card =
      blockDegree G inGraph u S := by
  cases inGraph <;> simp [colorRelation, blockDegree]

/-- Ordered relation mass inside a finite set. -/
def relationMass (r : V → V → Prop) (A : Finset V) : ℝ :=
  ∑ u ∈ A, ((relNeighbors r u A).card : ℝ)

lemma relNeighbors_union (r : V → V → Prop) (u : V) (S T : Finset V) :
    relNeighbors r u (S ∪ T) = relNeighbors r u S ∪ relNeighbors r u T := by
  ext v
  simp only [mem_relNeighbors, Finset.mem_union]
  aesop

lemma disjoint_relNeighbors (r : V → V → Prop) (u : V) {S T : Finset V}
    (hST : Disjoint S T) :
    Disjoint (relNeighbors r u S) (relNeighbors r u T) := by
  exact hST.mono (by intro v hv; exact (mem_relNeighbors.mp hv).1)
    (by intro v hv; exact (mem_relNeighbors.mp hv).1)

/-- Split ordered relation mass across a disjoint union. -/
lemma relationMass_union (r : V → V → Prop)
    (hsymm : ∀ v w, r v w ↔ r w v) {S T : Finset V}
    (hST : Disjoint S T) :
    relationMass r (S ∪ T) =
      relationMass r S + relationMass r T +
        2 * ∑ u ∈ T, ((relNeighbors r u S).card : ℝ) := by
  classical
  have hcrossNat := sum_card_relNeighbors_comm r hsymm S T
  have hcross :
      ∑ u ∈ S, ((relNeighbors r u T).card : ℝ) =
        ∑ u ∈ T, ((relNeighbors r u S).card : ℝ) := by
    exact_mod_cast hcrossNat
  simp_rw [relationMass, Finset.sum_union hST, relNeighbors_union,
    Finset.card_union_of_disjoint (disjoint_relNeighbors r _ hST), Nat.cast_add,
    Finset.sum_add_distrib]
  rw [hcross]
  ring

lemma relationMass_le_card_sq (r : V → V → Prop) (S : Finset V) :
    relationMass r S ≤ (S.card : ℝ) ^ 2 := by
  unfold relationMass
  calc
    ∑ u ∈ S, ((relNeighbors r u S).card : ℝ) ≤
        ∑ _u ∈ S, (S.card : ℝ) := by
      apply Finset.sum_le_sum
      intro u _hu
      exact_mod_cast Finset.card_le_card (show relNeighbors r u S ⊆ S by
        intro v hv
        exact (mem_relNeighbors.mp hv).1)
    _ = (S.card : ℝ) ^ 2 := by simp [pow_two]

/-- The union of all blocks of one colour has small ordered relation mass.
The term `4ρ c²` accounts for cross-block pairs and `c` for the uncontrolled
mass internal to each of the `c` blocks. -/
lemma NestedRichnessChain.relationMass_colorUnion_le
    {G : SimpleGraph V} {δ ρ : ℝ} {q K : ℕ} {U : Finset V}
    (chain : NestedRichnessChain G δ ρ q K U) (inGraph : Bool)
    (hρ : 0 ≤ ρ) :
    relationMass (colorRelation G inGraph) (chain.colorUnion inGraph) ≤
      (4 * ρ * (chain.colorCount inGraph : ℝ) ^ 2 +
          chain.colorCount inGraph) * (q : ℝ) ^ 2 := by
  induction chain with
  | nil => simp [NestedRichnessChain.colorUnion, NestedRichnessChain.colorCount,
      NestedRichnessChain.blocks, relationMass]
  | @cons K U U' S direction step tail ih =>
      by_cases hdir : direction = inGraph
      · subst direction
        let T := tail.colorUnion inGraph
        let c := tail.colorCount inGraph
        have hTU' : T ⊆ U' := tail.colorUnion_subset inGraph
        have hST : Disjoint S T := step.disjoint.symm.mono_right hTU'
        have hcross :
            ∑ u ∈ T,
                ((relNeighbors (colorRelation G inGraph) u S).card : ℝ) ≤
              (T.card : ℝ) * (4 * ρ * S.card) := by
          calc
            ∑ u ∈ T,
                ((relNeighbors (colorRelation G inGraph) u S).card : ℝ) ≤
                ∑ _u ∈ T, 4 * ρ * S.card := by
              apply Finset.sum_le_sum
              intro u hu
              simpa using step.sparse u (hTU' hu)
            _ = (T.card : ℝ) * (4 * ρ * S.card) := by
              simp [mul_assoc, mul_comm, mul_left_comm]
        have hTcard : (T.card : ℝ) = (c : ℝ) * q := by
          exact_mod_cast tail.card_colorUnion inGraph
        have hScard : (S.card : ℝ) = q := by exact_mod_cast step.block_card
        have hinternal := relationMass_le_card_sq (colorRelation G inGraph) S
        have htail := ih
        have hUnion :
            (NestedRichnessChain.cons step tail).colorUnion inGraph = S ∪ T := by
          simp [NestedRichnessChain.colorUnion, T]
        have hCount :
            (NestedRichnessChain.cons step tail).colorCount inGraph =
              tail.colorCount inGraph + 1 := by
          simp [NestedRichnessChain.colorCount, NestedRichnessChain.blocks]
        rw [hUnion, relationMass_union (colorRelation G inGraph)
          (colorRelation_symm G inGraph) hST, hCount]
        dsimp [T, c] at hcross hTcard htail
        rw [hTcard, hScard] at hcross
        rw [hScard] at hinternal
        have hz : (0 : ℝ) ≤ tail.colorCount inGraph := Nat.cast_nonneg _
        have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
        calc
          relationMass (colorRelation G inGraph) S +
                relationMass (colorRelation G inGraph) (tail.colorUnion inGraph) +
              2 * ∑ u ∈ tail.colorUnion inGraph,
                ((relNeighbors (colorRelation G inGraph) u S).card : ℝ) ≤
              (q : ℝ) ^ 2 +
                  (4 * ρ * (tail.colorCount inGraph : ℝ) ^ 2 +
                    tail.colorCount inGraph) * (q : ℝ) ^ 2 +
                2 * (((tail.colorCount inGraph : ℝ) * q) * (4 * ρ * q)) := by
            gcongr
          _ ≤ (4 * ρ * ((tail.colorCount inGraph : ℝ) + 1) ^ 2 +
                ((tail.colorCount inGraph : ℝ) + 1)) * (q : ℝ) ^ 2 := by
            ring_nf
            nlinarith [mul_nonneg hρ (sq_nonneg (q : ℝ))]
          _ = (4 * ρ * ((tail.colorCount inGraph + 1 : ℕ) : ℝ) ^ 2 +
                ((tail.colorCount inGraph + 1 : ℕ) : ℝ)) * (q : ℝ) ^ 2 := by
            simp only [Nat.cast_add, Nat.cast_one]
      · have hUnion :
            (NestedRichnessChain.cons step tail).colorUnion inGraph =
              tail.colorUnion inGraph := by
          simp [NestedRichnessChain.colorUnion, hdir]
        have hCount :
            (NestedRichnessChain.cons step tail).colorCount inGraph =
              tail.colorCount inGraph := by
          simp [NestedRichnessChain.colorCount, NestedRichnessChain.blocks, hdir]
        rw [hUnion, hCount]
        exact ih

/-- One of the two colours occurs on at least half of the steps. -/
lemma NestedRichnessChain.exists_majority_color
    {G : SimpleGraph V} {δ ρ : ℝ} {q K : ℕ} {U : Finset V}
    (chain : NestedRichnessChain G δ ρ q K U) :
    ∃ inGraph : Bool, K ≤ 2 * chain.colorCount inGraph := by
  have hsum := chain.colorCount_true_add_false
  by_cases hle : chain.colorCount false ≤ chain.colorCount true
  · exact ⟨true, by omega⟩
  · exact ⟨false, by omega⟩

/-- Divide the ordered-mass estimate by the exact square of the union size.
This is the `4ρ + 1/c` density bound in the KSSS proof. -/
lemma NestedRichnessChain.relationMass_colorUnion_density
    {G : SimpleGraph V} {δ ρ : ℝ} {q K : ℕ} {U : Finset V}
    (chain : NestedRichnessChain G δ ρ q K U) (inGraph : Bool)
    (hρ : 0 ≤ ρ) (hc : 0 < chain.colorCount inGraph) :
    relationMass (colorRelation G inGraph) (chain.colorUnion inGraph) ≤
      (4 * ρ + (chain.colorCount inGraph : ℝ)⁻¹) *
        (chain.colorUnion inGraph).card ^ 2 := by
  have hmain := chain.relationMass_colorUnion_le inGraph hρ
  rw [chain.card_colorUnion inGraph]
  have hcreal : (0 : ℝ) < chain.colorCount inGraph := by exact_mod_cast hc
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  push_cast
  field_simp
  nlinarith [sq_nonneg (q : ℝ)]

/-- The graph selected by a block colour. -/
def colorGraph (G : SimpleGraph V) (inGraph : Bool) : SimpleGraph V :=
  if inGraph then G else Gᶜ

/-- The actual degree in the selected graph is bounded by `blockDegree`.
For the complement colour `blockDegree` also counts the diagonal, hence the
inequality rather than equality. -/
lemma degree_induce_colorGraph_le_blockDegree (G : SimpleGraph V)
    (inGraph : Bool) (A : Finset V) (v : A) :
    FiniteES.vertexDegree ((colorGraph G inGraph).induce (A : Set V)) v ≤
      blockDegree G inGraph v.1 A := by
  classical
  let H := (colorGraph G inGraph).induce (A : Set V)
  let f : H.neighborSet v →
      {w // w ∈ relNeighbors (colorRelation G inGraph) v.1 A} := fun w ↦
    ⟨w.1.1, by
      have hadj := w.2
      change (colorGraph G inGraph).Adj v.1 w.1.1 at hadj
      cases inGraph
      · simp only [colorGraph, Bool.false_eq_true, ↓reduceIte,
          SimpleGraph.compl_adj] at hadj
        exact mem_relNeighbors.mpr ⟨w.1.2, hadj.2⟩
      · exact mem_relNeighbors.mpr
          ⟨w.1.2, by simpa [colorRelation, colorGraph] using hadj⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hv : x.1.1 = y.1.1 := congrArg (fun z ↦ (z.1 : V)) hxy
    exact Subtype.ext (Subtype.ext hv)
  have hcard := Nat.card_le_card_of_injective f hf
  calc
    FiniteES.vertexDegree H v = Nat.card (H.neighborSet v) := rfl
    _ ≤ Nat.card {w // w ∈ relNeighbors (colorRelation G inGraph) v.1 A} := hcard
    _ = (relNeighbors (colorRelation G inGraph) v.1 A).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = blockDegree G inGraph v.1 A := card_relNeighbors_colorRelation _ _ _ _

/-- Convert the ordered relation-mass bound into an upper bound for the
ordinary unordered edge count of the selected induced graph. -/
lemma edgeCount_induce_colorGraph_le_relationMass (G : SimpleGraph V)
    (inGraph : Bool) (A : Finset V) :
    (FiniteES.edgeCount ((colorGraph G inGraph).induce (A : Set V)) : ℝ) ≤
      relationMass (colorRelation G inGraph) A := by
  classical
  let H := (colorGraph G inGraph).induce (A : Set V)
  letI : DecidableRel H.Adj := Classical.decRel _
  have hdegNat :
      ∑ v : A, FiniteES.vertexDegree H v ≤
        ∑ u ∈ A, blockDegree G inGraph u A := by
    rw [← A.sum_attach]
    simp only [Finset.attach_eq_univ]
    apply Finset.sum_le_sum
    intro v _hv
    exact degree_induce_colorGraph_le_blockDegree G inGraph A v
  have hedgesNat :
      FiniteES.edgeCount H ≤ ∑ u ∈ A, blockDegree G inGraph u A := by
    have hsum := H.sum_degrees_eq_twice_card_edges
    have hedgeDegree : H.edgeFinset.card ≤
        ∑ v : A, FiniteES.vertexDegree H v := by
      simp_rw [FiniteES.vertexDegree_eq_degree]
      calc
        H.edgeFinset.card ≤ 2 * H.edgeFinset.card := by omega
        _ = ∑ v : A, H.degree v := hsum.symm
    change H.edgeFinset.card ≤ ∑ u ∈ A, blockDegree G inGraph u A
    exact hedgeDegree.trans hdegNat
  change (FiniteES.edgeCount H : ℝ) ≤
    ∑ u ∈ A, ((relNeighbors (colorRelation G inGraph) u A).card : ℝ)
  simp_rw [card_relNeighbors_colorRelation]
  exact_mod_cast hedgesNat

/-- Positive powers of natural numbers eventually dominate every fixed real
constant.  This packages the only asymptotic input needed when the selected
block union is shown to have order at least `n^(α/2)`. -/
lemma exists_nat_rpow_ge (p B : ℝ) (hp : 0 < p) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → B ≤ (n : ℝ) ^ p := by
  have ht : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) ^ p) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in Filter.atTop, B ≤ (n : ℝ) ^ p :=
    ht.eventually (Filter.eventually_ge_atTop B)
  exact Filter.eventually_atTop.mp hev

/-- Rounding bounds for the common block size used in the KSSS iteration. -/
lemma natFloor_quarter_bounds {x : ℝ} (hx : 8 ≤ x) :
    let q := ⌊x / 4⌋₊
    0 < q ∧ (2 : ℝ) * q ≤ x ∧ x / 8 ≤ q := by
  let q := ⌊x / 4⌋₊
  have hxnonneg : 0 ≤ x / 4 := by positivity
  have hqUpper : (q : ℝ) ≤ x / 4 := by
    exact Nat.floor_le hxnonneg
  have hqLower : x / 4 < (q : ℝ) + 1 := by
    exact Nat.lt_floor_add_one (x / 4)
  have hqpos : 0 < q := by
    have hone : (1 : ℕ) ≤ q := by
      apply Nat.le_floor
      norm_num
      linarith
    omega
  refine ⟨hqpos, ?_, ?_⟩ <;> linarith

/-- Simultaneous fixed-constant choices in the proof of KSSS Lemma 4.4. -/
lemma exists_richness_iteration_parameters {a α : ℝ}
    (ha : 0 < a) (hα : 0 < α) (hαone : α < 1) :
    ∃ (K : ℕ) (ρ : ℝ),
      16 ≤ K ∧ 0 < ρ ∧ ρ < 1 ∧
        4 * ρ + 2 / K < a ∧
        ρ * K ≤ 1 / 3 ∧
        ρ ≤ ((4 : ℝ) ^ (-(K : ℝ))) ^ (3 / 2 : ℝ) ∧ ρ ≤ 1 - α := by
  obtain ⟨K, hK⟩ := exists_nat_gt (max 16 (4 / a))
  have hK16 : 16 ≤ K := by
    exact_mod_cast (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hK))
  have hKpos : (0 : ℝ) < K := by positivity
  let ρ : ℝ := min (1 / 2) <|
      min (a / 16) <|
      min ((1 - α) / 2) <|
        min (1 / (3 * (K : ℝ)))
          (((4 : ℝ) ^ (-(K : ℝ))) ^ (3 / 2 : ℝ))
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    repeat' apply lt_min <;> positivity
  have hρhalf : ρ ≤ 1 / 2 := by exact min_le_left _ _
  have hρa : ρ ≤ a / 16 := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hρα : ρ ≤ (1 - α) / 2 := by
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have hρK : ρ ≤ 1 / (3 * (K : ℝ)) := by
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have hρpow : ρ ≤ ((4 : ℝ) ^ (-(K : ℝ))) ^ (3 / 2 : ℝ) := by
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
  have hKlarge : 4 / a < (K : ℝ) :=
    (lt_of_le_of_lt (le_max_right _ _) hK)
  have htwoK : 2 / (K : ℝ) < a / 2 := by
    apply (div_lt_iff₀ hKpos).2
    have ha2 : 0 < a / 2 := by positivity
    apply (div_lt_iff₀ ha).mp at hKlarge
    nlinarith
  refine ⟨K, ρ, hK16, hρpos, by linarith, ?_, ?_, hρpow, by linarith⟩
  · nlinarith
  · have := mul_le_mul_of_nonneg_right hρK hKpos.le
    field_simp at this ⊢
    nlinarith

/-- Uniform numerical budget for all `K` nested steps. -/
lemma richness_iteration_budget {n : ℕ} {m ρ : ℝ} {K : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) (hmρ : m ≤ ρ * n)
    (hρ : 0 < ρ) (hρK : ρ * K ≤ 1 / 3)
    (hρsmall :
      ρ ≤ ((4 : ℝ) ^ (-(K : ℝ))) ^ (3 / 2 : ℝ)) :
    m ≤ (((m / n) ^ ρ) / 4) ^ K * n := by
  let x : ℝ := m / n
  let B : ℝ := (4 : ℝ) ^ (-(K : ℝ))
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : 0 < x := div_pos hm hnreal
  have hxone : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one hnreal).2 hmn
  have hB : 0 < B := Real.rpow_pos_of_pos (by norm_num) _
  have hxrho : x ≤ ρ := by
    dsimp [x]
    apply (div_le_iff₀ hnreal).2
    simpa [mul_comm] using hmρ
  have hxsmall : x ≤ B ^ (3 / 2 : ℝ) := hxrho.trans hρsmall
  have hxpow : x ^ (2 / 3 : ℝ) ≤ B := by
    have hmono := Real.rpow_le_rpow hx.le hxsmall (by norm_num : (0 : ℝ) ≤ 2 / 3)
    calc
      x ^ (2 / 3 : ℝ) ≤ (B ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := hmono
      _ = B := by
        rw [← Real.rpow_mul hB.le]
        norm_num
  have hexponent : x ^ (1 / 3 : ℝ) ≤ x ^ (ρ * K) :=
    (Real.antitone_rpow_of_base_le_one hx hxone) hρK
  have hxFactor : x ≤ B * x ^ (ρ * K) := by
    calc
      x = x ^ (1 / 3 : ℝ) * x ^ (2 / 3 : ℝ) := by
        rw [← Real.rpow_add hx]
        norm_num
      _ ≤ x ^ (1 / 3 : ℝ) * B :=
        mul_le_mul_of_nonneg_left hxpow (Real.rpow_nonneg hx.le _)
      _ ≤ x ^ (ρ * K) * B :=
        mul_le_mul_of_nonneg_right hexponent hB.le
      _ = B * x ^ (ρ * K) := by ring
  have hBpow : B = ((4 : ℝ) ^ K)⁻¹ := by
    dsimp [B]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), Real.rpow_natCast]
  have hfactorEq :
      (((m / n) ^ ρ) / 4) ^ K = B * x ^ (ρ * K) := by
    dsimp [x]
    rw [div_pow, ← Real.rpow_mul_natCast (div_nonneg hm.le hnreal.le)]
    rw [hBpow]
    field_simp
  have hratio : m = x * n := by
    dsimp [x]
    field_simp
  rw [hfactorEq, hratio]
  exact mul_le_mul_of_nonneg_right hxFactor (Nat.cast_nonneg _)

/-- The witness-set scale `δm` is still polynomially large. -/
lemma rpow_half_le_ratio_rpow_mul {n : ℕ} {m ρ α : ℝ}
    (hn : 1 ≤ n) (hsqrt : Real.sqrt n ≤ m)
    (hρ : 0 ≤ ρ) (hα : 0 ≤ α) (hρα : ρ ≤ 1 - α) :
    (n : ℝ) ^ (α / 2) ≤ (m / n) ^ ρ * m := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnreal
  have hsqrtone : (1 : ℝ) ≤ Real.sqrt n := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hnreal
  have hmone : (1 : ℝ) ≤ m := hsqrtone.trans hsqrt
  have hmpos : 0 < m := zero_lt_one.trans_le hmone
  have hnle : (n : ℝ) ≤ m ^ 2 := by
    calc
      (n : ℝ) = (Real.sqrt n) ^ 2 := by
        exact (Real.sq_sqrt (Nat.cast_nonneg n)).symm
      _ ≤ m ^ 2 := by nlinarith [Real.sqrt_nonneg (n : ℝ)]
  have hinv : 1 / m ≤ m / n := by
    apply (div_le_div_iff₀ hmpos hnpos).2
    simpa [pow_two] using hnle
  have hratioPow : (1 / m) ^ ρ ≤ (m / n) ^ ρ :=
    Real.rpow_le_rpow (by positivity) hinv hρ
  have halpha : α ≤ 1 - ρ := by linarith
  have hmexp : m ^ α ≤ m ^ (1 - ρ) :=
    Real.rpow_le_rpow_of_exponent_le hmone halpha
  have hsqrtPow : (Real.sqrt n) ^ α ≤ m ^ α :=
    Real.rpow_le_rpow (Real.sqrt_nonneg _) hsqrt hα
  have hleft : (n : ℝ) ^ (α / 2) = (Real.sqrt n) ^ α :=
    Real.rpow_div_two_eq_sqrt α (by positivity)
  have hright : (1 / m) ^ ρ * m = m ^ (1 - ρ) := by
    rw [Real.div_rpow zero_le_one hmpos.le, Real.one_rpow, Real.rpow_sub hmpos]
    field_simp
    exact (Real.rpow_one m).symm
  rw [hleft]
  calc
    (Real.sqrt n) ^ α ≤ m ^ α := hsqrtPow
    _ ≤ m ^ (1 - ρ) := hmexp
    _ = (1 / m) ^ ρ * m := hright.symm
    _ ≤ (m / n) ^ ρ * m :=
      mul_le_mul_of_nonneg_right hratioPow hmpos.le

/-- Ramsey-freeness passes to a sufficiently large induced subgraph, after
relabeling its finite vertex type by `Fin`. -/
lemma ramseyFree_induce_overFin {n : ℕ} (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) {C D : ℝ} (hG : RamseyFree C G)
    (hthreshold : C * Real.logb 2 n ≤ D * Real.logb 2 A.card) :
    RamseyFree D
      ((G.induce (A : Set (Fin n))).overFin (card_subtype_coe_finset A)) := by
  classical
  let H := G.induce (A : Set (Fin n))
  let e : H ≃g H.overFin (card_subtype_coe_finset A) :=
    H.overFinIso (card_subtype_coe_finset A)
  intro T hT
  let TI : Finset A := T.map e.symm.toEquiv.toEmbedding
  let S : Finset (Fin n) := TI.image Subtype.val
  have hcardTI : TI.card = T.card := by
    simp [TI]
  have hcardS : S.card = T.card := by
    rw [show S.card = TI.card by
      simp [S, Finset.card_image_iff.mpr Subtype.val_injective.injOn], hcardTI]
  have hhomTI : H.IsClique (TI : Set A) ∨ H.IsIndepSet (TI : Set A) := by
    rcases hT with hclique | hindep
    · left
      intro x hx y hy hxy
      simp only [TI, Finset.coe_map, Set.mem_image] at hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact e.symm.map_rel_iff.mp
        (hclique hx' hy' (fun h ↦ hxy (congrArg e.symm h)))
    · right
      intro x hx y hy hxy hadj
      simp only [TI, Finset.coe_map, Set.mem_image] at hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact hindep hx' hy' (fun h ↦ hxy (congrArg e.symm h))
        (e.symm.map_rel_iff.mpr hadj)
  have hhomS : G.IsClique (S : Set (Fin n)) ∨ G.IsIndepSet (S : Set (Fin n)) := by
    have hset : (S : Set (Fin n)) = Subtype.val '' (TI : Set A) := by
      ext x
      simp [S, TI]
    rcases hhomTI with hclique | hindep
    · left
      have himage := (isClique_induce_iff G).mp hclique
      rw [hset]
      exact himage
    · right
      have himage := (isIndepSet_induce_iff G).mp hindep
      rw [hset]
      exact himage
  have hsmall := hG S hhomS
  rw [hcardS] at hsmall
  exact hsmall.trans_le hthreshold

lemma ramseyFree_colorGraph {n : ℕ} {C : ℝ} (G : SimpleGraph (Fin n))
    (inGraph : Bool) (hG : RamseyFree C G) :
    RamseyFree C (colorGraph G inGraph) := by
  cases inGraph
  · simpa [colorGraph] using (ramseyFree_compl G).2 hG
  · simpa [colorGraph] using hG

lemma edgeCount_overFin {W : Type u} [Fintype W]
    (G : SimpleGraph W) {n : ℕ} (hc : Fintype.card W = n) :
    FiniteES.edgeCount (G.overFin hc) = FiniteES.edgeCount G := by
  classical
  unfold FiniteES.edgeCount
  exact (G.overFinIso hc).card_edgeFinset_eq.symm

/-- The exact finite density contradiction obtained from a majority-colour
block union.  All asymptotic parameter choices have been isolated into the
four displayed scalar hypotheses. -/
lemma nestedRichnessChain_density_contradiction {n : ℕ}
    {G : SimpleGraph (Fin n)} {δ ρ : ℝ} {q K : ℕ}
    (chain : NestedRichnessChain G δ ρ q K Finset.univ)
    (inGraph : Bool) {C D a : ℝ} {N : ℕ}
    (hG : RamseyFree C G) (hρ : 0 ≤ ρ)
    (hc : 0 < chain.colorCount inGraph) (hA : 0 < (chain.colorUnion inGraph).card)
    (hN : N ≤ (chain.colorUnion inGraph).card)
    (hthreshold : C * Real.logb 2 n ≤
      D * Real.logb 2 (chain.colorUnion inGraph).card)
    (hgap : 4 * ρ + (chain.colorCount inGraph : ℝ)⁻¹ < a)
    (hdensity : ∀ s : ℕ, N ≤ s → ∀ H : SimpleGraph (Fin s),
      RamseyFree D H → a * (s : ℝ) ^ 2 ≤ (FiniteES.edgeCount H : ℝ)) : False := by
  let A := chain.colorUnion inGraph
  let H := (colorGraph G inGraph).induce (A : Set (Fin n))
  let HF := H.overFin (card_subtype_coe_finset A)
  have hcolor : RamseyFree C (colorGraph G inGraph) :=
    ramseyFree_colorGraph G inGraph hG
  have hramsey : RamseyFree D HF := by
    exact ramseyFree_induce_overFin (colorGraph G inGraph) A hcolor hthreshold
  have hlower := hdensity A.card hN HF hramsey
  have hcount : FiniteES.edgeCount HF = FiniteES.edgeCount H :=
    edgeCount_overFin H (card_subtype_coe_finset A)
  rw [hcount] at hlower
  have hmass := chain.relationMass_colorUnion_density inGraph hρ hc
  have hedge := edgeCount_induce_colorGraph_le_relationMass G inGraph A
  have hupper :
      (FiniteES.edgeCount H : ℝ) ≤
        (4 * ρ + (chain.colorCount inGraph : ℝ)⁻¹) * (A.card : ℝ) ^ 2 :=
    hedge.trans hmass
  exact richness_density_contradiction_endpoint hA hgap hlower hupper

/-- Iterate the failed-richness step a prescribed finite number of times.
The single budget inequality says that even the final residual set still has
at least `m` vertices. -/
lemma exists_nestedRichnessChain {G : SimpleGraph V} {U₀ : Finset V}
    {δ ρ α m : ℝ} {q K : ℕ}
    (hρ : 0 < ρ) (hα : 0 < α) (hm : 0 ≤ m)
    (hδ : 0 ≤ δ) (hδ4 : δ / 4 ≤ 1) (hqpos : 0 < q)
    (hqpow : (2 : ℝ) * q ≤ m ^ α)
    (hqW : (2 : ℝ) * q ≤ δ * m)
    (hbudget : m ≤ (δ / 4) ^ K * U₀.card)
    (hnoRich : ∀ U : Finset V, U ⊆ U₀ → m ≤ U.card →
      ¬ RichOn G U δ ρ α) :
    Nonempty (NestedRichnessChain G δ ρ q K U₀) := by
  have hfac : 0 ≤ δ / 4 := div_nonneg hδ (by norm_num)
  induction K generalizing U₀ with
  | zero => exact ⟨.nil U₀⟩
  | succ K ih =>
      have hpow_le_one : (δ / 4) ^ (K + 1) ≤ 1 :=
        pow_le_one₀ hfac hδ4
      have hUlarge : m ≤ (U₀.card : ℝ) := by
        refine hbudget.trans ?_
        have hcardnonneg : (0 : ℝ) ≤ U₀.card := Nat.cast_nonneg _
        nlinarith
      have hpowU : m ^ α ≤ (U₀.card : ℝ) ^ α :=
        Real.rpow_le_rpow hm hUlarge hα.le
      have hqpowU : (2 : ℝ) * q ≤ (U₀.card : ℝ) ^ α := hqpow.trans hpowU
      have hqWU : (2 : ℝ) * q ≤ δ * U₀.card := by
        exact hqW.trans (mul_le_mul_of_nonneg_left hUlarge hδ)
      have hfail := hnoRich U₀ Finset.Subset.rfl hUlarge
      obtain ⟨U', S, hU'sub, hSsub, hdisj, hScard, hU'card, hside⟩ :=
        failed_richness_nested_step hρ hqpos hfail hqpowU hqWU
      have hnextBudget : m ≤ (δ / 4) ^ K * U'.card := by
        have hstepCard : (δ / 4) * U₀.card ≤ (U'.card : ℝ) := by
          convert hU'card using 1 <;> ring
        have hmul := mul_le_mul_of_nonneg_left hstepCard (pow_nonneg hfac K)
        calc
          m ≤ (δ / 4) ^ (K + 1) * U₀.card := hbudget
          _ = (δ / 4) ^ K * ((δ / 4) * U₀.card) := by rw [pow_succ]; ring
          _ ≤ (δ / 4) ^ K * U'.card := hmul
      have hnoRich' : ∀ T : Finset V, T ⊆ U' → m ≤ T.card →
          ¬ RichOn G T δ ρ α := by
        intro T hTU' hTm
        exact hnoRich T (hTU'.trans hU'sub) hTm
      obtain ⟨tail⟩ := ih hnextBudget hnoRich'
      rcases hside with hsparse | hsparse
      · let step : NestedRichnessStep G δ ρ q U₀ U' S true :=
          { residual_subset := hU'sub
            block_subset := hSsub
            disjoint := hdisj
            block_card := hScard
            residual_card := hU'card
            sparse := by simpa [blockDegree] using hsparse }
        exact ⟨.cons step tail⟩
      · let step : NestedRichnessStep G δ ρ q U₀ U' S false :=
          { residual_subset := hU'sub
            block_subset := hSsub
            disjoint := hdisj
            block_card := hScard
            residual_card := hU'card
            sparse := by simpa [blockDegree] using hsparse }
        exact ⟨.cons step tail⟩

/-- Exact quantified statement of KSSS Lemma 4.4.  Keeping the statement as
a named proposition makes the scale and all dependencies available to the
later Fourier modules without concealing them in notation. -/
def KSSSLemma44 : Prop :=
  ∀ (C α : ℝ), 0 < C → 0 < α →
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℝ,
        Real.sqrt n ≤ m → m ≤ ρ * n →
          ∀ G : SimpleGraph (Fin n), RamseyFree C G →
            ∃ U : Finset (Fin n),
              m ≤ U.card ∧
                Rich (G.induce (U : Set (Fin n))) ((m / n) ^ ρ) ρ α

/-- The easy exponent range of KSSS Lemma 4.4. -/
lemma ksssLemma44_of_one_le_alpha (C α : ℝ) (hα : 1 ≤ α) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℝ,
        Real.sqrt n ≤ m → m ≤ ρ * n →
          ∀ G : SimpleGraph (Fin n), RamseyFree C G →
            ∃ U : Finset (Fin n),
              m ≤ U.card ∧
                Rich (G.induce (U : Set (Fin n))) ((m / n) ^ ρ) ρ α := by
  refine ⟨1 / 2, by norm_num, by norm_num, 1, ?_⟩
  intro n hn m _hmLower hmUpper G _hG
  have hnpos : 0 < n := by omega
  let v : Fin n := ⟨0, hnpos⟩
  haveI : Nonempty (↥(↑(Finset.univ : Finset (Fin n)) : Set (Fin n))) :=
    ⟨⟨v, by simp⟩⟩
  refine ⟨Finset.univ, ?_, ?_⟩
  · simp only [Finset.card_univ, Fintype.card_fin]
    have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  · exact rich_of_one_le_alpha
      (G.induce (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)))
      ((m / n) ^ (1 / 2)) (1 / 2) hα

/-- Kwan--Sah--Sauermann--Sawhney, Lemma 4.4. -/
theorem ksssLemma44 : KSSSLemma44 := by
  intro C α hC hα
  by_cases hαone : 1 ≤ α
  · exact ksssLemma44_of_one_le_alpha C α hαone
  have hαlt : α < 1 := lt_of_not_ge hαone
  let D : ℝ := 2 * C / α
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨a, ha, N₀, hdensity⟩ :=
    FiniteES.ramseyFree_edgeCount_density_lower D hD
  obtain ⟨K, ρ, hK, hρ, hρone, hgapK, hρK, hρsmall, hρα⟩ :=
    exists_richness_iteration_parameters ha hα hαlt
  obtain ⟨N₁, hN₁⟩ :=
    exists_nat_rpow_ge (α / 2) (max 8 N₀) (by positivity)
  let N := max 1 N₁
  refine ⟨ρ, hρ, hρone, N, ?_⟩
  intro n hn m hsqrt hmρ G hG
  have hn1 : 1 ≤ n := (le_max_left 1 N₁).trans (show N ≤ n from hn)
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.2 (by positivity)
  have hmpos : 0 < m := hsqrtpos.trans_le hsqrt
  have hmn : m ≤ n := by
    have := hmρ
    have hnnonneg : (0 : ℝ) ≤ n := hnreal.le
    nlinarith
  let δ : ℝ := (m / n) ^ ρ
  have hratioPos : 0 < m / n := div_pos hmpos hnreal
  have hratioOne : m / n ≤ 1 := (div_le_one hnreal).2 hmn
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδone : δ ≤ 1 := by
    dsimp [δ]
    exact Real.rpow_le_one hratioPos.le hratioOne hρ.le
  have hnPower : max 8 (N₀ : ℝ) ≤ (n : ℝ) ^ (α / 2) := by
    exact hN₁ n ((le_max_right 1 N₁).trans hn)
  have hscale₁ : (n : ℝ) ^ (α / 2) ≤ m ^ α := by
    rw [Real.rpow_div_two_eq_sqrt α (Nat.cast_nonneg _)]
    exact Real.rpow_le_rpow (Real.sqrt_nonneg _) hsqrt hα.le
  have hscale₂ : (n : ℝ) ^ (α / 2) ≤ δ * m := by
    simpa [δ] using rpow_half_le_ratio_rpow_mul hn1 hsqrt hρ.le hα.le hρα
  let blockScale : ℝ := min (m ^ α) (δ * m)
  have hblockScale : (n : ℝ) ^ (α / 2) ≤ blockScale :=
    le_min hscale₁ hscale₂
  have hblockEight : 8 ≤ blockScale :=
    (le_max_left 8 (N₀ : ℝ)).trans (hnPower.trans hblockScale)
  let q : ℕ := ⌊blockScale / 4⌋₊
  obtain ⟨hqpos, hqScale, hqLower⟩ := natFloor_quarter_bounds hblockEight
  have hqpow : (2 : ℝ) * q ≤ m ^ α :=
    hqScale.trans (min_le_left _ _)
  have hqW : (2 : ℝ) * q ≤ δ * m :=
    hqScale.trans (min_le_right _ _)
  have hbudget : m ≤ (δ / 4) ^ K * (Finset.univ : Finset (Fin n)).card := by
    simpa [δ] using richness_iteration_budget hnpos hmpos hmn hmρ hρ hρK hρsmall
  by_contra hnone
  push_neg at hnone
  have hnoRichOn : ∀ U : Finset (Fin n), U ⊆ Finset.univ → m ≤ U.card →
      ¬ RichOn G U δ ρ α := by
    intro U _hU hUm hrichOn
    exact hnone U hUm ((rich_induce_iff_richOn G U δ ρ α).2 hrichOn)
  obtain ⟨chain⟩ := exists_nestedRichnessChain
    hρ hα hmpos.le hδpos.le (by nlinarith) hqpos hqpow hqW hbudget hnoRichOn
  obtain ⟨direction, hmajority⟩ := chain.exists_majority_color
  let c := chain.colorCount direction
  let A := chain.colorUnion direction
  have hcpos : 0 < c := by
    have : 0 < K := by omega
    omega
  have hcEight : (8 : ℝ) ≤ c := by
    exact_mod_cast (show 8 ≤ c by omega)
  have hAcardNat : A.card = c * q := chain.card_colorUnion direction
  have hAcard : (A.card : ℝ) = (c : ℝ) * q := by
    exact_mod_cast hAcardNat
  have hAblock : blockScale ≤ A.card := by
    rw [hAcard]
    have hqLower' : blockScale / 8 ≤ (q : ℝ) := hqLower
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ c by positivity)
      (show (0 : ℝ) ≤ q by positivity)]
  have hApower : (n : ℝ) ^ (α / 2) ≤ A.card :=
    hblockScale.trans hAblock
  have hApos : 0 < A.card := by
    rw [hAcardNat]
    positivity
  have hAN₀ : N₀ ≤ A.card := by
    have : (N₀ : ℝ) ≤ (n : ℝ) ^ (α / 2) :=
      (le_max_right 8 (N₀ : ℝ)).trans hnPower
    exact_mod_cast this.trans hApower
  have hlog : C * Real.logb 2 n ≤ D * Real.logb 2 A.card := by
    have hpowpos : 0 < (n : ℝ) ^ (α / 2) := Real.rpow_pos_of_pos hnreal _
    have hlogmono :
        Real.logb 2 ((n : ℝ) ^ (α / 2)) ≤ Real.logb 2 A.card :=
      Real.logb_le_logb_of_le (by norm_num) hpowpos hApower
    rw [Real.logb_rpow_eq_mul_logb_of_pos hnreal] at hlogmono
    dsimp [D]
    have hlogn : 0 ≤ Real.logb 2 (n : ℝ) := by
      rw [Real.logb]
      positivity
    have hlogA : 0 ≤ Real.logb 2 (A.card : ℝ) := by
      rw [Real.logb]
      have : (1 : ℝ) ≤ A.card := by exact_mod_cast hApos
      positivity
    have hmult := mul_le_mul_of_nonneg_left hlogmono
      (show 0 ≤ 2 * C / α by positivity)
    calc
      C * Real.logb 2 n =
          (2 * C / α) * ((α / 2) * Real.logb 2 n) := by field_simp
      _ ≤ (2 * C / α) * Real.logb 2 A.card := hmult
  have hcinv : (c : ℝ)⁻¹ ≤ 2 / K := by
    have hKReal : (0 : ℝ) < K := by positivity
    have hhalf : (K : ℝ) / 2 ≤ c := by
      have hmajorityReal : (K : ℝ) ≤ 2 * c := by exact_mod_cast hmajority
      linarith
    calc
      (c : ℝ)⁻¹ = 1 / c := by rw [one_div]
      _ ≤ 1 / ((K : ℝ) / 2) :=
        one_div_le_one_div_of_le (by positivity) hhalf
      _ = 2 / K := by field_simp
  have hgap : 4 * ρ + (c : ℝ)⁻¹ < a := by
    have hle : 4 * ρ + (c : ℝ)⁻¹ ≤ 4 * ρ + 2 / K := by
      simpa [add_comm] using add_le_add_left hcinv (4 * ρ)
    exact hle.trans_lt hgapK
  exact nestedRichnessChain_density_contradiction chain direction hG hρ.le hcpos hApos
    hAN₀ hlog hgap hdensity

end Richness

section DependentRandomChoice

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Delete at most one point for every nonempty forbidden set. -/
lemma delete_forbidden_sets (X : Finset V) (B : Finset (Finset V))
    (hne : ∀ R ∈ B, R.Nonempty) :
    ∃ U : Finset V,
      U ⊆ X ∧ X.card ≤ U.card + B.card ∧ ∀ R ∈ B, ¬ R ⊆ U := by
  classical
  induction B using Finset.induction_on with
  | empty =>
      exact ⟨X, Finset.Subset.rfl, by simp, by simp⟩
  | @insert R B hRB ih =>
      have hRne : R.Nonempty := hne R (by simp)
      obtain ⟨x, hxR⟩ := hRne
      have hBne : ∀ S ∈ B, S.Nonempty := by
        intro S hSB
        exact hne S (by simp [hSB])
      obtain ⟨U, hUX, hcard, havoid⟩ := ih hBne
      refine ⟨U.erase x, ?_, ?_, ?_⟩
      · exact (Finset.erase_subset x U).trans hUX
      · rw [Finset.card_insert_of_notMem hRB]
        have herase : U.card ≤ (U.erase x).card + 1 := by
          by_cases hxU : x ∈ U
          · rw [Finset.card_erase_of_mem hxU]
            omega
          · rw [Finset.erase_eq_of_notMem hxU]
            omega
        omega
      · intro S hS hSU
        rcases (Finset.mem_insert.mp hS) with rfl | hSB
        · have hx : x ∈ U.erase x := hSU hxR
          simpa using hx
        · exact havoid S hSB (hSU.trans (Finset.erase_subset x U))

/-- Division-free finite averaging: a large total score gives one outcome
whose score is at least its bad-set count plus the desired reserve. -/
lemma exists_add_badCount_le {Omega : Type*} [Fintype Omega] [Nonempty Omega]
    (value badCount : Omega → ℕ) (a : ℕ)
    (hsum : Fintype.card Omega * a + ∑ ω : Omega, badCount ω ≤
      ∑ ω : Omega, value ω) :
    ∃ ω : Omega, a + badCount ω ≤ value ω := by
  by_contra h
  push_neg at h
  have hlt :
      ∑ ω : Omega, value ω < ∑ ω : Omega, (a + badCount ω) := by
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun ω _ ↦ h ω)
  have hrhs :
      ∑ ω : Omega, (a + badCount ω) =
        Fintype.card Omega * a + ∑ ω : Omega, badCount ω := by
    simp [Finset.sum_add_distrib, Nat.mul_comm]
  rw [hrhs] at hlt
  exact (not_lt_of_ge hsum) hlt

/-- Exact finite selection/deletion core of dependent random choice.

`X ω` is the common-neighbour set generated by outcome `ω`, while `B`
is the family of bad `r`-sets.  The displayed assumption is precisely the
unnormalized expectation inequality in KSSS Lemma 13.3. -/
theorem finite_drc_core {Omega : Type*} [Fintype Omega] [Nonempty Omega]
    (X : Omega → Finset V) (B : Finset (Finset V)) (a : ℕ)
    (hne : ∀ R ∈ B, R.Nonempty)
    (hsum : Fintype.card Omega * a +
        ∑ ω : Omega, (B.filter fun R ↦ R ⊆ X ω).card ≤
      ∑ ω : Omega, (X ω).card) :
    ∃ (ω : Omega) (U : Finset V),
      U ⊆ X ω ∧ a ≤ U.card ∧ ∀ R ∈ B, ¬ R ⊆ U := by
  let badCount : Omega → ℕ := fun ω ↦ (B.filter fun R ↦ R ⊆ X ω).card
  obtain ⟨ω, hω⟩ := exists_add_badCount_le (fun ω ↦ (X ω).card) badCount a hsum
  let Bω := B.filter fun R ↦ R ⊆ X ω
  have hneω : ∀ R ∈ Bω, R.Nonempty := by
    intro R hR
    exact hne R (Finset.mem_filter.mp hR).1
  obtain ⟨U, hUX, hcard, havoid⟩ := delete_forbidden_sets (X ω) Bω hneω
  refine ⟨ω, U, hUX, ?_, ?_⟩
  · dsimp [badCount] at hω
    dsimp [Bω] at hcard havoid
    omega
  · intro R hRB hRU
    have hRX : R ⊆ X ω := hRU.trans hUX
    exact havoid R (Finset.mem_filter.mpr ⟨hRB, hRX⟩) hRU

/-- The common neighbourhood of a finite set of vertices. -/
def commonNeighborFinset (G : SimpleGraph V) (R : Finset V) : Finset V :=
  letI := Classical.decPred fun w ↦ ∀ v ∈ R, G.Adj v w
  Finset.univ.filter fun w ↦ ∀ v ∈ R, G.Adj v w

@[simp] lemma mem_commonNeighborFinset {G : SimpleGraph V} {R : Finset V} {w : V} :
    w ∈ commonNeighborFinset G R ↔ ∀ v ∈ R, G.Adj v w := by
  simp [commonNeighborFinset]

@[simp] lemma commonNeighborFinset_empty (G : SimpleGraph V) :
    commonNeighborFinset G ∅ = Finset.univ := by
  ext w
  simp [commonNeighborFinset]

lemma commonNeighborFinset_anti {G : SimpleGraph V} {R S : Finset V}
    (h : R ⊆ S) : commonNeighborFinset G S ⊆ commonNeighborFinset G R := by
  intro w hw
  simp only [mem_commonNeighborFinset] at hw ⊢
  intro v hv
  exact hw v (h hv)

/-- A set all of whose `r`-subsets have at least `s` common neighbours. -/
def HasCommonNeighbors (G : SimpleGraph V) (A : Finset V) (r s : ℕ) : Prop :=
  ∀ R ⊆ A, R.card = r → s ≤ (commonNeighborFinset G R).card

lemma HasCommonNeighbors.mono_subset {G : SimpleGraph V} {A B : Finset V}
    {r s : ℕ} (h : HasCommonNeighbors G A r s) (hBA : B ⊆ A) :
    HasCommonNeighbors G B r s := by
  intro R hR hr
  exact h R (hR.trans hBA) hr

lemma HasCommonNeighbors.mono_s {G : SimpleGraph V} {A : Finset V}
    {r s₁ s₂ : ℕ} (h : HasCommonNeighbors G A r s₂) (hs : s₁ ≤ s₂) :
    HasCommonNeighbors G A r s₁ := by
  intro R hR hr
  exact hs.trans (h R hR hr)

/-- Deterministic deletion core of dependent random choice.  If a set `A`
has `b` bad `r`-subsets, deleting one chosen vertex from every bad subset
leaves at least `|A|-b` vertices and no bad `r`-subset.  This is the final,
purely finite step in KSSS Lemma 13.3. -/
lemma dependentRandomChoice_deletion
    (G : SimpleGraph V) (A : Finset V) (r s : ℕ) (hr : 0 < r) :
    ∃ B ⊆ A,
      A.card -
          ((A.powersetCard r).filter fun R ↦
            (commonNeighborFinset G R).card < s).card ≤ B.card ∧
        HasCommonNeighbors G B r s := by
  classical
  let bad : Finset (Finset V) :=
    (A.powersetCard r).filter fun R ↦ (commonNeighborFinset G R).card < s
  have bad_nonempty (R : {R // R ∈ bad}) : R.1.Nonempty := by
    have hcard : R.1.card = r := by
      have hm := R.2
      simp only [bad, Finset.mem_filter, Finset.mem_powersetCard] at hm
      exact hm.1.2
    exact Finset.card_pos.mp (by omega)
  let selected : {R // R ∈ bad} → V := fun R ↦ Classical.choose (bad_nonempty R)
  let chosen : Finset V := bad.attach.image selected
  refine ⟨A \ chosen, Finset.sdiff_subset, ?_, ?_⟩
  · have hchosen : chosen.card ≤ bad.card := by
      exact (Finset.card_image_le.trans_eq Finset.card_attach)
    have hsdiff : A.card - chosen.card ≤ (A \ chosen).card :=
      Finset.le_card_sdiff chosen A
    dsimp [bad] at hchosen ⊢
    omega
  · intro R hR hr
    by_contra hsmall
    have hbad : R ∈ bad := by
      simp only [bad, Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨hR.trans Finset.sdiff_subset, hr⟩, Nat.lt_of_not_ge hsmall⟩
    let Rbad : {R // R ∈ bad} := ⟨R, hbad⟩
    have hselected_mem_R : selected Rbad ∈ R :=
      Classical.choose_spec (bad_nonempty Rbad)
    have hselected_mem_chosen : selected Rbad ∈ chosen := by
      simp only [chosen, Finset.mem_image]
      exact ⟨Rbad, by simp, rfl⟩
    have hselected_mem_diff : selected Rbad ∈ A \ chosen := hR hselected_mem_R
    simp only [Finset.mem_sdiff] at hselected_mem_diff
    exact hselected_mem_diff.2 hselected_mem_chosen

end DependentRandomChoice

end

end Erdos88
