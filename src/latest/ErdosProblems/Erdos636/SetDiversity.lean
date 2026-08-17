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

import ErdosProblems.Erdos636.External.Erdos88.Richness

/-!
# The finite set-diversity lemma for Erdős Problem 636

This file formalizes the deterministic incidence argument in Kwan--Sudakov's
set-diversity lemma.  The paper's diversity quantity is the support on which
the two neighbourhood multiplicities differ; this is `supportDiff`.  We also
record the multiplicity-sensitive `incidenceDiffMass`, the corresponding
`ℓ¹` mass.  For vertex sets of uniformly bounded order the two quantities
are comparable by explicit constants.

The richness input is deliberately presented as the abstract predicate
`CorrectedRichWithBound`.  It records exactly the corrected (arXiv v4)
exceptional-vertex conclusion needed here and is independent of how a later
assembly obtains the numerical bound.
-/

open Classical SimpleGraph

namespace Erdos636

universe u

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The multiplicity with which `u` occurs in the union of the neighbourhoods
of vertices in `x`. -/
def incidence (G : SimpleGraph V) (x : Finset V) (u : V) : ℕ :=
  (x.filter fun v ↦ G.Adj v u).card

omit [Fintype V] [DecidableEq V] in
lemma incidence_le_card (G : SimpleGraph V) (x : Finset V) (u : V) :
    incidence G x u ≤ x.card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma incidence_eq_card_of_mem_commonNeighbor {G : SimpleGraph V}
    {x : Finset V} {u : V} (hu : u ∈ Erdos88.commonNeighborFinset G x) :
    incidence G x u = x.card := by
  rw [Erdos88.mem_commonNeighborFinset] at hu
  simp only [incidence, Finset.card_filter_eq_iff]
  exact hu

/-- The contribution of a single ambient vertex to the multiset symmetric
difference of two neighbourhood unions. -/
def incidenceDiffTerm (G : SimpleGraph V) (x y : Finset V) (u : V) : ℕ :=
  Int.natAbs ((incidence G x u : ℤ) - incidence G y u)

/-- Multiplicity-sensitive `ℓ¹` incidence-difference mass restricted to `A`.

For singleton `x` and `y` this is the usual symmetric-difference cardinality.
For larger vertex sets it retains multiplicity magnitudes, whereas the
Kwan--Sudakov support notion below records only whether a magnitude is
nonzero. -/
def incidenceDiffMass (G : SimpleGraph V) (A x y : Finset V) : ℕ :=
  ∑ u ∈ A, incidenceDiffTerm G x y u

/-- The support on which the two neighbourhood-incidence multiplicities
differ.  Its cardinality is the set-diversity quantity in Kwan--Sudakov. -/
def supportDiff (G : SimpleGraph V) (A x y : Finset V) : Finset V :=
  A.filter fun u ↦ incidence G x u ≠ incidence G y u

omit [Fintype V] [DecidableEq V] in
@[simp] lemma mem_supportDiff {G : SimpleGraph V} {A x y : Finset V} {u : V} :
    u ∈ supportDiff G A x y ↔
      u ∈ A ∧ incidence G x u ≠ incidence G y u := by
  simp [supportDiff]

/-- Cardinality of the incidence-difference support. -/
def supportDiffCard (G : SimpleGraph V) (A x y : Finset V) : ℕ :=
  (supportDiff G A x y).card

omit [Fintype V] [DecidableEq V] in
/-- The `ℓ¹` mass is supported exactly on `supportDiff`. -/
lemma incidenceDiffMass_eq_sum_supportDiff (G : SimpleGraph V)
    (A x y : Finset V) :
    incidenceDiffMass G A x y =
      ∑ u ∈ supportDiff G A x y, incidenceDiffTerm G x y u := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro u huA huSupport
  have heq : incidence G x u = incidence G y u := by
    by_contra hne
    exact huSupport (mem_supportDiff.mpr ⟨huA, hne⟩)
  simp [incidenceDiffTerm, heq]

/-- Every nonzero integer incidence difference contributes at least one unit
to the `ℓ¹` mass. -/
lemma supportDiffCard_le_incidenceDiffMass (G : SimpleGraph V)
    (A x y : Finset V) :
    supportDiffCard G A x y ≤ incidenceDiffMass G A x y := by
  rw [supportDiffCard, incidenceDiffMass_eq_sum_supportDiff]
  calc
    (supportDiff G A x y).card =
        ∑ _u ∈ supportDiff G A x y, 1 := by simp
    _ ≤ ∑ u ∈ supportDiff G A x y, incidenceDiffTerm G x y u := by
      apply Finset.sum_le_sum
      intro u hu
      rw [Nat.one_le_iff_ne_zero, incidenceDiffTerm,
        Int.natAbs_sub_ne_zero_iff]
      exact_mod_cast (mem_supportDiff.mp hu).2

/-- On vertex sets of order at most `K`, every incidence difference is at
most `K`; hence `ℓ¹` mass is at most `K` times support size. -/
lemma incidenceDiffMass_le_mul_supportDiffCard (G : SimpleGraph V)
    (A x y : Finset V) (K : ℕ) (hx : x.card ≤ K) (hy : y.card ≤ K) :
    incidenceDiffMass G A x y ≤ K * supportDiffCard G A x y := by
  rw [incidenceDiffMass_eq_sum_supportDiff, supportDiffCard]
  calc
    ∑ u ∈ supportDiff G A x y, incidenceDiffTerm G x y u ≤
        ∑ _u ∈ supportDiff G A x y, K := by
      apply Finset.sum_le_sum
      intro u _hu
      exact Int.natAbs_coe_sub_coe_le_of_le
        ((incidence_le_card G x u).trans hx)
        ((incidence_le_card G y u).trans hy)
    _ = K * (supportDiff G A x y).card := by
      simp [Nat.mul_comm]

lemma one_le_incidenceDiffTerm_of_missing {G : SimpleGraph V}
    {W x y : Finset V} {u v : V}
    (huW : u ∈ W) (hWx : W ⊆ Erdos88.commonNeighborFinset G x)
    (hcard : x.card = y.card) (hvy : v ∈ y)
    (huv : u ∉ Erdos88.neighborsIn G v W) :
    1 ≤ incidenceDiffTerm G x y u := by
  have hix : incidence G x u = x.card :=
    incidence_eq_card_of_mem_commonNeighbor (hWx huW)
  have huv' : ¬ G.Adj v u := by
    intro hadj
    exact huv (Erdos88.mem_neighborsIn.mpr ⟨huW, hadj⟩)
  have hvfilter : v ∉ y.filter fun w ↦ G.Adj w u := by
    simp [hvy, huv']
  have hproper : y.filter (fun w ↦ G.Adj w u) ⊂ y := by
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨Finset.filter_subset _ _, fun heq ↦ hvfilter (heq.symm ▸ hvy)⟩
  have hiy : incidence G y u < y.card := by
    exact Finset.card_lt_card hproper
  rw [incidenceDiffTerm, hix, hcard,
    Int.natAbs_natCast_sub_natCast_of_ge (incidence_le_card G y u)]
  omega

/-- A vertex missing an edge to `v` contributes at least one unit to the
incidence difference.  Consequently the number of such vertices is bounded
by the entire incidence-difference mass. -/
lemma card_sdiff_neighborsIn_le_incidenceDiffMass {G : SimpleGraph V}
    {W x y : Finset V} {v : V}
    (hWx : W ⊆ Erdos88.commonNeighborFinset G x)
    (hcard : x.card = y.card) (hvy : v ∈ y) :
    (W \ Erdos88.neighborsIn G v W).card ≤ incidenceDiffMass G W x y := by
  calc
    (W \ Erdos88.neighborsIn G v W).card =
        ∑ _u ∈ W \ Erdos88.neighborsIn G v W, 1 := by simp
    _ ≤ ∑ u ∈ W \ Erdos88.neighborsIn G v W,
        incidenceDiffTerm G x y u := by
      apply Finset.sum_le_sum
      intro u hu
      exact one_le_incidenceDiffTerm_of_missing
        (Finset.mem_sdiff.mp hu).1 hWx hcard hvy
        (Finset.mem_sdiff.mp hu).2
    _ ≤ ∑ u ∈ W, incidenceDiffTerm G x y u := by
      exact Finset.sum_le_sum_of_subset Finset.sdiff_subset
    _ = incidenceDiffMass G W x y := rfl

/-- The sharper support bridge used in the paper: every vertex of `W` missed
by a member of `y` has different incidence multiplicities for `x` and `y`. -/
lemma card_sdiff_neighborsIn_le_supportDiffCard {G : SimpleGraph V}
    {W x y : Finset V} {v : V}
    (hWx : W ⊆ Erdos88.commonNeighborFinset G x)
    (hcard : x.card = y.card) (hvy : v ∈ y) :
    (W \ Erdos88.neighborsIn G v W).card ≤ supportDiffCard G W x y := by
  rw [supportDiffCard]
  apply Finset.card_le_card
  intro u hu
  have hone : 1 ≤ incidenceDiffTerm G x y u :=
    one_le_incidenceDiffTerm_of_missing
      (Finset.mem_sdiff.mp hu).1 hWx hcard hvy (Finset.mem_sdiff.mp hu).2
  apply mem_supportDiff.mpr
  refine ⟨(Finset.mem_sdiff.mp hu).1, ?_⟩
  intro heq
  have hzero : incidenceDiffTerm G x y u = 0 := by
    simp [incidenceDiffTerm, heq]
  omega

/-- The exact corrected-richness interface used by set diversity: every test
set above the `δ` cutoff has at most `b` vertices which are sparse or dense
at threshold `ρ`. -/
def CorrectedRichWithBound (G : SimpleGraph V) (δ ρ : ℝ) (b : ℕ) : Prop :=
  ∀ W : Finset V,
    δ * Fintype.card V ≤ W.card →
      (Erdos88.exceptionalVertices G W ρ).card ≤ b

/-- Convert the real-power exceptional bound in the repository's corrected
`Erdos88.Rich` predicate to a natural bound suitable for finite counting. -/
lemma correctedRichWithBound_of_rich {G : SimpleGraph V} {δ ρ α : ℝ} {b : ℕ}
    (hrich : Erdos88.Rich G δ ρ α)
    (hbound : (Fintype.card V : ℝ) ^ α ≤ b) :
    CorrectedRichWithBound G δ ρ b := by
  intro W hW
  have hreal : ((Erdos88.exceptionalVertices G W ρ).card : ℝ) ≤ b :=
    (hrich W hW).trans hbound
  exact_mod_cast hreal

/-- If the incidence-difference mass is below `ρ |W|`, one member of `y`
is exceptionally dense into `W`. -/
lemma exists_mem_highExceptional_of_incidenceDiffMass_lt
    {G : SimpleGraph V} {ρ : ℝ} {k : ℕ} {W x y : Finset V}
    (hk : 0 < k) (hWx : W ⊆ Erdos88.commonNeighborFinset G x)
    (hxcard : x.card = k) (hycard : y.card = k)
    (hmass : (incidenceDiffMass G W x y : ℝ) < ρ * W.card) :
    ∃ v ∈ y,
      ((W \ Erdos88.neighborsIn G v W).card : ℝ) ≤ ρ * W.card := by
  have hyne : y.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hvy⟩ := hyne
  refine ⟨v, hvy, ?_⟩
  by_contra hlarge
  have hlt : ρ * (W.card : ℝ) <
      ((W \ Erdos88.neighborsIn G v W).card : ℝ) := lt_of_not_ge hlarge
  have hcard : x.card = y.card := hxcard.trans hycard.symm
  have hleNat := card_sdiff_neighborsIn_le_incidenceDiffMass hWx hcard hvy
  have hle : ((W \ Erdos88.neighborsIn G v W).card : ℝ) ≤
      incidenceDiffMass G W x y := by
    exact_mod_cast hleNat
  exact (not_lt_of_ge hle) (hmass.trans hlt)

/-- Support version of the preceding exceptional-vertex lemma.  This is the
form used by Kwan--Sudakov: only the locations of unequal multiplicities are
counted. -/
lemma exists_mem_highExceptional_of_supportDiffCard_lt
    {G : SimpleGraph V} {ρ : ℝ} {k : ℕ} {W x y : Finset V}
    (hk : 0 < k) (hWx : W ⊆ Erdos88.commonNeighborFinset G x)
    (hxcard : x.card = k) (hycard : y.card = k)
    (hsupport : (supportDiffCard G W x y : ℝ) < ρ * W.card) :
    ∃ v ∈ y,
      ((W \ Erdos88.neighborsIn G v W).card : ℝ) ≤ ρ * W.card := by
  have hyne : y.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hvy⟩ := hyne
  refine ⟨v, hvy, ?_⟩
  by_contra hlarge
  have hlt : ρ * (W.card : ℝ) <
      ((W \ Erdos88.neighborsIn G v W).card : ℝ) := lt_of_not_ge hlarge
  have hcard : x.card = y.card := hxcard.trans hycard.symm
  have hleNat := card_sdiff_neighborsIn_le_supportDiffCard hWx hcard hvy
  have hle : ((W \ Erdos88.neighborsIn G v W).card : ℝ) ≤
      supportDiffCard G W x y := by
    exact_mod_cast hleNat
  exact (not_lt_of_ge hle) (hsupport.trans hlt)

/-- An `ℓ¹` strengthening of finite Kwan--Sudakov set diversity.

If `x` is a nonempty `k`-set with common-neighbour test set `W`, then a
pairwise-disjoint family of `k`-sets whose incidence mass from `x` is below
`ρ |W|` has cardinality at most the corrected-richness exceptional bound.
The paper additionally assumes every member is disjoint from `x`; this is
recorded here even though the incidence argument proves the stronger result
without using it. -/
theorem setDiversity
    {G : SimpleGraph V} {δ ρ : ℝ} {b k : ℕ}
    {W x : Finset V} {Y : Finset (Finset V)}
    (hrich : CorrectedRichWithBound G δ ρ b)
    (hWsize : δ * Fintype.card V ≤ W.card)
    (hk : 0 < k) (hWx : W ⊆ Erdos88.commonNeighborFinset G x)
    (hxcard : x.card = k)
    (hYcard : ∀ y ∈ Y, y.card = k)
    (_hYbase : ∀ y ∈ Y, Disjoint x y)
    (hYdisjoint : (Y : Set (Finset V)).PairwiseDisjoint id)
    (hYmass : ∀ y ∈ Y,
      (incidenceDiffMass G W x y : ℝ) < ρ * W.card) :
    Y.card ≤ b := by
  have hexceptional : ∀ y ∈ Y, ∃ v, v ∈ y ∧
      v ∈ Erdos88.exceptionalVertices G W ρ := by
    intro y hyY
    obtain ⟨v, hvy, hvdense⟩ :=
      exists_mem_highExceptional_of_incidenceDiffMass_lt
        hk hWx hxcard (hYcard y hyY) (hYmass y hyY)
    exact ⟨v, hvy, Erdos88.mem_exceptionalVertices.mpr (Or.inr hvdense)⟩
  let chosen : {y // y ∈ Y} → V := fun y ↦
    Classical.choose (hexceptional y.1 y.2)
  have hchosen_mem (y : {y // y ∈ Y}) : chosen y ∈ y.1 :=
    (Classical.choose_spec (hexceptional y.1 y.2)).1
  have hchosen_exceptional (y : {y // y ∈ Y}) :
      chosen y ∈ Erdos88.exceptionalVertices G W ρ :=
    (Classical.choose_spec (hexceptional y.1 y.2)).2
  have hcard : Y.attach.card ≤ (Erdos88.exceptionalVertices G W ρ).card := by
    apply Finset.card_le_card_of_injOn chosen
    · intro y _hy
      exact hchosen_exceptional y
    · intro y _hy z _hz hyz
      apply Subtype.ext
      by_contra hyzne
      have hdisj : Disjoint y.1 z.1 := hYdisjoint y.2 z.2 hyzne
      have hchosen_z : chosen y ∈ z.1 := by
        rw [hyz]
        exact hchosen_mem z
      exact (Finset.disjoint_left.mp hdisj) (hchosen_mem y) hchosen_z
  simpa using hcard.trans (hrich W hWsize)

/-- Finite Kwan--Sudakov set diversity in the paper's support formulation.

For every member of the pairwise-disjoint family, a small support difference
provides a vertex which is exceptionally dense into `W`.  Choosing one such
vertex from each member is injective because the family is pairwise disjoint.
-/
theorem setDiversity_support
    {G : SimpleGraph V} {δ ρ : ℝ} {b k : ℕ}
    {W x : Finset V} {Y : Finset (Finset V)}
    (hrich : CorrectedRichWithBound G δ ρ b)
    (hWsize : δ * Fintype.card V ≤ W.card)
    (hk : 0 < k) (hWx : W ⊆ Erdos88.commonNeighborFinset G x)
    (hxcard : x.card = k)
    (hYcard : ∀ y ∈ Y, y.card = k)
    (_hYbase : ∀ y ∈ Y, Disjoint x y)
    (hYdisjoint : (Y : Set (Finset V)).PairwiseDisjoint id)
    (hYsupport : ∀ y ∈ Y,
      (supportDiffCard G W x y : ℝ) < ρ * W.card) :
    Y.card ≤ b := by
  have hexceptional : ∀ y ∈ Y, ∃ v, v ∈ y ∧
      v ∈ Erdos88.exceptionalVertices G W ρ := by
    intro y hyY
    obtain ⟨v, hvy, hvdense⟩ :=
      exists_mem_highExceptional_of_supportDiffCard_lt
        hk hWx hxcard (hYcard y hyY) (hYsupport y hyY)
    exact ⟨v, hvy, Erdos88.mem_exceptionalVertices.mpr (Or.inr hvdense)⟩
  let chosen : {y // y ∈ Y} → V := fun y ↦
    Classical.choose (hexceptional y.1 y.2)
  have hchosen_mem (y : {y // y ∈ Y}) : chosen y ∈ y.1 :=
    (Classical.choose_spec (hexceptional y.1 y.2)).1
  have hchosen_exceptional (y : {y // y ∈ Y}) :
      chosen y ∈ Erdos88.exceptionalVertices G W ρ :=
    (Classical.choose_spec (hexceptional y.1 y.2)).2
  have hcard : Y.attach.card ≤ (Erdos88.exceptionalVertices G W ρ).card := by
    apply Finset.card_le_card_of_injOn chosen
    · intro y _hy
      exact hchosen_exceptional y
    · intro y _hy z _hz hyz
      apply Subtype.ext
      by_contra hyzne
      have hdisj : Disjoint y.1 z.1 := hYdisjoint y.2 z.2 hyzne
      have hchosen_z : chosen y ∈ z.1 := by
        rw [hyz]
        exact hchosen_mem z
      exact (Finset.disjoint_left.mp hdisj) (hchosen_mem y) hchosen_z
  simpa using hcard.trans (hrich W hWsize)

/-- Ambient-order normalization of the support set-diversity theorem. -/
theorem setDiversity_support_of_globalCard_lt
    {G : SimpleGraph V} {δ ρ : ℝ} {b k : ℕ}
    {W x : Finset V} {Y : Finset (Finset V)}
    (hrich : CorrectedRichWithBound G δ ρ b)
    (hWsize : δ * Fintype.card V ≤ W.card) (hρ : 0 ≤ ρ)
    (hk : 0 < k) (hWx : W ⊆ Erdos88.commonNeighborFinset G x)
    (hxcard : x.card = k)
    (hYcard : ∀ y ∈ Y, y.card = k)
    (hYbase : ∀ y ∈ Y, Disjoint x y)
    (hYdisjoint : (Y : Set (Finset V)).PairwiseDisjoint id)
    (hYsupport : ∀ y ∈ Y,
      (supportDiffCard G W x y : ℝ) < δ * ρ * Fintype.card V) :
    Y.card ≤ b := by
  apply setDiversity_support hrich hWsize hk hWx hxcard hYcard hYbase hYdisjoint
  intro y hyY
  refine (hYsupport y hyY).trans_le ?_
  calc
    δ * ρ * (Fintype.card V : ℝ) = ρ * (δ * Fintype.card V) := by ring
    _ ≤ ρ * W.card := mul_le_mul_of_nonneg_left hWsize hρ

/-- Paper-normalized form of set diversity.  The mass hypothesis is measured
against the ambient order `|V|`: `δρ |V| ≤ ρ |W|` follows from the test-set
size condition and `ρ ≥ 0`. -/
theorem setDiversity_of_globalMass_lt
    {G : SimpleGraph V} {δ ρ : ℝ} {b k : ℕ}
    {W x : Finset V} {Y : Finset (Finset V)}
    (hrich : CorrectedRichWithBound G δ ρ b)
    (hWsize : δ * Fintype.card V ≤ W.card) (hρ : 0 ≤ ρ)
    (hk : 0 < k) (hWx : W ⊆ Erdos88.commonNeighborFinset G x)
    (hxcard : x.card = k)
    (hYcard : ∀ y ∈ Y, y.card = k)
    (hYbase : ∀ y ∈ Y, Disjoint x y)
    (hYdisjoint : (Y : Set (Finset V)).PairwiseDisjoint id)
    (hYmass : ∀ y ∈ Y,
      (incidenceDiffMass G W x y : ℝ) < δ * ρ * Fintype.card V) :
    Y.card ≤ b := by
  apply setDiversity hrich hWsize hk hWx hxcard hYcard hYbase hYdisjoint
  intro y hyY
  refine (hYmass y hyY).trans_le ?_
  calc
    δ * ρ * (Fintype.card V : ℝ) = ρ * (δ * Fintype.card V) := by ring
    _ ≤ ρ * W.card := mul_le_mul_of_nonneg_left hWsize hρ

/-- Contradiction form of `setDiversity`, matching the common phrase
"there do not exist more than `b` pairwise-disjoint bad sets". -/
theorem not_exists_setDiversity_family
    {G : SimpleGraph V} {δ ρ : ℝ} {b k : ℕ}
    {W x : Finset V} {Y : Finset (Finset V)}
    (hrich : CorrectedRichWithBound G δ ρ b)
    (hWsize : δ * Fintype.card V ≤ W.card)
    (hk : 0 < k) (hWx : W ⊆ Erdos88.commonNeighborFinset G x)
    (hxcard : x.card = k)
    (hYcard : ∀ y ∈ Y, y.card = k)
    (hYbase : ∀ y ∈ Y, Disjoint x y)
    (hYdisjoint : (Y : Set (Finset V)).PairwiseDisjoint id)
    (hYmass : ∀ y ∈ Y,
      (incidenceDiffMass G W x y : ℝ) < ρ * W.card)
    (hlarge : b < Y.card) : False := by
  exact (not_lt_of_ge
    (setDiversity hrich hWsize hk hWx hxcard hYcard hYbase hYdisjoint hYmass)) hlarge

end

end Erdos636
