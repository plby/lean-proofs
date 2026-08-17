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

import ErdosProblems.Erdos636.CommonNeighborhood
import ErdosProblems.Erdos636.RichnessBridge

/-!
# Candidate reservoirs for Erdős Problem 636

This file turns the ordered-tuple common-neighbourhood estimate into an
exact estimate for genuine finite sets.  The final result chooses a
reservoir away from an arbitrary already-used base and retains an explicit
target number of good `K`-sets.  Consequently all later finite losses
(degree fibres, the sunflower bound, and Turán thinning) can be substituted
directly for `target`.
-/

open Classical SimpleGraph

namespace Erdos636

universe u

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The family of `K`-subsets of `A` having at least the richness-scale
number of common neighbours. -/
def goodCandidateFamily (G : SimpleGraph V) (epsilon : ℝ) (K : ℕ)
    (A : Finset V) : Finset (Finset V) :=
  (A.powersetCard K).filter fun X ↦
    epsilon ^ K * Fintype.card V ≤
      (Erdos88.commonNeighborFinset G X).card

lemma goodCandidateFamily_subset_powersetCard
    (G : SimpleGraph V) (epsilon : ℝ) (K : ℕ) (A : Finset V) :
    goodCandidateFamily G epsilon K A ⊆ A.powersetCard K :=
  Finset.filter_subset _ _

lemma goodCandidateFamily_subset {G : SimpleGraph V} {epsilon : ℝ}
    {K : ℕ} {A X : Finset V} (hX : X ∈ goodCandidateFamily G epsilon K A) :
    X ⊆ A := by
  exact (Finset.mem_powersetCard.mp
    (goodCandidateFamily_subset_powersetCard G epsilon K A hX)).1

lemma goodCandidateFamily_card_eq {G : SimpleGraph V} {epsilon : ℝ}
    {K : ℕ} {A X : Finset V} (hX : X ∈ goodCandidateFamily G epsilon K A) :
    X.card = K := by
  exact (Finset.mem_powersetCard.mp
    (goodCandidateFamily_subset_powersetCard G epsilon K A hX)).2

lemma goodCandidateFamily_common {G : SimpleGraph V} {epsilon : ℝ}
    {K : ℕ} {A X : Finset V} (hX : X ∈ goodCandidateFamily G epsilon K A) :
    epsilon ^ K * Fintype.card V ≤
      (Erdos88.commonNeighborFinset G X).card := by
  exact (Finset.mem_filter.mp hX).2

/-! ## Canonical enumeration of a finite set -/

/-- Enumerate a finite set whose cardinality is `K`.  No ambient ordering is
needed: `Finset.equivFin` supplies an arbitrary, but fixed, equivalence. -/
def tupleOfFinset (K : ℕ) (X : Finset V) (hX : X.card = K) : Fin K → V :=
  fun i ↦ ((X.equivFin).symm (Fin.cast hX.symm i)).1

lemma tupleOfFinset_mem (K : ℕ) (X : Finset V) (hX : X.card = K)
    (i : Fin K) : tupleOfFinset K X hX i ∈ X :=
  ((X.equivFin).symm (Fin.cast hX.symm i)).2

lemma exists_tupleOfFinset_eq (K : ℕ) (X : Finset V)
    (hX : X.card = K) {v : V} (hv : v ∈ X) :
    ∃ i : Fin K, tupleOfFinset K X hX i = v := by
  let j : Fin X.card := X.equivFin ⟨v, hv⟩
  refine ⟨Fin.cast hX j, ?_⟩
  simp [tupleOfFinset, j]

lemma tupleOfFinset_injective_on_sets (K : ℕ) {X Y : Finset V}
    (hX : X.card = K) (hY : Y.card = K)
    (h : tupleOfFinset K X hX = tupleOfFinset K Y hY) : X = Y := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi⟩ := exists_tupleOfFinset_eq K X hX hv
    rw [← hi, h]
    exact tupleOfFinset_mem K Y hY i
  · intro hv
    obtain ⟨i, hi⟩ := exists_tupleOfFinset_eq K Y hY hv
    rw [← hi, ← h]
    exact tupleOfFinset_mem K X hX i

lemma commonNeighbors_tupleOfFinset (G : SimpleGraph V) (K : ℕ)
    (X : Finset V) (hX : X.card = K) :
    commonNeighbors G (tupleOfFinset K X hX) =
      Erdos88.commonNeighborFinset G X := by
  ext w
  simp only [mem_commonNeighbors, Erdos88.mem_commonNeighborFinset]
  constructor
  · intro h v hv
    obtain ⟨i, rfl⟩ := exists_tupleOfFinset_eq K X hX hv
    exact h i
  · intro h i
    exact h _ (tupleOfFinset_mem K X hX i)

/-! ## Richness count -/

/-- The rounded common-neighbourhood threshold used in the ordered-tuple
induction. -/
def candidateCommonThreshold (epsilon : ℝ) (q : ℕ) : ℕ :=
  ⌈epsilon ^ q * Fintype.card V⌉₊

/-- Corrected richness bounds the bad ordered `K`-tuples at the power
density `epsilon^K`. -/
theorem card_badCandidateTuples_le
    {G : SimpleGraph V} {epsilon : ℝ} {K : ℕ}
    (hK : 1 ≤ K) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hrich : KwanSudakovRich G (epsilon ^ K) epsilon) :
    (badOrderedTuples
      (HasLargeCommonNeighborhood G
        (candidateCommonThreshold (V := V) epsilon)) K).card ≤
      K * Fintype.card V ^ (K - 1) *
        ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ := by
  simp only [badOrderedTuples, HasLargeCommonNeighborhood, not_le]
  apply card_orderedTuples_small_commonNeighbors_le
    G (candidateCommonThreshold (V := V) epsilon) K
      ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ hK
  · simp [candidateCommonThreshold]
  · intro q hq x hx
    let W : Finset V := commonNeighbors G x
    have hqle : q ≤ K - 1 := by omega
    have hpowmono : epsilon ^ (K - 1) ≤ epsilon ^ q :=
      pow_le_pow_of_le_one hepsilon0.le hepsilon1 hqle
    have hKpow : epsilon ^ K ≤ epsilon ^ (K - 1) :=
      ksRich_pow_le_previous hepsilon0.le hepsilon1 hK
    have hthresholdReal :
        epsilon ^ q * Fintype.card V ≤
          (candidateCommonThreshold (V := V) epsilon q : ℕ) := by
      exact Nat.le_ceil _
    have hWreal : epsilon ^ q * Fintype.card V ≤ (W.card : ℝ) := by
      exact hthresholdReal.trans (by exact_mod_cast hx)
    have hWlarge : epsilon ^ K * Fintype.card V ≤ W.card := by
      calc
        epsilon ^ K * (Fintype.card V : ℝ) ≤
            epsilon ^ (K - 1) * Fintype.card V := by gcongr
        _ ≤ epsilon ^ q * Fintype.card V := by gcongr
        _ ≤ W.card := hWreal
    have hsub :
        (Finset.univ.filter fun v : V ↦
          (Erdos88.neighborsIn G v W).card <
            candidateCommonThreshold (V := V) epsilon (q + 1)) ⊆
          strictExceptionalVertices G W epsilon := by
      intro v hv
      have hvltNat := (Finset.mem_filter.mp hv).2
      have hvlt :
          ((Erdos88.neighborsIn G v W).card : ℝ) <
            epsilon ^ (q + 1) * Fintype.card V := by
        exact Nat.lt_ceil.mp hvltNat
      have hnext : epsilon ^ (q + 1) * Fintype.card V ≤ epsilon * W.card := by
        rw [pow_succ]
        nlinarith
      exact mem_strictExceptionalVertices.mpr (Or.inl (hvlt.trans_le hnext))
    have hcard := Finset.card_le_card hsub
    have hrichW := hrich W hWlarge
    have hceil :
        (strictExceptionalVertices G W epsilon).card ≤
          ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ := by
      have hceilReal :
          ((strictExceptionalVertices G W epsilon).card : ℝ) ≤
            (⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ : ℕ) :=
        hrichW.trans (Nat.le_ceil _)
      exact_mod_cast hceilReal
    exact hcard.trans hceil

/-- Exact binomial-minus-error count for good `K`-sets in an arbitrary
reservoir `A`. -/
theorem choose_card_le_goodCandidateFamily_card_add_error
    [Nonempty V] {G : SimpleGraph V} {epsilon : ℝ} {K : ℕ}
    (A : Finset V)
    (hK : 1 ≤ K) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hrich : KwanSudakovRich G (epsilon ^ K) epsilon) :
    A.card.choose K ≤
      (goodCandidateFamily G epsilon K A).card +
        K * Fintype.card V ^ (K - 1) *
          ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ := by
  classical
  let bad : Finset (Finset V) :=
    (A.powersetCard K).filter fun X ↦
      ¬ epsilon ^ K * Fintype.card V ≤
        (Erdos88.commonNeighborFinset G X).card
  let BadSet := {X : Finset V // X ∈ bad}
  let BadTuple := {x : Fin K → V // x ∈
    badOrderedTuples
      (HasLargeCommonNeighborhood G
        (candidateCommonThreshold (V := V) epsilon)) K}
  let f : BadSet → BadTuple := fun X ↦ by
    have hXcard : X.1.card = K :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp X.2).1).2
    refine ⟨tupleOfFinset K X.1 hXcard, ?_⟩
    rw [mem_badOrderedTuples]
    simp only [HasLargeCommonNeighborhood]
    rw [commonNeighbors_tupleOfFinset]
    have hbad := (Finset.mem_filter.mp X.2).2
    rw [candidateCommonThreshold]
    exact Nat.not_le_of_lt (Nat.lt_ceil.mpr (lt_of_not_ge hbad))
  have hf : Function.Injective f := by
    intro X Y hXY
    apply Subtype.ext
    dsimp [f] at hXY
    exact tupleOfFinset_injective_on_sets K
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp X.2).1).2
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp Y.2).1).2
      (congrArg Subtype.val hXY)
  have hbadCard : bad.card ≤
      (badOrderedTuples
        (HasLargeCommonNeighborhood G
          (candidateCommonThreshold (V := V) epsilon)) K).card := by
    calc
      bad.card = Fintype.card BadSet := by
        simp only [BadSet, Fintype.card_coe]
      _ ≤ Fintype.card BadTuple := Fintype.card_le_of_injective f hf
      _ = (badOrderedTuples
          (HasLargeCommonNeighborhood G
            (candidateCommonThreshold (V := V) epsilon)) K).card := by
        simp only [BadTuple, Fintype.card_coe]
  have hbadBound : bad.card ≤
      K * Fintype.card V ^ (K - 1) *
        ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ :=
    hbadCard.trans (card_badCandidateTuples_le hK hepsilon0 hepsilon1 hrich)
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := A.powersetCard K)
    (p := fun X : Finset V ↦
      epsilon ^ K * Fintype.card V ≤
        (Erdos88.commonNeighborFinset G X).card)
  rw [Finset.card_powersetCard] at hpartition
  change A.card.choose K ≤
    (goodCandidateFamily G epsilon K A).card + _
  rw [← hpartition]
  exact Nat.add_le_add_left hbadBound _

/-! ## Choosing a reservoir away from a used base -/

/-- Choose a prescribed-size reservoir outside `base`, and retain more than
`target` good `K`-sets.  The single numerical hypothesis is deliberately
exact: later callers substitute their entire fibre/sunflower/Turán loss for
`target`. -/
theorem exists_goodCandidateReservoir
    [Nonempty V] {G : SimpleGraph V} {epsilon : ℝ} {K s target : ℕ}
    (base : Finset V)
    (hK : 1 ≤ K) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hrich : KwanSudakovRich G (epsilon ^ K) epsilon)
    (hcapacity : s ≤ (Finset.univ \ base).card)
    (hnumerical :
      K * Fintype.card V ^ (K - 1) *
          ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ + target <
        s.choose K) :
    ∃ A : Finset V,
      A ⊆ Finset.univ \ base ∧ A.card = s ∧
      target < (goodCandidateFamily G epsilon K A).card := by
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hcapacity
  refine ⟨A, hAsub, hAcard, ?_⟩
  have hcount := choose_card_le_goodCandidateFamily_card_add_error
    A hK hepsilon0 hepsilon1 hrich
  rw [hAcard] at hcount
  omega

/-- Graph-facing form with all structural-family properties exposed. -/
theorem exists_goodCandidateReservoir_package
    [Nonempty V] {G : SimpleGraph V} {epsilon : ℝ} {K s target : ℕ}
    (base : Finset V)
    (hK : 1 ≤ K) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hrich : KwanSudakovRich G (epsilon ^ K) epsilon)
    (hcapacity : s ≤ (Finset.univ \ base).card)
    (hnumerical :
      K * Fintype.card V ^ (K - 1) *
          ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ + target <
        s.choose K) :
    ∃ A : Finset V, ∃ candidates : Finset (Finset V),
      A ⊆ Finset.univ \ base ∧ A.card = s ∧
      candidates = goodCandidateFamily G epsilon K A ∧
      (∀ X ∈ candidates, X ⊆ A) ∧
      (∀ X ∈ candidates, X.card = K) ∧
      (∀ X ∈ candidates,
        epsilon ^ K * Fintype.card V ≤
          (Erdos88.commonNeighborFinset G X).card) ∧
      target < candidates.card := by
  obtain ⟨A, hAsub, hAcard, hlarge⟩ :=
    exists_goodCandidateReservoir base hK hepsilon0 hepsilon1 hrich
      hcapacity hnumerical
  refine ⟨A, goodCandidateFamily G epsilon K A,
    hAsub, hAcard, rfl, ?_, ?_, ?_, hlarge⟩
  · exact fun X hX ↦ goodCandidateFamily_subset hX
  · exact fun X hX ↦ goodCandidateFamily_card_eq hX
  · exact fun X hX ↦ goodCandidateFamily_common hX

/-- Version of the package for the three pairwise-disjoint reservoirs used
by the structural argument.  The extra `s` in `hfit` is essential: the
non-strict base-capacity assertion alone could fill the whole ambient
vertex set and leave no candidate reservoir. -/
theorem exists_goodCandidateReservoir_away_three
    [Nonempty V] {G : SimpleGraph V} {epsilon : ℝ} {K s target : ℕ}
    (Wminus Wplus U0 : Finset V)
    (hWmWp : Disjoint Wminus Wplus)
    (hWmU : Disjoint Wminus U0) (hWpU : Disjoint Wplus U0)
    (hK : 1 ≤ K) (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hrich : KwanSudakovRich G (epsilon ^ K) epsilon)
    (hfit : Wminus.card + Wplus.card + U0.card + s ≤ Fintype.card V)
    (hnumerical :
      K * Fintype.card V ^ (K - 1) *
          ⌈(Fintype.card V : ℝ) ^ (1 / 5 : ℝ)⌉₊ + target <
        s.choose K) :
    ∃ A : Finset V, ∃ candidates : Finset (Finset V),
      Disjoint A (Wminus ∪ Wplus ∪ U0) ∧ A.card = s ∧
      candidates = goodCandidateFamily G epsilon K A ∧
      (∀ X ∈ candidates, X ⊆ A) ∧
      (∀ X ∈ candidates, X.card = K) ∧
      (∀ X ∈ candidates,
        epsilon ^ K * Fintype.card V ≤
          (Erdos88.commonNeighborFinset G X).card) ∧
      target < candidates.card := by
  let base := Wminus ∪ Wplus ∪ U0
  have hbaseDisj : Disjoint (Wminus ∪ Wplus) U0 := by
    simpa only [Finset.disjoint_union_left] using And.intro hWmU hWpU
  have hbaseCard : base.card = Wminus.card + Wplus.card + U0.card := by
    dsimp [base]
    rw [Finset.card_union_of_disjoint hbaseDisj,
      Finset.card_union_of_disjoint hWmWp]
  have hcomplementCard : (Finset.univ \ base).card =
      Fintype.card V - (Wminus.card + Wplus.card + U0.card) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ base),
      Finset.card_univ, hbaseCard]
  have hcapacity : s ≤ (Finset.univ \ base).card := by
    rw [hcomplementCard]
    omega
  obtain ⟨A, candidates, hAsub, hAcard, hcandidates, hsub,
      huniform, hcommon, hlarge⟩ :=
    exists_goodCandidateReservoir_package base hK hepsilon0 hepsilon1
      hrich hcapacity hnumerical
  refine ⟨A, candidates, ?_, hAcard, hcandidates, hsub,
    huniform, hcommon, hlarge⟩
  rw [Finset.disjoint_left]
  intro v hvA hvbase
  exact (Finset.mem_sdiff.mp (hAsub hvA)).2 hvbase

end

end Erdos636
