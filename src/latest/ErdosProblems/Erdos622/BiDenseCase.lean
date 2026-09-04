/-
Copyright 2026 The Lean-Proofs Authors.

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
import ErdosProblems.Erdos622.Assembly
import ErdosProblems.Erdos622.Concentration
import ErdosProblems.Erdos622.DiracStability
import ErdosProblems.Erdos622.EdgeCounting
import ErdosProblems.Erdos622.KSSStability
import ErdosProblems.Erdos622.Regularity
import ErdosProblems.Erdos622.TailoredTrichotomy

/-!
# The bi-dense case of Erdős Problem 622

This file develops the uniform sampling estimates used in the bi-dense
branch.  The sample space is the powerset of the whole vertex set.  In
particular, the estimates below apply both to the cells of a weak cut
decomposition and to the neighbourhood of every vertex.
-/

open Filter Finset Real
open scoped BigOperators Topology

namespace Erdos622
namespace BiDenseCase

noncomputable section

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

private def halfProbability (_ : V) : ℝ := 1 / 2

/-- Number of selected elements belonging to a fixed test set. -/
def intersectionCount (C S : Finset V) : ℝ := ((S ∩ C).card : ℝ)

private lemma intersectionCount_sum_indicator (C S : Finset V) :
    intersectionCount C S = ∑ v ∈ C, if v ∈ S then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole]
  simp [intersectionCount, Finset.filter_mem_eq_inter, Finset.inter_comm]

/-- The exact mean of the intersection with a fixed set under uniform
vertex sampling. -/
lemma bernoulliExpectation_half_intersectionCount (C : Finset V) :
    Erdos76.FiniteNibble.bernoulliExpectation (univ : Finset V)
        halfProbability (intersectionCount C) = (C.card : ℝ) / 2 := by
  rw [Erdos76.FiniteNibble.bernoulliExpectation]
  simp_rw [intersectionCount_sum_indicator, mul_sum]
  rw [Finset.sum_comm]
  calc
    ∑ v ∈ C, ∑ S ∈ (univ : Finset V).powerset,
        Erdos76.FiniteNibble.bernoulliMass univ halfProbability S *
          (if v ∈ S then (1 : ℝ) else 0) =
        ∑ _v ∈ C, (1 / 2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro v hv
      calc
        ∑ S ∈ (univ : Finset V).powerset,
            Erdos76.FiniteNibble.bernoulliMass univ halfProbability S *
              (if v ∈ S then (1 : ℝ) else 0) =
            ∑ S ∈ (univ : Finset V).powerset with v ∈ S,
              Erdos76.FiniteNibble.bernoulliMass univ halfProbability S := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro S hS
          by_cases hvS : v ∈ S <;> simp [hvS]
        _ = 1 / 2 := by
          simpa [halfProbability] using
            (Erdos76.FiniteNibble.sum_bernoulliMass_filter_mem
              (U := (univ : Finset V)) (p := halfProbability)
              (e := v) (Finset.mem_univ v))
    _ = (C.card : ℝ) / 2 := by simp; ring

/-- Toggling one vertex changes a fixed intersection cardinality by at most
one, and changes it by zero outside the test set. -/
lemma intersectionCount_hasBoundedDifferences (C : Finset V) :
    Erdos76.FiniteNibble.HasBoundedDifferences (univ : Finset V)
      (intersectionCount C) (fun v ↦ if v ∈ C then 1 else 0) := by
  intro v _ T hT
  have hvT : v ∉ T := by
    intro hvT
    exact (Finset.mem_erase.mp (hT hvT)).1 rfl
  by_cases hvC : v ∈ C
  · have hnot : v ∉ T ∩ C := fun h ↦ hvT (Finset.mem_inter.mp h).1
    simp [intersectionCount, hvC, hvT, hnot]
  · have heq : insert v T ∩ C = T ∩ C := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hwT, hwC⟩
        · exact (hvC hwC).elim
        · exact ⟨hwT, hwC⟩
      · rintro ⟨hwT, hwC⟩
        exact ⟨Or.inr hwT, hwC⟩
    simp [intersectionCount, hvC, heq]

private lemma sum_intersection_lipschitz_sq (C : Finset V) :
    (∑ v ∈ (univ : Finset V),
        (if v ∈ C then (1 : ℝ) else 0) ^ 2) = C.card := by
  simp

/-- Uniform two-sided Hoeffding bound for the intersection with an arbitrary
fixed test set.  The denominator is the test-set size, rather than the size
of the ambient vertex set. -/
theorem intersectionCount_twoSided (C : Finset V) {t : ℝ} (ht : 0 ≤ t) :
    ((((univ : Finset V).powerset.filter fun S ↦
        t ≤ |intersectionCount C S - (C.card : ℝ) / 2|).card : ℝ)) ≤
      2 * (2 : ℝ) ^ Fintype.card V * exp (-2 * t ^ 2 / C.card) := by
  let U : Finset V := univ
  let F : Finset V → ℝ := intersectionCount C
  let c : V → ℝ := fun v ↦ if v ∈ C then 1 else 0
  let A := U.powerset.filter fun S ↦
    Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F + t ≤ F S
  let B := U.powerset.filter fun S ↦
    F S ≤ Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F - t
  have hsub : U.powerset.filter (fun S ↦
      t ≤ |F S - Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F|) ⊆
        A ∪ B := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union, A, B] at hS ⊢
    rcases (le_abs.mp hS.2) with h | h
    · exact Or.inl ⟨hS.1, by linarith⟩
    · exact Or.inr ⟨hS.1, by linarith⟩
  have hcard : (U.powerset.filter fun S ↦
      t ≤ |F S - Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F|).card ≤
      A.card + B.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le A B)
  have hA := Concentration.countEvent_upperTail_le
    (U := U) (F := F) (c := c) (t := t)
    (intersectionCount_hasBoundedDifferences C) ht
  have hB := Concentration.countEvent_lowerTail_le
    (U := U) (F := F) (c := c) (t := t)
    (intersectionCount_hasBoundedDifferences C) ht
  change ((U.powerset.filter fun S ↦
      Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F + t ≤ F S).card : ℝ) ≤
      (2 : ℝ) ^ U.card * exp (-2 * t ^ 2 / (∑ e ∈ U, c e ^ 2)) at hA
  change ((U.powerset.filter fun S ↦
      F S ≤ Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F - t).card : ℝ) ≤
      (2 : ℝ) ^ U.card * exp (-2 * t ^ 2 / (∑ e ∈ U, c e ^ 2)) at hB
  have hcardR : ((U.powerset.filter fun S ↦
      t ≤ |F S - Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F|).card : ℝ) ≤
      (A.card : ℝ) + (B.card : ℝ) := by exact_mod_cast hcard
  have hmean :
      Erdos76.FiniteNibble.bernoulliExpectation U halfProbability F =
        (C.card : ℝ) / 2 := by
    simpa [U, F] using bernoulliExpectation_half_intersectionCount C
  have hvariance : (∑ v ∈ U, c v ^ 2) = (C.card : ℝ) := by
    simpa [U, c] using sum_intersection_lipschitz_sq C
  rw [hmean] at hcardR hA hB
  rw [hvariance] at hA hB
  change ((U.powerset.filter fun S ↦
      t ≤ |F S - (C.card : ℝ) / 2|).card : ℝ) ≤ _
  calc
    ((U.powerset.filter fun S ↦
        t ≤ |F S - (C.card : ℝ) / 2|).card : ℝ) ≤
        (A.card : ℝ) + (B.card : ℝ) := hcardR
    _ ≤ 2 * (2 : ℝ) ^ Fintype.card V *
        exp (-2 * t ^ 2 / C.card) := by
      dsimp [A, B, U, F] at hA hB ⊢
      rw [bernoulliExpectation_half_intersectionCount] at ⊢
      norm_num at hA hB ⊢
      nlinarith

/-- A simultaneous version for a finite family of test sets.  It is this
form that is used for all cells of a bounded weak-regularity profile and,
separately, for all vertex neighbourhoods. -/
theorem count_badIntersections_le [Nonempty V]
    (𝒞 : Finset (Finset V)) {t : ℝ} (ht : 0 < t) :
    let bad : Finset V → Finset (Finset V) := fun C ↦
      (univ : Finset V).powerset.filter fun S ↦
        t ≤ |intersectionCount C S - (C.card : ℝ) / 2|
    (((𝒞.biUnion bad).card : ℝ)) ≤
      (𝒞.card : ℝ) *
        (2 * (2 : ℝ) ^ Fintype.card V *
          exp (-2 * t ^ 2 / Fintype.card V)) := by
  dsimp only
  let bad : Finset V → Finset (Finset V) := fun C ↦
    (univ : Finset V).powerset.filter fun S ↦
      t ≤ |intersectionCount C S - (C.card : ℝ) / 2|
  have hcardNat : (𝒞.biUnion bad).card ≤ ∑ C ∈ 𝒞, (bad C).card :=
    Finset.card_biUnion_le
  have hcard : ((𝒞.biUnion bad).card : ℝ) ≤
      ∑ C ∈ 𝒞, ((bad C).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((𝒞.biUnion bad).card : ℝ) ≤
        ∑ C ∈ 𝒞, ((bad C).card : ℝ) := hcard
    _ ≤ ∑ _C ∈ 𝒞,
        2 * (2 : ℝ) ^ Fintype.card V *
          exp (-2 * t ^ 2 / Fintype.card V) := by
      apply Finset.sum_le_sum
      intro C hC
      by_cases hCempty : C = ∅
      · subst C
        simp only [neg_mul]
        positivity
      · have hCpos : (0 : ℝ) < C.card := by
          exact_mod_cast (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hCempty))
        have hCleNat : C.card ≤ Fintype.card V := Finset.card_le_univ C
        have hCle : (C.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hCleNat
        have hfrac :
            t ^ 2 / (Fintype.card V : ℝ) ≤ t ^ 2 / (C.card : ℝ) :=
          div_le_div_of_nonneg_left (sq_nonneg t) hCpos hCle
        have hexp :
            exp (-2 * t ^ 2 / (C.card : ℝ)) ≤
              exp (-2 * t ^ 2 / Fintype.card V) := by
          apply Real.exp_le_exp.mpr
          calc
            -2 * t ^ 2 / (C.card : ℝ) =
                -2 * (t ^ 2 / (C.card : ℝ)) := by ring
            _ ≤ -2 * (t ^ 2 / Fintype.card V) :=
              mul_le_mul_of_nonpos_left hfrac (by norm_num)
            _ = -2 * t ^ 2 / Fintype.card V := by ring
        have hsingle := intersectionCount_twoSided C ht.le
        change ((bad C).card : ℝ) ≤ _ at hsingle
        exact hsingle.trans
          (mul_le_mul_of_nonneg_left hexp (by positivity))
    _ = (𝒞.card : ℝ) *
        (2 * (2 : ℝ) ^ Fintype.card V *
          exp (-2 * t ^ 2 / Fintype.card V)) := by
      simp

section Graph

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Samples for which at least one ambient vertex has an atypical number of
selected neighbours.  Quantifying over ambient vertices (including vertices
outside the sample) is convenient and only strengthens the event needed for
the induced minimum-degree estimate. -/
def degreeBadSamples (t : ℝ) : Finset (Finset V) :=
  (univ : Finset V).biUnion fun v ↦
    (univ : Finset V).powerset.filter fun S ↦
      t ≤ |intersectionCount (G.neighborFinset v) S - (G.degree v : ℝ) / 2|

lemma degree_typical_of_not_mem {t : ℝ} {S : Finset V}
    (hS : S ∉ degreeBadSamples G t) (v : V) :
    |intersectionCount (G.neighborFinset v) S - (G.degree v : ℝ) / 2| < t := by
  by_contra h
  have hbad : t ≤
      |intersectionCount (G.neighborFinset v) S - (G.degree v : ℝ) / 2| :=
    le_of_not_gt h
  exact hS (Finset.mem_biUnion.mpr
    ⟨v, Finset.mem_univ v, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ S), hbad⟩⟩)

/-- A union bound over all vertex neighbourhoods. -/
theorem card_degreeBadSamples_le [Nonempty V] {t : ℝ} (ht : 0 < t) :
    ((degreeBadSamples G t).card : ℝ) ≤
      (Fintype.card V : ℝ) *
        (2 * (2 : ℝ) ^ Fintype.card V *
          exp (-2 * t ^ 2 / Fintype.card V)) := by
  let 𝒞 : Finset (Finset V) :=
    (univ : Finset V).image fun v ↦ G.neighborFinset v
  let bad : Finset V → Finset (Finset V) := fun C ↦
    (univ : Finset V).powerset.filter fun S ↦
      t ≤ |intersectionCount C S - (C.card : ℝ) / 2|
  have heq : degreeBadSamples G t = 𝒞.biUnion bad := by
    ext S
    simp only [degreeBadSamples, Finset.mem_biUnion, Finset.mem_univ,
      true_and, 𝒞, Finset.mem_image, bad, Finset.mem_filter]
    constructor
    · rintro ⟨v, hS⟩
      refine ⟨G.neighborFinset v, ⟨v, rfl⟩, ?_⟩
      simpa [G.card_neighborFinset_eq_degree] using hS
    · rintro ⟨C, ⟨v, rfl⟩, hS⟩
      exact ⟨v, by simpa [G.card_neighborFinset_eq_degree] using hS⟩
  have hfamily := count_badIntersections_le 𝒞 ht
  dsimp only at hfamily
  rw [heq]
  calc
    (((𝒞.biUnion bad).card : ℕ) : ℝ) ≤
        (𝒞.card : ℝ) *
          (2 * (2 : ℝ) ^ Fintype.card V *
            exp (-2 * t ^ 2 / Fintype.card V)) := by
      simpa [bad] using hfamily
    _ ≤ (Fintype.card V : ℝ) *
          (2 * (2 : ℝ) ^ Fintype.card V *
            exp (-2 * t ^ 2 / Fintype.card V)) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (Finset.card_image_le.trans (by simp : (univ : Finset V).card ≤ Fintype.card V))
      · positivity

end Graph

/-- Uniformly over all graphs on `2n` vertices, the proportion of samples
having a linear-sized degree deviation tends to zero. -/
theorem eventually_degreeBadSamples_density_lt
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (G : SimpleGraph (Fin (2 * n))) [DecidableRel G.Adj],
        ((degreeBadSamples G (δ * (2 * n : ℝ))).card : ℝ) /
            (2 : ℝ) ^ (2 * n) < ε := by
  have hc : 0 < 4 * δ ^ 2 := by positivity
  have hevent := Concentration.eventually_linear_mul_exp_neg_lt
    hc (show 0 < ε / 4 by positivity)
  filter_upwards [eventually_ge_atTop 1, hevent] with n hn hdec
  intro G _
  let : Nonempty (Fin (2 * n)) :=
    Fin.pos_iff_nonempty.mp (by omega)
  have ht : 0 < δ * (2 * n : ℝ) := mul_pos hδ (by positivity)
  have hcard := card_degreeBadSamples_le G ht
  have hcard' :
      ((degreeBadSamples G (δ * (2 * n : ℝ))).card : ℝ) ≤
        (2 * n : ℝ) *
          (2 * (2 : ℝ) ^ (2 * n) *
            exp (-2 * (δ * (2 * n : ℝ)) ^ 2 / (2 * n : ℝ))) := by
    simpa using hcard
  have hpow : 0 < (2 : ℝ) ^ (2 * n) := by positivity
  calc
    ((degreeBadSamples G (δ * (2 * n : ℝ))).card : ℝ) /
          (2 : ℝ) ^ (2 * n) ≤
        ((2 * n : ℝ) *
          (2 * (2 : ℝ) ^ (2 * n) *
            exp (-2 * (δ * (2 * n : ℝ)) ^ 2 / (2 * n : ℝ)))) /
          (2 : ℝ) ^ (2 * n) :=
      div_le_div_of_nonneg_right hcard' hpow.le
    _ = 4 * ((n : ℝ) * exp (-(4 * δ ^ 2) * n)) := by
      have hexponent :
          -2 * (δ * (2 * n : ℝ)) ^ 2 / (2 * n : ℝ) =
            -(4 * δ ^ 2) * n := by
        have hn0 : (n : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      rw [hexponent]
      field_simp
      norm_num
    _ < ε := by nlinarith

section Profiles

/-- The Boolean membership profile of a vertex with respect to all two
rectangle-sides occurring in a cut decomposition. -/
abbrev CutProfile (L : CutDecomposition V) := Fin L.length → Bool × Bool

def cutProfile (L : CutDecomposition V) (v : V) : CutProfile L := fun i ↦
  let q := L.get i
  (decide (v ∈ q.1), decide (v ∈ q.2.1))

/-- The cell consisting of vertices with a prescribed rectangle-membership
profile.  These cells refine every set occurring in the decomposition. -/
def profileCell (L : CutDecomposition V) (p : CutProfile L) : Finset V :=
  univ.filter fun v ↦ cutProfile L v = p

@[simp] lemma mem_profileCell_iff (L : CutDecomposition V)
    (p : CutProfile L) (v : V) :
    v ∈ profileCell L p ↔ cutProfile L v = p := by
  simp [profileCell]

/-- The profile cells partition the vertex set, expressed as the exact
cardinality identity needed for rounding arguments. -/
lemma sum_card_inter_profileCell (L : CutDecomposition V) (X : Finset V) :
    ∑ p : CutProfile L, (X ∩ profileCell L p).card = X.card := by
  have hpair : ((univ : Finset (CutProfile L)) : Set (CutProfile L)).PairwiseDisjoint
      (fun p ↦ X ∩ profileCell L p) := by
    intro p _hp q _hq hpq
    change Disjoint (X ∩ profileCell L p) (X ∩ profileCell L q)
    rw [Finset.disjoint_left]
    intro v hvp hvq
    have hp : cutProfile L v = p :=
      (mem_profileCell_iff L p v).mp (Finset.mem_inter.mp hvp).2
    have hq : cutProfile L v = q :=
      (mem_profileCell_iff L q v).mp (Finset.mem_inter.mp hvq).2
    exact hpq (hp.symm.trans hq)
  have hunion :
      (univ : Finset (CutProfile L)).biUnion
          (fun p ↦ X ∩ profileCell L p) = X := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_inter, mem_profileCell_iff]
    constructor
    · rintro ⟨p, hvX, _hp⟩
      exact hvX
    · intro hvX
      exact ⟨cutProfile L v, hvX, rfl⟩
  rw [← Finset.card_biUnion hpair, hunion]

def doubledCellTarget (L : CutDecomposition V) (X : Finset V)
    (p : CutProfile L) : ℕ :=
  min (profileCell L p).card (2 * (X ∩ profileCell L p).card)

noncomputable def doubledCellChunk (L : CutDecomposition V) (X : Finset V)
    (p : CutProfile L) : Finset V :=
  Classical.choose (Finset.exists_subset_card_eq
    (show doubledCellTarget L X p ≤ (profileCell L p).card by
      exact min_le_left _ _))

lemma doubledCellChunk_subset (L : CutDecomposition V) (X : Finset V)
    (p : CutProfile L) :
    doubledCellChunk L X p ⊆ profileCell L p :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (show doubledCellTarget L X p ≤ (profileCell L p).card by
      exact min_le_left _ _))).1

@[simp] lemma card_doubledCellChunk (L : CutDecomposition V) (X : Finset V)
    (p : CutProfile L) :
    (doubledCellChunk L X p).card = doubledCellTarget L X p :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (show doubledCellTarget L X p ≤ (profileCell L p).card by
      exact min_le_left _ _))).2

/-- The union of cellwise chunks whose sizes are the clipped doubles of the
profile counts of `X`. -/
noncomputable def doubledProfileCore (L : CutDecomposition V) (X : Finset V) :
    Finset V :=
  (univ : Finset (CutProfile L)).biUnion (doubledCellChunk L X)

lemma doubledCellChunks_pairwise (L : CutDecomposition V) (X : Finset V) :
    ((univ : Finset (CutProfile L)) : Set (CutProfile L)).PairwiseDisjoint
      (doubledCellChunk L X) := by
  intro p _hp q _hq hpq
  change Disjoint (doubledCellChunk L X p) (doubledCellChunk L X q)
  rw [Finset.disjoint_left]
  intro v hvp hvq
  have hvpcell := doubledCellChunk_subset L X p hvp
  have hvqcell := doubledCellChunk_subset L X q hvq
  have hp := (mem_profileCell_iff L p v).mp hvpcell
  have hq := (mem_profileCell_iff L q v).mp hvqcell
  exact hpq (hp.symm.trans hq)

@[simp] lemma card_doubledProfileCore (L : CutDecomposition V) (X : Finset V) :
    (doubledProfileCore L X).card =
      ∑ p : CutProfile L, doubledCellTarget L X p := by
  rw [doubledProfileCore, Finset.card_biUnion (doubledCellChunks_pairwise L X)]
  simp

lemma doubledProfileCore_inter_cell (L : CutDecomposition V) (X : Finset V)
    (p : CutProfile L) :
    doubledProfileCore L X ∩ profileCell L p = doubledCellChunk L X p := by
  ext v
  constructor
  · intro hv
    obtain ⟨q, _hq, hvchunk⟩ := Finset.mem_biUnion.mp
      (show v ∈ doubledProfileCore L X from (Finset.mem_inter.mp hv).1)
    have hvqcell := doubledCellChunk_subset L X q hvchunk
    have hvpcell := (Finset.mem_inter.mp hv).2
    have hqp : q = p := by
      have hq := (mem_profileCell_iff L q v).mp hvqcell
      have hp := (mem_profileCell_iff L p v).mp hvpcell
      exact hq.symm.trans hp
    simpa [hqp] using hvchunk
  · intro hv
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p, hv⟩,
        doubledCellChunk_subset L X p hv⟩

lemma card_doubledProfileCore_le_two_mul (L : CutDecomposition V)
    (X : Finset V) :
    (doubledProfileCore L X).card ≤ 2 * X.card := by
  rw [card_doubledProfileCore]
  calc
    ∑ p : CutProfile L, doubledCellTarget L X p ≤
        ∑ p : CutProfile L, 2 * (X ∩ profileCell L p).card := by
      apply Finset.sum_le_sum
      intro p _hp
      exact min_le_right _ _
    _ = 2 * X.card := by
      rw [← Finset.mul_sum]
      rw [sum_card_inter_profileCell]

/-- The clipped cellwise doubling loses at most `2t` vertices in each
profile cell when the sample is `t`-typical on that cell. -/
lemma doubledProfileCore_deficit_le
    (L : CutDecomposition V) {S X : Finset V} {t : ℝ}
    (hXS : X ⊆ S) (ht : 0 ≤ t)
    (htypical : ∀ p : CutProfile L,
      |intersectionCount (profileCell L p) S -
        ((profileCell L p).card : ℝ) / 2| < t) :
    2 * (X.card : ℝ) - (doubledProfileCore L X).card ≤
      2 * (Fintype.card (CutProfile L) : ℝ) * t := by
  have hcell (p : CutProfile L) :
      2 * ((X ∩ profileCell L p).card : ℝ) -
          (doubledCellTarget L X p : ℝ) ≤ 2 * t := by
    by_cases hle : 2 * (X ∩ profileCell L p).card ≤
        (profileCell L p).card
    · rw [doubledCellTarget, min_eq_right hle]
      norm_num
      positivity
    · have hgt : (profileCell L p).card <
          2 * (X ∩ profileCell L p).card := by omega
      rw [doubledCellTarget, min_eq_left hgt.le]
      have hsub : (X ∩ profileCell L p).card ≤
          (S ∩ profileCell L p).card := by
        exact Finset.card_le_card (Finset.inter_subset_inter hXS (fun _ h ↦ h))
      have hupper := (abs_lt.mp (htypical p)).2
      rw [intersectionCount] at hupper
      have hsubR : ((X ∩ profileCell L p).card : ℝ) ≤
          (S ∩ profileCell L p).card := by exact_mod_cast hsub
      linarith
  have hsumR :
      (∑ p : CutProfile L, ((X ∩ profileCell L p).card : ℝ)) =
        (X.card : ℝ) := by
    exact_mod_cast sum_card_inter_profileCell L X
  calc
    2 * (X.card : ℝ) - (doubledProfileCore L X).card =
        ∑ p : CutProfile L,
          (2 * ((X ∩ profileCell L p).card : ℝ) -
            (doubledCellTarget L X p : ℝ)) := by
      rw [card_doubledProfileCore]
      push_cast
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
        hsumR]
    _ ≤ ∑ _p : CutProfile L, 2 * t := by
      exact Finset.sum_le_sum fun p _ ↦ hcell p
    _ = 2 * (Fintype.card (CutProfile L) : ℝ) * t := by
      simp
      ring

noncomputable def profileL1Distance (L : CutDecomposition V)
    (A X : Finset V) : ℝ :=
  ∑ p : CutProfile L,
    |((A ∩ profileCell L p).card : ℝ) -
      2 * ((X ∩ profileCell L p).card : ℝ)|

/-- Extend the clipped doubled core to a prescribed cardinality.  The total
profile error is controlled by the size gap plus the cellwise concentration
loss. -/
theorem exists_profile_double
    (L : CutDecomposition V) {S X : Finset V} {t : ℝ} {m : ℕ}
    (hXS : X ⊆ S) (ht : 0 ≤ t)
    (hXm : 2 * X.card ≤ m) (hmV : m ≤ Fintype.card V)
    (htypical : ∀ p : CutProfile L,
      |intersectionCount (profileCell L p) S -
        ((profileCell L p).card : ℝ) / 2| < t) :
    ∃ A : Finset V, A.card = m ∧
      profileL1Distance L A X ≤
        (m : ℝ) - 2 * X.card +
          4 * (Fintype.card (CutProfile L) : ℝ) * t := by
  let D := doubledProfileCore L X
  have hDtwo : D.card ≤ 2 * X.card := by
    simpa [D] using card_doubledProfileCore_le_two_mul L X
  have hDm : D.card ≤ m := hDtwo.trans hXm
  obtain ⟨A, hDA, hAcard⟩ := Finset.exists_superset_card_eq hDm hmV
  have hdef := doubledProfileCore_deficit_le L hXS ht htypical
  have hpoint (p : CutProfile L) :
      |((A ∩ profileCell L p).card : ℝ) -
          2 * ((X ∩ profileCell L p).card : ℝ)| ≤
        ((A ∩ profileCell L p).card : ℝ) -
            ((D ∩ profileCell L p).card : ℝ) +
          (2 * ((X ∩ profileCell L p).card : ℝ) -
            ((D ∩ profileCell L p).card : ℝ)) := by
    have hDcellA : D ∩ profileCell L p ⊆ A ∩ profileCell L p :=
      Finset.inter_subset_inter hDA (fun _ h ↦ h)
    have hdpA : ((D ∩ profileCell L p).card : ℝ) ≤
        (A ∩ profileCell L p).card := by
      exact_mod_cast Finset.card_le_card hDcellA
    have hdpX : ((D ∩ profileCell L p).card : ℝ) ≤
        2 * ((X ∩ profileCell L p).card : ℝ) := by
      rw [show D ∩ profileCell L p = doubledCellChunk L X p by
        simpa [D] using doubledProfileCore_inter_cell L X p]
      rw [card_doubledCellChunk, doubledCellTarget]
      exact_mod_cast min_le_right (profileCell L p).card
        (2 * (X ∩ profileCell L p).card)
    rw [abs_le]
    constructor <;> linarith
  have hsumA :
      (∑ p : CutProfile L, ((A ∩ profileCell L p).card : ℝ)) =
        (A.card : ℝ) := by
    exact_mod_cast sum_card_inter_profileCell L A
  have hsumX :
      (∑ p : CutProfile L, ((X ∩ profileCell L p).card : ℝ)) =
        (X.card : ℝ) := by
    exact_mod_cast sum_card_inter_profileCell L X
  have hsumD :
      (∑ p : CutProfile L, ((D ∩ profileCell L p).card : ℝ)) =
        (D.card : ℝ) := by
    exact_mod_cast sum_card_inter_profileCell L D
  refine ⟨A, hAcard, ?_⟩
  calc
    profileL1Distance L A X ≤
        ∑ p : CutProfile L,
          (((A ∩ profileCell L p).card : ℝ) -
              ((D ∩ profileCell L p).card : ℝ) +
            (2 * ((X ∩ profileCell L p).card : ℝ) -
              ((D ∩ profileCell L p).card : ℝ))) := by
      exact Finset.sum_le_sum fun p _ ↦ hpoint p
    _ = (m : ℝ) + 2 * X.card - 2 * D.card := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
      rw [hsumA, hsumX, hsumD, hAcard]
      ring
    _ ≤ (m : ℝ) - 2 * X.card +
        4 * (Fintype.card (CutProfile L) : ℝ) * t := by
      dsimp [D] at hdef ⊢
      linarith

lemma mem_get_left_iff_of_mem_profileCell (L : CutDecomposition V)
    (i : Fin L.length) (p : CutProfile L) {v : V}
    (hv : v ∈ profileCell L p) :
    v ∈ (L.get i).1 ↔ (p i).1 = true := by
  have hp := congrFun ((mem_profileCell_iff L p v).mp hv) i
  have hp' : decide (v ∈ (L.get i).1) = (p i).1 := by
    simpa [cutProfile] using congrArg Prod.fst hp
  rw [← hp']
  simp

lemma mem_get_right_iff_of_mem_profileCell (L : CutDecomposition V)
    (i : Fin L.length) (p : CutProfile L) {v : V}
    (hv : v ∈ profileCell L p) :
    v ∈ (L.get i).2.1 ↔ (p i).2 = true := by
  have hp := congrFun ((mem_profileCell_iff L p v).mp hv) i
  have hp' : decide (v ∈ (L.get i).2.1) = (p i).2 := by
    simpa [cutProfile] using congrArg Prod.snd hp
  rw [← hp']
  simp

private lemma profileIntersections_pairwise (L : CutDecomposition V)
    (X : Finset V) (P : Finset (CutProfile L)) :
    (P : Set (CutProfile L)).PairwiseDisjoint
      (fun p ↦ X ∩ profileCell L p) := by
  intro p _hp q _hq hpq
  change Disjoint (X ∩ profileCell L p) (X ∩ profileCell L q)
  rw [Finset.disjoint_left]
  intro v hvp hvq
  have hp := (mem_profileCell_iff L p v).mp (Finset.mem_inter.mp hvp).2
  have hq := (mem_profileCell_iff L q v).mp (Finset.mem_inter.mp hvq).2
  exact hpq (hp.symm.trans hq)

lemma card_inter_get_left_eq_profile_sum (L : CutDecomposition V)
    (X : Finset V) (i : Fin L.length) :
    (X ∩ (L.get i).1).card =
      ∑ p ∈ (univ : Finset (CutProfile L)).filter (fun p ↦ (p i).1 = true),
        (X ∩ profileCell L p).card := by
  let P := (univ : Finset (CutProfile L)).filter (fun p ↦ (p i).1 = true)
  have hunion : P.biUnion (fun p ↦ X ∩ profileCell L p) =
      X ∩ (L.get i).1 := by
    ext v
    simp only [Finset.mem_biUnion, P, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_inter]
    constructor
    · rintro ⟨p, hptrue, hvX, hvcell⟩
      exact ⟨hvX, (mem_get_left_iff_of_mem_profileCell L i p hvcell).mpr hptrue⟩
    · rintro ⟨hvX, hvside⟩
      refine ⟨cutProfile L v, ?_, hvX, (mem_profileCell_iff L _ v).mpr rfl⟩
      exact (mem_get_left_iff_of_mem_profileCell L i (cutProfile L v)
        ((mem_profileCell_iff L _ v).mpr rfl)).mp hvside
  rw [← hunion, Finset.card_biUnion (profileIntersections_pairwise L X P)]

lemma card_inter_get_right_eq_profile_sum (L : CutDecomposition V)
    (X : Finset V) (i : Fin L.length) :
    (X ∩ (L.get i).2.1).card =
      ∑ p ∈ (univ : Finset (CutProfile L)).filter (fun p ↦ (p i).2 = true),
        (X ∩ profileCell L p).card := by
  let P := (univ : Finset (CutProfile L)).filter (fun p ↦ (p i).2 = true)
  have hunion : P.biUnion (fun p ↦ X ∩ profileCell L p) =
      X ∩ (L.get i).2.1 := by
    ext v
    simp only [Finset.mem_biUnion, P, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_inter]
    constructor
    · rintro ⟨p, hptrue, hvX, hvcell⟩
      exact ⟨hvX, (mem_get_right_iff_of_mem_profileCell L i p hvcell).mpr hptrue⟩
    · rintro ⟨hvX, hvside⟩
      refine ⟨cutProfile L v, ?_, hvX, (mem_profileCell_iff L _ v).mpr rfl⟩
      exact (mem_get_right_iff_of_mem_profileCell L i (cutProfile L v)
        ((mem_profileCell_iff L _ v).mpr rfl)).mp hvside
  rw [← hunion, Finset.card_biUnion (profileIntersections_pairwise L X P)]

/-- Every rectangle factor occurring in `L` changes by at most the total
profile `L¹` distance. -/
lemma rectangle_factors_close_of_profileL1
    (L : CutDecomposition V) (A X : Finset V) {q : Finset V × Finset V × ℝ}
    (hq : q ∈ L) :
    |((A ∩ q.1).card : ℝ) - 2 * ((X ∩ q.1).card : ℝ)| ≤
        profileL1Distance L A X ∧
      |((A ∩ q.2.1).card : ℝ) - 2 * ((X ∩ q.2.1).card : ℝ)| ≤
        profileL1Distance L A X := by
  obtain ⟨i, hi⟩ := (List.mem_iff_get.mp hq)
  subst q
  constructor
  · rw [card_inter_get_left_eq_profile_sum, card_inter_get_left_eq_profile_sum]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc
      |∑ p ∈ (univ : Finset (CutProfile L)).filter (fun p ↦ (p i).1 = true),
          (((A ∩ profileCell L p).card : ℝ) -
            2 * ((X ∩ profileCell L p).card : ℝ))| ≤
          ∑ p ∈ (univ : Finset (CutProfile L)).filter (fun p ↦ (p i).1 = true),
            |((A ∩ profileCell L p).card : ℝ) -
              2 * ((X ∩ profileCell L p).card : ℝ)| := abs_sum_le_sum_abs _ _
      _ ≤ profileL1Distance L A X := by
        unfold profileL1Distance
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _hp _hnot ↦ abs_nonneg
            (((A ∩ profileCell L p).card : ℝ) -
              2 * ((X ∩ profileCell L p).card : ℝ)))
  · rw [card_inter_get_right_eq_profile_sum, card_inter_get_right_eq_profile_sum]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc
      |∑ p ∈ (univ : Finset (CutProfile L)).filter (fun p ↦ (p i).2 = true),
          (((A ∩ profileCell L p).card : ℝ) -
            2 * ((X ∩ profileCell L p).card : ℝ))| ≤
          ∑ p ∈ (univ : Finset (CutProfile L)).filter (fun p ↦ (p i).2 = true),
            |((A ∩ profileCell L p).card : ℝ) -
              2 * ((X ∩ profileCell L p).card : ℝ)| := abs_sum_le_sum_abs _ _
      _ ≤ profileL1Distance L A X := by
        unfold profileL1Distance
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun p _hp _hnot ↦ abs_nonneg
            (((A ∩ profileCell L p).card : ℝ) -
              2 * ((X ∩ profileCell L p).card : ℝ)))

lemma cutProfileValue_halves (L : CutDecomposition V) (A B : Finset V) :
    cutProfileValue L
        (fun q ↦ ((A ∩ q.1).card : ℝ) / 2)
        (fun q ↦ ((B ∩ q.2.1).card : ℝ) / 2) =
      (1 / 4 : ℝ) * matrixCutSum (cutDecompositionMatrix L) A B := by
  rw [matrixCutSum_cutDecompositionMatrix_eq_profile]
  induction L with
  | nil => simp [cutProfileValue]
  | cons q L ih =>
      simp only [cutProfileValue, List.map_cons, List.sum_cons]
      have ih' :
          (List.map
              (fun q ↦ q.2.2 * (((A ∩ q.1).card : ℝ) / 2) *
                (((B ∩ q.2.1).card : ℝ) / 2)) L).sum =
            (1 / 4 : ℝ) *
              (List.map
                (fun q ↦ q.2.2 * ((A ∩ q.1).card : ℝ) *
                  ((B ∩ q.2.1).card : ℝ)) L).sum := by
        simpa only [cutProfileValue] using ih
      rw [ih']
      ring

/-- Bilinear cut values transfer from two ambient profile doubles to their
sampled sets. -/
lemma cutValue_sampled_sub_quarter_ambient_le
    (L : CutDecomposition V) (A B X Y : Finset V)
    (C N E : ℝ) (hC : cutCoefficientMass L ≤ C)
    (hN : (Fintype.card V : ℝ) ≤ N) (hE : 0 ≤ E)
    (hAX : profileL1Distance L A X ≤ E)
    (hBY : profileL1Distance L B Y ≤ E) :
    |matrixCutSum (cutDecompositionMatrix L) X Y -
        (1 / 4 : ℝ) * matrixCutSum (cutDecompositionMatrix L) A B| ≤
      C * (N * E) := by
  let a : (Finset V × Finset V × ℝ) → ℝ :=
    fun q ↦ ((A ∩ q.1).card : ℝ) / 2
  let b : (Finset V × Finset V × ℝ) → ℝ :=
    fun q ↦ ((B ∩ q.2.1).card : ℝ) / 2
  have hcardNonneg : (0 : ℝ) ≤ Fintype.card V := by positivity
  have hVN : 0 ≤ N := hcardNonneg.trans hN
  have hδ : 0 ≤ E / 2 := div_nonneg hE (by norm_num)
  have hXbound : ∀ q ∈ L, |((X ∩ q.1).card : ℝ)| ≤ N := by
    intro q hq
    rw [abs_of_nonneg (by positivity)]
    have hc : ((X ∩ q.1).card : ℝ) ≤ Fintype.card V := by
      exact_mod_cast Finset.card_le_univ (X ∩ q.1)
    exact hc.trans hN
  have hBbound : ∀ q ∈ L, |b q| ≤ N := by
    intro q hq
    rw [abs_of_nonneg (by positivity)]
    have hc : ((B ∩ q.2.1).card : ℝ) ≤ Fintype.card V := by
      exact_mod_cast Finset.card_le_univ (B ∩ q.2.1)
    dsimp [b]
    nlinarith
  have hXclose : ∀ q ∈ L,
      |((X ∩ q.1).card : ℝ) - a q| ≤ E / 2 := by
    intro q hq
    have hfactor := (rectangle_factors_close_of_profileL1 L A X hq).1
    have hfactorE := hfactor.trans hAX
    dsimp [a]
    calc
      |((X ∩ q.1).card : ℝ) - ((A ∩ q.1).card : ℝ) / 2| =
          |((A ∩ q.1).card : ℝ) - 2 * ((X ∩ q.1).card : ℝ)| / 2 := by
        have heq :
            ((X ∩ q.1).card : ℝ) - ((A ∩ q.1).card : ℝ) / 2 =
              -(((A ∩ q.1).card : ℝ) - 2 * ((X ∩ q.1).card : ℝ)) / 2 := by
          ring
        rw [heq, abs_div, abs_neg]
        norm_num
      _ ≤ E / 2 := div_le_div_of_nonneg_right hfactorE (by norm_num)
  have hYclose : ∀ q ∈ L,
      |((Y ∩ q.2.1).card : ℝ) - b q| ≤ E / 2 := by
    intro q hq
    have hfactor := (rectangle_factors_close_of_profileL1 L B Y hq).2
    have hfactorE := hfactor.trans hBY
    dsimp [b]
    calc
      |((Y ∩ q.2.1).card : ℝ) - ((B ∩ q.2.1).card : ℝ) / 2| =
          |((B ∩ q.2.1).card : ℝ) - 2 * ((Y ∩ q.2.1).card : ℝ)| / 2 := by
        have heq :
            ((Y ∩ q.2.1).card : ℝ) - ((B ∩ q.2.1).card : ℝ) / 2 =
              -(((B ∩ q.2.1).card : ℝ) - 2 * ((Y ∩ q.2.1).card : ℝ)) / 2 := by
          ring
        rw [heq, abs_div, abs_neg]
        norm_num
      _ ≤ E / 2 := div_le_div_of_nonneg_right hfactorE (by norm_num)
  have htransfer := profile_density_transfer_estimate L X Y a b C N (E / 2)
    hC hVN hδ hXbound hBbound hXclose hYclose
  rw [cutProfileValue_halves] at htransfer
  have hscale : 2 * N * (E / 2) = N * E := by ring
  simpa only [hscale] using htransfer

def profileCellFamily (L : CutDecomposition V) : Finset (Finset V) :=
  (univ : Finset (CutProfile L)).image (profileCell L)

lemma card_profileCellFamily_le (L : CutDecomposition V) :
    (profileCellFamily L).card ≤ 4 ^ L.length := by
  calc
    (profileCellFamily L).card ≤
        (univ : Finset (CutProfile L)).card := Finset.card_image_le
    _ = Fintype.card (CutProfile L) := Finset.card_univ
    _ = 4 ^ L.length := by
      simp [CutProfile]

/-- Samples on which at least one weak-regularity profile cell fails its
prescribed absolute concentration window. -/
def profileBadSamples (L : CutDecomposition V) (t : ℝ) :
    Finset (Finset V) :=
  (profileCellFamily L).biUnion fun C ↦
    (univ : Finset V).powerset.filter fun S ↦
      t ≤ |intersectionCount C S - (C.card : ℝ) / 2|

lemma profile_typical_of_not_mem (L : CutDecomposition V)
    {t : ℝ} {S : Finset V} (hS : S ∉ profileBadSamples L t)
    (p : CutProfile L) :
    |intersectionCount (profileCell L p) S -
        ((profileCell L p).card : ℝ) / 2| < t := by
  have hcell : profileCell L p ∈ profileCellFamily L := by
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩
  by_contra h
  have hbad : t ≤
      |intersectionCount (profileCell L p) S -
        ((profileCell L p).card : ℝ) / 2| := le_of_not_gt h
  exact hS (Finset.mem_biUnion.mpr
    ⟨profileCell L p, hcell, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ S), hbad⟩⟩)

theorem card_profileBadSamples_le [Nonempty V]
    (L : CutDecomposition V) {t : ℝ} (ht : 0 < t) :
    ((profileBadSamples L t).card : ℝ) ≤
      (4 ^ L.length : ℕ) *
        (2 * (2 : ℝ) ^ Fintype.card V *
          exp (-2 * t ^ 2 / Fintype.card V)) := by
  have hfamily := count_badIntersections_le (profileCellFamily L) ht
  dsimp only at hfamily
  calc
    ((profileBadSamples L t).card : ℝ) ≤
        ((profileCellFamily L).card : ℝ) *
          (2 * (2 : ℝ) ^ Fintype.card V *
            exp (-2 * t ^ 2 / Fintype.card V)) := by
      simpa [profileBadSamples] using hfamily
    _ ≤ (4 ^ L.length : ℕ) *
          (2 * (2 : ℝ) ^ Fintype.card V *
            exp (-2 * t ^ 2 / Fintype.card V)) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_profileCellFamily_le L
      · positivity

/-- Uniform vanishing of the bad profile-cell event for every decomposition
with a prescribed (constant) number of rectangles. -/
theorem eventually_profileBadSamples_density_lt
    (k : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∀ L : CutDecomposition (Fin (2 * n)), L.length ≤ k →
        ((profileBadSamples L (δ * (2 * n : ℝ))).card : ℝ) /
            (2 : ℝ) ^ (2 * n) < ε := by
  have hc : 0 < 4 * δ ^ 2 := by positivity
  have hdenom : 0 < ε / (2 * (4 ^ k : ℕ)) := by positivity
  have hevent := Concentration.eventually_linear_mul_exp_neg_lt hc hdenom
  filter_upwards [eventually_ge_atTop 1, hevent] with n hn hdec
  intro L hL
  let : Nonempty (Fin (2 * n)) :=
    Fin.pos_iff_nonempty.mp (by omega)
  have ht : 0 < δ * (2 * n : ℝ) := mul_pos hδ (by positivity)
  have hcard := card_profileBadSamples_le L ht
  have hcard' :
      ((profileBadSamples L (δ * (2 * n : ℝ))).card : ℝ) ≤
        (4 ^ L.length : ℕ) *
          (2 * (2 : ℝ) ^ (2 * n) *
            exp (-2 * (δ * (2 * n : ℝ)) ^ 2 / (2 * n : ℝ))) := by
    simpa using hcard
  have hpow : 0 < (2 : ℝ) ^ (2 * n) := by positivity
  have hexponent :
      -2 * (δ * (2 * n : ℝ)) ^ 2 / (2 * n : ℝ) =
        -(4 * δ ^ 2) * n := by
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hpowFour : (4 ^ L.length : ℕ) ≤ 4 ^ k :=
    Nat.pow_le_pow_right (by omega) hL
  calc
    ((profileBadSamples L (δ * (2 * n : ℝ))).card : ℝ) /
          (2 : ℝ) ^ (2 * n) ≤
        ((4 ^ L.length : ℕ) *
          (2 * (2 : ℝ) ^ (2 * n) *
            exp (-2 * (δ * (2 * n : ℝ)) ^ 2 / (2 * n : ℝ)))) /
          (2 : ℝ) ^ (2 * n) :=
      div_le_div_of_nonneg_right hcard' hpow.le
    _ = 2 * (4 ^ L.length : ℕ) * exp (-(4 * δ ^ 2) * n) := by
      rw [hexponent]
      field_simp
    _ ≤ 2 * (4 ^ k : ℕ) *
        ((n : ℝ) * exp (-(4 * δ ^ 2) * n)) := by
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hexpNonneg : 0 ≤ exp (-(4 * δ ^ 2) * n) := Real.exp_nonneg _
      have hpowFourR : ((4 ^ L.length : ℕ) : ℝ) ≤ (4 ^ k : ℕ) := by
        exact_mod_cast hpowFour
      have hfirst :
          2 * ((4 ^ L.length : ℕ) : ℝ) *
              exp (-(4 * δ ^ 2) * n) ≤
            2 * ((4 ^ k : ℕ) : ℝ) *
              exp (-(4 * δ ^ 2) * n) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpowFourR (by norm_num)) hexpNonneg
      have hsecond :
          exp (-(4 * δ ^ 2) * n) ≤
            (n : ℝ) * exp (-(4 * δ ^ 2) * n) := by
        nlinarith
      exact hfirst.trans
        (mul_le_mul_of_nonneg_left hsecond (by positivity))
    _ < ε := by
      have hfactor : 0 < (2 * (4 ^ k : ℕ) : ℝ) := by positivity
      calc
        2 * (4 ^ k : ℕ) *
            ((n : ℝ) * exp (-(4 * δ ^ 2) * n)) <
            2 * (4 ^ k : ℕ) * (ε / (2 * (4 ^ k : ℕ))) :=
          mul_lt_mul_of_pos_left hdec hfactor
        _ = ε := by field_simp

/-! ## Deterministic transfer through a cut decomposition -/

lemma matrixCutSum_graphAdjacencyMatrix_eq_edgeCount
    (G : SimpleGraph V) (A B : Finset V) :
    matrixCutSum (graphAdjacencyMatrix G) A B =
      Trichotomy.edgeCount G A B := by
  rw [matrixCutSum_graphAdjacencyMatrix,
    Trichotomy.edgeCount_eq_sum_degreeInto]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Trichotomy.degreeInto_eq_card_filter]
  exact Finset.sum_boole (R := ℝ) (fun w ↦ G.Adj v w) B

/-- Controlling every profile cell also controls the total sample size. -/
lemma sampleCard_close_of_profile_typical
    (L : CutDecomposition V) (S : Finset V) (t : ℝ)
    (htypical : ∀ p : CutProfile L,
      |intersectionCount (profileCell L p) S -
        ((profileCell L p).card : ℝ) / 2| < t) :
    |(S.card : ℝ) - (Fintype.card V : ℝ) / 2| <
      (Fintype.card (CutProfile L) : ℝ) * t := by
  have hsumS :
      (∑ p : CutProfile L, ((S ∩ profileCell L p).card : ℝ)) =
        (S.card : ℝ) := by
    exact_mod_cast sum_card_inter_profileCell L S
  have hsumV :
      (∑ p : CutProfile L, ((profileCell L p).card : ℝ)) =
        (Fintype.card V : ℝ) := by
    have h := sum_card_inter_profileCell L (univ : Finset V)
    simp only [Finset.univ_inter] at h
    exact_mod_cast h
  calc
    |(S.card : ℝ) - (Fintype.card V : ℝ) / 2| =
        |∑ p : CutProfile L,
          (((S ∩ profileCell L p).card : ℝ) -
            ((profileCell L p).card : ℝ) / 2)| := by
      rw [Finset.sum_sub_distrib, hsumS, ← Finset.sum_div, hsumV]
    _ ≤ ∑ p : CutProfile L,
          |((S ∩ profileCell L p).card : ℝ) -
            ((profileCell L p).card : ℝ) / 2| :=
      abs_sum_le_sum_abs _ _
    _ < ∑ _p : CutProfile L, t := by
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro p hp
      simpa [intersectionCount, Finset.inter_comm] using htypical p
    _ = (Fintype.card (CutProfile L) : ℝ) * t := by simp

/-- The quantitative core of bi-density inheritance.  If `A,B` are
ambient half-sets whose cut profiles are twice those of `X,Y`, then weak cut
regularity transfers one quarter of the ambient edge lower bound to `X,Y`.
The `5/4` is the sum of the sampled residual error and one quarter of the
ambient residual error. -/
lemma edgeCount_sampled_lower_of_profile_doubles
    (G : SimpleGraph V)
    (L : CutDecomposition V) (A B X Y : Finset V)
    (ambientDensity regularityError coefficientBound profileError : ℝ)
    (hRegular : IsCutRegular regularityError
      (graphAdjacencyMatrix G - cutDecompositionMatrix L))
    (hMass : cutCoefficientMass L ≤ coefficientBound)
    (hProfileError : 0 ≤ profileError)
    (hAX : profileL1Distance L A X ≤ profileError)
    (hBY : profileL1Distance L B Y ≤ profileError)
    (hAmbient : ambientDensity * (Fintype.card V : ℝ) ^ 2 ≤
      Trichotomy.edgeCount G A B) :
    (ambientDensity / 4 - 5 * regularityError / 4) *
          (Fintype.card V : ℝ) ^ 2 -
        coefficientBound * ((Fintype.card V : ℝ) * profileError) ≤
      Trichotomy.edgeCount G X Y := by
  have hResidualXY := hRegular X Y
  have hResidualAB := hRegular A B
  rw [matrixCutSum_sub,
    matrixCutSum_graphAdjacencyMatrix_eq_edgeCount] at hResidualXY hResidualAB
  have hTransfer := cutValue_sampled_sub_quarter_ambient_le
    L A B X Y coefficientBound (Fintype.card V : ℝ) profileError
    hMass (le_rfl) hProfileError hAX hBY
  have hXYlower :
      matrixCutSum (cutDecompositionMatrix L) X Y -
          regularityError * (Fintype.card V : ℝ) ^ 2 ≤
        Trichotomy.edgeCount G X Y := by
    have h := (abs_le.mp hResidualXY).1
    linarith
  have hABlower :
      Trichotomy.edgeCount G A B -
          regularityError * (Fintype.card V : ℝ) ^ 2 ≤
        matrixCutSum (cutDecompositionMatrix L) A B := by
    have h := (abs_le.mp hResidualAB).2
    linarith
  have hCutLower :
      (1 / 4 : ℝ) * matrixCutSum (cutDecompositionMatrix L) A B -
          coefficientBound * ((Fintype.card V : ℝ) * profileError) ≤
        matrixCutSum (cutDecompositionMatrix L) X Y := by
    have h := (abs_le.mp hTransfer).1
    linarith
  linarith

/-- Uniform finite Boolean-cube inheritance of bi-density.  The hypotheses
are the deterministic properties of one sample: every weak-regularity cell
is typical, and the displayed numerical margin is larger than the desired
edge budget. -/
lemma inherited_biDenseOn_of_profile_typical
    (G : SimpleGraph V)
    (L : CutDecomposition V) (S : Finset V)
    (n q b : ℕ) (ambientDensity regularityError coefficientBound t : ℝ)
    (hCard : Fintype.card V = 2 * n)
    (hBiDense : Trichotomy.BiDense G n ambientDensity)
    (hRegular : IsCutRegular regularityError
      (graphAdjacencyMatrix G - cutDecompositionMatrix L))
    (hMass : cutCoefficientMass L ≤ coefficientBound)
    (ht : 0 ≤ t) (hq : 2 * q ≤ n)
    (hTypical : ∀ p : CutProfile L,
      |intersectionCount (profileCell L p) S -
        ((profileCell L p).card : ℝ) / 2| < t)
    (hMargin : (b : ℝ) <
      (ambientDensity / 4 - 5 * regularityError / 4) *
          (Fintype.card V : ℝ) ^ 2 -
        coefficientBound * ((Fintype.card V : ℝ) *
          ((n : ℝ) - 2 * q +
            4 * (Fintype.card (CutProfile L) : ℝ) * t))) :
    ∀ X Y : Finset V,
      X ⊆ S → Y ⊆ S → q ≤ X.card → q ≤ Y.card →
        b < (G.interedges X Y).card := by
  have hnV : n ≤ Fintype.card V := by omega
  have hExact : ∀ X Y : Finset V,
      X ⊆ S → Y ⊆ S → X.card = q → Y.card = q →
        (b : ℝ) < Trichotomy.edgeCount G X Y := by
    intro X Y hXS hYS hXcard hYcard
    have htwoX : 2 * X.card ≤ n := by omega
    have htwoY : 2 * Y.card ≤ n := by omega
    obtain ⟨A, hAcard, hAX⟩ := exists_profile_double L hXS ht htwoX hnV hTypical
    obtain ⟨B, hBcard, hBY⟩ := exists_profile_double L hYS ht htwoY hnV hTypical
    let E : ℝ := (n : ℝ) - 2 * q +
      4 * (Fintype.card (CutProfile L) : ℝ) * t
    have hE : 0 ≤ E := by
      dsimp [E]
      have hqn : (2 * q : ℝ) ≤ n := by exact_mod_cast hq
      positivity
    have hAX' : profileL1Distance L A X ≤ E := by
      simpa [E, hXcard] using hAX
    have hBY' : profileL1Distance L B Y ≤ E := by
      simpa [E, hYcard] using hBY
    have hAmbient :
        ambientDensity * (Fintype.card V : ℝ) ^ 2 ≤
          Trichotomy.edgeCount G A B := by
      rw [hCard]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        hBiDense A B hAcard hBcard
    have hLower := edgeCount_sampled_lower_of_profile_doubles
      G L A B X Y ambientDensity regularityError coefficientBound E
      hRegular hMass hE hAX' hBY' hAmbient
    exact hMargin.trans_le (by simpa [E] using hLower)
  intro X Y hXS hYS hXq hYq
  obtain ⟨X', hX'X, hX'card⟩ := Finset.exists_subset_card_eq hXq
  obtain ⟨Y', hY'Y, hY'card⟩ := Finset.exists_subset_card_eq hYq
  have hSmall := hExact X' Y'
    (hX'X.trans hXS) (hY'Y.trans hYS) hX'card hY'card
  have hMono := Trichotomy.edgeCount_mono G hX'X hY'Y
  have hReal : (b : ℝ) < Trichotomy.edgeCount G X Y := hSmall.trans_le hMono
  rw [Trichotomy.edgeCount] at hReal
  exact_mod_cast hReal

end Profiles

/-! ## Passing ambient finite sets to an induced graph -/

def ambientFinset (S : Finset V) (A : Finset (S : Set V)) : Finset V :=
  A.map (Function.Embedding.subtype _)

@[simp] lemma card_ambientFinset (S : Finset V) (A : Finset (S : Set V)) :
    (ambientFinset S A).card = A.card := by
  simp [ambientFinset]

lemma ambientFinset_subset (S : Finset V) (A : Finset (S : Set V)) :
    ambientFinset S A ⊆ S := by
  intro v hv
  rw [ambientFinset] at hv
  obtain ⟨a, ha, hav⟩ := Finset.mem_map.mp hv
  rw [← hav]
  exact a.property

lemma card_interedges_induce_eq_ambient
    (G : SimpleGraph V) (S : Finset V) (A B : Finset (S : Set V))
    (dG : DecidableRel G.Adj)
    (dH : DecidableRel (G.induce (S : Set V)).Adj) :
    (@SimpleGraph.interedges (S : Set V) (G.induce (S : Set V)) dH A B).card =
      (@SimpleGraph.interedges V G dG
        (ambientFinset S A) (ambientFinset S B)).card := by
  let e : (S : Set V) ↪ V := Function.Embedding.subtype _
  have hmap :
      (@SimpleGraph.interedges (S : Set V) (G.induce (S : Set V)) dH A B).map
          (e.prodMap e) =
        @SimpleGraph.interedges V G dG
          (ambientFinset S A) (ambientFinset S B) := by
    ext x
    simp [SimpleGraph.mem_interedges_iff, ambientFinset, e]
    aesop
  rw [← hmap, Finset.card_map]

/-- An ambient edge lower bound for all large subsets of `S` is exactly the
`BiDenseAbove` condition needed to eliminate the two exceptional KSS
outcomes in the induced graph. -/
lemma biDenseAbove_induce_of_ambient
    (G : SimpleGraph V) (S : Finset V) (k b : ℕ)
    (hDense : ∀ X Y : Finset V,
      X ⊆ S → Y ⊆ S → k ≤ X.card → k ≤ Y.card →
        b < (G.interedges X Y).card) :
    DiracStability.BiDenseAbove (G.induce (S : Set V)) k b := by
  intro A B hA hB
  have hd := hDense (ambientFinset S A) (ambientFinset S B)
    (ambientFinset_subset S A) (ambientFinset_subset S B)
    (by simpa using hA) (by simpa using hB)
  apply lt_of_lt_of_eq hd
  symm
  apply card_interedges_induce_eq_ambient

/-! ## Induced minimum degree from neighborhood concentration -/

lemma degree_induce_eq_intersectionCount
    (G : SimpleGraph V) (S : Finset V) (v : (S : Set V)) :
    ((G.induce (S : Set V)).degree v : ℝ) =
      intersectionCount (G.neighborFinset v.1) S := by
  rw [EdgeCounting.degree_induce_eq_degreeInto]
  simp [EdgeCounting.degreeInto, intersectionCount, Finset.inter_comm]

/-- A typical neighborhood count and an upper bound on the sample order give
the real minimum-degree hypothesis in the fixed-loss KSS theorem. -/
lemma induced_minDegree_of_degree_typical
    (G : SimpleGraph V) (S : Finset V) (n : ℕ) (rho t sampleError : ℝ)
    (hRegular : G.IsRegularOfDegree (n + 1))
    (hRhoNonneg : 0 ≤ rho) (hRhoHalf : rho ≤ 1 / 2)
    (hSampleUpper : (S.card : ℝ) ≤ (n : ℝ) + sampleError)
    (hTypical : ∀ v : V,
      |intersectionCount (G.neighborFinset v) S - (G.degree v : ℝ) / 2| < t)
    (hNumerical : t + (1 / 2 - rho) * sampleError ≤
      rho * n + 1 / 2) :
    ∀ v : (S : Set V),
      (1 / 2 - rho) * (Fintype.card (S : Set V) : ℝ) ≤
        (G.induce (S : Set V)).degree v := by
  intro v
  have hdeg : G.degree v.1 = n + 1 := hRegular v.1
  have hlow := (abs_lt.mp (hTypical v.1)).1
  have hcardS : Fintype.card (S : Set V) = S.card := Fintype.card_coe S
  rw [hcardS, degree_induce_eq_intersectionCount]
  have hfactor : 0 ≤ (1 / 2 : ℝ) - rho := by linarith
  have hsampleMul :
      (1 / 2 - rho) * (S.card : ℝ) ≤
        (1 / 2 - rho) * ((n : ℝ) + sampleError) :=
    mul_le_mul_of_nonneg_left hSampleUpper hfactor
  rw [hdeg] at hlow
  push_cast at hlow
  linarith

/-- The floor, degree, and density-margin arithmetic common to every good
sample.  Keeping this calculation separate makes the final asymptotic proof
depend only on the two concentration bounds. -/
lemma good_sample_numerics
    (e C Q rho delta : ℝ) (n : ℕ) (S : Finset (Fin (2 * n)))
    (profileCount : ℝ)
    (he : 0 < e) (heOne : e ≤ 1) (hC : 0 ≤ C)
    (hQ : 1 ≤ Q) (hProfileCount : 0 ≤ profileCount)
    (hProfileCountQ : profileCount ≤ Q)
    (hRho : 0 < rho) (hRhoHalf : rho ≤ 1 / 2)
    (hDelta : 0 ≤ delta)
    (hQdelta : Q * delta ≤ rho / 100)
    (hCrho : C * rho ≤ e / 1000)
    (hnLarge : 100 * (C + 1) < e * n)
    (hSsubset : S ⊆ (univ : Finset (Fin (2 * n))))
    (hSize : |(S.card : ℝ) - (n : ℝ)| <
      profileCount * (delta * (2 * n : ℝ))) :
    21 ≤ S.card ∧
    2 * DiracStability.exceptionalSize rho S.card ≤ n ∧
    delta * (2 * n : ℝ) + (1 / 2 - rho) *
        (profileCount * (delta * (2 * n : ℝ))) ≤
      rho * n + 1 / 2 ∧
    (S.card : ℝ) <
      (e / 4 - 5 * (e / 10) / 4) * (2 * n : ℝ) ^ 2 -
        C * ((2 * n : ℝ) *
          ((n : ℝ) -
            2 * DiracStability.exceptionalSize rho S.card +
            4 * profileCount * (delta * (2 * n : ℝ)))) := by
  let nr : ℝ := n
  let s : ℝ := S.card
  let err : ℝ := profileCount * (delta * (2 * n : ℝ))
  let q : ℕ := DiracStability.exceptionalSize rho S.card
  have hnr : 0 ≤ nr := by positivity
  have hs : 0 ≤ s := by positivity
  have hfactor : 0 ≤ (1 / 2 : ℝ) - rho := by linarith
  have hfactorOne : (1 / 2 : ℝ) - rho ≤ 1 := by linarith
  have hfactorTwo : 0 ≤ (1 : ℝ) - 2 * rho := by linarith
  have hfactorTwoOne : (1 : ℝ) - 2 * rho ≤ 1 := by linarith
  have hProfileDelta : profileCount * delta ≤ Q * delta :=
    mul_le_mul_of_nonneg_right hProfileCountQ hDelta
  have hProfileDelta' : profileCount * delta ≤ rho / 100 :=
    hProfileDelta.trans hQdelta
  have hDeltaRho : delta ≤ rho / 100 := by
    have := mul_le_mul_of_nonneg_right hQ hDelta
    nlinarith
  have herr : err ≤ rho * nr / 50 := by
    have hmul := mul_le_mul_of_nonneg_right hProfileDelta'
      (show 0 ≤ 2 * nr by positivity)
    dsimp [err, nr] at hmul ⊢
    push_cast at hmul ⊢
    nlinarith
  have herr0 : 0 ≤ err := by
    dsimp [err]
    positivity
  have hsizeLower : nr - err < s := by
    dsimp [nr, s, err]
    have h := (abs_lt.mp hSize).1
    linarith
  have hsizeUpper : s ≤ nr + err := by
    dsimp [nr, s, err]
    have h := (abs_lt.mp hSize).2
    linarith
  have hnHundred : (100 : ℝ) < nr := by
    have hen : e * nr ≤ 1 * nr := mul_le_mul_of_nonneg_right heOne hnr
    dsimp [nr] at hnLarge ⊢
    have hCplus : 1 ≤ C + 1 := by linarith
    nlinarith
  have hsTwentyOne : (21 : ℝ) < s := by
    have hrhonr : rho * nr ≤ nr / 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hRhoHalf hnr]
    nlinarith
  have hCard21 : 21 ≤ S.card := by
    dsimp [s] at hsTwentyOne
    exact_mod_cast hsTwentyOne.le
  have hx0 : 0 ≤ (1 / 2 - rho) * s := mul_nonneg hfactor hs
  have hqFloor : (q : ℝ) ≤ (1 / 2 - rho) * s := by
    dsimp [q, DiracStability.exceptionalSize]
    exact Nat.floor_le hx0
  have hfactorSize :
      (1 / 2 - rho) * s ≤ (1 / 2 - rho) * (nr + err) :=
    mul_le_mul_of_nonneg_left hsizeUpper hfactor
  have hfactorErr : (1 - 2 * rho) * err ≤ err :=
    by nlinarith [mul_le_mul_of_nonneg_right hfactorTwoOne herr0]
  have hTwoQReal : (2 * q : ℝ) ≤ nr := by
    push_cast
    have hq2 : 2 * (q : ℝ) ≤ 2 * ((1 / 2 - rho) * s) := by linarith
    nlinarith only [hq2, hfactorSize, hfactorErr, herr, hRho.le, hnr]
  have hTwoQ : 2 * q ≤ n := by
    dsimp [nr] at hTwoQReal
    exact_mod_cast hTwoQReal
  have htBound : delta * (2 * n : ℝ) ≤ rho * nr / 50 := by
    have hmul := mul_le_mul_of_nonneg_right hDeltaRho
      (show 0 ≤ 2 * nr by positivity)
    dsimp [nr] at hmul ⊢
    push_cast at hmul ⊢
    nlinarith
  have hfactorErrHalf : (1 / 2 - rho) * err ≤ err :=
    by nlinarith [mul_le_mul_of_nonneg_right hfactorOne herr0]
  have hDegreeNumerical :
      delta * (2 * n : ℝ) + (1 / 2 - rho) * err ≤
        rho * nr + 1 / 2 := by
    have hrhonr0 : 0 ≤ rho * nr := mul_nonneg hRho.le hnr
    nlinarith
  have hqLower : (1 / 2 - rho) * s < (q : ℝ) + 1 := by
    dsimp [q, DiracStability.exceptionalSize]
    exact Nat.lt_floor_add_one _
  have htwoXLower :
      (1 - 2 * rho) * (nr - err) < 2 * (q : ℝ) + 2 := by
    have hmul := mul_le_mul_of_nonneg_left hsizeLower.le hfactorTwo
    nlinarith
  have hEbound :
      nr - 2 * (q : ℝ) + 4 * err < (21 / 10 : ℝ) * rho * nr + 2 := by
    nlinarith only [htwoXLower, herr, herr0, hRho.le, hnr]
  have hEboundLe :
      nr - 2 * (q : ℝ) + 4 * err ≤ (21 / 10 : ℝ) * rho * nr + 2 :=
    hEbound.le
  have hE0 : 0 ≤ nr - 2 * (q : ℝ) + 4 * err := by
    nlinarith only [hTwoQReal, herr0]
  have hProfileErrorBound :
      C * (2 * nr * (nr - 2 * (q : ℝ) + 4 * err)) ≤
        C * (2 * nr * ((21 / 10 : ℝ) * rho * nr + 2)) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hEboundLe (by positivity)) hC
  have hquad : C * rho * nr ^ 2 ≤ (e / 1000) * nr ^ 2 :=
    mul_le_mul_of_nonneg_right hCrho (sq_nonneg nr)
  have hlinear : 100 * (C + 1) * nr < e * nr ^ 2 := by
    have hnpos : 0 < (n : ℝ) := by
      dsimp [nr] at hnHundred
      positivity
    have hmul := mul_lt_mul_of_pos_right hnLarge hnpos
    dsimp [nr]
    calc
      100 * (C + 1) * (n : ℝ) < e * (n : ℝ) * (n : ℝ) := hmul
      _ = e * (n : ℝ) ^ 2 := by ring
  have hScard : s ≤ 2 * nr := by
    have hnat := Finset.card_le_card hSsubset
    have hnat' : S.card ≤ 2 * n := by simpa using hnat
    have hreal : (S.card : ℝ) ≤ (2 * n : ℕ) := by exact_mod_cast hnat'
    simpa [s, nr] using hreal
  have hquad' :
      (21 / 5 : ℝ) * (C * rho * nr ^ 2) ≤
        (21 / 5000 : ℝ) * e * nr ^ 2 := by
    nlinarith only [hquad]
  have hlin' :
      4 * C * nr + s < (1 / 25 : ℝ) * e * nr ^ 2 := by
    nlinarith only [hlinear, hScard, hC, hnr]
  have htotal :
      s + C * (2 * nr * ((21 / 10 : ℝ) * rho * nr + 2)) <
        (1 / 2 : ℝ) * e * nr ^ 2 := by
    nlinarith only [hquad', hlin', he, sq_nonneg nr]
  have hMargin :
      s < (e / 4 - 5 * (e / 10) / 4) * (2 * nr) ^ 2 -
        C * (2 * nr * (nr - 2 * (q : ℝ) + 4 * err)) := by
    nlinarith only [hProfileErrorBound, htotal]
  refine ⟨hCard21, hTwoQ, ?_, ?_⟩
  · simpa [err, nr] using hDegreeNumerical
  · dsimp [s, nr, err, q] at hMargin ⊢
    convert hMargin using 1 <;> ring

/-- Deterministic conclusion for one sample after the KSS stability
alternative has been supplied.  This statement is useful independently of
the asymptotic choice of constants: all its assumptions are explicit finite
inequalities verified below for every sufficiently large `n`. -/
lemma isSpannedByCycle_of_good_sample_of_stability
    {n : ℕ} (G : SimpleGraph (Fin (2 * n)))
    (L : CutDecomposition (Fin (2 * n))) (S : Finset (Fin (2 * n)))
    (rho delta coefficientBound : ℝ)
    (hRegularGraph : G.IsRegularOfDegree (n + 1))
    (hBiDense : Trichotomy.BiDense G n TailoredTrichotomy.epsilon0)
    (hCutRegular : IsCutRegular (TailoredTrichotomy.epsilon0 / 10)
      (graphAdjacencyMatrix G - cutDecompositionMatrix L))
    (hMass : cutCoefficientMass L ≤ coefficientBound)
    (hRhoPos : 0 < rho) (hRhoHalf : rho ≤ 1 / 2)
    (hDeltaNonneg : 0 ≤ delta)
    (hDegreeGood : S ∉ degreeBadSamples G (delta * (2 * n : ℝ)))
    (hProfileGood : S ∉ profileBadSamples L (delta * (2 * n : ℝ)))
    (hCard : 21 ≤ S.card)
    (hTwoQ :
      2 * DiracStability.exceptionalSize rho S.card ≤ n)
    (hDegreeNumerical :
      delta * (2 * n : ℝ) + (1 / 2 - rho) *
          ((Fintype.card (CutProfile L) : ℝ) *
            (delta * (2 * n : ℝ))) ≤
        rho * n + 1 / 2)
    (hMargin : (S.card : ℝ) <
      (TailoredTrichotomy.epsilon0 / 4 -
          5 * (TailoredTrichotomy.epsilon0 / 10) / 4) *
          (2 * n : ℝ) ^ 2 -
        coefficientBound * ((2 * n : ℝ) *
          ((n : ℝ) -
            2 * DiracStability.exceptionalSize rho S.card +
            4 * (Fintype.card (CutProfile L) : ℝ) *
              (delta * (2 * n : ℝ)))))
    (hKSS : DiracStability.StabilityStatement.{0} rho 21) :
    IsSpannedByCycle G S := by
  let q := DiracStability.exceptionalSize rho S.card
  let t := delta * (2 * n : ℝ)
  have hProfileTypical : ∀ p : CutProfile L,
      |intersectionCount (profileCell L p) S -
        ((profileCell L p).card : ℝ) / 2| < t :=
    profile_typical_of_not_mem L hProfileGood
  have hSize := sampleCard_close_of_profile_typical L S t hProfileTypical
  have hSizeUpper :
      (S.card : ℝ) ≤ (n : ℝ) +
        (Fintype.card (CutProfile L) : ℝ) * t := by
    have h := (abs_lt.mp hSize).2
    simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at h
    linarith
  have hDegreeTypical : ∀ v : Fin (2 * n),
      |intersectionCount (G.neighborFinset v) S - (G.degree v : ℝ) / 2| < t :=
    degree_typical_of_not_mem G hDegreeGood
  have hMinDegree : ∀ v : (S : Set (Fin (2 * n))),
      (1 / 2 - rho) *
          (Fintype.card (S : Set (Fin (2 * n))) : ℝ) ≤
        (G.induce (S : Set (Fin (2 * n)))).degree v := by
    apply induced_minDegree_of_degree_typical G S n rho t
      ((Fintype.card (CutProfile L) : ℝ) * t)
      hRegularGraph hRhoPos.le hRhoHalf hSizeUpper hDegreeTypical
    simpa [t] using hDegreeNumerical
  have hAmbientDense : ∀ X Y : Finset (Fin (2 * n)),
      X ⊆ S → Y ⊆ S → q ≤ X.card → q ≤ Y.card →
        S.card < (G.interedges X Y).card := by
    apply inherited_biDenseOn_of_profile_typical
      G L S n q S.card TailoredTrichotomy.epsilon0
        (TailoredTrichotomy.epsilon0 / 10) coefficientBound t
      (by simp) hBiDense hCutRegular hMass
      (by dsimp [t]; positivity) hTwoQ hProfileTypical
    simpa [q, t] using hMargin
  have hDenseAbove : DiracStability.BiDenseAbove
      (G.induce (S : Set (Fin (2 * n)))) q S.card :=
    biDenseAbove_induce_of_ambient G S q S.card hAmbientDense
  have hStability : DiracStability.StabilityAlternative
      (G.induce (S : Set (Fin (2 * n)))) q S.card := by
    let W : Type := ↑(S : Set (Fin (2 * n)))
    have hCardW : 21 ≤ Fintype.card W := by
      simpa [W, Fintype.card_coe] using hCard
    have hMinW : ∀ v : W,
        (1 / 2 - rho) * (Fintype.card W : ℝ) ≤
          (G.induce (S : Set (Fin (2 * n)))).degree v := by
      simpa [W, Fintype.card_coe] using hMinDegree
    simpa [q, W, Fintype.card_coe] using
      hKSS.2 W (G.induce (S : Set (Fin (2 * n)))) hCardW hMinW
  have hHam := hStability.isHamiltonian_of_biDenseAbove hDenseAbove
  exact (isSpannedByCycle_iff_isHamiltonian (by omega)).mpr hHam

/-- Finite counting reduction used at the end of the bi-dense case: every
subset is either cyclic or belongs to the declared bad event. -/
lemma powerset_card_le_cycleSpanned_add_bad
    (G : SimpleGraph V) (bad : Finset (Finset V))
    (hGood : ∀ S ∈ (univ : Finset V).powerset,
      S ∉ bad → IsSpannedByCycle G S) :
    ((univ : Finset V).powerset).card ≤
      (cycleSpannedSubsets G).card + bad.card := by
  have hsub : (univ : Finset V).powerset ⊆
      cycleSpannedSubsets G ∪ bad := by
    intro S hS
    by_cases hbad : S ∈ bad
    · exact Finset.mem_union_right _ hbad
    · exact Finset.mem_union_left _
        (mem_cycleSpannedSubsets.mpr (hGood S hS hbad))
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-! ## Uniform asymptotic bi-dense case -/

/-- The complete bi-dense case, reduced only to the fixed-loss KSS stability
statement.  The next theorem discharges that input with the unconditional
KSS theorem. -/
theorem uniformCaseDensityBound_biDense_of_stability
    (hStability : ∀ {rho : ℝ}, 0 < rho → rho ≤ 1 / 12 →
      DiracStability.StabilityStatement.{0} rho 21) :
    UniformCaseDensityBound
      (fun n G ↦ Trichotomy.BiDense G n TailoredTrichotomy.epsilon0) := by
  intro epsilon hEpsilon
  let e : ℝ := TailoredTrichotomy.epsilon0
  have he : 0 < e := by simpa [e] using TailoredTrichotomy.epsilon0_pos
  have heOne : e ≤ 1 := by
    dsimp [e, TailoredTrichotomy.epsilon0]
    norm_num
  have heta : 0 < e / 10 := by positivity
  obtain ⟨k, hkLarge⟩ := exists_nat_gt (1 / (e / 10) ^ 2)
  have hk : 1 ≤ (k : ℝ) * (e / 10) ^ 2 := by
    exact ((div_lt_iff₀ (sq_pos_of_pos heta)).mp hkLarge).le
  let C : ℝ := (k : ℝ) * (2 : ℝ) ^ k
  let Q : ℝ := (4 ^ k : ℕ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact_mod_cast (Nat.one_le_pow k 4 (by omega))
  have hCQ : 1 ≤ (C + 1) * (Q + 1) := by
    nlinarith [mul_le_mul (show (1 : ℝ) ≤ C + 1 by linarith)
      (show (1 : ℝ) ≤ Q + 1 by linarith) (by positivity) (by positivity)]
  let rho : ℝ := e / (1000 * (C + 1) * (Q + 1))
  have hRhoDen : 0 < 1000 * (C + 1) * (Q + 1) := by positivity
  have hRho : 0 < rho := by dsimp [rho]; positivity
  have hRhoLe : rho ≤ e / 1000 := by
    rw [show rho = e / (1000 * (C + 1) * (Q + 1)) by rfl]
    apply (div_le_iff₀ hRhoDen).2
    calc
      e ≤ e * ((C + 1) * (Q + 1)) :=
        by simpa using mul_le_mul_of_nonneg_left hCQ he.le
      _ = e / 1000 * (1000 * (C + 1) * (Q + 1)) := by ring
  have hRhoTwelve : rho ≤ 1 / 12 := by
    have : e / 1000 ≤ (1 / 12 : ℝ) := by
      calc
        e / 1000 ≤ 1 / 1000 := div_le_div_of_nonneg_right heOne (by norm_num)
        _ ≤ 1 / 12 := by norm_num
    exact hRhoLe.trans this
  have hRhoHalf : rho ≤ 1 / 2 := hRhoTwelve.trans (by norm_num)
  let delta : ℝ := rho / (100 * (Q + 1))
  have hDeltaDen : 0 < 100 * (Q + 1) := by positivity
  have hDelta : 0 < delta := by dsimp [delta]; positivity
  have hQratio : Q / (Q + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    linarith
  have hQdelta : Q * delta ≤ rho / 100 := by
    have heq : Q * delta = (rho / 100) * (Q / (Q + 1)) := by
      dsimp [delta]
      field_simp
    rw [heq]
    have hrho100 : 0 ≤ rho / 100 := by positivity
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hQratio hrho100
  have hCProduct : C ≤ (C + 1) * (Q + 1) := by
    have hCstep : C ≤ C + 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_left
      (show (1 : ℝ) ≤ Q + 1 by linarith) (by positivity : 0 ≤ C + 1)
    nlinarith
  have hCrho : C * rho ≤ e / 1000 := by
    have hmul := mul_le_mul_of_nonneg_right hCProduct hRho.le
    have heq : (C + 1) * (Q + 1) * rho = e / 1000 := by
      dsimp [rho]
      field_simp
    linarith
  have hProfileEvent := eventually_profileBadSamples_density_lt
    k hDelta (show 0 < epsilon / 4 by positivity)
  have hDegreeEvent := eventually_degreeBadSamples_density_lt
    hDelta (show 0 < epsilon / 4 by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (100 * (C + 1) / e)
  filter_upwards [hProfileEvent, hDegreeEvent, eventually_ge_atTop N] with
      n hProfileDensity hDegreeDensity hn
  intro G hRegularGraph hBiDense
  obtain ⟨L, hLength, hCutRegular, _hCoefficients, hMass⟩ :=
    finite_graph_weak_regularity_bounded G (e / 10) heta k hk
  have hProfileCountNat : Fintype.card (CutProfile L) ≤ 4 ^ k := by
    calc
      Fintype.card (CutProfile L) = 4 ^ L.length := by simp [CutProfile]
      _ ≤ 4 ^ k := Nat.pow_le_pow_right (by omega) hLength
  have hProfileCount :
      (Fintype.card (CutProfile L) : ℝ) ≤ Q := by
    dsimp [Q]
    exact_mod_cast hProfileCountNat
  have hnLarge : 100 * (C + 1) < e * n := by
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hx : 100 * (C + 1) / e < (n : ℝ) := hN.trans_le hNn
    simpa [mul_comm] using (div_lt_iff₀ he).mp hx
  let bad : Finset (Finset (Fin (2 * n))) :=
    degreeBadSamples G (delta * (2 * n : ℝ)) ∪
      profileBadSamples L (delta * (2 * n : ℝ))
  have hDegreeDensity' :
      ((degreeBadSamples G (delta * (2 * n : ℝ))).card : ℝ) /
          (2 : ℝ) ^ (2 * n) < epsilon / 4 :=
    hDegreeDensity G
  have hProfileDensity' :
      ((profileBadSamples L (delta * (2 * n : ℝ))).card : ℝ) /
          (2 : ℝ) ^ (2 * n) < epsilon / 4 :=
    hProfileDensity L hLength
  have hBadDensity :
      (bad.card : ℝ) / (2 : ℝ) ^ (2 * n) < epsilon / 2 := by
    have hbadNat : bad.card ≤
        (degreeBadSamples G (delta * (2 * n : ℝ))).card +
          (profileBadSamples L (delta * (2 * n : ℝ))).card := by
      exact Finset.card_union_le _ _
    have hbadReal : (bad.card : ℝ) ≤
        (degreeBadSamples G (delta * (2 * n : ℝ))).card +
          (profileBadSamples L (delta * (2 * n : ℝ))).card := by
      exact_mod_cast hbadNat
    have hpow : 0 < (2 : ℝ) ^ (2 * n) := by positivity
    calc
      (bad.card : ℝ) / (2 : ℝ) ^ (2 * n) ≤
          (((degreeBadSamples G (delta * (2 * n : ℝ))).card : ℝ) +
            ((profileBadSamples L (delta * (2 * n : ℝ))).card : ℝ)) /
              (2 : ℝ) ^ (2 * n) :=
        div_le_div_of_nonneg_right hbadReal hpow.le
      _ = ((degreeBadSamples G (delta * (2 * n : ℝ))).card : ℝ) /
            (2 : ℝ) ^ (2 * n) +
          ((profileBadSamples L (delta * (2 * n : ℝ))).card : ℝ) /
            (2 : ℝ) ^ (2 * n) := by ring
      _ < epsilon / 2 := by linarith
  have hGood : ∀ S ∈ (univ : Finset (Fin (2 * n))).powerset,
      S ∉ bad → IsSpannedByCycle G S := by
    intro S hSpower hSbad
    have hSsubset : S ⊆ (univ : Finset (Fin (2 * n))) :=
      Finset.mem_powerset.mp hSpower
    have hDegreeGood :
        S ∉ degreeBadSamples G (delta * (2 * n : ℝ)) := by
      intro h
      exact hSbad (Finset.mem_union_left _ h)
    have hProfileGood :
        S ∉ profileBadSamples L (delta * (2 * n : ℝ)) := by
      intro h
      exact hSbad (Finset.mem_union_right _ h)
    have hTypical : ∀ p : CutProfile L,
        |intersectionCount (profileCell L p) S -
          ((profileCell L p).card : ℝ) / 2| < delta * (2 * n : ℝ) :=
      profile_typical_of_not_mem L hProfileGood
    have hSizeRaw := sampleCard_close_of_profile_typical
      L S (delta * (2 * n : ℝ)) hTypical
    have hSize : |(S.card : ℝ) - (n : ℝ)| <
        (Fintype.card (CutProfile L) : ℝ) *
          (delta * (2 * n : ℝ)) := by
      convert hSizeRaw using 1 <;> simp <;> ring
    obtain ⟨hCard, hTwoQ, hDegreeNumerical, hMargin⟩ :=
      good_sample_numerics e C Q rho delta n S
        (Fintype.card (CutProfile L) : ℝ)
        he heOne hC hQ (by positivity) hProfileCount hRho hRhoHalf
        hDelta.le hQdelta hCrho hnLarge hSsubset hSize
    apply isSpannedByCycle_of_good_sample_of_stability
      G L S rho delta C hRegularGraph hBiDense
    · simpa [e] using hCutRegular
    · simpa [C] using hMass
    · exact hRho
    · exact hRhoHalf
    · exact hDelta.le
    · exact hDegreeGood
    · exact hProfileGood
    · exact hCard
    · exact hTwoQ
    · exact hDegreeNumerical
    · simpa [e] using hMargin
    · exact hStability hRho hRhoTwelve
  have hSplitNat := powerset_card_le_cycleSpanned_add_bad G bad hGood
  have hSplitReal : (2 : ℝ) ^ (2 * n) ≤
      (cycleSpannedSubsets G).card + bad.card := by
    have hcast :
        (((univ : Finset (Fin (2 * n))).powerset).card : ℝ) ≤
          ((cycleSpannedSubsets G).card : ℝ) + bad.card := by
      exact_mod_cast hSplitNat
    simpa using hcast
  have hpow : 0 < (2 : ℝ) ^ (2 * n) := by positivity
  have hBadCount : (bad.card : ℝ) <
      (epsilon / 2) * (2 : ℝ) ^ (2 * n) :=
    (div_lt_iff₀ hpow).mp hBadDensity
  apply (cyclicSubsetDensity_lower_iff_count_lower
    G ((1 / 2 : ℝ) - epsilon)).mpr
  have hpositive : 0 < (1 / 2 + epsilon / 2) * (2 : ℝ) ^ (2 * n) :=
    mul_pos (by linarith) hpow
  nlinarith

end

/-- The bi-dense branch of the uniform Erdős--Faudree density bound. -/
theorem uniformCaseDensityBound_biDense :
    UniformCaseDensityBound
      (fun n G ↦ Trichotomy.BiDense G n TailoredTrichotomy.epsilon0) :=
  uniformCaseDensityBound_biDense_of_stability
    (fun hρpos hρ ↦
      KSSStability.stabilityStatement_of_small_positive_loss hρpos hρ)

end BiDenseCase
end Erdos622
