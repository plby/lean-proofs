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
import ErdosProblems.Erdos76.PippengerSpencerInnerSharp
import ErdosProblems.Erdos76.PippengerSpencerSequentialCount
import Mathlib.Data.Nat.Choose.Sum

/-!
# All-order zero-count estimates for the inner nibble

The quadratic Bonferroni estimate loses a term of order `(a * beta)^2` for
a vertex set of size `a`.  This is harmless for one fixed set but does not
close the backward hierarchy, where `a` grows linearly with the remaining
number of rounds.  Here we retain the complete inclusion--exclusion sum.

The principal theorem, `weighted_zeroMass_close_of_chooseMoments_close`,
shows that cardinality-weighted control of every binomial moment of a bounded
count gives a zero-count estimate whose error is the *sum* of the moment
errors.  Its comparison profile is the exact product `(1-t)^a`, so the
independent quadratic and higher terms are absorbed rather than charged as
absolute error.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

namespace FiniteHypergraph

universe uV uE

variable {V : Type uV} {E : Type uE}
  [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The real alternating binomial sum is the zero indicator. -/
lemma real_alternating_sum_range_choose (n : ℕ) :
    (∑ j ∈ range (n + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ)) =
      if n = 0 then 1 else 0 := by
  exact_mod_cast Int.alternating_sum_range_choose (n := n)

/-- Extending the alternating binomial sum beyond `n` does not change it,
because all higher binomial coefficients vanish. -/
lemma real_alternating_sum_range_choose_of_le
    {n a : ℕ} (hna : n ≤ a) :
    (∑ j ∈ range (a + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ)) =
      if n = 0 then 1 else 0 := by
  rw [← real_alternating_sum_range_choose n]
  symm
  apply sum_subset
  · exact range_mono (Nat.succ_le_succ hna)
  · intro j hja hjn
    have hnj : n < j := by
      have hjn' : ¬j < n + 1 := by simpa using hjn
      omega
    rw [Nat.choose_eq_zero_of_lt hnj]
    simp

/-- Exact product expansion in the alternating-moment normalization. -/
lemma one_sub_pow_eq_sum_alternating_choose (a : ℕ) (t : ℝ) :
    (1 - t) ^ a =
      ∑ j ∈ range (a + 1),
        (-1 : ℝ) ^ j * (a.choose j : ℝ) * t ^ j := by
  have h := add_pow (-t) 1 a
  calc
    (1 - t) ^ a = (-t + 1) ^ a := by congr 1 <;> ring
    _ = ∑ j ∈ range (a + 1),
        (-t) ^ j * 1 ^ (a - j) * (a.choose j : ℝ) := h
    _ = ∑ j ∈ range (a + 1),
        (-1 : ℝ) ^ j * (a.choose j : ℝ) * t ^ j := by
      apply sum_congr rfl
      intro j _
      rw [neg_pow]
      simp
      ring

/-- A weighted zero-count mass for an integer-valued random variable on a
finite sample space.  No normalization of the weights is required. -/
def weightedZeroMass {Omega : Type*} [Fintype Omega]
    (w : Omega → ℝ) (N : Omega → ℕ) : ℝ :=
  ∑ omega, w omega * if N omega = 0 then 1 else 0

/-- The `j`-th binomial moment of a weighted finite count. -/
def weightedChooseMoment {Omega : Type*} [Fintype Omega]
    (w : Omega → ℝ) (N : Omega → ℕ) (j : ℕ) : ℝ :=
  ∑ omega, w omega * (N omega).choose j

/-- Full inclusion--exclusion for a weighted count bounded by `a`. -/
lemma weightedZeroMass_eq_sum_alternating_chooseMoments
    {Omega : Type*} [Fintype Omega]
    (w : Omega → ℝ) (N : Omega → ℕ) (a : ℕ)
    (hN : ∀ omega, N omega ≤ a) :
    weightedZeroMass w N =
      ∑ j ∈ range (a + 1),
        (-1 : ℝ) ^ j * weightedChooseMoment w N j := by
  unfold weightedZeroMass weightedChooseMoment
  calc
    (∑ omega, w omega * if N omega = 0 then 1 else 0) =
        ∑ omega, w omega *
          (∑ j ∈ range (a + 1),
            (-1 : ℝ) ^ j * ((N omega).choose j : ℝ)) := by
      apply sum_congr rfl
      intro omega _
      rw [real_alternating_sum_range_choose_of_le (hN omega)]
    _ = ∑ j ∈ range (a + 1),
          (-1 : ℝ) ^ j *
            (∑ omega, w omega * ((N omega).choose j : ℝ)) := by
      simp_rw [Finset.mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro omega _
      ring

/-- The exact parity-sensitive consequence of two-sided binomial-moment
bounds.  Even moments enter inclusion--exclusion with positive sign and odd
moments with negative sign, so the endpoints must be reversed on the odd
indices.  In particular, this is the valid replacement for a (generally
false) coordinatewise monotonicity claim for alternating sums. -/
theorem weightedZeroMass_mem_Icc_of_chooseMoments_mem_Icc
    {Omega : Type*} [Fintype Omega]
    (w : Omega → ℝ) (N : Omega → ℕ) (a : ℕ)
    (lower upper : ℕ → ℝ)
    (hN : ∀ omega, N omega ≤ a)
    (hmoment : ∀ j, j ≤ a →
      weightedChooseMoment w N j ∈ Set.Icc (lower j) (upper j)) :
    weightedZeroMass w N ∈
      Set.Icc
        (∑ j ∈ range (a + 1), (-1 : ℝ) ^ j *
          if Even j then lower j else upper j)
        (∑ j ∈ range (a + 1), (-1 : ℝ) ^ j *
          if Even j then upper j else lower j) := by
  rw [weightedZeroMass_eq_sum_alternating_chooseMoments w N a hN]
  constructor
  · apply sum_le_sum
    intro j hj
    have hjle : j ≤ a := Nat.le_of_lt_succ (mem_range.mp hj)
    have hjBounds := hmoment j hjle
    by_cases hjEven : Even j
    · rw [if_pos hjEven, hjEven.neg_one_pow, one_mul]
      simpa using hjBounds.1
    · have hjOdd : Odd j := Nat.not_even_iff_odd.mp hjEven
      rw [if_neg hjEven, hjOdd.neg_one_pow, neg_one_mul]
      simpa using neg_le_neg hjBounds.2
  · apply sum_le_sum
    intro j hj
    have hjle : j ≤ a := Nat.le_of_lt_succ (mem_range.mp hj)
    have hjBounds := hmoment j hjle
    by_cases hjEven : Even j
    · rw [if_pos hjEven, hjEven.neg_one_pow, one_mul]
      simpa using hjBounds.2
    · have hjOdd : Odd j := Nat.not_even_iff_odd.mp hjEven
      rw [if_neg hjEven, hjOdd.neg_one_pow, neg_one_mul]
      simpa using neg_le_neg hjBounds.1

/-- The width of the parity-sensitive interval is exactly the sum of the
individual moment widths.  Thus no extra factor is introduced by splitting
the alternating sum into its valid one-sided endpoints. -/
lemma parity_interval_width_eq_sum_sub
    (a : ℕ) (lower upper : ℕ → ℝ) :
    (∑ j ∈ range (a + 1), (-1 : ℝ) ^ j *
        if Even j then upper j else lower j) -
      (∑ j ∈ range (a + 1), (-1 : ℝ) ^ j *
        if Even j then lower j else upper j) =
      ∑ j ∈ range (a + 1), (upper j - lower j) := by
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  by_cases hjEven : Even j
  · simp [hjEven, hjEven.neg_one_pow]
  · have hjOdd : Odd j := Nat.not_even_iff_odd.mp hjEven
    simp [hjEven, hjOdd.neg_one_pow]
    ring

/-- Alternating sums are Lipschitz in the `l¹` norm of their coefficients.
This is the analytic reason to use cardinality-weighted moment errors. -/
lemma abs_sum_alternating_sub_le_sum_abs
    (a : ℕ) (f g : ℕ → ℝ) :
    |∑ j ∈ range (a + 1), (-1 : ℝ) ^ j * f j -
        ∑ j ∈ range (a + 1), (-1 : ℝ) ^ j * g j| ≤
      ∑ j ∈ range (a + 1), |f j - g j| := by
  rw [← sum_sub_distrib]
  calc
    |∑ j ∈ range (a + 1),
        ((-1 : ℝ) ^ j * f j - (-1 : ℝ) ^ j * g j)| ≤
      ∑ j ∈ range (a + 1),
        |(-1 : ℝ) ^ j * f j - (-1 : ℝ) ^ j * g j| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ range (a + 1), |f j - g j| := by
      apply sum_congr rfl
      intro j _
      rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- All-order product zero-count estimate.  If every binomial moment is
close to the corresponding binomial-profile moment, then the zero mass is
close to `W * (1-t)^a`; importantly, no independent `(a*t)^2` term appears. -/
theorem weighted_zeroMass_close_of_chooseMoments_close
    {Omega : Type*} [Fintype Omega]
    (w : Omega → ℝ) (N : Omega → ℕ) (a : ℕ)
    (W t : ℝ) (epsilon : ℕ → ℝ)
    (hN : ∀ omega, N omega ≤ a)
    (hmoment : ∀ j, j ≤ a →
      |weightedChooseMoment w N j -
        W * (a.choose j : ℝ) * t ^ j| ≤ epsilon j) :
    |weightedZeroMass w N - W * (1 - t) ^ a| ≤
      ∑ j ∈ range (a + 1), epsilon j := by
  rw [weightedZeroMass_eq_sum_alternating_chooseMoments w N a hN,
    one_sub_pow_eq_sum_alternating_choose]
  rw [Finset.mul_sum]
  have hcenter :
      (∑ j ∈ range (a + 1),
          W * ((-1 : ℝ) ^ j * (a.choose j : ℝ) * t ^ j)) =
        ∑ j ∈ range (a + 1),
          (-1 : ℝ) ^ j * (W * (a.choose j : ℝ) * t ^ j) := by
    apply sum_congr rfl
    intro j _
    ring
  rw [hcenter]
  calc
    |∑ j ∈ range (a + 1),
          (-1 : ℝ) ^ j * weightedChooseMoment w N j -
        ∑ j ∈ range (a + 1),
          (-1 : ℝ) ^ j * (W * (a.choose j : ℝ) * t ^ j)| ≤
      ∑ j ∈ range (a + 1),
        |weightedChooseMoment w N j -
          W * (a.choose j : ℝ) * t ^ j| := by
      exact abs_sum_alternating_sub_le_sum_abs a
        (weightedChooseMoment w N)
        (fun j ↦ W * (a.choose j : ℝ) * t ^ j)
    _ ≤ ∑ j ∈ range (a + 1), epsilon j := by
      apply sum_le_sum
      intro j hj
      exact hmoment j (Nat.le_of_lt_succ (mem_range.mp hj))

/-! ### One-round hypergraph bridge -/

/-- The all-order zero-count estimate specialized to the number of newly
accepted edges meeting `A` in one inner nibble round.  This is deliberately
stated in terms of conditional binomial moments: a later combinatorial lemma
may estimate those moments without changing the exact inclusion--exclusion
and survival argument here. -/
theorem oneRoundJointUncoveredMass_close_of_chooseMoments_close
    (H : FiniteHypergraph V E) (M : Finset E) (A : Finset V)
    (p W t : ℝ) (epsilon : ℕ → ℝ)
    (hunc : ∀ v ∈ A, H.UncoveredBy M v)
    (hmoment : ∀ j, j ≤ A.card →
      |weightedChooseMoment
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p))
          (fun S ↦ (H.innerNewAcceptedMeeting M S A).card) j -
        W * (A.card.choose j : ℝ) * t ^ j| ≤ epsilon j) :
    |(∑ S : Finset E,
        FiniteNibble.bernoulliMass univ (fun _ ↦ p) S *
          if ∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v then 1 else 0) -
        W * (1 - t) ^ A.card| ≤
      ∑ j ∈ range (A.card + 1), epsilon j := by
  let w : Finset E → ℝ :=
    FiniteNibble.bernoulliMass univ (fun _ ↦ p)
  let N : Finset E → ℕ := fun S ↦
    (H.innerNewAcceptedMeeting M S A).card
  have hN (S : Finset E) : N S ≤ A.card := by
    exact H.innerNewAcceptedMeeting_card_le M S A
  have hzero (S : Finset E) :
      (if ∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v then (1 : ℝ) else 0) =
        if N S = 0 then 1 else 0 := by
    have hiff :=
      H.jointUncovered_innerStep_iff_innerNewAcceptedMeeting_eq_empty
        (S := S) hunc
    by_cases hjoint : ∀ v ∈ A, H.UncoveredBy (H.innerStep M S) v
    · have hempty := hiff.mp hjoint
      have hn : N S = 0 := by simp [N, hempty]
      rw [if_pos hjoint, if_pos hn]
    · have hne : N S ≠ 0 := by
        intro hz
        apply hjoint
        apply hiff.mpr
        exact card_eq_zero.mp hz
      rw [if_neg hjoint, if_neg hne]
  have hmain := weighted_zeroMass_close_of_chooseMoments_close
    w N A.card W t epsilon hN (by
      intro j hj
      simpa [w, N] using hmoment j hj)
  simpa only [weightedZeroMass, w, N, hzero] using hmain

/-- The `j`-th binomial moment of the newly accepted meeting-edge count,
averaged over the first `r` rounds and restricted to trajectories on which
`A` is still jointly uncovered. -/
def averagedInnerNewAcceptedMeetingChooseMoment
    (H : FiniteHypergraph V E) (w : Finset E → ℝ)
    (r : ℕ) (M : Finset E) (A : Finset V) (j : ℕ) : ℝ :=
  ∑ X : Fin r → Finset E,
    FiniteProduct.productMass w X *
      (if ∀ v ∈ A,
          H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
        then 1 else 0) *
      ∑ S : Finset E, w S *
        (((H.innerNewAcceptedMeeting
          ((List.ofFn X).foldl H.innerStep M) S A).card.choose j : ℕ) : ℝ)

/-- The zeroth averaged binomial moment is exactly the current joint
uncovered mass. -/
@[simp] lemma averagedInnerNewAcceptedMeetingChooseMoment_zero
    (H : FiniteHypergraph V E) (p : E → ℝ)
    (r : ℕ) (M : Finset E) (A : Finset V) :
    H.averagedInnerNewAcceptedMeetingChooseMoment
        (FiniteNibble.bernoulliMass univ p) r M A 0 =
      H.innerJointUncoveredMass
        (FiniteNibble.bernoulliMass univ p) r M A := by
  have hsum :
      ∑ S : Finset E, FiniteNibble.bernoulliMass univ p S = 1 := by
    simpa using FiniteNibble.sum_bernoulliMass (univ : Finset E) p
  simp [averagedInnerNewAcceptedMeetingChooseMoment,
    innerJointUncoveredMass, hsum]

/-- Matching `j`-edge subfamilies all of whose edges meet `A`.  Every
nonmatching family has simultaneous isolated-acceptance mass zero, so this
is the exact support of the all-order moment sum. -/
def matchingMeetingFamilies (H : FiniteHypergraph V E)
    (A : Finset V) (j : ℕ) : Finset (Finset E) :=
  ((H.edgesMeeting A).powersetCard j).filter H.IsMatching

@[simp] lemma mem_matchingMeetingFamilies
    (H : FiniteHypergraph V E) (A : Finset V) (j : ℕ) (F : Finset E) :
    F ∈ H.matchingMeetingFamilies A j ↔
      F ⊆ H.edgesMeeting A ∧ F.card = j ∧ H.IsMatching F := by
  simp [matchingMeetingFamilies, and_assoc]

/-- Union of the vertex supports of a finite edge family. -/
def familySupport (H : FiniteHypergraph V E) (F : Finset E) : Finset V :=
  F.biUnion H.support

@[simp] lemma mem_familySupport
    (H : FiniteHypergraph V E) (F : Finset E) (v : V) :
    v ∈ H.familySupport F ↔ ∃ e ∈ F, v ∈ H.support e := by
  simp [familySupport]

/-- Joint uncoveredness of `A` together with every support in `F` is
equivalent to joint uncoveredness of `A` and liveness of every edge in
`F`. -/
lemma jointUncovered_union_familySupport_iff
    {H : FiniteHypergraph V E} {k : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) (M : Finset E) (A : Finset V) (F : Finset E) :
    (∀ v ∈ A ∪ H.familySupport F, H.UncoveredBy M v) ↔
      (∀ v ∈ A, H.UncoveredBy M v) ∧
        ∀ e ∈ F, H.InnerLive M e := by
  constructor
  · intro hall
    refine ⟨fun v hvA ↦ hall v (mem_union_left _ hvA), ?_⟩
    intro e heF
    rw [H.innerLive_iff_uncovered_of_uniform hk hunif M e]
    intro v hve
    exact hall v (mem_union_right A
      ((H.mem_familySupport F v).2 ⟨e, heF, hve⟩))
  · rintro ⟨hA, hlive⟩ v hv
    rcases mem_union.mp hv with hvA | hvF
    · exact hA v hvA
    · obtain ⟨e, heF, hve⟩ := (H.mem_familySupport F v).1 hvF
      exact (H.innerLive_iff_uncovered_of_uniform hk hunif M e).1
        (hlive e heF) v hve

/-- In the powerset expansion, all nonmatching families may be deleted
exactly: they can never be subsets of an isolated sample. -/
lemma sum_innerNewAcceptanceFamilyMass_eq_sum_matching
    (H : FiniteHypergraph V E) (M : Finset E) (p : E → ℝ)
    (A : Finset V) (j : ℕ) :
    (∑ F ∈ (H.edgesMeeting A).powersetCard j,
        H.innerNewAcceptanceFamilyMass M p F) =
      ∑ F ∈ H.matchingMeetingFamilies A j,
        H.innerNewAcceptanceFamilyMass M p F := by
  unfold matchingMeetingFamilies
  rw [sum_filter]
  apply sum_congr rfl
  intro F _
  by_cases hF : H.IsMatching F
  · simp [hF]
  · simp [hF, H.innerNewAcceptanceFamilyMass_eq_zero_of_not_isMatching M p F]

/-- The exact averaged moment as a sum over matching families. -/
theorem averagedInnerNewAcceptedMeetingChooseMoment_eq_sum_matching
    (H : FiniteHypergraph V E) (p : E → ℝ)
    (r : ℕ) (M : Finset E) (A : Finset V) (j : ℕ) :
    H.averagedInnerNewAcceptedMeetingChooseMoment
        (FiniteNibble.bernoulliMass univ p) r M A j =
      ∑ X : Fin r → Finset E,
        FiniteProduct.productMass
            (FiniteNibble.bernoulliMass univ p) X *
          (if ∀ v ∈ A,
              H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
            then 1 else 0) *
          ∑ F ∈ H.matchingMeetingFamilies A j,
            H.innerNewAcceptanceFamilyMass
              ((List.ofFn X).foldl H.innerStep M) p F := by
  unfold averagedInnerNewAcceptedMeetingChooseMoment
  apply sum_congr rfl
  intro X _
  congr 1
  rw [H.sum_bernoulliMass_mul_choose_innerNewAcceptedMeeting_card]
  exact H.sum_innerNewAcceptanceFamilyMass_eq_sum_matching
    ((List.ofFn X).foldl H.innerStep M) p A j

/-- Sum of the enlarged joint-uncovered masses indexed by matching
`j`-families meeting `A`. -/
def matchingFamilyJointMass
    (H : FiniteHypergraph V E) (w : Finset E → ℝ)
    (r : ℕ) (M : Finset E) (A : Finset V) (j : ℕ) : ℝ :=
  ∑ F ∈ H.matchingMeetingFamilies A j,
    H.innerJointUncoveredMass w r M (A ∪ F.biUnion H.support)

/-! ### Exact expansion of the isolation product

The interval estimate obtained by replacing every live conflict
neighbourhood by its worst possible cardinality loses the signs which make
the long all-order evolution stable.  The following identities instead
expand the product exactly over the *static* conflict union.  After
averaging over the old trajectory, every resulting liveness indicator is
again a joint-uncovered mass on a larger finite vertex set. -/

/-- The static union of the conflict neighbourhoods of a finite edge
family. -/
def innerStaticConflictUnion (H : FiniteHypergraph V E)
    (F : Finset E) : Finset E :=
  F.biUnion H.conflictNeighborhood

@[simp] lemma mem_innerStaticConflictUnion
    (H : FiniteHypergraph V E) (F : Finset E) (g : E) :
    g ∈ H.innerStaticConflictUnion F ↔
      ∃ e ∈ F, H.Conflicts e g := by
  simp [innerStaticConflictUnion]

/-- For a matching family, the static conflict union is exactly the set of
edges meeting its support union, with the family itself removed.  This is
the counting form of the isolation neighbourhood: there is no hidden
per-edge overcount. -/
lemma innerStaticConflictUnion_eq_edgesMeeting_familySupport_sdiff
    (H : FiniteHypergraph V E) (F : Finset E) (hF : H.IsMatching F) :
    H.innerStaticConflictUnion F = H.edgesMeeting (H.familySupport F) \ F := by
  ext g
  constructor
  · intro hg
    obtain ⟨e, heF, heg⟩ := (H.mem_innerStaticConflictUnion F g).1 hg
    obtain ⟨v, hve, hvg⟩ := not_disjoint_iff.mp heg.2
    apply mem_sdiff.mpr
    constructor
    · apply (H.mem_edgesMeeting (H.familySupport F) g).2
      exact not_disjoint_iff.mpr ⟨v, hvg,
        (H.mem_familySupport F v).2 ⟨e, heF, hve⟩⟩
    · intro hgF
      exact heg.2 (hF heF hgF heg.1)
  · intro hg
    have hgData := mem_sdiff.mp hg
    obtain ⟨v, hvg, hvFamily⟩ := not_disjoint_iff.mp
      ((H.mem_edgesMeeting (H.familySupport F) g).1 hgData.1)
    obtain ⟨e, heF, hve⟩ := (H.mem_familySupport F v).1 hvFamily
    apply (H.mem_innerStaticConflictUnion F g).2
    refine ⟨e, heF, ?_⟩
    exact ⟨fun heg ↦ hgData.2 (heg ▸ heF),
      not_disjoint_iff.mpr ⟨v, hve, hvg⟩⟩

/-- A uniform matching family has exactly `k` distinct support vertices per
edge. -/
lemma card_familySupport_eq_of_matching_uniform
    (H : FiniteHypergraph V E) (F : Finset E) {k : ℕ}
    (hunif : H.IsUniform k) (hF : H.IsMatching F) :
    (H.familySupport F).card = F.card * k := by
  unfold familySupport
  rw [card_biUnion hF]
  calc
    (∑ e ∈ F, (H.support e).card) = ∑ _e ∈ F, k := by
      apply sum_congr rfl
      intro e _
      exact hunif e
    _ = F.card * k := by simp

/-- Every edge of a positive-uniform family meets the family's support
union. -/
lemma subset_edgesMeeting_familySupport_of_uniform
    (H : FiniteHypergraph V E) (F : Finset E) {k : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) :
    F ⊆ H.edgesMeeting (H.familySupport F) := by
  intro e heF
  have hnonempty : (H.support e).Nonempty := by
    rw [← card_pos, hunif e]
    exact hk
  obtain ⟨v, hv⟩ := hnonempty
  apply (H.mem_edgesMeeting (H.familySupport F) e).2
  exact not_disjoint_iff.mpr ⟨v, hv,
    (H.mem_familySupport F v).2 ⟨e, heF, hv⟩⟩

/-- Exact cardinality of the static conflict union in terms of the meeting
edge set of the support union. -/
lemma card_innerStaticConflictUnion_eq
    (H : FiniteHypergraph V E) (F : Finset E) {k : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) (hF : H.IsMatching F) :
    (H.innerStaticConflictUnion F).card =
      (H.edgesMeeting (H.familySupport F)).card - F.card := by
  rw [H.innerStaticConflictUnion_eq_edgesMeeting_familySupport_sdiff F hF,
    card_sdiff_of_subset
      (H.subset_edgesMeeting_familySupport_of_uniform F hk hunif)]

/-- Maximum degree gives the ideal `|F| k D` upper scale for the static
conflict union. -/
lemma card_innerStaticConflictUnion_le
    (H : FiniteHypergraph V E) (F : Finset E) {k D : ℕ}
    (hk : 0 < k) (hunif : H.IsUniform k) (hF : H.IsMatching F)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) :
    (H.innerStaticConflictUnion F).card ≤ F.card * k * D := by
  rw [H.card_innerStaticConflictUnion_eq F hk hunif hF]
  exact (Nat.sub_le _ _).trans (by
    simpa [H.card_familySupport_eq_of_matching_uniform F hunif hF,
      Nat.mul_assoc] using
      H.edgesMeeting_card_le_mul_degree (H.familySupport F) D hdeg)

/-- The low-codegree incidence estimate controls the deficit from the ideal
static-conflict count.  The additional `|F|` term is exactly the removal of
the chosen family itself. -/
lemma card_mul_uniform_degreeLower_le_staticConflict_add_error
    (H : FiniteHypergraph V E) (F : Finset E) {k degreeLower C : ℕ}
    (hk : 0 < k) (hunif : H.IsUniform k) (hF : H.IsMatching F)
    (hlow : ∀ v ∈ H.familySupport F, degreeLower ≤ H.edgeDegree v)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C) :
    F.card * k * degreeLower ≤
      (H.innerStaticConflictUnion F).card + F.card +
        (F.card * k) ^ 2 * C * k := by
  have hmeet := H.card_mul_degreeLower_le_edgesMeeting_add_pairError
    (H.familySupport F) hunif hlow hpair
  have hsubset := H.subset_edgesMeeting_familySupport_of_uniform F hk hunif
  have hpartition := card_sdiff_add_card_eq_card hsubset
  rw [← H.innerStaticConflictUnion_eq_edgesMeeting_familySupport_sdiff F hF]
    at hpartition
  rw [H.card_familySupport_eq_of_matching_uniform F hunif hF] at hmeet
  omega

/-- Two-sided cardinal profile for the static isolation neighbourhood.  In
an exactly `D`-regular low-codegree hypergraph, specialize
`degreeLower = D`; the width is then the explicit codegree error plus the
chosen family itself. -/
theorem card_innerStaticConflictUnion_mem_Icc
    (H : FiniteHypergraph V E) (F : Finset E) {k D degreeLower C : ℕ}
    (hk : 0 < k) (hunif : H.IsUniform k) (hF : H.IsMatching F)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hlow : ∀ v ∈ H.familySupport F, degreeLower ≤ H.edgeDegree v)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C) :
    (H.innerStaticConflictUnion F).card ∈ Set.Icc
      (F.card * k * degreeLower -
        (F.card + (F.card * k) ^ 2 * C * k))
      (F.card * k * D) := by
  constructor
  · have h := H.card_mul_uniform_degreeLower_le_staticConflict_add_error
      F hk hunif hF hlow hpair
    omega
  · exact H.card_innerStaticConflictUnion_le F hk hunif hF hdeg

/-! ### Profile-preserving conflict subfamilies -/

/-- A family enlarges `B` cleanly when every edge meets `B` exactly once
and the portions outside `B` are pairwise disjoint.  The full edges need not
form a matching: several of them may use the same already-present anchor. -/
def IsProfileEnlargingFamily (H : FiniteHypergraph V E)
    (B : Finset V) (Q : Finset E) : Prop :=
  Q ⊆ H.singleMeetingEdges B ∧
    ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f →
      Disjoint (H.support e \ B) (H.support f \ B)

lemma IsProfileEnlargingFamily.subset_singleMeetingEdges
    {H : FiniteHypergraph V E} {B : Finset V} {Q : Finset E}
    (hQ : H.IsProfileEnlargingFamily B Q) :
    Q ⊆ H.singleMeetingEdges B := hQ.1

lemma IsProfileEnlargingFamily.outside_pairwise
    {H : FiniteHypergraph V E} {B : Finset V} {Q : Finset E}
    (hQ : H.IsProfileEnlargingFamily B Q) :
    ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f →
      Disjoint (H.support e \ B) (H.support f \ B) := hQ.2

/-- A profile-enlarging `q`-family raises the joint-set order by exactly
`q(k-1)`. -/
theorem card_union_familySupport_eq_of_profileEnlarging
    (H : FiniteHypergraph V E) (B : Finset V) (Q : Finset E)
    {k : ℕ} (hk : 0 < k) (hunif : H.IsUniform k)
    (hQ : H.IsProfileEnlargingFamily B Q) :
    (B ∪ H.familySupport Q).card = B.card + Q.card * (k - 1) := by
  have houtsideCard (e : E) (he : e ∈ Q) :
      (H.support e \ B).card = k - 1 := by
    have hsingle := (H.mem_singleMeetingEdges B e).1 (hQ.1 he)
    have hinter : (H.support e ∩ B).card = 1 :=
      H.inter_card_eq_one_of_mem_edgesMeeting_not_multi
        B hsingle.1 hsingle.2
    have hpartition := card_sdiff_add_card_inter (H.support e) B
    rw [hunif e, hinter] at hpartition
    omega
  have hunion : B ∪ H.familySupport Q =
      B ∪ Q.biUnion (fun e ↦ H.support e \ B) := by
    ext v
    simp only [mem_union, mem_familySupport, mem_biUnion, mem_sdiff]
    constructor
    · rintro (hvB | ⟨e, heQ, hve⟩)
      · exact Or.inl hvB
      · by_cases hvB : v ∈ B
        · exact Or.inl hvB
        · exact Or.inr ⟨e, heQ, hve, hvB⟩
    · rintro (hvB | ⟨e, heQ, hve, _⟩)
      · exact Or.inl hvB
      · exact Or.inr ⟨e, heQ, hve⟩
  have hdisjoint : Disjoint B
      (Q.biUnion fun e ↦ H.support e \ B) := by
    rw [disjoint_left]
    intro v hvB hvOutside
    obtain ⟨e, _, hve⟩ := mem_biUnion.mp hvOutside
    exact (mem_sdiff.mp hve).2 hvB
  rw [hunion, card_union_of_disjoint hdisjoint,
    card_biUnion hQ.2]
  calc
    B.card + ∑ e ∈ Q, (H.support e \ B).card =
        B.card + ∑ _e ∈ Q, (k - 1) := by
      apply congrArg (B.card + ·)
      apply sum_congr rfl
      intro e he
      exact houtsideCard e he
    _ = B.card + Q.card * (k - 1) := by simp

/-- Profile-preserving `q`-subfamilies of an ambient edge family `C`. -/
def profileEnlargingSubfamilies (H : FiniteHypergraph V E)
    (B : Finset V) (C : Finset E) (q : ℕ) : Finset (Finset E) :=
  (C.powersetCard q).filter (H.IsProfileEnlargingFamily B)

/-- The complementary exceptional `q`-subfamilies. -/
def exceptionalProfileSubfamilies (H : FiniteHypergraph V E)
    (B : Finset V) (C : Finset E) (q : ℕ) : Finset (Finset E) :=
  C.powersetCard q \ H.profileEnlargingSubfamilies B C q

@[simp] lemma exceptionalProfileSubfamilies_zero
    (H : FiniteHypergraph V E) (B : Finset V) (C : Finset E) :
    H.exceptionalProfileSubfamilies B C 0 = ∅ := by
  simp [exceptionalProfileSubfamilies, profileEnlargingSubfamilies,
    IsProfileEnlargingFamily]

@[simp] lemma mem_profileEnlargingSubfamilies
    (H : FiniteHypergraph V E) (B : Finset V) (C : Finset E)
    (q : ℕ) (Q : Finset E) :
    Q ∈ H.profileEnlargingSubfamilies B C q ↔
      Q ⊆ C ∧ Q.card = q ∧ H.IsProfileEnlargingFamily B Q := by
  simp [profileEnlargingSubfamilies, and_assoc]

/-- A fixed `s`-subfamily is contained in at most `|C|^(q-s)` members of
`C.powersetCard q`. -/
lemma card_filter_powersetCard_superset_le_pow
    (C S : Finset E) (q : ℕ) (hSC : S ⊆ C) (hSq : S.card ≤ q) :
    ((C.powersetCard q).filter (S ⊆ ·)).card ≤ C.card ^ (q - S.card) := by
  rw [card_filter_powersetCard_subset]
  · exact (Nat.choose_le_pow _ _).trans
      (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
  · exact hSC
  · exact hSq

lemma powersetCard_eq_profile_union_exceptional
    (H : FiniteHypergraph V E) (B : Finset V) (C : Finset E) (q : ℕ) :
    C.powersetCard q = H.profileEnlargingSubfamilies B C q ∪
      H.exceptionalProfileSubfamilies B C q := by
  unfold exceptionalProfileSubfamilies profileEnlargingSubfamilies
  symm
  apply union_sdiff_of_subset
  exact filter_subset _ _

/-- Exact witness dichotomy for an exceptional conflict subfamily.  When
the ambient family meets `B`, failure of the clean profile means either one
edge meets `B` multiple times or two selected edges overlap outside `B`.
These are the two codegree-counted error pools in the signed recurrence. -/
theorem exceptionalProfileSubfamily_witness
    (H : FiniteHypergraph V E) (B : Finset V) (C Q : Finset E)
    (hCmeet : C ⊆ H.edgesMeeting B) (hQsub : Q ⊆ C)
    (hbad : ¬H.IsProfileEnlargingFamily B Q) :
    (∃ e ∈ Q, e ∈ H.multiMeetingEdges B) ∨
      ∃ e ∈ Q, ∃ f ∈ Q, e ≠ f ∧
        e ∈ H.singleMeetingEdges B ∧ f ∈ H.singleMeetingEdges B ∧
        ¬Disjoint (H.support e \ B) (H.support f \ B) := by
  by_cases hsingle : Q ⊆ H.singleMeetingEdges B
  · right
    have hnotPair : ¬(∀ e ∈ Q, ∀ f ∈ Q, e ≠ f →
        Disjoint (H.support e \ B) (H.support f \ B)) :=
      fun hp ↦ hbad ⟨hsingle, hp⟩
    push Not at hnotPair
    obtain ⟨e, heQ, f, hfQ, hef, hoverlap⟩ := hnotPair
    exact ⟨e, heQ, f, hfQ, hef, hsingle heQ, hsingle hfQ, hoverlap⟩
  · left
    obtain ⟨e, heQ, heNotSingle⟩ := Set.not_subset.mp hsingle
    have heMeet : e ∈ H.edgesMeeting B := hCmeet (hQsub heQ)
    have heMulti : e ∈ H.multiMeetingEdges B := by
      by_contra heNotMulti
      exact heNotSingle ((H.mem_singleMeetingEdges B e).2
        ⟨heMeet, heNotMulti⟩)
    exact ⟨e, heQ, heMulti⟩

/-- Single-meeting edges whose portions outside `B` overlap the outside
portion of `g`. -/
def outsideOverlappingSingleEdges (H : FiniteHypergraph V E)
    (B : Finset V) (g : E) : Finset E :=
  (H.singleMeetingEdges B).filter fun h ↦
    ¬Disjoint (H.support g \ B) (H.support h \ B)

@[simp] lemma mem_outsideOverlappingSingleEdges
    (H : FiniteHypergraph V E) (B : Finset V) (g h : E) :
    h ∈ H.outsideOverlappingSingleEdges B g ↔
      h ∈ H.singleMeetingEdges B ∧
        ¬Disjoint (H.support g \ B) (H.support h \ B) := by
  simp [outsideOverlappingSingleEdges]

/-- A fixed edge has only `k |B| C` single-meeting partners which overlap
it outside `B`.  The proof charges such a partner to one outside vertex of
`g`, its unique anchor in `B`, and the corresponding pair degree. -/
theorem outsideOverlappingSingleEdges_card_le
    (H : FiniteHypergraph V E) (B : Finset V) (g : E) {k C : ℕ}
    (hunif : H.IsUniform k)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C) :
    (H.outsideOverlappingSingleEdges B g).card ≤ k * B.card * C := by
  let pairEdges : V → V → Finset E := fun u v ↦
    (univ : Finset E).filter fun e ↦
      u ∈ H.support e ∧ v ∈ H.support e
  let cover : Finset E := (H.support g \ B).biUnion fun u ↦
    B.biUnion fun v ↦ pairEdges u v
  have hsub : H.outsideOverlappingSingleEdges B g ⊆ cover := by
    intro h hh
    have hhData := (H.mem_outsideOverlappingSingleEdges B g h).1 hh
    obtain ⟨u, huG, huH⟩ := not_disjoint_iff.mp hhData.2
    have huGData := mem_sdiff.mp huG
    have hhSingle := (H.mem_singleMeetingEdges B h).1 hhData.1
    obtain ⟨v, hvH, hvB⟩ := not_disjoint_iff.mp
      ((H.mem_edgesMeeting B h).1 hhSingle.1)
    have huv : u ≠ v := fun huv ↦ huGData.2 (huv ▸ hvB)
    apply mem_biUnion.mpr
    refine ⟨u, huG, mem_biUnion.mpr ⟨v, hvB, ?_⟩⟩
    exact mem_filter.mpr ⟨mem_univ h, (mem_sdiff.mp huH).1, hvH⟩
  have hpairEdges (u v : V) (huv : u ≠ v) :
      (pairEdges u v).card ≤ C := by
    by_cases hu : u ∈ H.vertexSet
    · by_cases hv : v ∈ H.vertexSet
      · simpa [pairEdges, edgePairDegree] using hpair u hu v hv huv
      · have hno : ∀ e : E, v ∉ H.support e := by
          intro e hve
          exact hv (H.support_subset_vertexSet e hve)
        simp [pairEdges, hno]
    · have hno : ∀ e : E, u ∉ H.support e := by
        intro e hue
        exact hu (H.support_subset_vertexSet e hue)
      simp [pairEdges, hno]
  have hinner (u : V) (hu : u ∈ H.support g \ B) :
      (B.biUnion fun v ↦ pairEdges u v).card ≤ B.card * C := by
    calc
      (B.biUnion fun v ↦ pairEdges u v).card ≤
          ∑ v ∈ B, (pairEdges u v).card := card_biUnion_le
      _ ≤ ∑ _v ∈ B, C := by
        apply sum_le_sum
        intro v hvB
        exact hpairEdges u v (fun huv ↦ (mem_sdiff.mp hu).2 (huv ▸ hvB))
      _ = B.card * C := by simp
  calc
    (H.outsideOverlappingSingleEdges B g).card ≤ cover.card :=
      card_le_card hsub
    _ ≤ ∑ u ∈ H.support g \ B,
        (B.biUnion fun v ↦ pairEdges u v).card := card_biUnion_le
    _ ≤ ∑ _u ∈ H.support g \ B, B.card * C := by
      apply sum_le_sum
      intro u hu
      exact hinner u hu
    _ = (H.support g \ B).card * (B.card * C) := by simp
    _ ≤ k * (B.card * C) := by
      exact Nat.mul_le_mul_right (B.card * C)
        ((card_le_card sdiff_subset).trans_eq (hunif g))
    _ = k * B.card * C := by rw [Nat.mul_assoc]

/-- Explicit count of exceptional `q`-subfamilies.  The first term chooses
a multiple-meeting edge; the second chooses an ordered outside-overlapping
pair.  The remaining edges are charged by arbitrary choices from `C`.
This deliberately overcounts, which keeps the expression polynomial and is
the form needed after multiplying by `p^q`. -/
theorem exceptionalProfileSubfamilies_card_le
    (H : FiniteHypergraph V E) (B : Finset V) (Cset : Finset E)
    {k codegree q : ℕ} (hq : 2 ≤ q)
    (hunif : H.IsUniform k)
    (hCmeet : Cset ⊆ H.edgesMeeting B)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ codegree) :
    (H.exceptionalProfileSubfamilies B Cset q).card ≤
      B.card ^ 2 * codegree * Cset.card ^ (q - 1) +
        Cset.card * (k * B.card * codegree) * Cset.card ^ (q - 2) := by
  let badEdges : Finset E := Cset ∩ H.multiMeetingEdges B
  let edgeCover : E → Finset (Finset E) := fun e ↦
    (Cset.powersetCard q).filter ({e} ⊆ ·)
  let badPartners : E → Finset E := fun e ↦
    (Cset ∩ H.outsideOverlappingSingleEdges B e).erase e
  let pairCover : E → E → Finset (Finset E) := fun e f ↦
    (Cset.powersetCard q).filter ({e, f} ⊆ ·)
  let edgeUnion : Finset (Finset E) := badEdges.biUnion edgeCover
  let pairUnion : Finset (Finset E) := Cset.biUnion fun e ↦
    (badPartners e).biUnion (pairCover e)
  have hsub : H.exceptionalProfileSubfamilies B Cset q ⊆
      edgeUnion ∪ pairUnion := by
    intro Q hQ
    have hQdata := mem_sdiff.mp hQ
    have hQpow := mem_powersetCard.mp hQdata.1
    have hbad : ¬H.IsProfileEnlargingFamily B Q := by
      intro hgood
      exact hQdata.2 ((H.mem_profileEnlargingSubfamilies B Cset q Q).2
        ⟨hQpow.1, hQpow.2, hgood⟩)
    rcases H.exceptionalProfileSubfamily_witness B Cset Q
        hCmeet hQpow.1 hbad with hedge | houtside
    · obtain ⟨e, heQ, heMulti⟩ := hedge
      apply mem_union_left
      apply mem_biUnion.mpr
      refine ⟨e, mem_inter.mpr ⟨hQpow.1 heQ, heMulti⟩, ?_⟩
      exact mem_filter.mpr ⟨hQdata.1, by simpa using heQ⟩
    · obtain ⟨e, heQ, f, hfQ, hef, heSingle, hfSingle, hoverlap⟩ := houtside
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨e, hQpow.1 heQ, mem_biUnion.mpr ⟨f, ?_, ?_⟩⟩
      · exact mem_erase.mpr ⟨hef.symm, mem_inter.mpr ⟨hQpow.1 hfQ,
          (H.mem_outsideOverlappingSingleEdges B e f).2
            ⟨hfSingle, hoverlap⟩⟩⟩
      · apply mem_filter.mpr
        refine ⟨hQdata.1, ?_⟩
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact heQ
        · exact hfQ
  have hedgePool : badEdges.card ≤ B.card ^ 2 * codegree := by
    exact (card_le_card inter_subset_right).trans
      (H.multiMeetingEdges_card_le_sq_mul_pairDegree B codegree hpair)
  have hedgeCover (e : E) (he : e ∈ badEdges) :
      (edgeCover e).card ≤ Cset.card ^ (q - 1) := by
    have heC : e ∈ Cset := (mem_inter.mp he).1
    simpa [edgeCover] using card_filter_powersetCard_superset_le_pow
      Cset ({e} : Finset E) q (by simpa using heC) (by simp; omega)
  have hpartner (e : E) :
      (badPartners e).card ≤ k * B.card * codegree := by
    exact (card_le_card (erase_subset _ _)).trans
      ((card_le_card inter_subset_right).trans
      (H.outsideOverlappingSingleEdges_card_le B e hunif hpair)
      )
  have hpairCover (e : E) (heC : e ∈ Cset)
      (f : E) (hf : f ∈ badPartners e) :
      (pairCover e f).card ≤ Cset.card ^ (q - 2) := by
    have hfData := mem_erase.mp hf
    have hfC : f ∈ Cset := (mem_inter.mp hfData.2).1
    have hfOverlap := (H.mem_outsideOverlappingSingleEdges B e f).1
      (mem_inter.mp hfData.2).2
    have hef : e ≠ f := hfData.1.symm
    have hpairSub : ({e, f} : Finset E) ⊆ Cset := by
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact heC
      · exact hfC
    have hpairCard : ({e, f} : Finset E).card = 2 := by simp [hef]
    simpa [pairCover, hpairCard] using
      card_filter_powersetCard_superset_le_pow Cset ({e, f} : Finset E)
        q hpairSub (by omega)
  have hedgeUnion : edgeUnion.card ≤
      badEdges.card * Cset.card ^ (q - 1) := by
    calc
      edgeUnion.card ≤ ∑ e ∈ badEdges, (edgeCover e).card := card_biUnion_le
      _ ≤ ∑ _e ∈ badEdges, Cset.card ^ (q - 1) := by
        apply sum_le_sum
        intro e he
        exact hedgeCover e he
      _ = badEdges.card * Cset.card ^ (q - 1) := by simp
  have hpairUnion : pairUnion.card ≤
      Cset.card * (k * B.card * codegree) * Cset.card ^ (q - 2) := by
    calc
      pairUnion.card ≤ ∑ e ∈ Cset,
          ((badPartners e).biUnion (pairCover e)).card := card_biUnion_le
      _ ≤ ∑ _e ∈ Cset,
          (k * B.card * codegree) * Cset.card ^ (q - 2) := by
        apply sum_le_sum
        intro e heC
        calc
          ((badPartners e).biUnion (pairCover e)).card ≤
              ∑ f ∈ badPartners e, (pairCover e f).card := card_biUnion_le
          _ ≤ ∑ _f ∈ badPartners e, Cset.card ^ (q - 2) := by
            apply sum_le_sum
            intro f hf
            exact hpairCover e heC f hf
          _ = (badPartners e).card * Cset.card ^ (q - 2) := by simp
          _ ≤ (k * B.card * codegree) * Cset.card ^ (q - 2) :=
            Nat.mul_le_mul_right _ (hpartner e)
      _ = Cset.card * (k * B.card * codegree) *
          Cset.card ^ (q - 2) := by simp [Nat.mul_assoc]
  calc
    (H.exceptionalProfileSubfamilies B Cset q).card ≤
        (edgeUnion ∪ pairUnion).card := card_le_card hsub
    _ ≤ edgeUnion.card + pairUnion.card := card_union_le edgeUnion pairUnion
    _ ≤ badEdges.card * Cset.card ^ (q - 1) +
        Cset.card * (k * B.card * codegree) * Cset.card ^ (q - 2) :=
      Nat.add_le_add hedgeUnion hpairUnion
    _ ≤ B.card ^ 2 * codegree * Cset.card ^ (q - 1) +
        Cset.card * (k * B.card * codegree) * Cset.card ^ (q - 2) :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hedgePool) _

/-- At conflict order one, the only exceptional families are generated by
multiple-meeting edges.  This supplies the codegree-small first-order term
which is not covered by the pair-counting statement above. -/
theorem exceptionalProfileSubfamilies_one_card_le
    (H : FiniteHypergraph V E) (B : Finset V) (Cset : Finset E)
    {codegree : ℕ}
    (hCmeet : Cset ⊆ H.edgesMeeting B)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ codegree) :
    (H.exceptionalProfileSubfamilies B Cset 1).card ≤
      B.card ^ 2 * codegree := by
  let badEdges : Finset E := Cset ∩ H.multiMeetingEdges B
  let edgeCover : E → Finset (Finset E) := fun e ↦
    (Cset.powersetCard 1).filter ({e} ⊆ ·)
  let edgeUnion : Finset (Finset E) := badEdges.biUnion edgeCover
  have hsub : H.exceptionalProfileSubfamilies B Cset 1 ⊆ edgeUnion := by
    intro Q hQ
    have hQdata := mem_sdiff.mp hQ
    have hQpow := mem_powersetCard.mp hQdata.1
    have hbad : ¬H.IsProfileEnlargingFamily B Q := by
      intro hgood
      exact hQdata.2 ((H.mem_profileEnlargingSubfamilies B Cset 1 Q).2
        ⟨hQpow.1, hQpow.2, hgood⟩)
    rcases H.exceptionalProfileSubfamily_witness B Cset Q
        hCmeet hQpow.1 hbad with hedge | houtside
    · obtain ⟨e, heQ, heMulti⟩ := hedge
      apply mem_biUnion.mpr
      refine ⟨e, mem_inter.mpr ⟨hQpow.1 heQ, heMulti⟩, ?_⟩
      exact mem_filter.mpr ⟨hQdata.1, by simpa using heQ⟩
    · obtain ⟨e, heQ, f, hfQ, hef, _⟩ := houtside
      have hcardle : Q.card ≤ 1 := by omega
      exact (hef (Finset.card_le_one.mp hcardle e heQ f hfQ)).elim
  have hbadEdges : badEdges.card ≤ B.card ^ 2 * codegree := by
    exact (card_le_card inter_subset_right).trans
      (H.multiMeetingEdges_card_le_sq_mul_pairDegree B codegree hpair)
  have hedgeCover (e : E) (he : e ∈ badEdges) :
      (edgeCover e).card ≤ 1 := by
    have heC : e ∈ Cset := (mem_inter.mp he).1
    simpa [edgeCover] using card_filter_powersetCard_superset_le_pow
      Cset ({e} : Finset E) 1 (by simpa using heC) (by simp)
  calc
    (H.exceptionalProfileSubfamilies B Cset 1).card ≤ edgeUnion.card :=
      card_le_card hsub
    _ ≤ ∑ e ∈ badEdges, (edgeCover e).card := card_biUnion_le
    _ ≤ ∑ _e ∈ badEdges, 1 := by
      exact sum_le_sum fun e he ↦ hedgeCover e he
    _ = badEdges.card := by simp
    _ ≤ B.card ^ 2 * codegree := hbadEdges

/-- Uniform positive-order exceptional-family envelope, including the
first-order multiple-meeting case and all higher outside-overlap cases. -/
theorem exceptionalProfileSubfamilies_card_le_uniform
    (H : FiniteHypergraph V E) (B : Finset V) (Cset : Finset E)
    {k codegree q : ℕ} (hq : 0 < q)
    (hunif : H.IsUniform k)
    (hCmeet : Cset ⊆ H.edgesMeeting B)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ codegree) :
    (H.exceptionalProfileSubfamilies B Cset q).card ≤
      (B.card ^ 2 + k * B.card) * codegree * Cset.card ^ (q - 1) := by
  rcases q with _ | q
  · simp at hq
  · cases q with
    | zero =>
        simpa using (H.exceptionalProfileSubfamilies_one_card_le
          B Cset hCmeet hpair).trans
            (Nat.mul_le_mul_right codegree (Nat.le_add_right _ _))
    | succ q =>
        have hq2 : 2 ≤ q + 2 := by omega
        have hmain := H.exceptionalProfileSubfamilies_card_le
          B Cset hq2 hunif hCmeet hpair
        have hpow : Cset.card * Cset.card ^ (q + 2 - 2) =
            Cset.card ^ (q + 2 - 1) := by
          rw [show q + 2 - 2 = q by omega,
            show q + 2 - 1 = q + 1 by omega, pow_succ']
        calc
          (H.exceptionalProfileSubfamilies B Cset (q + 2)).card ≤
              B.card ^ 2 * codegree * Cset.card ^ (q + 2 - 1) +
                Cset.card * (k * B.card * codegree) *
                  Cset.card ^ (q + 2 - 2) := hmain
          _ = (B.card ^ 2 + k * B.card) * codegree *
              Cset.card ^ (q + 2 - 1) := by
            rw [show Cset.card * (k * B.card * codegree) *
                Cset.card ^ (q + 2 - 2) =
                (k * B.card * codegree) *
                  (Cset.card * Cset.card ^ (q + 2 - 2)) by ring,
              hpow]
            ring

/-- Every static conflict of `F` meets the enlarged base consisting of `A`
and the support union of `F`. -/
lemma innerStaticConflictUnion_subset_edgesMeeting_union_familySupport
    (H : FiniteHypergraph V E) (A : Finset V) (F : Finset E) :
    H.innerStaticConflictUnion F ⊆
      H.edgesMeeting (A ∪ H.familySupport F) := by
  intro g hg
  obtain ⟨e, heF, heg⟩ := (H.mem_innerStaticConflictUnion F g).1 hg
  obtain ⟨v, hve, hvg⟩ := not_disjoint_iff.mp heg.2
  apply (H.mem_edgesMeeting (A ∪ H.familySupport F) g).2
  exact not_disjoint_iff.mpr ⟨v, hvg, mem_union_right A
    ((H.mem_familySupport F v).2 ⟨e, heF, hve⟩)⟩

/-- Specialization of the exceptional `Q`-family count to the static
isolation neighbourhood of an outer family `F`. -/
theorem exceptionalStaticConflictSubfamilies_card_le
    (H : FiniteHypergraph V E) (A : Finset V) (F : Finset E)
    {k codegree q : ℕ} (hq : 2 ≤ q)
    (hunif : H.IsUniform k)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ codegree) :
    (H.exceptionalProfileSubfamilies
        (A ∪ H.familySupport F) (H.innerStaticConflictUnion F) q).card ≤
      (A ∪ H.familySupport F).card ^ 2 * codegree *
          (H.innerStaticConflictUnion F).card ^ (q - 1) +
        (H.innerStaticConflictUnion F).card *
          (k * (A ∪ H.familySupport F).card * codegree) *
          (H.innerStaticConflictUnion F).card ^ (q - 2) := by
  exact H.exceptionalProfileSubfamilies_card_le
    (A ∪ H.familySupport F) (H.innerStaticConflictUnion F)
      hq hunif
      (H.innerStaticConflictUnion_subset_edgesMeeting_union_familySupport A F)
      hpair

/-- A dominant outer family followed by a profile-enlarging conflict family
has exactly the ideal enlarged joint-set order. -/
theorem card_union_familySupport_union_eq_of_good_outer_profile
    (H : FiniteHypergraph V E) (A : Finset V) (F Q : Finset E)
    {k : ℕ} (hk : 0 < k) (hunif : H.IsUniform k)
    (hF : H.IsMatching F) (hFsingle : F ⊆ H.singleMeetingEdges A)
    (hQ : H.IsProfileEnlargingFamily (A ∪ H.familySupport F) Q) :
    (A ∪ H.familySupport (F ∪ Q)).card =
      A.card + F.card * (k - 1) + Q.card * (k - 1) := by
  have hFcard := H.card_union_biUnion_support_eq_of_matching_subset_singleMeeting
    A F hk hunif hF hFsingle
  have hFcard' : (A ∪ H.familySupport F).card =
      A.card + F.card * (k - 1) := by
    simpa [familySupport] using hFcard
  have hQcard := H.card_union_familySupport_eq_of_profileEnlarging
    (A ∪ H.familySupport F) Q hk hunif hQ
  rw [hFcard'] at hQcard
  have hfamilyUnion : H.familySupport (F ∪ Q) =
      H.familySupport F ∪ H.familySupport Q := by
    ext v
    constructor
    · intro hv
      obtain ⟨e, he, hve⟩ := (H.mem_familySupport (F ∪ Q) v).1 hv
      rcases mem_union.mp he with heF | heQ
      · exact mem_union_left _ ((H.mem_familySupport F v).2 ⟨e, heF, hve⟩)
      · exact mem_union_right _ ((H.mem_familySupport Q v).2 ⟨e, heQ, hve⟩)
    · intro hv
      rcases mem_union.mp hv with hvF | hvQ
      · obtain ⟨e, heF, hve⟩ := (H.mem_familySupport F v).1 hvF
        exact (H.mem_familySupport (F ∪ Q) v).2
          ⟨e, mem_union_left _ heF, hve⟩
      · obtain ⟨e, heQ, hve⟩ := (H.mem_familySupport Q v).1 hvQ
        exact (H.mem_familySupport (F ∪ Q) v).2
          ⟨e, mem_union_right _ heQ, hve⟩
  rw [hfamilyUnion, ← union_assoc]
  exact hQcard

/-- A clean/exceptional partition converts a uniform profile estimate on
clean `q`-families into an absolute estimate for the complete `q`-moment.
Every exceptional family costs at most one because both the actual mass and
the reference target lie in `[0,1]`. -/
theorem sum_powersetCard_profile_close
    (H : FiniteHypergraph V E) (B : Finset V) (Cset : Finset E)
    (q : ℕ) (U : Finset E → ℝ) (target epsilon : ℝ)
    (hU : ∀ Q, U Q ∈ Set.Icc (0 : ℝ) 1)
    (htarget : target ∈ Set.Icc (0 : ℝ) 1)
    (hepsilon : 0 ≤ epsilon)
    (hprofile : ∀ Q ∈ H.profileEnlargingSubfamilies B Cset q,
      |U Q - target| ≤ epsilon) :
    |(∑ Q ∈ Cset.powersetCard q, U Q) -
        (Cset.card.choose q : ℝ) * target| ≤
      (Cset.card.choose q : ℝ) * epsilon +
        ((H.exceptionalProfileSubfamilies B Cset q).card : ℝ) := by
  let good := H.profileEnlargingSubfamilies B Cset q
  let bad := H.exceptionalProfileSubfamilies B Cset q
  have hpartition : Cset.powersetCard q = good ∪ bad :=
    H.powersetCard_eq_profile_union_exceptional B Cset q
  have hdisjoint : Disjoint good bad := by
    unfold good bad exceptionalProfileSubfamilies
    exact disjoint_sdiff
  have hbadBound (Q : Finset E) : |U Q - target| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [(hU Q).1, (hU Q).2, htarget.1, htarget.2]
  have hcenter :
      (∑ Q ∈ Cset.powersetCard q, U Q) -
          (Cset.card.choose q : ℝ) * target =
        ∑ Q ∈ Cset.powersetCard q, (U Q - target) := by
    rw [sum_sub_distrib]
    simp
  rw [hcenter, hpartition, sum_union hdisjoint]
  calc
    |(∑ Q ∈ good, (U Q - target)) +
        ∑ Q ∈ bad, (U Q - target)| ≤
        |∑ Q ∈ good, (U Q - target)| +
          |∑ Q ∈ bad, (U Q - target)| := abs_add_le _ _
    _ ≤ (∑ Q ∈ good, |U Q - target|) +
        ∑ Q ∈ bad, |U Q - target| := by
      exact add_le_add (abs_sum_le_sum_abs _ _) (abs_sum_le_sum_abs _ _)
    _ ≤ (∑ _Q ∈ good, epsilon) + ∑ _Q ∈ bad, (1 : ℝ) := by
      apply add_le_add <;> apply sum_le_sum
      · intro Q hQ
        exact hprofile Q hQ
      · intro Q _
        exact hbadBound Q
    _ = (good.card : ℝ) * epsilon + (bad.card : ℝ) := by simp
    _ ≤ ((Cset.powersetCard q).card : ℝ) * epsilon +
        (bad.card : ℝ) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast card_le_card (by
            intro Q hQ
            have hQdata :=
              (H.mem_profileEnlargingSubfamilies B Cset q Q).1 hQ
            exact mem_powersetCard.mpr ⟨hQdata.1, hQdata.2.1⟩))
          hepsilon
      · exact le_rfl
    _ = (Cset.card.choose q : ℝ) * epsilon +
        ((H.exceptionalProfileSubfamilies B Cset q).card : ℝ) := by
      simp [good, bad]

/-- Regroup a signed powerset sum by subfamily cardinality. -/
lemma sum_powerset_signed_eq_sum_powersetCard
    (Cset : Finset E) (p : ℝ) (U : Finset E → ℝ) :
    (∑ Q ∈ Cset.powerset, (-p) ^ Q.card * U Q) =
      ∑ q ∈ range (Cset.card + 1),
        (-p) ^ q * ∑ Q ∈ Cset.powersetCard q, U Q := by
  have hdisj : ∀ i ∈ range (Cset.card + 1),
      ∀ j ∈ range (Cset.card + 1), i ≠ j →
        Disjoint (Cset.powersetCard i) (Cset.powersetCard j) := by
    intro i _ j _ hij
    rw [disjoint_left]
    intro Q hQi hQj
    have hi := (mem_powersetCard.mp hQi).2
    have hj := (mem_powersetCard.mp hQj).2
    exact hij (hi.symm.trans hj)
  rw [powerset_card_biUnion, sum_biUnion hdisj]
  apply sum_congr rfl
  intro q _
  rw [mul_sum]
  apply sum_congr rfl
  intro Q hQ
  rw [(mem_powersetCard.mp hQ).2]

/-- The ideal signed `q`-profile is exactly the isolation-adjusted product
factor.  This is the cancellation-preserving scalar reference for one
inner round. -/
lemma sum_signed_binomial_jointProfile
    (N b d : ℕ) (p y : ℝ) :
    (∑ q ∈ range (N + 1),
        (-p) ^ q * (N.choose q : ℝ) * y ^ (b + q * d)) =
      y ^ b * (1 - p * y ^ d) ^ N := by
  calc
    (∑ q ∈ range (N + 1),
        (-p) ^ q * (N.choose q : ℝ) * y ^ (b + q * d)) =
        y ^ b * ∑ q ∈ range (N + 1),
          (N.choose q : ℝ) * (-p * y ^ d) ^ q := by
      rw [mul_sum]
      apply sum_congr rfl
      intro q _
      rw [pow_add, pow_mul, mul_pow]
      ring
    _ = y ^ b * (1 + (-p * y ^ d)) ^ N := by
      congr 1
      rw [add_comm (1 : ℝ) (-p * y ^ d), add_pow]
      apply sum_congr rfl
      intro q _
      simp
      ring
    _ = y ^ b * (1 - p * y ^ d) ^ N := by
      congr 2
      ring

/-- Stability of the complete signed isolation expansion around the exact
product reference.  All cancellation is retained in
`y^b * (1-p*y^d)^|C|`; the right side charges only profile errors and the
explicit exceptional-family counts, weighted by the correct power of
`|p|`. -/
theorem sum_powerset_signed_jointProfile_close
    (H : FiniteHypergraph V E) (B : Finset V) (Cset : Finset E)
    (U : Finset E → ℝ) (p y : ℝ) (b d : ℕ)
    (epsilon : ℕ → ℝ)
    (hU : ∀ Q, U Q ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hepsilon : ∀ q, 0 ≤ epsilon q)
    (hprofile : ∀ q, ∀ Q ∈ H.profileEnlargingSubfamilies B Cset q,
      |U Q - y ^ (b + q * d)| ≤ epsilon q) :
    |(∑ Q ∈ Cset.powerset, (-p) ^ Q.card * U Q) -
        y ^ b * (1 - p * y ^ d) ^ Cset.card| ≤
      ∑ q ∈ range (Cset.card + 1),
        |p| ^ q * ((Cset.card.choose q : ℝ) * epsilon q +
          ((H.exceptionalProfileSubfamilies B Cset q).card : ℝ)) := by
  let moment : ℕ → ℝ := fun q ↦
    ∑ Q ∈ Cset.powersetCard q, U Q
  have hmoment (q : ℕ) :
      |moment q - (Cset.card.choose q : ℝ) * y ^ (b + q * d)| ≤
        (Cset.card.choose q : ℝ) * epsilon q +
          ((H.exceptionalProfileSubfamilies B Cset q).card : ℝ) := by
    exact H.sum_powersetCard_profile_close B Cset q U
      (y ^ (b + q * d)) (epsilon q) hU
      ⟨pow_nonneg hy.1 _, pow_le_one₀ hy.1 hy.2⟩
      (hepsilon q) (hprofile q)
  rw [sum_powerset_signed_eq_sum_powersetCard]
  change |(∑ q ∈ range (Cset.card + 1), (-p) ^ q * moment q) - _| ≤ _
  rw [← sum_signed_binomial_jointProfile Cset.card b d p y,
    ← sum_sub_distrib]
  calc
    |∑ q ∈ range (Cset.card + 1),
        ((-p) ^ q * moment q -
          (-p) ^ q * (Cset.card.choose q : ℝ) * y ^ (b + q * d))| ≤
        ∑ q ∈ range (Cset.card + 1),
          |(-p) ^ q * moment q -
            (-p) ^ q * (Cset.card.choose q : ℝ) * y ^ (b + q * d)| :=
      abs_sum_le_sum_abs _ _
    _ = ∑ q ∈ range (Cset.card + 1),
        |p| ^ q *
          |moment q - (Cset.card.choose q : ℝ) * y ^ (b + q * d)| := by
      apply sum_congr rfl
      intro q _
      have hfactor :
          (-p) ^ q * moment q -
              (-p) ^ q * (Cset.card.choose q : ℝ) * y ^ (b + q * d) =
            (-p) ^ q *
              (moment q - (Cset.card.choose q : ℝ) * y ^ (b + q * d)) := by
        ring
      rw [hfactor, abs_mul, abs_pow, abs_neg]
    _ ≤ ∑ q ∈ range (Cset.card + 1),
        |p| ^ q * ((Cset.card.choose q : ℝ) * epsilon q +
          ((H.exceptionalProfileSubfamilies B Cset q).card : ℝ)) := by
      apply sum_le_sum
      intro q _
      exact mul_le_mul_of_nonneg_left (hmoment q) (pow_nonneg (abs_nonneg p) _)

/-- Cutoff form of the signed isolation estimate.  Clean profile control is
required only through order `Qcut`; every higher-order coefficient is
charged by its exact binomial-tail weight.  This is the finite-order bridge
needed for a backward, time-dependent cutoff argument. -/
theorem sum_powerset_signed_jointProfile_close_cutoff
    (H : FiniteHypergraph V E) (B : Finset V) (Cset : Finset E)
    (U : Finset E → ℝ) (p y : ℝ) (b d Qcut : ℕ)
    (epsilon : ℕ → ℝ)
    (hU : ∀ Q, U Q ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hepsilon : ∀ q, 0 ≤ epsilon q)
    (hprofile : ∀ q, q ≤ Qcut →
      ∀ Q ∈ H.profileEnlargingSubfamilies B Cset q,
        |U Q - y ^ (b + q * d)| ≤ epsilon q) :
    |(∑ Q ∈ Cset.powerset, (-p) ^ Q.card * U Q) -
        y ^ b * (1 - p * y ^ d) ^ Cset.card| ≤
      ∑ q ∈ range (Cset.card + 1), |p| ^ q *
        (if q ≤ Qcut then
          (Cset.card.choose q : ℝ) * epsilon q +
            ((H.exceptionalProfileSubfamilies B Cset q).card : ℝ)
        else (Cset.card.choose q : ℝ)) := by
  let moment : ℕ → ℝ := fun q ↦
    ∑ Q ∈ Cset.powersetCard q, U Q
  have hmomentSharp (q : ℕ) (hq : q ≤ Qcut) :
      |moment q - (Cset.card.choose q : ℝ) * y ^ (b + q * d)| ≤
        (Cset.card.choose q : ℝ) * epsilon q +
          ((H.exceptionalProfileSubfamilies B Cset q).card : ℝ) := by
    exact H.sum_powersetCard_profile_close B Cset q U
      (y ^ (b + q * d)) (epsilon q) hU
      ⟨pow_nonneg hy.1 _, pow_le_one₀ hy.1 hy.2⟩
      (hepsilon q) (hprofile q hq)
  have hmomentCrude (q : ℕ) :
      |moment q - (Cset.card.choose q : ℝ) * y ^ (b + q * d)| ≤
        (Cset.card.choose q : ℝ) := by
    have hmoment₀ : 0 ≤ moment q := by
      exact sum_nonneg fun Q _ ↦ (hU Q).1
    have hmoment₁ : moment q ≤ (Cset.card.choose q : ℝ) := by
      calc
        moment q ≤ ∑ _Q ∈ Cset.powersetCard q, (1 : ℝ) := by
          exact sum_le_sum fun Q _ ↦ (hU Q).2
        _ = (Cset.card.choose q : ℝ) := by simp
    have htarget₀ :
        0 ≤ (Cset.card.choose q : ℝ) * y ^ (b + q * d) :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hy.1 _)
    have htarget₁ :
        (Cset.card.choose q : ℝ) * y ^ (b + q * d) ≤
          (Cset.card.choose q : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left
        (pow_le_one₀ hy.1 hy.2) (Nat.cast_nonneg (Cset.card.choose q))
    rw [abs_le]
    constructor <;> linarith
  rw [sum_powerset_signed_eq_sum_powersetCard]
  change |(∑ q ∈ range (Cset.card + 1), (-p) ^ q * moment q) - _| ≤ _
  rw [← sum_signed_binomial_jointProfile Cset.card b d p y,
    ← sum_sub_distrib]
  calc
    |∑ q ∈ range (Cset.card + 1),
        ((-p) ^ q * moment q -
          (-p) ^ q * (Cset.card.choose q : ℝ) * y ^ (b + q * d))| ≤
        ∑ q ∈ range (Cset.card + 1),
          |(-p) ^ q * moment q -
            (-p) ^ q * (Cset.card.choose q : ℝ) *
              y ^ (b + q * d)| := abs_sum_le_sum_abs _ _
    _ = ∑ q ∈ range (Cset.card + 1), |p| ^ q *
          |moment q -
            (Cset.card.choose q : ℝ) * y ^ (b + q * d)| := by
      apply sum_congr rfl
      intro q _
      rw [show (-p) ^ q * moment q -
          (-p) ^ q * (Cset.card.choose q : ℝ) * y ^ (b + q * d) =
        (-p) ^ q * (moment q -
          (Cset.card.choose q : ℝ) * y ^ (b + q * d)) by ring,
        abs_mul, abs_pow, abs_neg]
    _ ≤ ∑ q ∈ range (Cset.card + 1), |p| ^ q *
        (if q ≤ Qcut then
          (Cset.card.choose q : ℝ) * epsilon q +
            ((H.exceptionalProfileSubfamilies B Cset q).card : ℝ)
        else (Cset.card.choose q : ℝ)) := by
      apply sum_le_sum
      intro q _
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg p) _)
      by_cases hq : q ≤ Qcut
      · rw [if_pos hq]
        exact hmomentSharp q hq
      · rw [if_neg hq]
        exact hmomentCrude q

/-- Concrete fixed-family isolation estimate for the inner process.  A
cardinality-indexed joint-survival induction hypothesis supplies the clean
`Q` terms automatically through the exact order formula above. -/
theorem staticConflictSignedJointMass_close
    (H : FiniteHypergraph V E) (w : Finset E → ℝ)
    (hw₀ : ∀ S, 0 ≤ w S) (hw : ∑ S, w S = 1)
    (r : ℕ) (M : Finset E) (A : Finset V) (F : Finset E)
    {k : ℕ} (hk : 0 < k) (hunif : H.IsUniform k)
    (hF : H.IsMatching F) (hFsingle : F ⊆ H.singleMeetingEdges A)
    (p y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (orderError : ℕ → ℝ) (herror₀ : ∀ a, 0 ≤ orderError a)
    (hprofile : ∀ S : Finset V,
      |H.innerJointUncoveredMass w r M S - y ^ S.card| ≤
        orderError S.card) :
    |(∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
        (-p) ^ Q.card *
          H.innerJointUncoveredMass w r M
            (A ∪ H.familySupport (F ∪ Q))) -
        y ^ (A.card + F.card * (k - 1)) *
          (1 - p * y ^ (k - 1)) ^
            (H.innerStaticConflictUnion F).card| ≤
      ∑ q ∈ range ((H.innerStaticConflictUnion F).card + 1),
        |p| ^ q *
          (((H.innerStaticConflictUnion F).card.choose q : ℝ) *
              orderError
                (A.card + F.card * (k - 1) + q * (k - 1)) +
            ((H.exceptionalProfileSubfamilies
              (A ∪ H.familySupport F)
              (H.innerStaticConflictUnion F) q).card : ℝ)) := by
  let B := A ∪ H.familySupport F
  let Cset := H.innerStaticConflictUnion F
  let U : Finset E → ℝ := fun Q ↦
    H.innerJointUncoveredMass w r M
      (A ∪ H.familySupport (F ∪ Q))
  let b := A.card + F.card * (k - 1)
  let d := k - 1
  let epsilon : ℕ → ℝ := fun q ↦ orderError (b + q * d)
  have hU (Q : Finset E) : U Q ∈ Set.Icc (0 : ℝ) 1 := by
    exact H.innerJointUncoveredMass_mem_Icc w hw₀ hw r M _
  have hepsilon (q : ℕ) : 0 ≤ epsilon q := herror₀ _
  have hclean (q : ℕ)
      (Q : Finset E) (hQ : Q ∈ H.profileEnlargingSubfamilies B Cset q) :
      |U Q - y ^ (b + q * d)| ≤ epsilon q := by
    have hQdata := (H.mem_profileEnlargingSubfamilies B Cset q Q).1 hQ
    have hcard := H.card_union_familySupport_union_eq_of_good_outer_profile
      A F Q hk hunif hF hFsingle hQdata.2.2
    have h := hprofile (A ∪ H.familySupport (F ∪ Q))
    dsimp only [U, b, d, epsilon]
    rw [hcard, hQdata.2.1] at h
    exact h
  simpa [B, Cset, U, b, d, epsilon] using
    H.sum_powerset_signed_jointProfile_close B Cset U p y b d epsilon
      hU hy hepsilon hclean

/-- Fixed-family cutoff specialization.  Joint-profile control is used
only for enlarged vertex sets whose order is at most
`b + Qcut*(k-1)`; all larger conflict subfamilies are absorbed into the
signed binomial tail. -/
theorem staticConflictSignedJointMass_close_cutoff
    (H : FiniteHypergraph V E) (w : Finset E → ℝ)
    (hw₀ : ∀ S, 0 ≤ w S) (hw : ∑ S, w S = 1)
    (r : ℕ) (M : Finset E) (A : Finset V) (F : Finset E)
    {k : ℕ} (hk : 0 < k) (hunif : H.IsUniform k)
    (hA : A ⊆ H.vertexSet)
    (hF : H.IsMatching F) (hFsingle : F ⊆ H.singleMeetingEdges A)
    (p y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (Qcut : ℕ) (orderError : ℕ → ℝ)
    (herror₀ : ∀ a, 0 ≤ orderError a)
    (hprofile : ∀ S : Finset V,
      S ⊆ H.vertexSet →
      S.card ≤ A.card + F.card * (k - 1) + Qcut * (k - 1) →
      |H.innerJointUncoveredMass w r M S - y ^ S.card| ≤
        orderError S.card) :
    |(∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
        (-p) ^ Q.card *
          H.innerJointUncoveredMass w r M
            (A ∪ H.familySupport (F ∪ Q))) -
        y ^ (A.card + F.card * (k - 1)) *
          (1 - p * y ^ (k - 1)) ^
            (H.innerStaticConflictUnion F).card| ≤
      ∑ q ∈ range ((H.innerStaticConflictUnion F).card + 1),
        |p| ^ q *
          (if q ≤ Qcut then
            ((H.innerStaticConflictUnion F).card.choose q : ℝ) *
                orderError
                  (A.card + F.card * (k - 1) + q * (k - 1)) +
              ((H.exceptionalProfileSubfamilies
                (A ∪ H.familySupport F)
                (H.innerStaticConflictUnion F) q).card : ℝ)
          else
            ((H.innerStaticConflictUnion F).card.choose q : ℝ)) := by
  let B := A ∪ H.familySupport F
  let Cset := H.innerStaticConflictUnion F
  let U : Finset E → ℝ := fun Q ↦
    H.innerJointUncoveredMass w r M
      (A ∪ H.familySupport (F ∪ Q))
  let b := A.card + F.card * (k - 1)
  let d := k - 1
  let epsilon : ℕ → ℝ := fun q ↦ orderError (b + q * d)
  have hU (Q : Finset E) : U Q ∈ Set.Icc (0 : ℝ) 1 :=
    H.innerJointUncoveredMass_mem_Icc w hw₀ hw r M _
  have hepsilon (q : ℕ) : 0 ≤ epsilon q := herror₀ _
  have hclean (q : ℕ) (hq : q ≤ Qcut)
      (Q : Finset E) (hQ : Q ∈ H.profileEnlargingSubfamilies B Cset q) :
      |U Q - y ^ (b + q * d)| ≤ epsilon q := by
    have hQdata := (H.mem_profileEnlargingSubfamilies B Cset q Q).1 hQ
    have hcard := H.card_union_familySupport_union_eq_of_good_outer_profile
      A F Q hk hunif hF hFsingle hQdata.2.2
    have hcardBound :
        (A ∪ H.familySupport (F ∪ Q)).card ≤
          A.card + F.card * (k - 1) + Qcut * (k - 1) := by
      rw [hcard, hQdata.2.1]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hq) _
    have hvertex : A ∪ H.familySupport (F ∪ Q) ⊆ H.vertexSet := by
      intro v hv
      rw [mem_union] at hv
      rcases hv with hv | hv
      · exact hA hv
      · obtain ⟨e, _he, hve⟩ := (H.mem_familySupport (F ∪ Q) v).1 hv
        exact H.support_subset_vertexSet e hve
    have h := hprofile (A ∪ H.familySupport (F ∪ Q)) hvertex hcardBound
    dsimp only [U, b, d, epsilon]
    rw [hcard, hQdata.2.1] at h
    exact h
  simpa [B, Cset, U, b, d, epsilon] using
    H.sum_powerset_signed_jointProfile_close_cutoff
      B Cset U p y b d Qcut epsilon hU hy hepsilon hclean

/-- Powers on `[0,1]` are Lipschitz in a decrease of the exponent.  The
factor `1-z` is essential here: for the isolation base
`z = 1-p*y^(k-1)` it supplies the extra Bernoulli factor which makes a
codegree-sized cardinality error negligible after degree normalization. -/
lemma abs_pow_sub_pow_le_exponent_gap
    {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) {n N : ℕ} (hnN : n ≤ N) :
    |z ^ n - z ^ N| ≤ ((N - n : ℕ) : ℝ) * (1 - z) := by
  have hpowOrder : z ^ N ≤ z ^ n := by
    exact pow_le_pow_of_le_one hz.1 hz.2 hnN
  have hfactor₀ : 0 ≤ 1 - z ^ (N - n) := by
    exact sub_nonneg.mpr (pow_le_one₀ hz.1 hz.2)
  have hzn₀ : 0 ≤ z ^ n := pow_nonneg hz.1 n
  have hzn₁ : z ^ n ≤ 1 := pow_le_one₀ hz.1 hz.2
  have hbern : 1 - z ^ (N - n) ≤ ((N - n : ℕ) : ℝ) * (1 - z) := by
    have h := one_sub_one_sub_pow_le_natCast_mul
      (N - n) (sub_nonneg.mpr hz.2) (by linarith [hz.1])
    simpa [sub_sub_cancel] using h
  rw [abs_of_nonneg (sub_nonneg.mpr hpowOrder)]
  have hpowSplit : z ^ N = z ^ n * z ^ (N - n) := by
    calc
      z ^ N = z ^ (n + (N - n)) := by congr 1 <;> omega
      _ = z ^ n * z ^ (N - n) := pow_add z n (N - n)
  calc
    z ^ n - z ^ N = z ^ n * (1 - z ^ (N - n)) := by
      rw [hpowSplit]
      ring
    _ ≤ 1 * (1 - z ^ (N - n)) :=
      mul_le_mul_of_nonneg_right hzn₁ hfactor₀
    _ ≤ ((N - n : ℕ) : ℝ) * (1 - z) := by
      simpa using hbern

/-- Replacing the actual static-conflict exponent by its ideal regular
value costs the conflict-cardinality deficit times the single-coordinate
failure probability. -/
lemma staticConflictProfile_exponent_close
    (H : FiniteHypergraph V E) (F : Finset E)
    {k D : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) (hF : H.IsMatching F)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {p y : ℝ} (hp₀ : 0 ≤ p) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpY : p * y ^ (k - 1) ≤ 1) :
    |(1 - p * y ^ (k - 1)) ^ (H.innerStaticConflictUnion F).card -
        (1 - p * y ^ (k - 1)) ^ (F.card * k * D)| ≤
      ((F.card * k * D - (H.innerStaticConflictUnion F).card : ℕ) : ℝ) *
        (p * y ^ (k - 1)) := by
  have hbase : 1 - p * y ^ (k - 1) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr hpY
    · exact sub_le_self _ (mul_nonneg hp₀ (pow_nonneg hy.1 _))
  simpa using abs_pow_sub_pow_le_exponent_gap hbase
    (H.card_innerStaticConflictUnion_le F hk hunif hF hdeg)

/-- In an exactly regular hypergraph the exponent deficit is itself bounded
by the family-removal and low-codegree incidence errors. -/
lemma card_innerStaticConflictUnion_deficit_le
    (H : FiniteHypergraph V E) (F : Finset E)
    {k D C : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) (hF : H.IsMatching F)
    (hlow : ∀ v ∈ H.familySupport F, D ≤ H.edgeDegree v)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C) :
    F.card * k * D - (H.innerStaticConflictUnion F).card ≤
      F.card + (F.card * k) ^ 2 * C * k := by
  have h := H.card_mul_uniform_degreeLower_le_staticConflict_add_error
    F hk hunif hF hlow hpair
  omega

/-- Fully explicit exponent-replacement error.  After setting `p=beta/D`
and `C≤eta*D+1`, the right side is a fixed polynomial times
`eta + 1/D`. -/
theorem staticConflictProfile_exponent_close_explicit
    (H : FiniteHypergraph V E) (F : Finset E)
    {k D C : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) (hF : H.IsMatching F)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hlow : ∀ v ∈ H.familySupport F, D ≤ H.edgeDegree v)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {p y : ℝ} (hp₀ : 0 ≤ p) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpY : p * y ^ (k - 1) ≤ 1) :
    |(1 - p * y ^ (k - 1)) ^ (H.innerStaticConflictUnion F).card -
        (1 - p * y ^ (k - 1)) ^ (F.card * k * D)| ≤
      ((F.card + (F.card * k) ^ 2 * C * k : ℕ) : ℝ) *
        (p * y ^ (k - 1)) := by
  have hmain := H.staticConflictProfile_exponent_close F hk hunif hF
    hdeg hp₀ hy hpY
  have hdeficit := H.card_innerStaticConflictUnion_deficit_le
    F hk hunif hF hlow hpair
  exact hmain.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast hdeficit)
    (mul_nonneg hp₀ (pow_nonneg hy.1 _)))

/-- The fixed-family signed expansion centered at the *ideal* regular
conflict exponent.  This is the form that can be summed over all dominant
outer families: its center depends only on `|F|`, while every deviation is
kept on the explicit right-hand side. -/
theorem staticConflictSignedJointMass_close_idealExponent
    (H : FiniteHypergraph V E) (w : Finset E → ℝ)
    (hw₀ : ∀ S, 0 ≤ w S) (hw : ∑ S, w S = 1)
    (r : ℕ) (M : Finset E) (A : Finset V) (F : Finset E)
    {k D C : ℕ} (hk : 0 < k) (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hlow : ∀ v ∈ H.vertexSet, D ≤ H.edgeDegree v)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (hF : H.IsMatching F) (hFsingle : F ⊆ H.singleMeetingEdges A)
    (p y : ℝ) (hp₀ : 0 ≤ p) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpY : p * y ^ (k - 1) ≤ 1)
    (orderError : ℕ → ℝ) (herror₀ : ∀ a, 0 ≤ orderError a)
    (hprofile : ∀ S : Finset V,
      |H.innerJointUncoveredMass w r M S - y ^ S.card| ≤
        orderError S.card) :
    |(∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
        (-p) ^ Q.card *
          H.innerJointUncoveredMass w r M
            (A ∪ H.familySupport (F ∪ Q))) -
        y ^ (A.card + F.card * (k - 1)) *
          (1 - p * y ^ (k - 1)) ^ (F.card * k * D)| ≤
      (∑ q ∈ range ((H.innerStaticConflictUnion F).card + 1),
        |p| ^ q *
          (((H.innerStaticConflictUnion F).card.choose q : ℝ) *
              orderError
                (A.card + F.card * (k - 1) + q * (k - 1)) +
            ((H.exceptionalProfileSubfamilies
              (A ∪ H.familySupport F)
              (H.innerStaticConflictUnion F) q).card : ℝ))) +
        y ^ (A.card + F.card * (k - 1)) *
          (((F.card + (F.card * k) ^ 2 * C * k : ℕ) : ℝ) *
            (p * y ^ (k - 1))) := by
  let actual : ℝ :=
    ∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
      (-p) ^ Q.card *
        H.innerJointUncoveredMass w r M
          (A ∪ H.familySupport (F ∪ Q))
  let b : ℕ := A.card + F.card * (k - 1)
  let z : ℝ := 1 - p * y ^ (k - 1)
  let qError : ℝ :=
    ∑ q ∈ range ((H.innerStaticConflictUnion F).card + 1),
      |p| ^ q *
        (((H.innerStaticConflictUnion F).card.choose q : ℝ) *
            orderError (b + q * (k - 1)) +
          ((H.exceptionalProfileSubfamilies
            (A ∪ H.familySupport F)
            (H.innerStaticConflictUnion F) q).card : ℝ))
  let exponentError : ℝ :=
    ((F.card + (F.card * k) ^ 2 * C * k : ℕ) : ℝ) *
      (p * y ^ (k - 1))
  have hfamilyVertex : H.familySupport F ⊆ H.vertexSet := by
    intro v hv
    obtain ⟨e, _heF, hve⟩ := (H.mem_familySupport F v).1 hv
    exact H.support_subset_vertexSet e hve
  have hfixed : |actual - y ^ b * z ^ (H.innerStaticConflictUnion F).card| ≤
      qError := by
    simpa [actual, b, z, qError] using
      H.staticConflictSignedJointMass_close w hw₀ hw r M A F hk hunif
        hF hFsingle p y hy orderError herror₀ hprofile
  have hexponent :
      |z ^ (H.innerStaticConflictUnion F).card - z ^ (F.card * k * D)| ≤
        exponentError := by
    simpa [z, exponentError] using
      H.staticConflictProfile_exponent_close_explicit F hk hunif hF hdeg
        (fun v hv ↦ hlow v (hfamilyVertex hv)) hpair hp₀ hy hpY
  have hyPow₀ : 0 ≤ y ^ b := pow_nonneg hy.1 b
  have hscaled :
      |y ^ b * z ^ (H.innerStaticConflictUnion F).card -
          y ^ b * z ^ (F.card * k * D)| ≤ y ^ b * exponentError := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hyPow₀]
    exact mul_le_mul_of_nonneg_left hexponent hyPow₀
  calc
    |actual - y ^ b * z ^ (F.card * k * D)| =
        |(actual - y ^ b * z ^ (H.innerStaticConflictUnion F).card) +
          (y ^ b * z ^ (H.innerStaticConflictUnion F).card -
            y ^ b * z ^ (F.card * k * D))| := by
      congr 1
      ring
    _ ≤ |actual - y ^ b * z ^ (H.innerStaticConflictUnion F).card| +
          |y ^ b * z ^ (H.innerStaticConflictUnion F).card -
            y ^ b * z ^ (F.card * k * D)| := abs_add_le _ _
    _ ≤ qError + y ^ b * exponentError := add_le_add hfixed hscaled

/-- The explicit error budget for one dominant outer family after replacing
its static isolation exponent by the ideal regular exponent. -/
def staticConflictSignedError
    (H : FiniteHypergraph V E) (A : Finset V) (F : Finset E)
    (k C : ℕ) (p y : ℝ) (orderError : ℕ → ℝ) : ℝ :=
  (∑ q ∈ range ((H.innerStaticConflictUnion F).card + 1),
    |p| ^ q *
      (((H.innerStaticConflictUnion F).card.choose q : ℝ) *
          orderError
            (A.card + F.card * (k - 1) + q * (k - 1)) +
        ((H.exceptionalProfileSubfamilies
          (A ∪ H.familySupport F)
          (H.innerStaticConflictUnion F) q).card : ℝ))) +
    y ^ (A.card + F.card * (k - 1)) *
      (((F.card + (F.card * k) ^ 2 * C * k : ℕ) : ℝ) *
        (p * y ^ (k - 1)))

/-- Sampling-weighted version of the ideal-exponent fixed-family estimate.
This is exactly the termwise hypothesis consumed by
`averagedMoment_close_of_goodFamily_close`. -/
theorem weightedStaticConflictSignedJointMass_close_idealExponent
    (H : FiniteHypergraph V E)
    (r : ℕ) (M : Finset E) (A : Finset V) (F : Finset E)
    {k D C : ℕ} (hk : 0 < k) (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hlow : ∀ v ∈ H.vertexSet, D ≤ H.edgeDegree v)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (hF : H.IsMatching F) (hFsingle : F ⊆ H.singleMeetingEdges A)
    (p y : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpY : p * y ^ (k - 1) ≤ 1)
    (orderError : ℕ → ℝ) (herror₀ : ∀ a, 0 ≤ orderError a)
    (hprofile : ∀ S : Finset V,
      |H.innerJointUncoveredMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M S -
          y ^ S.card| ≤ orderError S.card) :
    |p ^ F.card *
          (∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
            (-p) ^ Q.card *
              H.innerJointUncoveredMass
                (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M
                (A ∪ H.familySupport (F ∪ Q))) -
        p ^ F.card *
          (y ^ (A.card + F.card * (k - 1)) *
            (1 - p * y ^ (k - 1)) ^ (F.card * k * D))| ≤
      p ^ F.card *
        H.staticConflictSignedError A F k C p y orderError := by
  let w : Finset E → ℝ :=
    FiniteNibble.bernoulliMass univ (fun _ ↦ p)
  have hw₀ (S : Finset E) : 0 ≤ w S :=
    FiniteNibble.bernoulliMass_nonneg (subset_univ S)
      (fun _ _ ↦ hp₀) (fun _ _ ↦ hp₁)
  have hw : ∑ S, w S = 1 := by
    simpa [w] using FiniteNibble.sum_bernoulliMass
      (univ : Finset E) (fun _ ↦ p)
  have hraw := H.staticConflictSignedJointMass_close_idealExponent
    w hw₀ hw r M A F hk hunif hdeg hlow hpair hF hFsingle
      p y hp₀ hy hpY orderError herror₀ hprofile
  have hpPow₀ : 0 ≤ p ^ F.card := pow_nonneg hp₀ _
  rw [← mul_sub, abs_mul, abs_of_nonneg hpPow₀]
  exact mul_le_mul_of_nonneg_left
    (by simpa [staticConflictSignedError] using hraw) hpPow₀

/-- Cutoff analogue of `staticConflictSignedError`. -/
def staticConflictSignedErrorCutoff
    (H : FiniteHypergraph V E) (A : Finset V) (F : Finset E)
    (k C : ℕ) (p y : ℝ) (Qcut : ℕ)
    (orderError : ℕ → ℝ) : ℝ :=
  (∑ q ∈ range ((H.innerStaticConflictUnion F).card + 1),
    |p| ^ q *
      (if q ≤ Qcut then
        ((H.innerStaticConflictUnion F).card.choose q : ℝ) *
            orderError
              (A.card + F.card * (k - 1) + q * (k - 1)) +
          ((H.exceptionalProfileSubfamilies
            (A ∪ H.familySupport F)
            (H.innerStaticConflictUnion F) q).card : ℝ)
      else ((H.innerStaticConflictUnion F).card.choose q : ℝ))) +
    y ^ (A.card + F.card * (k - 1)) *
      (((F.card + (F.card * k) ^ 2 * C * k : ℕ) : ℝ) *
        (p * y ^ (k - 1)))

/-- Sampling-weighted fixed-family estimate with a finite conflict-order
cutoff and the ideal regular isolation exponent. -/
theorem weightedStaticConflictSignedJointMass_close_cutoff
    (H : FiniteHypergraph V E)
    (r : ℕ) (M : Finset E) (A : Finset V) (F : Finset E)
    {k D C : ℕ} (hk : 0 < k) (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hlow : ∀ v ∈ H.vertexSet, D ≤ H.edgeDegree v)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (hA : A ⊆ H.vertexSet)
    (hF : H.IsMatching F) (hFsingle : F ⊆ H.singleMeetingEdges A)
    (p y : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpY : p * y ^ (k - 1) ≤ 1)
    (Qcut : ℕ) (orderError : ℕ → ℝ)
    (herror₀ : ∀ a, 0 ≤ orderError a)
    (hprofile : ∀ S : Finset V,
      S ⊆ H.vertexSet →
      S.card ≤ A.card + F.card * (k - 1) + Qcut * (k - 1) →
      |H.innerJointUncoveredMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M S -
          y ^ S.card| ≤ orderError S.card) :
    |p ^ F.card *
          (∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
            (-p) ^ Q.card *
              H.innerJointUncoveredMass
                (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M
                (A ∪ H.familySupport (F ∪ Q))) -
        p ^ F.card *
          (y ^ (A.card + F.card * (k - 1)) *
            (1 - p * y ^ (k - 1)) ^ (F.card * k * D))| ≤
      p ^ F.card *
        H.staticConflictSignedErrorCutoff
          A F k C p y Qcut orderError := by
  let w : Finset E → ℝ :=
    FiniteNibble.bernoulliMass univ (fun _ ↦ p)
  let actual : ℝ :=
    ∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
      (-p) ^ Q.card *
        H.innerJointUncoveredMass w r M
          (A ∪ H.familySupport (F ∪ Q))
  let b := A.card + F.card * (k - 1)
  let z := 1 - p * y ^ (k - 1)
  let qError : ℝ :=
    ∑ q ∈ range ((H.innerStaticConflictUnion F).card + 1),
      |p| ^ q *
        (if q ≤ Qcut then
          ((H.innerStaticConflictUnion F).card.choose q : ℝ) *
              orderError (b + q * (k - 1)) +
            ((H.exceptionalProfileSubfamilies
              (A ∪ H.familySupport F)
              (H.innerStaticConflictUnion F) q).card : ℝ)
        else ((H.innerStaticConflictUnion F).card.choose q : ℝ))
  let exponentError : ℝ :=
    ((F.card + (F.card * k) ^ 2 * C * k : ℕ) : ℝ) *
      (p * y ^ (k - 1))
  have hw₀ (S : Finset E) : 0 ≤ w S :=
    FiniteNibble.bernoulliMass_nonneg (subset_univ S)
      (fun _ _ ↦ hp₀) (fun _ _ ↦ hp₁)
  have hw : ∑ S, w S = 1 := by
    simpa [w] using FiniteNibble.sum_bernoulliMass
      (univ : Finset E) (fun _ ↦ p)
  have hfixed :
      |actual - y ^ b * z ^ (H.innerStaticConflictUnion F).card| ≤
        qError := by
    simpa [w, actual, b, z, qError] using
      H.staticConflictSignedJointMass_close_cutoff
        w hw₀ hw r M A F hk hunif hA hF hFsingle p y hy Qcut
          orderError herror₀ hprofile
  have hfamilyVertex : H.familySupport F ⊆ H.vertexSet := by
    intro v hv
    obtain ⟨e, _heF, hve⟩ := (H.mem_familySupport F v).1 hv
    exact H.support_subset_vertexSet e hve
  have hexponent :
      |z ^ (H.innerStaticConflictUnion F).card - z ^ (F.card * k * D)| ≤
        exponentError := by
    simpa [z, exponentError] using
      H.staticConflictProfile_exponent_close_explicit F hk hunif hF hdeg
        (fun v hv ↦ hlow v (hfamilyVertex hv)) hpair hp₀ hy hpY
  have hyPow₀ : 0 ≤ y ^ b := pow_nonneg hy.1 _
  have hscaled :
      |y ^ b * z ^ (H.innerStaticConflictUnion F).card -
          y ^ b * z ^ (F.card * k * D)| ≤ y ^ b * exponentError := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hyPow₀]
    exact mul_le_mul_of_nonneg_left hexponent hyPow₀
  have hraw : |actual - y ^ b * z ^ (F.card * k * D)| ≤
      qError + y ^ b * exponentError := by
    calc
      |actual - y ^ b * z ^ (F.card * k * D)| =
          |(actual - y ^ b * z ^ (H.innerStaticConflictUnion F).card) +
            (y ^ b * z ^ (H.innerStaticConflictUnion F).card -
              y ^ b * z ^ (F.card * k * D))| := by
        congr 1
        ring
      _ ≤ |actual - y ^ b * z ^ (H.innerStaticConflictUnion F).card| +
            |y ^ b * z ^ (H.innerStaticConflictUnion F).card -
              y ^ b * z ^ (F.card * k * D)| := abs_add_le _ _
      _ ≤ qError + y ^ b * exponentError := add_le_add hfixed hscaled
  have hpPow₀ : 0 ≤ p ^ F.card := pow_nonneg hp₀ _
  rw [← mul_sub, abs_mul, abs_of_nonneg hpPow₀]
  exact mul_le_mul_of_nonneg_left
    (by simpa [w, actual, b, z, qError, exponentError,
      staticConflictSignedErrorCutoff] using hraw) hpPow₀

/-- The live conflict union is the liveness filter of the corresponding
static conflict union. -/
lemma innerLiveConflictUnion_eq_filter_innerStaticConflictUnion
    (H : FiniteHypergraph V E) (M F : Finset E) :
    H.innerLiveConflictUnion M F =
      (H.innerStaticConflictUnion F).filter (H.InnerLive M) := by
  ext g
  constructor
  · intro hg
    obtain ⟨e, heF, hge⟩ :=
      (H.mem_innerLiveConflictUnion M F g).1 hg
    have hgeData := (H.mem_innerLiveConflictNeighbors M e g).1 hge
    exact mem_filter.mpr ⟨
      (H.mem_innerStaticConflictUnion F g).2
        ⟨e, heF, hgeData.1.symm, hgeData.2.2⟩,
      hgeData.2.1⟩
  · intro hg
    have hgData := mem_filter.mp hg
    obtain ⟨e, heF, heg⟩ :=
      (H.mem_innerStaticConflictUnion F g).1 hgData.1
    exact (H.mem_innerLiveConflictUnion M F g).2
      ⟨e, heF, (H.mem_innerLiveConflictNeighbors M e g).2
        ⟨heg.1.symm, hgData.2, heg.2⟩⟩

/-- Exact powerset expansion of the absent-live-conflict product.  The
chosen static subfamily `Q` contributes only when all of its edges are live
in the old state. -/
lemma prod_one_sub_innerLiveConflictUnion_eq_sum_powerset
    (H : FiniteHypergraph V E) (M F : Finset E) (p : ℝ) :
    (∏ g ∈ H.innerLiveConflictUnion M F, (1 - p)) =
      ∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
        (-p) ^ Q.card *
          if ∀ g ∈ Q, H.InnerLive M g then 1 else 0 := by
  rw [H.innerLiveConflictUnion_eq_filter_innerStaticConflictUnion M F]
  let C := H.innerStaticConflictUnion F
  calc
    (∏ g ∈ C.filter (H.InnerLive M), (1 - p)) =
        ∏ g ∈ C,
          (1 + if H.InnerLive M g then -p else 0) := by
      rw [prod_filter]
      apply prod_congr rfl
      intro g _
      by_cases hg : H.InnerLive M g <;> simp [hg, sub_eq_add_neg]
    _ = ∑ Q ∈ C.powerset,
          ∏ g ∈ Q, (if H.InnerLive M g then -p else 0) := by
      rw [prod_one_add]
    _ = ∑ Q ∈ C.powerset,
          (-p) ^ Q.card *
            if ∀ g ∈ Q, H.InnerLive M g then 1 else 0 := by
      apply sum_congr rfl
      intro Q _
      by_cases hQ : ∀ g ∈ Q, H.InnerLive M g
      · rw [if_pos hQ, mul_one]
        calc
          (∏ g ∈ Q, (if H.InnerLive M g then -p else 0)) =
              ∏ _g ∈ Q, (-p) := by
            apply prod_congr rfl
            intro g hg
            rw [if_pos (hQ g hg)]
          _ = (-p) ^ Q.card := by simp
      · push_neg at hQ
        obtain ⟨g, hgQ, hgNotLive⟩ := hQ
        have hprodZero :
            (∏ z ∈ Q, (if H.InnerLive M z then -p else 0)) = 0 := by
          apply prod_eq_zero hgQ
          rw [if_neg hgNotLive]
        rw [hprodZero, if_neg]
        · ring
        · push_neg
          exact ⟨g, hgQ, hgNotLive⟩

/-- Exact static-conflict expansion of simultaneous isolated acceptance
for a matching family. -/
theorem innerNewAcceptanceFamilyMass_const_eq_sum_staticConflict
    (H : FiniteHypergraph V E) (M F : Finset E) (p : ℝ)
    (hF : H.IsMatching F) :
    H.innerNewAcceptanceFamilyMass M (fun _ ↦ p) F =
      if ∀ e ∈ F, H.InnerLive M e then
        p ^ F.card *
          (∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
            (-p) ^ Q.card *
              if ∀ g ∈ Q, H.InnerLive M g then 1 else 0)
      else 0 := by
  rw [H.innerNewAcceptanceFamilyMass_eq M (fun _ ↦ p) F hF]
  by_cases hLive : ∀ e ∈ F, H.InnerLive M e
  · rw [if_pos hLive, if_pos hLive]
    rw [prod_const]
    rw [H.prod_one_sub_innerLiveConflictUnion_eq_sum_powerset M F p]
  · rw [if_neg hLive, if_neg hLive]

/-- After averaging over the old trajectory, the exact static-conflict
expansion becomes a signed double sum of enlarged joint-uncovered masses.
This retains the cancellation inside the isolation product which is lost
by a uniform cardinality squeeze. -/
theorem averagedInnerNewAcceptedMeetingChooseMoment_eq_staticConflictExpansion
    (H : FiniteHypergraph V E) {k : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) (p : ℝ)
    (r : ℕ) (M : Finset E) (A : Finset V) (j : ℕ) :
    H.averagedInnerNewAcceptedMeetingChooseMoment
        (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M A j =
      ∑ F ∈ H.matchingMeetingFamilies A j,
        p ^ F.card *
          ∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
            (-p) ^ Q.card *
              H.innerJointUncoveredMass
                (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M
                (A ∪ (F ∪ Q).biUnion H.support) := by
  let w : Finset E → ℝ :=
    FiniteNibble.bernoulliMass univ (fun _ ↦ p)
  let state : (Fin r → Finset E) → Finset E := fun X ↦
    (List.ofFn X).foldl H.innerStep M
  let oldIndicator : (Fin r → Finset E) → ℝ := fun X ↦
    if ∀ v ∈ A, H.UncoveredBy (state X) v then 1 else 0
  let familyLiveIndicator : Finset E → (Fin r → Finset E) → ℝ :=
    fun G X ↦ if ∀ e ∈ G, H.InnerLive (state X) e then 1 else 0
  have hfamily (F : Finset E) (hFmem : F ∈ H.matchingMeetingFamilies A j) :
      (∑ X : Fin r → Finset E,
          FiniteProduct.productMass w X * oldIndicator X *
            H.innerNewAcceptanceFamilyMass (state X) (fun _ ↦ p) F) =
        p ^ F.card *
          ∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
            (-p) ^ Q.card *
              H.innerJointUncoveredMass w r M
                (A ∪ (F ∪ Q).biUnion H.support) := by
    have hFmatch : H.IsMatching F :=
      (H.mem_matchingMeetingFamilies A j F).1 hFmem |>.2.2
    have hUnionLive (X : Fin r → Finset E) (Q : Finset E) :
        (∀ e ∈ F ∪ Q, H.InnerLive (state X) e) ↔
          (∀ e ∈ F, H.InnerLive (state X) e) ∧
            ∀ e ∈ Q, H.InnerLive (state X) e := by
      constructor
      · intro hall
        exact ⟨
          fun e he ↦ hall e (mem_union_left Q he),
          fun e he ↦ hall e (mem_union_right F he)⟩
      · rintro ⟨hF, hQ⟩ e he
        rcases mem_union.mp he with heF | heQ
        · exact hF e heF
        · exact hQ e heQ
    have hpoint (X : Fin r → Finset E) :
        H.innerNewAcceptanceFamilyMass (state X) (fun _ ↦ p) F =
          p ^ F.card *
            ∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
              (-p) ^ Q.card * familyLiveIndicator (F ∪ Q) X := by
      rw [H.innerNewAcceptanceFamilyMass_const_eq_sum_staticConflict
        (state X) F p hFmatch]
      by_cases hFLive : ∀ e ∈ F, H.InnerLive (state X) e
      · rw [if_pos hFLive]
        congr 1
        apply sum_congr rfl
        intro Q _
        have hiff : (∀ e ∈ F ∪ Q, H.InnerLive (state X) e) ↔
            (∀ e ∈ Q, H.InnerLive (state X) e) := by
          constructor
          · intro hall
            exact (hUnionLive X Q).1 hall |>.2
          · intro hQ
            exact (hUnionLive X Q).2 ⟨hFLive, hQ⟩
        change (-p) ^ Q.card *
            (if ∀ g ∈ Q, H.InnerLive (state X) g then 1 else 0) =
          (-p) ^ Q.card *
            (if ∀ e ∈ F ∪ Q, H.InnerLive (state X) e then 1 else 0)
        by_cases hQ : ∀ e ∈ Q, H.InnerLive (state X) e
        · rw [if_pos hQ, if_pos (hiff.mpr hQ)]
        · rw [if_neg hQ, if_neg (fun h ↦ hQ (hiff.mp h))]
      · rw [if_neg hFLive]
        symm
        apply mul_eq_zero_of_right
        apply sum_eq_zero
        intro Q _
        have hnUnion : ¬∀ e ∈ F ∪ Q, H.InnerLive (state X) e :=
          fun hall ↦ hFLive (hUnionLive X Q |>.1 hall |>.1)
        change (-p) ^ Q.card *
            (if ∀ e ∈ F ∪ Q, H.InnerLive (state X) e then 1 else 0) = 0
        rw [if_neg hnUnion, mul_zero]
    have hliveAverage (Q : Finset E) :
        (∑ X : Fin r → Finset E,
          FiniteProduct.productMass w X * oldIndicator X *
            familyLiveIndicator (F ∪ Q) X) =
          H.innerJointUncoveredMass w r M
            (A ∪ (F ∪ Q).biUnion H.support) := by
      simpa [w, state, oldIndicator, familyLiveIndicator] using
        H.sum_productMass_mul_jointUncovered_mul_familyLive
          hk hunif w r M A (F ∪ Q)
    calc
      (∑ X : Fin r → Finset E,
          FiniteProduct.productMass w X * oldIndicator X *
            H.innerNewAcceptanceFamilyMass (state X) (fun _ ↦ p) F) =
          ∑ X : Fin r → Finset E,
            ∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
              p ^ F.card * (-p) ^ Q.card *
                (FiniteProduct.productMass w X * oldIndicator X *
                  familyLiveIndicator (F ∪ Q) X) := by
        apply sum_congr rfl
        intro X _
        rw [hpoint X]
        simp_rw [mul_sum]
        apply sum_congr rfl
        intro Q _
        ring
      _ = ∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
            ∑ X : Fin r → Finset E,
              p ^ F.card * (-p) ^ Q.card *
                (FiniteProduct.productMass w X * oldIndicator X *
                  familyLiveIndicator (F ∪ Q) X) := by
        rw [sum_comm]
      _ = p ^ F.card *
          ∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
            (-p) ^ Q.card *
              H.innerJointUncoveredMass w r M
                (A ∪ (F ∪ Q).biUnion H.support) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro Q _
        rw [← mul_sum, hliveAverage Q]
        ring
  rw [H.averagedInnerNewAcceptedMeetingChooseMoment_eq_sum_matching]
  change
    (∑ X : Fin r → Finset E,
      FiniteProduct.productMass w X * oldIndicator X *
        ∑ F ∈ H.matchingMeetingFamilies A j,
          H.innerNewAcceptanceFamilyMass (state X) (fun _ ↦ p) F) = _
  calc
    (∑ X : Fin r → Finset E,
      FiniteProduct.productMass w X * oldIndicator X *
        ∑ F ∈ H.matchingMeetingFamilies A j,
          H.innerNewAcceptanceFamilyMass (state X) (fun _ ↦ p) F) =
        ∑ F ∈ H.matchingMeetingFamilies A j,
          ∑ X : Fin r → Finset E,
            FiniteProduct.productMass w X * oldIndicator X *
              H.innerNewAcceptanceFamilyMass
                (state X) (fun _ ↦ p) F := by
      simp_rw [mul_sum]
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro F hF
      exact hfamily F hF

/-- Per-family form of the exact static-conflict expansion.  Keeping this
identity separate from the moment sum lets exceptional outer families be
bounded by their genuine nonnegative acceptance probability. -/
theorem averagedInnerNewAcceptanceFamilyMass_eq_staticConflictExpansion
    (H : FiniteHypergraph V E) {k : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k) (p : ℝ)
    (r : ℕ) (M : Finset E) (A : Finset V) (F : Finset E)
    (hF : H.IsMatching F) :
    (∑ X : Fin r → Finset E,
        FiniteProduct.productMass
            (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) X *
          (if ∀ v ∈ A,
              H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
            then 1 else 0) *
          H.innerNewAcceptanceFamilyMass
            ((List.ofFn X).foldl H.innerStep M) (fun _ ↦ p) F) =
      p ^ F.card *
        ∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
          (-p) ^ Q.card *
            H.innerJointUncoveredMass
              (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M
              (A ∪ (F ∪ Q).biUnion H.support) := by
  let w : Finset E → ℝ :=
    FiniteNibble.bernoulliMass univ (fun _ ↦ p)
  let state : (Fin r → Finset E) → Finset E := fun X ↦
    (List.ofFn X).foldl H.innerStep M
  let oldIndicator : (Fin r → Finset E) → ℝ := fun X ↦
    if ∀ v ∈ A, H.UncoveredBy (state X) v then 1 else 0
  let familyLiveIndicator : Finset E → (Fin r → Finset E) → ℝ :=
    fun G X ↦ if ∀ e ∈ G, H.InnerLive (state X) e then 1 else 0
  have hUnionLive (X : Fin r → Finset E) (Q : Finset E) :
      (∀ e ∈ F ∪ Q, H.InnerLive (state X) e) ↔
        (∀ e ∈ F, H.InnerLive (state X) e) ∧
          ∀ e ∈ Q, H.InnerLive (state X) e := by
    constructor
    · intro hall
      exact ⟨
        fun e he ↦ hall e (mem_union_left Q he),
        fun e he ↦ hall e (mem_union_right F he)⟩
    · rintro ⟨hFLive, hQ⟩ e he
      rcases mem_union.mp he with heF | heQ
      · exact hFLive e heF
      · exact hQ e heQ
  have hpoint (X : Fin r → Finset E) :
      H.innerNewAcceptanceFamilyMass (state X) (fun _ ↦ p) F =
        p ^ F.card *
          ∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
            (-p) ^ Q.card * familyLiveIndicator (F ∪ Q) X := by
    rw [H.innerNewAcceptanceFamilyMass_const_eq_sum_staticConflict
      (state X) F p hF]
    by_cases hFLive : ∀ e ∈ F, H.InnerLive (state X) e
    · rw [if_pos hFLive]
      congr 1
      apply sum_congr rfl
      intro Q _
      have hiff : (∀ e ∈ F ∪ Q, H.InnerLive (state X) e) ↔
          (∀ e ∈ Q, H.InnerLive (state X) e) := by
        constructor
        · intro hall
          exact (hUnionLive X Q).1 hall |>.2
        · intro hQ
          exact (hUnionLive X Q).2 ⟨hFLive, hQ⟩
      change (-p) ^ Q.card *
          (if ∀ g ∈ Q, H.InnerLive (state X) g then 1 else 0) =
        (-p) ^ Q.card *
          (if ∀ e ∈ F ∪ Q, H.InnerLive (state X) e then 1 else 0)
      by_cases hQ : ∀ e ∈ Q, H.InnerLive (state X) e
      · rw [if_pos hQ, if_pos (hiff.mpr hQ)]
      · rw [if_neg hQ, if_neg (fun h ↦ hQ (hiff.mp h))]
    · rw [if_neg hFLive]
      symm
      apply mul_eq_zero_of_right
      apply sum_eq_zero
      intro Q _
      have hnUnion : ¬∀ e ∈ F ∪ Q, H.InnerLive (state X) e :=
        fun hall ↦ hFLive (hUnionLive X Q |>.1 hall |>.1)
      change (-p) ^ Q.card *
          (if ∀ e ∈ F ∪ Q, H.InnerLive (state X) e then 1 else 0) = 0
      rw [if_neg hnUnion, mul_zero]
  have hliveAverage (Q : Finset E) :
      (∑ X : Fin r → Finset E,
        FiniteProduct.productMass w X * oldIndicator X *
          familyLiveIndicator (F ∪ Q) X) =
        H.innerJointUncoveredMass w r M
          (A ∪ (F ∪ Q).biUnion H.support) := by
    simpa [w, state, oldIndicator, familyLiveIndicator] using
      H.sum_productMass_mul_jointUncovered_mul_familyLive
        hk hunif w r M A (F ∪ Q)
  change
    (∑ X : Fin r → Finset E,
      FiniteProduct.productMass w X * oldIndicator X *
        H.innerNewAcceptanceFamilyMass (state X) (fun _ ↦ p) F) = _
  calc
    (∑ X : Fin r → Finset E,
        FiniteProduct.productMass w X * oldIndicator X *
          H.innerNewAcceptanceFamilyMass (state X) (fun _ ↦ p) F) =
        ∑ X : Fin r → Finset E,
          ∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
            p ^ F.card * (-p) ^ Q.card *
              (FiniteProduct.productMass w X * oldIndicator X *
                familyLiveIndicator (F ∪ Q) X) := by
      apply sum_congr rfl
      intro X _
      rw [hpoint X]
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro Q _
      ring
    _ = ∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
          ∑ X : Fin r → Finset E,
            p ^ F.card * (-p) ^ Q.card *
              (FiniteProduct.productMass w X * oldIndicator X *
                familyLiveIndicator (F ∪ Q) X) := by
      rw [sum_comm]
    _ = p ^ F.card *
        ∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
          (-p) ^ Q.card *
            H.innerJointUncoveredMass w r M
              (A ∪ (F ∪ Q).biUnion H.support) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro Q _
      rw [← mul_sum, hliveAverage Q]
      ring

/-- A matching family's exact signed contribution is nevertheless a
genuine probability mass after multiplication by its sampling factor.  In
particular, an exceptional outer family costs at most `p^|F|`; no absolute
value of the internal alternating expansion is charged. -/
theorem staticConflictFamilyContribution_mem_Icc
    (H : FiniteHypergraph V E) {k D : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (r : ℕ) (M : Finset E) (A : Finset V) (F : Finset E)
    (hF : H.IsMatching F) :
    p ^ F.card *
        (∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
          (-p) ^ Q.card *
            H.innerJointUncoveredMass
              (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M
              (A ∪ (F ∪ Q).biUnion H.support)) ∈
      Set.Icc 0 (p ^ F.card) := by
  have heq := H.averagedInnerNewAcceptanceFamilyMass_eq_staticConflictExpansion
    hk hunif p r M A F hF
  rw [← heq]
  have havg :=
    H.sum_productMass_mul_jointUncovered_mul_innerNewAcceptanceFamilyMass_const_mem_Icc
      hk hunif hdeg hp₀ hp₁ r M A F hF
  have hjoint := H.innerJointUncoveredMass_bernoulli_mem_Icc
    (fun _ ↦ p) (fun _ ↦ hp₀) (fun _ ↦ hp₁) r M
      (A ∪ F.biUnion H.support)
  have hpPow₀ : 0 ≤ p ^ F.card := pow_nonneg hp₀ _
  have honeSubPow₀ : 0 ≤ (1 - p) ^ (F.card * k * D) :=
    pow_nonneg (sub_nonneg.mpr hp₁) _
  constructor
  · exact (mul_nonneg
      (mul_nonneg hpPow₀ honeSubPow₀) hjoint.1).trans havg.1
  · simpa using havg.2.trans
      (mul_le_mul_of_nonneg_left hjoint.2 hpPow₀)

/-- A reusable finite-sum aggregation lemma.  The good terms are compared
termwise with one common center, the deficit in the number of good terms is
charged separately, and bad terms are charged by their actual nonnegative
mass bound. -/
lemma abs_sum_partition_sub_ideal_mul_le
    {Omega : Type*} [DecidableEq Omega]
    (S good bad : Finset Omega) (value error : Omega → ℝ)
    (ideal center countError badBound : ℝ)
    (hpartition : S = good ∪ bad) (hdisjoint : Disjoint good bad)
    (hcenter₀ : 0 ≤ center)
    (hgood : ∀ x ∈ good, |value x - center| ≤ error x)
    (hbad : ∀ x ∈ bad, value x ∈ Set.Icc 0 badBound)
    (hcardUpper : ((good.card : ℕ) : ℝ) ≤ ideal)
    (hcardDeficit : ideal - ((good.card : ℕ) : ℝ) ≤ countError) :
    |(∑ x ∈ S, value x) - ideal * center| ≤
      (∑ x ∈ good, error x) + countError * center +
        ((bad.card : ℕ) : ℝ) * badBound := by
  rw [hpartition, sum_union hdisjoint]
  have hgoodAbs :
      |∑ x ∈ good, (value x - center)| ≤ ∑ x ∈ good, error x := by
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x hx ↦ hgood x hx)
  have hcountSign :
      (((good.card : ℕ) : ℝ) - ideal) * center ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcardUpper) hcenter₀
  have hcountAbs :
      |(((good.card : ℕ) : ℝ) - ideal) * center| ≤
        countError * center := by
    rw [abs_of_nonpos hcountSign]
    have := mul_le_mul_of_nonneg_right hcardDeficit hcenter₀
    nlinarith
  have hbad₀ : 0 ≤ ∑ x ∈ bad, value x :=
    sum_nonneg fun x hx ↦ (hbad x hx).1
  have hbadUpper :
      ∑ x ∈ bad, value x ≤ ((bad.card : ℕ) : ℝ) * badBound := by
    calc
      (∑ x ∈ bad, value x) ≤ ∑ _x ∈ bad, badBound := by
        exact sum_le_sum fun x hx ↦ (hbad x hx).2
      _ = ((bad.card : ℕ) : ℝ) * badBound := by simp
  have hrearrange :
      (∑ x ∈ good, value x) + (∑ x ∈ bad, value x) -
          ideal * center =
        (∑ x ∈ good, (value x - center)) +
          ((((good.card : ℕ) : ℝ) - ideal) * center) +
          (∑ x ∈ bad, value x) := by
    simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
    ring
  rw [hrearrange]
  calc
    |(∑ x ∈ good, (value x - center)) +
        ((((good.card : ℕ) : ℝ) - ideal) * center) +
        (∑ x ∈ bad, value x)| ≤
      |∑ x ∈ good, (value x - center)| +
        |(((good.card : ℕ) : ℝ) - ideal) * center| +
        |∑ x ∈ bad, value x| := by
      linarith [abs_add_le
        (∑ x ∈ good, (value x - center))
        ((((good.card : ℕ) : ℝ) - ideal) * center),
        abs_add_le
          ((∑ x ∈ good, (value x - center)) +
            ((((good.card : ℕ) : ℝ) - ideal) * center))
          (∑ x ∈ bad, value x)]
    _ ≤ (∑ x ∈ good, error x) + countError * center +
        ((bad.card : ℕ) : ℝ) * badBound := by
      rw [abs_of_nonneg hbad₀]
      exact add_le_add (add_le_add hgoodAbs hcountAbs) hbadUpper

/-- Dominant matching families: every chosen edge meets `A` in exactly one
vertex.  Their enlarged support has the deterministic cardinality
`|A| + j (k-1)`. -/
def goodMatchingMeetingFamilies (H : FiniteHypergraph V E)
    (A : Finset V) (j : ℕ) : Finset (Finset E) :=
  (H.matchingMeetingFamilies A j).filter fun F ↦
    F ⊆ H.singleMeetingEdges A

/-- Exceptional matching families, necessarily containing an edge that
meets `A` more than once. -/
def exceptionalMatchingMeetingFamilies (H : FiniteHypergraph V E)
    (A : Finset V) (j : ℕ) : Finset (Finset E) :=
  H.matchingMeetingFamilies A j \ H.goodMatchingMeetingFamilies A j

@[simp] lemma mem_goodMatchingMeetingFamilies
    (H : FiniteHypergraph V E) (A : Finset V) (j : ℕ) (F : Finset E) :
    F ∈ H.goodMatchingMeetingFamilies A j ↔
      F ∈ H.matchingMeetingFamilies A j ∧
        F ⊆ H.singleMeetingEdges A := by
  simp [goodMatchingMeetingFamilies]

lemma matchingMeetingFamilies_eq_good_union_exceptional
    (H : FiniteHypergraph V E) (A : Finset V) (j : ℕ) :
    H.matchingMeetingFamilies A j =
      H.goodMatchingMeetingFamilies A j ∪
        H.exceptionalMatchingMeetingFamilies A j := by
  unfold exceptionalMatchingMeetingFamilies goodMatchingMeetingFamilies
  symm
  apply union_sdiff_of_subset
  exact filter_subset _ _

/-- Aggregate the exact signed fixed-family estimates into a binomial
moment estimate.  This theorem deliberately keeps the dominant-family
error and count deficit abstract; the concrete regular/codegree bounds can
then be substituted without reopening the probability calculation. -/
theorem averagedMoment_close_of_goodFamily_close
    (H : FiniteHypergraph V E) {k D : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (r : ℕ) (M : Finset E) (A : Finset V) (j : ℕ)
    (ideal center countError : ℝ) (familyError : Finset E → ℝ)
    (hcenter₀ : 0 ≤ center)
    (hgoodClose : ∀ F ∈ H.goodMatchingMeetingFamilies A j,
      |p ^ F.card *
          (∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
            (-p) ^ Q.card *
              H.innerJointUncoveredMass
                (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M
                (A ∪ (F ∪ Q).biUnion H.support)) - center| ≤
        familyError F)
    (hcardUpper :
      (((H.goodMatchingMeetingFamilies A j).card : ℕ) : ℝ) ≤ ideal)
    (hcardDeficit :
      ideal - (((H.goodMatchingMeetingFamilies A j).card : ℕ) : ℝ) ≤
        countError) :
    |H.averagedInnerNewAcceptedMeetingChooseMoment
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M A j -
        ideal * center| ≤
      (∑ F ∈ H.goodMatchingMeetingFamilies A j, familyError F) +
        countError * center +
        (((H.exceptionalMatchingMeetingFamilies A j).card : ℕ) : ℝ) *
          p ^ j := by
  let value : Finset E → ℝ := fun F ↦
    p ^ F.card *
      ∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
        (-p) ^ Q.card *
          H.innerJointUncoveredMass
            (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M
            (A ∪ (F ∪ Q).biUnion H.support)
  have hbad : ∀ F ∈ H.exceptionalMatchingMeetingFamilies A j,
      value F ∈ Set.Icc 0 (p ^ j) := by
    intro F hF
    have hFmatchingMem : F ∈ H.matchingMeetingFamilies A j :=
      (mem_sdiff.mp hF).1
    have hFdata := (H.mem_matchingMeetingFamilies A j F).1 hFmatchingMem
    simpa [value, hFdata.2.1] using
      H.staticConflictFamilyContribution_mem_Icc hk hunif hdeg hp₀ hp₁
        r M A F hFdata.2.2
  have hdisjoint : Disjoint (H.goodMatchingMeetingFamilies A j)
      (H.exceptionalMatchingMeetingFamilies A j) := by
    unfold exceptionalMatchingMeetingFamilies
    exact disjoint_sdiff
  rw [H.averagedInnerNewAcceptedMeetingChooseMoment_eq_staticConflictExpansion
    hk hunif p r M A j]
  change |(∑ F ∈ H.matchingMeetingFamilies A j, value F) -
      ideal * center| ≤ _
  exact abs_sum_partition_sub_ideal_mul_le
    (H.matchingMeetingFamilies A j)
    (H.goodMatchingMeetingFamilies A j)
    (H.exceptionalMatchingMeetingFamilies A j)
    value familyError ideal center countError (p ^ j)
    (H.matchingMeetingFamilies_eq_good_union_exceptional A j)
    hdisjoint hcenter₀ (by simpa [value] using hgoodClose) hbad
    hcardUpper hcardDeficit

/-- Profile estimate for the all-order family sum.  The dominant families
use their exact enlarged-support cardinality; the exceptional families are
charged only by their cardinality.  Subsequent counting lemmas provide the
three explicit family-cardinality hypotheses. -/
theorem matchingFamilyJointMass_profile_mem_Icc
    (H : FiniteHypergraph V E) (w : Finset E → ℝ)
    (r : ℕ) (M : Finset E) (A : Finset V) (j : ℕ)
    {k : ℕ} (hk : 0 < k) (hunif : H.IsUniform k)
    (U : Finset V → ℝ)
    (hU : ∀ B, U B ∈ Set.Icc (0 : ℝ) 1)
    (target epsilon ideal countError exceptionalError : ℝ)
    (htarget₀ : 0 ≤ target) (hepsilon₀ : 0 ≤ epsilon)
    (hprofile : ∀ F ∈ H.goodMatchingMeetingFamilies A j,
      |U (A ∪ F.biUnion H.support) - target| ≤ epsilon)
    (hgoodLower : ideal - countError ≤
      ((H.goodMatchingMeetingFamilies A j).card : ℝ))
    (hgoodUpper : ((H.goodMatchingMeetingFamilies A j).card : ℝ) ≤ ideal)
    (hexceptional :
      ((H.exceptionalMatchingMeetingFamilies A j).card : ℝ) ≤
        exceptionalError) :
    (∑ F ∈ H.matchingMeetingFamilies A j,
        U (A ∪ F.biUnion H.support)) ∈
      Set.Icc
        (max 0 (ideal - countError) * max 0 (target - epsilon))
        (ideal * (target + epsilon) + exceptionalError) := by
  have hgoodBounds : ∀ F ∈ H.goodMatchingMeetingFamilies A j,
      max 0 (target - epsilon) ≤ U (A ∪ F.biUnion H.support) ∧
        U (A ∪ F.biUnion H.support) ≤ target + epsilon := by
    intro F hF
    have habs := abs_sub_le_iff.mp (hprofile F hF)
    constructor
    · exact max_le (hU _).1 (by linarith)
    · linarith
  have hgoodCard₀ : 0 ≤
      ((H.goodMatchingMeetingFamilies A j).card : ℝ) := Nat.cast_nonneg _
  have hcountLower : max 0 (ideal - countError) ≤
      ((H.goodMatchingMeetingFamilies A j).card : ℝ) :=
    max_le hgoodCard₀ hgoodLower
  have htargetMinus₀ : 0 ≤ max 0 (target - epsilon) := le_max_left _ _
  rw [H.matchingMeetingFamilies_eq_good_union_exceptional]
  have hdisj : Disjoint (H.goodMatchingMeetingFamilies A j)
      (H.exceptionalMatchingMeetingFamilies A j) := by
    unfold exceptionalMatchingMeetingFamilies
    exact disjoint_sdiff
  rw [sum_union hdisj]
  constructor
  · calc
      max 0 (ideal - countError) * max 0 (target - epsilon) ≤
          ((H.goodMatchingMeetingFamilies A j).card : ℝ) *
            max 0 (target - epsilon) :=
        mul_le_mul_of_nonneg_right hcountLower htargetMinus₀
      _ = ∑ _F ∈ H.goodMatchingMeetingFamilies A j,
          max 0 (target - epsilon) := by simp
      _ ≤ ∑ F ∈ H.goodMatchingMeetingFamilies A j,
          U (A ∪ F.biUnion H.support) := by
        apply sum_le_sum
        intro F hF
        exact (hgoodBounds F hF).1
      _ ≤ (∑ F ∈ H.goodMatchingMeetingFamilies A j,
          U (A ∪ F.biUnion H.support)) +
          ∑ F ∈ H.exceptionalMatchingMeetingFamilies A j,
            U (A ∪ F.biUnion H.support) := by
        exact le_add_of_nonneg_right (sum_nonneg fun F _ ↦ (hU _).1)
  · calc
      (∑ F ∈ H.goodMatchingMeetingFamilies A j,
          U (A ∪ F.biUnion H.support)) +
          ∑ F ∈ H.exceptionalMatchingMeetingFamilies A j,
            U (A ∪ F.biUnion H.support) ≤
          ((H.goodMatchingMeetingFamilies A j).card : ℝ) *
              (target + epsilon) +
            ((H.exceptionalMatchingMeetingFamilies A j).card : ℝ) := by
        apply add_le_add
        · calc
            (∑ F ∈ H.goodMatchingMeetingFamilies A j,
                U (A ∪ F.biUnion H.support)) ≤
                ∑ _F ∈ H.goodMatchingMeetingFamilies A j,
                  (target + epsilon) := by
              apply sum_le_sum
              intro F hF
              exact (hgoodBounds F hF).2
            _ = ((H.goodMatchingMeetingFamilies A j).card : ℝ) *
                (target + epsilon) := by simp <;> ring
        · calc
            (∑ F ∈ H.exceptionalMatchingMeetingFamilies A j,
                U (A ∪ F.biUnion H.support)) ≤
                ∑ _F ∈ H.exceptionalMatchingMeetingFamilies A j,
                  (1 : ℝ) := by
              apply sum_le_sum
              intro F _
              exact (hU _).2
            _ = ((H.exceptionalMatchingMeetingFamilies A j).card : ℝ) := by simp
      _ ≤ ideal * (target + epsilon) + exceptionalError := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hgoodUpper (by linarith)
        · exact hexceptional

/-- Matching families containing a multiple-meeting edge are sparse.  The
remaining `j-1` edges are bounded by arbitrary choices from `edgesMeeting`;
the resulting `D^(j-1)` scale is exactly what is needed after multiplication
by the `j`-th Bernoulli moment. -/
lemma exceptionalMatchingMeetingFamilies_card_le
    (H : FiniteHypergraph V E) (A : Finset V) (j : ℕ)
    {D C : ℕ} (hj : 0 < j)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C) :
    (H.exceptionalMatchingMeetingFamilies A j).card ≤
      A.card ^ 2 * C * (A.card * D) ^ (j - 1) := by
  let cover : E → Finset (Finset E) := fun e ↦
    ((H.edgesMeeting A).powersetCard j).filter ({e} ⊆ ·)
  have hsub : H.exceptionalMatchingMeetingFamilies A j ⊆
      (H.multiMeetingEdges A).biUnion cover := by
    intro F hF
    have hFmatch : F ∈ H.matchingMeetingFamilies A j :=
      (mem_sdiff.mp hF).1
    have hnotgood : F ∉ H.goodMatchingMeetingFamilies A j :=
      (mem_sdiff.mp hF).2
    have hFdata := (H.mem_matchingMeetingFamilies A j F).1 hFmatch
    have hnotSingle : ¬F ⊆ H.singleMeetingEdges A := by
      exact fun hs ↦ hnotgood
        ((H.mem_goodMatchingMeetingFamilies A j F).2 ⟨hFmatch, hs⟩)
    obtain ⟨e, heF, heNotSingle⟩ := Set.not_subset.mp hnotSingle
    have heMeeting : e ∈ H.edgesMeeting A := hFdata.1 heF
    have heMulti : e ∈ H.multiMeetingEdges A := by
      by_contra heNotMulti
      exact heNotSingle ((H.mem_singleMeetingEdges A e).2
        ⟨heMeeting, heNotMulti⟩)
    apply mem_biUnion.mpr
    refine ⟨e, heMulti, ?_⟩
    simp only [cover, mem_filter, mem_powersetCard]
    exact ⟨⟨hFdata.1, hFdata.2.1⟩, by simpa using heF⟩
  have hcoverCard (e : E) (he : e ∈ H.multiMeetingEdges A) :
      (cover e).card ≤ (H.edgesMeeting A).card ^ (j - 1) := by
    dsimp only [cover]
    rw [card_filter_powersetCard_subset]
    · exact (Nat.choose_le_pow _ _).trans
        (Nat.pow_le_pow_left (Nat.sub_le _ _) _)
    · simpa using H.multiMeetingEdges_subset_edgesMeeting A he
    · change ({e} : Finset E).card ≤ j
      rw [card_singleton]
      omega
  have hmeeting := H.edgesMeeting_card_le_mul_degree A D hdeg
  have hmulti := H.multiMeetingEdges_card_le_sq_mul_pairDegree A C hpair
  calc
    (H.exceptionalMatchingMeetingFamilies A j).card ≤
        ((H.multiMeetingEdges A).biUnion cover).card := card_le_card hsub
    _ ≤ ∑ e ∈ H.multiMeetingEdges A, (cover e).card := card_biUnion_le
    _ ≤ ∑ _e ∈ H.multiMeetingEdges A,
        (H.edgesMeeting A).card ^ (j - 1) := by
      apply sum_le_sum
      intro e he
      exact hcoverCard e he
    _ = (H.multiMeetingEdges A).card *
        (H.edgesMeeting A).card ^ (j - 1) := by simp
    _ ≤ (A.card ^ 2 * C) * (A.card * D) ^ (j - 1) := by
      exact Nat.mul_le_mul hmulti (Nat.pow_le_pow_left hmeeting (j - 1))

/-! ### Unique-anchor encoding of dominant families -/

/-- The vertices of `A` used as the unique anchors of a family. -/
def familyAnchorSet (H : FiniteHypergraph V E)
    (A : Finset V) (F : Finset E) : Finset V :=
  F.biUnion fun e ↦ H.support e ∩ A

@[simp] lemma mem_familyAnchorSet
    (H : FiniteHypergraph V E) (A : Finset V) (F : Finset E) (v : V) :
    v ∈ H.familyAnchorSet A F ↔
      ∃ e ∈ F, v ∈ H.support e ∧ v ∈ A := by
  simp [familyAnchorSet, and_assoc]

lemma familyAnchorSet_subset
    (H : FiniteHypergraph V E) (A : Finset V) (F : Finset E) :
    H.familyAnchorSet A F ⊆ A := by
  intro v hv
  obtain ⟨e, _heF, _hve, hvA⟩ := (H.mem_familyAnchorSet A F v).1 hv
  exact hvA

/-- At an anchor of a matching family there is a unique family edge. -/
lemma existsUnique_edge_at_anchor_of_matching
    (H : FiniteHypergraph V E) (A : Finset V) (F : Finset E)
    (hF : H.IsMatching F) {v : V} (hv : v ∈ H.familyAnchorSet A F) :
    ∃! e, e ∈ F ∧ v ∈ H.support e := by
  obtain ⟨e, heF, hve, _⟩ := (H.mem_familyAnchorSet A F v).1 hv
  refine ⟨e, ⟨heF, hve⟩, ?_⟩
  rintro f ⟨hfF, hvf⟩
  by_contra hef
  exact (Finset.disjoint_left.mp (hF heF hfF (Ne.symm hef))) hve hvf

/-- A total option-valued edge selector.  On a genuine family anchor it is
the unique incident family edge; `none` is used only off the anchor set. -/
noncomputable def familyEdgeAt
    (H : FiniteHypergraph V E) (F : Finset E) (v : V) : Option E :=
  if h : ∃ e, e ∈ F ∧ v ∈ H.support e then some h.choose else none

lemma familyEdgeAt_eq_some_of_unique
    (H : FiniteHypergraph V E) (F : Finset E) (v : V) (e : E)
    (huniq : ∃! f, f ∈ F ∧ v ∈ H.support f)
    (he : e ∈ F ∧ v ∈ H.support e) :
    H.familyEdgeAt F v = some e := by
  let hex : ∃ f, f ∈ F ∧ v ∈ H.support f := ⟨e, he⟩
  rw [familyEdgeAt, dif_pos hex]
  congr 1
  exact huniq.unique (Classical.choose_spec hex) he

/-- Dominant families with a prescribed anchor set. -/
def goodMatchingFamiliesWithAnchors
    (H : FiniteHypergraph V E) (A : Finset V) (j : ℕ) (B : Finset V) :
    Finset (Finset E) :=
  (H.goodMatchingMeetingFamilies A j).filter fun F ↦
    H.familyAnchorSet A F = B

/-- Partial option-valued encodings of one incident edge at each vertex of
`B`. -/
def anchorChoiceCodes (H : FiniteHypergraph V E) (B : Finset V) :
    Finset (∀ v, v ∈ B → Option E) :=
  B.pi fun v ↦ (H.incidentEdges v).image Function.Embedding.some

/-- The unique-anchor code of a family over a prescribed anchor set. -/
noncomputable def familyAnchorCode
    (H : FiniteHypergraph V E) (B : Finset V) (F : Finset E) :
    ∀ v, v ∈ B → Option E :=
  fun v _ ↦ H.familyEdgeAt F v

lemma familyAnchorCode_mem
    (H : FiniteHypergraph V E) (A : Finset V) (j : ℕ) (B : Finset V)
    {F : Finset E} (hF : F ∈ H.goodMatchingFamiliesWithAnchors A j B) :
    H.familyAnchorCode B F ∈ H.anchorChoiceCodes B := by
  rw [anchorChoiceCodes, mem_pi]
  intro v hvB
  have hgood := (mem_filter.mp hF).1
  have hanchor : H.familyAnchorSet A F = B := (mem_filter.mp hF).2
  have hmatch := (H.mem_matchingMeetingFamilies A j F).1
    ((H.mem_goodMatchingMeetingFamilies A j F).1 hgood).1 |>.2.2
  have hvAnchor : v ∈ H.familyAnchorSet A F := by simpa [hanchor] using hvB
  obtain ⟨e, he, huniq⟩ := H.existsUnique_edge_at_anchor_of_matching
    A F hmatch hvAnchor
  rw [familyAnchorCode,
    H.familyEdgeAt_eq_some_of_unique F v e ⟨e, he, huniq⟩ he]
  exact mem_image.mpr ⟨e,
    (H.mem_incidentEdges v e).2 he.2, rfl⟩

lemma familyAnchorCode_injOn
    (H : FiniteHypergraph V E) (A : Finset V) (j : ℕ) (B : Finset V) :
    Set.InjOn (H.familyAnchorCode B)
      (H.goodMatchingFamiliesWithAnchors A j B : Set (Finset E)) := by
  intro F hF G hG hcode
  have hgoodF := (mem_filter.mp hF).1
  have hgoodG := (mem_filter.mp hG).1
  have hanchorF : H.familyAnchorSet A F = B := (mem_filter.mp hF).2
  have hanchorG : H.familyAnchorSet A G = B := (mem_filter.mp hG).2
  have hdataF := (H.mem_goodMatchingMeetingFamilies A j F).1 hgoodF
  have hdataG := (H.mem_goodMatchingMeetingFamilies A j G).1 hgoodG
  have hmatchF := (H.mem_matchingMeetingFamilies A j F).1 hdataF.1 |>.2.2
  have hmatchG := (H.mem_matchingMeetingFamilies A j G).1 hdataG.1 |>.2.2
  apply Subset.antisymm
  · intro e heF
    obtain ⟨v, ⟨hvA, hve⟩, hvuniq⟩ :=
      H.existsUnique_anchor_of_mem_singleMeetingEdges A (hdataF.2 heF)
    have hvAnchorF : v ∈ H.familyAnchorSet A F :=
      (H.mem_familyAnchorSet A F v).2 ⟨e, heF, hve, hvA⟩
    have hvB : v ∈ B := by simpa [hanchorF] using hvAnchorF
    have hedgeF := H.existsUnique_edge_at_anchor_of_matching
      A F hmatchF hvAnchorF
    have hFcode : H.familyAnchorCode B F v hvB = some e := by
      exact H.familyEdgeAt_eq_some_of_unique F v e hedgeF ⟨heF, hve⟩
    have hGcode : H.familyAnchorCode B G v hvB = some e := by
      rw [← hcode]
      exact hFcode
    have hvAnchorG : v ∈ H.familyAnchorSet A G := by simpa [hanchorG] using hvB
    obtain ⟨f, hf, hfunique⟩ := H.existsUnique_edge_at_anchor_of_matching
      A G hmatchG hvAnchorG
    have hSomeF : H.familyAnchorCode B G v hvB = some f :=
      H.familyEdgeAt_eq_some_of_unique G v f ⟨f, hf, hfunique⟩ hf
    have : e = f := Option.some.inj (hGcode.symm.trans hSomeF)
    exact this.symm ▸ hf.1
  · intro e heG
    obtain ⟨v, ⟨hvA, hve⟩, hvuniq⟩ :=
      H.existsUnique_anchor_of_mem_singleMeetingEdges A (hdataG.2 heG)
    have hvAnchorG : v ∈ H.familyAnchorSet A G :=
      (H.mem_familyAnchorSet A G v).2 ⟨e, heG, hve, hvA⟩
    have hvB : v ∈ B := by simpa [hanchorG] using hvAnchorG
    have hedgeG := H.existsUnique_edge_at_anchor_of_matching
      A G hmatchG hvAnchorG
    have hGcode : H.familyAnchorCode B G v hvB = some e :=
      H.familyEdgeAt_eq_some_of_unique G v e hedgeG ⟨heG, hve⟩
    have hFcode : H.familyAnchorCode B F v hvB = some e := by
      rw [hcode]
      exact hGcode
    have hvAnchorF : v ∈ H.familyAnchorSet A F := by simpa [hanchorF] using hvB
    obtain ⟨f, hf, hfunique⟩ := H.existsUnique_edge_at_anchor_of_matching
      A F hmatchF hvAnchorF
    have hSomeF : H.familyAnchorCode B F v hvB = some f :=
      H.familyEdgeAt_eq_some_of_unique F v f ⟨f, hf, hfunique⟩ hf
    have : e = f := Option.some.inj (hFcode.symm.trans hSomeF)
    exact this.symm ▸ hf.1

lemma goodMatchingFamiliesWithAnchors_card_le
    (H : FiniteHypergraph V E) (A : Finset V) (j D : ℕ)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (B : Finset V) (hBA : B ⊆ A) (hBcard : B.card = j) :
    (H.goodMatchingFamiliesWithAnchors A j B).card ≤ D ^ j := by
  have hdegAll (v : V) : H.edgeDegree v ≤ D := by
    by_cases hv : v ∈ H.vertexSet
    · exact hdeg v hv
    · have hno : ∀ e : E, v ∉ H.support e := by
        intro e hve
        exact hv (H.support_subset_vertexSet e hve)
      simp [edgeDegree, incidentEdges, hno]
  calc
    (H.goodMatchingFamiliesWithAnchors A j B).card ≤
        (H.anchorChoiceCodes B).card :=
      card_le_card_of_injOn (H.familyAnchorCode B)
        (fun _ hF ↦ H.familyAnchorCode_mem A j B hF)
        (H.familyAnchorCode_injOn A j B)
    _ = ∏ v ∈ B, (H.incidentEdges v).card := by
      unfold anchorChoiceCodes
      rw [card_pi]
      apply prod_congr rfl
      intro v _
      exact card_image_of_injective _ (Option.some_injective E)
    _ ≤ ∏ _v ∈ B, D := by
      apply prod_le_prod
      · intro v _
        exact Nat.zero_le _
      intro v _
      exact hdegAll v
    _ = D ^ j := by simp [hBcard]

/-- Every leaf produced by the sequential anchor chooser is a dominant
matching family with exactly the prescribed anchor set. -/
lemma anchorFamilyTree_toList_subset_goodMatchingFamiliesWithAnchors
    (H : FiniteHypergraph V E) (A B : Finset V) (hBsub : B ⊆ A) :
    H.anchorFamilyTree A B.toList ⊆
      H.goodMatchingFamiliesWithAnchors A B.card B := by
  intro F hF
  have hspec := H.mem_anchorFamilyTree_toList_spec A B hBsub hF
  apply mem_filter.mpr
  refine ⟨(H.mem_goodMatchingMeetingFamilies A B.card F).2 ⟨?_, hspec.2.1⟩, ?_⟩
  · apply (H.mem_matchingMeetingFamilies A B.card F).2
    refine ⟨?_, hspec.2.2.1, hspec.1⟩
    intro e he
    exact (H.mem_singleMeetingEdges A e).1 (hspec.2.1 he) |>.1
  · simpa [anchorSet, familyAnchorSet] using hspec.2.2.2

/-- For one prescribed anchor set, the sequential availability estimate is
a lower bound on the number of dominant matching families with those
anchors. -/
lemma sequentialChoiceBase_pow_le_goodMatchingFamiliesWithAnchors_card
    (H : FiniteHypergraph V E) (A B : Finset V)
    {k C degreeLower j : ℕ} (hj : 0 < j)
    (hBsub : B ⊆ A) (hBvertex : B ⊆ H.vertexSet) (hBcard : B.card = j)
    (hunif : H.IsUniform k)
    (hlow : ∀ v ∈ A, degreeLower ≤ H.edgeDegree v)
    (hpair : ∀ u ∈ H.vertexSet, ∀ z ∈ H.vertexSet, u ≠ z →
      H.edgePairDegree u z ≤ C) :
    (degreeLower - (A.card - 1) * C - (j - 1) * (k * C)) ^ j ≤
      (H.goodMatchingFamiliesWithAnchors A j B).card := by
  calc
    (degreeLower - (A.card - 1) * C - (j - 1) * (k * C)) ^ j ≤
        (H.anchorFamilyTree A B.toList).card :=
      H.sequentialChoiceBase_pow_le_card_anchorFamilyTree_toList
        A B hj hBsub hBvertex hBcard hunif hlow hpair
    _ ≤ (H.goodMatchingFamiliesWithAnchors A j B).card := by
      apply card_le_card
      simpa [hBcard] using
        H.anchorFamilyTree_toList_subset_goodMatchingFamiliesWithAnchors
          A B hBsub

/-- Sharp lower count for dominant `j`-families.  The error is charged
inside the sequential choice base, so after multiplication by `p^j` it has
the correct low-codegree scale. -/
theorem choose_mul_sequentialChoiceBase_pow_le_goodMatchingMeetingFamilies_card
    (H : FiniteHypergraph V E) (A : Finset V)
    {k C degreeLower j : ℕ} (hj : 0 < j)
    (hAvertex : A ⊆ H.vertexSet)
    (hunif : H.IsUniform k)
    (hlow : ∀ v ∈ A, degreeLower ≤ H.edgeDegree v)
    (hpair : ∀ u ∈ H.vertexSet, ∀ z ∈ H.vertexSet, u ≠ z →
      H.edgePairDegree u z ≤ C) :
    A.card.choose j *
        (degreeLower - (A.card - 1) * C - (j - 1) * (k * C)) ^ j ≤
      (H.goodMatchingMeetingFamilies A j).card := by
  let anchored : Finset V → Finset (Finset E) := fun B ↦
    H.goodMatchingFamiliesWithAnchors A j B
  have hunion : (A.powersetCard j).biUnion anchored =
      H.goodMatchingMeetingFamilies A j := by
    apply Subset.antisymm
    · intro F hF
      obtain ⟨B, hB, hFB⟩ := mem_biUnion.mp hF
      exact (mem_filter.mp hFB).1
    · intro F hF
      let B := H.familyAnchorSet A F
      have hdata := (H.mem_goodMatchingMeetingFamilies A j F).1 hF
      have hmatching := (H.mem_matchingMeetingFamilies A j F).1 hdata.1 |>.2.2
      have hBsub : B ⊆ A := H.familyAnchorSet_subset A F
      have hBcard : B.card = j := by
        dsimp only [B, familyAnchorSet]
        rw [H.card_biUnion_support_inter_eq_of_matching_subset_singleMeeting
          A F hmatching hdata.2]
        exact (H.mem_matchingMeetingFamilies A j F).1 hdata.1 |>.2.1
      apply mem_biUnion.mpr
      refine ⟨B, mem_powersetCard.mpr ⟨hBsub, hBcard⟩, ?_⟩
      exact mem_filter.mpr ⟨hF, rfl⟩
  have hdisj : ∀ B ∈ A.powersetCard j, ∀ C ∈ A.powersetCard j,
      B ≠ C → Disjoint (anchored B) (anchored C) := by
    intro B _ C _ hBC
    rw [disjoint_left]
    intro F hFB hFC
    have hB := (mem_filter.mp hFB).2
    have hC := (mem_filter.mp hFC).2
    exact hBC (hB.symm.trans hC)
  calc
    A.card.choose j *
        (degreeLower - (A.card - 1) * C - (j - 1) * (k * C)) ^ j =
        ∑ _B ∈ A.powersetCard j,
          (degreeLower - (A.card - 1) * C - (j - 1) * (k * C)) ^ j := by
      simp
    _ ≤ ∑ B ∈ A.powersetCard j, (anchored B).card := by
      apply sum_le_sum
      intro B hB
      have hBdata := mem_powersetCard.mp hB
      exact H.sequentialChoiceBase_pow_le_goodMatchingFamiliesWithAnchors_card
        A B hj hBdata.1 (fun _ hv ↦ hAvertex (hBdata.1 hv)) hBdata.2
          hunif hlow hpair
    _ = ((A.powersetCard j).biUnion anchored).card :=
      (card_biUnion hdisj).symm
    _ = (H.goodMatchingMeetingFamilies A j).card := by rw [hunion]

/-- Sharp upper count for dominant `j`-families. -/
theorem goodMatchingMeetingFamilies_card_le_choose_mul_pow
    (H : FiniteHypergraph V E) (A : Finset V) (j D : ℕ)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D) :
    (H.goodMatchingMeetingFamilies A j).card ≤ A.card.choose j * D ^ j := by
  let anchors : Finset V → Finset (Finset E) := fun B ↦
    H.goodMatchingFamiliesWithAnchors A j B
  have hsub : H.goodMatchingMeetingFamilies A j ⊆
      (A.powersetCard j).biUnion anchors := by
    intro F hF
    let B := H.familyAnchorSet A F
    have hdata := (H.mem_goodMatchingMeetingFamilies A j F).1 hF
    have hmatch := (H.mem_matchingMeetingFamilies A j F).1 hdata.1 |>.2.2
    have hsingle := hdata.2
    have hBsub : B ⊆ A := H.familyAnchorSet_subset A F
    have hBcard : B.card = j := by
      dsimp only [B, familyAnchorSet]
      rw [H.card_biUnion_support_inter_eq_of_matching_subset_singleMeeting
        A F hmatch hsingle]
      exact (H.mem_matchingMeetingFamilies A j F).1 hdata.1 |>.2.1
    apply mem_biUnion.mpr
    refine ⟨B, mem_powersetCard.mpr ⟨hBsub, hBcard⟩, ?_⟩
    exact mem_filter.mpr ⟨hF, rfl⟩
  calc
    (H.goodMatchingMeetingFamilies A j).card ≤
        ((A.powersetCard j).biUnion anchors).card := card_le_card hsub
    _ ≤ ∑ B ∈ A.powersetCard j, (anchors B).card := card_biUnion_le
    _ ≤ ∑ _B ∈ A.powersetCard j, D ^ j := by
      apply sum_le_sum
      intro B hB
      have hBdata := mem_powersetCard.mp hB
      exact H.goodMatchingFamiliesWithAnchors_card_le
        A j D hdeg B hBdata.1 hBdata.2
    _ = A.card.choose j * D ^ j := by simp

/-- Concrete all-order estimate for the `j`-th accepted-meeting moment in
an exactly regular low-codegree hypergraph.  The center is the signed
isolation-adjusted mean-field term.  The four displayed errors are,
respectively: the fixed-family profile/isolation errors, the deficit in the
number of dominant outer families, and the actual exceptional-outer-family
count bounded by codegree. -/
theorem averagedMoment_close_signedRegularProfile
    (H : FiniteHypergraph V E) {k D C : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k)
    (hreg : ∀ v ∈ H.vertexSet, H.edgeDegree v = D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (r : ℕ) (M : Finset E) (A : Finset V) (hA : A ⊆ H.vertexSet)
    (j : ℕ) (hj : 0 < j)
    {p y : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpY : p * y ^ (k - 1) ≤ 1)
    (orderError : ℕ → ℝ) (herror₀ : ∀ a, 0 ≤ orderError a)
    (hprofile : ∀ S : Finset V,
      |H.innerJointUncoveredMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M S -
          y ^ S.card| ≤ orderError S.card) :
    let choiceBase :=
      D - (A.card - 1) * C - (j - 1) * (k * C)
    let idealCount := A.card.choose j * D ^ j
    let lowerCount := A.card.choose j * choiceBase ^ j
    let center :=
      p ^ j * (y ^ (A.card + j * (k - 1)) *
        (1 - p * y ^ (k - 1)) ^ (j * k * D))
    let familyError : Finset E → ℝ := fun F ↦
      p ^ F.card *
        H.staticConflictSignedError A F k C p y orderError
    |H.averagedInnerNewAcceptedMeetingChooseMoment
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M A j -
        (idealCount : ℝ) * center| ≤
      (∑ F ∈ H.goodMatchingMeetingFamilies A j, familyError F) +
        ((idealCount - lowerCount : ℕ) : ℝ) * center +
        ((A.card ^ 2 * C * (A.card * D) ^ (j - 1) : ℕ) : ℝ) * p ^ j := by
  let choiceBase :=
    D - (A.card - 1) * C - (j - 1) * (k * C)
  let idealCount := A.card.choose j * D ^ j
  let lowerCount := A.card.choose j * choiceBase ^ j
  let center :=
    p ^ j * (y ^ (A.card + j * (k - 1)) *
      (1 - p * y ^ (k - 1)) ^ (j * k * D))
  let familyError : Finset E → ℝ := fun F ↦
    p ^ F.card *
      H.staticConflictSignedError A F k C p y orderError
  have hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D := by
    intro v hv
    exact (hreg v hv).le
  have hlow : ∀ v ∈ H.vertexSet, D ≤ H.edgeDegree v := by
    intro v hv
    exact (hreg v hv).ge
  have hcenter₀ : 0 ≤ center := by
    have hz₀ : 0 ≤ 1 - p * y ^ (k - 1) := sub_nonneg.mpr hpY
    exact mul_nonneg (pow_nonneg hp₀ _)
      (mul_nonneg (pow_nonneg hy.1 _) (pow_nonneg hz₀ _))
  have hgoodClose : ∀ F ∈ H.goodMatchingMeetingFamilies A j,
      |p ^ F.card *
          (∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
            (-p) ^ Q.card *
              H.innerJointUncoveredMass
                (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M
                (A ∪ (F ∪ Q).biUnion H.support)) - center| ≤
        familyError F := by
    intro F hF
    have hFdata := (H.mem_goodMatchingMeetingFamilies A j F).1 hF
    have hmeeting := (H.mem_matchingMeetingFamilies A j F).1 hFdata.1
    have hweighted :=
      H.weightedStaticConflictSignedJointMass_close_idealExponent
        r M A F hk hunif hdeg hlow hpair hmeeting.2.2 hFdata.2
        p y hp₀ hp₁ hy hpY orderError herror₀ hprofile
    simpa [center, familyError, hmeeting.2.1, familySupport] using hweighted
  have hlowerNat : lowerCount ≤
      (H.goodMatchingMeetingFamilies A j).card := by
    simpa [lowerCount, choiceBase] using
      H.choose_mul_sequentialChoiceBase_pow_le_goodMatchingMeetingFamilies_card
        A hj hA hunif (fun v hv ↦ hlow v (hA hv)) hpair
  have hupperNat : (H.goodMatchingMeetingFamilies A j).card ≤ idealCount := by
    simpa [idealCount] using
      H.goodMatchingMeetingFamilies_card_le_choose_mul_pow A j D hdeg
  have hcardUpper :
      (((H.goodMatchingMeetingFamilies A j).card : ℕ) : ℝ) ≤
        (idealCount : ℝ) := by
    exact_mod_cast hupperNat
  have hdeficitNat :
      idealCount - (H.goodMatchingMeetingFamilies A j).card ≤
        idealCount - lowerCount := by
    omega
  have hcardDeficit :
      (idealCount : ℝ) -
          (((H.goodMatchingMeetingFamilies A j).card : ℕ) : ℝ) ≤
        ((idealCount - lowerCount : ℕ) : ℝ) := by
    rw [← Nat.cast_sub hupperNat]
    exact_mod_cast hdeficitNat
  have hmain := H.averagedMoment_close_of_goodFamily_close
    hk hunif hdeg hp₀ hp₁ r M A j
      (idealCount : ℝ) center ((idealCount - lowerCount : ℕ) : ℝ)
      familyError hcenter₀ hgoodClose hcardUpper hcardDeficit
  have hexceptional := H.exceptionalMatchingMeetingFamilies_card_le
    A j hj hdeg hpair
  have hexceptionalReal :
      (((H.exceptionalMatchingMeetingFamilies A j).card : ℕ) : ℝ) ≤
        ((A.card ^ 2 * C * (A.card * D) ^ (j - 1) : ℕ) : ℝ) := by
    exact_mod_cast hexceptional
  have hexceptionalWeighted := mul_le_mul_of_nonneg_right
    hexceptionalReal (pow_nonneg hp₀ j)
  have hreplace :
      (∑ F ∈ H.goodMatchingMeetingFamilies A j, familyError F) +
          ((idealCount - lowerCount : ℕ) : ℝ) * center +
          (((H.exceptionalMatchingMeetingFamilies A j).card : ℕ) : ℝ) *
            p ^ j ≤
        (∑ F ∈ H.goodMatchingMeetingFamilies A j, familyError F) +
          ((idealCount - lowerCount : ℕ) : ℝ) * center +
          ((A.card ^ 2 * C * (A.card * D) ^ (j - 1) : ℕ) : ℝ) *
            p ^ j :=
    by linarith
  simpa [choiceBase, idealCount, lowerCount, center, familyError] using
    hmain.trans hreplace

/-- Algebraic normalization of the ideal dominant-family center.  The
outer-family sampling factor and the exact signed isolation factor combine
into one binomial-moment step coefficient. -/
lemma idealSignedMomentCenter_eq
    (a j k D : ℕ) (p y : ℝ) :
    ((a.choose j * D ^ j : ℕ) : ℝ) *
        (p ^ j * (y ^ (a + j * (k - 1)) *
          (1 - p * y ^ (k - 1)) ^ (j * k * D))) =
      y ^ a * (a.choose j : ℝ) *
        (p * (D : ℝ) * y ^ (k - 1) *
          (1 - p * y ^ (k - 1)) ^ (k * D)) ^ j := by
  push_cast
  rw [pow_add]
  have hyexp : y ^ (j * (k - 1)) = (y ^ (k - 1)) ^ j := by
    rw [show j * (k - 1) = (k - 1) * j by ac_rfl, pow_mul]
  have hzexp :
      (1 - p * y ^ (k - 1)) ^ (j * k * D) =
        ((1 - p * y ^ (k - 1)) ^ (k * D)) ^ j := by
    rw [show j * k * D = (k * D) * j by ac_rfl, pow_mul]
  rw [hyexp, hzexp]
  repeat' rw [mul_pow]
  ring

/-- Normalized form of `averagedMoment_close_signedRegularProfile`.  Its
center is exactly the binomial moment of the signed isolation-adjusted
one-step mean-field update, so it plugs directly into the all-order tower
recurrence. -/
theorem averagedMoment_close_signedRegularMeanField
    (H : FiniteHypergraph V E) {k D C : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k)
    (hreg : ∀ v ∈ H.vertexSet, H.edgeDegree v = D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (r : ℕ) (M : Finset E) (A : Finset V) (hA : A ⊆ H.vertexSet)
    (j : ℕ) (hj : 0 < j)
    {p y : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpY : p * y ^ (k - 1) ≤ 1)
    (orderError : ℕ → ℝ) (herror₀ : ∀ a, 0 ≤ orderError a)
    (hprofile : ∀ S : Finset V,
      |H.innerJointUncoveredMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M S -
          y ^ S.card| ≤ orderError S.card) :
    let choiceBase :=
      D - (A.card - 1) * C - (j - 1) * (k * C)
    let idealCount := A.card.choose j * D ^ j
    let lowerCount := A.card.choose j * choiceBase ^ j
    let center :=
      p ^ j * (y ^ (A.card + j * (k - 1)) *
        (1 - p * y ^ (k - 1)) ^ (j * k * D))
    let step :=
      p * (D : ℝ) * y ^ (k - 1) *
        (1 - p * y ^ (k - 1)) ^ (k * D)
    let familyError : Finset E → ℝ := fun F ↦
      p ^ F.card *
        H.staticConflictSignedError A F k C p y orderError
    |H.averagedInnerNewAcceptedMeetingChooseMoment
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M A j -
        y ^ A.card * (A.card.choose j : ℝ) * step ^ j| ≤
      (∑ F ∈ H.goodMatchingMeetingFamilies A j, familyError F) +
        ((idealCount - lowerCount : ℕ) : ℝ) * center +
        ((A.card ^ 2 * C * (A.card * D) ^ (j - 1) : ℕ) : ℝ) * p ^ j := by
  have hmain := H.averagedMoment_close_signedRegularProfile
    hk hunif hreg hpair r M A hA j hj hp₀ hp₁ hy hpY
      orderError herror₀ hprofile
  simpa only [idealSignedMomentCenter_eq] using hmain

/-- Cutoff version of the concrete regular-profile moment estimate.  It
requires the incoming profile only up to the enlarged order reached by
`Qcut`, while retaining the same signed mean-field center. -/
theorem averagedMoment_close_signedRegularMeanField_cutoff
    (H : FiniteHypergraph V E) {k D C : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k)
    (hreg : ∀ v ∈ H.vertexSet, H.edgeDegree v = D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (r : ℕ) (M : Finset E) (A : Finset V) (hA : A ⊆ H.vertexSet)
    (j Qcut : ℕ) (hj : 0 < j)
    {p y : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpY : p * y ^ (k - 1) ≤ 1)
    (orderError : ℕ → ℝ) (herror₀ : ∀ a, 0 ≤ orderError a)
    (hprofile : ∀ S : Finset V,
      S ⊆ H.vertexSet →
      S.card ≤ A.card + j * (k - 1) + Qcut * (k - 1) →
      |H.innerJointUncoveredMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M S -
          y ^ S.card| ≤ orderError S.card) :
    let choiceBase :=
      D - (A.card - 1) * C - (j - 1) * (k * C)
    let idealCount := A.card.choose j * D ^ j
    let lowerCount := A.card.choose j * choiceBase ^ j
    let center :=
      p ^ j * (y ^ (A.card + j * (k - 1)) *
        (1 - p * y ^ (k - 1)) ^ (j * k * D))
    let step :=
      p * (D : ℝ) * y ^ (k - 1) *
        (1 - p * y ^ (k - 1)) ^ (k * D)
    let familyError : Finset E → ℝ := fun F ↦
      p ^ F.card * H.staticConflictSignedErrorCutoff
        A F k C p y Qcut orderError
    |H.averagedInnerNewAcceptedMeetingChooseMoment
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M A j -
        y ^ A.card * (A.card.choose j : ℝ) * step ^ j| ≤
      (∑ F ∈ H.goodMatchingMeetingFamilies A j, familyError F) +
        ((idealCount - lowerCount : ℕ) : ℝ) * center +
        ((A.card ^ 2 * C * (A.card * D) ^ (j - 1) : ℕ) : ℝ) * p ^ j := by
  let choiceBase :=
    D - (A.card - 1) * C - (j - 1) * (k * C)
  let idealCount := A.card.choose j * D ^ j
  let lowerCount := A.card.choose j * choiceBase ^ j
  let center :=
    p ^ j * (y ^ (A.card + j * (k - 1)) *
      (1 - p * y ^ (k - 1)) ^ (j * k * D))
  let familyError : Finset E → ℝ := fun F ↦
    p ^ F.card * H.staticConflictSignedErrorCutoff
      A F k C p y Qcut orderError
  have hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D := by
    intro v hv
    exact (hreg v hv).le
  have hlow : ∀ v ∈ H.vertexSet, D ≤ H.edgeDegree v := by
    intro v hv
    exact (hreg v hv).ge
  have hcenter₀ : 0 ≤ center := by
    have hz₀ : 0 ≤ 1 - p * y ^ (k - 1) := sub_nonneg.mpr hpY
    exact mul_nonneg (pow_nonneg hp₀ _)
      (mul_nonneg (pow_nonneg hy.1 _) (pow_nonneg hz₀ _))
  have hgoodClose : ∀ F ∈ H.goodMatchingMeetingFamilies A j,
      |p ^ F.card *
          (∑ Q ∈ (H.innerStaticConflictUnion F).powerset,
            (-p) ^ Q.card *
              H.innerJointUncoveredMass
                (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M
                (A ∪ (F ∪ Q).biUnion H.support)) - center| ≤
        familyError F := by
    intro F hF
    have hFdata := (H.mem_goodMatchingMeetingFamilies A j F).1 hF
    have hmeeting := (H.mem_matchingMeetingFamilies A j F).1 hFdata.1
    have hweighted := H.weightedStaticConflictSignedJointMass_close_cutoff
      r M A F hk hunif hdeg hlow hpair hA hmeeting.2.2 hFdata.2
        p y hp₀ hp₁ hy hpY Qcut orderError herror₀ (by
          intro S hSvertex hS
          apply hprofile S hSvertex
          simpa [hmeeting.2.1] using hS)
    simpa [center, familyError, hmeeting.2.1, familySupport] using hweighted
  have hlowerNat : lowerCount ≤
      (H.goodMatchingMeetingFamilies A j).card := by
    simpa [lowerCount, choiceBase] using
      H.choose_mul_sequentialChoiceBase_pow_le_goodMatchingMeetingFamilies_card
        A hj hA hunif (fun v hv ↦ hlow v (hA hv)) hpair
  have hupperNat : (H.goodMatchingMeetingFamilies A j).card ≤ idealCount := by
    simpa [idealCount] using
      H.goodMatchingMeetingFamilies_card_le_choose_mul_pow A j D hdeg
  have hcardUpper :
      (((H.goodMatchingMeetingFamilies A j).card : ℕ) : ℝ) ≤
        (idealCount : ℝ) := by exact_mod_cast hupperNat
  have hdeficitNat :
      idealCount - (H.goodMatchingMeetingFamilies A j).card ≤
        idealCount - lowerCount := by omega
  have hcardDeficit :
      (idealCount : ℝ) -
          (((H.goodMatchingMeetingFamilies A j).card : ℕ) : ℝ) ≤
        ((idealCount - lowerCount : ℕ) : ℝ) := by
    rw [← Nat.cast_sub hupperNat]
    exact_mod_cast hdeficitNat
  have hmain := H.averagedMoment_close_of_goodFamily_close
    hk hunif hdeg hp₀ hp₁ r M A j
      (idealCount : ℝ) center ((idealCount - lowerCount : ℕ) : ℝ)
      familyError hcenter₀ hgoodClose hcardUpper hcardDeficit
  have hexceptional := H.exceptionalMatchingMeetingFamilies_card_le
    A j hj hdeg hpair
  have hexceptionalReal :
      (((H.exceptionalMatchingMeetingFamilies A j).card : ℕ) : ℝ) ≤
        ((A.card ^ 2 * C * (A.card * D) ^ (j - 1) : ℕ) : ℝ) := by
    exact_mod_cast hexceptional
  have hexceptionalWeighted := mul_le_mul_of_nonneg_right
    hexceptionalReal (pow_nonneg hp₀ j)
  have hreplace :
      (∑ F ∈ H.goodMatchingMeetingFamilies A j, familyError F) +
          ((idealCount - lowerCount : ℕ) : ℝ) * center +
          (((H.exceptionalMatchingMeetingFamilies A j).card : ℕ) : ℝ) *
            p ^ j ≤
        (∑ F ∈ H.goodMatchingMeetingFamilies A j, familyError F) +
          ((idealCount - lowerCount : ℕ) : ℝ) * center +
          ((A.card ^ 2 * C * (A.card * D) ^ (j - 1) : ℕ) : ℝ) *
            p ^ j := by linarith
  have hfull := hmain.trans hreplace
  have hcenterEq :
      (idealCount : ℝ) * center =
        y ^ A.card * (A.card.choose j : ℝ) *
          (p * (D : ℝ) * y ^ (k - 1) *
            (1 - p * y ^ (k - 1)) ^ (k * D)) ^ j := by
    simpa [idealCount, center] using
      idealSignedMomentCenter_eq A.card j k D p y
  rw [hcenterEq] at hfull
  simpa [choiceBase, idealCount, lowerCount, center, familyError] using hfull

/-- Exact signed isolation-adjusted scalar step coefficient for an
exactly `D`-regular hypergraph. -/
def signedRegularStep (k D : ℕ) (p y : ℝ) : ℝ :=
  p * (D : ℝ) * y ^ (k - 1) *
    (1 - p * y ^ (k - 1)) ^ (k * D)

/-- Scalar survival-density update corresponding to `signedRegularStep`. -/
def signedRegularSurvivalStep (k D : ℕ) (p y : ℝ) : ℝ :=
  y * (1 - signedRegularStep k D p y)

/-- Iterated signed-isolation mean-field survival profile. -/
def signedRegularSurvival (k D : ℕ) (p : ℝ) : ℕ → ℝ
  | 0 => 1
  | r + 1 => signedRegularSurvivalStep k D p
      (signedRegularSurvival k D p r)

@[simp] lemma signedRegularSurvival_zero (k D : ℕ) (p : ℝ) :
    signedRegularSurvival k D p 0 = 1 := rfl

@[simp] lemma signedRegularSurvival_succ (k D r : ℕ) (p : ℝ) :
    signedRegularSurvival k D p (r + 1) =
      signedRegularSurvivalStep k D p
        (signedRegularSurvival k D p r) := rfl

/-- Under the natural scaled sampling restriction `pD ≤ 1`, the exact
signed-isolation reference trajectory stays a genuine density. -/
lemma signedRegularSurvival_mem_Icc
    (k D : ℕ) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hpD : p * (D : ℝ) ≤ 1) (r : ℕ) :
    signedRegularSurvival k D p r ∈ Set.Icc (0 : ℝ) 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
      let y := signedRegularSurvival k D p r
      have hyPow : y ^ (k - 1) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨pow_nonneg ih.1 _, pow_le_one₀ ih.1 ih.2⟩
      have hpy : p * y ^ (k - 1) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨mul_nonneg hp₀ hyPow.1, mul_le_one₀ hp₁ hyPow.1 hyPow.2⟩
      have hz : 1 - p * y ^ (k - 1) ∈ Set.Icc (0 : ℝ) 1 := by
        constructor <;> linarith [hpy.1, hpy.2]
      have hzPow :
          (1 - p * y ^ (k - 1)) ^ (k * D) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨pow_nonneg hz.1 _, pow_le_one₀ hz.1 hz.2⟩
      have hstep₀ : 0 ≤ signedRegularStep k D p y := by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg hp₀ (Nat.cast_nonneg D)) hyPow.1) hzPow.1
      have hstep₁ : signedRegularStep k D p y ≤ 1 := by
        calc
          signedRegularStep k D p y ≤ p * (D : ℝ) := by
            unfold signedRegularStep
            have hpD₀ : 0 ≤ p * (D : ℝ) :=
              mul_nonneg hp₀ (Nat.cast_nonneg D)
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left
              (mul_le_one₀ hyPow.2 hzPow.1 hzPow.2) hpD₀
          _ ≤ 1 := hpD
      rw [signedRegularSurvival_succ]
      change y * (1 - signedRegularStep k D p y) ∈ Set.Icc (0 : ℝ) 1
      exact ⟨mul_nonneg ih.1 (sub_nonneg.mpr hstep₁),
        mul_le_one₀ ih.2 (sub_nonneg.mpr hstep₁) (by linarith)⟩

lemma mul_signedRegularSurvival_pow_le_one
    (k D : ℕ) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hpD : p * (D : ℝ) ≤ 1) (r : ℕ) :
    p * signedRegularSurvival k D p r ^ (k - 1) ≤ 1 := by
  have hy := signedRegularSurvival_mem_Icc k D hp₀ hp₁ hpD r
  exact mul_le_one₀ hp₁ (pow_nonneg hy.1 _) (pow_le_one₀ hy.1 hy.2)

/-- Algebraic form of one signed-isolation survival step as an explicit
decrement. -/
lemma signedRegularSurvivalStep_eq_sub
    {k : ℕ} (hk : 0 < k) (D : ℕ) (p y : ℝ) :
    signedRegularSurvivalStep k D p y =
      y - (p * (D : ℝ)) * y ^ k *
        (1 - p * y ^ (k - 1)) ^ (k * D) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simp only [signedRegularSurvivalStep, signedRegularStep,
    Nat.succ_sub_one, pow_succ]
  push_cast
  ring

/-- Bernoulli bounds for the exact isolation factor. -/
lemma signedRegularIsolationFactor_mem_Icc
    (k D : ℕ) {p y : ℝ} (hp₀ : 0 ≤ p)
    (hp₁ : p ≤ 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (1 - (((k * D : ℕ) : ℝ) * p)) ≤
        (1 - p * y ^ (k - 1)) ^ (k * D) ∧
      (1 - p * y ^ (k - 1)) ^ (k * D) ≤ 1 := by
  have hyPow : y ^ (k - 1) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨pow_nonneg hy.1 _, pow_le_one₀ hy.1 hy.2⟩
  have hpy : p * y ^ (k - 1) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hp₀ hyPow.1, mul_le_one₀ hp₁ hyPow.1 hyPow.2⟩
  have hbase : 1 - p * y ^ (k - 1) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [hpy.1, hpy.2]
  constructor
  · have hbern := one_sub_one_sub_pow_le_natCast_mul
      (k * D) hpy.1 hpy.2
    have hscale :
        (((k * D : ℕ) : ℝ) * (p * y ^ (k - 1))) ≤
          (((k * D : ℕ) : ℝ) * p) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact mul_le_of_le_one_right hp₀ hyPow.2
    linarith
  · exact pow_le_one₀ hbase.1 hbase.2

/-- The exact isolation-adjusted decrement telescopes. -/
lemma scaled_sum_signedRegularSurvival_pow_mul_isolation
    {k : ℕ} (hk : 0 < k) (D L : ℕ) (p : ℝ) :
    (p * (D : ℝ)) *
        (∑ r ∈ range L,
          signedRegularSurvival k D p r ^ k *
            (1 - p * signedRegularSurvival k D p r ^ (k - 1)) ^
              (k * D)) =
      1 - signedRegularSurvival k D p L := by
  induction L with
  | zero => simp
  | succ L ih =>
      rw [sum_range_succ, mul_add, ih, signedRegularSurvival_succ,
        signedRegularSurvivalStep_eq_sub hk]
      ring

/-- The unweighted live-profile sum is squeezed by the telescoping
isolation-adjusted decrement. -/
lemma signedRegularSurvival_sum_pow_bounds
    {k : ℕ} (hk : 0 < k) (D L : ℕ) {p : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hpD : p * (D : ℝ) ≤ 1) :
    (p * (D : ℝ)) * (1 - (((k * D : ℕ) : ℝ) * p)) *
          (∑ r ∈ range L, signedRegularSurvival k D p r ^ k) ≤
        1 - signedRegularSurvival k D p L ∧
      1 - signedRegularSurvival k D p L ≤
        (p * (D : ℝ)) *
          (∑ r ∈ range L, signedRegularSurvival k D p r ^ k) := by
  let liveSum : ℝ :=
    ∑ r ∈ range L, signedRegularSurvival k D p r ^ k
  let isolatedSum : ℝ :=
    ∑ r ∈ range L,
      signedRegularSurvival k D p r ^ k *
        (1 - p * signedRegularSurvival k D p r ^ (k - 1)) ^ (k * D)
  have hlower :
      (1 - (((k * D : ℕ) : ℝ) * p)) * liveSum ≤ isolatedSum := by
    dsimp only [liveSum, isolatedSum]
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro r _
    have hy := signedRegularSurvival_mem_Icc k D hp₀ hp₁ hpD r
    have hfactor := signedRegularIsolationFactor_mem_Icc k D hp₀ hp₁ hy
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_right hfactor.1 (pow_nonneg hy.1 k)
  have hupper : isolatedSum ≤ liveSum := by
    dsimp only [liveSum, isolatedSum]
    apply sum_le_sum
    intro r _
    have hy := signedRegularSurvival_mem_Icc k D hp₀ hp₁ hpD r
    have hfactor := signedRegularIsolationFactor_mem_Icc k D hp₀ hp₁ hy
    simpa using mul_le_mul_of_nonneg_left hfactor.2 (pow_nonneg hy.1 k)
  have hscale₀ : 0 ≤ p * (D : ℝ) :=
    mul_nonneg hp₀ (Nat.cast_nonneg D)
  have htelescope :=
    scaled_sum_signedRegularSurvival_pow_mul_isolation hk D L p
  change (p * (D : ℝ)) *
      (1 - (((k * D : ℕ) : ℝ) * p)) * liveSum ≤ _ ∧
    _ ≤ (p * (D : ℝ)) * liveSum
  constructor
  · calc
      (p * (D : ℝ)) *
          (1 - (((k * D : ℕ) : ℝ) * p)) * liveSum =
          (p * (D : ℝ)) *
            ((1 - (((k * D : ℕ) : ℝ) * p)) * liveSum) := by ring
      _ ≤ (p * (D : ℝ)) * isolatedSum :=
        mul_le_mul_of_nonneg_left hlower hscale₀
      _ = 1 - signedRegularSurvival k D p L := by
        simpa [isolatedSum] using htelescope
  · calc
      1 - signedRegularSurvival k D p L =
          (p * (D : ℝ)) * isolatedSum := by
        simpa [isolatedSum] using htelescope.symm
      _ ≤ (p * (D : ℝ)) * liveSum :=
        mul_le_mul_of_nonneg_left hupper hscale₀

/-- The exact signed-isolation trajectory is dominated by the ordinary
Euler trajectory with the Bernoulli lower step size
`beta * (1 - k * beta)`. -/
theorem signedRegularSurvival_le_meanFieldSurvival_collisionAdjusted
    {k D : ℕ} (hk : 0 < k) (hD : 0 < D) {beta : ℝ}
    (hbeta₀ : 0 ≤ beta) (hbeta₁ : beta ≤ 1)
    (hp₁ : beta / (D : ℝ) ≤ 1)
    (hbetaK : (k : ℝ) * beta ≤ 1) (r : ℕ) :
    signedRegularSurvival k D (beta / (D : ℝ)) r ≤
      meanFieldSurvival k (beta * (1 - (k : ℝ) * beta)) r := by
  let p : ℝ := beta / (D : ℝ)
  let alpha : ℝ := beta * (1 - (k : ℝ) * beta)
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hp₀ : 0 ≤ p := div_nonneg hbeta₀ hDreal.le
  have hpD : p * (D : ℝ) = beta := by
    dsimp only [p]
    field_simp
  have hpDle : p * (D : ℝ) ≤ 1 := hpD.le.trans hbeta₁
  have hkDp : (((k * D : ℕ) : ℝ) * p) = (k : ℝ) * beta := by
    dsimp only [p]
    push_cast
    field_simp
  have halpha₀ : 0 ≤ alpha :=
    mul_nonneg hbeta₀ (sub_nonneg.mpr hbetaK)
  have halphaBeta : alpha ≤ beta := by
    dsimp only [alpha]
    nlinarith [mul_nonneg hbeta₀
      (mul_nonneg (Nat.cast_nonneg k) hbeta₀)]
  have halpha₁ : alpha ≤ 1 := halphaBeta.trans hbeta₁
  have halphaK : alpha * (k : ℝ) ≤ 1 := by
    calc
      alpha * (k : ℝ) ≤ beta * (k : ℝ) :=
        mul_le_mul_of_nonneg_right halphaBeta (Nat.cast_nonneg k)
      _ = (k : ℝ) * beta := by ring
      _ ≤ 1 := hbetaK
  induction r with
  | zero => simp [alpha, p]
  | succ r ih =>
      let ys := signedRegularSurvival k D p r
      let ym := meanFieldSurvival k alpha r
      have hys : ys ∈ Set.Icc (0 : ℝ) 1 :=
        signedRegularSurvival_mem_Icc k D hp₀ hp₁ hpDle r
      have hym : ym ∈ Set.Icc (0 : ℝ) 1 :=
        meanFieldSurvival_mem_Icc hk halpha₀ halpha₁ r
      have hfactor :=
        (signedRegularIsolationFactor_mem_Icc k D hp₀ hp₁ hys).1
      rw [hkDp] at hfactor
      have hcoeff :
          beta * ys ^ k * (1 - (k : ℝ) * beta) ≤
            beta * ys ^ k *
              (1 - p * ys ^ (k - 1)) ^ (k * D) :=
        mul_le_mul_of_nonneg_left hfactor
          (mul_nonneg hbeta₀ (pow_nonneg hys.1 k))
      have hpoint :
          signedRegularSurvivalStep k D p ys ≤
            ys - alpha * ys ^ k := by
        calc
          signedRegularSurvivalStep k D p ys =
              ys - beta * ys ^ k *
                (1 - p * ys ^ (k - 1)) ^ (k * D) := by
            rw [signedRegularSurvivalStep_eq_sub hk, hpD]
          _ ≤ ys - beta * ys ^ k * (1 - (k : ℝ) * beta) :=
            sub_le_sub_left hcoeff ys
          _ = ys - alpha * ys ^ k := by
            dsimp only [alpha]
            ring
      have hmono : ys - alpha * ys ^ k ≤ ym - alpha * ym ^ k :=
        sub_mul_pow_mono_on_Icc k halpha₀ halphaK hys.1 ih hym.2
      simpa [signedRegularSurvival_succ, meanFieldSurvival_succ, ys, ym,
        p, alpha] using hpoint.trans hmono

/-- Consequently, whenever `k * beta < 1`, the signed-isolation reference
trajectory reaches every positive target after finitely many rounds. -/
theorem exists_signedRegularSurvival_lt
    {k D : ℕ} (hk : 0 < k) (hD : 0 < D) {beta epsilon : ℝ}
    (hbeta₀ : 0 < beta) (hbeta₁ : beta ≤ 1)
    (hp₁ : beta / (D : ℝ) ≤ 1)
    (hbetaK : (k : ℝ) * beta < 1) (hepsilon : 0 < epsilon) :
    ∃ L : ℕ,
      signedRegularSurvival k D (beta / (D : ℝ)) L < epsilon := by
  let alpha : ℝ := beta * (1 - (k : ℝ) * beta)
  have halpha₀ : 0 < alpha :=
    mul_pos hbeta₀ (sub_pos.mpr hbetaK)
  have halphaBeta : alpha ≤ beta := by
    dsimp only [alpha]
    nlinarith [mul_nonneg hbeta₀.le
      (mul_nonneg (Nat.cast_nonneg k) hbeta₀.le)]
  obtain ⟨L, hL⟩ := exists_meanFieldSurvival_lt hk halpha₀
    (halphaBeta.trans hbeta₁) hepsilon
  refine ⟨L, ?_⟩
  exact (signedRegularSurvival_le_meanFieldSurvival_collisionAdjusted
    hk hD hbeta₀.le hbeta₁ hp₁ hbetaK.le L).trans_lt hL

/-- Scalar budget for the final marginal, centered directly at the exact
signed-isolation trajectory.  The lower isolation factor is absorbed
multiplicatively, so no separate mean-field trajectory approximation is
needed. -/
lemma signedRegular_marginal_scalar_budget
    {k D L : ℕ} (hk : 0 < k) (hD : 0 < D)
    {beta rho zeta : ℝ}
    (hbeta₀ : 0 ≤ beta) (hbeta₁ : beta ≤ 1)
    (hp₁ : beta / (D : ℝ) ≤ 1)
    (hrho₀ : 0 ≤ rho) (hzeta₀ : 0 ≤ zeta) (hzeta₁ : zeta ≤ 1)
    (hcollision : (k : ℝ) * beta ≤ zeta / 4)
    (htail₀ : 0 ≤ signedRegularSurvival k D (beta / (D : ℝ)) L)
    (htail : signedRegularSurvival k D (beta / (D : ℝ)) L ≤ zeta / 4)
    (herror : beta * (L : ℝ) * rho ≤ zeta / 4) :
    0 ≤ beta / (D : ℝ) -
        (((k * D : ℕ) : ℝ) * (beta / (D : ℝ)) ^ 2) ∧
      (1 - zeta) / (D : ℝ) ≤
        (beta / (D : ℝ) -
          (((k * D : ℕ) : ℝ) * (beta / (D : ℝ)) ^ 2)) *
          (∑ r ∈ range L,
            (signedRegularSurvival k D (beta / (D : ℝ)) r ^ k - rho)) ∧
      beta / (D : ℝ) *
          (∑ r ∈ range L,
            (signedRegularSurvival k D (beta / (D : ℝ)) r ^ k + rho)) ≤
        (1 + zeta) / (D : ℝ) := by
  let p : ℝ := beta / (D : ℝ)
  let y : ℕ → ℝ := signedRegularSurvival k D p
  let liveSum : ℝ := ∑ r ∈ range L, y r ^ k
  let err : ℝ := beta * (L : ℝ) * rho
  let a : ℝ := 1 - (k : ℝ) * beta
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hp₀ : 0 ≤ p := div_nonneg hbeta₀ hDreal.le
  have hpD : p * (D : ℝ) = beta := by
    dsimp only [p]
    field_simp
  have hkDp : (((k * D : ℕ) : ℝ) * p) = (k : ℝ) * beta := by
    dsimp only [p]
    push_cast
    field_simp
  have hsum := signedRegularSurvival_sum_pow_bounds
    hk D L hp₀ hp₁ (by simpa [hpD] using hbeta₁)
  rw [hpD, hkDp] at hsum
  change beta * a * liveSum ≤ 1 - y L ∧
      1 - y L ≤ beta * liveSum at hsum
  have hkbeta₀ : 0 ≤ (k : ℝ) * beta :=
    mul_nonneg (Nat.cast_nonneg k) hbeta₀
  have hkbeta₁ : (k : ℝ) * beta ≤ 1 := by
    calc
      (k : ℝ) * beta ≤ zeta / 4 := hcollision
      _ ≤ 1 := by linarith
  have ha₀ : 0 ≤ a := sub_nonneg.mpr hkbeta₁
  have ha₁ : a ≤ 1 := by dsimp only [a]; linarith
  have herr₀ : 0 ≤ err := by
    exact mul_nonneg (mul_nonneg hbeta₀ (Nat.cast_nonneg L)) hrho₀
  have hliveSum₀ : 0 ≤ liveSum := by
    dsimp only [liveSum, y]
    exact sum_nonneg fun r _ ↦
      pow_nonneg (signedRegularSurvival_mem_Icc
        k D hp₀ hp₁ (by simpa [hpD] using hbeta₁) r).1 _
  have hqeq :
      beta / (D : ℝ) -
          (((k * D : ℕ) : ℝ) * (beta / (D : ℝ)) ^ 2) =
        beta * a / (D : ℝ) := by
    dsimp only [a]
    push_cast
    field_simp
  have hlowerNumerator :
      1 - zeta ≤ a * (1 - y L - err) := by
    dsimp only [a, y, err]
    nlinarith
  have hupperNumerator : beta * liveSum + err ≤ 1 + zeta := by
    have haerr : a * err ≤ err :=
      mul_le_of_le_one_left herr₀ ha₁
    have hscaled : a * (beta * liveSum + err) ≤ 1 + zeta / 4 := by
      calc
        a * (beta * liveSum + err) = beta * a * liveSum + a * err := by ring
        _ ≤ (1 - y L) + err := add_le_add hsum.1 haerr
        _ ≤ 1 + zeta / 4 := by linarith
    have hkbetaMul :
        (k : ℝ) * beta * (1 + zeta) ≤ zeta / 2 := by
      calc
        (k : ℝ) * beta * (1 + zeta) ≤
            (zeta / 4) * (1 + zeta) :=
          mul_le_mul_of_nonneg_right hcollision (by linarith)
        _ ≤ (zeta / 4) * 2 :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = zeta / 2 := by ring
    have htargetScaled : 1 + zeta / 4 ≤ a * (1 + zeta) := by
      dsimp only [a]
      nlinarith
    have haPos : 0 < a := by
      dsimp only [a]
      nlinarith
    exact le_of_mul_le_mul_left (hscaled.trans htargetScaled) haPos
  constructor
  · rw [hqeq]
    exact div_nonneg (mul_nonneg hbeta₀ ha₀) hDreal.le
  constructor
  · rw [hqeq]
    apply (div_le_iff₀ hDreal).2
    have hliveRewrite :
        (∑ r ∈ range L, (y r ^ k - rho)) =
          liveSum - (L : ℝ) * rho := by
      dsimp only [liveSum]
      rw [sum_sub_distrib]
      simp
    change (1 - zeta) ≤
      (beta * a / (D : ℝ) *
        (∑ r ∈ range L, (y r ^ k - rho))) * (D : ℝ)
    rw [hliveRewrite]
    field_simp
    calc
      1 - zeta ≤ a * (1 - y L - err) := hlowerNumerator
      _ ≤ beta * a * (liveSum - (L : ℝ) * rho) := by
        have hscaledLive := mul_le_mul_of_nonneg_left hsum.2 ha₀
        dsimp only [err]
        nlinarith
      _ = beta * a * (liveSum - (L : ℝ) * rho) := rfl
  · apply (le_div_iff₀ hDreal).2
    have hliveRewrite :
        (∑ r ∈ range L, (y r ^ k + rho)) =
          liveSum + (L : ℝ) * rho := by
      dsimp only [liveSum]
      rw [sum_add_distrib]
      simp
    change (beta / (D : ℝ) *
      (∑ r ∈ range L, (y r ^ k + rho))) * (D : ℝ) ≤ 1 + zeta
    rw [hliveRewrite]
    field_simp
    simpa [err, mul_add, mul_assoc] using hupperNumerator

/-- Complete explicit error budget for the `j`-th averaged binomial
moment.  At `j=0` it is just the incoming profile error.  At positive
orders it combines the fixed-family signed error, dominant-family count
deficit, and exceptional outer-family count. -/
def signedRegularMomentError
    (H : FiniteHypergraph V E) (A : Finset V)
    (k D C : ℕ) (p y : ℝ) (orderError : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then orderError A.card else
    let choiceBase :=
      D - (A.card - 1) * C - (j - 1) * (k * C)
    let idealCount := A.card.choose j * D ^ j
    let lowerCount := A.card.choose j * choiceBase ^ j
    let center :=
      p ^ j * (y ^ (A.card + j * (k - 1)) *
        (1 - p * y ^ (k - 1)) ^ (j * k * D))
    (∑ F ∈ H.goodMatchingMeetingFamilies A j,
        p ^ F.card *
          H.staticConflictSignedError A F k C p y orderError) +
      ((idealCount - lowerCount : ℕ) : ℝ) * center +
      ((A.card ^ 2 * C * (A.card * D) ^ (j - 1) : ℕ) : ℝ) * p ^ j

/-- Finite-conflict-order version of `signedRegularMomentError`. -/
def signedRegularMomentErrorCutoff
    (H : FiniteHypergraph V E) (A : Finset V)
    (k D C : ℕ) (p y : ℝ) (Qcut : ℕ)
    (orderError : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j = 0 then orderError A.card else
    let choiceBase :=
      D - (A.card - 1) * C - (j - 1) * (k * C)
    let idealCount := A.card.choose j * D ^ j
    let lowerCount := A.card.choose j * choiceBase ^ j
    let center :=
      p ^ j * (y ^ (A.card + j * (k - 1)) *
        (1 - p * y ^ (k - 1)) ^ (j * k * D))
    (∑ F ∈ H.goodMatchingMeetingFamilies A j,
        p ^ F.card * H.staticConflictSignedErrorCutoff
          A F k C p y Qcut orderError) +
      ((idealCount - lowerCount : ℕ) : ℝ) * center +
      ((A.card ^ 2 * C * (A.card * D) ^ (j - 1) : ℕ) : ℝ) * p ^ j

lemma staticConflictSignedError_nonneg
    (H : FiniteHypergraph V E) (A : Finset V) (F : Finset E)
    (k C : ℕ) {p y : ℝ} (hp₀ : 0 ≤ p) (hy₀ : 0 ≤ y)
    (orderError : ℕ → ℝ) (herror₀ : ∀ a, 0 ≤ orderError a) :
    0 ≤ H.staticConflictSignedError A F k C p y orderError := by
  unfold staticConflictSignedError
  apply add_nonneg
  · apply sum_nonneg
    intro q _
    exact mul_nonneg (pow_nonneg (abs_nonneg p) _)
      (add_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (herror₀ _))
        (Nat.cast_nonneg _))
  · exact mul_nonneg (pow_nonneg hy₀ _)
      (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg hp₀ (pow_nonneg hy₀ _)))

lemma signedRegularMomentError_nonneg
    (H : FiniteHypergraph V E) (A : Finset V)
    (k D C : ℕ) {p y : ℝ} (hp₀ : 0 ≤ p)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpY : p * y ^ (k - 1) ≤ 1)
    (orderError : ℕ → ℝ) (herror₀ : ∀ a, 0 ≤ orderError a)
    (j : ℕ) :
    0 ≤ H.signedRegularMomentError A k D C p y orderError j := by
  unfold signedRegularMomentError
  split_ifs with hj
  · exact herror₀ _
  · have hz₀ : 0 ≤ 1 - p * y ^ (k - 1) := sub_nonneg.mpr hpY
    apply add_nonneg
    · apply add_nonneg
      · apply sum_nonneg
        intro F _
        exact mul_nonneg (pow_nonneg hp₀ _)
          (H.staticConflictSignedError_nonneg A F k C hp₀ hy.1
            orderError herror₀)
      · exact mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (pow_nonneg hp₀ _)
            (mul_nonneg (pow_nonneg hy.1 _) (pow_nonneg hz₀ _)))
    · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp₀ _)

lemma staticConflictSignedErrorCutoff_nonneg
    (H : FiniteHypergraph V E) (A : Finset V) (F : Finset E)
    (k C : ℕ) {p y : ℝ} (hp₀ : 0 ≤ p) (hy₀ : 0 ≤ y)
    (Qcut : ℕ) (orderError : ℕ → ℝ)
    (herror₀ : ∀ a, 0 ≤ orderError a) :
    0 ≤ H.staticConflictSignedErrorCutoff
      A F k C p y Qcut orderError := by
  unfold staticConflictSignedErrorCutoff
  apply add_nonneg
  · apply sum_nonneg
    intro q _
    apply mul_nonneg (pow_nonneg (abs_nonneg p) _)
    split_ifs
    · exact add_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (herror₀ _))
        (Nat.cast_nonneg _)
    · exact Nat.cast_nonneg _
  · exact mul_nonneg (pow_nonneg hy₀ _)
      (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg hp₀ (pow_nonneg hy₀ _)))

lemma signedRegularMomentErrorCutoff_nonneg
    (H : FiniteHypergraph V E) (A : Finset V)
    (k D C : ℕ) {p y : ℝ} (hp₀ : 0 ≤ p)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpY : p * y ^ (k - 1) ≤ 1)
    (Qcut : ℕ) (orderError : ℕ → ℝ)
    (herror₀ : ∀ a, 0 ≤ orderError a) (j : ℕ) :
    0 ≤ H.signedRegularMomentErrorCutoff
      A k D C p y Qcut orderError j := by
  unfold signedRegularMomentErrorCutoff
  split_ifs
  · exact herror₀ _
  · have hz₀ : 0 ≤ 1 - p * y ^ (k - 1) := sub_nonneg.mpr hpY
    apply add_nonneg
    · apply add_nonneg
      · apply sum_nonneg
        intro F _
        exact mul_nonneg (pow_nonneg hp₀ _)
          (H.staticConflictSignedErrorCutoff_nonneg
            A F k C hp₀ hy.1 Qcut orderError herror₀)
      · exact mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (pow_nonneg hp₀ _)
            (mul_nonneg (pow_nonneg hy.1 _) (pow_nonneg hz₀ _)))
    · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp₀ _)

/-- Exact all-order family squeeze after averaging over the first `r`
rounds.  The lower transition coefficient retains the full isolation
product; no Taylor or quadratic truncation is used. -/
theorem averagedInnerNewAcceptedMeetingChooseMoment_mem_Icc
    (H : FiniteHypergraph V E) {k D : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (r : ℕ) (M : Finset E) (A : Finset V) (j : ℕ)
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    H.averagedInnerNewAcceptedMeetingChooseMoment
        (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M A j ∈
      Set.Icc
        (p ^ j * (1 - p) ^ (j * k * D) *
          H.matchingFamilyJointMass
            (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M A j)
        (p ^ j *
          H.matchingFamilyJointMass
            (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M A j) := by
  let w : Finset E → ℝ :=
    FiniteNibble.bernoulliMass univ (fun _ ↦ p)
  let oldIndicator : (Fin r → Finset E) → ℝ := fun X ↦
    if ∀ v ∈ A,
        H.UncoveredBy ((List.ofFn X).foldl H.innerStep M) v
      then 1 else 0
  let liveIndicator : Finset E → (Fin r → Finset E) → ℝ := fun F X ↦
    if ∀ e ∈ F,
        H.InnerLive ((List.ofFn X).foldl H.innerStep M) e
      then 1 else 0
  let familyAverage : Finset E → ℝ := fun F ↦
    ∑ X : Fin r → Finset E,
      FiniteProduct.productMass w X * oldIndicator X *
        H.innerNewAcceptanceFamilyMass
          ((List.ofFn X).foldl H.innerStep M) (fun _ ↦ p) F
  let lower : ℝ := p ^ j * (1 - p) ^ (j * k * D)
  let upper : ℝ := p ^ j
  have hprod₀ (X : Fin r → Finset E) :
      0 ≤ FiniteProduct.productMass w X := by
    unfold FiniteProduct.productMass w
    exact prod_nonneg fun i _ ↦
      FiniteNibble.bernoulliMass_nonneg (subset_univ (X i))
        (fun _ _ ↦ hp₀) (fun _ _ ↦ hp₁)
  have hold₀ (X : Fin r → Finset E) : 0 ≤ oldIndicator X := by
    dsimp only [oldIndicator]
    split <;> norm_num
  have hfamily (F : Finset E) (hFmem : F ∈ H.matchingMeetingFamilies A j) :
      lower * H.innerJointUncoveredMass w r M
          (A ∪ F.biUnion H.support) ≤ familyAverage F ∧
        familyAverage F ≤ upper * H.innerJointUncoveredMass w r M
          (A ∪ F.biUnion H.support) := by
    have hFcard : F.card = j := (H.mem_matchingMeetingFamilies A j F).1 hFmem |>.2.1
    have hFmatch : H.IsMatching F :=
      (H.mem_matchingMeetingFamilies A j F).1 hFmem |>.2.2
    have hpoint (X : Fin r → Finset E) :
        H.innerNewAcceptanceFamilyMass
            ((List.ofFn X).foldl H.innerStep M) (fun _ ↦ p) F ∈
          Set.Icc (lower * liveIndicator F X) (upper * liveIndicator F X) := by
      simpa [lower, upper, liveIndicator, hFcard] using
        H.innerNewAcceptanceFamilyMass_const_indicator_mem_Icc
          hunif hdeg ((List.ofFn X).foldl H.innerStep M) F hp₀ hp₁ hFmatch
    have hliveAverage :
        (∑ X : Fin r → Finset E,
          FiniteProduct.productMass w X * oldIndicator X *
            liveIndicator F X) =
          H.innerJointUncoveredMass w r M
            (A ∪ F.biUnion H.support) := by
      simpa [w, oldIndicator, liveIndicator] using
        H.sum_productMass_mul_jointUncovered_mul_familyLive
          hk hunif w r M A F
    constructor
    · calc
        lower * H.innerJointUncoveredMass w r M
            (A ∪ F.biUnion H.support) =
            ∑ X : Fin r → Finset E,
              FiniteProduct.productMass w X * oldIndicator X *
                (lower * liveIndicator F X) := by
          rw [← hliveAverage, Finset.mul_sum]
          apply sum_congr rfl
          intro X _
          ring
        _ ≤ familyAverage F := by
          dsimp only [familyAverage]
          apply sum_le_sum
          intro X _
          exact mul_le_mul_of_nonneg_left (hpoint X).1
            (mul_nonneg (hprod₀ X) (hold₀ X))
    · calc
        familyAverage F ≤
            ∑ X : Fin r → Finset E,
              FiniteProduct.productMass w X * oldIndicator X *
                (upper * liveIndicator F X) := by
          dsimp only [familyAverage]
          apply sum_le_sum
          intro X _
          exact mul_le_mul_of_nonneg_left (hpoint X).2
            (mul_nonneg (hprod₀ X) (hold₀ X))
        _ = upper * H.innerJointUncoveredMass w r M
            (A ∪ F.biUnion H.support) := by
          rw [← hliveAverage, Finset.mul_sum]
          apply sum_congr rfl
          intro X _
          ring
  have hmoment :
      H.averagedInnerNewAcceptedMeetingChooseMoment w r M A j =
        ∑ F ∈ H.matchingMeetingFamilies A j, familyAverage F := by
    rw [show w = FiniteNibble.bernoulliMass univ (fun _ ↦ p) from rfl,
      H.averagedInnerNewAcceptedMeetingChooseMoment_eq_sum_matching]
    dsimp only [familyAverage, oldIndicator]
    simp_rw [mul_sum]
    rw [sum_comm]
  rw [hmoment]
  change
    lower * H.matchingFamilyJointMass w r M A j ≤
        ∑ F ∈ H.matchingMeetingFamilies A j, familyAverage F ∧
      (∑ F ∈ H.matchingMeetingFamilies A j, familyAverage F) ≤
        upper * H.matchingFamilyJointMass w r M A j
  unfold matchingFamilyJointMass
  constructor
  · rw [Finset.mul_sum]
    apply sum_le_sum
    intro F hF
    exact (hfamily F hF).1
  · rw [Finset.mul_sum]
    apply sum_le_sum
    intro F hF
    exact (hfamily F hF).2

/-- Exact all-order tower recurrence.  It is the untruncated replacement
for the quadratic Bonferroni recurrence: every independent higher-order
term is retained in the alternating binomial-moment sum. -/
theorem innerJointUncoveredMass_succ_eq_sum_alternating_averagedMoments
    (H : FiniteHypergraph V E) (w : Finset E → ℝ)
    (r : ℕ) (M : Finset E) (A : Finset V) :
    H.innerJointUncoveredMass w (r + 1) M A =
      ∑ j ∈ range (A.card + 1),
        (-1 : ℝ) ^ j *
          H.averagedInnerNewAcceptedMeetingChooseMoment w r M A j := by
  let state : (Fin r → Finset E) → Finset E := fun X ↦
    (List.ofFn X).foldl H.innerStep M
  have hpoint (X : Fin r → Finset E) (S : Finset E) :
      (if ∀ v ∈ A, H.UncoveredBy (H.innerStep (state X) S) v
        then (1 : ℝ) else 0) =
        (if ∀ v ∈ A, H.UncoveredBy (state X) v then 1 else 0) *
          (∑ j ∈ range (A.card + 1),
            (-1 : ℝ) ^ j *
              (((H.innerNewAcceptedMeeting (state X) S A).card.choose j : ℕ) : ℝ)) := by
    by_cases hA : ∀ v ∈ A, H.UncoveredBy (state X) v
    · have hiff :=
        H.jointUncovered_innerStep_iff_innerNewAcceptedMeeting_eq_empty
          (S := S) hA
      rw [if_pos hA]
      have hcard := H.innerNewAcceptedMeeting_card_le (state X) S A
      rw [real_alternating_sum_range_choose_of_le hcard]
      by_cases hnext : ∀ v ∈ A,
          H.UncoveredBy (H.innerStep (state X) S) v
      · have hempty := hiff.mp hnext
        have hcardzero :
            (H.innerNewAcceptedMeeting (state X) S A).card = 0 := by
          simp [hempty]
        rw [if_pos hnext, if_pos hcardzero]
        norm_num
      · have hne : H.innerNewAcceptedMeeting (state X) S A ≠ ∅ := by
          exact fun hempty ↦ hnext (hiff.mpr hempty)
        have hcardne :
            (H.innerNewAcceptedMeeting (state X) S A).card ≠ 0 := by
          simpa [card_eq_zero] using hne
        rw [if_neg hnext, if_neg hcardne]
        norm_num
    · have hnext : ¬∀ v ∈ A,
          H.UncoveredBy (H.innerStep (state X) S) v :=
        H.not_jointUncovered_innerStep hA
      simp [hA, hnext]
  rw [H.innerJointUncoveredMass_succ_last]
  change
    (∑ X : Fin r → Finset E,
      FiniteProduct.productMass w X *
        ∑ S : Finset E, w S *
          if ∀ v ∈ A, H.UncoveredBy (H.innerStep (state X) S) v
          then 1 else 0) = _
  simp_rw [hpoint]
  unfold averagedInnerNewAcceptedMeetingChooseMoment
  change
    (∑ X : Fin r → Finset E,
      FiniteProduct.productMass w X *
        ∑ S : Finset E, w S *
          ((if ∀ v ∈ A, H.UncoveredBy (state X) v then 1 else 0) *
            ∑ j ∈ range (A.card + 1),
              (-1 : ℝ) ^ j *
                (((H.innerNewAcceptedMeeting (state X) S A).card.choose j : ℕ) : ℝ))) = _
  calc
    (∑ X : Fin r → Finset E,
      FiniteProduct.productMass w X *
        ∑ S : Finset E, w S *
          ((if ∀ v ∈ A, H.UncoveredBy (state X) v then 1 else 0) *
            ∑ j ∈ range (A.card + 1),
              (-1 : ℝ) ^ j *
                (((H.innerNewAcceptedMeeting (state X) S A).card.choose j : ℕ) : ℝ))) =
        ∑ X : Fin r → Finset E, ∑ S : Finset E,
          ∑ j ∈ range (A.card + 1),
            FiniteProduct.productMass w X *
              (w S *
                ((if ∀ v ∈ A, H.UncoveredBy (state X) v then 1 else 0) *
                  ((-1 : ℝ) ^ j *
                    (((H.innerNewAcceptedMeeting
                      (state X) S A).card.choose j : ℕ) : ℝ)))) := by
      apply sum_congr rfl
      intro X _
      rw [mul_sum]
      apply sum_congr rfl
      intro S _
      simp_rw [mul_sum]
    _ = ∑ X : Fin r → Finset E, ∑ j ∈ range (A.card + 1),
          ∑ S : Finset E,
            FiniteProduct.productMass w X *
              (w S *
                ((if ∀ v ∈ A, H.UncoveredBy (state X) v then 1 else 0) *
                  ((-1 : ℝ) ^ j *
                    (((H.innerNewAcceptedMeeting
                      (state X) S A).card.choose j : ℕ) : ℝ)))) := by
      apply sum_congr rfl
      intro X _
      rw [sum_comm]
    _ = ∑ j ∈ range (A.card + 1),
          ∑ X : Fin r → Finset E, ∑ S : Finset E,
            FiniteProduct.productMass w X *
              (w S *
                ((if ∀ v ∈ A, H.UncoveredBy (state X) v then 1 else 0) *
                  ((-1 : ℝ) ^ j *
                    (((H.innerNewAcceptedMeeting
                      (state X) S A).card.choose j : ℕ) : ℝ)))) := by
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro j _
      rw [mul_sum]
      apply sum_congr rfl
      intro X _
      rw [mul_sum]
      rw [mul_sum]
      apply sum_congr rfl
      intro S _
      ring

/-- Exact parity-split one-step interval from two-sided averaged moment
bounds.  The lower endpoint uses lower bounds for even moments and upper
bounds for odd moments; the upper endpoint uses the opposite choices. -/
theorem innerJointUncoveredMass_succ_mem_Icc_of_averagedMoments_mem_Icc
    (H : FiniteHypergraph V E) (w : Finset E → ℝ)
    (r : ℕ) (M : Finset E) (A : Finset V)
    (lower upper : ℕ → ℝ)
    (hmoment : ∀ j, j ≤ A.card →
      H.averagedInnerNewAcceptedMeetingChooseMoment w r M A j ∈
        Set.Icc (lower j) (upper j)) :
    H.innerJointUncoveredMass w (r + 1) M A ∈
      Set.Icc
        (∑ j ∈ range (A.card + 1), (-1 : ℝ) ^ j *
          if Even j then lower j else upper j)
        (∑ j ∈ range (A.card + 1), (-1 : ℝ) ^ j *
          if Even j then upper j else lower j) := by
  rw [H.innerJointUncoveredMass_succ_eq_sum_alternating_averagedMoments]
  constructor
  · apply sum_le_sum
    intro j hj
    have hjle : j ≤ A.card := Nat.le_of_lt_succ (mem_range.mp hj)
    have hjBounds := hmoment j hjle
    by_cases hjEven : Even j
    · rw [if_pos hjEven, hjEven.neg_one_pow, one_mul]
      simpa using hjBounds.1
    · have hjOdd : Odd j := Nat.not_even_iff_odd.mp hjEven
      rw [if_neg hjEven, hjOdd.neg_one_pow, neg_one_mul]
      simpa using neg_le_neg hjBounds.2
  · apply sum_le_sum
    intro j hj
    have hjle : j ≤ A.card := Nat.le_of_lt_succ (mem_range.mp hj)
    have hjBounds := hmoment j hjle
    by_cases hjEven : Even j
    · rw [if_pos hjEven, hjEven.neg_one_pow, one_mul]
      simpa using hjBounds.2
    · have hjOdd : Odd j := Nat.not_even_iff_odd.mp hjEven
      rw [if_neg hjEven, hjOdd.neg_one_pow, neg_one_mul]
      simpa using neg_le_neg hjBounds.1

/-- Averaged all-order product estimate.  A cardinality-weighted estimate
of the exact averaged moments now gives the joint-survival recurrence with
no quadratic truncation error. -/
theorem innerJointUncoveredMass_succ_close_of_averagedMoments_close
    (H : FiniteHypergraph V E) (w : Finset E → ℝ)
    (r : ℕ) (M : Finset E) (A : Finset V)
    (W t : ℝ) (epsilon : ℕ → ℝ)
    (hmoment : ∀ j, j ≤ A.card →
      |H.averagedInnerNewAcceptedMeetingChooseMoment w r M A j -
        W * (A.card.choose j : ℝ) * t ^ j| ≤ epsilon j) :
    |H.innerJointUncoveredMass w (r + 1) M A -
        W * (1 - t) ^ A.card| ≤
      ∑ j ∈ range (A.card + 1), epsilon j := by
  rw [H.innerJointUncoveredMass_succ_eq_sum_alternating_averagedMoments,
    one_sub_pow_eq_sum_alternating_choose, Finset.mul_sum]
  have hcenter :
      (∑ j ∈ range (A.card + 1),
          W * ((-1 : ℝ) ^ j * (A.card.choose j : ℝ) * t ^ j)) =
        ∑ j ∈ range (A.card + 1),
          (-1 : ℝ) ^ j * (W * (A.card.choose j : ℝ) * t ^ j) := by
    apply sum_congr rfl
    intro j _
    ring
  rw [hcenter]
  exact (abs_sum_alternating_sub_le_sum_abs A.card
    (H.averagedInnerNewAcceptedMeetingChooseMoment w r M A)
    (fun j ↦ W * (A.card.choose j : ℝ) * t ^ j)).trans (by
      apply sum_le_sum
      intro j hj
      exact hmoment j (Nat.le_of_lt_succ (mem_range.mp hj)))

/-- One-step all-order joint-survival recurrence for the concrete inner
process on an exactly regular low-codegree hypergraph.  Unlike the earlier
quadratic Bonferroni recurrence, its scalar center retains the full signed
isolation product; every remaining deviation appears in the explicit
finite moment-error sum. -/
theorem innerJointUncoveredMass_succ_close_signedRegularProfile
    (H : FiniteHypergraph V E) {k D C : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k)
    (hreg : ∀ v ∈ H.vertexSet, H.edgeDegree v = D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (r : ℕ) (M : Finset E) (A : Finset V) (hA : A ⊆ H.vertexSet)
    {p y : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpY : p * y ^ (k - 1) ≤ 1)
    (orderError : ℕ → ℝ) (herror₀ : ∀ a, 0 ≤ orderError a)
    (hprofile : ∀ S : Finset V,
      |H.innerJointUncoveredMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M S -
          y ^ S.card| ≤ orderError S.card) :
    |H.innerJointUncoveredMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) (r + 1) M A -
        y ^ A.card *
          (1 - signedRegularStep k D p y) ^ A.card| ≤
      ∑ j ∈ range (A.card + 1),
        H.signedRegularMomentError A k D C p y orderError j := by
  apply H.innerJointUncoveredMass_succ_close_of_averagedMoments_close
    (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M A
      (y ^ A.card) (signedRegularStep k D p y)
      (H.signedRegularMomentError A k D C p y orderError)
  intro j hj
  by_cases hj₀ : j = 0
  · subst j
    simpa [signedRegularStep, signedRegularMomentError] using hprofile A
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj₀
    simpa [signedRegularStep, signedRegularMomentError, hj₀] using
      H.averagedMoment_close_signedRegularMeanField
        hk hunif hreg hpair r M A hA j hjpos hp₀ hp₁ hy hpY
          orderError herror₀ hprofile

/-- The same recurrence centered at the next scalar survival density. -/
theorem innerJointUncoveredMass_succ_close_signedRegularSurvivalStep
    (H : FiniteHypergraph V E) {k D C : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k)
    (hreg : ∀ v ∈ H.vertexSet, H.edgeDegree v = D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (r : ℕ) (M : Finset E) (A : Finset V) (hA : A ⊆ H.vertexSet)
    {p y : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpY : p * y ^ (k - 1) ≤ 1)
    (orderError : ℕ → ℝ) (herror₀ : ∀ a, 0 ≤ orderError a)
    (hprofile : ∀ S : Finset V,
      |H.innerJointUncoveredMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M S -
          y ^ S.card| ≤ orderError S.card) :
    |H.innerJointUncoveredMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) (r + 1) M A -
        signedRegularSurvivalStep k D p y ^ A.card| ≤
      ∑ j ∈ range (A.card + 1),
        H.signedRegularMomentError A k D C p y orderError j := by
  simpa [signedRegularSurvivalStep, mul_pow] using
    H.innerJointUncoveredMass_succ_close_signedRegularProfile
      hk hunif hreg hpair r M A hA hp₀ hp₁ hy hpY
        orderError herror₀ hprofile

/-- Finite-order one-step recurrence.  To control all moment orders
`j≤|A|`, it suffices to know the incoming joint profile through order
`|A| + |A|(k-1) + Qcut(k-1)`.  Higher conflict-family orders are charged by
the explicit binomial tail inside `signedRegularMomentErrorCutoff`. -/
theorem innerJointUncoveredMass_succ_close_signedRegularSurvivalStep_cutoff
    (H : FiniteHypergraph V E) {k D C : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k)
    (hreg : ∀ v ∈ H.vertexSet, H.edgeDegree v = D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (r : ℕ) (M : Finset E) (A : Finset V) (hA : A ⊆ H.vertexSet)
    {p y : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpY : p * y ^ (k - 1) ≤ 1)
    (Qcut : ℕ) (orderError : ℕ → ℝ)
    (herror₀ : ∀ a, 0 ≤ orderError a)
    (hprofile : ∀ S : Finset V,
      S ⊆ H.vertexSet →
      S.card ≤ A.card + A.card * (k - 1) + Qcut * (k - 1) →
      |H.innerJointUncoveredMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M S -
          y ^ S.card| ≤ orderError S.card) :
    |H.innerJointUncoveredMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) (r + 1) M A -
        signedRegularSurvivalStep k D p y ^ A.card| ≤
      ∑ j ∈ range (A.card + 1),
        H.signedRegularMomentErrorCutoff
          A k D C p y Qcut orderError j := by
  have hmoment : ∀ j, j ≤ A.card →
      |H.averagedInnerNewAcceptedMeetingChooseMoment
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M A j -
        y ^ A.card * (A.card.choose j : ℝ) *
          signedRegularStep k D p y ^ j| ≤
        H.signedRegularMomentErrorCutoff
          A k D C p y Qcut orderError j := by
    intro j hjle
    by_cases hj₀ : j = 0
    · subst j
      simpa [signedRegularStep, signedRegularMomentErrorCutoff] using
        hprofile A hA (by omega)
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj₀
      have hprofileJ : ∀ S : Finset V,
          S ⊆ H.vertexSet →
          S.card ≤ A.card + j * (k - 1) + Qcut * (k - 1) →
          |H.innerJointUncoveredMass
              (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M S -
              y ^ S.card| ≤ orderError S.card := by
        intro S hSvertex hS
        apply hprofile S hSvertex
        calc
          S.card ≤ A.card + j * (k - 1) + Qcut * (k - 1) := hS
          _ ≤ A.card + A.card * (k - 1) + Qcut * (k - 1) := by
            gcongr
      simpa [signedRegularStep, signedRegularMomentErrorCutoff, hj₀] using
        H.averagedMoment_close_signedRegularMeanField_cutoff
          hk hunif hreg hpair r M A hA j Qcut hjpos hp₀ hp₁ hy hpY
            orderError herror₀ hprofileJ
  have hmain :=
    H.innerJointUncoveredMass_succ_close_of_averagedMoments_close
      (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r M A
        (y ^ A.card) (signedRegularStep k D p y)
        (H.signedRegularMomentErrorCutoff
          A k D C p y Qcut orderError) hmoment
  simpa [signedRegularSurvivalStep, mul_pow] using hmain

/-- Iteration of the finite-cutoff recurrence through a prescribed backward
order-cap schedule.  This theorem separates the exact probabilistic
induction from the remaining scalar task: it is enough to dominate the
explicit one-step moment-error sum at each round. -/
theorem innerJointUncoveredMass_close_signedRegularSurvival_of_cutoff_induction
    (H : FiniteHypergraph V E) {k D C : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k)
    (hreg : ∀ v ∈ H.vertexSet, H.edgeDegree v = D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (L : ℕ)
    (orderCap conflictCutoff : ℕ → ℕ)
    (profileError : ℕ → ℕ → ℝ)
    (hcap : ∀ r, r < L →
      orderCap (r + 1) + orderCap (r + 1) * (k - 1) +
          conflictCutoff r * (k - 1) ≤ orderCap r)
    (htrajectory : ∀ r, r ≤ L →
      signedRegularSurvival k D p r ∈ Set.Icc (0 : ℝ) 1)
    (hpY : ∀ r, r < L →
      p * signedRegularSurvival k D p r ^ (k - 1) ≤ 1)
    (herror₀ : ∀ r a, 0 ≤ profileError r a)
    (hstep : ∀ r, r < L → ∀ A : Finset V,
      A ⊆ H.vertexSet → A.card ≤ orderCap (r + 1) →
      (∑ j ∈ range (A.card + 1),
        H.signedRegularMomentErrorCutoff
          A k D C p (signedRegularSurvival k D p r)
            (conflictCutoff r) (profileError r) j) ≤
        profileError (r + 1) A.card) :
    ∀ r, r ≤ L → ∀ A : Finset V,
      A ⊆ H.vertexSet → A.card ≤ orderCap r →
      |H.innerJointUncoveredMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r ∅ A -
        signedRegularSurvival k D p r ^ A.card| ≤
          profileError r A.card := by
  intro r hr
  induction r with
  | zero =>
      intro A _hA _hcard
      rw [H.innerJointUncoveredMass_zero]
      simpa [FiniteHypergraph.UncoveredBy] using herror₀ 0 A.card
  | succ r ih =>
      intro A hA hAcard
      have hrlt : r < L := Nat.lt_of_succ_le hr
      have hprofile : ∀ S : Finset V,
          S ⊆ H.vertexSet →
          S.card ≤ A.card + A.card * (k - 1) +
              conflictCutoff r * (k - 1) →
          |H.innerJointUncoveredMass
              (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r ∅ S -
            signedRegularSurvival k D p r ^ S.card| ≤
              profileError r S.card := by
        intro S hS hScard
        apply ih (Nat.le_of_lt hrlt) S hS
        calc
          S.card ≤ A.card + A.card * (k - 1) +
              conflictCutoff r * (k - 1) := hScard
          _ ≤ orderCap (r + 1) + orderCap (r + 1) * (k - 1) +
              conflictCutoff r * (k - 1) := by gcongr
          _ ≤ orderCap r := hcap r hrlt
      have hone :=
        H.innerJointUncoveredMass_succ_close_signedRegularSurvivalStep_cutoff
          hk hunif hreg hpair r ∅ A hA hp₀ hp₁
            (htrajectory r (Nat.le_of_lt hrlt)) (hpY r hrlt)
            (conflictCutoff r) (profileError r) (herror₀ r) hprofile
      have hbound := hone.trans (hstep r hrlt A hA hAcard)
      simpa [signedRegularSurvival] using hbound

/-- Scaled-sampling specialization of the cutoff induction.  The density
and one-step product hypotheses are automatic from `pD ≤ 1`. -/
theorem innerJointUncoveredMass_close_signedRegularSurvival_of_scaled_cutoff_induction
    (H : FiniteHypergraph V E) {k D C : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k)
    (hreg : ∀ v ∈ H.vertexSet, H.edgeDegree v = D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hpD : p * (D : ℝ) ≤ 1) (L : ℕ)
    (orderCap conflictCutoff : ℕ → ℕ)
    (profileError : ℕ → ℕ → ℝ)
    (hcap : ∀ r, r < L →
      orderCap (r + 1) + orderCap (r + 1) * (k - 1) +
          conflictCutoff r * (k - 1) ≤ orderCap r)
    (herror₀ : ∀ r a, 0 ≤ profileError r a)
    (hstep : ∀ r, r < L → ∀ A : Finset V,
      A ⊆ H.vertexSet → A.card ≤ orderCap (r + 1) →
      (∑ j ∈ range (A.card + 1),
        H.signedRegularMomentErrorCutoff
          A k D C p (signedRegularSurvival k D p r)
            (conflictCutoff r) (profileError r) j) ≤
        profileError (r + 1) A.card) :
    ∀ r, r ≤ L → ∀ A : Finset V,
      A ⊆ H.vertexSet → A.card ≤ orderCap r →
      |H.innerJointUncoveredMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r ∅ A -
        signedRegularSurvival k D p r ^ A.card| ≤
          profileError r A.card := by
  exact H.innerJointUncoveredMass_close_signedRegularSurvival_of_cutoff_induction
    hk hunif hreg hpair hp₀ hp₁ L orderCap conflictCutoff profileError hcap
      (fun r _ ↦ signedRegularSurvival_mem_Icc k D hp₀ hp₁ hpD r)
      (fun r _ ↦ mul_signedRegularSurvival_pow_le_one k D hp₀ hp₁ hpD r)
      herror₀ hstep

/-- Edge-live specialization of the finite-cutoff induction.  Once the
terminal order cap contains `k`, the joint-moment theorem gives the exact
round-by-round live-mass comparison needed by the marginal interface. -/
theorem innerLiveMass_close_signedRegularSurvival_of_scaled_cutoff_induction
    (H : FiniteHypergraph V E) {k D C : ℕ} (hk : 0 < k)
    (hunif : H.IsUniform k)
    (hreg : ∀ v ∈ H.vertexSet, H.edgeDegree v = D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hpD : p * (D : ℝ) ≤ 1) (L : ℕ)
    (orderCap conflictCutoff : ℕ → ℕ)
    (profileError : ℕ → ℕ → ℝ)
    (hcap : ∀ r, r < L →
      orderCap (r + 1) + orderCap (r + 1) * (k - 1) +
          conflictCutoff r * (k - 1) ≤ orderCap r)
    (herror₀ : ∀ r a, 0 ≤ profileError r a)
    (hstep : ∀ r, r < L → ∀ A : Finset V,
      A ⊆ H.vertexSet → A.card ≤ orderCap (r + 1) →
      (∑ j ∈ range (A.card + 1),
        H.signedRegularMomentErrorCutoff
          A k D C p (signedRegularSurvival k D p r)
            (conflictCutoff r) (profileError r) j) ≤
        profileError (r + 1) A.card)
    (r : ℕ) (hr : r ≤ L) (hkcap : k ≤ orderCap r) (e : E) :
    |H.innerLiveMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r ∅ e -
        signedRegularSurvival k D p r ^ k| ≤ profileError r k := by
  rw [H.innerLiveMass_eq_innerJointUncoveredMass_support hk hunif]
  have hmain :=
    H.innerJointUncoveredMass_close_signedRegularSurvival_of_scaled_cutoff_induction
      hk hunif hreg hpair hp₀ hp₁ hpD L orderCap conflictCutoff
        profileError hcap herror₀ hstep r hr (H.support e)
        (H.support_subset_vertexSet e) (by simpa [hunif e] using hkcap)
  simpa [hunif e] using hmain

/-- A uniform live-mass comparison with the signed-isolation reference
trajectory gives the two-sided inner marginal. -/
theorem innerAcceptanceMass_twoSided_of_signedRegular_liveMass_close
    (H : FiniteHypergraph V E) {k D L : ℕ} (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {p rho zeta : ℝ}
    (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hq₀ : 0 ≤ p - (((k * D : ℕ) : ℝ) * p ^ 2))
    (hlower : (1 - zeta) / (D : ℝ) ≤
      (p - (((k * D : ℕ) : ℝ) * p ^ 2)) *
        (∑ r ∈ range L,
          (signedRegularSurvival k D p r ^ k - rho)))
    (hupper : p *
        (∑ r ∈ range L,
          (signedRegularSurvival k D p r ^ k + rho)) ≤
      (1 + zeta) / (D : ℝ))
    (hclose : ∀ e r, r < L →
      |H.innerLiveMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r ∅ e -
        signedRegularSurvival k D p r ^ k| ≤ rho) (e : E) :
    (1 - zeta) / (D : ℝ) ≤
        H.innerAcceptanceMass L (fun _ ↦ p) e ∧
      H.innerAcceptanceMass L (fun _ ↦ p) e ≤
        (1 + zeta) / (D : ℝ) := by
  have hliveLower : ∀ r < L,
      signedRegularSurvival k D p r ^ k - rho ≤
        H.innerLiveMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r ∅ e := by
    intro r hr
    have habs := abs_sub_le_iff.mp (hclose e r hr)
    linarith
  have hliveUpper : ∀ r < L,
      H.innerLiveMass
          (FiniteNibble.bernoulliMass univ (fun _ ↦ p)) r ∅ e ≤
        signedRegularSurvival k D p r ^ k + rho := by
    intro r hr
    have habs := abs_sub_le_iff.mp (hclose e r hr)
    linarith
  constructor
  · exact hlower.trans
      (H.sub_mul_sum_le_innerAcceptanceMass_const_of_innerLiveMass_ge
        hunif hdeg hp₀ hp₁ hq₀ L
          (fun r ↦ signedRegularSurvival k D p r ^ k - rho) hliveLower)
  · exact (H.innerAcceptanceMass_le_mul_sum_of_innerLiveMass_le
      (fun _ ↦ hp₀) (fun _ ↦ hp₁) L e
        (fun r ↦ signedRegularSurvival k D p r ^ k + rho)
          hliveUpper).trans hupper

/-- The complete conditional signed-reference reduction.  A prescribed
finite cutoff hierarchy whose explicit moment errors close at tolerance
`rho`, together with the three scalar budget inequalities, already gives
the required two-sided marginal for every edge.  Thus the only remaining
work is the finite scalar choice of caps, cutoffs, and error bounds. -/
theorem innerAcceptanceMass_twoSided_of_signedRegular_cutoff_induction
    (H : FiniteHypergraph V E) {k D C L : ℕ} (hk : 0 < k) (hD : 0 < D)
    (hunif : H.IsUniform k)
    (hreg : ∀ v ∈ H.vertexSet, H.edgeDegree v = D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {beta rho zeta : ℝ}
    (hbeta₀ : 0 ≤ beta) (hbeta₁ : beta ≤ 1)
    (hp₁ : beta / (D : ℝ) ≤ 1)
    (hrho₀ : 0 ≤ rho) (hzeta₀ : 0 ≤ zeta) (hzeta₁ : zeta ≤ 1)
    (hcollision : (k : ℝ) * beta ≤ zeta / 4)
    (htail : signedRegularSurvival k D (beta / (D : ℝ)) L ≤ zeta / 4)
    (herror : beta * (L : ℝ) * rho ≤ zeta / 4)
    (orderCap conflictCutoff : ℕ → ℕ)
    (profileError : ℕ → ℕ → ℝ)
    (hcap : ∀ r, r < L →
      orderCap (r + 1) + orderCap (r + 1) * (k - 1) +
          conflictCutoff r * (k - 1) ≤ orderCap r)
    (herror₀ : ∀ r a, 0 ≤ profileError r a)
    (hstep : ∀ r, r < L → ∀ A : Finset V,
      A ⊆ H.vertexSet → A.card ≤ orderCap (r + 1) →
      (∑ j ∈ range (A.card + 1),
        H.signedRegularMomentErrorCutoff
          A k D C (beta / (D : ℝ))
            (signedRegularSurvival k D (beta / (D : ℝ)) r)
            (conflictCutoff r) (profileError r) j) ≤
        profileError (r + 1) A.card)
    (hkcap : ∀ r, r < L → k ≤ orderCap r)
    (hprofile : ∀ r, r < L → profileError r k ≤ rho) :
    ∀ e : E,
      (1 - zeta) / (D : ℝ) ≤
          H.innerAcceptanceMass L (fun _ ↦ beta / (D : ℝ)) e ∧
        H.innerAcceptanceMass L (fun _ ↦ beta / (D : ℝ)) e ≤
          (1 + zeta) / (D : ℝ) := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hp₀ : 0 ≤ beta / (D : ℝ) := div_nonneg hbeta₀ hDreal.le
  have hpD : beta / (D : ℝ) * (D : ℝ) ≤ 1 := by
    rw [div_mul_cancel₀ beta hDreal.ne']
    exact hbeta₁
  have htail₀ :
      0 ≤ signedRegularSurvival k D (beta / (D : ℝ)) L :=
    (signedRegularSurvival_mem_Icc k D hp₀ hp₁ hpD L).1
  have hbudget := signedRegular_marginal_scalar_budget
    hk hD hbeta₀ hbeta₁ hp₁ hrho₀ hzeta₀ hzeta₁ hcollision
      htail₀ htail herror
  have hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D := by
    intro v hv
    exact (hreg v hv).le
  intro e
  apply H.innerAcceptanceMass_twoSided_of_signedRegular_liveMass_close
    hunif hdeg hp₀ hp₁ hbudget.1 hbudget.2.1 hbudget.2.2
  intro f r hr
  exact (H.innerLiveMass_close_signedRegularSurvival_of_scaled_cutoff_induction
    hk hunif hreg hpair hp₀ hp₁ hpD L orderCap conflictCutoff profileError
      hcap herror₀ hstep r (Nat.le_of_lt hr) (hkcap r hr) f).trans
        (hprofile r hr)

/-- Geometric/cardinality weighting sums exactly.  This is the preferred
shape for errors in the joint-moment hierarchy. -/
lemma sum_choose_mul_pow (a : ℕ) (c : ℝ) :
    (∑ j ∈ range (a + 1), (a.choose j : ℝ) * c ^ j) = (1 + c) ^ a := by
  have h := add_pow c 1 a
  calc
    (∑ j ∈ range (a + 1), (a.choose j : ℝ) * c ^ j) =
        (c + 1) ^ a := by
      rw [h]
      apply sum_congr rfl
      intro j _
      simp
      ring
    _ = (1 + c) ^ a := by rw [add_comm]

/-- A single cardinality-weighted error coefficient therefore costs only an
exact product factor, rather than a power of two or a quadratic truncation
loss. -/
lemma sum_choose_mul_pow_mul
    (a : ℕ) (c delta : ℝ) :
    (∑ j ∈ range (a + 1),
      delta * (a.choose j : ℝ) * c ^ j) = delta * (1 + c) ^ a := by
  calc
    (∑ j ∈ range (a + 1), delta * (a.choose j : ℝ) * c ^ j) =
        ∑ j ∈ range (a + 1), delta * ((a.choose j : ℝ) * c ^ j) := by
      apply sum_congr rfl
      intro j _
      ring
    _ = delta * (∑ j ∈ range (a + 1), (a.choose j : ℝ) * c ^ j) := by
      rw [Finset.mul_sum]
    _ = delta * (1 + c) ^ a := by rw [sum_choose_mul_pow]

/-- A binomial generating function with bounded mean is controlled by the
corresponding exponential generating function. -/
lemma sum_choose_mul_pow_mul_const_le_exp_mean
    (N : ℕ) {p rho mu : ℝ}
    (hp₀ : 0 ≤ p) (hrho₀ : 0 ≤ rho) (hmean : (N : ℝ) * p ≤ mu) :
    (∑ q ∈ range (N + 1),
      p ^ q * ((N.choose q : ℝ) * rho)) ≤ rho * Real.exp mu := by
  calc
    (∑ q ∈ range (N + 1),
      p ^ q * ((N.choose q : ℝ) * rho)) =
        rho * (1 + p) ^ N := by
      rw [← sum_choose_mul_pow_mul]
      apply sum_congr rfl
      intro q _
      ring
    _ ≤ rho * (Real.exp p) ^ N := by
      apply mul_le_mul_of_nonneg_left _ hrho₀
      exact pow_le_pow_left₀ (by linarith) (by
        simpa [add_comm] using Real.add_one_le_exp p) N
    _ = rho * Real.exp ((N : ℝ) * p) := by
      rw [Real.exp_nat_mul]
    _ ≤ rho * Real.exp mu := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmean) hrho₀

/-- Uniform Poisson-tail cutoff for finite binomial expansions.  If the
binomial mean `N*p` is at most `mu`, then after a cutoff depending only on
`mu` and the requested error, every shifted finite tail is small.  This is
the scalar compactness fact needed to choose conflict cutoffs independently
of the ambient degree. -/
lemma exists_uniform_binomial_tail_cutoff
    {mu epsilon : ℝ} (hmu₀ : 0 ≤ mu) (hepsilon : 0 < epsilon) :
    ∃ Q : ℕ, ∀ (N : ℕ) {p : ℝ}, 0 ≤ p → (N : ℝ) * p ≤ mu →
      (∑ n ∈ range N,
        (N.choose (n + (Q + 1)) : ℝ) * p ^ (n + (Q + 1))) < epsilon := by
  let f : ℕ → ℝ := fun q ↦ mu ^ q / (q.factorial : ℝ)
  have hfsum : Summable f := by
    simpa [f] using Real.summable_pow_div_factorial mu
  have htail : Filter.Tendsto
      (fun i ↦ ∑' n : ℕ, f (n + i)) Filter.atTop (nhds 0) :=
    tendsto_sum_nat_add f
  have hevent : ∀ᶠ i : ℕ in Filter.atTop,
      (∑' n : ℕ, f (n + i)) < epsilon :=
    (tendsto_order.1 htail).2 epsilon hepsilon
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨Q, ?_⟩
  intro N p hp₀ hmean
  have hmean₀ : 0 ≤ (N : ℝ) * p :=
    mul_nonneg (Nat.cast_nonneg N) hp₀
  have hterm (n : ℕ) :
      (N.choose (n + (Q + 1)) : ℝ) * p ^ (n + (Q + 1)) ≤
        f (n + (Q + 1)) := by
    let q := n + (Q + 1)
    have hchoose : (N.choose q : ℝ) ≤
        (N : ℝ) ^ q / (q.factorial : ℝ) :=
      Nat.choose_le_pow_div q N
    calc
      (N.choose q : ℝ) * p ^ q ≤
          ((N : ℝ) ^ q / (q.factorial : ℝ)) * p ^ q :=
        mul_le_mul_of_nonneg_right hchoose (pow_nonneg hp₀ q)
      _ = (((N : ℝ) * p) ^ q) / (q.factorial : ℝ) := by
        rw [mul_pow]
        ring
      _ ≤ mu ^ q / (q.factorial : ℝ) := by
        exact div_le_div_of_nonneg_right
          (pow_le_pow_left₀ hmean₀ hmean q) (Nat.cast_nonneg _)
      _ = f q := rfl
  have hshiftSum : Summable (fun n ↦ f (n + (Q + 1))) :=
    (summable_nat_add_iff (Q + 1)).2 hfsum
  calc
    (∑ n ∈ range N,
        (N.choose (n + (Q + 1)) : ℝ) * p ^ (n + (Q + 1))) ≤
        ∑ n ∈ range N, f (n + (Q + 1)) := by
      exact sum_le_sum fun n _ ↦ hterm n
    _ ≤ ∑' n : ℕ, f (n + (Q + 1)) :=
      hshiftSum.sum_le_tsum (range N) (fun _ _ ↦ by
        exact div_nonneg (pow_nonneg hmu₀ _) (Nat.cast_nonneg _))
    _ < epsilon := hQ (Q + 1) (Nat.le_succ Q)

/-- Reindex the part of a finite sum strictly above a cutoff. -/
lemma sum_range_ite_cutoff_eq_shift
    (f : ℕ → ℝ) (N Q : ℕ) :
    (∑ q ∈ range (N + 1), if q ≤ Q then 0 else f q) =
      ∑ n ∈ range (N - Q), f (n + (Q + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [sum_range_succ, ih]
      by_cases hQN : Q ≤ N
      · have hsub : N + 1 - Q = (N - Q) + 1 := by omega
        rw [hsub, sum_range_succ, if_neg (by omega)]
        have hidx : N - Q + (Q + 1) = N + 1 := by omega
        rw [hidx]
      · have hlt : N < Q := Nat.lt_of_not_ge hQN
        have hsub₀ : N - Q = 0 := Nat.sub_eq_zero_of_le hlt.le
        have hsub₁ : N + 1 - Q = 0 := Nat.sub_eq_zero_of_le (by omega)
        rw [hsub₀, hsub₁, if_pos (by omega)]
        simp

/-- Truncating a nonnegative range sum below `Q` is bounded by the full
range-`Q` sum. -/
lemma sum_range_ite_lt_le_sum_range
    (f : ℕ → ℝ) (N Q : ℕ) (hf : ∀ n, 0 ≤ f n) :
    (∑ n ∈ range N, if n < Q then f n else 0) ≤
      ∑ n ∈ range Q, f n := by
  rw [← sum_filter]
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact mem_range.mpr (mem_filter.mp hn).2
  · intro n _ _
    exact hf n

/-- Scaling the positive-order exceptional-family envelope by
`p=beta/D` leaves one factor `C/D` and a power of the bounded mean `N*p`. -/
lemma scaled_exceptionalEnvelope_eq
    (B k C N n D : ℕ) (beta : ℝ) (hD : D ≠ 0) :
    (beta / (D : ℝ)) ^ (n + 1) *
        (((B ^ 2 + k * B) * C * N ^ n : ℕ) : ℝ) =
      (((B ^ 2 + k * B : ℕ) : ℝ) * ((C : ℝ) / (D : ℝ)) * beta) *
        (((N : ℝ) * (beta / (D : ℝ))) ^ n) := by
  push_cast
  rw [pow_succ, mul_pow]
  field_simp

/-- The preceding cutoff in the literal upper-tail form appearing in
`staticConflictSignedErrorCutoff`. -/
lemma exists_uniform_binomial_upper_tail_cutoff
    {mu epsilon : ℝ} (hmu₀ : 0 ≤ mu) (hepsilon : 0 < epsilon) :
    ∃ Q : ℕ, ∀ (N : ℕ) {p : ℝ}, 0 ≤ p → (N : ℝ) * p ≤ mu →
      (∑ q ∈ range (N + 1),
        if q ≤ Q then 0 else (N.choose q : ℝ) * p ^ q) < epsilon := by
  obtain ⟨Q, hQ⟩ := exists_uniform_binomial_tail_cutoff hmu₀ hepsilon
  refine ⟨Q, ?_⟩
  intro N p hp₀ hmean
  rw [sum_range_ite_cutoff_eq_shift]
  exact (sum_le_sum_of_subset_of_nonneg
    ((range_subset_range).2 (Nat.sub_le N Q))
    (fun _ _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp₀ _))).trans_lt
      (hQ N hp₀ hmean)

/-- Degree-uniform cutoff for the actual static-conflict binomial tail of a
fixed matching family.  Its mean is bounded by `|F|*k*beta`, so the selected
cutoff is independent of `D` and of the hypergraph. -/
theorem exists_staticConflict_binomial_upper_tail_cutoff
    (H : FiniteHypergraph V E) (F : Finset E) {k D : ℕ}
    (hk : 0 < k) (hD : 0 < D) (hunif : H.IsUniform k)
    (hF : H.IsMatching F)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {beta epsilon : ℝ} (hbeta₀ : 0 ≤ beta) (hepsilon : 0 < epsilon) :
    ∃ Q : ℕ,
      (∑ q ∈ range ((H.innerStaticConflictUnion F).card + 1),
        if q ≤ Q then 0 else
          |beta / (D : ℝ)| ^ q *
            ((H.innerStaticConflictUnion F).card.choose q : ℝ)) < epsilon := by
  let mu : ℝ := ((F.card * k : ℕ) : ℝ) * beta
  have hmu₀ : 0 ≤ mu :=
    mul_nonneg (Nat.cast_nonneg _) hbeta₀
  obtain ⟨Q, hQ⟩ :=
    exists_uniform_binomial_upper_tail_cutoff hmu₀ hepsilon
  refine ⟨Q, ?_⟩
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hp₀ : 0 ≤ beta / (D : ℝ) := div_nonneg hbeta₀ hDreal.le
  have hcardNat := H.card_innerStaticConflictUnion_le F hk hunif hF hdeg
  have hcard : ((H.innerStaticConflictUnion F).card : ℝ) ≤
      ((F.card * k * D : ℕ) : ℝ) := by exact_mod_cast hcardNat
  have hmean : ((H.innerStaticConflictUnion F).card : ℝ) *
      (beta / (D : ℝ)) ≤ mu := by
    calc
      ((H.innerStaticConflictUnion F).card : ℝ) * (beta / (D : ℝ)) ≤
          ((F.card * k * D : ℕ) : ℝ) * (beta / (D : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard hp₀
      _ = mu := by
        dsimp only [mu]
        push_cast
        field_simp
  simpa [abs_of_nonneg hp₀, mul_comm] using
    hQ (H.innerStaticConflictUnion F).card hp₀ hmean

/-- The retained profile-error part of a fixed family's conflict expansion
amplifies by at most `exp (|F|*k*beta)`.  In particular this factor is
uniform in the degree. -/
theorem staticConflict_profileErrorPart_le_exp
    (H : FiniteHypergraph V E) (A : Finset V) (F : Finset E)
    {k D Qcut : ℕ} (hk : 0 < k) (hD : 0 < D)
    (hunif : H.IsUniform k) (hF : H.IsMatching F)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {beta rho : ℝ} (hbeta₀ : 0 ≤ beta) (hrho₀ : 0 ≤ rho)
    (orderError : ℕ → ℝ)
    (horder : ∀ q, q ≤ Qcut →
      orderError (A.card + F.card * (k - 1) + q * (k - 1)) ≤ rho) :
    (∑ q ∈ range ((H.innerStaticConflictUnion F).card + 1),
      (beta / (D : ℝ)) ^ q *
        (if q ≤ Qcut then
          ((H.innerStaticConflictUnion F).card.choose q : ℝ) *
            orderError (A.card + F.card * (k - 1) + q * (k - 1))
        else 0)) ≤
      rho * Real.exp (((F.card * k : ℕ) : ℝ) * beta) := by
  let N := (H.innerStaticConflictUnion F).card
  let p := beta / (D : ℝ)
  let mu := ((F.card * k : ℕ) : ℝ) * beta
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hp₀ : 0 ≤ p := div_nonneg hbeta₀ hDreal.le
  have hcardNat := H.card_innerStaticConflictUnion_le F hk hunif hF hdeg
  have hcard : (N : ℝ) ≤ ((F.card * k * D : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  have hmean : (N : ℝ) * p ≤ mu := by
    calc
      (N : ℝ) * p ≤ ((F.card * k * D : ℕ) : ℝ) * p :=
        mul_le_mul_of_nonneg_right hcard hp₀
      _ = mu := by
        dsimp only [p, mu]
        push_cast
        field_simp
  calc
    (∑ q ∈ range (N + 1),
      p ^ q *
        (if q ≤ Qcut then
          (N.choose q : ℝ) *
            orderError (A.card + F.card * (k - 1) + q * (k - 1))
        else 0)) ≤
        ∑ q ∈ range (N + 1), p ^ q * ((N.choose q : ℝ) * rho) := by
      apply sum_le_sum
      intro q _
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hp₀ q)
      by_cases hq : q ≤ Qcut
      · rw [if_pos hq]
        exact mul_le_mul_of_nonneg_left (horder q hq) (Nat.cast_nonneg _)
      · rw [if_neg hq]
        exact mul_nonneg (Nat.cast_nonneg _) hrho₀
    _ ≤ rho * Real.exp mu :=
      sum_choose_mul_pow_mul_const_le_exp_mean N hp₀ hrho₀ hmean

/-- The error from replacing the actual static-conflict exponent by the
ideal regular exponent is normalized by `D`: the chosen-family loss gives
`|F|/D`, and all low-codegree overlap losses give `C/D`. -/
theorem staticConflict_exponentError_le
    (A : Finset V) (F : Finset E) (k C D : ℕ)
    {beta y : ℝ} (hD : 0 < D) (hbeta₀ : 0 ≤ beta)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    y ^ (A.card + F.card * (k - 1)) *
        (((F.card + (F.card * k) ^ 2 * C * k : ℕ) : ℝ) *
          ((beta / (D : ℝ)) * y ^ (k - 1))) ≤
      (((F.card : ℝ) / (D : ℝ)) +
          (((F.card * k) ^ 2 * k : ℕ) : ℝ) *
            ((C : ℝ) / (D : ℝ))) * beta := by
  let loss : ℕ := F.card + (F.card * k) ^ 2 * C * k
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hp₀ : 0 ≤ beta / (D : ℝ) := div_nonneg hbeta₀ hDreal.le
  have hpow₀ : 0 ≤
      y ^ (A.card + F.card * (k - 1)) * y ^ (k - 1) :=
    mul_nonneg (pow_nonneg hy.1 _) (pow_nonneg hy.1 _)
  have hpow₁ :
      y ^ (A.card + F.card * (k - 1)) * y ^ (k - 1) ≤ 1 := by
    calc
      y ^ (A.card + F.card * (k - 1)) * y ^ (k - 1) ≤ 1 * 1 :=
        mul_le_mul (pow_le_one₀ hy.1 hy.2) (pow_le_one₀ hy.1 hy.2)
          (pow_nonneg hy.1 _) zero_le_one
      _ = 1 := by ring
  have hcoeff₀ : 0 ≤ (loss : ℝ) * (beta / (D : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) hp₀
  calc
    y ^ (A.card + F.card * (k - 1)) *
        (((F.card + (F.card * k) ^ 2 * C * k : ℕ) : ℝ) *
          ((beta / (D : ℝ)) * y ^ (k - 1))) =
        ((loss : ℝ) * (beta / (D : ℝ))) *
          (y ^ (A.card + F.card * (k - 1)) * y ^ (k - 1)) := by
      dsimp only [loss]
      ring
    _ ≤ (loss : ℝ) * (beta / (D : ℝ)) :=
      mul_le_of_le_one_right hcoeff₀ hpow₁
    _ = (((F.card : ℝ) / (D : ℝ)) +
          (((F.card * k) ^ 2 * k : ℕ) : ℝ) *
            ((C : ℝ) / (D : ℝ))) * beta := by
      dsimp only [loss]
      push_cast
      field_simp

/-- The retained exceptional conflict subfamilies contribute only one
factor of `codegree / D`.  The remaining powers are controlled by the
degree-independent mean `|F|*k*beta`. -/
theorem staticConflict_exceptionalPart_le_geometric
    (H : FiniteHypergraph V E) (A : Finset V) (F : Finset E)
    {k D C Qcut : ℕ} (hk : 0 < k) (hD : 0 < D)
    (hunif : H.IsUniform k) (hF : H.IsMatching F)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {beta : ℝ} (hbeta₀ : 0 ≤ beta) :
    (∑ q ∈ range ((H.innerStaticConflictUnion F).card + 1),
      (beta / (D : ℝ)) ^ q *
        (if q ≤ Qcut then
          ((H.exceptionalProfileSubfamilies
            (A ∪ H.familySupport F)
            (H.innerStaticConflictUnion F) q).card : ℝ)
        else 0)) ≤
      (((A ∪ H.familySupport F).card ^ 2 +
          k * (A ∪ H.familySupport F).card : ℕ) : ℝ) *
        ((C : ℝ) / (D : ℝ)) * beta *
          (∑ n ∈ range Qcut,
            (((F.card * k : ℕ) : ℝ) * beta) ^ n) := by
  let B : Finset V := A ∪ H.familySupport F
  let Cset : Finset E := H.innerStaticConflictUnion F
  let p : ℝ := beta / (D : ℝ)
  let mu : ℝ := ((F.card * k : ℕ) : ℝ) * beta
  let base : ℝ := (((B.card ^ 2 + k * B.card : ℕ) : ℝ) *
    ((C : ℝ) / (D : ℝ)) * beta)
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hp₀ : 0 ≤ p := div_nonneg hbeta₀ hDreal.le
  have hbase₀ : 0 ≤ base := by
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (div_nonneg (Nat.cast_nonneg _) hDreal.le))
      hbeta₀
  have hcardNat : Cset.card ≤ F.card * k * D := by
    exact H.card_innerStaticConflictUnion_le F hk hunif hF hdeg
  have hmean : (Cset.card : ℝ) * p ≤ mu := by
    have hcard : (Cset.card : ℝ) ≤ ((F.card * k * D : ℕ) : ℝ) := by
      exact_mod_cast hcardNat
    calc
      (Cset.card : ℝ) * p ≤ ((F.card * k * D : ℕ) : ℝ) * p :=
        mul_le_mul_of_nonneg_right hcard hp₀
      _ = mu := by
        dsimp only [p, mu]
        push_cast
        field_simp
  have hCmeet : Cset ⊆ H.edgesMeeting B := by
    exact H.innerStaticConflictUnion_subset_edgesMeeting_union_familySupport A F
  rw [show H.innerStaticConflictUnion F = Cset by rfl,
    show A ∪ H.familySupport F = B by rfl]
  rw [sum_range_succ']
  simp only [H.exceptionalProfileSubfamilies_zero, card_empty,
    Nat.cast_zero, if_pos (Nat.zero_le Qcut), mul_zero, add_zero]
  calc
    (∑ n ∈ range Cset.card,
      p ^ (n + 1) *
        (if n + 1 ≤ Qcut then
          ((H.exceptionalProfileSubfamilies B Cset (n + 1)).card : ℝ)
        else 0)) ≤
        ∑ n ∈ range Cset.card,
          if n < Qcut then base * mu ^ n else 0 := by
      apply sum_le_sum
      intro n hn
      by_cases hcut : n + 1 ≤ Qcut
      · rw [if_pos hcut, if_pos (by omega)]
        have hexNat := H.exceptionalProfileSubfamilies_card_le_uniform
          B Cset (show 0 < n + 1 by omega) hunif hCmeet hpair
        have hex :
            ((H.exceptionalProfileSubfamilies B Cset (n + 1)).card : ℝ) ≤
              (((B.card ^ 2 + k * B.card) * C * Cset.card ^ n : ℕ) : ℝ) := by
          exact_mod_cast hexNat
        calc
          p ^ (n + 1) *
              ((H.exceptionalProfileSubfamilies B Cset (n + 1)).card : ℝ) ≤
              p ^ (n + 1) *
                (((B.card ^ 2 + k * B.card) * C * Cset.card ^ n : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hex (pow_nonneg hp₀ _)
          _ = base * (((Cset.card : ℝ) * p) ^ n) := by
            simpa [p, base, mul_assoc] using
              (scaled_exceptionalEnvelope_eq B.card k C Cset.card n D beta
                hD.ne')
          _ ≤ base * mu ^ n :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀
                (mul_nonneg (Nat.cast_nonneg _) hp₀) hmean n) hbase₀
      · rw [if_neg hcut, if_neg (by omega)]
        simp
    _ ≤ ∑ n ∈ range Qcut, base * mu ^ n :=
      sum_range_ite_lt_le_sum_range (fun n ↦ base * mu ^ n)
        Cset.card Qcut (fun n ↦ mul_nonneg hbase₀
          (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) hbeta₀) n))
    _ = base * ∑ n ∈ range Qcut, mu ^ n := by rw [Finset.mul_sum]
    _ = (((B.card ^ 2 + k * B.card : ℕ) : ℝ) *
        ((C : ℝ) / (D : ℝ)) * beta) *
          (∑ n ∈ range Qcut, mu ^ n) := rfl

/-- Complete scalar bound for the cutoff static-conflict error of one
dominant outer family.  Its four summands are, respectively, propagated
profile error, exceptional low-codegree families, the discarded binomial
tail, and replacement of the actual isolation exponent by `|F|*k*D`. -/
theorem staticConflictSignedErrorCutoff_le
    (H : FiniteHypergraph V E) (A : Finset V) (F : Finset E)
    {k D C Qcut : ℕ} (hk : 0 < k) (hD : 0 < D)
    (hunif : H.IsUniform k) (hF : H.IsMatching F)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {beta y rho tailBudget : ℝ}
    (hbeta₀ : 0 ≤ beta) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hrho₀ : 0 ≤ rho)
    (orderError : ℕ → ℝ)
    (horder : ∀ q, q ≤ Qcut →
      orderError (A.card + F.card * (k - 1) + q * (k - 1)) ≤ rho)
    (htail :
      (∑ q ∈ range ((H.innerStaticConflictUnion F).card + 1),
        if q ≤ Qcut then 0 else
          (beta / (D : ℝ)) ^ q *
            ((H.innerStaticConflictUnion F).card.choose q : ℝ)) ≤
        tailBudget) :
    H.staticConflictSignedErrorCutoff A F k C
        (beta / (D : ℝ)) y Qcut orderError ≤
      rho * Real.exp (((F.card * k : ℕ) : ℝ) * beta) +
        ((((A ∪ H.familySupport F).card ^ 2 +
            k * (A ∪ H.familySupport F).card : ℕ) : ℝ) *
          ((C : ℝ) / (D : ℝ)) * beta) *
            (∑ n ∈ range Qcut,
              (((F.card * k : ℕ) : ℝ) * beta) ^ n) +
        tailBudget +
        ((((F.card : ℝ) / (D : ℝ)) +
            (((F.card * k) ^ 2 * k : ℕ) : ℝ) *
              ((C : ℝ) / (D : ℝ))) * beta) := by
  let N := (H.innerStaticConflictUnion F).card
  let p : ℝ := beta / (D : ℝ)
  let profilePart : ℝ :=
    ∑ q ∈ range (N + 1), p ^ q *
      (if q ≤ Qcut then
        (N.choose q : ℝ) *
          orderError (A.card + F.card * (k - 1) + q * (k - 1))
      else 0)
  let exceptionalPart : ℝ :=
    ∑ q ∈ range (N + 1), p ^ q *
      (if q ≤ Qcut then
        ((H.exceptionalProfileSubfamilies
          (A ∪ H.familySupport F)
          (H.innerStaticConflictUnion F) q).card : ℝ)
      else 0)
  let tailPart : ℝ :=
    ∑ q ∈ range (N + 1),
      if q ≤ Qcut then 0 else p ^ q * (N.choose q : ℝ)
  let exponentPart : ℝ :=
    y ^ (A.card + F.card * (k - 1)) *
      (((F.card + (F.card * k) ^ 2 * C * k : ℕ) : ℝ) *
        (p * y ^ (k - 1)))
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hp₀ : 0 ≤ p := div_nonneg hbeta₀ hDreal.le
  have hsplit :
      H.staticConflictSignedErrorCutoff A F k C p y Qcut orderError =
        (profilePart + exceptionalPart + tailPart) + exponentPart := by
    unfold staticConflictSignedErrorCutoff
    rw [abs_of_nonneg hp₀]
    congr 1
    · rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply sum_congr rfl
      intro q _
      by_cases hq : q ≤ Qcut <;> simp [profilePart, exceptionalPart,
        tailPart, N, hq] <;> ring
  have hprofile : profilePart ≤
      rho * Real.exp (((F.card * k : ℕ) : ℝ) * beta) := by
    simpa [profilePart, N, p] using
      H.staticConflict_profileErrorPart_le_exp A F hk hD hunif hF hdeg
        hbeta₀ hrho₀ orderError horder
  have hexceptional : exceptionalPart ≤
      ((((A ∪ H.familySupport F).card ^ 2 +
          k * (A ∪ H.familySupport F).card : ℕ) : ℝ) *
        ((C : ℝ) / (D : ℝ)) * beta) *
          (∑ n ∈ range Qcut,
            (((F.card * k : ℕ) : ℝ) * beta) ^ n) := by
    simpa [exceptionalPart, N, p] using
      H.staticConflict_exceptionalPart_le_geometric A F hk hD hunif hF
        hdeg hpair hbeta₀
  have htailPart : tailPart ≤ tailBudget := by
    simpa [tailPart, N, p] using htail
  have hexponent : exponentPart ≤
      (((F.card : ℝ) / (D : ℝ)) +
        (((F.card * k) ^ 2 * k : ℕ) : ℝ) *
          ((C : ℝ) / (D : ℝ))) * beta := by
    simpa [exponentPart, p] using
      staticConflict_exponentError_le A F k C D hD hbeta₀ hy
  rw [hsplit]
  exact add_le_add (add_le_add (add_le_add hprofile hexceptional)
    htailPart) hexponent

/-- Degree powers cancel exactly against the sampling normalization
`p=beta/D`. -/
lemma cast_choose_mul_degreePow_mul_scaledPow_eq
    (a j D : ℕ) (beta delta : ℝ) (hD : D ≠ 0) :
    ((a.choose j * D ^ j : ℕ) : ℝ) *
        (beta / (D : ℝ)) ^ j * delta =
      (a.choose j : ℝ) * beta ^ j * delta := by
  push_cast
  rw [div_pow]
  field_simp

/-- If every dominant outer family has fixed-family error at most `delta`,
then its entire contribution to the `j`-th moment is at most the normalized
binomial weight `choose(|A|,j)*beta^j*delta`.  The two purely combinatorial
outer-family errors are left unchanged for their separate scalar bounds. -/
theorem signedRegularMomentErrorCutoff_le_of_staticBound
    (H : FiniteHypergraph V E) (A : Finset V)
    {k D C Qcut j : ℕ} (hD : 0 < D) (hj : 0 < j)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {beta y delta : ℝ} (hbeta₀ : 0 ≤ beta) (hdelta₀ : 0 ≤ delta)
    (orderError : ℕ → ℝ)
    (hstatic : ∀ F ∈ H.goodMatchingMeetingFamilies A j,
      H.staticConflictSignedErrorCutoff A F k C
        (beta / (D : ℝ)) y Qcut orderError ≤ delta) :
    H.signedRegularMomentErrorCutoff A k D C
        (beta / (D : ℝ)) y Qcut orderError j ≤
      (A.card.choose j : ℝ) * beta ^ j * delta +
        (((A.card.choose j * D ^ j -
            A.card.choose j *
              (D - (A.card - 1) * C - (j - 1) * (k * C)) ^ j : ℕ) : ℝ) *
          ((beta / (D : ℝ)) ^ j *
            (y ^ (A.card + j * (k - 1)) *
              (1 - (beta / (D : ℝ)) * y ^ (k - 1)) ^ (j * k * D)))) +
        (((A.card ^ 2 * C * (A.card * D) ^ (j - 1) : ℕ) : ℝ) *
          (beta / (D : ℝ)) ^ j) := by
  have hjne : j ≠ 0 := Nat.ne_of_gt hj
  let good := H.goodMatchingMeetingFamilies A j
  let p : ℝ := beta / (D : ℝ)
  let deltaTerm : ℝ := (A.card.choose j : ℝ) * beta ^ j * delta
  have hp₀ : 0 ≤ p := div_nonneg hbeta₀ (by exact_mod_cast hD.le)
  have hfamily :
      (∑ F ∈ good, p ^ F.card *
        H.staticConflictSignedErrorCutoff
          A F k C p y Qcut orderError) ≤ deltaTerm := by
    calc
      (∑ F ∈ good, p ^ F.card *
          H.staticConflictSignedErrorCutoff
            A F k C p y Qcut orderError) ≤
          ∑ F ∈ good, p ^ j * delta := by
        apply sum_le_sum
        intro F hF
        have hFcard : F.card = j :=
          ((H.mem_matchingMeetingFamilies A j F).1
            ((H.mem_goodMatchingMeetingFamilies A j F).1 hF).1).2.1
        rw [hFcard]
        exact mul_le_mul_of_nonneg_left (hstatic F hF) (pow_nonneg hp₀ _)
      _ = (good.card : ℝ) * (p ^ j * delta) := by simp
      _ ≤ ((A.card.choose j * D ^ j : ℕ) : ℝ) * (p ^ j * delta) := by
        apply mul_le_mul_of_nonneg_right _
          (mul_nonneg (pow_nonneg hp₀ _) hdelta₀)
        exact_mod_cast H.goodMatchingMeetingFamilies_card_le_choose_mul_pow
          A j D hdeg
      _ = deltaTerm := by
        dsimp only [p, deltaTerm]
        simpa [mul_assoc] using
          cast_choose_mul_degreePow_mul_scaledPow_eq
            A.card j D beta delta hD.ne'
  unfold signedRegularMomentErrorCutoff
  rw [if_neg hjne]
  exact add_le_add (add_le_add hfamily le_rfl) le_rfl

/-- Summed version of `signedRegularMomentErrorCutoff_le_of_staticBound`.
The zeroth moment is exactly the incoming profile error; all positive
moments are reindexed as `j=m+1`. -/
theorem sum_signedRegularMomentErrorCutoff_le_of_staticBounds
    (H : FiniteHypergraph V E) (A : Finset V)
    {k D C Qcut : ℕ} (hD : 0 < D)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {beta y : ℝ} (hbeta₀ : 0 ≤ beta)
    (orderError : ℕ → ℝ) (delta : ℕ → ℝ)
    (hdelta₀ : ∀ j, 0 ≤ delta j)
    (hstatic : ∀ j, 0 < j → ∀ F ∈ H.goodMatchingMeetingFamilies A j,
      H.staticConflictSignedErrorCutoff A F k C
        (beta / (D : ℝ)) y Qcut orderError ≤ delta j) :
    (∑ j ∈ range (A.card + 1),
      H.signedRegularMomentErrorCutoff A k D C
        (beta / (D : ℝ)) y Qcut orderError j) ≤
      (∑ m ∈ range A.card,
        ((A.card.choose (m + 1) : ℝ) * beta ^ (m + 1) * delta (m + 1) +
          (((A.card.choose (m + 1) * D ^ (m + 1) -
              A.card.choose (m + 1) *
                (D - (A.card - 1) * C - m * (k * C)) ^ (m + 1) : ℕ) : ℝ) *
            ((beta / (D : ℝ)) ^ (m + 1) *
              (y ^ (A.card + (m + 1) * (k - 1)) *
                (1 - (beta / (D : ℝ)) * y ^ (k - 1)) ^
                  ((m + 1) * k * D)))) +
          (((A.card ^ 2 * C * (A.card * D) ^ m : ℕ) : ℝ) *
            (beta / (D : ℝ)) ^ (m + 1)))) +
        orderError A.card := by
  rw [sum_range_succ']
  apply add_le_add
  · apply sum_le_sum
    intro m hm
    simpa only [Nat.add_sub_cancel] using
      H.signedRegularMomentErrorCutoff_le_of_staticBound A hD
        (show 0 < m + 1 by omega) hdeg hbeta₀ (hdelta₀ (m + 1))
          orderError (hstatic (m + 1) (by omega))
  · simp [signedRegularMomentErrorCutoff]

/-- The summed dominant-family count deficit is normalized by `D`.  The
two terms on the right are the anchor-collision and previously-chosen-edge
collision losses from sequentially constructing a dominant family. -/
theorem sum_outerFamilyCountDeficit_le
    (a k C D : ℕ) {beta : ℝ} (hD : 0 < D) (hbeta₀ : 0 ≤ beta)
    (hsufficient : ∀ j ∈ range (a + 1), 0 < j →
      (a - 1) * C + (j - 1) * (k * C) ≤ D) :
    (∑ m ∈ range a,
      (((a.choose (m + 1) * D ^ (m + 1) -
          a.choose (m + 1) *
            (D - (a - 1) * C - m * (k * C)) ^ (m + 1) : ℕ) : ℝ) *
        (beta / (D : ℝ)) ^ (m + 1)) ≤
      ((((a : ℝ) - 1) * (C : ℝ)) / (D : ℝ)) *
          ((a : ℝ) * beta * (1 + beta) ^ (a - 1)) +
        (((k : ℝ) * (C : ℝ)) / (D : ℝ)) *
          ((a : ℝ) * ((a : ℝ) - 1) * beta ^ 2 *
            (1 + beta) ^ (a - 2))) := by
  let lowerNat : ℕ → ℕ := fun j ↦
    D - (a - 1) * C - (j - 1) * (k * C)
  let lowerReal : ℕ → ℝ := fun j ↦
    (D : ℝ) - ((a : ℝ) - 1) * (C : ℝ) -
      ((j : ℝ) - 1) * (k : ℝ) * (C : ℝ)
  have hcastLower (j : ℕ) (hjmem : j ∈ range (a + 1)) (hj : 0 < j) :
      (lowerNat j : ℝ) = lowerReal j := by
    have ha : 1 ≤ a := by
      have hjle : j ≤ a := Nat.le_of_lt_succ (mem_range.mp hjmem)
      omega
    have hsum := hsufficient j hjmem hj
    have hx : (a - 1) * C ≤ D := (Nat.le_add_right _ _).trans hsum
    have hy : (j - 1) * (k * C) ≤ D - (a - 1) * C := by omega
    dsimp only [lowerNat, lowerReal]
    rw [Nat.cast_sub hy, Nat.cast_sub hx]
    push_cast
    have hca : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
      simpa using (Nat.cast_sub ha : ((a - 1 : ℕ) : ℝ) = _)
    have hcj : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      simpa using (Nat.cast_sub (Nat.succ_le_iff.mpr hj) :
        ((j - 1 : ℕ) : ℝ) = _)
    rw [hca, hcj]
    ring
  have hlower (j : ℕ) (hjmem : j ∈ range (a + 1)) (hj : 0 < j) :
      0 ≤ lowerReal j ∧ lowerReal j ≤ (D : ℝ) := by
    rw [← hcastLower j hjmem hj]
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have hle : lowerNat j ≤ D := by
      dsimp only [lowerNat]
      exact (Nat.sub_le _ _).trans (Nat.sub_le _ _)
    exact_mod_cast hle
  have hmain := sum_choose_scaledSequentialLower_deficit_le
    a k (D := (D : ℝ)) (degreeLower := (D : ℝ)) (C := (C : ℝ))
      (beta := beta) (by exact_mod_cast hD) hbeta₀ (by
        intro j hjmem hj
        simpa [lowerReal] using hlower j hjmem hj)
  let rawSum : ℝ := (∑ m ∈ range a,
        (((a.choose (m + 1) * D ^ (m + 1) -
            a.choose (m + 1) * lowerNat (m + 1) ^ (m + 1) : ℕ) : ℝ) *
          (beta / (D : ℝ)) ^ (m + 1)))
  let analyticSum : ℝ := (∑ j ∈ range (a + 1),
    (a.choose j : ℝ) * (beta / (D : ℝ)) ^ j *
      ((D : ℝ) ^ j - lowerReal j ^ j))
  have heq : rawSum = analyticSum := by
    dsimp only [rawSum, analyticSum]
    rw [sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one,
      sub_self, mul_zero, add_zero]
    apply sum_congr rfl
    intro m hm
    have hjmem : m + 1 ∈ range (a + 1) := by
      exact mem_range.mpr (Nat.succ_lt_succ (mem_range.mp hm))
    have hlowNat : lowerNat (m + 1) ≤ D := by
      dsimp only [lowerNat]
      omega
    have hpowNat : lowerNat (m + 1) ^ (m + 1) ≤ D ^ (m + 1) :=
      Nat.pow_le_pow_left hlowNat _
    have hmulNat :
        a.choose (m + 1) * lowerNat (m + 1) ^ (m + 1) ≤
          a.choose (m + 1) * D ^ (m + 1) :=
      Nat.mul_le_mul_left _ hpowNat
    rw [Nat.cast_sub hmulNat]
    push_cast
    rw [hcastLower (m + 1) hjmem (by omega)]
    ring
  have hraw : (∑ m ∈ range a,
      (((a.choose (m + 1) * D ^ (m + 1) -
          a.choose (m + 1) *
            (D - (a - 1) * C - m * (k * C)) ^ (m + 1) : ℕ) : ℝ) *
        (beta / (D : ℝ)) ^ (m + 1))) = rawSum := by
    dsimp only [rawSum]
    apply sum_congr rfl
    intro m _
    simp [lowerNat]
  rw [hraw, heq]
  dsimp only [analyticSum]
  simpa [lowerReal] using hmain

/-- The survival and isolation factors multiplying the outer-family count
deficit are both at most one, so the normalized count-deficit bound remains
valid for the actual signed-reference center. -/
theorem sum_outerFamilyCountCenter_le
    (a k C D : ℕ) {beta y : ℝ}
    (hD : 0 < D) (hbeta₀ : 0 ≤ beta)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpY : (beta / (D : ℝ)) * y ^ (k - 1) ≤ 1)
    (hsufficient : ∀ j ∈ range (a + 1), 0 < j →
      (a - 1) * C + (j - 1) * (k * C) ≤ D) :
    (∑ m ∈ range a,
      (((a.choose (m + 1) * D ^ (m + 1) -
          a.choose (m + 1) *
            (D - (a - 1) * C - m * (k * C)) ^ (m + 1) : ℕ) : ℝ) *
        ((beta / (D : ℝ)) ^ (m + 1) *
          (y ^ (a + (m + 1) * (k - 1)) *
            (1 - (beta / (D : ℝ)) * y ^ (k - 1)) ^
              ((m + 1) * k * D))))) ≤
      ((((a : ℝ) - 1) * (C : ℝ)) / (D : ℝ)) *
          ((a : ℝ) * beta * (1 + beta) ^ (a - 1)) +
        (((k : ℝ) * (C : ℝ)) / (D : ℝ)) *
          ((a : ℝ) * ((a : ℝ) - 1) * beta ^ 2 *
            (1 + beta) ^ (a - 2)) := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hp₀ : 0 ≤ beta / (D : ℝ) := div_nonneg hbeta₀ hDreal.le
  have hz : 1 - (beta / (D : ℝ)) * y ^ (k - 1) ∈
      Set.Icc (0 : ℝ) 1 := by
    exact ⟨sub_nonneg.mpr hpY, by
      have := mul_nonneg hp₀ (pow_nonneg hy.1 (k - 1))
      linarith⟩
  have hdrop :
      (∑ m ∈ range a,
        (((a.choose (m + 1) * D ^ (m + 1) -
            a.choose (m + 1) *
              (D - (a - 1) * C - m * (k * C)) ^ (m + 1) : ℕ) : ℝ) *
          ((beta / (D : ℝ)) ^ (m + 1) *
            (y ^ (a + (m + 1) * (k - 1)) *
              (1 - (beta / (D : ℝ)) * y ^ (k - 1)) ^
                ((m + 1) * k * D))))) ≤
        ∑ m ∈ range a,
          (((a.choose (m + 1) * D ^ (m + 1) -
              a.choose (m + 1) *
                (D - (a - 1) * C - m * (k * C)) ^ (m + 1) : ℕ) : ℝ) *
            (beta / (D : ℝ)) ^ (m + 1)) := by
    apply sum_le_sum
    intro m _
    have hcoeff₀ : 0 ≤
        (((a.choose (m + 1) * D ^ (m + 1) -
          a.choose (m + 1) *
            (D - (a - 1) * C - m * (k * C)) ^ (m + 1) : ℕ) : ℝ) *
          (beta / (D : ℝ)) ^ (m + 1)) :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp₀ _)
    have hprofile₁ :
        y ^ (a + (m + 1) * (k - 1)) *
          (1 - (beta / (D : ℝ)) * y ^ (k - 1)) ^ ((m + 1) * k * D) ≤ 1 := by
      calc
        y ^ (a + (m + 1) * (k - 1)) *
            (1 - (beta / (D : ℝ)) * y ^ (k - 1)) ^ ((m + 1) * k * D) ≤
            1 * 1 :=
          mul_le_mul (pow_le_one₀ hy.1 hy.2) (pow_le_one₀ hz.1 hz.2)
            (pow_nonneg hz.1 _) zero_le_one
        _ = 1 := by ring
    calc
      (((a.choose (m + 1) * D ^ (m + 1) -
          a.choose (m + 1) *
            (D - (a - 1) * C - m * (k * C)) ^ (m + 1) : ℕ) : ℝ) *
        ((beta / (D : ℝ)) ^ (m + 1) *
          (y ^ (a + (m + 1) * (k - 1)) *
            (1 - (beta / (D : ℝ)) * y ^ (k - 1)) ^ ((m + 1) * k * D)))) =
          ((((a.choose (m + 1) * D ^ (m + 1) -
            a.choose (m + 1) *
              (D - (a - 1) * C - m * (k * C)) ^ (m + 1) : ℕ) : ℝ) *
            (beta / (D : ℝ)) ^ (m + 1)) *
              (y ^ (a + (m + 1) * (k - 1)) *
                (1 - (beta / (D : ℝ)) * y ^ (k - 1)) ^
                  ((m + 1) * k * D))) := by ring
      _ ≤ (((a.choose (m + 1) * D ^ (m + 1) -
          a.choose (m + 1) *
            (D - (a - 1) * C - m * (k * C)) ^ (m + 1) : ℕ) : ℝ) *
          (beta / (D : ℝ)) ^ (m + 1)) :=
        mul_le_of_le_one_right hcoeff₀ hprofile₁
  exact hdrop.trans
    (sum_outerFamilyCountDeficit_le a k C D hD hbeta₀ hsufficient)

/-- The outer exceptional-family envelope has the same `C/D`
normalization as the inner exceptional conflict families. -/
theorem sum_outerExceptionalFamilyError_le
    (a C D : ℕ) {beta eta : ℝ}
    (hD : 0 < D) (hbeta₀ : 0 ≤ beta)
    (hcodeg : (C : ℝ) ≤ eta * (D : ℝ)) :
    (∑ m ∈ range a,
      (((a ^ 2 * C * (a * D) ^ m : ℕ) : ℝ) *
        (beta / (D : ℝ)) ^ (m + 1))) ≤
      eta * ((a : ℝ) ^ 2) * beta *
        ∑ m ∈ range a, (((a : ℝ) * beta) ^ m) := by
  have hmain := sum_badFamilyEnvelope_shift_le_of_codegree
    a (C := (C : ℝ)) (D := (D : ℝ)) (beta := beta) (eta := eta)
      (by exact_mod_cast hD) hbeta₀ (Nat.cast_nonneg C) hcodeg
  simpa [Nat.cast_pow, mul_comm, mul_left_comm, mul_assoc] using hmain

/-- Fully normalized one-step moment-error sum.  Once every fixed dominant
family is bounded by `delta j`, the remaining two outer-family errors are
explicit multiples of `C/D`. -/
theorem sum_signedRegularMomentErrorCutoff_le_normalized
    (H : FiniteHypergraph V E) (A : Finset V)
    {k D C Qcut : ℕ} (hD : 0 < D)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    {beta y eta : ℝ} (hbeta₀ : 0 ≤ beta)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpY : (beta / (D : ℝ)) * y ^ (k - 1) ≤ 1)
    (hcodeg : (C : ℝ) ≤ eta * (D : ℝ))
    (hsufficient : ∀ j ∈ range (A.card + 1), 0 < j →
      (A.card - 1) * C + (j - 1) * (k * C) ≤ D)
    (orderError : ℕ → ℝ) (delta : ℕ → ℝ)
    (hdelta₀ : ∀ j, 0 ≤ delta j)
    (hstatic : ∀ j, 0 < j → ∀ F ∈ H.goodMatchingMeetingFamilies A j,
      H.staticConflictSignedErrorCutoff A F k C
        (beta / (D : ℝ)) y Qcut orderError ≤ delta j) :
    (∑ j ∈ range (A.card + 1),
      H.signedRegularMomentErrorCutoff A k D C
        (beta / (D : ℝ)) y Qcut orderError j) ≤
      (∑ m ∈ range A.card,
        (A.card.choose (m + 1) : ℝ) * beta ^ (m + 1) * delta (m + 1)) +
      ((((A.card : ℝ) - 1) * (C : ℝ)) / (D : ℝ)) *
        ((A.card : ℝ) * beta * (1 + beta) ^ (A.card - 1)) +
      (((k : ℝ) * (C : ℝ)) / (D : ℝ)) *
        ((A.card : ℝ) * ((A.card : ℝ) - 1) * beta ^ 2 *
          (1 + beta) ^ (A.card - 2)) +
      eta * ((A.card : ℝ) ^ 2) * beta *
        ∑ m ∈ range A.card, (((A.card : ℝ) * beta) ^ m) +
      orderError A.card := by
  let familySum : ℝ := ∑ m ∈ range A.card,
    (A.card.choose (m + 1) : ℝ) * beta ^ (m + 1) * delta (m + 1)
  let countSum : ℝ := ∑ m ∈ range A.card,
    (((A.card.choose (m + 1) * D ^ (m + 1) -
        A.card.choose (m + 1) *
          (D - (A.card - 1) * C - m * (k * C)) ^ (m + 1) : ℕ) : ℝ) *
      ((beta / (D : ℝ)) ^ (m + 1) *
        (y ^ (A.card + (m + 1) * (k - 1)) *
          (1 - (beta / (D : ℝ)) * y ^ (k - 1)) ^
            ((m + 1) * k * D))))
  let badSum : ℝ := ∑ m ∈ range A.card,
    (((A.card ^ 2 * C * (A.card * D) ^ m : ℕ) : ℝ) *
      (beta / (D : ℝ)) ^ (m + 1))
  have hraw := H.sum_signedRegularMomentErrorCutoff_le_of_staticBounds
    A hD hdeg hbeta₀ orderError delta hdelta₀ hstatic
  have hsplit :
      (∑ m ∈ range A.card,
        ((A.card.choose (m + 1) : ℝ) * beta ^ (m + 1) * delta (m + 1) +
          (((A.card.choose (m + 1) * D ^ (m + 1) -
              A.card.choose (m + 1) *
                (D - (A.card - 1) * C - m * (k * C)) ^ (m + 1) : ℕ) : ℝ) *
            ((beta / (D : ℝ)) ^ (m + 1) *
              (y ^ (A.card + (m + 1) * (k - 1)) *
                (1 - (beta / (D : ℝ)) * y ^ (k - 1)) ^
                  ((m + 1) * k * D)))) +
          (((A.card ^ 2 * C * (A.card * D) ^ m : ℕ) : ℝ) *
            (beta / (D : ℝ)) ^ (m + 1)))) =
        familySum + countSum + badSum := by
    dsimp only [familySum, countSum, badSum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have hcount : countSum ≤
      ((((A.card : ℝ) - 1) * (C : ℝ)) / (D : ℝ)) *
          ((A.card : ℝ) * beta * (1 + beta) ^ (A.card - 1)) +
        (((k : ℝ) * (C : ℝ)) / (D : ℝ)) *
          ((A.card : ℝ) * ((A.card : ℝ) - 1) * beta ^ 2 *
            (1 + beta) ^ (A.card - 2)) := by
    simpa [countSum] using sum_outerFamilyCountCenter_le
      A.card k C D hD hbeta₀ hy hpY hsufficient
  have hbad : badSum ≤
      eta * ((A.card : ℝ) ^ 2) * beta *
        ∑ m ∈ range A.card, (((A.card : ℝ) * beta) ^ m) := by
    simpa [badSum] using sum_outerExceptionalFamilyError_le
      A.card C D hD hbeta₀ hcodeg
  calc
    (∑ j ∈ range (A.card + 1),
      H.signedRegularMomentErrorCutoff A k D C
        (beta / (D : ℝ)) y Qcut orderError j) ≤
        (familySum + countSum + badSum) + orderError A.card := by
      rw [hsplit] at hraw
      exact hraw
    _ ≤ ((∑ m ∈ range A.card,
        (A.card.choose (m + 1) : ℝ) * beta ^ (m + 1) * delta (m + 1)) +
        ((((A.card : ℝ) - 1) * (C : ℝ)) / (D : ℝ)) *
          ((A.card : ℝ) * beta * (1 + beta) ^ (A.card - 1)) +
        (((k : ℝ) * (C : ℝ)) / (D : ℝ)) *
          ((A.card : ℝ) * ((A.card : ℝ) - 1) * beta ^ 2 *
            (1 + beta) ^ (A.card - 2)) +
        eta * ((A.card : ℝ) ^ 2) * beta *
          ∑ m ∈ range A.card, (((A.card : ℝ) * beta) ^ m)) +
        orderError A.card := by
      dsimp only [familySum]
      linarith
    _ = _ := rfl

/-- Degree-normalized scalar envelope for the static-conflict expansion of
one dominant `j`-edge outer family over an `a`-vertex joint event. -/
def dominantStaticConflictDelta
    (a j k C D Qcut : ℕ) (beta rho tailBudget : ℝ) : ℝ :=
  rho * Real.exp (((j * k : ℕ) : ℝ) * beta) +
    ((((a + j * (k - 1)) ^ 2 + k * (a + j * (k - 1)) : ℕ) : ℝ) *
      ((C : ℝ) / (D : ℝ)) * beta) *
        (∑ n ∈ range Qcut, (((j * k : ℕ) : ℝ) * beta) ^ n) +
    tailBudget +
    ((((j : ℝ) / (D : ℝ)) +
      (((j * k) ^ 2 * k : ℕ) : ℝ) * ((C : ℝ) / (D : ℝ))) * beta)

/-- Degree-free version of `dominantStaticConflictDelta`, with independent
upper bounds for the codegree ratio and `1/D`. -/
def dominantStaticConflictDeltaEnvelope
    (a j k Qcut : ℕ) (beta rho tailBudget ratio invDegree : ℝ) : ℝ :=
  rho * Real.exp (((j * k : ℕ) : ℝ) * beta) +
    ((((a + j * (k - 1)) ^ 2 + k * (a + j * (k - 1)) : ℕ) : ℝ) *
      ratio * beta) *
        (∑ n ∈ range Qcut, (((j * k : ℕ) : ℝ) * beta) ^ n) +
    tailBudget +
    (((j : ℝ) * invDegree +
      (((j * k) ^ 2 * k : ℕ) : ℝ) * ratio) * beta)

lemma dominantStaticConflictDeltaEnvelope_nonneg
    (a j k Qcut : ℕ) {beta rho tailBudget ratio invDegree : ℝ}
    (hbeta₀ : 0 ≤ beta) (hrho₀ : 0 ≤ rho)
    (htail₀ : 0 ≤ tailBudget) (hratio₀ : 0 ≤ ratio)
    (hinv₀ : 0 ≤ invDegree) :
    0 ≤ dominantStaticConflictDeltaEnvelope a j k Qcut
      beta rho tailBudget ratio invDegree := by
  unfold dominantStaticConflictDeltaEnvelope
  positivity

lemma dominantStaticConflictDelta_le_envelope
    (a j k C D Qcut : ℕ) {beta rho tailBudget ratio invDegree : ℝ}
    (hD : 0 < D) (hbeta₀ : 0 ≤ beta) (hrho₀ : 0 ≤ rho)
    (htail₀ : 0 ≤ tailBudget) (hratio₀ : 0 ≤ ratio)
    (hinv₀ : 0 ≤ invDegree)
    (hratio : (C : ℝ) / (D : ℝ) ≤ ratio)
    (hinv : 1 / (D : ℝ) ≤ invDegree) :
    dominantStaticConflictDelta a j k C D Qcut beta rho tailBudget ≤
      dominantStaticConflictDeltaEnvelope a j k Qcut
        beta rho tailBudget ratio invDegree := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hsum₀ : 0 ≤
      ∑ n ∈ range Qcut, (((j * k : ℕ) : ℝ) * beta) ^ n :=
    sum_nonneg fun n _ ↦ pow_nonneg
      (mul_nonneg (Nat.cast_nonneg _) hbeta₀) n
  have hjdiv : (j : ℝ) / (D : ℝ) ≤ (j : ℝ) * invDegree := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hinv)
      (Nat.cast_nonneg j)
  unfold dominantStaticConflictDelta dominantStaticConflictDeltaEnvelope
  gcongr

lemma dominantStaticConflictDelta_nonneg
    (a j k C D Qcut : ℕ) {beta rho tailBudget : ℝ}
    (hD : 0 < D) (hbeta₀ : 0 ≤ beta) (hrho₀ : 0 ≤ rho)
    (htail₀ : 0 ≤ tailBudget) :
    0 ≤ dominantStaticConflictDelta a j k C D Qcut beta rho tailBudget := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  unfold dominantStaticConflictDelta
  positivity

/-- The one-family master estimate in a form depending only on its order
`j`, the current joint-set order `a`, and scalar parameters. -/
theorem staticConflictSignedErrorCutoff_le_dominantDelta
    (H : FiniteHypergraph V E) (A : Finset V) (F : Finset E)
    {k D C Qcut j : ℕ} (hk : 0 < k) (hD : 0 < D)
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (hFgood : F ∈ H.goodMatchingMeetingFamilies A j)
    {beta y rho tailBudget : ℝ}
    (hbeta₀ : 0 ≤ beta)
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hrho₀ : 0 ≤ rho)
    (orderError : ℕ → ℝ)
    (horder : ∀ q, q ≤ Qcut →
      orderError (A.card + j * (k - 1) + q * (k - 1)) ≤ rho)
    (htail :
      (∑ q ∈ range ((H.innerStaticConflictUnion F).card + 1),
        if q ≤ Qcut then 0 else
          (beta / (D : ℝ)) ^ q *
            ((H.innerStaticConflictUnion F).card.choose q : ℝ)) ≤
        tailBudget) :
    H.staticConflictSignedErrorCutoff A F k C
        (beta / (D : ℝ)) y Qcut orderError ≤
      dominantStaticConflictDelta A.card j k C D Qcut
        beta rho tailBudget := by
  have hdata := (H.mem_goodMatchingMeetingFamilies A j F).1 hFgood
  have hmeeting := (H.mem_matchingMeetingFamilies A j F).1 hdata.1
  have hFcard : F.card = j := hmeeting.2.1
  have hFmatching : H.IsMatching F := hmeeting.2.2
  have hBcard : (A ∪ H.familySupport F).card =
      A.card + j * (k - 1) := by
    have hcard := H.card_union_biUnion_support_eq_of_matching_subset_singleMeeting
      A F hk hunif hFmatching hdata.2
    simpa [familySupport, hFcard] using hcard
  have hbound := H.staticConflictSignedErrorCutoff_le A F hk hD hunif
    hFmatching hdeg hpair hbeta₀ hy hrho₀ orderError
      (fun q hq ↦ by simpa [hFcard] using horder q hq) htail
  simpa [dominantStaticConflictDelta, hFcard, hBcard] using hbound

/-- Uniform-tail form of the preceding fixed-family estimate.  A cutoff
chosen for the maximal mean `a*k*beta` works simultaneously for every
dominant family of order `j ≤ a`. -/
theorem staticConflictSignedErrorCutoff_le_dominantDelta_of_uniformTail
    (H : FiniteHypergraph V E) (A : Finset V) (F : Finset E)
    {a k D C Qcut j : ℕ} (hk : 0 < k) (hD : 0 < D)
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (hFgood : F ∈ H.goodMatchingMeetingFamilies A j) (hja : j ≤ a)
    {beta y rho tailBudget : ℝ}
    (hbeta₀ : 0 ≤ beta) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hrho₀ : 0 ≤ rho)
    (orderError : ℕ → ℝ)
    (horder : ∀ q, q ≤ Qcut →
      orderError (A.card + j * (k - 1) + q * (k - 1)) ≤ rho)
    (huniformTail : ∀ (N : ℕ) {p : ℝ}, 0 ≤ p →
      (N : ℝ) * p ≤ ((a * k : ℕ) : ℝ) * beta →
      (∑ q ∈ range (N + 1),
        if q ≤ Qcut then 0 else (N.choose q : ℝ) * p ^ q) ≤
          tailBudget) :
    H.staticConflictSignedErrorCutoff A F k C
        (beta / (D : ℝ)) y Qcut orderError ≤
      dominantStaticConflictDelta A.card j k C D Qcut
        beta rho tailBudget := by
  have hdata := (H.mem_goodMatchingMeetingFamilies A j F).1 hFgood
  have hmeeting := (H.mem_matchingMeetingFamilies A j F).1 hdata.1
  have hFcard : F.card = j := hmeeting.2.1
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hp₀ : 0 ≤ beta / (D : ℝ) := div_nonneg hbeta₀ hDreal.le
  have hcardNat := H.card_innerStaticConflictUnion_le F hk hunif
    hmeeting.2.2 hdeg
  have hcard : ((H.innerStaticConflictUnion F).card : ℝ) ≤
      ((j * k * D : ℕ) : ℝ) := by
    rw [← hFcard]
    exact_mod_cast hcardNat
  have hmean : ((H.innerStaticConflictUnion F).card : ℝ) *
      (beta / (D : ℝ)) ≤ ((a * k : ℕ) : ℝ) * beta := by
    calc
      ((H.innerStaticConflictUnion F).card : ℝ) *
          (beta / (D : ℝ)) ≤
          ((j * k * D : ℕ) : ℝ) * (beta / (D : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard hp₀
      _ = ((j * k : ℕ) : ℝ) * beta := by
        push_cast
        field_simp
      _ ≤ ((a * k : ℕ) : ℝ) * beta := by
        apply mul_le_mul_of_nonneg_right _ hbeta₀
        exact_mod_cast Nat.mul_le_mul_right k hja
  have htail := huniformTail (H.innerStaticConflictUnion F).card hp₀ hmean
  apply H.staticConflictSignedErrorCutoff_le_dominantDelta A F hk hD
    hunif hdeg hpair hFgood hbeta₀ hy hrho₀ orderError horder
  simpa [mul_comm] using htail

/-- A dominant `j`-edge family uses `j` distinct anchors of `A`. -/
lemma card_le_of_mem_goodMatchingMeetingFamilies
    (H : FiniteHypergraph V E) (A : Finset V) (F : Finset E) {j : ℕ}
    (hF : F ∈ H.goodMatchingMeetingFamilies A j) :
    j ≤ A.card := by
  have hdata := (H.mem_goodMatchingMeetingFamilies A j F).1 hF
  have hmeeting := (H.mem_matchingMeetingFamilies A j F).1 hdata.1
  have hanchorCard : (H.familyAnchorSet A F).card = F.card := by
    simpa [familyAnchorSet] using
      H.card_biUnion_support_inter_eq_of_matching_subset_singleMeeting
        A F hmeeting.2.2 hdata.2
  calc
    j = (H.familyAnchorSet A F).card := by rw [hanchorCard, hmeeting.2.1]
    _ ≤ A.card := card_le_card (H.familyAnchorSet_subset A F)

/-- Concrete one-step moment-error estimate after instantiating every
dominant-family error by the common uniform-tail envelope. -/
theorem sum_signedRegularMomentErrorCutoff_le_dominantDelta
    (H : FiniteHypergraph V E) (A : Finset V)
    {a k D C Qcut : ℕ} (hk : 0 < k) (hD : 0 < D)
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (hAa : A.card ≤ a)
    {beta y eta rho tailBudget : ℝ}
    (hbeta₀ : 0 ≤ beta) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpY : (beta / (D : ℝ)) * y ^ (k - 1) ≤ 1)
    (hrho₀ : 0 ≤ rho) (htail₀ : 0 ≤ tailBudget)
    (hcodeg : (C : ℝ) ≤ eta * (D : ℝ))
    (hsufficient : ∀ j ∈ range (A.card + 1), 0 < j →
      (A.card - 1) * C + (j - 1) * (k * C) ≤ D)
    (orderError : ℕ → ℝ)
    (horder : ∀ j, j ≤ A.card → ∀ q, q ≤ Qcut →
      orderError (A.card + j * (k - 1) + q * (k - 1)) ≤ rho)
    (huniformTail : ∀ (N : ℕ) {p : ℝ}, 0 ≤ p →
      (N : ℝ) * p ≤ ((a * k : ℕ) : ℝ) * beta →
      (∑ q ∈ range (N + 1),
        if q ≤ Qcut then 0 else (N.choose q : ℝ) * p ^ q) ≤
          tailBudget) :
    (∑ j ∈ range (A.card + 1),
      H.signedRegularMomentErrorCutoff A k D C
        (beta / (D : ℝ)) y Qcut orderError j) ≤
      (∑ m ∈ range A.card,
        (A.card.choose (m + 1) : ℝ) * beta ^ (m + 1) *
          dominantStaticConflictDelta A.card (m + 1) k C D Qcut
            beta rho tailBudget) +
      ((((A.card : ℝ) - 1) * (C : ℝ)) / (D : ℝ)) *
        ((A.card : ℝ) * beta * (1 + beta) ^ (A.card - 1)) +
      (((k : ℝ) * (C : ℝ)) / (D : ℝ)) *
        ((A.card : ℝ) * ((A.card : ℝ) - 1) * beta ^ 2 *
          (1 + beta) ^ (A.card - 2)) +
      eta * ((A.card : ℝ) ^ 2) * beta *
        ∑ m ∈ range A.card, (((A.card : ℝ) * beta) ^ m) +
      orderError A.card := by
  apply H.sum_signedRegularMomentErrorCutoff_le_normalized A hD hdeg
    hbeta₀ hy hpY hcodeg hsufficient orderError
    (fun j ↦ dominantStaticConflictDelta A.card j k C D Qcut
      beta rho tailBudget)
  · intro j
    exact dominantStaticConflictDelta_nonneg A.card j k C D Qcut hD
      hbeta₀ hrho₀ htail₀
  · intro j hj F hF
    have hjA := H.card_le_of_mem_goodMatchingMeetingFamilies A F hF
    exact H.staticConflictSignedErrorCutoff_le_dominantDelta_of_uniformTail
      A F hk hD hunif hdeg hpair hF (hjA.trans hAa) hbeta₀ hy hrho₀
        orderError (horder j hjA) huniformTail

/-- Degree-free scalar recurrence envelope for one joint-set order. -/
def signedRegularOneStepEnvelope
    (a k Qcut : ℕ)
    (beta rho tailBudget ratio invDegree : ℝ) : ℝ :=
  (∑ m ∈ range a,
    (a.choose (m + 1) : ℝ) * beta ^ (m + 1) *
      dominantStaticConflictDeltaEnvelope a (m + 1) k Qcut
        beta rho tailBudget ratio invDegree) +
  (((a : ℝ) - 1) * ratio) *
    ((a : ℝ) * beta * (1 + beta) ^ (a - 1)) +
  ((k : ℝ) * ratio) *
    ((a : ℝ) * ((a : ℝ) - 1) * beta ^ 2 *
      (1 + beta) ^ (a - 2)) +
  ratio * ((a : ℝ) ^ 2) * beta *
    (∑ m ∈ range a, (((a : ℝ) * beta) ^ m)) + rho

lemma signedRegularOneStepEnvelope_nonneg
    {a : ℕ} (ha : 0 < a) (k Qcut : ℕ)
    {beta rho tailBudget ratio invDegree : ℝ}
    (hbeta₀ : 0 ≤ beta) (hrho₀ : 0 ≤ rho)
    (htail₀ : 0 ≤ tailBudget) (hratio₀ : 0 ≤ ratio)
    (hinv₀ : 0 ≤ invDegree) :
    0 ≤ signedRegularOneStepEnvelope a k Qcut
      beta rho tailBudget ratio invDegree := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hsub₀ : 0 ≤ (a : ℝ) - 1 := sub_nonneg.mpr haR
  have honeBeta₀ : 0 ≤ 1 + beta := by linarith
  have hfamily₀ : 0 ≤
      ∑ m ∈ range a,
        (a.choose (m + 1) : ℝ) * beta ^ (m + 1) *
          dominantStaticConflictDeltaEnvelope a (m + 1) k Qcut
            beta rho tailBudget ratio invDegree := by
    apply sum_nonneg
    intro m _
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hbeta₀ _))
      (dominantStaticConflictDeltaEnvelope_nonneg a (m + 1) k Qcut
        hbeta₀ hrho₀ htail₀ hratio₀ hinv₀)
  unfold signedRegularOneStepEnvelope
  positivity

/-- The concrete exact-regular one-step error is bounded by the degree-free
scalar recurrence envelope. -/
theorem sum_signedRegularMomentErrorCutoff_le_oneStepEnvelope
    (H : FiniteHypergraph V E) (A : Finset V)
    {a k D C Qcut : ℕ} (ha : 0 < A.card) (hk : 0 < k) (hD : 0 < D)
    (hunif : H.IsUniform k)
    (hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (hAa : A.card ≤ a)
    {beta y rho tailBudget ratio invDegree : ℝ}
    (hbeta₀ : 0 ≤ beta) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hpY : (beta / (D : ℝ)) * y ^ (k - 1) ≤ 1)
    (hrho₀ : 0 ≤ rho) (htail₀ : 0 ≤ tailBudget)
    (hratio₀ : 0 ≤ ratio) (hinv₀ : 0 ≤ invDegree)
    (hratio : (C : ℝ) / (D : ℝ) ≤ ratio)
    (hinv : 1 / (D : ℝ) ≤ invDegree)
    (hsufficient : ∀ j ∈ range (A.card + 1), 0 < j →
      (A.card - 1) * C + (j - 1) * (k * C) ≤ D)
    (orderError : ℕ → ℝ)
    (horder : ∀ j, j ≤ A.card → ∀ q, q ≤ Qcut →
      orderError (A.card + j * (k - 1) + q * (k - 1)) ≤ rho)
    (huniformTail : ∀ (N : ℕ) {p : ℝ}, 0 ≤ p →
      (N : ℝ) * p ≤ ((a * k : ℕ) : ℝ) * beta →
      (∑ q ∈ range (N + 1),
        if q ≤ Qcut then 0 else (N.choose q : ℝ) * p ^ q) ≤
          tailBudget) :
    (∑ j ∈ range (A.card + 1),
      H.signedRegularMomentErrorCutoff A k D C
        (beta / (D : ℝ)) y Qcut orderError j) ≤
      signedRegularOneStepEnvelope A.card k Qcut
        beta rho tailBudget ratio invDegree := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hcodeg : (C : ℝ) ≤ ratio * (D : ℝ) :=
    (div_le_iff₀ hDreal).1 hratio
  have hraw := H.sum_signedRegularMomentErrorCutoff_le_dominantDelta
    A hk hD hunif hdeg hpair hAa hbeta₀ hy hpY hrho₀ htail₀ hcodeg
      hsufficient orderError horder huniformTail
  have hfamily :
      (∑ m ∈ range A.card,
        (A.card.choose (m + 1) : ℝ) * beta ^ (m + 1) *
          dominantStaticConflictDelta A.card (m + 1) k C D Qcut
            beta rho tailBudget) ≤
      ∑ m ∈ range A.card,
        (A.card.choose (m + 1) : ℝ) * beta ^ (m + 1) *
          dominantStaticConflictDeltaEnvelope A.card (m + 1) k Qcut
            beta rho tailBudget ratio invDegree := by
    apply sum_le_sum
    intro m _
    apply mul_le_mul_of_nonneg_left
    · exact dominantStaticConflictDelta_le_envelope A.card (m + 1) k C D
        Qcut hD hbeta₀ hrho₀ htail₀ hratio₀ hinv₀ hratio hinv
    · exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hbeta₀ _)
  have haR : (1 : ℝ) ≤ A.card := by exact_mod_cast ha
  have hcountOne :
      ((((A.card : ℝ) - 1) * (C : ℝ)) / (D : ℝ)) ≤
        ((A.card : ℝ) - 1) * ratio := by
    calc
      ((((A.card : ℝ) - 1) * (C : ℝ)) / (D : ℝ)) =
          ((A.card : ℝ) - 1) * ((C : ℝ) / (D : ℝ)) := by ring
      _ ≤ ((A.card : ℝ) - 1) * ratio :=
        mul_le_mul_of_nonneg_left hratio (sub_nonneg.mpr haR)
  have hcountTwo :
      (((k : ℝ) * (C : ℝ)) / (D : ℝ)) ≤ (k : ℝ) * ratio := by
    calc
      (((k : ℝ) * (C : ℝ)) / (D : ℝ)) =
          (k : ℝ) * ((C : ℝ) / (D : ℝ)) := by ring
      _ ≤ (k : ℝ) * ratio :=
        mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg k)
  calc
    (∑ j ∈ range (A.card + 1),
      H.signedRegularMomentErrorCutoff A k D C
        (beta / (D : ℝ)) y Qcut orderError j) ≤ _ := hraw
    _ ≤ signedRegularOneStepEnvelope A.card k Qcut
        beta rho tailBudget ratio invDegree := by
      unfold signedRegularOneStepEnvelope
      gcongr
      simpa using horder 0 (Nat.zero_le _) 0 (Nat.zero_le _)

@[simp] lemma dominantStaticConflictDeltaEnvelope_zero
    (a j k Qcut : ℕ) (beta : ℝ) :
    dominantStaticConflictDeltaEnvelope a j k Qcut beta 0 0 0 0 = 0 := by
  simp [dominantStaticConflictDeltaEnvelope]

@[simp] lemma signedRegularOneStepEnvelope_zero
    (a k Qcut : ℕ) (beta : ℝ) :
    signedRegularOneStepEnvelope a k Qcut beta 0 0 0 0 = 0 := by
  simp [signedRegularOneStepEnvelope]

/-- Sum of all positive joint orders up to `cap`; this supplies one common
error bound for every order needed at a round. -/
def signedRegularRoundEnvelope
    (cap k Qcut : ℕ) (beta rho small : ℝ) : ℝ :=
  ∑ m ∈ range cap,
    signedRegularOneStepEnvelope (m + 1) k Qcut
      beta rho small small small

/-- The full round envelope, with the tail budget separated from the
codegree/inverse-degree bounds.  Summing over every positive order below
`cap` gives one scalar bound which is simultaneously valid for all joint
sets occurring in that round. -/
def signedRegularRoundEnvelopeFull
    (cap k Qcut : ℕ)
    (beta rho tailBudget ratio invDegree : ℝ) : ℝ :=
  ∑ m ∈ range cap,
    signedRegularOneStepEnvelope (m + 1) k Qcut
      beta rho tailBudget ratio invDegree

@[simp] lemma signedRegularRoundEnvelopeFull_zero
    (cap k Qcut : ℕ) (beta : ℝ) :
    signedRegularRoundEnvelopeFull cap k Qcut beta 0 0 0 0 = 0 := by
  simp [signedRegularRoundEnvelopeFull]

/-- Iteration of the finite scalar envelopes.  All structural quantities
are charged to the single small parameter `small`. -/
def signedRegularErrorTrajectory
    (orderCap conflictCutoff : ℕ → ℕ) (k : ℕ) (beta small : ℝ) : ℕ → ℝ
  | 0 => 0
  | r + 1 => signedRegularRoundEnvelope (orderCap (r + 1)) k
      (conflictCutoff r) beta
      (signedRegularErrorTrajectory orderCap conflictCutoff k beta small r)
      small

@[simp] lemma signedRegularErrorTrajectory_zero_small
    (orderCap conflictCutoff : ℕ → ℕ) (k : ℕ) (beta : ℝ) (r : ℕ) :
    signedRegularErrorTrajectory orderCap conflictCutoff k beta 0 r = 0 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp [signedRegularErrorTrajectory, signedRegularRoundEnvelope, ih]

lemma signedRegularRoundEnvelope_nonneg
    (cap k Qcut : ℕ) {beta rho small : ℝ}
    (hbeta₀ : 0 ≤ beta) (hrho₀ : 0 ≤ rho) (hsmall₀ : 0 ≤ small) :
    0 ≤ signedRegularRoundEnvelope cap k Qcut beta rho small := by
  unfold signedRegularRoundEnvelope
  apply sum_nonneg
  intro m _
  exact signedRegularOneStepEnvelope_nonneg (by omega) k Qcut
    hbeta₀ hrho₀ hsmall₀ hsmall₀ hsmall₀

lemma signedRegularErrorTrajectory_nonneg
    (orderCap conflictCutoff : ℕ → ℕ) (k : ℕ)
    {beta small : ℝ} (hbeta₀ : 0 ≤ beta) (hsmall₀ : 0 ≤ small) (r : ℕ) :
    0 ≤ signedRegularErrorTrajectory
      orderCap conflictCutoff k beta small r := by
  induction r with
  | zero => simp [signedRegularErrorTrajectory]
  | succ r ih =>
      exact signedRegularRoundEnvelope_nonneg _ _ _ hbeta₀ ih hsmall₀

lemma continuous_signedRegularOneStepEnvelope_comp
    (a k Qcut : ℕ) (beta : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun small ↦ signedRegularOneStepEnvelope a k Qcut
      beta (f small) small small small) := by
  unfold signedRegularOneStepEnvelope dominantStaticConflictDeltaEnvelope
  fun_prop

/-- For fixed finite schedules, the accumulated error is continuous in the
single structural small parameter. -/
lemma continuous_signedRegularErrorTrajectory
    (orderCap conflictCutoff : ℕ → ℕ) (k : ℕ) (beta : ℝ) (r : ℕ) :
    Continuous (fun small ↦ signedRegularErrorTrajectory
      orderCap conflictCutoff k beta small r) := by
  induction r with
  | zero => exact continuous_const
  | succ r ih =>
      simp only [signedRegularErrorTrajectory, signedRegularRoundEnvelope]
      apply continuous_finset_sum
      intro m _
      exact continuous_signedRegularOneStepEnvelope_comp
        (m + 1) k (conflictCutoff r) beta ih

/-- Every fixed finite cap/cutoff schedule has arbitrarily small accumulated
error once the tail, codegree ratio, and inverse degree are simultaneously
small. -/
theorem exists_small_signedRegularErrorTrajectory
    (orderCap conflictCutoff : ℕ → ℕ) (k L : ℕ) (beta : ℝ)
    {target : ℝ} (htarget : 0 < target) :
    ∃ small : ℝ, 0 < small ∧
      signedRegularErrorTrajectory
        orderCap conflictCutoff k beta small L < target := by
  have hcont : ContinuousAt
      (fun small ↦ signedRegularErrorTrajectory
        orderCap conflictCutoff k beta small L) 0 :=
    (continuous_signedRegularErrorTrajectory
      orderCap conflictCutoff k beta L).continuousAt
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨delta, hdelta₀, hdelta⟩ := hcont target htarget
  refine ⟨delta / 2, half_pos hdelta₀, ?_⟩
  have hdist : dist (delta / 2) (0 : ℝ) < delta := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hdelta₀)]
    linarith
  have hclose := hdelta hdist
  rw [signedRegularErrorTrajectory_zero_small, Real.dist_eq, sub_zero] at hclose
  exact (le_abs_self _).trans_lt hclose

lemma signedRegularOneStepEnvelope_le_roundEnvelope
    {a cap k Qcut : ℕ} (ha : 0 < a) (hacap : a ≤ cap)
    {beta rho small : ℝ}
    (hbeta₀ : 0 ≤ beta) (hrho₀ : 0 ≤ rho) (hsmall₀ : 0 ≤ small) :
    signedRegularOneStepEnvelope a k Qcut beta rho small small small ≤
      signedRegularRoundEnvelope cap k Qcut beta rho small := by
  let f : ℕ → ℝ := fun m ↦
    signedRegularOneStepEnvelope (m + 1) k Qcut
      beta rho small small small
  have hmem : a - 1 ∈ range cap := by
    rw [mem_range]
    omega
  have hnonneg : ∀ m ∈ range cap, 0 ≤ f m := by
    intro m _
    exact signedRegularOneStepEnvelope_nonneg (by omega) k Qcut
      hbeta₀ hrho₀ hsmall₀ hsmall₀ hsmall₀
  have hsingle := Finset.single_le_sum hnonneg hmem
  simpa [signedRegularRoundEnvelope, f, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2
    (Nat.ne_of_gt ha))] using hsingle

lemma le_signedRegularRoundEnvelope
    {cap k Qcut : ℕ} (hcap : 0 < cap)
    {beta rho small : ℝ}
    (hbeta₀ : 0 ≤ beta) (hrho₀ : 0 ≤ rho) (hsmall₀ : 0 ≤ small) :
    rho ≤ signedRegularRoundEnvelope cap k Qcut beta rho small := by
  have hone := signedRegularOneStepEnvelope_le_roundEnvelope
    (a := 1) (cap := cap) (k := k) (Qcut := Qcut)
      (by omega) hcap hbeta₀ hrho₀ hsmall₀
  have hrest : rho ≤
      signedRegularOneStepEnvelope 1 k Qcut beta rho small small small := by
    have hdelta₀ : 0 ≤
        dominantStaticConflictDeltaEnvelope 1 1 k Qcut
          beta rho small small small :=
      dominantStaticConflictDeltaEnvelope_nonneg 1 1 k Qcut
        hbeta₀ hrho₀ hsmall₀ hsmall₀ hsmall₀
    have hbetaDelta₀ : 0 ≤ beta *
        dominantStaticConflictDeltaEnvelope 1 1 k Qcut
          beta rho small small small := mul_nonneg hbeta₀ hdelta₀
    have hsmallBeta₀ : 0 ≤ small * beta := mul_nonneg hsmall₀ hbeta₀
    simp [signedRegularOneStepEnvelope]
    nlinarith
  exact hrest.trans hone

lemma exists_pos_of_continuousAt_lt
    {f : ℝ → ℝ} {target : ℝ} (hf : ContinuousAt f 0)
    (hlt : f 0 < target) :
    ∃ x : ℝ, 0 < x ∧ f x < target := by
  have hepsilon : 0 < target - f 0 := sub_pos.mpr hlt
  rw [Metric.continuousAt_iff] at hf
  obtain ⟨delta, hdelta₀, hdelta⟩ := hf (target - f 0) hepsilon
  refine ⟨delta / 2, half_pos hdelta₀, ?_⟩
  have hdist : dist (delta / 2) (0 : ℝ) < delta := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hdelta₀)]
    linarith
  have hclose := hdelta hdist
  rw [Real.dist_eq] at hclose
  have hdiff : f (delta / 2) - f 0 ≤ |f (delta / 2) - f 0| :=
    le_abs_self _
  linarith

lemma exists_pos_lt_of_continuousAt_lt
    {f : ℝ → ℝ} {target bound : ℝ} (hf : ContinuousAt f 0)
    (hlt : f 0 < target) (hbound : 0 < bound) :
    ∃ x : ℝ, 0 < x ∧ x < bound ∧ f x < target := by
  have hepsilon : 0 < target - f 0 := sub_pos.mpr hlt
  rw [Metric.continuousAt_iff] at hf
  obtain ⟨delta, hdelta₀, hdelta⟩ := hf (target - f 0) hepsilon
  let x : ℝ := min delta bound / 2
  have hmin₀ : 0 < min delta bound := lt_min hdelta₀ hbound
  have hx₀ : 0 < x := half_pos hmin₀
  have hxdelta : x < delta := by
    dsimp only [x]
    calc
      min delta bound / 2 < min delta bound := half_lt_self hmin₀
      _ ≤ delta := min_le_left _ _
  have hxbound : x < bound := by
    dsimp only [x]
    calc
      min delta bound / 2 < min delta bound := half_lt_self hmin₀
      _ ≤ bound := min_le_right _ _
  refine ⟨x, hx₀, hxbound, ?_⟩
  have hdist : dist x (0 : ℝ) < delta := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hx₀]
    exact hxdelta
  have hclose := hdelta hdist
  rw [Real.dist_eq] at hclose
  have hdiff : f x - f 0 ≤ |f x - f 0| := le_abs_self _
  linarith

lemma continuous_signedRegularOneStepEnvelope_tail
    (a k Qcut : ℕ) (beta : ℝ) :
    Continuous (fun tail ↦ signedRegularOneStepEnvelope a k Qcut
      beta 0 tail 0 0) := by
  unfold signedRegularOneStepEnvelope dominantStaticConflictDeltaEnvelope
  fun_prop

lemma continuous_signedRegularOneStepEnvelope_diagonal
    (a k Qcut : ℕ) (beta tail : ℝ) :
    Continuous (fun small ↦ signedRegularOneStepEnvelope a k Qcut
      beta small tail small small) := by
  unfold signedRegularOneStepEnvelope dominantStaticConflictDeltaEnvelope
  fun_prop

lemma signedRegularOneStepEnvelope_tail_independent_cutoff
    (a k Qcut : ℕ) (beta tail : ℝ) :
    signedRegularOneStepEnvelope a k Qcut beta 0 tail 0 0 =
      signedRegularOneStepEnvelope a k 0 beta 0 tail 0 0 := by
  simp [signedRegularOneStepEnvelope,
    dominantStaticConflictDeltaEnvelope]

lemma signedRegularRoundEnvelopeFull_nonneg
    (cap k Qcut : ℕ)
    {beta rho tailBudget ratio invDegree : ℝ}
    (hbeta₀ : 0 ≤ beta) (hrho₀ : 0 ≤ rho)
    (htail₀ : 0 ≤ tailBudget) (hratio₀ : 0 ≤ ratio)
    (hinv₀ : 0 ≤ invDegree) :
    0 ≤ signedRegularRoundEnvelopeFull cap k Qcut
      beta rho tailBudget ratio invDegree := by
  unfold signedRegularRoundEnvelopeFull
  apply sum_nonneg
  intro m _
  exact signedRegularOneStepEnvelope_nonneg (by omega) k Qcut
    hbeta₀ hrho₀ htail₀ hratio₀ hinv₀

lemma signedRegularOneStepEnvelope_le_roundEnvelopeFull
    {a cap k Qcut : ℕ} (ha : 0 < a) (hacap : a ≤ cap)
    {beta rho tailBudget ratio invDegree : ℝ}
    (hbeta₀ : 0 ≤ beta) (hrho₀ : 0 ≤ rho)
    (htail₀ : 0 ≤ tailBudget) (hratio₀ : 0 ≤ ratio)
    (hinv₀ : 0 ≤ invDegree) :
    signedRegularOneStepEnvelope a k Qcut
        beta rho tailBudget ratio invDegree ≤
      signedRegularRoundEnvelopeFull cap k Qcut
        beta rho tailBudget ratio invDegree := by
  let f : ℕ → ℝ := fun m ↦
    signedRegularOneStepEnvelope (m + 1) k Qcut
      beta rho tailBudget ratio invDegree
  have hmem : a - 1 ∈ range cap := by
    rw [mem_range]
    omega
  have hnonneg : ∀ m ∈ range cap, 0 ≤ f m := by
    intro m _
    exact signedRegularOneStepEnvelope_nonneg (by omega) k Qcut
      hbeta₀ hrho₀ htail₀ hratio₀ hinv₀
  have hsingle := Finset.single_le_sum hnonneg hmem
  simpa [signedRegularRoundEnvelopeFull, f,
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt ha))]
      using hsingle

lemma le_signedRegularRoundEnvelopeFull
    {cap k Qcut : ℕ} (hcap : 0 < cap)
    {beta rho tailBudget ratio invDegree : ℝ}
    (hbeta₀ : 0 ≤ beta) (hrho₀ : 0 ≤ rho)
    (htail₀ : 0 ≤ tailBudget) (hratio₀ : 0 ≤ ratio)
    (hinv₀ : 0 ≤ invDegree) :
    rho ≤ signedRegularRoundEnvelopeFull cap k Qcut
      beta rho tailBudget ratio invDegree := by
  have hone := signedRegularOneStepEnvelope_le_roundEnvelopeFull
    (a := 1) (cap := cap) (k := k) (Qcut := Qcut)
      (by omega) hcap hbeta₀ hrho₀ htail₀ hratio₀ hinv₀
  have hrest : rho ≤
      signedRegularOneStepEnvelope 1 k Qcut
        beta rho tailBudget ratio invDegree := by
    have hdelta₀ : 0 ≤
        dominantStaticConflictDeltaEnvelope 1 1 k Qcut
          beta rho tailBudget ratio invDegree :=
      dominantStaticConflictDeltaEnvelope_nonneg 1 1 k Qcut
        hbeta₀ hrho₀ htail₀ hratio₀ hinv₀
    have hbetaDelta₀ : 0 ≤ beta *
        dominantStaticConflictDeltaEnvelope 1 1 k Qcut
          beta rho tailBudget ratio invDegree := mul_nonneg hbeta₀ hdelta₀
    have hratioBeta₀ : 0 ≤ ratio * beta := mul_nonneg hratio₀ hbeta₀
    simp [signedRegularOneStepEnvelope]
    nlinarith
  exact hrest.trans hone

lemma continuous_signedRegularRoundEnvelopeFull_tail
    (cap k Qcut : ℕ) (beta : ℝ) :
    Continuous (fun tail ↦ signedRegularRoundEnvelopeFull cap k Qcut
      beta 0 tail 0 0) := by
  unfold signedRegularRoundEnvelopeFull
  apply continuous_finset_sum
  intro m _
  exact continuous_signedRegularOneStepEnvelope_tail (m + 1) k Qcut beta

lemma continuous_signedRegularRoundEnvelopeFull_diagonal
    (cap k Qcut : ℕ) (beta tail : ℝ) :
    Continuous (fun small ↦ signedRegularRoundEnvelopeFull cap k Qcut
      beta small tail small small) := by
  unfold signedRegularRoundEnvelopeFull
  apply continuous_finset_sum
  intro m _
  exact continuous_signedRegularOneStepEnvelope_diagonal
    (m + 1) k Qcut beta tail

lemma signedRegularRoundEnvelopeFull_tail_independent_cutoff
    (cap k Qcut : ℕ) (beta tail : ℝ) :
    signedRegularRoundEnvelopeFull cap k Qcut beta 0 tail 0 0 =
      signedRegularRoundEnvelopeFull cap k 0 beta 0 tail 0 0 := by
  unfold signedRegularRoundEnvelopeFull
  apply sum_congr rfl
  intro m _
  exact signedRegularOneStepEnvelope_tail_independent_cutoff
    (m + 1) k Qcut beta tail

/-- Backward scalar construction for one round.  First choose a tiny tail
budget (its coefficient is cutoff-independent), then choose a cutoff, and
only afterwards choose the incoming/structural tolerance.  This ordering
avoids the circular global-cutoff problem. -/
theorem exists_signedRegularOneStepChoice
    (a k : ℕ) {beta target : ℝ}
    (hbeta₀ : 0 ≤ beta) (htarget : 0 < target) :
    ∃ Qcut : ℕ, ∃ tailBudget inputTolerance : ℝ,
      0 < tailBudget ∧ 0 < inputTolerance ∧ inputTolerance < target ∧
      (∀ (N : ℕ) {p : ℝ}, 0 ≤ p →
        (N : ℝ) * p ≤ ((a * k : ℕ) : ℝ) * beta →
        (∑ q ∈ range (N + 1),
          if q ≤ Qcut then 0 else (N.choose q : ℝ) * p ^ q) ≤
            tailBudget) ∧
      signedRegularRoundEnvelopeFull a k Qcut beta inputTolerance
          tailBudget inputTolerance inputTolerance < target := by
  let g : ℝ → ℝ := fun tail ↦
    signedRegularRoundEnvelopeFull a k 0 beta 0 tail 0 0
  have hg : ContinuousAt g 0 :=
    (continuous_signedRegularRoundEnvelopeFull_tail a k 0 beta).continuousAt
  have hg0 : g 0 = 0 := by
    simp [g]
  obtain ⟨tailBudget, htailPos, htailSmall⟩ :=
    exists_pos_of_continuousAt_lt hg (by simpa [hg0] using htarget)
  have hmu₀ : 0 ≤ ((a * k : ℕ) : ℝ) * beta :=
    mul_nonneg (Nat.cast_nonneg _) hbeta₀
  obtain ⟨Qcut, hQcut⟩ :=
    exists_uniform_binomial_upper_tail_cutoff hmu₀ htailPos
  let f : ℝ → ℝ := fun small ↦
    signedRegularRoundEnvelopeFull a k Qcut beta small
      tailBudget small small
  have hf : ContinuousAt f 0 :=
    (continuous_signedRegularRoundEnvelopeFull_diagonal
      a k Qcut beta tailBudget).continuousAt
  have hf0 : f 0 < target := by
    dsimp only [f]
    rw [signedRegularRoundEnvelopeFull_tail_independent_cutoff]
    exact htailSmall
  obtain ⟨inputTolerance, hinputPos, hinputTarget, hinputSmall⟩ :=
    exists_pos_lt_of_continuousAt_lt hf hf0 htarget
  refine ⟨Qcut, tailBudget, inputTolerance, htailPos, hinputPos,
    hinputTarget, ?_, ?_⟩
  · intro N p hp₀ hmean
    exact (hQcut N hp₀ hmean).le
  · exact hinputSmall

/-- Finite backward data for the signed exact-regular moment induction.
The order cap grows backwards, while the permitted error grows forwards.
The single `structuralBound` is small enough for every round's codegree
ratio and inverse-degree charge. -/
structure SignedRegularScalarSchedule
    (k L : ℕ) (beta target : ℝ) where
  orderCap : ℕ → ℕ
  conflictCutoff : ℕ → ℕ
  profileTolerance : ℕ → ℝ
  tailBudget : ℕ → ℝ
  structuralBound : ℝ
  terminal_cap : orderCap L = k
  cap_pos : ∀ r, r ≤ L → 0 < orderCap r
  k_le_cap : ∀ r, r ≤ L → k ≤ orderCap r
  tolerance_nonneg : ∀ r, 0 ≤ profileTolerance r
  tolerance_pos : ∀ r, r ≤ L → 0 < profileTolerance r
  tolerance_lt : ∀ r, r ≤ L → profileTolerance r < target
  structural_pos : 0 < structuralBound
  structural_le : ∀ r, r ≤ L → structuralBound ≤ profileTolerance r
  cap_step : ∀ r, r < L →
    orderCap (r + 1) + orderCap (r + 1) * (k - 1) +
        conflictCutoff r * (k - 1) ≤ orderCap r
  tail_pos : ∀ r, r < L → 0 < tailBudget r
  uniform_tail : ∀ r, r < L → ∀ (N : ℕ) {p : ℝ}, 0 ≤ p →
    (N : ℝ) * p ≤ (((orderCap (r + 1) * k : ℕ) : ℝ) * beta) →
    (∑ q ∈ range (N + 1),
      if q ≤ conflictCutoff r then 0 else (N.choose q : ℝ) * p ^ q) ≤
        tailBudget r
  step_envelope : ∀ r, r < L →
    signedRegularRoundEnvelopeFull (orderCap (r + 1)) k
      (conflictCutoff r) beta (profileTolerance r) (tailBudget r)
      (profileTolerance r) (profileTolerance r) < profileTolerance (r + 1)

/-- Every finite horizon admits a backward order/cutoff/error schedule. -/
theorem exists_signedRegularScalarSchedule
    (k L : ℕ) {beta target : ℝ}
    (hk : 0 < k) (hbeta₀ : 0 ≤ beta) (htarget : 0 < target) :
    Nonempty (SignedRegularScalarSchedule k L beta target) := by
  induction L with
  | zero =>
      let tolerance : ℝ := target / 2
      have htolerance₀ : 0 < tolerance := half_pos htarget
      have htoleranceTarget : tolerance < target := half_lt_self htarget
      exact ⟨{
        orderCap := fun _ ↦ k
        conflictCutoff := fun _ ↦ 0
        profileTolerance := fun _ ↦ tolerance
        tailBudget := fun _ ↦ tolerance
        structuralBound := tolerance
        terminal_cap := rfl
        cap_pos := by intro _ _; exact hk
        k_le_cap := by intro _ _; exact le_rfl
        tolerance_nonneg := by intro _; exact htolerance₀.le
        tolerance_pos := by intro _ _; exact htolerance₀
        tolerance_lt := by intro _ _; exact htoleranceTarget
        structural_pos := htolerance₀
        structural_le := by intro _ _; exact le_rfl
        cap_step := by omega
        tail_pos := by omega
        uniform_tail := by omega
        step_envelope := by omega }⟩
  | succ L ih =>
      obtain ⟨S⟩ := ih
      have hS0 : 0 < S.profileTolerance 0 := S.tolerance_pos 0 (by omega)
      obtain ⟨Qcut, tail, input, htail₀, hinput₀, hinputLt,
          huniform, hstep⟩ :=
        exists_signedRegularOneStepChoice (S.orderCap 0) k hbeta₀ hS0
      let cap : ℕ → ℕ
        | 0 => S.orderCap 0 + S.orderCap 0 * (k - 1) + Qcut * (k - 1)
        | r + 1 => S.orderCap r
      let cutoff : ℕ → ℕ
        | 0 => Qcut
        | r + 1 => S.conflictCutoff r
      let tolerance : ℕ → ℝ
        | 0 => input
        | r + 1 => S.profileTolerance r
      let tails : ℕ → ℝ
        | 0 => tail
        | r + 1 => S.tailBudget r
      let structural : ℝ := min input S.structuralBound
      have hstructural₀ : 0 < structural :=
        lt_min hinput₀ S.structural_pos
      exact ⟨{
        orderCap := cap
        conflictCutoff := cutoff
        profileTolerance := tolerance
        tailBudget := tails
        structuralBound := structural
        terminal_cap := by simp [cap, S.terminal_cap]
        cap_pos := by
          intro r hr
          cases r with
          | zero =>
              have hcap0 := S.cap_pos 0 (by omega)
              simp only [cap]
              omega
          | succ r =>
              simpa only [cap] using S.cap_pos r (by omega)
        k_le_cap := by
          intro r hr
          cases r with
          | zero =>
              have hcap0 := S.k_le_cap 0 (by omega)
              simp only [cap]
              omega
          | succ r =>
              simpa only [cap] using S.k_le_cap r (by omega)
        tolerance_nonneg := by
          intro r
          cases r with
          | zero => exact hinput₀.le
          | succ r => simpa only [tolerance] using S.tolerance_nonneg r
        tolerance_pos := by
          intro r hr
          cases r with
          | zero => simpa only [tolerance] using hinput₀
          | succ r =>
              simpa only [tolerance] using S.tolerance_pos r (by omega)
        tolerance_lt := by
          intro r hr
          cases r with
          | zero =>
              exact hinputLt.trans (S.tolerance_lt 0 (by omega))
          | succ r =>
              simpa only [tolerance] using S.tolerance_lt r (by omega)
        structural_pos := hstructural₀
        structural_le := by
          intro r hr
          cases r with
          | zero => exact min_le_left _ _
          | succ r =>
              exact (min_le_right _ _).trans (S.structural_le r (by omega))
        cap_step := by
          intro r hr
          cases r with
          | zero => simp [cap, cutoff]
          | succ r =>
              simpa only [cap, cutoff, Nat.succ_eq_add_one] using
                S.cap_step r (by omega)
        tail_pos := by
          intro r hr
          cases r with
          | zero => simpa only [tails] using htail₀
          | succ r =>
              simpa only [tails] using S.tail_pos r (by omega)
        uniform_tail := by
          intro r hr
          cases r with
          | zero =>
              intro N p hp hmean
              simpa only [cap, cutoff, tails] using huniform N hp hmean
          | succ r =>
              intro N p hp hmean
              simpa only [cap, cutoff, tails, Nat.succ_eq_add_one] using
                S.uniform_tail r (by omega) N hp hmean
        step_envelope := by
          intro r hr
          cases r with
          | zero => simpa only [cap, cutoff, tolerance, tails] using hstep
          | succ r =>
              simpa only [cap, cutoff, tolerance, tails,
                Nat.succ_eq_add_one] using S.step_envelope r (by omega) }⟩

/-- A scalar schedule discharges the concrete all-order moment step once
the codegree ratio, inverse degree, and elementary natural-number choice
margin are below its structural allowance. -/
theorem SignedRegularScalarSchedule.moment_step
    {k L : ℕ} {beta target : ℝ}
    (S : SignedRegularScalarSchedule k L beta target)
    (H : FiniteHypergraph V E) {D C : ℕ}
    (hk : 0 < k) (hD : 0 < D)
    (hunif : H.IsUniform k)
    (hreg : ∀ v ∈ H.vertexSet, H.edgeDegree v = D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    (hbeta₀ : 0 ≤ beta) (hbeta₁ : beta ≤ 1)
    (hp₁ : beta / (D : ℝ) ≤ 1)
    (hcodeg : (C : ℝ) / (D : ℝ) ≤ S.structuralBound)
    (hinv : 1 / (D : ℝ) ≤ S.structuralBound)
    (hsufficient : ∀ r, r < L →
      (S.orderCap (r + 1) - 1) * C +
          (S.orderCap (r + 1) - 1) * (k * C) ≤ D) :
    ∀ r, r < L → ∀ A : Finset V,
      A ⊆ H.vertexSet → A.card ≤ S.orderCap (r + 1) →
      (∑ j ∈ range (A.card + 1),
        H.signedRegularMomentErrorCutoff A k D C (beta / (D : ℝ))
          (signedRegularSurvival k D (beta / (D : ℝ)) r)
          (S.conflictCutoff r) (fun _ ↦ S.profileTolerance r) j) ≤
        S.profileTolerance (r + 1) := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hp₀ : 0 ≤ beta / (D : ℝ) := div_nonneg hbeta₀ hDreal.le
  have hpD : beta / (D : ℝ) * (D : ℝ) ≤ 1 := by
    rw [div_mul_cancel₀ beta hDreal.ne']
    exact hbeta₁
  have hdeg : ∀ v ∈ H.vertexSet, H.edgeDegree v ≤ D := by
    intro v hv
    exact (hreg v hv).le
  intro r hr A hA hAcap
  have htol₀ : 0 ≤ S.profileTolerance r :=
    (S.tolerance_pos r (by omega)).le
  have htail₀ : 0 ≤ S.tailBudget r := (S.tail_pos r hr).le
  have hratio : (C : ℝ) / (D : ℝ) ≤ S.profileTolerance r :=
    hcodeg.trans (S.structural_le r (by omega))
  have hinv' : 1 / (D : ℝ) ≤ S.profileTolerance r :=
    hinv.trans (S.structural_le r (by omega))
  have hy : signedRegularSurvival k D (beta / (D : ℝ)) r ∈
      Set.Icc (0 : ℝ) 1 :=
    signedRegularSurvival_mem_Icc k D hp₀ hp₁ hpD r
  have hpY : beta / (D : ℝ) *
      signedRegularSurvival k D (beta / (D : ℝ)) r ^ (k - 1) ≤ 1 :=
    mul_signedRegularSurvival_pow_le_one k D hp₀ hp₁ hpD r
  by_cases ha : A.card = 0
  · have hAempty : A = ∅ := card_eq_zero.mp ha
    subst A
    have hbase : S.profileTolerance r ≤
        signedRegularRoundEnvelopeFull (S.orderCap (r + 1)) k
          (S.conflictCutoff r) beta (S.profileTolerance r)
          (S.tailBudget r) (S.profileTolerance r)
          (S.profileTolerance r) :=
      le_signedRegularRoundEnvelopeFull
        (S.cap_pos (r + 1) (by omega)) hbeta₀ htol₀ htail₀ htol₀ htol₀
    have hlt := S.step_envelope r hr
    simpa [signedRegularMomentErrorCutoff] using hbase.trans hlt.le
  · have haPos : 0 < A.card := Nat.pos_of_ne_zero ha
    have hsuffA : ∀ j ∈ range (A.card + 1), 0 < j →
        (A.card - 1) * C + (j - 1) * (k * C) ≤ D := by
      intro j hj hjPos
      have hjle : j ≤ A.card := by simpa [mem_range] using hj
      calc
        (A.card - 1) * C + (j - 1) * (k * C) ≤
            (S.orderCap (r + 1) - 1) * C +
              (S.orderCap (r + 1) - 1) * (k * C) := by
                gcongr <;> omega
        _ ≤ D := hsufficient r hr
    have hone := H.sum_signedRegularMomentErrorCutoff_le_oneStepEnvelope
      A haPos hk hD hunif hdeg hpair hAcap hbeta₀ hy hpY htol₀
        htail₀ htol₀ htol₀ hratio hinv' hsuffA
        (fun _ ↦ S.profileTolerance r) (by intros; exact le_rfl)
        (S.uniform_tail r hr)
    have hround := signedRegularOneStepEnvelope_le_roundEnvelopeFull
      (a := A.card) (cap := S.orderCap (r + 1)) (k := k)
      (Qcut := S.conflictCutoff r)
      haPos hAcap hbeta₀ htol₀ htail₀ htol₀ htol₀
    exact hone.trans (hround.trans (S.step_envelope r hr).le)

/-- End-to-end use of a scalar schedule in the conditional marginal
theorem.  All hypergraph-dependent moment obligations are discharged by
`SignedRegularScalarSchedule.moment_step`. -/
theorem innerAcceptanceMass_twoSided_of_signedRegularScalarSchedule
    (H : FiniteHypergraph V E)
    {k L : ℕ} {beta target : ℝ}
    (S : SignedRegularScalarSchedule k L beta target)
    {D C : ℕ} (hk : 0 < k) (hD : 0 < D)
    (hunif : H.IsUniform k)
    (hreg : ∀ v ∈ H.vertexSet, H.edgeDegree v = D)
    (hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C)
    {zeta : ℝ}
    (hbeta₀ : 0 ≤ beta) (hbeta₁ : beta ≤ 1)
    (hp₁ : beta / (D : ℝ) ≤ 1)
    (hzeta₀ : 0 ≤ zeta) (hzeta₁ : zeta ≤ 1)
    (hcollision : (k : ℝ) * beta ≤ zeta / 4)
    (htail : signedRegularSurvival k D (beta / (D : ℝ)) L ≤ zeta / 4)
    (herror : beta * (L : ℝ) * target ≤ zeta / 4)
    (hcodeg : (C : ℝ) / (D : ℝ) ≤ S.structuralBound)
    (hinv : 1 / (D : ℝ) ≤ S.structuralBound)
    (hsufficient : ∀ r, r < L →
      (S.orderCap (r + 1) - 1) * C +
          (S.orderCap (r + 1) - 1) * (k * C) ≤ D) :
    ∀ e : E,
      (1 - zeta) / (D : ℝ) ≤
          H.innerAcceptanceMass L (fun _ ↦ beta / (D : ℝ)) e ∧
        H.innerAcceptanceMass L (fun _ ↦ beta / (D : ℝ)) e ≤
          (1 + zeta) / (D : ℝ) := by
  have htarget₀ : 0 ≤ target := by
    have htol₀ := S.tolerance_pos 0 (by omega)
    have htolTarget := S.tolerance_lt 0 (by omega)
    linarith
  apply H.innerAcceptanceMass_twoSided_of_signedRegular_cutoff_induction
    hk hD hunif hreg hpair hbeta₀ hbeta₁ hp₁ htarget₀ hzeta₀ hzeta₁
      hcollision htail herror S.orderCap S.conflictCutoff
      (fun r _ ↦ S.profileTolerance r) S.cap_step
  · intro r _
    exact S.tolerance_nonneg r
  · exact S.moment_step H hk hD hunif hreg hpair hbeta₀ hbeta₁ hp₁
      hcodeg hinv hsufficient
  · intro r hr
    exact S.k_le_cap r (Nat.le_of_lt hr)
  · intro r hr
    exact (S.tolerance_lt r (Nat.le_of_lt hr)).le

/-- A fixed scalar schedule supplies uniform codegree and degree thresholds
for the exact-regular inner marginal.  The floor converts the strict real
codegree hypothesis to the natural bound used by the combinatorial
recurrence. -/
theorem SignedRegularScalarSchedule.exists_exactRegularMarginalParameters
    {k L : ℕ} {beta target : ℝ}
    (S : SignedRegularScalarSchedule k L beta target)
    (hk : 0 < k)
    {zeta : ℝ}
    (hbeta₀ : 0 < beta) (hbeta₁ : beta ≤ 1)
    (hzeta₀ : 0 < zeta) (hzeta₁ : zeta < 1)
    (hcollision : (k : ℝ) * beta ≤ zeta / 4)
    (htail : ∀ D : ℕ, 0 < D → beta / (D : ℝ) ≤ 1 →
      signedRegularSurvival k D (beta / (D : ℝ)) L ≤ zeta / 4)
    (herror : beta * (L : ℝ) * target ≤ zeta / 4) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧
      ∃ D₀ : ℕ, 0 < D₀ ∧
        ExactRegularTwoSidedFixedLengthInnerMarginalAt.{0, 0}
          k zeta eta L D₀ := by
  let capSum : ℕ := ∑ r ∈ range (L + 1), S.orderCap r
  have hzeroMem : 0 ∈ range (L + 1) := by simp
  have hcapSumPos : 0 < capSum := by
    have hsingle : S.orderCap 0 ≤ capSum := by
      exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hzeroMem
    exact (S.cap_pos 0 (by omega)).trans_le hsingle
  let B : ℕ := capSum * (k + 1)
  have hBPos : 0 < B := Nat.mul_pos hcapSumPos (by omega)
  let eta : ℝ := min (1 / 2 : ℝ)
    (min (S.structuralBound / 2) (1 / (2 * (B : ℝ))))
  have hBReal : (0 : ℝ) < B := by exact_mod_cast hBPos
  have hetaPos : 0 < eta := by
    dsimp only [eta]
    exact lt_min (by norm_num)
      (lt_min (half_pos S.structural_pos)
        (one_div_pos.mpr (mul_pos (by norm_num) hBReal)))
  have hetaOne : eta < 1 :=
    (min_le_left _ _).trans_lt (by norm_num)
  have hetaStructural : eta ≤ S.structuralBound := by
    calc
      eta ≤ S.structuralBound / 2 :=
        (min_le_right _ _).trans (min_le_left _ _)
      _ ≤ S.structuralBound := by linarith [S.structural_pos]
  have hBetaEta : (B : ℝ) * eta ≤ 1 := by
    have hetaB : eta ≤ 1 / (2 * (B : ℝ)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hmul := mul_le_mul_of_nonneg_left hetaB hBReal.le
    have htwoB : (2 * (B : ℝ)) ≠ 0 := by positivity
    calc
      (B : ℝ) * eta ≤ (B : ℝ) * (1 / (2 * (B : ℝ))) := hmul
      _ = 1 / 2 := by field_simp
      _ ≤ 1 := by norm_num
  obtain ⟨Dlarge, hDlarge⟩ := exists_nat_gt (1 / S.structuralBound)
  let D₀ : ℕ := max 1 Dlarge
  have hD₀Pos : 0 < D₀ := (by simp [D₀])
  refine ⟨eta, hetaPos, hetaOne, D₀, hD₀Pos, ?_⟩
  intro V' E' _ _ _ H D hD₀D hunif hreg hpairReal
  have hDone : 1 ≤ D := (le_max_left 1 Dlarge).trans hD₀D
  have hDPos : 0 < D := Nat.zero_lt_of_lt hDone
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hDPos
  have hDlargeD : Dlarge ≤ D := (le_max_right 1 Dlarge).trans hD₀D
  have hlargeReal : 1 / S.structuralBound < (D : ℝ) :=
    hDlarge.trans_le (by exact_mod_cast hDlargeD)
  have hstructuralInv : 1 / (D : ℝ) ≤ S.structuralBound := by
    apply (div_le_iff₀ hDreal).2
    have hprod : 1 < S.structuralBound * (D : ℝ) := by
      rw [div_lt_iff₀ S.structural_pos] at hlargeReal
      simpa [mul_comm] using hlargeReal
    exact hprod.le
  have hp₁ : beta / (D : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hDreal).2
    have hbetaD : beta ≤ (D : ℝ) := by
      calc
        beta ≤ 1 := hbeta₁
        _ ≤ (D : ℝ) := by exact_mod_cast hDone
    simpa using hbetaD
  let C : ℕ := ⌊eta * (D : ℝ)⌋₊
  have hetaD₀ : 0 ≤ eta * (D : ℝ) :=
    mul_nonneg hetaPos.le hDreal.le
  have hCReal : (C : ℝ) ≤ eta * (D : ℝ) := by
    exact Nat.floor_le hetaD₀
  have hpair : ∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
      H.edgePairDegree u v ≤ C := by
    intro u hu v hv huv
    apply Nat.le_floor
    exact (hpairReal u hu v hv huv).le
  have hcodeg : (C : ℝ) / (D : ℝ) ≤ S.structuralBound := by
    calc
      (C : ℝ) / (D : ℝ) ≤
          (eta * (D : ℝ)) / (D : ℝ) :=
        (div_le_div_iff_of_pos_right hDreal).2 hCReal
      _ = eta := by field_simp
      _ ≤ S.structuralBound := hetaStructural
  have hsufficient : ∀ r, r < L →
      (S.orderCap (r + 1) - 1) * C +
          (S.orderCap (r + 1) - 1) * (k * C) ≤ D := by
    intro r hr
    have hrmem : r + 1 ∈ range (L + 1) := by
      rw [mem_range]
      omega
    have hcapSum : S.orderCap (r + 1) ≤ capSum := by
      exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hrmem
    have hcoefNat : (S.orderCap (r + 1) - 1) * (k + 1) ≤ B := by
      dsimp only [B]
      exact Nat.mul_le_mul ((Nat.sub_le _ _).trans hcapSum) le_rfl
    have hcoef : (((S.orderCap (r + 1) - 1) * (k + 1) : ℕ) : ℝ) ≤
        (B : ℝ) := by exact_mod_cast hcoefNat
    have hlhsReal :
        (((((S.orderCap (r + 1) - 1) * C +
            (S.orderCap (r + 1) - 1) * (k * C)) : ℕ) : ℝ)) ≤
          (D : ℝ) := by
      calc
        (((((S.orderCap (r + 1) - 1) * C +
            (S.orderCap (r + 1) - 1) * (k * C)) : ℕ) : ℝ)) =
            (((S.orderCap (r + 1) - 1) * (k + 1) : ℕ) : ℝ) *
              (C : ℝ) := by push_cast; ring
        _ ≤ (B : ℝ) * (C : ℝ) :=
          mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg C)
        _ ≤ (B : ℝ) * (eta * (D : ℝ)) :=
          mul_le_mul_of_nonneg_left hCReal hBReal.le
        _ = ((B : ℝ) * eta) * (D : ℝ) := by ring
        _ ≤ 1 * (D : ℝ) :=
          mul_le_mul_of_nonneg_right hBetaEta hDreal.le
        _ = (D : ℝ) := one_mul _
    exact_mod_cast hlhsReal
  refine ⟨(fun _ ↦ beta / (D : ℝ)), (fun _ ↦ ?_), (fun _ ↦ hp₁), ?_⟩
  · exact div_nonneg hbeta₀.le hDreal.le
  · exact H.innerAcceptanceMass_twoSided_of_signedRegularScalarSchedule
      S hk hDPos hunif hreg hpair hbeta₀.le hbeta₁ hp₁ hzeta₀.le
        hzeta₁.le hcollision (htail D hDPos hp₁) herror hcodeg
        hstructuralInv hsufficient

/-- The sharp two-sided fixed-length inner marginal for exact-regular
finite hypergraphs.  This is the unconditional probabilistic input needed
by the regular-completion outer iteration. -/
theorem sharpExactRegularTwoSidedFixedLengthInnerMarginal :
    SharpExactRegularTwoSidedFixedLengthInnerMarginal := by
  intro k hk zeta hzeta₀ hzeta₁
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  let beta : ℝ := zeta / (8 * (k : ℝ))
  have hdenom : (0 : ℝ) < 8 * (k : ℝ) := mul_pos (by norm_num) hkReal
  have hbeta₀ : 0 < beta := div_pos hzeta₀ hdenom
  have hbeta₁ : beta ≤ 1 := by
    apply (div_le_iff₀ hdenom).2
    have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hkb : (k : ℝ) * beta = zeta / 8 := by
    dsimp only [beta]
    field_simp
  have hcollision : (k : ℝ) * beta ≤ zeta / 4 := by
    rw [hkb]
    linarith
  have hkbOne : (k : ℝ) * beta < 1 := by
    rw [hkb]
    linarith
  let alpha : ℝ := beta * (1 - (k : ℝ) * beta)
  have halpha₀ : 0 < alpha :=
    mul_pos hbeta₀ (sub_pos.mpr hkbOne)
  have halphaBeta : alpha ≤ beta := by
    dsimp only [alpha]
    nlinarith [mul_nonneg hbeta₀.le
      (mul_nonneg (Nat.cast_nonneg k) hbeta₀.le)]
  have halpha₁ : alpha ≤ 1 := halphaBeta.trans hbeta₁
  obtain ⟨L, hmeanTail⟩ := exists_meanFieldSurvival_lt hk halpha₀
    halpha₁ (div_pos hzeta₀ (by norm_num : (0 : ℝ) < 4))
  let target : ℝ := zeta / (8 * (beta * (L : ℝ) + 1))
  have hfactor₀ : 0 < beta * (L : ℝ) + 1 := by positivity
  have htarget₀ : 0 < target := by
    exact div_pos hzeta₀ (mul_pos (by norm_num) hfactor₀)
  have htargetEq : target * (beta * (L : ℝ) + 1) = zeta / 8 := by
    dsimp only [target]
    field_simp
  have herror : beta * (L : ℝ) * target ≤ zeta / 4 := by
    have hpart : beta * (L : ℝ) ≤ beta * (L : ℝ) + 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hpart htarget₀.le
    have hzetaEight : zeta / 8 ≤ zeta / 4 := by linarith
    calc
      beta * (L : ℝ) * target ≤
          (beta * (L : ℝ) + 1) * target := by simpa [mul_assoc] using hmul
      _ = zeta / 8 := by rw [mul_comm]; exact htargetEq
      _ ≤ zeta / 4 := hzetaEight
  obtain ⟨S⟩ := exists_signedRegularScalarSchedule k L hk hbeta₀.le htarget₀
  have htail : ∀ D : ℕ, 0 < D → beta / (D : ℝ) ≤ 1 →
      signedRegularSurvival k D (beta / (D : ℝ)) L ≤ zeta / 4 := by
    intro D hD hp₁
    exact (signedRegularSurvival_le_meanFieldSurvival_collisionAdjusted
      hk hD hbeta₀.le hbeta₁ hp₁ hkbOne.le L).trans hmeanTail.le
  obtain ⟨eta, heta₀, heta₁, D₀, hD₀, hgen⟩ :=
    S.exists_exactRegularMarginalParameters hk hbeta₀ hbeta₁
      hzeta₀ hzeta₁ hcollision htail herror
  exact ⟨eta, heta₀, heta₁, L, D₀, hD₀, hgen⟩

end FiniteHypergraph

end

end Erdos76
