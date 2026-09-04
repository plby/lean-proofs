import ErdosProblems.Erdos88.SwitchingHalasz
import ErdosProblems.Erdos88.SwitchingLemma136
import ErdosProblems.Erdos88.BoundedWindow

/-!
# The lower fixed-tuple count in the switching argument

This module combines the private-neighbour fibre decomposition with the
near-central binomial lower bound.  It isolates the exact remaining input:
a large family of outside assignments on which the switching equations and
the bounded edge-count window can be completed simultaneously.
-/

open Classical
open scoped BigOperators

namespace Erdos88.Switching

open Erdos88.Probability
open Erdos88.Concentration

/-- Degrees split additively across disjoint vertex sets. -/
lemma degreeInto_union_of_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) {A B : Finset V} (hAB : Disjoint A B) :
    AKSGraph.degreeInto G v (A ∪ B) =
      AKSGraph.degreeInto G v A + AKSGraph.degreeInto G v B := by
  rw [AKSGraph.degreeInto, AKSGraph.degreeInto, AKSGraph.degreeInto]
  have hinter : G.neighborFinset v ∩ (A ∪ B) =
      (G.neighborFinset v ∩ A) ∪ (G.neighborFinset v ∩ B) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    aesop
  rw [hinter, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro x hxA hxB
  exact Finset.disjoint_left.mp hAB
    (Finset.mem_inter.mp hxA).2 (Finset.mem_inter.mp hxB).2

/-- Induced edges in a disjoint union split into the two internal counts
and the sum of the cross-degrees from the second set into the first. -/
lemma edgeCount_union_of_disjoint {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {A B : Finset V} (hAB : Disjoint A B) :
    AKSGraph.edgeCount G (A ∪ B) = AKSGraph.edgeCount G A +
      AKSGraph.edgeCount G B + ∑ v ∈ B, AKSGraph.degreeInto G v A := by
  revert hAB
  induction B using Finset.induction_on with
  | empty =>
      intro _hAB
      simp [AKSGraph.edgeCount]
  | @insert v B hv ih =>
      intro hAB
      have hvA : v ∉ A := by
        intro hvA
        exact Finset.disjoint_left.mp hAB hvA (Finset.mem_insert_self v B)
      have hAB' : Disjoint A B := hAB.mono_right (Finset.subset_insert v B)
      have hvUnion : v ∉ A ∪ B := by simp [hv, hvA]
      calc
        AKSGraph.edgeCount G (A ∪ insert v B) =
            AKSGraph.edgeCount G (insert v (A ∪ B)) := by
          congr 2
          ext x
          simp
        _ = AKSGraph.edgeCount G (A ∪ B) +
            AKSGraph.degreeInto G v (A ∪ B) :=
          AKSGraph.edgeCount_insert G v (A ∪ B) hvUnion
        _ = (AKSGraph.edgeCount G A + AKSGraph.edgeCount G B +
              ∑ x ∈ B, AKSGraph.degreeInto G x A) +
            (AKSGraph.degreeInto G v A + AKSGraph.degreeInto G v B) := by
          rw [ih hAB', degreeInto_union_of_disjoint G v hAB']
        _ = AKSGraph.edgeCount G A + AKSGraph.edgeCount G (insert v B) +
              ∑ x ∈ insert v B, AKSGraph.degreeInto G x A := by
          rw [AKSGraph.edgeCount_insert G v B hv, Finset.sum_insert hv]
          omega

/-- Integer form of `edgeCount_union_of_disjoint`. -/
lemma edgeScore_union_of_disjoint {n : ℕ} (G : SimpleGraph (Fin n))
    {A B : Finset (Fin n)} (hAB : Disjoint A B) :
    edgeScore G (A ∪ B) = edgeScore G A + edgeScore G B +
      ∑ v ∈ B, (AKSGraph.degreeInto G v A : ℤ) := by
  simp_rw [edgeScore_eq_edgeCount]
  have h := congrArg (fun x : ℕ ↦ (x : ℤ))
    (edgeCount_union_of_disjoint G hAB)
  push_cast at h
  exact h

/-- After exposing a disjoint outside set, the remaining induced-edge
statistic is exactly a linearly perturbed edge polynomial.  This is the
finite conditioning identity used when Theorem 3.1 is applied on the
common-nonneighbor reservoir in KSSS Lemma 13.4. -/
lemma edgeScore_union_eq_perturbedEdgePolynomial {n : ℕ}
    (G : SimpleGraph (Fin n)) {A B : Finset (Fin n)}
    (hAB : Disjoint A B) :
    (edgeScore G (A ∪ B) : ℝ) =
      Probability.perturbedEdgePolynomial G (edgeScore G A : ℝ)
        (fun v ↦ AKSGraph.degreeInto G v A) B := by
  rw [Probability.perturbedEdgePolynomial,
    Probability.edgePolynomial_eq_inducedEdgeCount]
  simp_rw [edgeScore_eq_edgeCount]
  change (AKSGraph.edgeCount G (A ∪ B) : ℝ) =
    (AKSGraph.edgeCount G A : ℝ) +
      (AKSGraph.edgeCount G B : ℝ) +
        ∑ v, (AKSGraph.degreeInto G v A : ℝ) * Probability.bit v B
  have hsum : (∑ v, (AKSGraph.degreeInto G v A : ℝ) *
      Probability.bit v B) =
      ∑ v ∈ B, (AKSGraph.degreeInto G v A : ℝ) := by
    simp [Probability.bit]
  rw [hsum]
  exact_mod_cast edgeCount_union_of_disjoint G hAB

/-- Conditioning a perturbed edge polynomial on a disjoint fixed set folds
that set into the constant term and adds its cross-degrees to the remaining
linear coefficients. -/
lemma perturbedEdgePolynomial_union_of_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (e₀ : ℝ) (c : V → ℝ)
    {O B : Finset V} (hOB : Disjoint O B) :
    Probability.perturbedEdgePolynomial G e₀ c (O ∪ B) =
      Probability.perturbedEdgePolynomial G
        (Probability.perturbedEdgePolynomial G e₀ c O)
        (fun v ↦ c v + AKSGraph.degreeInto G v O) B := by
  rw [Probability.perturbedEdgePolynomial,
    Probability.perturbedEdgePolynomial,
    Probability.perturbedEdgePolynomial]
  rw [Probability.edgePolynomial_eq_inducedEdgeCount,
    Probability.edgePolynomial_eq_inducedEdgeCount,
    Probability.edgePolynomial_eq_inducedEdgeCount]
  change e₀ + (AKSGraph.edgeCount G (O ∪ B) : ℝ) +
      ∑ v, c v * Probability.bit v (O ∪ B) =
    (e₀ + (AKSGraph.edgeCount G O : ℝ) +
      ∑ v, c v * Probability.bit v O) +
      (AKSGraph.edgeCount G B : ℝ) +
      ∑ v, (c v + AKSGraph.degreeInto G v O) * Probability.bit v B
  rw [edgeCount_union_of_disjoint G hOB]
  have hsumUnion :
      (∑ v, c v * Probability.bit v (O ∪ B)) =
        (∑ v, c v * Probability.bit v O) +
          ∑ v, c v * Probability.bit v B := by
    have hrestrict (S : Finset V) :
        (∑ v, c v * Probability.bit v S) = ∑ v ∈ S, c v := by
      simpa only [Probability.bit, mul_ite, mul_one, mul_zero,
        Finset.inter_eq_right.mpr (Finset.subset_univ S)] using
        (Finset.sum_ite_mem (Finset.univ : Finset V) S c)
    rw [hrestrict, hrestrict, hrestrict, Finset.sum_union hOB]
  have hsumDegree :
      (∑ v, (AKSGraph.degreeInto G v O : ℝ) * Probability.bit v B) =
        ∑ v ∈ B, (AKSGraph.degreeInto G v O : ℝ) := by
    simp [Probability.bit]
  rw [hsumUnion]
  rw [show (∑ v, (c v + AKSGraph.degreeInto G v O) *
      Probability.bit v B) =
      (∑ v, c v * Probability.bit v B) +
        ∑ v, (AKSGraph.degreeInto G v O : ℝ) *
          Probability.bit v B by
    simp only [add_mul, Finset.sum_add_distrib]]
  rw [hsumDegree]
  push_cast
  ring

/-- Exact size of a Boolean-cube event with a prescribed included set and
a disjoint prescribed excluded set.  This is the endpoint-orientation factor
in the first exposure of the lower half of KSSS Lemma 13.4. -/
lemma card_powerset_filter_forcedIncludedExcluded
    {V : Type*} [Fintype V] [DecidableEq V]
    (A Y Z : Finset V) (hY : Y ⊆ A) (hZ : Z ⊆ A)
    (hYZ : Disjoint Y Z) :
    (A.powerset.filter fun O ↦ Y ⊆ O ∧ Disjoint O Z).card =
      2 ^ (A.card - (Y ∪ Z).card) := by
  classical
  let source := (A \ (Y ∪ Z)).powerset
  let target := A.powerset.filter fun O ↦ Y ⊆ O ∧ Disjoint O Z
  have hcard : source.card = target.card := by
    apply Finset.card_bij (fun R _hR ↦ Y ∪ R)
    · intro R hR
      have hRA : R ⊆ A \ (Y ∪ Z) := Finset.mem_powerset.mp hR
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr ?_, Finset.subset_union_left, ?_⟩
      · exact Finset.union_subset hY fun x hxR ↦
          (Finset.mem_sdiff.mp (hRA hxR)).1
      · rw [Finset.disjoint_left]
        intro x hx hxZ
        rcases Finset.mem_union.mp hx with hxY | hxR
        · exact Finset.disjoint_left.mp hYZ hxY hxZ
        · exact (Finset.mem_sdiff.mp (hRA hxR)).2
            (Finset.mem_union_right Y hxZ)
    · intro R hR S hS hEq
      have hRY : Disjoint R Y := by
        rw [Finset.disjoint_left]
        intro x hxR hxY
        have hRsub : R ⊆ A \ (Y ∪ Z) := Finset.mem_powerset.mp hR
        exact (Finset.mem_sdiff.mp (hRsub hxR)).2
          (Finset.mem_union_left Z hxY)
      have hSY : Disjoint S Y := by
        rw [Finset.disjoint_left]
        intro x hxS hxY
        have hSsub : S ⊆ A \ (Y ∪ Z) := Finset.mem_powerset.mp hS
        exact (Finset.mem_sdiff.mp (hSsub hxS)).2
          (Finset.mem_union_left Z hxY)
      ext x
      have hx := Finset.ext_iff.mp hEq x
      by_cases hxY : x ∈ Y
      · have hxR : x ∉ R := fun hxR ↦
          Finset.disjoint_left.mp hRY hxR hxY
        have hxS : x ∉ S := fun hxS ↦
          Finset.disjoint_left.mp hSY hxS hxY
        simp [hxR, hxS]
      · simpa only [Finset.mem_union, hxY, false_or] using hx
    · intro O hO
      have hOA : O ⊆ A := Finset.mem_powerset.mp (Finset.mem_filter.mp hO).1
      have hYO : Y ⊆ O := (Finset.mem_filter.mp hO).2.1
      have hOZ : Disjoint O Z := (Finset.mem_filter.mp hO).2.2
      let R := O \ Y
      have hRsource : R ∈ source := by
        apply Finset.mem_powerset.mpr
        intro x hxR
        have hxR' := Finset.mem_sdiff.mp hxR
        apply Finset.mem_sdiff.mpr
        refine ⟨hOA hxR'.1, ?_⟩
        intro hxUnion
        rcases Finset.mem_union.mp hxUnion with hxY | hxZ
        · exact hxR'.2 hxY
        · exact Finset.disjoint_left.mp hOZ hxR'.1 hxZ
      refine ⟨R, hRsource, ?_⟩
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hxY | hxR
        · exact hYO hxY
        · exact (Finset.mem_sdiff.mp hxR).1
      · intro hxO
        by_cases hxY : x ∈ Y
        · exact Finset.mem_union_left R hxY
        · exact Finset.mem_union_right Y (Finset.mem_sdiff.mpr ⟨hxO, hxY⟩)
  rw [← hcard]
  dsimp only [source]
  rw [Finset.card_powerset,
    Finset.card_sdiff_of_subset (Finset.union_subset hY hZ)]

/-- Subtracting a finite union of bad events from a prescribed endpoint
orientation.  The bad-event counts are deliberately taken on the whole
cube, which is the form directly supplied by Chebyshev. -/
lemma card_powerset_filter_forcedIncludedExcluded_avoid_ge
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I]
    (A Y Z : Finset V) (hY : Y ⊆ A) (hZ : Z ⊆ A)
    (hYZ : Disjoint Y Z) (Q : I → Finset V → Prop) :
    ((2 ^ (A.card - (Y ∪ Z).card) : ℕ) : ℝ) -
        ∑ i : I, ((A.powerset.filter (Q i)).card : ℝ) ≤
      ((A.powerset.filter fun O ↦
        Y ⊆ O ∧ Disjoint O Z ∧ ∀ i, ¬ Q i O).card : ℝ) := by
  classical
  let endpoint := A.powerset.filter fun O ↦ Y ⊆ O ∧ Disjoint O Z
  let bad := A.powerset.filter fun O ↦ ∃ i, Q i O
  let good := A.powerset.filter fun O ↦
    Y ⊆ O ∧ Disjoint O Z ∧ ∀ i, ¬ Q i O
  have hbadSub : bad ⊆ Finset.univ.biUnion fun i : I ↦
      A.powerset.filter (Q i) := by
    intro O hO
    have hbad := (Finset.mem_filter.mp hO).2
    obtain ⟨i, hi⟩ := hbad
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hO).1, hi⟩⟩
  have hbadCard : (bad.card : ℝ) ≤
      ∑ i : I, ((A.powerset.filter (Q i)).card : ℝ) := by
    have h₁ := Finset.card_le_card hbadSub
    have h₂ : (Finset.univ.biUnion fun i : I ↦
        A.powerset.filter (Q i)).card ≤
        ∑ i ∈ (Finset.univ : Finset I),
          (A.powerset.filter (Q i)).card := Finset.card_biUnion_le
    exact_mod_cast h₁.trans (by simpa using h₂)
  have hendpointSub : endpoint ⊆ good ∪ bad := by
    intro O hO
    have hE := (Finset.mem_filter.mp hO).2
    by_cases hQ : ∃ i, Q i O
    · exact Finset.mem_union_right good
        (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hO).1, hQ⟩)
    · exact Finset.mem_union_left bad
        (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hO).1,
          hE.1, hE.2, by simpa only [not_exists] using hQ⟩)
  have hendpointCard : (endpoint.card : ℝ) ≤
      (good.card : ℝ) + (bad.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hendpointSub |>.trans
      (Finset.card_union_le good bad))
  have hendpoint : endpoint.card = 2 ^ (A.card - (Y ∪ Z).card) := by
    simpa only [endpoint] using
      card_powerset_filter_forcedIncludedExcluded A Y Z hY hZ hYZ
  rw [hendpoint] at hendpointCard
  linarith

/-- The uniform law on subsets of an arbitrary finite type is the
Bernoulli-`1/2` law. -/
lemma uniformProbability_eq_eventProbability_half_finite
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Finset V → Prop) :
    uniformProbability P = eventProbability (1 / 2 : ℝ) P := by
  classical
  calc
    uniformProbability P =
        uniformExpectation (fun W : Finset V ↦ if P W then 1 else 0) := by
      simp [uniformProbability, uniformExpectation]
    _ = expectation (1 / 2 : ℝ)
          (fun W : Finset V ↦ if P W then 1 else 0) :=
      Erdos88.BooleanSlices.uniformExpectation_finset_eq_probability_half_finite _
    _ = eventProbability (1 / 2 : ℝ) P := rfl

/-- Counting Chebyshev inequality on the powerset of a specified coordinate
set, expressed after forgetting subtype membership proofs. -/
lemma card_powerset_centered_tail_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Finset V) (X : Finset V → ℝ) (t : ℝ) (ht : 0 < t) :
    ((A.powerset.filter fun O ↦
        t ≤ |X O - expectation (1 / 2 : ℝ)
          (fun R : Finset (A : Set V) ↦
            X (BoundedWindow.subtypeSubsetImage A R))|).card : ℝ) ≤
      (2 : ℝ) ^ A.card *
        (variance (1 / 2 : ℝ)
          (fun R : Finset (A : Set V) ↦
            X (BoundedWindow.subtypeSubsetImage A R)) / t ^ 2) := by
  classical
  let X' := fun R : Finset (A : Set V) ↦
    X (BoundedWindow.subtypeSubsetImage A R)
  let P := fun R : Finset (A : Set V) ↦
    t ≤ |X' R - expectation (1 / 2 : ℝ) X'|
  have hcheb := chebyshev_sq_bound (V := (A : Set V))
    (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num) ht X'
  have hiff : ∀ R : Finset (A : Set V), P R ↔
      t ^ 2 ≤ (X' R - expectation (1 / 2 : ℝ) X') ^ 2 := by
    intro R
    simpa only [P, sq_abs] using
      (sq_le_sq₀ ht.le (abs_nonneg
        (X' R - expectation (1 / 2 : ℝ) X'))).symm
  have hprob : uniformProbability P ≤
      variance (1 / 2 : ℝ) X' / t ^ 2 := by
    rw [uniformProbability_eq_eventProbability_half_finite]
    unfold eventProbability at hcheb ⊢
    simpa only [hiff] using hcheb
  rw [uniformProbability] at hprob
  have hcard :
      ((Finset.univ : Finset (Finset (A : Set V))).filter P).card =
        (A.powerset.filter fun O ↦
          t ≤ |X O - expectation (1 / 2 : ℝ) X'|).card := by
    simpa only [P, X'] using
      BoundedWindow.card_filter_subtypeSubsetImage A
        (fun O ↦ t ≤ |X O - expectation (1 / 2 : ℝ) X'|)
  rw [hcard] at hprob
  have hden : (Fintype.card (Finset (A : Set V)) : ℝ) =
      (2 : ℝ) ^ A.card := by
    have hAcard : Fintype.card (A : Set V) = A.card := by
      simpa using Fintype.card_coe A
    rw [Fintype.card_finset, hAcard]
    norm_num [Nat.cast_pow]
  rw [hden] at hprob
  have hmul := (div_le_iff₀
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ A.card)).mp hprob
  simpa only [X', mul_comm] using hmul

/-- Mixed second moment of two Boolean coordinates at density one half. -/
lemma expectation_bit_mul_half
    {V : Type*} [Fintype V] [DecidableEq V] (i j : V) :
    expectation (1 / 2 : ℝ) (fun U : Finset V ↦ bit i U * bit j U) =
      if i = j then 1 / 2 else 1 / 4 := by
  have hi : bit i = monomial ({i} : Finset V) := by
    funext U
    simp [bit, monomial]
  have hj : bit j = monomial ({j} : Finset V) := by
    funext U
    simp [bit, monomial]
  rw [hi, hj, expectation_monomial_mul (by norm_num) (by norm_num)]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]
    norm_num

/-- Exact variance of a linear form in independent unbiased Boolean
coordinates.  This is the Chebyshev input for every switching row during the
first exposure. -/
lemma variance_linearBits_half
    {V : Type*} [Fintype V] [DecidableEq V] (a : V → ℝ) :
    variance (1 / 2 : ℝ)
        (fun U : Finset V ↦ ∑ i : V, a i * bit i U) =
      (1 / 4 : ℝ) * ∑ i : V, a i ^ 2 := by
  let X := fun U : Finset V ↦ ∑ i : V, a i * bit i U
  have hmean : expectation (1 / 2 : ℝ) X =
      (1 / 2 : ℝ) * ∑ i : V, a i := by
    change expectation (1 / 2 : ℝ)
        (fun U ↦ ∑ i ∈ (Finset.univ : Finset V), a i * bit i U) = _
    rw [expectation_sum]
    simp_rw [expectation_smul,
      expectation_bit (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num)]
    rw [← Finset.sum_mul]
    ring
  rw [variance_eq_expectation_sq_sub, hmean]
  have hsquare : (fun U : Finset V ↦ X U ^ 2) =
      fun U ↦ ∑ i ∈ (Finset.univ : Finset V),
        ∑ j ∈ (Finset.univ : Finset V),
          (a i * a j) * (bit i U * bit j U) := by
    funext U
    dsimp only [X]
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [hsquare, expectation_sum]
  simp_rw [expectation_sum, expectation_smul, expectation_bit_mul_half]
  have hdouble :
      (∑ i ∈ (Finset.univ : Finset V),
        ∑ j ∈ (Finset.univ : Finset V),
          a i * a j * if i = j then (1 / 2 : ℝ) else 1 / 4) =
      (1 / 4 : ℝ) * (∑ i : V, a i) ^ 2 +
        (1 / 4 : ℝ) * ∑ i : V, a i ^ 2 := by
    have hterm (i j : V) : a i * a j *
        (if i = j then (1 / 2 : ℝ) else 1 / 4) =
      (1 / 4 : ℝ) * (a i * a j) +
        if i = j then (1 / 4 : ℝ) * a i ^ 2 else 0 := by
      by_cases hij : i = j
      · subst j
        simp
        ring
      · simp [hij]
        ring
    simp_rw [hterm]
    simp only [Finset.sum_add_distrib]
    rw [show (∑ i ∈ (Finset.univ : Finset V),
        ∑ j ∈ (Finset.univ : Finset V), (1 / 4 : ℝ) * (a i * a j)) =
      (1 / 4 : ℝ) * (∑ i : V, a i) ^ 2 by
      calc
        _ = ∑ i : V, (1 / 4 : ℝ) *
            (a i * ∑ j : V, a j) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [← Finset.mul_sum]
          congr 1
          rw [← Finset.mul_sum]
        _ = (1 / 4 : ℝ) * ∑ i : V,
            (a i * ∑ j : V, a j) := by rw [Finset.mul_sum]
        _ = (1 / 4 : ℝ) *
            ((∑ i : V, a i) * ∑ j : V, a j) := by
          rw [Finset.sum_mul]
        _ = _ := by ring]
    have hdiag (i : V) :
        (∑ j : V, if i = j then (1 / 4 : ℝ) * a i ^ 2 else 0) =
          (1 / 4 : ℝ) * a i ^ 2 := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _hj hji
        simp [Ne.symm hji]
      · simp
    simp_rw [hdiag]
    rw [← Finset.mul_sum]
  rw [hdouble]
  ring

/-- A switching row evaluated on a subset of `A` is the corresponding
linear Boolean form on the subtype cut out by `A`. -/
lemma switchingDifferenceMatrix_mulVec_subtypeSubsetImage
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (A : Finset V)
    (R : Finset (A : Set V)) (i : I) :
    (switchingDifferenceMatrix G p).mulVec
        (finsetIndicator (BoundedWindow.subtypeSubsetImage A R)) i =
      ∑ v : (A : Set V),
        switchingDifferenceMatrix G p i v.1 * Probability.bit v R := by
  rw [Matrix.mulVec_apply]
  change (∑ v : V, switchingDifferenceMatrix G p i v *
      (if v ∈ BoundedWindow.subtypeSubsetImage A R then 1 else 0)) = _
  rw [show (∑ v : V, switchingDifferenceMatrix G p i v *
      (if v ∈ BoundedWindow.subtypeSubsetImage A R then 1 else 0)) =
      ∑ v ∈ A, switchingDifferenceMatrix G p i v *
        (if v ∈ BoundedWindow.subtypeSubsetImage A R then 1 else 0) by
    rw [← Finset.sum_subset (Finset.subset_univ A)]
    intro v _hvA hv
    have hvNot : v ∉ BoundedWindow.subtypeSubsetImage A R := fun hvImage ↦
      hv (BoundedWindow.subtypeSubsetImage_subset A R hvImage)
    simp [hvNot]]
  rw [show (∑ v ∈ A, switchingDifferenceMatrix G p i v *
      (if v ∈ BoundedWindow.subtypeSubsetImage A R then 1 else 0)) =
      ∑ v : (A : Set V), switchingDifferenceMatrix G p i v.1 *
        (if v ∈ R then 1 else 0) by
    calc
      _ = ∑ v : (A : Set V), switchingDifferenceMatrix G p i v.1 *
          (if v.1 ∈ BoundedWindow.subtypeSubsetImage A R then 1 else 0) :=
        Finset.sum_subtype A (fun _ ↦ Iff.rfl) _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v _hv
        congr 1
        simp [BoundedWindow.subtypeSubsetImage]]
  rfl

/-- Every switching-matrix row has restricted-cube variance at most one
quarter of the number of exposed coordinates. -/
lemma variance_switchingDifferenceMatrix_mulVec_on_powerset_le
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (A : Finset V) (i : I) :
    Probability.variance (1 / 2 : ℝ)
        (fun R : Finset (A : Set V) ↦
          (switchingDifferenceMatrix G p).mulVec
            (finsetIndicator (BoundedWindow.subtypeSubsetImage A R)) i) ≤
      (A.card : ℝ) / 4 := by
  have hfun : (fun R : Finset (A : Set V) ↦
      (switchingDifferenceMatrix G p).mulVec
        (finsetIndicator (BoundedWindow.subtypeSubsetImage A R)) i) =
      (fun R ↦ ∑ v : (A : Set V),
        switchingDifferenceMatrix G p i v.1 * Probability.bit v R) := by
    funext R
    exact switchingDifferenceMatrix_mulVec_subtypeSubsetImage G p A R i
  rw [hfun, variance_linearBits_half]
  have hsq : ∀ v : (A : Set V),
      (switchingDifferenceMatrix G p i v.1) ^ 2 ≤ 1 := by
    intro v
    rcases switchingDifferenceMatrix_ternary G p i v.1 with h | h | h <;>
      rw [h] <;> norm_num
  calc
    (1 / 4 : ℝ) * ∑ v : (A : Set V),
        (switchingDifferenceMatrix G p i v.1) ^ 2 ≤
      (1 / 4 : ℝ) * ∑ _v : (A : Set V), 1 := by
        gcongr with v
        exact hsq v
    _ = (A.card : ℝ) / 4 := by
      simp
      ring

/-- Counting Chebyshev bound for one switching row on a restricted outside
cube. -/
lemma card_switchingDifferenceMatrix_mulVec_centered_tail_le
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (A : Finset V)
    (i : I) (t : ℝ) (ht : 0 < t) :
    ((A.powerset.filter fun O ↦
        t ≤ |(switchingDifferenceMatrix G p).mulVec
              (finsetIndicator O) i -
            Probability.expectation (1 / 2 : ℝ)
              (fun R : Finset (A : Set V) ↦
                (switchingDifferenceMatrix G p).mulVec
                  (finsetIndicator
                    (BoundedWindow.subtypeSubsetImage A R)) i)|).card : ℝ) ≤
      (2 : ℝ) ^ A.card * (((A.card : ℝ) / 4) / t ^ 2) := by
  exact (card_powerset_centered_tail_le A
    (fun O ↦ (switchingDifferenceMatrix G p).mulVec
      (finsetIndicator O) i) t ht).trans
    (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right
        (variance_switchingDifferenceMatrix_mulVec_on_powerset_le G p A i)
        (sq_nonneg t)) (by positivity))

/-- First-exposure Chebyshev/union-bound count for KSSS Lemma 13.4.  The
mean-polynomial deviation is combined with every switching-row deviation,
while the endpoint orientation is counted exactly. -/
lemma card_switching_firstExposure_good_ge
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V)
    (A Y Z : Finset V) (hY : Y ⊆ A) (hZ : Z ⊆ A)
    (hYZ : Disjoint Y Z) (X : Finset V → ℝ)
    (tMean tRow : ℝ) (htMean : 0 < tMean) (htRow : 0 < tRow) :
    ((2 ^ (A.card - (Y ∪ Z).card) : ℕ) : ℝ) -
        (2 : ℝ) ^ A.card *
          (Probability.variance (1 / 2 : ℝ)
              (fun R : Finset (A : Set V) ↦
                X (BoundedWindow.subtypeSubsetImage A R)) / tMean ^ 2 +
            (Fintype.card I : ℝ) * (((A.card : ℝ) / 4) / tRow ^ 2)) ≤
      ((A.powerset.filter fun O ↦
        Y ⊆ O ∧ Disjoint O Z ∧
          |X O - Probability.expectation (1 / 2 : ℝ)
            (fun R : Finset (A : Set V) ↦
              X (BoundedWindow.subtypeSubsetImage A R))| < tMean ∧
          ∀ i,
            |(switchingDifferenceMatrix G p).mulVec
                  (finsetIndicator O) i -
              Probability.expectation (1 / 2 : ℝ)
                (fun R : Finset (A : Set V) ↦
                  (switchingDifferenceMatrix G p).mulVec
                    (finsetIndicator
                      (BoundedWindow.subtypeSubsetImage A R)) i)| <
                tRow).card : ℝ) := by
  classical
  let meanX := Probability.expectation (1 / 2 : ℝ)
    (fun R : Finset (A : Set V) ↦
      X (BoundedWindow.subtypeSubsetImage A R))
  let meanRow := fun i : I ↦ Probability.expectation (1 / 2 : ℝ)
    (fun R : Finset (A : Set V) ↦
      (switchingDifferenceMatrix G p).mulVec
        (finsetIndicator (BoundedWindow.subtypeSubsetImage A R)) i)
  let Q : Option I → Finset V → Prop
    | none => fun O ↦ tMean ≤ |X O - meanX|
    | some i => fun O ↦ tRow ≤
        |(switchingDifferenceMatrix G p).mulVec (finsetIndicator O) i -
          meanRow i|
  have havoid := card_powerset_filter_forcedIncludedExcluded_avoid_ge
    A Y Z hY hZ hYZ Q
  have hmeanBad :
      ((A.powerset.filter (Q none)).card : ℝ) ≤
        (2 : ℝ) ^ A.card *
          (Probability.variance (1 / 2 : ℝ)
            (fun R : Finset (A : Set V) ↦
              X (BoundedWindow.subtypeSubsetImage A R)) / tMean ^ 2) := by
    simpa only [Q, meanX] using card_powerset_centered_tail_le A X tMean htMean
  have hrowBad : ∀ i : I,
      ((A.powerset.filter (Q (some i))).card : ℝ) ≤
        (2 : ℝ) ^ A.card * (((A.card : ℝ) / 4) / tRow ^ 2) := by
    intro i
    simpa only [Q, meanRow] using
      card_switchingDifferenceMatrix_mulVec_centered_tail_le
        G p A i tRow htRow
  have hsumBad :
      (∑ q : Option I, ((A.powerset.filter (Q q)).card : ℝ)) ≤
        (2 : ℝ) ^ A.card *
          (Probability.variance (1 / 2 : ℝ)
              (fun R : Finset (A : Set V) ↦
                X (BoundedWindow.subtypeSubsetImage A R)) / tMean ^ 2 +
            (Fintype.card I : ℝ) * (((A.card : ℝ) / 4) / tRow ^ 2)) := by
    rw [Fintype.sum_option]
    calc
      ((A.powerset.filter (Q none)).card : ℝ) +
          ∑ i : I, ((A.powerset.filter (Q (some i))).card : ℝ) ≤
        (2 : ℝ) ^ A.card *
            (Probability.variance (1 / 2 : ℝ)
              (fun R : Finset (A : Set V) ↦
                X (BoundedWindow.subtypeSubsetImage A R)) / tMean ^ 2) +
          ∑ _i : I, (2 : ℝ) ^ A.card *
            (((A.card : ℝ) / 4) / tRow ^ 2) := by
        apply add_le_add hmeanBad
        exact Finset.sum_le_sum fun i _hi ↦ hrowBad i
      _ = _ := by simp; ring
  have hbase := (sub_le_sub_left hsumBad _).trans havoid
  have hcard :
      (A.powerset.filter fun O ↦
        Y ⊆ O ∧ Disjoint O Z ∧ ∀ q, ¬Q q O).card ≤
      (A.powerset.filter fun O ↦
        Y ⊆ O ∧ Disjoint O Z ∧
          |X O - Probability.expectation (1 / 2 : ℝ)
            (fun R : Finset (A : Set V) ↦
              X (BoundedWindow.subtypeSubsetImage A R))| < tMean ∧
          ∀ i,
            |(switchingDifferenceMatrix G p).mulVec
                  (finsetIndicator O) i -
              Probability.expectation (1 / 2 : ℝ)
                (fun R : Finset (A : Set V) ↦
                  (switchingDifferenceMatrix G p).mulVec
                    (finsetIndicator
                      (BoundedWindow.subtypeSubsetImage A R)) i)| <
                tRow).card := by
    apply Finset.card_le_card
    intro O hO
    simp only [Finset.mem_filter, Finset.mem_powerset] at hO ⊢
    refine ⟨hO.1, hO.2.1, hO.2.2.1, ?_, ?_⟩
    · simpa only [Q, meanX, not_le] using hO.2.2.2 none
    · intro i
      simpa only [Q, meanRow, not_le] using hO.2.2.2 (some i)
  exact hbase.trans (by exact_mod_cast hcard)

/-- A switching row vanishes on the common nonneighbor reservoir. -/
lemma switchingDifferenceMatrix_apply_of_mem_commonNonneighbors
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I]
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V)
    (i : I) {w : V} (hw : w ∈ switchingCommonNonneighbors G p S₀) :
    switchingDifferenceMatrix G p i w = 0 := by
  have hw' := mem_nonneighborsOf.mp hw
  have hy : ¬G.Adj (p i).1 w := hw'.2.2 _ (by simp)
  have hz : ¬G.Adj (p i).2 w := hw'.2.2 _ (by simp)
  simp [switchingDifferenceMatrix, hy, hz]

/-- The sum of row `i` over all private blocks is exactly the size of its
own private block. -/
lemma sum_switchingDifferenceMatrix_privateUnion
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V)
    (hp : PairEndpointsDistinct p) (i : I) :
    (∑ v ∈ Finset.univ.biUnion
        (fun j ↦ switchingPrivateNeighbors G p j S₀),
          switchingDifferenceMatrix G p i v) =
      (switchingPrivateNeighbors G p i S₀).card := by
  rw [Finset.sum_biUnion]
  · calc
      (∑ j ∈ (Finset.univ : Finset I),
          ∑ v ∈ switchingPrivateNeighbors G p j S₀,
            switchingDifferenceMatrix G p i v) =
        ∑ j ∈ (Finset.univ : Finset I),
          ∑ _v ∈ switchingPrivateNeighbors G p j S₀,
            if i = j then (1 : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro j _hj
          apply Finset.sum_congr rfl
          intro v hv
          exact switchingDifferenceMatrix_apply_of_mem_private
            G p j i S₀ hv
      _ = ∑ j ∈ (Finset.univ : Finset I),
          if i = j then ((switchingPrivateNeighbors G p j S₀).card : ℝ)
            else 0 := by
          apply Finset.sum_congr rfl
          intro j _hj
          by_cases hij : i = j
          · subst j
            simp
          · simp [hij]
      _ = (switchingPrivateNeighbors G p i S₀).card := by simp
  · intro j _hj k _hk hjk
    exact switchingPrivateNeighbors_pairwise_disjoint G p S₀ hp hjk

/-- After removing the private blocks and the common nonneighbor reservoir,
the sum of switching row `i` is its degree difference minus its private-block
size. -/
lemma sum_switchingDifferenceMatrix_row_outside_private_common
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V)
    (hp : PairEndpointsDistinct p) (i : I) :
    let B := Finset.univ.biUnion fun j ↦
      switchingPrivateNeighbors G p j S₀
    let N := switchingCommonNonneighbors G p S₀
    let A := (Finset.univ : Finset V) \ (B ∪ N)
    (∑ v ∈ A, switchingDifferenceMatrix G p i v) =
      (FiniteES.vertexDegree G (p i).2 : ℝ) -
        (FiniteES.vertexDegree G (p i).1 : ℝ) -
          (switchingPrivateNeighbors G p i S₀).card := by
  classical
  let B := Finset.univ.biUnion fun j ↦
    switchingPrivateNeighbors G p j S₀
  let N := switchingCommonNonneighbors G p S₀
  let A := (Finset.univ : Finset V) \ (B ∪ N)
  have hBN : Disjoint B N := by
    rw [Finset.disjoint_left]
    intro v hvB hvN
    obtain ⟨j, _hj, hvj⟩ := Finset.mem_biUnion.mp hvB
    exact Finset.disjoint_left.mp
      (switchingCommonNonneighbors_disjoint_private G p S₀ j)
      hvN hvj
  have hsumB : (∑ v ∈ B, switchingDifferenceMatrix G p i v) =
      (switchingPrivateNeighbors G p i S₀).card := by
    simpa only [B] using sum_switchingDifferenceMatrix_privateUnion
      G p S₀ hp i
  have hsumN : (∑ v ∈ N, switchingDifferenceMatrix G p i v) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    exact switchingDifferenceMatrix_apply_of_mem_commonNonneighbors
      G p S₀ i hv
  have hsumBN : (∑ v ∈ B ∪ N, switchingDifferenceMatrix G p i v) =
      (switchingPrivateNeighbors G p i S₀).card := by
    rw [Finset.sum_union hBN, hsumB, hsumN, add_zero]
  have hsub : B ∪ N ⊆ (Finset.univ : Finset V) := Finset.subset_univ _
  have hpartition :
      (∑ v : V, switchingDifferenceMatrix G p i v) =
        (∑ v ∈ B ∪ N, switchingDifferenceMatrix G p i v) +
          ∑ v ∈ A, switchingDifferenceMatrix G p i v := by
    rw [show (Finset.univ : Finset V) = (B ∪ N) ∪ A by
      ext v
      by_cases hv : v ∈ B ∪ N <;> simp [A, hv]]
    rw [Finset.sum_union]
    rw [Finset.disjoint_left]
    intro v hv hvc
    exact (Finset.mem_sdiff.mp hvc).2 hv
  rw [sum_switchingDifferenceMatrix_row, hsumBN] at hpartition
  linarith

/-- The exact restricted-cube mean of switching row `i` after removing all
private blocks and the common nonneighbor reservoir. -/
lemma expectation_switchingDifferenceMatrix_mulVec_outside_private_common
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V)
    (hp : PairEndpointsDistinct p) (i : I) :
    let B := Finset.univ.biUnion fun j ↦
      switchingPrivateNeighbors G p j S₀
    let N := switchingCommonNonneighbors G p S₀
    let A := (Finset.univ : Finset V) \ (B ∪ N)
    Probability.expectation (1 / 2 : ℝ)
        (fun R : Finset (A : Set V) ↦
          (switchingDifferenceMatrix G p).mulVec
            (finsetIndicator (BoundedWindow.subtypeSubsetImage A R)) i) =
      ((FiniteES.vertexDegree G (p i).2 : ℝ) -
        (FiniteES.vertexDegree G (p i).1 : ℝ) -
          (switchingPrivateNeighbors G p i S₀).card) / 2 := by
  classical
  let B := Finset.univ.biUnion fun j ↦
    switchingPrivateNeighbors G p j S₀
  let N := switchingCommonNonneighbors G p S₀
  let A := (Finset.univ : Finset V) \ (B ∪ N)
  dsimp only
  rw [show (fun R : Finset (A : Set V) ↦
      (switchingDifferenceMatrix G p).mulVec
        (finsetIndicator (BoundedWindow.subtypeSubsetImage A R)) i) =
      (fun R ↦ ∑ v : (A : Set V),
        switchingDifferenceMatrix G p i v.1 * Probability.bit v R) by
    funext R
    exact switchingDifferenceMatrix_mulVec_subtypeSubsetImage G p A R i]
  rw [show (fun R : Finset (A : Set V) ↦ ∑ v : (A : Set V),
      switchingDifferenceMatrix G p i v.1 * Probability.bit v R) =
      (fun R ↦ ∑ v ∈ (Finset.univ : Finset (A : Set V)),
        switchingDifferenceMatrix G p i v.1 * Probability.bit v R) by
    rfl]
  have hterm (v : (A : Set V)) :
      Probability.expectation (1 / 2 : ℝ)
          (fun R : Finset (A : Set V) ↦
            switchingDifferenceMatrix G p i v.1 * Probability.bit v R) =
        switchingDifferenceMatrix G p i v.1 * (1 / 2 : ℝ) := by
    rw [Probability.expectation_smul,
      Probability.expectation_bit (p := (1 / 2 : ℝ))
        (by norm_num) (by norm_num)]
  rw [Probability.expectation_sum]
  simp_rw [hterm]
  rw [← Finset.sum_mul]
  have hsumSubtype :
      (∑ v : (A : Set V), switchingDifferenceMatrix G p i v.1) =
        ∑ v ∈ A, switchingDifferenceMatrix G p i v := by
    exact (Finset.sum_subtype A (fun _ ↦ Iff.rfl) _).symm
  rw [hsumSubtype,
    sum_switchingDifferenceMatrix_row_outside_private_common G p S₀ hp i]
  ring

/-- The integral value which the `i`th private-block cardinality must have
after fixing an outside assignment. -/
noncomputable def switchingRequiredPrivateCountInt
    {n : ℕ} {I : Type*} [Fintype I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (O : Finset (Fin n)) (label : I → ℤ) (i : I) : ℤ :=
  label i -
      (AKSGraph.degreeInto G (p i).2 (O.erase (p i).1) : ℤ) +
    (AKSGraph.degreeInto G (p i).1 (O.erase (p i).2) : ℤ)

/-- The required private-block cardinality, truncated at zero outside the
admissible first-exposure event. -/
noncomputable def switchingRequiredPrivateCount
    {n : ℕ} {I : Type*} [Fintype I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (O : Finset (Fin n)) (label : I → ℤ) (i : I) : ℕ :=
  (switchingRequiredPrivateCountInt G p O label i).toNat

lemma switchingRequiredPrivateCountInt_cast
    {n : ℕ} {I : Type*} [Fintype I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (O : Finset (Fin n)) (label : I → ℤ) (i : I) :
    (switchingRequiredPrivateCountInt G p O label i : ℝ) =
      (label i : ℝ) -
        (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) i := by
  rw [switchingDifferenceMatrix_mulVec]
  unfold switchingRequiredPrivateCountInt
  push_cast
  ring

lemma switchingRequiredPrivateCount_spec
    {n : ℕ} {I : Type*} [Fintype I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (O : Finset (Fin n)) (label : I → ℤ) (i : I)
    (hnonneg : 0 ≤ (label i : ℝ) -
      (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) i) :
    (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) i +
        switchingRequiredPrivateCount G p O label i = (label i : ℝ) := by
  have hcastInt := switchingRequiredPrivateCountInt_cast G p O label i
  have hIntNonneg : 0 ≤ switchingRequiredPrivateCountInt G p O label i := by
    exact_mod_cast (hcastInt.symm ▸ hnonneg)
  have hto := Int.toNat_of_nonneg hIntNonneg
  have hcastNat :
      ((switchingRequiredPrivateCount G p O label i : ℕ) : ℝ) =
        (switchingRequiredPrivateCountInt G p O label i : ℝ) := by
    exact_mod_cast hto
  rw [hcastNat, hcastInt]
  ring

lemma switchingRequiredPrivateCount_le
    {n : ℕ} {I : Type*} [Fintype I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (O : Finset (Fin n)) (label : I → ℤ) (i : I) (b : ℕ)
    (hnonneg : 0 ≤ (label i : ℝ) -
      (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) i)
    (hle : (label i : ℝ) -
      (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) i ≤ b) :
    switchingRequiredPrivateCount G p O label i ≤ b := by
  have hcastInt := switchingRequiredPrivateCountInt_cast G p O label i
  have hIntNonneg : 0 ≤ switchingRequiredPrivateCountInt G p O label i := by
    exact_mod_cast (hcastInt.symm ▸ hnonneg)
  have hto := Int.toNat_of_nonneg hIntNonneg
  have hcastNat :
      ((switchingRequiredPrivateCount G p O label i : ℕ) : ℝ) =
        (switchingRequiredPrivateCountInt G p O label i : ℝ) := by
    exact_mod_cast hto
  exact_mod_cast (hcastNat.trans hcastInt ▸ hle)

lemma natDist_le_of_abs_cast_sub_le {x y D : ℕ}
    (h : |(x : ℝ) - (y : ℝ)| ≤ D) :
    Nat.dist x y ≤ D := by
  by_cases hxy : x ≤ y
  · rw [Nat.dist_eq_sub_of_le hxy]
    have hxyR : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hxy
    have hreal : (y : ℝ) - (x : ℝ) ≤ D := by
      rw [abs_of_nonpos (sub_nonpos.mpr hxyR)] at h
      linarith
    exact_mod_cast hreal
  · have hyx : y ≤ x := Nat.le_of_lt (Nat.lt_of_not_ge hxy)
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hyx]
    have hyxR : (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast hyx
    have hreal : (x : ℝ) - (y : ℝ) ≤ D := by
      rw [abs_of_nonneg (sub_nonneg.mpr hyxR)] at h
      exact h
    exact_mod_cast hreal

lemma abs_natHalf_cast_sub_realHalf_le (b : ℕ) :
    |↑(b / 2) - (b : ℝ) / 2| ≤ (1 / 2 : ℝ) := by
  have hloNat : 2 * (b / 2) ≤ b := by omega
  have hhiNat : b ≤ 2 * (b / 2) + 1 := by omega
  have hlo : 2 * ((b / 2 : ℕ) : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast hloNat
  have hhi : (b : ℝ) ≤ 2 * ((b / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hhiNat
  rw [abs_of_nonpos (by linarith)]
  linarith

lemma abs_sub_natHalf_le_of_abs_sub_realHalf_le
    {x R : ℝ} {b : ℕ} (h : |x - (b : ℝ) / 2| ≤ R) :
    |x - ((b / 2 : ℕ) : ℝ)| ≤ R + 1 / 2 := by
  calc
    |x - ((b / 2 : ℕ) : ℝ)| =
        |(x - (b : ℝ) / 2) +
          ((b : ℝ) / 2 - ((b / 2 : ℕ) : ℝ))| := by ring_nf
    _ ≤ |x - (b : ℝ) / 2| +
        |(b : ℝ) / 2 - ((b / 2 : ℕ) : ℝ)| := abs_add_le _ _
    _ ≤ R + 1 / 2 := by
      gcongr
      simpa only [abs_sub_comm] using abs_natHalf_cast_sub_realHalf_le b

lemma switchingRequiredPrivateCount_dist_half_le
    {n : ℕ} {I : Type*} [Fintype I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (O : Finset (Fin n)) (label : I → ℤ) (i : I) (b D : ℕ)
    (hnonneg : 0 ≤ (label i : ℝ) -
      (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) i)
    (hcenter : |(label i : ℝ) -
        (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) i -
          ((b / 2 : ℕ) : ℝ)| ≤ D) :
    Nat.dist (switchingRequiredPrivateCount G p O label i) (b / 2) ≤ D := by
  apply natDist_le_of_abs_cast_sub_le
  have hspec := switchingRequiredPrivateCount_spec G p O label i hnonneg
  rw [show ((switchingRequiredPrivateCount G p O label i : ℕ) : ℝ) =
      (label i : ℝ) -
        (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) i by
    linarith]
  exact hcenter

/-- Triangle-inequality bridge from a label close to half the endpoint-degree
difference and a first-exposure row close to its exact mean. -/
lemma abs_requiredTarget_sub_half_le
    {ell : ℤ} {row degreeDiff blockHalf labelRadius rowRadius : ℝ}
    (hlabel : |(ell : ℝ) - degreeDiff / 2| ≤ labelRadius)
    (hrow : |row - (degreeDiff / 2 - blockHalf)| ≤ rowRadius) :
    |(ell : ℝ) - row - blockHalf| ≤ labelRadius + rowRadius := by
  have hsum := abs_add_le ((ell : ℝ) - degreeDiff / 2)
    (degreeDiff / 2 - blockHalf - row)
  rw [show (ell : ℝ) - row - blockHalf =
      ((ell : ℝ) - degreeDiff / 2) +
        (degreeDiff / 2 - blockHalf - row) by ring]
  calc
    |(ell : ℝ) - degreeDiff / 2 +
        (degreeDiff / 2 - blockHalf - row)| ≤
        |(ell : ℝ) - degreeDiff / 2| +
          |degreeDiff / 2 - blockHalf - row| := hsum
    _ ≤ labelRadius + rowRadius := by
      gcongr
      simpa only [abs_sub_comm] using hrow

/-- A centered required value is an admissible private-block cardinality and
solves its switching equation exactly. -/
lemma switchingRequiredPrivateCount_admissible_of_centered
    {n : ℕ} {I : Type*} [Fintype I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (O : Finset (Fin n)) (label : I → ℤ) (i : I) (b D : ℕ)
    (hD : D ≤ b / 2)
    (hcenter : |(label i : ℝ) -
        (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) i -
          ((b / 2 : ℕ) : ℝ)| ≤ D) :
    switchingRequiredPrivateCount G p O label i ≤ b ∧
      Nat.dist (switchingRequiredPrivateCount G p O label i) (b / 2) ≤ D ∧
      (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) i +
          switchingRequiredPrivateCount G p O label i = (label i : ℝ) := by
  let x := (label i : ℝ) -
    (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) i
  have hhalfNonneg : 0 ≤ ((b / 2 : ℕ) : ℝ) := by positivity
  have hDR : (D : ℝ) ≤ ((b / 2 : ℕ) : ℝ) := by exact_mod_cast hD
  have hsumNat : b / 2 + b / 2 ≤ b := by omega
  have hsumR : ((b / 2 : ℕ) : ℝ) + (b / 2 : ℕ) ≤ b := by
    exact_mod_cast hsumNat
  have habs := abs_le.mp hcenter
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    linarith
  have hxb : x ≤ b := by
    dsimp only [x]
    linarith
  refine ⟨switchingRequiredPrivateCount_le G p O label i b hx0 hxb,
    switchingRequiredPrivateCount_dist_half_le G p O label i b D hx0 hcenter,
    switchingRequiredPrivateCount_spec G p O label i hx0⟩

/-- A switching row satisfying its first-exposure deviation bound yields a
required private-block count close to the integer midpoint. -/
lemma requiredPrivateCount_centered_of_row_good
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (S₀ A O : Finset (Fin n)) (hp : PairEndpointsDistinct p)
    (hA : A = (Finset.univ : Finset (Fin n)) \
      ((Finset.univ.biUnion fun j ↦
        switchingPrivateNeighbors G p j S₀) ∪
          switchingCommonNonneighbors G p S₀))
    (label : I → ℤ) (i : I) (labelRadius rowRadius : ℝ)
    (hlabel : |(label i : ℝ) -
        ((FiniteES.vertexDegree G (p i).2 : ℝ) -
          (FiniteES.vertexDegree G (p i).1 : ℝ)) / 2| ≤ labelRadius)
    (hrow : |(switchingDifferenceMatrix G p).mulVec
          (finsetIndicator O) i -
        Probability.expectation (1 / 2 : ℝ)
          (fun R : Finset (A : Set (Fin n)) ↦
            (switchingDifferenceMatrix G p).mulVec
              (finsetIndicator (BoundedWindow.subtypeSubsetImage A R)) i)| ≤
        rowRadius) :
    |(label i : ℝ) -
        (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) i -
          (((switchingPrivateNeighbors G p i S₀).card / 2 : ℕ) : ℝ)| ≤
      labelRadius + rowRadius + 1 / 2 := by
  subst A
  have hmean :=
    expectation_switchingDifferenceMatrix_mulVec_outside_private_common
      G p S₀ hp i
  dsimp only at hmean
  rw [hmean] at hrow
  have hrow' : |(switchingDifferenceMatrix G p).mulVec
        (finsetIndicator O) i -
      (((FiniteES.vertexDegree G (p i).2 : ℝ) -
        (FiniteES.vertexDegree G (p i).1 : ℝ)) / 2 -
          ((switchingPrivateNeighbors G p i S₀).card : ℝ) / 2)| ≤
      rowRadius := by
    convert hrow using 1 <;> ring_nf
  have hreal := abs_requiredTarget_sub_half_le hlabel hrow'
  exact abs_sub_natHalf_le_of_abs_sub_realHalf_le hreal

/-- Coordinates exposed before the private blocks and common-nonneighbor
reservoir are filled. -/
noncomputable def switchingFirstExposureDomain
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V) : Finset V :=
  (Finset.univ : Finset V) \
    ((Finset.univ.biUnion fun i ↦ switchingPrivateNeighbors G p i S₀) ∪
      switchingCommonNonneighbors G p S₀)

noncomputable def switchingLeftEndpoints
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] (p : I → V × V) : Finset V :=
  Finset.univ.image fun i ↦ (p i).1

noncomputable def switchingRightEndpoints
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] (p : I → V × V) : Finset V :=
  Finset.univ.image fun i ↦ (p i).2

lemma switchingLeftEndpoints_union_right
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] (p : I → V × V) :
    switchingLeftEndpoints p ∪ switchingRightEndpoints p =
      switchingEndpointFinset p := by
  rfl

lemma switchingLeftEndpoints_disjoint_right
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I] (p : I → V × V)
    (hp : PairEndpointsDistinct p) :
    Disjoint (switchingLeftEndpoints p) (switchingRightEndpoints p) := by
  rw [Finset.disjoint_left]
  intro v hvL hvR
  obtain ⟨i, _hi, hiv⟩ := Finset.mem_image.mp hvL
  obtain ⟨j, _hj, hjv⟩ := Finset.mem_image.mp hvR
  have heq : switchingEndpointMap p (Sum.inl i) =
      switchingEndpointMap p (Sum.inr j) := by
    simpa only [switchingEndpointMap, hiv, hjv]
  have := hp heq
  cases this

lemma switchingEndpointFinset_subset_firstExposureDomain
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V) :
    switchingEndpointFinset p ⊆ switchingFirstExposureDomain G p S₀ := by
  intro v hv
  rw [switchingFirstExposureDomain, Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hvUnion
  rcases Finset.mem_union.mp hvUnion with hvPrivate | hvN
  · exact Finset.disjoint_left.mp
      (switchingEndpointFinset_disjoint_privateUnion G p S₀) hv hvPrivate
  · exact (mem_nonneighborsOf.mp hvN).2.1 hv

lemma switchingLeftEndpoints_subset_firstExposureDomain
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V) :
    switchingLeftEndpoints p ⊆ switchingFirstExposureDomain G p S₀ := by
  exact fun _ hv ↦ switchingEndpointFinset_subset_firstExposureDomain
    G p S₀ (by
      rw [← switchingLeftEndpoints_union_right p]
      exact Finset.mem_union_left _ hv)

lemma switchingRightEndpoints_subset_firstExposureDomain
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V) :
    switchingRightEndpoints p ⊆ switchingFirstExposureDomain G p S₀ := by
  exact fun _ hv ↦ switchingEndpointFinset_subset_firstExposureDomain
    G p S₀ (by
      rw [← switchingLeftEndpoints_union_right p]
      exact Finset.mem_union_right _ hv)

lemma two_mul_card_le_switchingFirstExposureDomain
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V)
    (hp : PairEndpointsDistinct p) :
    2 * Fintype.card I ≤ (switchingFirstExposureDomain G p S₀).card := by
  rw [← card_switchingEndpointFinset_eq p hp]
  exact Finset.card_le_card
    (switchingEndpointFinset_subset_firstExposureDomain G p S₀)

/-- The first-exposure event in the lower half of KSSS Lemma 13.4: all
switches have the correct orientation, the mean polynomial is typical, and
every switching row is typical. -/
noncomputable def switchingFirstExposureGood
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V)
    (X : Finset V → ℝ) (tMean tRow : ℝ) : Finset (Finset V) :=
  let A := switchingFirstExposureDomain G p S₀
  A.powerset.filter fun O ↦
    switchingLeftEndpoints p ⊆ O ∧
      Disjoint O (switchingRightEndpoints p) ∧
      |X O - Probability.expectation (1 / 2 : ℝ)
        (fun R : Finset (A : Set V) ↦
          X (BoundedWindow.subtypeSubsetImage A R))| < tMean ∧
      ∀ i,
        |(switchingDifferenceMatrix G p).mulVec (finsetIndicator O) i -
          Probability.expectation (1 / 2 : ℝ)
            (fun R : Finset (A : Set V) ↦
              (switchingDifferenceMatrix G p).mulVec
                (finsetIndicator (BoundedWindow.subtypeSubsetImage A R)) i)| <
          tRow

/-- Exact first-exposure cardinality lower bound, including the `2s`
forced endpoint orientations. -/
lemma card_switchingFirstExposureGood_ge
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V)
    (hp : PairEndpointsDistinct p)
    (X : Finset V → ℝ) (tMean tRow : ℝ)
    (htMean : 0 < tMean) (htRow : 0 < tRow) :
    (((2 : ℕ) ^ ((switchingFirstExposureDomain G p S₀).card -
          2 * Fintype.card I) : ℕ) : ℝ) -
        (2 : ℝ) ^ (switchingFirstExposureDomain G p S₀).card *
          (Probability.variance (1 / 2 : ℝ)
              (fun R : Finset (switchingFirstExposureDomain G p S₀ : Set V) ↦
                X (BoundedWindow.subtypeSubsetImage
                  (switchingFirstExposureDomain G p S₀) R)) / tMean ^ 2 +
            (Fintype.card I : ℝ) *
              ((((switchingFirstExposureDomain G p S₀).card : ℝ) / 4) /
                tRow ^ 2)) ≤
      (switchingFirstExposureGood G p S₀ X tMean tRow).card := by
  have hbase := card_switching_firstExposure_good_ge G p
    (switchingFirstExposureDomain G p S₀)
    (switchingLeftEndpoints p) (switchingRightEndpoints p)
    (switchingLeftEndpoints_subset_firstExposureDomain G p S₀)
    (switchingRightEndpoints_subset_firstExposureDomain G p S₀)
    (switchingLeftEndpoints_disjoint_right p hp) X tMean tRow htMean htRow
  rw [switchingLeftEndpoints_union_right,
    card_switchingEndpointFinset_eq p hp] at hbase
  simpa only [switchingFirstExposureGood] using hbase

/-- The normalized Chebyshev/union-bound loss in the first exposure. -/
noncomputable def switchingFirstExposureError
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V)
    (X : Finset V → ℝ) (tMean tRow : ℝ) : ℝ :=
  Probability.variance (1 / 2 : ℝ)
      (fun R : Finset (switchingFirstExposureDomain G p S₀ : Set V) ↦
        X (BoundedWindow.subtypeSubsetImage
          (switchingFirstExposureDomain G p S₀) R)) / tMean ^ 2 +
    (Fintype.card I : ℝ) *
      ((((switchingFirstExposureDomain G p S₀).card : ℝ) / 4) /
        tRow ^ 2)

/-- The surviving normalized first-exposure rate after the `2|I|` forced
endpoint bits and all Chebyshev losses. -/
noncomputable def switchingFirstExposureRate
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V)
    (X : Finset V → ℝ) (tMean tRow : ℝ) : ℝ :=
  ((2 : ℝ) ^ (2 * Fintype.card I))⁻¹ -
    switchingFirstExposureError G p S₀ X tMean tRow

lemma card_switchingFirstExposureDomain
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (S₀ : Finset (Fin n)) :
    (switchingFirstExposureDomain G p S₀).card =
      n - ((Finset.univ.biUnion fun i ↦ switchingPrivateNeighbors G p i S₀) ∪
        switchingCommonNonneighbors G p S₀).card := by
  rw [switchingFirstExposureDomain, Finset.card_sdiff_of_subset]
  · simp
  · exact Finset.subset_univ _

/-- Multiplicative form of the first-exposure count. -/
lemma card_switchingFirstExposureGood_ge_rate
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V)
    (hp : PairEndpointsDistinct p)
    (X : Finset V → ℝ) (tMean tRow : ℝ)
    (htMean : 0 < tMean) (htRow : 0 < tRow)
    (hroom : 2 * Fintype.card I ≤
      (switchingFirstExposureDomain G p S₀).card) :
    switchingFirstExposureRate G p S₀ X tMean tRow *
        (2 : ℝ) ^ (switchingFirstExposureDomain G p S₀).card ≤
      (switchingFirstExposureGood G p S₀ X tMean tRow).card := by
  have hbase := card_switchingFirstExposureGood_ge
    G p S₀ hp X tMean tRow htMean htRow
  have hpow :
      (2 : ℝ) ^ ((switchingFirstExposureDomain G p S₀).card -
          2 * Fintype.card I) =
        (2 : ℝ) ^ (switchingFirstExposureDomain G p S₀).card *
          ((2 : ℝ) ^ (2 * Fintype.card I))⁻¹ :=
    pow_sub₀ (2 : ℝ) (by norm_num) hroom
  norm_num [Nat.cast_pow] at hbase
  rw [hpow] at hbase
  calc
    switchingFirstExposureRate G p S₀ X tMean tRow *
        (2 : ℝ) ^ (switchingFirstExposureDomain G p S₀).card =
      (2 : ℝ) ^ (switchingFirstExposureDomain G p S₀).card *
          ((2 : ℝ) ^ (2 * Fintype.card I))⁻¹ -
        (2 : ℝ) ^ (switchingFirstExposureDomain G p S₀).card *
          switchingFirstExposureError G p S₀ X tMean tRow := by
        unfold switchingFirstExposureRate
        ring
    _ ≤ _ := by
      unfold switchingFirstExposureError
      linarith

@[simp] lemma mem_switchingFirstExposureGood
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    {G : SimpleGraph V} {p : I → V × V} {S₀ : Finset V}
    {X : Finset V → ℝ} {tMean tRow : ℝ} {O : Finset V} :
    O ∈ switchingFirstExposureGood G p S₀ X tMean tRow ↔
      O ⊆ switchingFirstExposureDomain G p S₀ ∧
      switchingLeftEndpoints p ⊆ O ∧
      Disjoint O (switchingRightEndpoints p) ∧
      |X O - Probability.expectation (1 / 2 : ℝ)
        (fun R : Finset (switchingFirstExposureDomain G p S₀ : Set V) ↦
          X (BoundedWindow.subtypeSubsetImage
            (switchingFirstExposureDomain G p S₀) R))| < tMean ∧
      ∀ i,
        |(switchingDifferenceMatrix G p).mulVec (finsetIndicator O) i -
          Probability.expectation (1 / 2 : ℝ)
            (fun R : Finset (switchingFirstExposureDomain G p S₀ : Set V) ↦
              (switchingDifferenceMatrix G p).mulVec
                (finsetIndicator (BoundedWindow.subtypeSubsetImage
                  (switchingFirstExposureDomain G p S₀) R)) i)| < tRow := by
  simp [switchingFirstExposureGood]

/-- Every good first exposure avoids the unexposed blocks and reservoir and
orients every switch correctly. -/
lemma switchingFirstExposureGood_core_properties
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V)
    (X : Finset V → ℝ) (tMean tRow : ℝ)
    {O : Finset V} (hO : O ∈ switchingFirstExposureGood G p S₀ X tMean tRow) :
    Disjoint O (Finset.univ.biUnion fun i ↦
        switchingPrivateNeighbors G p i S₀) ∧
      Disjoint O (switchingCommonNonneighbors G p S₀) ∧
      (∀ i, (p i).1 ∈ O) ∧ ∀ i, (p i).2 ∉ O := by
  have hO' := mem_switchingFirstExposureGood.mp hO
  have hsub := hO'.1
  have hblocks : Disjoint O (Finset.univ.biUnion fun i ↦
      switchingPrivateNeighbors G p i S₀) := by
    rw [Finset.disjoint_left]
    intro v hvO hvB
    have hvA := hsub hvO
    exact (Finset.mem_sdiff.mp hvA).2 (Finset.mem_union_left _ hvB)
  have hN : Disjoint O (switchingCommonNonneighbors G p S₀) := by
    rw [Finset.disjoint_left]
    intro v hvO hvN
    have hvA := hsub hvO
    exact (Finset.mem_sdiff.mp hvA).2 (Finset.mem_union_right _ hvN)
  refine ⟨hblocks, hN, ?_, ?_⟩
  · intro i
    exact hO'.2.1 (by simp [switchingLeftEndpoints])
  · intro i hi
    exact Finset.disjoint_left.mp hO'.2.2.1 hi
      (by simp [switchingRightEndpoints])

/-- On every good first exposure, the canonical required counts are valid,
near-central, and solve all switching equations. -/
lemma switchingFirstExposureGood_privateCounts
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (S₀ : Finset (Fin n)) (hp : PairEndpointsDistinct p)
    (X : Finset (Fin n) → ℝ) (tMean tRow labelRadius : ℝ)
    (D : ℕ) (label : I → ℤ)
    (hlabel : ∀ i, |(label i : ℝ) -
        ((FiniteES.vertexDegree G (p i).2 : ℝ) -
          (FiniteES.vertexDegree G (p i).1 : ℝ)) / 2| ≤ labelRadius)
    (hRadius : labelRadius + tRow + 1 / 2 ≤ (D : ℝ))
    (hD : ∀ i, D ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    {O : Finset (Fin n)}
    (hO : O ∈ switchingFirstExposureGood G p S₀ X tMean tRow) :
    ∀ i,
      switchingRequiredPrivateCount G p O label i ≤
          (switchingPrivateNeighbors G p i S₀).card ∧
      Nat.dist (switchingRequiredPrivateCount G p O label i)
          ((switchingPrivateNeighbors G p i S₀).card / 2) ≤ D ∧
      (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) i +
          switchingRequiredPrivateCount G p O label i = (label i : ℝ) := by
  intro i
  have hO' := mem_switchingFirstExposureGood.mp hO
  have hcenter := requiredPrivateCount_centered_of_row_good
    G p S₀ (switchingFirstExposureDomain G p S₀) O hp rfl
      label i labelRadius tRow (hlabel i) (le_of_lt (hO'.2.2.2.2 i))
  have hcenterD : |(label i : ℝ) -
        (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) i -
          (((switchingPrivateNeighbors G p i S₀).card / 2 : ℕ) : ℝ)| ≤
      D := hcenter.trans hRadius
  exact switchingRequiredPrivateCount_admissible_of_centered
    G p O label i (switchingPrivateNeighbors G p i S₀).card D
      (hD i) hcenterD

/-- Image of a finite subset under an equivalence. -/
def equivFinsetImage {α β : Type*} [DecidableEq β]
    (e : α ≃ β) (S : Finset α) : Finset β :=
  S.map e.toEmbedding

/-- Preimage of a finite set under an equivalence. -/
def equivFinsetPreimage {α β : Type*} [Fintype α]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (S : Finset β) : Finset α :=
  Finset.univ.filter fun i ↦ e i ∈ S

@[simp] lemma mem_equivFinsetPreimage {α β : Type*} [Fintype α]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (S : Finset β) (i : α) :
    i ∈ equivFinsetPreimage e S ↔ e i ∈ S := by
  simp [equivFinsetPreimage]

lemma equivFinsetImage_preimage {α β : Type*} [Fintype α]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (S : Finset β) :
    equivFinsetImage e (equivFinsetPreimage e S) = S := by
  ext v
  simp [equivFinsetImage, equivFinsetPreimage]

lemma card_equivFinsetPreimage {α β : Type*} [Fintype α]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (S : Finset β) :
    (equivFinsetPreimage e S).card = S.card := by
  rw [← Finset.card_map e.toEmbedding]
  change (equivFinsetImage e (equivFinsetPreimage e S)).card = S.card
  rw [equivFinsetImage_preimage]

/-- The elements of `B` regarded as members of a containing finite set
`A`. -/
noncomputable def finsetSubtypePreimage {V : Type*} [DecidableEq V]
    (A B : Finset V) : Finset (A : Set V) :=
  B.preimage Subtype.val Subtype.val_injective.injOn

@[simp] lemma mem_finsetSubtypePreimage {V : Type*} [DecidableEq V]
    (A B : Finset V) (v : (A : Set V)) :
    v ∈ finsetSubtypePreimage A B ↔ v.1 ∈ B := by
  simp [finsetSubtypePreimage]

lemma card_finsetSubtypePreimage_of_subset {V : Type*} [DecidableEq V]
    {A B : Finset V} (hBA : B ⊆ A) :
    (finsetSubtypePreimage A B).card = B.card := by
  let emb : (A : Set V) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : (finsetSubtypePreimage A B).map emb = B := by
    ext v
    simp only [Finset.mem_map, mem_finsetSubtypePreimage]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hv
      exact ⟨⟨v, hBA hv⟩, hv, rfl⟩
  calc
    (finsetSubtypePreimage A B).card =
        ((finsetSubtypePreimage A B).map emb).card :=
      (Finset.card_map emb).symm
    _ = B.card := congrArg Finset.card hmap

lemma pairwiseDisjoint_equivFinsetPreimage
    {α β ι : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (W : ι → Finset β)
    (hW : Set.PairwiseDisjoint Set.univ W) :
    Set.PairwiseDisjoint Set.univ (fun i ↦ equivFinsetPreimage e (W i)) := by
  intro i _hi j _hj hij
  change Disjoint (equivFinsetPreimage e (W i))
    (equivFinsetPreimage e (W j))
  rw [Finset.disjoint_left]
  intro x hxi hxj
  exact Finset.disjoint_left.mp (hW (Set.mem_univ i) (Set.mem_univ j) hij)
    (by simpa using hxi) (by simpa using hxj)

/-- Canonical finite reindexing of the union of a family of blocks. -/
noncomputable def blockUnionVertexEquiv
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] (W : ι → Finset V) :
    Fin (Finset.univ.biUnion W).card ≃
      ↑(Finset.univ.biUnion W : Finset V) := by
  simpa only [Fintype.card_coe] using
    (Fintype.equivFin ↑(Finset.univ.biUnion W : Finset V)).symm

/-- A block transported to the canonical finite indexing of the union. -/
noncomputable def reindexedBlock
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] (W : ι → Finset V) (i : ι) :
    Finset (Fin (Finset.univ.biUnion W).card) :=
  equivFinsetPreimage (blockUnionVertexEquiv W)
    (finsetSubtypePreimage (Finset.univ.biUnion W) (W i))

lemma card_reindexedBlock
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] (W : ι → Finset V) (i : ι) :
    (reindexedBlock W i).card = (W i).card := by
  rw [reindexedBlock, card_equivFinsetPreimage]
  apply card_finsetSubtypePreimage_of_subset
  exact Finset.subset_biUnion_of_mem W (Finset.mem_univ i)

lemma reindexedBlock_pairwiseDisjoint
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [DecidableEq ι]
    (W : ι → Finset V) (hW : Set.PairwiseDisjoint Set.univ W) :
    Set.PairwiseDisjoint Set.univ (reindexedBlock W) := by
  apply pairwiseDisjoint_equivFinsetPreimage
  intro i _hi j _hj hij
  change Disjoint
    (finsetSubtypePreimage (Finset.univ.biUnion W) (W i))
    (finsetSubtypePreimage (Finset.univ.biUnion W) (W j))
  rw [Finset.disjoint_left]
  intro v hvi hvj
  have hvi' : v.1 ∈ W i :=
    (mem_finsetSubtypePreimage _ _ v).mp hvi
  have hvj' : v.1 ∈ W j :=
    (mem_finsetSubtypePreimage _ _ v).mp hvj
  exact Finset.disjoint_left.mp (hW (Set.mem_univ i) (Set.mem_univ j) hij)
    hvi' hvj'

lemma biUnion_reindexedBlock_eq_univ
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] [DecidableEq ι] (W : ι → Finset V) :
    Finset.univ.biUnion (reindexedBlock W) = Finset.univ := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro _h
    trivial
  · intro _h
    let v := blockUnionVertexEquiv W x
    have hv : v.1 ∈ Finset.univ.biUnion W := v.2
    obtain ⟨i, _hi, hvi⟩ := Finset.mem_biUnion.mp hv
    refine ⟨i, ?_⟩
    rw [reindexedBlock, mem_equivFinsetPreimage]
    exact (mem_finsetSubtypePreimage _ _ _).mpr hvi

/-- Forget the canonical reindexing and view a subset of the block union in
the original ambient vertex type. -/
noncomputable def reindexedSubsetImage
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] (W : ι → Finset V)
    (S : Finset (Fin (Finset.univ.biUnion W).card)) : Finset V :=
  BoundedWindow.subtypeSubsetImage (Finset.univ.biUnion W)
    (equivFinsetImage (blockUnionVertexEquiv W) S)

lemma reindexedSubsetImage_subset
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] (W : ι → Finset V)
    (S : Finset (Fin (Finset.univ.biUnion W).card)) :
    reindexedSubsetImage W S ⊆ Finset.univ.biUnion W :=
  BoundedWindow.subtypeSubsetImage_subset _ _

lemma reindexedSubsetImage_injective
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] (W : ι → Finset V) :
    Function.Injective (reindexedSubsetImage W) := by
  intro S T hST
  ext x
  have hx := congrArg
    (fun U : Finset V ↦ (blockUnionVertexEquiv W x).1 ∈ U) hST
  simpa [reindexedSubsetImage, BoundedWindow.subtypeSubsetImage,
    equivFinsetImage] using hx

lemma reindexedSubsetImage_inter_block
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] (W : ι → Finset V)
    (S : Finset (Fin (Finset.univ.biUnion W).card)) (i : ι) :
    (reindexedSubsetImage W S ∩ W i).card =
      (S ∩ reindexedBlock W i).card := by
  let e := blockUnionVertexEquiv W
  symm
  apply Finset.card_bij (fun x _hx ↦ (e x).1)
  · intro x hx
    have hx' := Finset.mem_inter.mp hx
    apply Finset.mem_inter.mpr
    constructor
    · simp only [reindexedSubsetImage, BoundedWindow.subtypeSubsetImage,
        equivFinsetImage, Finset.mem_image, Finset.mem_map]
      exact ⟨e x, ⟨x, hx'.1, rfl⟩, rfl⟩
    · have hxBlock : e x ∈ finsetSubtypePreimage
          (Finset.univ.biUnion W) (W i) := by
        simpa only [e, reindexedBlock, mem_equivFinsetPreimage] using hx'.2
      exact (mem_finsetSubtypePreimage _ _ _).mp hxBlock
  · intro x _hx y _hy hxy
    exact e.injective (Subtype.ext hxy)
  · intro v hv
    have hv' := Finset.mem_inter.mp hv
    simp only [reindexedSubsetImage, BoundedWindow.subtypeSubsetImage,
      equivFinsetImage, Finset.mem_image, Finset.mem_map] at hv'
    obtain ⟨w, ⟨x, hxS, hxw⟩, hwv⟩ := hv'.1
    subst w
    have hxv : (e x).1 = v := by simpa using hwv
    have hxBlock : x ∈ reindexedBlock W i := by
      rw [reindexedBlock, mem_equivFinsetPreimage]
      apply (mem_finsetSubtypePreimage _ _ _).mpr
      rw [hxv]
      exact hv'.2
    exact ⟨x, Finset.mem_inter.mpr ⟨hxS, hxBlock⟩, hxv⟩

/-- Induced-edge counts are invariant under an equivalence used to pull a
graph back to the source type. -/
lemma inducedEdges_comap_equiv {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (e : α ≃ β) (S : Finset α) :
    inducedEdges (G.comap e) S =
      inducedEdges G (equivFinsetImage e S) := by
  let H := G.comap e
  let sα : Set α := S
  let sβ : Set β := e '' sα
  let ev : sα ≃ sβ := Equiv.Set.image e sα e.injective
  let iso : H.induce sα ≃g G.induce sβ :=
    { toEquiv := ev
      map_rel_iff' := by intro x y; rfl }
  have hU : (↑(equivFinsetImage e S) : Set β) = sβ := by
    ext x
    simp [equivFinsetImage, sβ, sα]
  let iso' : H.induce sα ≃g
      G.induce (↑(equivFinsetImage e S) : Set β) := by
    rw [hU]
    exact iso
  rw [inducedEdges_eq_card_edgeFinset_induce,
    inducedEdges_eq_card_edgeFinset_induce]
  exact iso'.card_edgeFinset_eq

/-- A perturbed edge polynomial is invariant under pulling the graph and
linear coefficients back along an equivalence. -/
lemma perturbedEdgePolynomial_comap_equiv
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (e : α ≃ β) (e₀ : ℝ) (c : β → ℝ) (S : Finset α) :
    Probability.perturbedEdgePolynomial (G.comap e) e₀ (fun i ↦ c (e i)) S =
      Probability.perturbedEdgePolynomial G e₀ c (equivFinsetImage e S) := by
  rw [Probability.perturbedEdgePolynomial,
    Probability.perturbedEdgePolynomial,
    Probability.edgePolynomial_eq_inducedEdgeCount,
    Probability.edgePolynomial_eq_inducedEdgeCount]
  rw [BoundedWindow.probability_inducedEdgeCount_eq_inducedEdges,
    BoundedWindow.probability_inducedEdgeCount_eq_inducedEdges,
    inducedEdges_comap_equiv]
  congr 1
  calc
    (∑ i : α, c (e i) * Probability.bit i S) = ∑ i ∈ S, c (e i) := by
      simp only [Probability.bit]
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.univ_inter]
    _ = ∑ v ∈ equivFinsetImage e S, c v := by
      rw [equivFinsetImage]
      exact (Finset.sum_map S e.toEmbedding c).symm
    _ = ∑ v : β, c v * Probability.bit v (equivFinsetImage e S) := by
      simp only [Probability.bit]
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.univ_inter]

lemma perturbedEdgePolynomial_reindexedSubsetImage
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] (W : ι → Finset V)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e₀ : ℝ) (c : V → ℝ)
    (S : Finset (Fin (Finset.univ.biUnion W).card)) :
    Probability.perturbedEdgePolynomial
        ((G.induce (Finset.univ.biUnion W : Set V)).comap
          (blockUnionVertexEquiv W)) e₀
        (fun i ↦ c (blockUnionVertexEquiv W i).1) S =
      Probability.perturbedEdgePolynomial G e₀ c
        (reindexedSubsetImage W S) := by
  have hcomap := perturbedEdgePolynomial_comap_equiv
    (G.induce (Finset.univ.biUnion W : Set V))
    (blockUnionVertexEquiv W) e₀ (fun v ↦ c v.1) S
  rw [show Probability.perturbedEdgePolynomial
        ((G.induce (Finset.univ.biUnion W : Set V)).comap
          (blockUnionVertexEquiv W)) e₀
        (fun i ↦ c (blockUnionVertexEquiv W i).1) S =
      Probability.perturbedEdgePolynomial (G.induce
        (Finset.univ.biUnion W : Set V)) e₀ (fun v ↦ c v.1)
        (equivFinsetImage (blockUnionVertexEquiv W) S) by exact hcomap]
  exact BoundedWindow.perturbedEdgePolynomial_induce_subtypeSubsetImage
    G (Finset.univ.biUnion W) e₀ c
      (equivFinsetImage (blockUnionVertexEquiv W) S)

/-- Assemble a subset of the reindexed block union with a fixed disjoint
outside assignment. -/
noncomputable def fixedOutsideReindexedSliceMap
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] (W : ι → Finset V) (O : Finset V)
    (S : Finset (Fin (Finset.univ.biUnion W).card)) : Finset V :=
  O ∪ reindexedSubsetImage W S

lemma fixedOutsideReindexedSliceMap_sdiff
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] (W : ι → Finset V) (O : Finset V)
    (hO : Disjoint O (Finset.univ.biUnion W))
    (S : Finset (Fin (Finset.univ.biUnion W).card)) :
    fixedOutsideReindexedSliceMap W O S \ Finset.univ.biUnion W = O := by
  ext v
  have hB := reindexedSubsetImage_subset W S
  simp only [fixedOutsideReindexedSliceMap, Finset.mem_sdiff,
    Finset.mem_union]
  constructor
  · rintro ⟨hvO | hvB, _hvA⟩
    · exact hvO
    · exact False.elim (_hvA (hB hvB))
  · intro hvO
    exact ⟨Or.inl hvO, fun hvA ↦ Finset.disjoint_left.mp hO hvO hvA⟩

lemma fixedOutsideReindexedSliceMap_inter_block
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] (W : ι → Finset V) (O : Finset V)
    (hO : Disjoint O (Finset.univ.biUnion W))
    (S : Finset (Fin (Finset.univ.biUnion W).card)) (i : ι) :
    (fixedOutsideReindexedSliceMap W O S ∩ W i).card =
      (S ∩ reindexedBlock W i).card := by
  rw [← reindexedSubsetImage_inter_block W S i]
  congr 1
  ext v
  simp only [fixedOutsideReindexedSliceMap, Finset.mem_inter, Finset.mem_union]
  constructor
  · rintro ⟨hvO | hvB, hvWi⟩
    · have hvA : v ∈ Finset.univ.biUnion W :=
        Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hvWi⟩
      exact False.elim (Finset.disjoint_left.mp hO hvO hvA)
    · exact ⟨hvB, hvWi⟩
  · rintro ⟨hvB, hvWi⟩
    exact ⟨Or.inr hvB, hvWi⟩

lemma fixedOutsideReindexedSliceMap_injective
    {V ι : Type*} [Fintype V] [DecidableEq V]
    [Fintype ι] (W : ι → Finset V) (O : Finset V)
    (hO : Disjoint O (Finset.univ.biUnion W)) :
    Function.Injective (fixedOutsideReindexedSliceMap W O) := by
  intro S T hST
  apply reindexedSubsetImage_injective W
  have hB (U : Finset (Fin (Finset.univ.biUnion W).card)) :
      fixedOutsideReindexedSliceMap W O U ∩ Finset.univ.biUnion W =
        reindexedSubsetImage W U := by
    ext v
    have hsub := reindexedSubsetImage_subset W U
    simp only [fixedOutsideReindexedSliceMap, Finset.mem_inter,
      Finset.mem_union]
    constructor
    · rintro ⟨hvO | hvB, hvA⟩
      · exact False.elim (Finset.disjoint_left.mp hO hvO hvA)
      · exact hvB
    · intro hvB
      exact ⟨Or.inr hvB, hsub hvB⟩
  rw [← hB S, ← hB T, hST]

/-- Lemma 13.1's common-nonneighbor conclusion and its linear lower bound
for `S₀` give the corresponding linear lower bound for the switching
reservoir. -/
lemma switchingCommonNonneighbors_card_ge_linear
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph (Fin n)) (S S₀ : Finset (Fin n))
    (p : I → Fin n × Fin n) (δ base : ℝ) (D : ℕ)
    (hδ : 0 ≤ δ)
    (hcommon : HasLargeCommonNonneighbors G S S₀ δ D)
    (hI : 2 * Fintype.card I ≤ D)
    (hp : ∀ j, p j ∈ S ×ˢ S)
    (hS₀ : base * n ≤ (S₀.card : ℝ)) :
    δ * base * n ≤
      ((switchingCommonNonneighbors G p S₀).card : ℝ) := by
  calc
    δ * base * n = δ * (base * n) := by ring
    _ ≤ δ * S₀.card := mul_le_mul_of_nonneg_left hS₀ hδ
    _ ≤ _ := hcommon.on_switchingEndpointFinset hI p hp

/-- If a reservoir occupies at least an `eta` fraction of the ambient
vertices, every exposed-set degree is bounded by `eta⁻¹` times the
reservoir size. -/
lemma degreeInto_le_inv_mul_card_of_linear_reservoir
    {n : ℕ} (G : SimpleGraph (Fin n)) (N O : Finset (Fin n))
    {eta : ℝ} (heta : 0 < eta)
    (hN : eta * n ≤ (N.card : ℝ)) (v : Fin n) :
    (AKSGraph.degreeInto G v O : ℝ) ≤ eta⁻¹ * N.card := by
  have hdegNat : AKSGraph.degreeInto G v O ≤ n :=
    (AKSGraph.degreeInto_le_card G v O).trans <| by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ O)
  have hdeg : (AKSGraph.degreeInto G v O : ℝ) ≤ n := by
    exact_mod_cast hdegNat
  calc
    (AKSGraph.degreeInto G v O : ℝ) ≤ n := hdeg
    _ = eta⁻¹ * (eta * n) := by field_simp
    _ ≤ eta⁻¹ * N.card :=
      mul_le_mul_of_nonneg_left hN (inv_nonneg.mpr heta.le)

/-- Every fixed positive fraction of `n` eventually dominates `√n`. -/
lemma exists_sqrt_le_mul_natCast (eta : ℝ) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Real.sqrt n ≤ eta * n := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_rpow_ge
    (1 / 2 : ℝ) (1 / eta) (by norm_num)
  let N := max 1 N₀
  refine ⟨N, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := by dsimp only [N] at hn; omega
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hpow := hN₀ n (by dsimp only [N] at hn; omega)
  rw [← Real.sqrt_eq_rpow] at hpow
  have hone : 1 ≤ eta * Real.sqrt n := by
    simpa only [mul_comm] using (div_le_iff₀ heta).mp hpow
  calc
    Real.sqrt n = 1 * Real.sqrt n := by ring
    _ ≤ (eta * Real.sqrt n) * Real.sqrt n :=
      mul_le_mul_of_nonneg_right hone (Real.sqrt_nonneg _)
    _ = eta * n := by rw [mul_assoc, Real.mul_self_sqrt hn0]

/-- The concrete Ramsey and coefficient hypotheses needed to apply the
bounded-window theorem on a switching common-nonneighbor reservoir. -/
lemma switchingCommonNonneighbors_boundedWindow_hypotheses
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph (Fin n)) (S S₀ : Finset (Fin n))
    (p : I → Fin n × Fin n) {C δ base : ℝ} {D : ℕ}
    (hC : 0 < C) (hn : 1 ≤ n) (hG : RamseyFree C G)
    (hδ : 0 < δ) (hbase : 0 < base)
    (hcommon : HasLargeCommonNonneighbors G S S₀ δ D)
    (hI : 2 * Fintype.card I ≤ D)
    (hp : ∀ j, p j ∈ S ×ˢ S)
    (hS₀ : base * n ≤ (S₀.card : ℝ))
    (hsqrt : Real.sqrt n ≤ δ * base * n) :
    FiniteRamseyFree (2 * C)
        (G.induce (switchingCommonNonneighbors G p S₀ :
      Set (Fin n))) ∧
      ∀ O : Finset (Fin n), ∀ v ∈ switchingCommonNonneighbors G p S₀,
        (AKSGraph.degreeInto G v O : ℝ) ≤
          (δ * base)⁻¹ *
            (switchingCommonNonneighbors G p S₀).card := by
  let N := switchingCommonNonneighbors G p S₀
  have heta : 0 < δ * base := mul_pos hδ hbase
  have hN : δ * base * n ≤ (N.card : ℝ) := by
    simpa only [N] using switchingCommonNonneighbors_card_ge_linear
      G S S₀ p δ base D hδ.le hcommon hI hp hS₀
  constructor
  · apply finiteRamseyFree_induce_of_sqrt G N hC hn hG
    exact hsqrt.trans hN
  · intro O v _hv
    exact degreeInto_le_inv_mul_card_of_linear_reservoir
      G N O heta hN v

/-- The number of edges crossing two finite vertex sets can be counted
from either side. -/
lemma sum_degreeInto_comm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Finset V) :
    (∑ v ∈ A, AKSGraph.degreeInto G v B) =
      ∑ w ∈ B, AKSGraph.degreeInto G w A := by
  have hdeg (v : V) (S : Finset V) :
      AKSGraph.degreeInto G v S =
        ∑ w ∈ S, if G.Adj v w then 1 else 0 := by
    rw [AKSGraph.degreeInto]
    simp only [Finset.sum_boole, Nat.cast_id]
    congr 1
    ext x
    simp [and_comm]
  simp_rw [hdeg]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _hw
  apply Finset.sum_congr rfl
  intro v _hv
  rw [G.adj_comm]

/-- As a function of the exposed set `O`, the mean of the remaining
edge-score polynomial on `N` is again a perturbed edge polynomial. -/
noncomputable def conditionalMeanPolynomial {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (N : Finset V)
    (O : Finset V) : ℝ :=
  Probability.perturbedEdgePolynomial G
    ((AKSGraph.edgeCount G N : ℝ) / 4)
    (fun v ↦ (AKSGraph.degreeInto G v N : ℝ) / 2) O

/-- Exact conditional-mean identity for the fair subset model. -/
lemma expectation_conditional_edgeScore_eq_conditionalMeanPolynomial
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (N O : Finset V) :
    Probability.expectation (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial
          (G.induce (N : Set V)) (AKSGraph.edgeCount G O : ℝ)
          (fun v ↦ (AKSGraph.degreeInto G v.1 O : ℝ))) =
      conditionalMeanPolynomial G N O := by
  have hedge : (G.induce (N : Set V)).edgeFinset.card =
      AKSGraph.edgeCount G N := by
    rw [← G.card_filter_edgeFinset_toFinset_subset N]
    rfl
  have hsumSubtype :
      (∑ v : (N : Set V), (AKSGraph.degreeInto G v.1 O : ℝ)) =
        ∑ v ∈ N, (AKSGraph.degreeInto G v O : ℝ) := by
    symm
    apply Finset.sum_subtype
    intro v
    simp
  have hcross :
      (∑ v ∈ N, (AKSGraph.degreeInto G v O : ℝ)) =
        ∑ w ∈ O, (AKSGraph.degreeInto G w N : ℝ) := by
    exact_mod_cast sum_degreeInto_comm G N O
  rw [Probability.expectation_perturbedEdgePolynomial _
    (by norm_num) (by norm_num)]
  rw [hedge, hsumSubtype, hcross]
  unfold conditionalMeanPolynomial Probability.perturbedEdgePolynomial
  rw [Probability.edgePolynomial_eq_inducedEdgeCount]
  change (AKSGraph.edgeCount G O : ℝ) + (1 / 2 : ℝ) ^ 2 *
      AKSGraph.edgeCount G N + (1 / 2 : ℝ) *
        ∑ w ∈ O, (AKSGraph.degreeInto G w N : ℝ) =
    (AKSGraph.edgeCount G N : ℝ) / 4 +
      (AKSGraph.edgeCount G O : ℝ) +
        ∑ v, ((AKSGraph.degreeInto G v N : ℝ) / 2) *
          Probability.bit v O
  have hsum :
      (∑ v, ((AKSGraph.degreeInto G v N : ℝ) / 2) *
          Probability.bit v O) =
        ∑ v ∈ O, (AKSGraph.degreeInto G v N : ℝ) / 2 := by
    simp [Probability.bit]
  rw [hsum, ← Finset.sum_div]
  ring

/-- The spanning graph obtained by deleting all edges incident to `N`. -/
noncomputable def outsideGraph {V : Type*} (G : SimpleGraph V)
    (N : Finset V) : SimpleGraph V :=
  (G.induce ((N : Set V)ᶜ)).spanningCoe

lemma outsideGraph_adj {V : Type*} (G : SimpleGraph V)
    (N : Finset V) (u v : V) :
    (outsideGraph G N).Adj u v ↔
      G.Adj u v ∧ u ∉ N ∧ v ∉ N := by
  simp only [outsideGraph, SimpleGraph.spanningCoe, SimpleGraph.map_adj,
    SimpleGraph.induce_adj]
  constructor
  · rintro ⟨u', v', huv, rfl, rfl⟩
    exact ⟨huv, u'.2, v'.2⟩
  · rintro ⟨huv, hu, hv⟩
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, huv, rfl, rfl⟩

lemma outsideGraph_edgePolynomial_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (N O : Finset V) (hON : Disjoint O N) :
    Probability.edgePolynomial (outsideGraph G N) O =
      Probability.edgePolynomial G O := by
  let H := outsideGraph G N
  have hgraph : H.induce (O : Set V) = G.induce (O : Set V) := by
    ext u v
    simp only [SimpleGraph.induce_adj]
    rw [show H.Adj u.1 v.1 ↔
        G.Adj u.1 v.1 ∧ u.1 ∉ N ∧ v.1 ∉ N by
      exact outsideGraph_adj G N u.1 v.1]
    have hu : u.1 ∉ N := fun huN ↦
      Finset.disjoint_left.mp hON u.2 huN
    have hv : v.1 ∉ N := fun hvN ↦
      Finset.disjoint_left.mp hON v.2 hvN
    simp only [hu, hv, not_false_eq_true, and_true]
  rw [Probability.edgePolynomial_eq_inducedEdgeCount,
    Probability.edgePolynomial_eq_inducedEdgeCount]
  rw [BoundedWindow.probability_inducedEdgeCount_eq_inducedEdges,
    BoundedWindow.probability_inducedEdgeCount_eq_inducedEdges]
  unfold inducedEdges
  rw [hgraph]

/-- The full-cube polynomial whose restriction to sets disjoint from `N`
is the conditional mean of the remaining edge score on `N`.  Its graph and
linear coefficient both vanish on `N`, so its fair-cube expectation is the
unconditional edge-count mean. -/
noncomputable def outsideConditionalMeanPolynomial
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (N O : Finset V) : ℝ :=
  Probability.perturbedEdgePolynomial (outsideGraph G N)
    ((AKSGraph.edgeCount G N : ℝ) / 4)
    (fun v ↦ if v ∈ N then 0 else
      (AKSGraph.degreeInto G v N : ℝ) / 2) O

lemma outsideConditionalMeanPolynomial_eq_conditionalMeanPolynomial
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (N O : Finset V) (hON : Disjoint O N) :
    outsideConditionalMeanPolynomial G N O =
      conditionalMeanPolynomial G N O := by
  unfold outsideConditionalMeanPolynomial conditionalMeanPolynomial
  unfold Probability.perturbedEdgePolynomial
  rw [show Probability.edgePolynomial (outsideGraph G N) O =
      Probability.edgePolynomial G O by
    exact outsideGraph_edgePolynomial_eq G N O hON]
  congr 1
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hvN : v ∈ N
  · have hvO : v ∉ O := fun hvO ↦
      Finset.disjoint_left.mp hON hvO hvN
    simp [hvN, hvO, Probability.bit]
  · simp [hvN]

lemma outsideGraph_edgeFinset_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (N : Finset V) :
    (outsideGraph G N).edgeFinset.card =
      AKSGraph.edgeCount G ((Finset.univ : Finset V) \ N) := by
  let O := (Finset.univ : Finset V) \ N
  have hON : Disjoint O N := by
    rw [Finset.disjoint_left]
    intro x hxO hxN
    exact (Finset.mem_sdiff.mp hxO).2 hxN
  have hpoly := outsideGraph_edgePolynomial_eq G N O hON
  rw [Probability.edgePolynomial_eq_inducedEdgeCount,
    Probability.edgePolynomial_eq_inducedEdgeCount] at hpoly
  change (AKSGraph.edgeCount (outsideGraph G N) O : ℝ) =
      (AKSGraph.edgeCount G O : ℝ) at hpoly
  have hfull : AKSGraph.edgeCount (outsideGraph G N) O =
      (outsideGraph G N).edgeFinset.card := by
    unfold AKSGraph.edgeCount
    rw [Finset.filter_eq_self.2]
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        simp only [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] at he
        have huv := (outsideGraph_adj G N u v).mp he
        rw [Sym2.toFinset_mk_eq]
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, huv.2.1⟩
        · rw [Finset.mem_singleton] at hx
          subst x
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, huv.2.2⟩
  have hpolyNat : AKSGraph.edgeCount (outsideGraph G N) O =
      AKSGraph.edgeCount G O := by
    exact_mod_cast hpoly
  exact hfull.symm.trans hpolyNat

/-- The outside conditional-mean polynomial has exactly the same fair-cube
mean as the original induced-edge count. -/
lemma expectation_outsideConditionalMeanPolynomial
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (N : Finset V) :
    Probability.expectation (1 / 2 : ℝ)
        (outsideConditionalMeanPolynomial G N) =
      Probability.expectation (1 / 2 : ℝ)
        (Probability.edgePolynomial G) := by
  let O := (Finset.univ : Finset V) \ N
  have hON : Disjoint N O := by
    rw [Finset.disjoint_left]
    intro x hxN hxO
    exact (Finset.mem_sdiff.mp hxO).2 hxN
  have hOutsideCard : (outsideGraph G N).edgeFinset.card =
      AKSGraph.edgeCount G O := by
    simpa only [O] using outsideGraph_edgeFinset_card G N
  have hcoeff :
      (∑ v : V, if v ∈ N then (0 : ℝ) else
          (AKSGraph.degreeInto G v N : ℝ) / 2) =
        ∑ v ∈ O, (AKSGraph.degreeInto G v N : ℝ) / 2 := by
    change (∑ v ∈ (Finset.univ : Finset V),
        if v ∈ N then (0 : ℝ) else
          (AKSGraph.degreeInto G v N : ℝ) / 2) = _
    calc
      _ = ∑ v ∈ (Finset.univ : Finset V),
          if v ∉ N then (AKSGraph.degreeInto G v N : ℝ) / 2 else 0 := by
        apply Finset.sum_congr rfl
        intro v _hv
        by_cases hvN : v ∈ N <;> simp [hvN]
      _ = ∑ v ∈ (Finset.univ.filter fun v : V ↦ v ∉ N),
          (AKSGraph.degreeInto G v N : ℝ) / 2 := by
        rw [Finset.sum_filter]
      _ = _ := by
        congr 1
        ext v
        simp [O]
  have htotalNat : AKSGraph.edgeCount G Finset.univ =
      AKSGraph.edgeCount G N + AKSGraph.edgeCount G O +
        ∑ v ∈ O, AKSGraph.degreeInto G v N := by
    have h := edgeCount_union_of_disjoint G hON
    have hunion : N ∪ O = (Finset.univ : Finset V) := by
      ext v
      by_cases hv : v ∈ N <;> simp [O, hv]
    rw [hunion] at h
    exact h
  have htotal : (G.edgeFinset.card : ℝ) =
      (AKSGraph.edgeCount G N : ℝ) +
        (AKSGraph.edgeCount G O : ℝ) +
          ∑ v ∈ O, (AKSGraph.degreeInto G v N : ℝ) := by
    have h := congrArg (fun k : ℕ ↦ (k : ℝ)) htotalNat
    simp only [AKSGraph.edgeCount_univ, Nat.cast_add, Nat.cast_sum] at h
    exact h
  unfold outsideConditionalMeanPolynomial
  rw [Probability.expectation_perturbedEdgePolynomial _
      (by norm_num) (by norm_num),
    Probability.expectation_edgePolynomial _ (by norm_num) (by norm_num)]
  rw [hOutsideCard, hcoeff, ← Finset.sum_div, htotal]
  ring

/-- A centered outside-state estimate supplies exactly the bulk hypothesis
for the bounded-window lower bound on the remaining reservoir. -/
lemma conditional_bulk_of_outsideConditionalMean_close
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (N O : Finset V) (hON : Disjoint O N)
    (x A t : ℝ)
    (hx : |x - Probability.expectation (1 / 2 : ℝ)
      (Probability.edgePolynomial G)| ≤ A)
    (hO : |outsideConditionalMeanPolynomial G N O -
      Probability.expectation (1 / 2 : ℝ)
        (Probability.edgePolynomial G)| < t) :
    |x - Probability.expectation (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial
          (G.induce (N : Set V)) (AKSGraph.edgeCount G O : ℝ)
          (fun v ↦ (AKSGraph.degreeInto G v.1 O : ℝ)))| < A + t := by
  let E := Probability.expectation (1 / 2 : ℝ)
    (Probability.edgePolynomial G)
  let M := Probability.expectation (1 / 2 : ℝ)
    (Probability.perturbedEdgePolynomial
      (G.induce (N : Set V)) (AKSGraph.edgeCount G O : ℝ)
      (fun v ↦ (AKSGraph.degreeInto G v.1 O : ℝ)))
  have hmean : M = outsideConditionalMeanPolynomial G N O := by
    rw [show M = conditionalMeanPolynomial G N O by
      exact expectation_conditional_edgeScore_eq_conditionalMeanPolynomial
        G N O]
    exact (outsideConditionalMeanPolynomial_eq_conditionalMeanPolynomial
      G N O hON).symm
  calc
    |x - M| = |(x - E) + (E - M)| := by ring_nf
    _ ≤ |x - E| + |E - M| := abs_add_le _ _
    _ = |x - E| +
        |outsideConditionalMeanPolynomial G N O - E| := by
      rw [hmean]
      congr 1
      exact abs_sub_comm E (outsideConditionalMeanPolynomial G N O)
    _ < A + t := add_lt_add_of_le_of_lt hx hO

lemma conditional_bulk_of_outsideConditionalMean_close_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (N O : Finset V) (hON : Disjoint O N)
    (x A t R : ℝ)
    (hx : |x - Probability.expectation (1 / 2 : ℝ)
      (Probability.edgePolynomial G)| ≤ A)
    (hO : |outsideConditionalMeanPolynomial G N O -
      Probability.expectation (1 / 2 : ℝ)
        (Probability.edgePolynomial G)| < t)
    (hscale : A + t ≤ R) :
    |x - Probability.expectation (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial
          (G.induce (N : Set V)) (AKSGraph.edgeCount G O : ℝ)
          (fun v ↦ (AKSGraph.degreeInto G v.1 O : ℝ)))| ≤ R :=
  (conditional_bulk_of_outsideConditionalMean_close
    G N O hON x A t hx hO).le.trans hscale

/-- A reservoir occupying an `eta` fraction of the ambient vertices converts
ambient `n^(3/2)` bulk and centering errors into the reservoir normalization
required by the lower half of the bounded-window theorem. -/
lemma conditional_bulk_of_outsideConditionalMean_close_scaled
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (N O : Finset V) (hON : Disjoint O N)
    (x eta A t : ℝ) (heta : 0 < eta) (hA : 0 ≤ A) (ht : 0 ≤ t)
    {n : ℕ} (hN : eta * n ≤ (N.card : ℝ))
    (hx : |x - Probability.expectation (1 / 2 : ℝ)
      (Probability.edgePolynomial G)| ≤ A * (n : ℝ) ^ (3 / 2 : ℝ))
    (hO : |outsideConditionalMeanPolynomial G N O -
      Probability.expectation (1 / 2 : ℝ)
        (Probability.edgePolynomial G)| < t * (n : ℝ) ^ (3 / 2 : ℝ)) :
    |x - Probability.expectation (1 / 2 : ℝ)
        (Probability.perturbedEdgePolynomial
          (G.induce (N : Set V)) (AKSGraph.edgeCount G O : ℝ)
          (fun v ↦ (AKSGraph.degreeInto G v.1 O : ℝ)))| <
      ((A + t) * eta⁻¹ ^ (3 / 2 : ℝ)) *
        (N.card : ℝ) ^ (3 / 2 : ℝ) := by
  have hnle : (n : ℝ) ≤ eta⁻¹ * (N.card : ℝ) := by
    calc
      (n : ℝ) = eta⁻¹ * (eta * n) := by field_simp
      _ ≤ eta⁻¹ * (N.card : ℝ) :=
        mul_le_mul_of_nonneg_left hN (inv_nonneg.mpr heta.le)
  have hpow : (n : ℝ) ^ (3 / 2 : ℝ) ≤
      eta⁻¹ ^ (3 / 2 : ℝ) * (N.card : ℝ) ^ (3 / 2 : ℝ) := by
    calc
      (n : ℝ) ^ (3 / 2 : ℝ) ≤
          (eta⁻¹ * (N.card : ℝ)) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hnle (by norm_num)
      _ = eta⁻¹ ^ (3 / 2 : ℝ) *
          (N.card : ℝ) ^ (3 / 2 : ℝ) := by
        rw [Real.mul_rpow (inv_nonneg.mpr heta.le) (by positivity)]
  have hbulk := conditional_bulk_of_outsideConditionalMean_close
    G N O hON x (A * (n : ℝ) ^ (3 / 2 : ℝ))
      (t * (n : ℝ) ^ (3 / 2 : ℝ)) hx hO
  have hscale :
      A * (n : ℝ) ^ (3 / 2 : ℝ) +
          t * (n : ℝ) ^ (3 / 2 : ℝ) ≤
        ((A + t) * eta⁻¹ ^ (3 / 2 : ℝ)) *
          (N.card : ℝ) ^ (3 / 2 : ℝ) := by
    calc
      A * (n : ℝ) ^ (3 / 2 : ℝ) +
          t * (n : ℝ) ^ (3 / 2 : ℝ) =
        (A + t) * (n : ℝ) ^ (3 / 2 : ℝ) := by ring
      _ ≤ (A + t) *
          (eta⁻¹ ^ (3 / 2 : ℝ) *
            (N.card : ℝ) ^ (3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow (add_nonneg hA ht)
      _ = ((A + t) * eta⁻¹ ^ (3 / 2 : ℝ)) *
          (N.card : ℝ) ^ (3 / 2 : ℝ) := by ring
  exact hbulk.trans_le hscale

/-- A bounded-window probability estimate on the graph induced by `N`
becomes the exact conditional count needed after exposing the disjoint set
`O`.  The target statistic is rewritten using
`edgeScore_union_eq_perturbedEdgePolynomial`. -/
lemma card_conditional_edgeScore_window_ge_of_probability
    {n : ℕ} (G : SimpleGraph (Fin n)) (N O : Finset (Fin n))
    (hON : Disjoint O N) (x : ℤ) (B : ℕ) (q : ℝ)
    (hprob : q ≤ Probability.eventProbability (1 / 2 : ℝ)
      (fun R : Finset (N : Set (Fin n)) ↦
        |Probability.perturbedEdgePolynomial (G.induce (N : Set (Fin n)))
          (edgeScore G O : ℝ)
          (fun v ↦ (AKSGraph.degreeInto G v.1 O : ℝ)) R - x| ≤ B)) :
    q * (2 : ℝ) ^ N.card ≤
      ((N.powerset.filter fun R ↦
        |edgeScore G (O ∪ R) - x| ≤ (B : ℤ)).card : ℝ) := by
  classical
  let c : Fin n → ℝ := fun v ↦ (AKSGraph.degreeInto G v O : ℝ)
  have hcount := BoundedWindow.card_induced_window_ge_of_probability
    G N (edgeScore G O : ℝ) c x B q (by simpa only [c] using hprob)
  have hfilter :
      (N.powerset.filter fun R ↦
        |Probability.perturbedEdgePolynomial G (edgeScore G O : ℝ) c R - x| ≤ B) =
      (N.powerset.filter fun R ↦
        |edgeScore G (O ∪ R) - x| ≤ (B : ℤ)) := by
    apply Finset.filter_congr
    intro R hR
    have hRsub : R ⊆ N := Finset.mem_powerset.mp hR
    have hdisj : Disjoint O R := hON.mono_right hRsub
    have hpoly := edgeScore_union_eq_perturbedEdgePolynomial G hdisj
    change (edgeScore G (O ∪ R) : ℝ) =
      Probability.perturbedEdgePolynomial G (edgeScore G O : ℝ) c R at hpoly
    rw [← hpoly]
    exact_mod_cast Iff.rfl
  rw [hfilter] at hcount
  exact hcount

/-- Upper-count companion of
`card_conditional_edgeScore_window_ge_of_probability`. -/
lemma card_conditional_edgeScore_window_le_of_probability
    {n : ℕ} (G : SimpleGraph (Fin n)) (N O : Finset (Fin n))
    (hON : Disjoint O N) (x : ℤ) (B : ℕ) (q : ℝ)
    (hprob : Probability.eventProbability (1 / 2 : ℝ)
      (fun R : Finset (N : Set (Fin n)) ↦
        |Probability.perturbedEdgePolynomial (G.induce (N : Set (Fin n)))
          (edgeScore G O : ℝ)
          (fun v ↦ (AKSGraph.degreeInto G v.1 O : ℝ)) R - x| ≤ B) ≤ q) :
    ((N.powerset.filter fun R ↦
        |edgeScore G (O ∪ R) - x| ≤ (B : ℤ)).card : ℝ) ≤
      q * (2 : ℝ) ^ N.card := by
  classical
  let c : Fin n → ℝ := fun v ↦ (AKSGraph.degreeInto G v O : ℝ)
  have hcount := BoundedWindow.card_induced_window_le_of_probability
    G N (edgeScore G O : ℝ) c x B q (by simpa only [c] using hprob)
  have hfilter :
      (N.powerset.filter fun R ↦
        |Probability.perturbedEdgePolynomial G (edgeScore G O : ℝ) c R - x| ≤ B) =
      (N.powerset.filter fun R ↦
        |edgeScore G (O ∪ R) - x| ≤ (B : ℤ)) := by
    apply Finset.filter_congr
    intro R hR
    have hRsub : R ⊆ N := Finset.mem_powerset.mp hR
    have hdisj : Disjoint O R := hON.mono_right hRsub
    have hpoly := edgeScore_union_eq_perturbedEdgePolynomial G hdisj
    change (edgeScore G (O ∪ R) : ℝ) =
      Probability.perturbedEdgePolynomial G (edgeScore G O : ℝ) c R at hpoly
    rw [← hpoly]
    exact_mod_cast Iff.rfl
  rw [hfilter] at hcount
  exact hcount

/-- The lower half of KSSS Theorem 3.1, specialized to a disjoint exposed
set and an induced reservoir.  All transport and counting normalization is
discharged here; the remaining hypotheses are exactly Ramsey inheritance,
the linear-coefficient bound, and membership of the target in the
conditional bulk. -/
lemma exists_conditional_edgeScore_window_lower_of_ksssBoundedWindow
    (hBW : KSSSBoundedWindow) (C H A : ℝ)
    (hC : 0 < C) (hH : 0 < H) (hA : 0 < A) :
    ∃ (B : ℕ) (kappa : ℝ), 0 < B ∧ 0 < kappa ∧ ∃ N₀ : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (N O : Finset (Fin n)),
        Disjoint O N → N₀ ≤ N.card →
        FiniteRamseyFree C (G.induce (N : Set (Fin n))) →
        (∀ v ∈ N,
          (AKSGraph.degreeInto G v O : ℝ) ≤ H * N.card) →
        ∀ x : ℤ,
          |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
              (Probability.perturbedEdgePolynomial
                (G.induce (N : Set (Fin n))) (edgeScore G O : ℝ)
                (fun v ↦ (AKSGraph.degreeInto G v.1 O : ℝ)))| ≤
              A * (N.card : ℝ) ^ (3 / 2 : ℝ) →
          kappa * (N.card : ℝ) ^ (-(3 / 2 : ℝ)) *
              (2 : ℝ) ^ N.card ≤
            ((N.powerset.filter fun R ↦
              |edgeScore G (O ∪ R) - x| ≤ (B : ℤ)).card : ℝ) := by
  obtain ⟨B, hB, _hupper, hlower⟩ := hBW C hC
  obtain ⟨kappa, hkappa, N₀, hN₀⟩ := hlower H A hH hA
  refine ⟨B, kappa, hB, hkappa, N₀, ?_⟩
  intro n G N O hON hNcard hRamsey hc x hbulk
  classical
  have hsize : N₀ ≤ Fintype.card (N : Set (Fin n)) := by
    simpa only [card_subtype_coe_finset N] using hNcard
  have hcoeff : ∀ v : (N : Set (Fin n)),
      0 ≤ (AKSGraph.degreeInto G v.1 O : ℝ) ∧
        (AKSGraph.degreeInto G v.1 O : ℝ) ≤
          H * Fintype.card (N : Set (Fin n)) := by
    intro v
    constructor
    · positivity
    · simpa only [card_subtype_coe_finset N] using hc v.1 v.2
  have hprob := hN₀ (N : Set (Fin n))
    (G.induce (N : Set (Fin n))) hsize hRamsey
    (edgeScore G O : ℝ)
    (fun v ↦ (AKSGraph.degreeInto G v.1 O : ℝ)) hcoeff x
    (by simpa only [card_subtype_coe_finset N] using hbulk)
  exact card_conditional_edgeScore_window_ge_of_probability
    G N O hON x B
      (kappa * (N.card : ℝ) ^ (-(3 / 2 : ℝ)))
      (by simpa only [card_subtype_coe_finset N] using hprob)

/-- The upper half of KSSS Theorem 3.1 in the same conditional counting
normalization. -/
lemma exists_conditional_edgeScore_window_upper_of_ksssBoundedWindow
    (hBW : KSSSBoundedWindow) (C H : ℝ)
    (hC : 0 < C) (hH : 0 < H) :
    ∃ (B : ℕ) (K : ℝ), 0 < B ∧ 0 < K ∧ ∃ N₀ : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (N O : Finset (Fin n)),
        Disjoint O N → N₀ ≤ N.card →
        FiniteRamseyFree C (G.induce (N : Set (Fin n))) →
        (∀ v ∈ N,
          (AKSGraph.degreeInto G v O : ℝ) ≤ H * N.card) →
        ∀ x : ℤ,
          ((N.powerset.filter fun R ↦
              |edgeScore G (O ∪ R) - x| ≤ (B : ℤ)).card : ℝ) ≤
            K * (N.card : ℝ) ^ (-(3 / 2 : ℝ)) *
              (2 : ℝ) ^ N.card := by
  obtain ⟨B, hB, hupper, _hlower⟩ := hBW C hC
  obtain ⟨K, hK, N₀, hN₀⟩ := hupper H hH
  refine ⟨B, K, hB, hK, N₀, ?_⟩
  intro n G N O hON hNcard hRamsey hc x
  classical
  have hsize : N₀ ≤ Fintype.card (N : Set (Fin n)) := by
    simpa only [card_subtype_coe_finset N] using hNcard
  have hcoeff : ∀ v : (N : Set (Fin n)),
      0 ≤ (AKSGraph.degreeInto G v.1 O : ℝ) ∧
        (AKSGraph.degreeInto G v.1 O : ℝ) ≤
          H * Fintype.card (N : Set (Fin n)) := by
    intro v
    constructor
    · positivity
    · simpa only [card_subtype_coe_finset N] using hc v.1 v.2
  have hprob := hN₀ (N : Set (Fin n))
    (G.induce (N : Set (Fin n))) hsize hRamsey
    (edgeScore G O : ℝ)
    (fun v ↦ (AKSGraph.degreeInto G v.1 O : ℝ)) hcoeff x
  exact card_conditional_edgeScore_window_le_of_probability
    G N O hON x B
      (K * (N.card : ℝ) ^ (-(3 / 2 : ℝ)))
      (by simpa only [card_subtype_coe_finset N] using hprob)

/-- The upper bounded-window count on every switching common-nonneighbor
reservoir, with all hypotheses supplied by Lemma 13.1 and ambient
Ramsey-freeness. -/
theorem exists_switchingConditional_window_upper_of_ksssBoundedWindow
    (hBW : KSSSBoundedWindow) (C δ base : ℝ)
    (hC : 0 < C) (hδ : 0 < δ) (hbase : 0 < base) :
    ∃ (B : ℕ) (K : ℝ), 0 < B ∧ 0 < K ∧ ∃ N₀ : ℕ,
      ∀ n : ℕ, N₀ ≤ n →
      ∀ (G : SimpleGraph (Fin n)), RamseyFree C G →
      ∀ (I : Type) [Fintype I] [DecidableEq I]
        (S S₀ : Finset (Fin n)) (p : I → Fin n × Fin n) (D : ℕ),
        HasLargeCommonNonneighbors G S S₀ δ D →
        2 * Fintype.card I ≤ D →
        (∀ j, p j ∈ S ×ˢ S) →
        base * n ≤ (S₀.card : ℝ) →
        ∀ O : Finset (Fin n),
          Disjoint O (switchingCommonNonneighbors G p S₀) →
          ∀ x : ℤ,
          (((switchingCommonNonneighbors G p S₀).powerset.filter fun R ↦
              |edgeScore G (O ∪ R) - x| ≤ (B : ℤ)).card : ℝ) ≤
            K * ((switchingCommonNonneighbors G p S₀).card : ℝ) ^
                (-(3 / 2 : ℝ)) *
              (2 : ℝ) ^ (switchingCommonNonneighbors G p S₀).card := by
  let eta := δ * base
  have heta : 0 < eta := by dsimp only [eta]; positivity
  obtain ⟨B, K, hB, hK, Nwindow, hwindow⟩ :=
    exists_conditional_edgeScore_window_upper_of_ksssBoundedWindow
      hBW (2 * C) eta⁻¹ (by positivity) (inv_pos.mpr heta)
  obtain ⟨Nsqrt, hsqrt⟩ := exists_sqrt_le_mul_natCast eta heta
  obtain ⟨Nsize, hsize⟩ := exists_nat_rpow_ge
    1 (Nwindow / eta) (by norm_num)
  let N₀ := max 1 (max Nsqrt Nsize)
  refine ⟨B, K, hB, hK, N₀, ?_⟩
  intro n hn G hG I instI instDecI S S₀ p D hcommon hID hp hS₀ O hON x
  let N := switchingCommonNonneighbors G p S₀
  have hn1 : 1 ≤ n := by dsimp only [N₀] at hn; omega
  have hnSqrt : Nsqrt ≤ n := by dsimp only [N₀] at hn; omega
  have hnSize : Nsize ≤ n := by dsimp only [N₀] at hn; omega
  have hNlinear : eta * n ≤ (N.card : ℝ) := by
    simpa only [eta, N] using switchingCommonNonneighbors_card_ge_linear
      G S S₀ p δ base D hδ.le hcommon hID hp hS₀
  have hNwindowReal : (Nwindow : ℝ) ≤ eta * n := by
    have hpow := hsize n hnSize
    rw [Real.rpow_one] at hpow
    simpa only [mul_comm] using (div_le_iff₀ heta).mp hpow
  have hNwindow : Nwindow ≤ N.card := by
    exact_mod_cast hNwindowReal.trans hNlinear
  have hdata := switchingCommonNonneighbors_boundedWindow_hypotheses
    G S S₀ p hC hn1 hG hδ hbase hcommon hID hp hS₀
      (by simpa only [eta] using hsqrt n hnSqrt)
  exact hwindow n G N O hON hNwindow
    (by simpa only [N] using hdata.1)
    (by simpa only [eta, N] using hdata.2 O) x

/-- The matching lower conditional count.  The sole remaining per-outside
hypothesis is now exactly the bulk condition, for which
`conditional_bulk_of_outsideConditionalMean_close` supplies the deterministic
bridge. -/
theorem exists_switchingConditional_window_lower_of_ksssBoundedWindow
    (hBW : KSSSBoundedWindow) (C δ base A : ℝ)
    (hC : 0 < C) (hδ : 0 < δ) (hbase : 0 < base) (hA : 0 < A) :
    ∃ (B : ℕ) (kappa : ℝ), 0 < B ∧ 0 < kappa ∧ ∃ N₀ : ℕ,
      ∀ n : ℕ, N₀ ≤ n →
      ∀ (G : SimpleGraph (Fin n)), RamseyFree C G →
      ∀ (I : Type) [Fintype I] [DecidableEq I]
        (S S₀ : Finset (Fin n)) (p : I → Fin n × Fin n) (D : ℕ),
        HasLargeCommonNonneighbors G S S₀ δ D →
        2 * Fintype.card I ≤ D →
        (∀ j, p j ∈ S ×ˢ S) →
        base * n ≤ (S₀.card : ℝ) →
        ∀ O : Finset (Fin n),
          Disjoint O (switchingCommonNonneighbors G p S₀) →
          ∀ x : ℤ,
          |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
              (Probability.perturbedEdgePolynomial
                (G.induce (switchingCommonNonneighbors G p S₀ :
                  Set (Fin n))) (edgeScore G O : ℝ)
                (fun v ↦ (AKSGraph.degreeInto G v.1 O : ℝ)))| ≤
              A * ((switchingCommonNonneighbors G p S₀).card : ℝ) ^
                (3 / 2 : ℝ) →
          kappa * ((switchingCommonNonneighbors G p S₀).card : ℝ) ^
                (-(3 / 2 : ℝ)) *
              (2 : ℝ) ^ (switchingCommonNonneighbors G p S₀).card ≤
            (((switchingCommonNonneighbors G p S₀).powerset.filter fun R ↦
              |edgeScore G (O ∪ R) - x| ≤ (B : ℤ)).card : ℝ) := by
  let eta := δ * base
  have heta : 0 < eta := by dsimp only [eta]; positivity
  obtain ⟨B, kappa, hB, hkappa, Nwindow, hwindow⟩ :=
    exists_conditional_edgeScore_window_lower_of_ksssBoundedWindow
      hBW (2 * C) eta⁻¹ A (by positivity) (inv_pos.mpr heta) hA
  obtain ⟨Nsqrt, hsqrt⟩ := exists_sqrt_le_mul_natCast eta heta
  obtain ⟨Nsize, hsize⟩ := exists_nat_rpow_ge
    1 (Nwindow / eta) (by norm_num)
  let N₀ := max 1 (max Nsqrt Nsize)
  refine ⟨B, kappa, hB, hkappa, N₀, ?_⟩
  intro n hn G hG I instI instDecI S S₀ p D hcommon hID hp hS₀ O hON x hbulk
  let N := switchingCommonNonneighbors G p S₀
  have hn1 : 1 ≤ n := by dsimp only [N₀] at hn; omega
  have hnSqrt : Nsqrt ≤ n := by dsimp only [N₀] at hn; omega
  have hnSize : Nsize ≤ n := by dsimp only [N₀] at hn; omega
  have hNlinear : eta * n ≤ (N.card : ℝ) := by
    simpa only [eta, N] using switchingCommonNonneighbors_card_ge_linear
      G S S₀ p δ base D hδ.le hcommon hID hp hS₀
  have hNwindowReal : (Nwindow : ℝ) ≤ eta * n := by
    have hpow := hsize n hnSize
    rw [Real.rpow_one] at hpow
    simpa only [mul_comm] using (div_le_iff₀ heta).mp hpow
  have hNwindow : Nwindow ≤ N.card := by
    exact_mod_cast hNwindowReal.trans hNlinear
  have hdata := switchingCommonNonneighbors_boundedWindow_hypotheses
    G S S₀ p hC hn1 hG hδ hbase hcommon hID hp hS₀
      (by simpa only [eta] using hsqrt n hnSqrt)
  exact hwindow n G N O hON hNwindow
    (by simpa only [N] using hdata.1)
    (by simpa only [eta, N] using hdata.2 O) x
    (by simpa only [N] using hbulk)

/-- Source-shaped form of the lower conditional window estimate.  It is
enough to center the target and the exposed outside state on the global
edge-count mean at ambient scale: the linear-size switching reservoir then
converts both errors to the normalization required by Theorem 3.1. -/
theorem exists_switchingConditional_window_lower_of_ksssBoundedWindow_of_outside_close
    (hBW : KSSSBoundedWindow) (C delta base A t : ℝ)
    (hC : 0 < C) (hdelta : 0 < delta) (hbase : 0 < base)
    (hA : 0 < A) (ht : 0 ≤ t) :
    ∃ (B : ℕ) (kappa : ℝ), 0 < B ∧ 0 < kappa ∧ ∃ N₀ : ℕ,
      ∀ n : ℕ, N₀ ≤ n →
      ∀ (G : SimpleGraph (Fin n)), RamseyFree C G →
      ∀ (I : Type) [Fintype I] [DecidableEq I]
        (S S₀ : Finset (Fin n)) (p : I → Fin n × Fin n) (D : ℕ),
        HasLargeCommonNonneighbors G S S₀ delta D →
        2 * Fintype.card I ≤ D →
        (∀ j, p j ∈ S ×ˢ S) →
        base * n ≤ (S₀.card : ℝ) →
        ∀ O : Finset (Fin n),
          Disjoint O (switchingCommonNonneighbors G p S₀) →
          ∀ x : ℤ,
          |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
              (Probability.edgePolynomial G)| ≤
                A * (n : ℝ) ^ (3 / 2 : ℝ) →
          |outsideConditionalMeanPolynomial G
              (switchingCommonNonneighbors G p S₀) O -
              Probability.expectation (1 / 2 : ℝ)
                (Probability.edgePolynomial G)| <
                t * (n : ℝ) ^ (3 / 2 : ℝ) →
          kappa * ((switchingCommonNonneighbors G p S₀).card : ℝ) ^
                (-(3 / 2 : ℝ)) *
              (2 : ℝ) ^ (switchingCommonNonneighbors G p S₀).card ≤
            (((switchingCommonNonneighbors G p S₀).powerset.filter fun R ↦
              |edgeScore G (O ∪ R) - x| ≤ (B : ℤ)).card : ℝ) := by
  let eta := delta * base
  have heta : 0 < eta := by dsimp only [eta]; positivity
  let Ares := (A + t) * eta⁻¹ ^ (3 / 2 : ℝ)
  have hAres : 0 < Ares := by
    dsimp only [Ares]
    positivity
  obtain ⟨B, kappa, hB, hkappa, N₀, hwindow⟩ :=
    exists_switchingConditional_window_lower_of_ksssBoundedWindow
      hBW C delta base Ares hC hdelta hbase hAres
  refine ⟨B, kappa, hB, hkappa, N₀, ?_⟩
  intro n hn G hG I instI instDecI S S₀ p D
    hcommon hID hp hS₀ O hON x hx hO
  let N := switchingCommonNonneighbors G p S₀
  have hNlinear : eta * n ≤ (N.card : ℝ) := by
    simpa only [eta, N] using switchingCommonNonneighbors_card_ge_linear
      G S S₀ p delta base D hdelta.le hcommon hID hp hS₀
  apply hwindow n hn G hG I S S₀ p D hcommon hID hp hS₀ O hON x
  have hbulk := conditional_bulk_of_outsideConditionalMean_close_scaled
    G N O (by simpa only [N] using hON) (x : ℝ) eta A t heta hA.le ht
      hNlinear hx (by simpa only [N] using hO)
  have hscore : (edgeScore G O : ℝ) = (AKSGraph.edgeCount G O : ℝ) := by
    exact_mod_cast edgeScore_eq_edgeCount G O
  rw [hscore]
  simpa only [Ares, N] using hbulk.le

/-- The powers of two from a disjoint family of blocks and its complement
combine to the Boolean-cube factor, for an arbitrary finite index type. -/
lemma finite_family_lower_factor_eq {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I]
    (W : I → Finset (Fin n))
    (hdisj : Set.PairwiseDisjoint Set.univ W) (C : ℝ) :
    (∏ i : I, (((2 : ℝ) ^ (W i).card / (8 * Real.sqrt n)) *
        Real.exp (-8 * C))) *
      (2 : ℝ) ^ (n - (Finset.univ.biUnion W).card) =
    (2 : ℝ) ^ n *
      (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^ Fintype.card I := by
  have hWcard : (Finset.univ.biUnion W).card = ∑ i, (W i).card := by
    apply Finset.card_biUnion
    intro i _hi j _hj hij
    exact hdisj (Set.mem_univ i) (Set.mem_univ j) hij
  have hWle : (Finset.univ.biUnion W).card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Finset.univ.biUnion W))
  simp_rw [show ∀ i : I,
      ((2 : ℝ) ^ (W i).card / (8 * Real.sqrt n)) * Real.exp (-8 * C) =
        (2 : ℝ) ^ (W i).card *
          (Real.exp (-8 * C) / (8 * Real.sqrt n)) by
    intro i
    ring]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp only [Finset.prod_const, Finset.card_univ]
  calc
    (2 : ℝ) ^ (∑ i, (W i).card) *
          (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^ Fintype.card I *
        (2 : ℝ) ^ (n - (Finset.univ.biUnion W).card) =
        ((2 : ℝ) ^ (∑ i, (W i).card) *
          (2 : ℝ) ^ (n - (Finset.univ.biUnion W).card)) *
            (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^ Fintype.card I := by
      ring
    _ = (2 : ℝ) ^ n *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^ Fintype.card I := by
      rw [← pow_add, ← hWcard, Nat.add_sub_of_le hWle]

/-- Source-shaped lower count for one good ordered switching tuple.  A
`q`-fraction (in counting normalization) of outside assignments may be
completed using near-central counts in every private-neighbour block.  The
result has exactly the `2^n n^{-s/2}` factor required in the lower half of
KSSS Lemma 13.4; choosing `q` of order `n^{-3/2}` supplies the remaining
bounded-window factor. -/
lemma card_states_containing_switchingTuple_and_window_ge_of_outsides
    {n : ℕ}
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (S₀ : Finset (Fin n))
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (hpT : ∀ j, p j ∈ T) (hp : PairEndpointsDistinct p)
    (outsides : Finset (Finset (Fin n)))
    (counts : Finset (Fin n) → RawTupleIndex labels a → ℕ)
    (D : ℕ) (C q : ℝ)
    (hblockPos : ∀ i, 1 ≤ (switchingPrivateNeighbors G p i S₀).card)
    (hblockHalf : ∀ i,
      1 ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hD : ∀ i,
      8 * D ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hcountsLe : ∀ O ∈ outsides, ∀ i,
      counts O i ≤ (switchingPrivateNeighbors G p i S₀).card)
    (hcountsNear : ∀ O ∈ outsides, ∀ i,
      Nat.dist (counts O i)
        ((switchingPrivateNeighbors G p i S₀).card / 2) ≤ D)
    (hquad : ∀ i, (D : ℝ) ^ 2 ≤
      C * ((switchingPrivateNeighbors G p i S₀).card / 2 : ℕ))
    (houtsideCount :
      q * (2 : ℝ) ^
          (n - (Finset.univ.biUnion fun i ↦
            switchingPrivateNeighbors G p i S₀).card) ≤
        (outsides.card : ℝ))
    (houtside : ∀ O ∈ outsides,
      Disjoint O (Finset.univ.biUnion
        (fun i ↦ switchingPrivateNeighbors G p i S₀)))
    (hy : ∀ O ∈ outsides, ∀ j, (p j).1 ∈ O)
    (hz : ∀ O ∈ outsides, ∀ j, (p j).2 ∉ O)
    (hrequired : ∀ O ∈ outsides, ∀ j,
      (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) j +
          counts O j = (j.1.1 : ℝ))
    (window : Finset (Fin n) → Prop)
    (hwindow : ∀ U,
      U \ Finset.univ.biUnion
          (fun i ↦ switchingPrivateNeighbors G p i S₀) ∈ outsides →
      (∀ i, (U ∩ switchingPrivateNeighbors G p i S₀).card =
        counts (U \ Finset.univ.biUnion
          (fun j ↦ switchingPrivateNeighbors G p j S₀)) i) →
      window U) :
    q * ((2 : ℝ) ^ n *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
          Fintype.card (RawTupleIndex labels a)) ≤
      (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          window U).card : ℝ) := by
  classical
  let blocks := fun i : RawTupleIndex labels a ↦
    switchingPrivateNeighbors G p i S₀
  let lower : ℝ := ∏ i : RawTupleIndex labels a,
    (((2 : ℝ) ^ (blocks i).card / (8 * Real.sqrt n)) *
      Real.exp (-8 * C))
  let target := (Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
    p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧ window U
  have hblockN : ∀ i, (blocks i).card ≤ n := by
    intro i
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (blocks i))
  have hprod : ∀ O ∈ outsides, lower ≤
      ∏ i : RawTupleIndex labels a,
        (Nat.choose (blocks i).card (counts O i) : ℝ) := by
    intro O hO
    exact prod_choose_near_middle_lower_of_ambient n
      (fun i ↦ (blocks i).card) (counts O) D C
      (by simpa only [blocks] using hblockPos)
      hblockN
      (by simpa only [blocks] using hblockHalf)
      (by simpa only [blocks] using hD)
      (by simpa only [blocks] using hcountsLe O hO)
      (by simpa only [blocks] using hcountsNear O hO)
      (by simpa only [blocks] using hquad)
  have hcountNat :=
    sum_private_choose_le_card_states_containing_switchingTuple_and_window
      T G labels a S₀ p hpT hp outsides counts houtside hy hz hrequired
        window hwindow
  have hcountReal :
      (((∑ O ∈ outsides, ∏ i,
        Nat.choose (blocks i).card (counts O i)) : ℕ) : ℝ) ≤
          (target.card : ℝ) := by
    exact_mod_cast (by simpa only [blocks, target] using hcountNat)
  have hsum : (outsides.card : ℝ) * lower ≤
      (((∑ O ∈ outsides, ∏ i,
        Nat.choose (blocks i).card (counts O i)) : ℕ) : ℝ) := by
    calc
      (outsides.card : ℝ) * lower = ∑ _O ∈ outsides, lower := by simp
      _ ≤ ∑ O ∈ outsides, ∏ i,
          (Nat.choose (blocks i).card (counts O i) : ℝ) := by
        exact Finset.sum_le_sum fun O hO ↦ hprod O hO
      _ = (((∑ O ∈ outsides, ∏ i,
          Nat.choose (blocks i).card (counts O i)) : ℕ) : ℝ) := by
        push_cast
        rfl
  have hdisjoint : Set.PairwiseDisjoint Set.univ blocks := by
    intro i _hi j _hj hij
    exact switchingPrivateNeighbors_pairwise_disjoint G p S₀ hp hij
  have hlower : 0 ≤ lower := by
    dsimp only [lower]
    positivity
  calc
    q * ((2 : ℝ) ^ n *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
          Fintype.card (RawTupleIndex labels a)) =
        (q * (2 : ℝ) ^
          (n - (Finset.univ.biUnion blocks).card)) * lower := by
      rw [← finite_family_lower_factor_eq blocks hdisjoint C]
      ring
    _ ≤ (outsides.card : ℝ) * lower :=
      mul_le_mul_of_nonneg_right
        (by simpa only [blocks] using houtsideCount) hlower
    _ ≤ (((∑ O ∈ outsides, ∏ i,
        Nat.choose (blocks i).card (counts O i)) : ℕ) : ℝ) := hsum
    _ ≤ (target.card : ℝ) := hcountReal
    _ = (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          window U).card : ℝ) := rfl

/-- Source-shaped lower count when only a fixed fraction of each exact
private-block fibre satisfies the window-producing good event.  The two
factors separate the first exposure (`qOutside`) from the conditional slice
concentration inside each prescribed-count fibre (`qGood`). -/
lemma card_states_containingSwitchingTuple_and_window_ge_of_goodFibers
    {n : ℕ}
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (S₀ : Finset (Fin n))
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (hpT : ∀ j, p j ∈ T) (hp : PairEndpointsDistinct p)
    (outsides : Finset (Finset (Fin n)))
    (counts : Finset (Fin n) → RawTupleIndex labels a → ℕ)
    (D : ℕ) (C qOutside qGood : ℝ)
    (hqGood : 0 ≤ qGood)
    (hblockPos : ∀ i, 1 ≤ (switchingPrivateNeighbors G p i S₀).card)
    (hblockHalf : ∀ i,
      1 ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hD : ∀ i,
      8 * D ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hcountsLe : ∀ O ∈ outsides, ∀ i,
      counts O i ≤ (switchingPrivateNeighbors G p i S₀).card)
    (hcountsNear : ∀ O ∈ outsides, ∀ i,
      Nat.dist (counts O i)
        ((switchingPrivateNeighbors G p i S₀).card / 2) ≤ D)
    (hquad : ∀ i, (D : ℝ) ^ 2 ≤
      C * ((switchingPrivateNeighbors G p i S₀).card / 2 : ℕ))
    (houtsideCount :
      qOutside * (2 : ℝ) ^
          (n - (Finset.univ.biUnion fun i ↦
            switchingPrivateNeighbors G p i S₀).card) ≤
        (outsides.card : ℝ))
    (hy : ∀ O ∈ outsides, ∀ j, (p j).1 ∈ O)
    (hz : ∀ O ∈ outsides, ∀ j, (p j).2 ∉ O)
    (hrequired : ∀ O ∈ outsides, ∀ j,
      (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) j +
          counts O j = (j.1.1 : ℝ))
    (good window : Finset (Fin n) → Prop)
    (hgoodFiber : ∀ O ∈ outsides,
      qGood * (∏ i,
          (Nat.choose (switchingPrivateNeighbors G p i S₀).card
            (counts O i) : ℝ)) ≤
        (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
          U \ Finset.univ.biUnion
              (fun i ↦ switchingPrivateNeighbors G p i S₀) = O ∧
            (∀ i, (U ∩ switchingPrivateNeighbors G p i S₀).card =
              counts O i) ∧ good U).card : ℝ))
    (hwindow : ∀ U,
      U \ Finset.univ.biUnion
          (fun i ↦ switchingPrivateNeighbors G p i S₀) ∈ outsides →
      (∀ i, (U ∩ switchingPrivateNeighbors G p i S₀).card =
        counts (U \ Finset.univ.biUnion
          (fun j ↦ switchingPrivateNeighbors G p j S₀)) i) →
      good U → window U) :
    (qGood * qOutside) * ((2 : ℝ) ^ n *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
          Fintype.card (RawTupleIndex labels a)) ≤
      (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          window U).card : ℝ) := by
  classical
  let blocks := fun i : RawTupleIndex labels a ↦
    switchingPrivateNeighbors G p i S₀
  let lower : ℝ := ∏ i : RawTupleIndex labels a,
    (((2 : ℝ) ^ (blocks i).card / (8 * Real.sqrt n)) *
      Real.exp (-8 * C))
  let goodFiber := fun O : Finset (Fin n) ↦
    (Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
      U \ Finset.univ.biUnion blocks = O ∧
        (∀ i, (U ∩ blocks i).card = counts O i) ∧ good U
  let target := (Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
    p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧ window U
  have hblockN : ∀ i, (blocks i).card ≤ n := by
    intro i
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (blocks i))
  have hprod : ∀ O ∈ outsides, lower ≤
      ∏ i : RawTupleIndex labels a,
        (Nat.choose (blocks i).card (counts O i) : ℝ) := by
    intro O hO
    exact prod_choose_near_middle_lower_of_ambient n
      (fun i ↦ (blocks i).card) (counts O) D C
      (by simpa only [blocks] using hblockPos)
      hblockN
      (by simpa only [blocks] using hblockHalf)
      (by simpa only [blocks] using hD)
      (by simpa only [blocks] using hcountsLe O hO)
      (by simpa only [blocks] using hcountsNear O hO)
      (by simpa only [blocks] using hquad)
  have hcountNat :=
    sum_private_goodFibers_le_card_states_containingSwitchingTuple_and_window
      T G labels a S₀ p hpT hp outsides counts hy hz hrequired good window hwindow
  have hcountReal :
      ((∑ O ∈ outsides, (goodFiber O).card : ℕ) : ℝ) ≤
          (target.card : ℝ) := by
    exact_mod_cast (by simpa only [blocks, goodFiber, target] using hcountNat)
  have hsum : (outsides.card : ℝ) * (qGood * lower) ≤
      ((∑ O ∈ outsides, (goodFiber O).card : ℕ) : ℝ) := by
    calc
      (outsides.card : ℝ) * (qGood * lower) =
          ∑ _O ∈ outsides, qGood * lower := by simp
      _ ≤ ∑ O ∈ outsides, ((goodFiber O).card : ℝ) := by
        apply Finset.sum_le_sum
        intro O hO
        exact (mul_le_mul_of_nonneg_left (hprod O hO) hqGood).trans
          (by simpa only [blocks, goodFiber] using hgoodFiber O hO)
      _ = ((∑ O ∈ outsides, (goodFiber O).card : ℕ) : ℝ) := by
        push_cast
        rfl
  have hdisjoint : Set.PairwiseDisjoint Set.univ blocks := by
    intro i _hi j _hj hij
    exact switchingPrivateNeighbors_pairwise_disjoint G p S₀ hp hij
  have hlower : 0 ≤ lower := by
    dsimp only [lower]
    positivity
  calc
    (qGood * qOutside) * ((2 : ℝ) ^ n *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
          Fintype.card (RawTupleIndex labels a)) =
        (qOutside * (2 : ℝ) ^
          (n - (Finset.univ.biUnion blocks).card)) * (qGood * lower) := by
      rw [← finite_family_lower_factor_eq blocks hdisjoint C]
      ring
    _ ≤ (outsides.card : ℝ) * (qGood * lower) :=
      mul_le_mul_of_nonneg_right
        (by simpa only [blocks] using houtsideCount)
        (mul_nonneg hqGood hlower)
    _ ≤ ((∑ O ∈ outsides, (goodFiber O).card : ℕ) : ℝ) := hsum
    _ ≤ (target.card : ℝ) := hcountReal
    _ = (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          window U).card : ℝ) := rfl

/-- The preceding private-block count restricted to assignments outside the
common-nonneighbor reservoir.  This is the outside factor which is multiplied
by the conditional bounded-window count on that reservoir. -/
private lemma card_outside_states_containing_switchingTuple_ge_full_cube_normalization
    {n : ℕ}
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (S₀ : Finset (Fin n))
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (hpT : ∀ j, p j ∈ T) (hp : PairEndpointsDistinct p)
    (cores : Finset (Finset (Fin n)))
    (counts : Finset (Fin n) → RawTupleIndex labels a → ℕ)
    (D : ℕ) (C q : ℝ)
    (hblockPos : ∀ i, 1 ≤ (switchingPrivateNeighbors G p i S₀).card)
    (hblockHalf : ∀ i,
      1 ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hD : ∀ i,
      8 * D ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hcountsLe : ∀ O ∈ cores, ∀ i,
      counts O i ≤ (switchingPrivateNeighbors G p i S₀).card)
    (hcountsNear : ∀ O ∈ cores, ∀ i,
      Nat.dist (counts O i)
        ((switchingPrivateNeighbors G p i S₀).card / 2) ≤ D)
    (hquad : ∀ i, (D : ℝ) ^ 2 ≤
      C * ((switchingPrivateNeighbors G p i S₀).card / 2 : ℕ))
    (hcoreCount :
      q * (2 : ℝ) ^
          (n - (Finset.univ.biUnion fun i ↦
            switchingPrivateNeighbors G p i S₀).card) ≤
        (cores.card : ℝ))
    (hcoreBlocks : ∀ O ∈ cores,
      Disjoint O (Finset.univ.biUnion
        (fun i ↦ switchingPrivateNeighbors G p i S₀)))
    (hcoreN : ∀ O ∈ cores,
      Disjoint O (switchingCommonNonneighbors G p S₀))
    (hy : ∀ O ∈ cores, ∀ j, (p j).1 ∈ O)
    (hz : ∀ O ∈ cores, ∀ j, (p j).2 ∉ O)
    (hrequired : ∀ O ∈ cores, ∀ j,
      (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) j +
          counts O j = (j.1.1 : ℝ)) :
    q * ((2 : ℝ) ^ n *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
          Fintype.card (RawTupleIndex labels a)) ≤
      ((((Finset.univ : Finset (Fin n)) \
          switchingCommonNonneighbors G p S₀).powerset.filter
        (fun U ↦ p ∈ switchingTupleFinset T (edgeScore G) labels a U)).card : ℝ) := by
  classical
  let N := switchingCommonNonneighbors G p S₀
  let blocks := fun i : RawTupleIndex labels a ↦
    switchingPrivateNeighbors G p i S₀
  let outsideN := (Finset.univ : Finset (Fin n)) \ N
  have hbase := card_states_containing_switchingTuple_and_window_ge_of_outsides
    T G labels a S₀ p hpT hp cores counts D C q hblockPos hblockHalf hD
      hcountsLe hcountsNear hquad hcoreCount hcoreBlocks hy hz hrequired
      (fun U ↦ U ⊆ outsideN) (by
        intro U hO _hcounts x hxU
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ x, ?_⟩
        intro hxN
        by_cases hxB : x ∈ Finset.univ.biUnion blocks
        · obtain ⟨i, _hi, hxi⟩ := Finset.mem_biUnion.mp hxB
          exact Finset.disjoint_left.mp
            (switchingCommonNonneighbors_disjoint_private G p S₀ i)
            hxN hxi
        · have hxOutside : x ∈
              U \ Finset.univ.biUnion blocks :=
            Finset.mem_sdiff.mpr ⟨hxU, hxB⟩
          exact Finset.disjoint_left.mp
            (hcoreN _ hO) hxOutside hxN)
  have hfilter :
      ((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
            U ⊆ outsideN) =
        outsideN.powerset.filter fun U ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a U := by
    ext U
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_powerset]
    exact and_comm
  refine hbase.trans_eq ?_
  exact_mod_cast (by
    simpa only [outsideN, N] using congrArg Finset.card hfilter)

/-- Correctly normalized outside-state count.  The common-nonneighbor
reservoir is forbidden in every outside state, so its `N.card` free Boolean
coordinates are removed here and restored only by the subsequent
conditional window count. -/
lemma card_outside_states_containing_switchingTuple_ge_of_outsides
    {n : ℕ}
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (S₀ : Finset (Fin n))
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (hpT : ∀ j, p j ∈ T) (hp : PairEndpointsDistinct p)
    (cores : Finset (Finset (Fin n)))
    (counts : Finset (Fin n) → RawTupleIndex labels a → ℕ)
    (D : ℕ) (C q : ℝ)
    (hblockPos : ∀ i, 1 ≤ (switchingPrivateNeighbors G p i S₀).card)
    (hblockHalf : ∀ i,
      1 ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hD : ∀ i,
      8 * D ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hcountsLe : ∀ O ∈ cores, ∀ i,
      counts O i ≤ (switchingPrivateNeighbors G p i S₀).card)
    (hcountsNear : ∀ O ∈ cores, ∀ i,
      Nat.dist (counts O i)
        ((switchingPrivateNeighbors G p i S₀).card / 2) ≤ D)
    (hquad : ∀ i, (D : ℝ) ^ 2 ≤
      C * ((switchingPrivateNeighbors G p i S₀).card / 2 : ℕ))
    (hq : 0 ≤ q)
    (hcoreCount :
      q * (2 : ℝ) ^
          (n - ((Finset.univ.biUnion fun i ↦
            switchingPrivateNeighbors G p i S₀) ∪
              switchingCommonNonneighbors G p S₀).card) ≤
        (cores.card : ℝ))
    (hcoreBlocks : ∀ O ∈ cores,
      Disjoint O (Finset.univ.biUnion
        (fun i ↦ switchingPrivateNeighbors G p i S₀)))
    (hcoreN : ∀ O ∈ cores,
      Disjoint O (switchingCommonNonneighbors G p S₀))
    (hy : ∀ O ∈ cores, ∀ j, (p j).1 ∈ O)
    (hz : ∀ O ∈ cores, ∀ j, (p j).2 ∉ O)
    (hrequired : ∀ O ∈ cores, ∀ j,
      (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) j +
          counts O j = (j.1.1 : ℝ)) :
    q * ((2 : ℝ) ^
          (n - (switchingCommonNonneighbors G p S₀).card) *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
          Fintype.card (RawTupleIndex labels a)) ≤
      ((((Finset.univ : Finset (Fin n)) \
          switchingCommonNonneighbors G p S₀).powerset.filter
        (fun U ↦ p ∈ switchingTupleFinset T (edgeScore G) labels a U)).card : ℝ) := by
  classical
  let N := switchingCommonNonneighbors G p S₀
  let blocks := Finset.univ.biUnion fun i ↦
    switchingPrivateNeighbors G p i S₀
  have hdisj : Disjoint blocks N := by
    rw [Finset.disjoint_left]
    intro x hxB hxN
    obtain ⟨i, _hi, hxi⟩ := Finset.mem_biUnion.mp hxB
    exact Finset.disjoint_left.mp
      (switchingCommonNonneighbors_disjoint_private G p S₀ i)
      hxN hxi
  have hcardUnion : (blocks ∪ N).card = blocks.card + N.card :=
    Finset.card_union_of_disjoint hdisj
  have hsumLe : blocks.card + N.card ≤ n := by
    rw [← hcardUnion]
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (blocks ∪ N))
  have hNleBlock : N.card ≤ n - blocks.card := by omega
  have hNle : N.card ≤ n := by omega
  let q' : ℝ := q / (2 : ℝ) ^ N.card
  have hq' : 0 ≤ q' := by positivity
  have hpowBlock :
      (2 : ℝ) ^ (n - blocks.card - N.card) =
        (2 : ℝ) ^ (n - blocks.card) * ((2 : ℝ) ^ N.card)⁻¹ :=
    pow_sub₀ (2 : ℝ) (by norm_num) hNleBlock
  have hcount' : q' * (2 : ℝ) ^ (n - blocks.card) ≤
      (cores.card : ℝ) := by
    calc
      q' * (2 : ℝ) ^ (n - blocks.card) =
          q * (2 : ℝ) ^ (n - blocks.card - N.card) := by
        rw [hpowBlock]
        dsimp only [q']
        field_simp
      _ = q * (2 : ℝ) ^ (n - (blocks ∪ N).card) := by
        rw [hcardUnion]
        congr 2
        omega
      _ ≤ (cores.card : ℝ) := by
        simpa only [blocks, N] using hcoreCount
  have hbase :=
    card_outside_states_containing_switchingTuple_ge_full_cube_normalization
      T G labels a S₀ p hpT hp cores counts D C q' hblockPos hblockHalf hD
        hcountsLe hcountsNear hquad
        (by simpa only [blocks] using hcount')
        hcoreBlocks hcoreN hy hz hrequired
  have hpowN :
      (2 : ℝ) ^ (n - N.card) =
        (2 : ℝ) ^ n * ((2 : ℝ) ^ N.card)⁻¹ :=
    pow_sub₀ (2 : ℝ) (by norm_num) hNle
  calc
    q * ((2 : ℝ) ^ (n - N.card) *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
          Fintype.card (RawTupleIndex labels a)) =
      q' * ((2 : ℝ) ^ n *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
          Fintype.card (RawTupleIndex labels a)) := by
      rw [hpowN]
      dsimp only [q']
      field_simp
    _ ≤ _ := by simpa only [N] using hbase

/-- Good private-block fibres can be counted entirely outside the common
reservoir while retaining an additional predicate needed by the later
conditional window step. -/
lemma card_outside_states_containing_switchingTuple_and_good_ge_of_goodFibers
    {n : ℕ}
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (S₀ : Finset (Fin n))
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (hpT : ∀ j, p j ∈ T) (hp : PairEndpointsDistinct p)
    (cores : Finset (Finset (Fin n)))
    (counts : Finset (Fin n) → RawTupleIndex labels a → ℕ)
    (D : ℕ) (C q qGood : ℝ) (hq : 0 ≤ q) (hqGood : 0 ≤ qGood)
    (hblockPos : ∀ i, 1 ≤ (switchingPrivateNeighbors G p i S₀).card)
    (hblockHalf : ∀ i,
      1 ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hD : ∀ i,
      8 * D ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hcountsLe : ∀ O ∈ cores, ∀ i,
      counts O i ≤ (switchingPrivateNeighbors G p i S₀).card)
    (hcountsNear : ∀ O ∈ cores, ∀ i,
      Nat.dist (counts O i)
        ((switchingPrivateNeighbors G p i S₀).card / 2) ≤ D)
    (hquad : ∀ i, (D : ℝ) ^ 2 ≤
      C * ((switchingPrivateNeighbors G p i S₀).card / 2 : ℕ))
    (hcoreCount :
      q * (2 : ℝ) ^
          (n - ((Finset.univ.biUnion fun i ↦
            switchingPrivateNeighbors G p i S₀) ∪
              switchingCommonNonneighbors G p S₀).card) ≤
        (cores.card : ℝ))
    (hcoreN : ∀ O ∈ cores,
      Disjoint O (switchingCommonNonneighbors G p S₀))
    (hy : ∀ O ∈ cores, ∀ j, (p j).1 ∈ O)
    (hz : ∀ O ∈ cores, ∀ j, (p j).2 ∉ O)
    (hrequired : ∀ O ∈ cores, ∀ j,
      (switchingDifferenceMatrix G p).mulVec (finsetIndicator O) j +
          counts O j = (j.1.1 : ℝ))
    (good : Finset (Fin n) → Prop)
    (hgoodFiber : ∀ O ∈ cores,
      qGood * (∏ i,
          (Nat.choose (switchingPrivateNeighbors G p i S₀).card
            (counts O i) : ℝ)) ≤
        (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
          U \ Finset.univ.biUnion
              (fun i ↦ switchingPrivateNeighbors G p i S₀) = O ∧
            (∀ i, (U ∩ switchingPrivateNeighbors G p i S₀).card =
              counts O i) ∧ good U).card : ℝ)) :
    (qGood * q) * ((2 : ℝ) ^
          (n - (switchingCommonNonneighbors G p S₀).card) *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
          Fintype.card (RawTupleIndex labels a)) ≤
      ((((Finset.univ : Finset (Fin n)) \
          switchingCommonNonneighbors G p S₀).powerset.filter
        (fun U ↦ p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          good U)).card : ℝ) := by
  classical
  let N := switchingCommonNonneighbors G p S₀
  let blocks := Finset.univ.biUnion fun i ↦
    switchingPrivateNeighbors G p i S₀
  let outsideN := (Finset.univ : Finset (Fin n)) \ N
  have hdisj : Disjoint blocks N := by
    rw [Finset.disjoint_left]
    intro x hxB hxN
    obtain ⟨i, _hi, hxi⟩ := Finset.mem_biUnion.mp hxB
    exact Finset.disjoint_left.mp
      (switchingCommonNonneighbors_disjoint_private G p S₀ i)
      hxN hxi
  have hcardUnion : (blocks ∪ N).card = blocks.card + N.card :=
    Finset.card_union_of_disjoint hdisj
  have hsumLe : blocks.card + N.card ≤ n := by
    rw [← hcardUnion]
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (blocks ∪ N))
  have hNleBlock : N.card ≤ n - blocks.card := by omega
  have hNle : N.card ≤ n := by omega
  let q' : ℝ := q / (2 : ℝ) ^ N.card
  have hq' : 0 ≤ q' := by positivity
  have hpowBlock :
      (2 : ℝ) ^ (n - blocks.card - N.card) =
        (2 : ℝ) ^ (n - blocks.card) * ((2 : ℝ) ^ N.card)⁻¹ :=
    pow_sub₀ (2 : ℝ) (by norm_num) hNleBlock
  have hcount' : q' * (2 : ℝ) ^ (n - blocks.card) ≤
      (cores.card : ℝ) := by
    calc
      q' * (2 : ℝ) ^ (n - blocks.card) =
          q * (2 : ℝ) ^ (n - blocks.card - N.card) := by
        rw [hpowBlock]
        dsimp only [q']
        field_simp
      _ = q * (2 : ℝ) ^ (n - (blocks ∪ N).card) := by
        rw [hcardUnion]
        congr 2
        omega
      _ ≤ (cores.card : ℝ) := by
        simpa only [blocks, N] using hcoreCount
  have hbase := card_states_containingSwitchingTuple_and_window_ge_of_goodFibers
    T G labels a S₀ p hpT hp cores counts D C q' qGood hqGood
      hblockPos hblockHalf hD hcountsLe hcountsNear hquad
      (by simpa only [blocks] using hcount') hy hz hrequired good
      (fun U ↦ U ⊆ outsideN ∧ good U)
      (by
        intro O hO
        exact hgoodFiber O hO)
      (by
        intro U hO _hcounts hgood
        refine ⟨?_, hgood⟩
        intro x hxU
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ x, ?_⟩
        intro hxN
        by_cases hxB : x ∈ blocks
        · obtain ⟨i, _hi, hxi⟩ := Finset.mem_biUnion.mp hxB
          exact Finset.disjoint_left.mp
            (switchingCommonNonneighbors_disjoint_private G p S₀ i)
            hxN hxi
        · have hxOutside : x ∈ U \ blocks :=
            Finset.mem_sdiff.mpr ⟨hxU, hxB⟩
          exact Finset.disjoint_left.mp
            (hcoreN _ hO) hxOutside hxN)
  have hpowN :
      (2 : ℝ) ^ (n - N.card) =
        (2 : ℝ) ^ n * ((2 : ℝ) ^ N.card)⁻¹ :=
    pow_sub₀ (2 : ℝ) (by norm_num) hNle
  calc
    (qGood * q) * ((2 : ℝ) ^ (n - N.card) *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
          Fintype.card (RawTupleIndex labels a)) =
      (qGood * q') * ((2 : ℝ) ^ n *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
          Fintype.card (RawTupleIndex labels a)) := by
        rw [hpowN]
        dsimp only [q']
        field_simp
    _ ≤ _ := by
      refine hbase.trans_eq ?_
      norm_cast
      apply congrArg Finset.card
      ext U
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_powerset]
      constructor
      · rintro ⟨htuple, hsub, hgood⟩
        exact ⟨hsub, htuple, hgood⟩
      · rintro ⟨hsub, htuple, hgood⟩
        exact ⟨htuple, hsub, hgood⟩

/-- The first-exposure event supplies all structural inputs to a private-block
good-fibre count, retaining the fibre predicate in the completed outside
state. -/
lemma card_outside_states_containing_switchingTuple_and_good_ge_of_firstExposure
    {n : ℕ}
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (S₀ : Finset (Fin n))
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (hpT : ∀ j, p j ∈ T) (hp : PairEndpointsDistinct p)
    (X : Finset (Fin n) → ℝ) (tMean tRow labelRadius : ℝ)
    (D : ℕ) (C q qGood : ℝ) (hq : 0 ≤ q) (hqGood : 0 ≤ qGood)
    (hlabel : ∀ i, |(i.1.1 : ℝ) -
        ((FiniteES.vertexDegree G (p i).2 : ℝ) -
          (FiniteES.vertexDegree G (p i).1 : ℝ)) / 2| ≤ labelRadius)
    (hRadius : labelRadius + tRow + 1 / 2 ≤ (D : ℝ))
    (hblockPos : ∀ i, 1 ≤ (switchingPrivateNeighbors G p i S₀).card)
    (hblockHalf : ∀ i,
      1 ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hD : ∀ i,
      8 * D ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hquad : ∀ i, (D : ℝ) ^ 2 ≤
      C * ((switchingPrivateNeighbors G p i S₀).card / 2 : ℕ))
    (hcoreCount :
      q * (2 : ℝ) ^
          (n - ((Finset.univ.biUnion fun i ↦
            switchingPrivateNeighbors G p i S₀) ∪
              switchingCommonNonneighbors G p S₀).card) ≤
        ((switchingFirstExposureGood G p S₀ X tMean tRow).card : ℝ))
    (good : Finset (Fin n) → Prop)
    (hgoodFiber : ∀ O ∈ switchingFirstExposureGood G p S₀ X tMean tRow,
      qGood * (∏ i,
          (Nat.choose (switchingPrivateNeighbors G p i S₀).card
            (switchingRequiredPrivateCount G p O
              (fun j : RawTupleIndex labels a ↦ j.1.1) i) : ℝ)) ≤
        (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
          U \ Finset.univ.biUnion
              (fun i ↦ switchingPrivateNeighbors G p i S₀) = O ∧
            (∀ i, (U ∩ switchingPrivateNeighbors G p i S₀).card =
              switchingRequiredPrivateCount G p O
                (fun j : RawTupleIndex labels a ↦ j.1.1) i) ∧
            good U).card : ℝ)) :
    (qGood * q) * ((2 : ℝ) ^
          (n - (switchingCommonNonneighbors G p S₀).card) *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
          Fintype.card (RawTupleIndex labels a)) ≤
      ((((Finset.univ : Finset (Fin n)) \
          switchingCommonNonneighbors G p S₀).powerset.filter
        (fun U ↦ p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          good U)).card : ℝ) := by
  let cores := switchingFirstExposureGood G p S₀ X tMean tRow
  let count := fun O : Finset (Fin n) ↦
    switchingRequiredPrivateCount G p O
      (fun i : RawTupleIndex labels a ↦ i.1.1)
  apply card_outside_states_containing_switchingTuple_and_good_ge_of_goodFibers
    T G labels a S₀ p hpT hp cores count D C q qGood hq hqGood
  · exact hblockPos
  · exact hblockHalf
  · exact hD
  · intro O hO i
    exact (switchingFirstExposureGood_privateCounts
      G p S₀ hp X tMean tRow labelRadius D
        (fun i : RawTupleIndex labels a ↦ i.1.1) hlabel hRadius
        (fun i ↦ (Nat.le_trans (by omega) (hD i))) hO i).1
  · intro O hO i
    exact (switchingFirstExposureGood_privateCounts
      G p S₀ hp X tMean tRow labelRadius D
        (fun i : RawTupleIndex labels a ↦ i.1.1) hlabel hRadius
        (fun i ↦ (Nat.le_trans (by omega) (hD i))) hO i).2.1
  · exact hquad
  · simpa only [cores] using hcoreCount
  · intro O hO
    exact (switchingFirstExposureGood_core_properties
      G p S₀ X tMean tRow hO).2.1
  · intro O hO i
    exact (switchingFirstExposureGood_core_properties
      G p S₀ X tMean tRow hO).2.2.1 i
  · intro O hO i
    exact (switchingFirstExposureGood_core_properties
      G p S₀ X tMean tRow hO).2.2.2 i
  · intro O hO i
    exact (switchingFirstExposureGood_privateCounts
      G p S₀ hp X tMean tRow labelRadius D
        (fun i : RawTupleIndex labels a ↦ i.1.1) hlabel hRadius
        (fun i ↦ (Nat.le_trans (by omega) (hD i))) hO i).2.2
  · exact hgoodFiber

/-- The first-exposure event supplies every structural and arithmetic input
to the private-block outside-state count. -/
lemma card_outside_states_containing_switchingTuple_ge_of_firstExposure
    {n : ℕ}
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (S₀ : Finset (Fin n))
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (hpT : ∀ j, p j ∈ T) (hp : PairEndpointsDistinct p)
    (X : Finset (Fin n) → ℝ) (tMean tRow labelRadius : ℝ)
    (D : ℕ) (C q : ℝ)
    (hlabel : ∀ i, |(i.1.1 : ℝ) -
        ((FiniteES.vertexDegree G (p i).2 : ℝ) -
          (FiniteES.vertexDegree G (p i).1 : ℝ)) / 2| ≤ labelRadius)
    (hRadius : labelRadius + tRow + 1 / 2 ≤ (D : ℝ))
    (hblockPos : ∀ i, 1 ≤ (switchingPrivateNeighbors G p i S₀).card)
    (hblockHalf : ∀ i,
      1 ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hD : ∀ i,
      8 * D ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hquad : ∀ i, (D : ℝ) ^ 2 ≤
      C * ((switchingPrivateNeighbors G p i S₀).card / 2 : ℕ))
    (hq : 0 ≤ q)
    (hcoreCount :
      q * (2 : ℝ) ^
          (n - ((Finset.univ.biUnion fun i ↦
            switchingPrivateNeighbors G p i S₀) ∪
              switchingCommonNonneighbors G p S₀).card) ≤
        ((switchingFirstExposureGood G p S₀ X tMean tRow).card : ℝ)) :
    q * ((2 : ℝ) ^
          (n - (switchingCommonNonneighbors G p S₀).card) *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
          Fintype.card (RawTupleIndex labels a)) ≤
      ((((Finset.univ : Finset (Fin n)) \
          switchingCommonNonneighbors G p S₀).powerset.filter
        (fun U ↦ p ∈ switchingTupleFinset T (edgeScore G) labels a U)).card : ℝ) := by
  let good := switchingFirstExposureGood G p S₀ X tMean tRow
  let count := fun O : Finset (Fin n) ↦
    switchingRequiredPrivateCount G p O
      (fun i : RawTupleIndex labels a ↦ i.1.1)
  apply card_outside_states_containing_switchingTuple_ge_of_outsides
    T G labels a S₀ p hpT hp good count D C q
  · exact hblockPos
  · exact hblockHalf
  · exact hD
  · intro O hO i
    exact (switchingFirstExposureGood_privateCounts
      G p S₀ hp X tMean tRow labelRadius D
        (fun i : RawTupleIndex labels a ↦ i.1.1) hlabel hRadius
        (fun i ↦ (Nat.le_trans (by omega) (hD i))) hO i).1
  · intro O hO i
    exact (switchingFirstExposureGood_privateCounts
      G p S₀ hp X tMean tRow labelRadius D
        (fun i : RawTupleIndex labels a ↦ i.1.1) hlabel hRadius
        (fun i ↦ (Nat.le_trans (by omega) (hD i))) hO i).2.1
  · exact hquad
  · exact hq
  · simpa only [good] using hcoreCount
  · intro O hO
    exact (switchingFirstExposureGood_core_properties
      G p S₀ X tMean tRow hO).1
  · intro O hO
    exact (switchingFirstExposureGood_core_properties
      G p S₀ X tMean tRow hO).2.1
  · intro O hO i
    exact (switchingFirstExposureGood_core_properties
      G p S₀ X tMean tRow hO).2.2.1 i
  · intro O hO i
    exact (switchingFirstExposureGood_core_properties
      G p S₀ X tMean tRow hO).2.2.2 i
  · intro O hO i
    exact (switchingFirstExposureGood_privateCounts
      G p S₀ hp X tMean tRow labelRadius D
        (fun i : RawTupleIndex labels a ↦ i.1.1) hlabel hRadius
        (fun i ↦ (Nat.le_trans (by omega) (hD i))) hO i).2.2

/-- Fully normalized outside-state count obtained directly from the
first-exposure Chebyshev rate. -/
lemma card_outside_states_containing_switchingTuple_ge_of_firstExposureRate
    {n : ℕ}
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (S₀ : Finset (Fin n))
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (hpT : ∀ j, p j ∈ T) (hp : PairEndpointsDistinct p)
    (X : Finset (Fin n) → ℝ) (tMean tRow labelRadius : ℝ)
    (D : ℕ) (C : ℝ)
    (htMean : 0 < tMean) (htRow : 0 < tRow)
    (hroom : 2 * Fintype.card (RawTupleIndex labels a) ≤
      (switchingFirstExposureDomain G p S₀).card)
    (hrate : 0 ≤ switchingFirstExposureRate G p S₀ X tMean tRow)
    (hlabel : ∀ i, |(i.1.1 : ℝ) -
        ((FiniteES.vertexDegree G (p i).2 : ℝ) -
          (FiniteES.vertexDegree G (p i).1 : ℝ)) / 2| ≤ labelRadius)
    (hRadius : labelRadius + tRow + 1 / 2 ≤ (D : ℝ))
    (hblockPos : ∀ i, 1 ≤ (switchingPrivateNeighbors G p i S₀).card)
    (hblockHalf : ∀ i,
      1 ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hD : ∀ i,
      8 * D ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hquad : ∀ i, (D : ℝ) ^ 2 ≤
      C * ((switchingPrivateNeighbors G p i S₀).card / 2 : ℕ)) :
    switchingFirstExposureRate G p S₀ X tMean tRow *
        ((2 : ℝ) ^
          (n - (switchingCommonNonneighbors G p S₀).card) *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
          Fintype.card (RawTupleIndex labels a)) ≤
      ((((Finset.univ : Finset (Fin n)) \
          switchingCommonNonneighbors G p S₀).powerset.filter
        (fun U ↦ p ∈ switchingTupleFinset T (edgeScore G) labels a U)).card : ℝ) := by
  apply card_outside_states_containing_switchingTuple_ge_of_firstExposure
    T G labels a S₀ p hpT hp X tMean tRow labelRadius D C
      (switchingFirstExposureRate G p S₀ X tMean tRow)
      hlabel hRadius hblockPos hblockHalf hD hquad hrate
  have hcount := card_switchingFirstExposureGood_ge_rate
    G p S₀ hp X tMean tRow htMean htRow hroom
  rw [card_switchingFirstExposureDomain G p S₀] at hcount
  exact hcount

/-- Multiply an outside switching-state lower bound by a uniform conditional
window lower bound on the common-nonneighbor reservoir. -/
lemma card_states_containing_switchingTuple_and_window_ge_of_conditional
    {n : ℕ}
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ)
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (S₀ : Finset (Fin n)) (window : Finset (Fin n) → Prop)
    (outsideLower windowLower : ℝ) (hwindowLower : 0 ≤ windowLower)
    (houtside : outsideLower ≤
      ((((Finset.univ : Finset (Fin n)) \
          switchingCommonNonneighbors G p S₀).powerset.filter fun O ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a O).card : ℝ))
    (hwindow : ∀ O ∈ (((Finset.univ : Finset (Fin n)) \
        switchingCommonNonneighbors G p S₀).powerset.filter fun O ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a O),
      windowLower ≤
        (((switchingCommonNonneighbors G p S₀).powerset.filter fun R ↦
          window (O ∪ R)).card : ℝ)) :
    outsideLower * windowLower ≤
      (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          window U).card : ℝ) := by
  have hconditional :=
    card_states_containing_switchingTuple_and_window_ge_conditional
      T G labels a p S₀ window windowLower hwindow
  exact (mul_le_mul_of_nonneg_right houtside hwindowLower).trans hconditional

/-- Source-normalized product of the outside private-block count and the
conditional common-nonneighbor window count.  The two Boolean-cube factors
multiply back to `2^n` exactly. -/
lemma card_states_containing_switchingTuple_and_window_ge_of_normalized_factors
    {n : ℕ}
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ)
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (S₀ : Finset (Fin n)) (window : Finset (Fin n) → Prop)
    (q privateFactor windowRate : ℝ) (hwindowRate : 0 ≤ windowRate)
    (houtside :
      q * ((2 : ℝ) ^
          (n - (switchingCommonNonneighbors G p S₀).card) *
            privateFactor) ≤
        ((((Finset.univ : Finset (Fin n)) \
            switchingCommonNonneighbors G p S₀).powerset.filter fun O ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a O).card : ℝ))
    (hwindow : ∀ O ∈ (((Finset.univ : Finset (Fin n)) \
        switchingCommonNonneighbors G p S₀).powerset.filter fun O ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a O),
      (2 : ℝ) ^ (switchingCommonNonneighbors G p S₀).card * windowRate ≤
        (((switchingCommonNonneighbors G p S₀).powerset.filter fun R ↦
          window (O ∪ R)).card : ℝ)) :
    q * windowRate * ((2 : ℝ) ^ n * privateFactor) ≤
      (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          window U).card : ℝ) := by
  let N := switchingCommonNonneighbors G p S₀
  have hNle : N.card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ N)
  have hpow : (2 : ℝ) ^ (n - N.card) * (2 : ℝ) ^ N.card =
      (2 : ℝ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hNle]
  have hcombined :=
    card_states_containing_switchingTuple_and_window_ge_of_conditional
      T G labels a p S₀ window
      (q * ((2 : ℝ) ^ (n - N.card) * privateFactor))
      ((2 : ℝ) ^ N.card * windowRate)
      (mul_nonneg (by positivity) hwindowRate)
      (by simpa only [N] using houtside)
      (by simpa only [N] using hwindow)
  calc
    q * windowRate * ((2 : ℝ) ^ n * privateFactor) =
        (q * ((2 : ℝ) ^ (n - N.card) * privateFactor)) *
          ((2 : ℝ) ^ N.card * windowRate) := by
      rw [← hpow]
      ring
    _ ≤ _ := hcombined

/-- Lower raw-moment assembly for KSSS Lemma 13.4.  The good-tuple count
supplies the factor `|T|^s / 2`; for every good tuple the correctly
normalized outside count and the conditional common-nonneighbor count
recombine to the full Boolean-cube factor. -/
lemma rawMoment_switchingCount_ge_of_good_tuples_and_normalized_factors
    {n : ℕ}
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (S₀ : Finset (Fin n))
    (privateLower C q windowRate : ℝ)
    (hq : 0 ≤ q) (hwindowRate : 0 ≤ windowRate)
    (hgood : T.card ^ Fintype.card (RawTupleIndex labels a) ≤
      2 * (goodSwitchingTupleClass T G labels a S₀ privateLower).card)
    (window : Finset (Fin n) → Prop)
    (houtside : ∀ p ∈ goodSwitchingTupleClass
        T G labels a S₀ privateLower,
      q * ((2 : ℝ) ^
          (n - (switchingCommonNonneighbors G p S₀).card) *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
          Fintype.card (RawTupleIndex labels a)) ≤
        ((((Finset.univ : Finset (Fin n)) \
            switchingCommonNonneighbors G p S₀).powerset.filter fun O ↦
          p ∈ switchingTupleFinset T (edgeScore G) labels a O).card : ℝ))
    (hwindow : ∀ p ∈ goodSwitchingTupleClass
        T G labels a S₀ privateLower,
      ∀ O ∈ (((Finset.univ : Finset (Fin n)) \
          switchingCommonNonneighbors G p S₀).powerset.filter fun O ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a O),
        (2 : ℝ) ^ (switchingCommonNonneighbors G p S₀).card *
            windowRate ≤
          (((switchingCommonNonneighbors G p S₀).powerset.filter fun R ↦
            window (O ∪ R)).card : ℝ)) :
    ((T.card : ℝ) ^ Fintype.card (RawTupleIndex labels a) / 2) *
        (q * windowRate *
          ((2 : ℝ) ^ n *
            (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
              Fintype.card (RawTupleIndex labels a))) ≤
      rawMoment (Finset.univ : Finset (Finset (Fin n))) window
        (fun ell U ↦ (switchingCount T (edgeScore G) ell U : ℝ))
        a labels := by
  let privateFactor :=
    (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
      Fintype.card (RawTupleIndex labels a)
  have hprivateFactor : 0 ≤ privateFactor := by
    dsimp only [privateFactor]
    positivity
  apply rawMoment_switchingCount_ge_of_good_tuple_count_and_state_bound
    G T labels a S₀ privateLower hgood window
      (q * windowRate * ((2 : ℝ) ^ n * privateFactor))
  · positivity
  · intro p hp
    apply card_states_containing_switchingTuple_and_window_ge_of_normalized_factors
      T G labels a p S₀ window q privateFactor windowRate hwindowRate
    · simpa only [privateFactor] using houtside p hp
    · exact hwindow p hp

/-- The graph induced on the union of the private blocks, canonically
reindexed by a finite interval. -/
noncomputable def privateBlockGraph {n : ℕ} {I : Type*} [Fintype I]
    (W : I → Finset (Fin n)) (G : SimpleGraph (Fin n)) :
    SimpleGraph (Fin (Finset.univ.biUnion W).card) :=
  (G.induce (Finset.univ.biUnion W : Set (Fin n))).comap
    (blockUnionVertexEquiv W)

/-- Constant term after conditioning a perturbed edge polynomial on the
fixed outside assignment. -/
noncomputable def privateBlockConstant {n : ℕ}
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (O : Finset (Fin n)) : ℝ :=
  Probability.perturbedEdgePolynomial G e₀ c O

/-- Linear coefficient on a private-block vertex after conditioning on the
outside assignment. -/
noncomputable def privateBlockCoefficient {n : ℕ} {I : Type*} [Fintype I]
    (W : I → Finset (Fin n)) (G : SimpleGraph (Fin n))
    (c : Fin n → ℝ) (O : Finset (Fin n))
    (i : Fin (Finset.univ.biUnion W).card) : ℝ :=
  c (blockUnionVertexEquiv W i).1 +
    AKSGraph.degreeInto G (blockUnionVertexEquiv W i).1 O

/-- Fair-cube mean of the conditioned polynomial on the union of the private
blocks. -/
noncomputable def privateBlockMean {n : ℕ} {I : Type*} [Fintype I]
    (W : I → Finset (Fin n)) (G : SimpleGraph (Fin n))
    (e₀ : ℝ) (c : Fin n → ℝ) (O : Finset (Fin n)) : ℝ :=
  Probability.expectation (1 / 2 : ℝ)
    (Probability.perturbedEdgePolynomial (privateBlockGraph W G)
      (privateBlockConstant G e₀ c O) (privateBlockCoefficient W G c O))

/-- KSSS Lemma 13.6(2) on the private-block union after a fixed outside
exposure.  The complement bucket disappears after reindexing the union, so
the count is exactly a fraction of the product of the prescribed binomial
coefficients. -/
lemma card_fixedOutside_privateBlockSlice_centered_window_lower
    {n m : ℕ}
    (W : Fin m → Finset (Fin n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (O : Finset (Fin n))
    (hO : Disjoint O (Finset.univ.biUnion W))
    (ell : Fin m → ℕ) (hell : ∀ k, ell k ≤ (W k).card)
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (R : ℝ) (hR : 1 ≤ R)
    (hc : ∀ v ∈ Finset.univ.biUnion W,
      |c v + AKSGraph.degreeInto G v O| ≤
        R * (Finset.univ.biUnion W).card)
    (A B D t : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (ht : 0 < t)
    (hellCenter : ∀ k,
      |(ell k : ℝ) - ((W k).card : ℝ) / 2| ≤ A) :
    let W' := reindexedBlock W
    let outside := (Finset.univ : Finset
      (Fin (Finset.univ.biUnion W).card)) \ Finset.univ.biUnion W'
    let q := 1 -
        (R ^ 2 * ((Finset.univ.biUnion W).card : ℝ) ^ 3) / t ^ 2 -
        ((∑ k : Fin m, binomialTailBound (W' k) D) +
          binomialTailBound outside D) -
        binomialTailBound outside B
    q * (∏ k : Fin m, ((W k).card.choose (ell k) : ℝ)) ≤
      (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        U \ Finset.univ.biUnion W = O ∧
          (∀ k, (U ∩ W k).card = ell k) ∧
          |Probability.perturbedEdgePolynomial G e₀ c U -
            privateBlockMean W G e₀ c O| <
              t + (((m + 1 : ℕ) : ℝ) * (max A B + D)) *
                ((R + 1) * (Finset.univ.biUnion W).card)).card : ℝ) := by
  classical
  let W' := reindexedBlock W
  let outside := (Finset.univ : Finset
    (Fin (Finset.univ.biUnion W).card)) \ Finset.univ.biUnion W'
  let q := 1 -
      (R ^ 2 * ((Finset.univ.biUnion W).card : ℝ) ^ 3) / t ^ 2 -
      ((∑ k : Fin m, binomialTailBound (W' k) D) +
        binomialTailBound outside D) -
      binomialTailBound outside B
  have hdisj' : ∀ i j, i ≠ j → Disjoint (W' i) (W' j) := by
    intro i j hij
    exact reindexedBlock_pairwiseDisjoint W
      (by intro i _hi j _hj hij; exact hdisj i j hij)
      (Set.mem_univ i) (Set.mem_univ j) hij
  have hell' : ∀ k, ell k ≤ (W' k).card := by
    intro k
    simpa only [W', card_reindexedBlock] using hell k
  have hc' : ∀ i, |privateBlockCoefficient W G c O i| ≤
      R * (Finset.univ.biUnion W).card := by
    intro i
    apply hc
    exact (blockUnionVertexEquiv W i).2
  have hcenter' : ∀ k,
      |(ell k : ℝ) - ((W' k).card : ℝ) / 2| ≤ A := by
    intro k
    simpa only [W', card_reindexedBlock] using hellCenter k
  have hbase := card_prescribedFamilySlice_centered_window_lower
    W' hdisj' ell hell' (privateBlockGraph W G)
      (privateBlockConstant G e₀ c O) (privateBlockCoefficient W G c O)
      R hR hc' A B D t hB hD ht hcenter'
  let source := (Finset.univ : Finset
      (PrescribedFamilySlicePoint (reindexedBlock W) ell)).filter fun S ↦
    |Probability.perturbedEdgePolynomial (privateBlockGraph W G)
        (privateBlockConstant G e₀ c O) (privateBlockCoefficient W G c O) S.1 -
      privateBlockMean W G e₀ c O| <
        t + (((m + 1 : ℕ) : ℝ) * (max A B + D)) *
          ((R + 1) * (Finset.univ.biUnion W).card)
  let target := (Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
    U \ Finset.univ.biUnion W = O ∧
      (∀ k, (U ∩ W k).card = ell k) ∧
      |Probability.perturbedEdgePolynomial G e₀ c U -
        privateBlockMean W G e₀ c O| <
          t + (((m + 1 : ℕ) : ℝ) * (max A B + D)) *
            ((R + 1) * (Finset.univ.biUnion W).card)
  have hsourceTarget : source.card ≤ target.card := by
    apply Finset.card_le_card_of_injOn
      (fun S : PrescribedFamilySlicePoint (reindexedBlock W) ell ↦
        fixedOutsideReindexedSliceMap W O S.1)
    · intro S hS
      have hS' := (Finset.mem_filter.mp hS).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, fixedOutsideReindexedSliceMap_sdiff W O hO S.1,
        ?_, ?_⟩
      · intro k
        rw [fixedOutsideReindexedSliceMap_inter_block W O hO S.1 k]
        simpa only [W'] using S.2 k
      · have hBsub := reindexedSubsetImage_subset W S.1
        have hOB : Disjoint O (reindexedSubsetImage W S.1) :=
          hO.mono_right hBsub
        have hpolyUnion := perturbedEdgePolynomial_union_of_disjoint
          G e₀ c hOB
        have hpolyReindex := perturbedEdgePolynomial_reindexedSubsetImage
          W G (privateBlockConstant G e₀ c O)
            (fun v ↦ c v + AKSGraph.degreeInto G v O) S.1
        have hpoly :
            Probability.perturbedEdgePolynomial G e₀ c
                (fixedOutsideReindexedSliceMap W O S.1) =
              Probability.perturbedEdgePolynomial (privateBlockGraph W G)
                (privateBlockConstant G e₀ c O)
                (privateBlockCoefficient W G c O) S.1 := by
          calc
            Probability.perturbedEdgePolynomial G e₀ c
                (fixedOutsideReindexedSliceMap W O S.1) =
                Probability.perturbedEdgePolynomial G e₀ c
                  (O ∪ reindexedSubsetImage W S.1) := rfl
            _ = Probability.perturbedEdgePolynomial G
                (Probability.perturbedEdgePolynomial G e₀ c O)
                (fun v ↦ c v + AKSGraph.degreeInto G v O)
                  (reindexedSubsetImage W S.1) := hpolyUnion
            _ = Probability.perturbedEdgePolynomial (privateBlockGraph W G)
                (privateBlockConstant G e₀ c O)
                (privateBlockCoefficient W G c O) S.1 := by
              convert hpolyReindex.symm using 1 <;> rfl
        rw [hpoly]
        exact hS'
    · intro S _hS T _hT hEq
      apply Subtype.ext
      exact fixedOutsideReindexedSliceMap_injective W O hO hEq
  have hbase' :
      q * (((∏ k : Fin m, (W' k).card.choose (ell k)) *
          2 ^ ((Finset.univ.biUnion W).card -
            (Finset.univ.biUnion W').card) : ℕ) : ℝ) ≤ source.card := by
    convert hbase using 1 <;> rfl
  have hUnion : Finset.univ.biUnion W' = Finset.univ := by
    simpa only [W'] using biUnion_reindexedBlock_eq_univ W
  have hfactor :
      (((∏ k : Fin m, (W' k).card.choose (ell k)) *
          2 ^ ((Finset.univ.biUnion W).card -
            (Finset.univ.biUnion W').card) : ℕ) : ℝ) =
        ∏ k : Fin m, ((W k).card.choose (ell k) : ℝ) := by
    rw [hUnion]
    simp only [Finset.card_univ, Fintype.card_fin, Nat.sub_self,
      pow_zero, mul_one]
    push_cast
    apply Finset.prod_congr rfl
    intro k _hk
    simp only [W', card_reindexedBlock]
  rw [← hfactor]
  exact hbase'.trans (by exact_mod_cast hsourceTarget)

/-- The private-neighbor family, canonically indexed by a finite interval so
that the finite-family form of Lemma 13.6(2) applies directly. -/
noncomputable def switchingPrivateBlocksFin
    {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V) :
    Fin (Fintype.card I) → Finset V :=
  fun k ↦ switchingPrivateNeighbors G p ((Fintype.equivFin I).symm k) S₀

lemma biUnion_switchingPrivateBlocksFin
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) (p : I → V × V) (S₀ : Finset V) :
    Finset.univ.biUnion (switchingPrivateBlocksFin G p S₀) =
      Finset.univ.biUnion fun i ↦ switchingPrivateNeighbors G p i S₀ := by
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨(Fintype.equivFin I).symm k,
      by simpa only [switchingPrivateBlocksFin] using hk⟩
  · rintro ⟨i, hi⟩
    refine ⟨Fintype.equivFin I i, ?_⟩
    simpa only [switchingPrivateBlocksFin, Equiv.symm_apply_apply] using hi

/-- Conditional mean after the first exposure: average the outside-
reservoir polynomial over all private blocks. -/
noncomputable def switchingFirstExposureMeanPolynomial
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (S₀ O : Finset (Fin n)) : ℝ :=
  let N := switchingCommonNonneighbors G p S₀
  privateBlockMean (switchingPrivateBlocksFin G p S₀)
    (outsideGraph G N) ((AKSGraph.edgeCount G N : ℝ) / 4)
    (fun v ↦ if v ∈ N then 0 else
      (AKSGraph.degreeInto G v N : ℝ) / 2) O

lemma abs_natCast_sub_realHalf_le_of_dist_le
    {x b D : ℕ} (h : Nat.dist x (b / 2) ≤ D) :
    |(x : ℝ) - (b : ℝ) / 2| ≤ (D : ℝ) + 1 / 2 := by
  calc
    |(x : ℝ) - (b : ℝ) / 2| =
        |((x : ℝ) - ((b / 2 : ℕ) : ℝ)) +
          (((b / 2 : ℕ) : ℝ) - (b : ℝ) / 2)| := by ring_nf
    _ ≤ |(x : ℝ) - ((b / 2 : ℕ) : ℝ)| +
        |((b / 2 : ℕ) : ℝ) - (b : ℝ) / 2| := abs_add_le _ _
    _ ≤ (D : ℝ) + 1 / 2 := by
      gcongr
      · rw [← natCast_dist_eq_abs_sub]
        exact_mod_cast h
      · exact abs_natHalf_cast_sub_realHalf_le b

/-- Lemma 13.6(2), applied fibrewise after the canonical first exposure.
The retained outside states have their full outside-reservoir conditional
mean close to the first-exposure conditional mean. -/
lemma card_outside_states_containing_switchingTuple_and_mean_close_ge_of_firstExposure
    {n : ℕ}
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (S₀ : Finset (Fin n))
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (hpT : ∀ j, p j ∈ T) (hp : PairEndpointsDistinct p)
    (tMean tRow labelRadius : ℝ)
    (D : ℕ) (C q R B Δ t : ℝ) (hq : 0 ≤ q)
    (hR : 1 ≤ R) (hB : 0 ≤ B) (hΔ : 0 ≤ Δ) (ht : 0 < t)
    (hqPrivate : 0 ≤
      1 - (R ^ 2 * ((Finset.univ.biUnion
          (switchingPrivateBlocksFin G p S₀)).card : ℝ) ^ 3) / t ^ 2 -
        ((∑ k, binomialTailBound
            (reindexedBlock (switchingPrivateBlocksFin G p S₀) k) Δ) +
          binomialTailBound
            ((Finset.univ : Finset (Fin (Finset.univ.biUnion
              (switchingPrivateBlocksFin G p S₀)).card)) \
                Finset.univ.biUnion
                  (reindexedBlock (switchingPrivateBlocksFin G p S₀))) Δ) -
        binomialTailBound
          ((Finset.univ : Finset (Fin (Finset.univ.biUnion
            (switchingPrivateBlocksFin G p S₀)).card)) \
              Finset.univ.biUnion
                (reindexedBlock (switchingPrivateBlocksFin G p S₀))) B)
    (hlabel : ∀ i, |(i.1.1 : ℝ) -
        ((FiniteES.vertexDegree G (p i).2 : ℝ) -
          (FiniteES.vertexDegree G (p i).1 : ℝ)) / 2| ≤ labelRadius)
    (hRadius : labelRadius + tRow + 1 / 2 ≤ (D : ℝ))
    (hblockPos : ∀ i, 1 ≤ (switchingPrivateNeighbors G p i S₀).card)
    (hblockHalf : ∀ i,
      1 ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hD : ∀ i,
      8 * D ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hquad : ∀ i, (D : ℝ) ^ 2 ≤
      C * ((switchingPrivateNeighbors G p i S₀).card / 2 : ℕ))
    (hcoreCount :
      q * (2 : ℝ) ^
          (n - ((Finset.univ.biUnion fun i ↦
            switchingPrivateNeighbors G p i S₀) ∪
              switchingCommonNonneighbors G p S₀).card) ≤
        ((switchingFirstExposureGood G p S₀
          (switchingFirstExposureMeanPolynomial G p S₀)
          tMean tRow).card : ℝ))
    (hMean : Probability.expectation (1 / 2 : ℝ)
        (fun R : Finset (switchingFirstExposureDomain G p S₀ : Set (Fin n)) ↦
          switchingFirstExposureMeanPolynomial G p S₀
            (BoundedWindow.subtypeSubsetImage
              (switchingFirstExposureDomain G p S₀) R)) =
      Probability.expectation (1 / 2 : ℝ)
        (Probability.edgePolynomial G))
    (hc : ∀ O ∈ switchingFirstExposureGood G p S₀
        (switchingFirstExposureMeanPolynomial G p S₀) tMean tRow,
      ∀ v ∈ Finset.univ.biUnion (switchingPrivateBlocksFin G p S₀),
        |(if v ∈ switchingCommonNonneighbors G p S₀ then 0 else
              (AKSGraph.degreeInto G v
                (switchingCommonNonneighbors G p S₀) : ℝ) / 2) +
            AKSGraph.degreeInto
              (outsideGraph G (switchingCommonNonneighbors G p S₀)) v O| ≤
          R * (Finset.univ.biUnion
            (switchingPrivateBlocksFin G p S₀)).card) :
    let W := switchingPrivateBlocksFin G p S₀
    let W' := reindexedBlock W
    let outside := (Finset.univ : Finset
      (Fin (Finset.univ.biUnion W).card)) \ Finset.univ.biUnion W'
    let qPrivate := 1 -
        (R ^ 2 * ((Finset.univ.biUnion W).card : ℝ) ^ 3) / t ^ 2 -
        ((∑ k, binomialTailBound (W' k) Δ) +
          binomialTailBound outside Δ) -
        binomialTailBound outside B
    let radius := t +
      (((Fintype.card (RawTupleIndex labels a) + 1 : ℕ) : ℝ) *
        (max ((D : ℝ) + 1 / 2) B + Δ)) *
          ((R + 1) * (Finset.univ.biUnion W).card)
    (qPrivate * q) * ((2 : ℝ) ^
          (n - (switchingCommonNonneighbors G p S₀).card) *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
          Fintype.card (RawTupleIndex labels a)) ≤
      ((((Finset.univ : Finset (Fin n)) \
          switchingCommonNonneighbors G p S₀).powerset.filter
        (fun U ↦ p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          |outsideConditionalMeanPolynomial G
              (switchingCommonNonneighbors G p S₀) U -
            Probability.expectation (1 / 2 : ℝ)
              (Probability.edgePolynomial G)| < radius + tMean)).card : ℝ) := by
  classical
  let I := RawTupleIndex labels a
  let N := switchingCommonNonneighbors G p S₀
  let W := switchingPrivateBlocksFin G p S₀
  let W' := reindexedBlock W
  let outside := (Finset.univ : Finset
    (Fin (Finset.univ.biUnion W).card)) \ Finset.univ.biUnion W'
  let qPrivate := 1 -
      (R ^ 2 * ((Finset.univ.biUnion W).card : ℝ) ^ 3) / t ^ 2 -
      ((∑ k, binomialTailBound (W' k) Δ) +
        binomialTailBound outside Δ) -
      binomialTailBound outside B
  let radius := t +
    (((Fintype.card I + 1 : ℕ) : ℝ) *
      (max ((D : ℝ) + 1 / 2) B + Δ)) *
        ((R + 1) * (Finset.univ.biUnion W).card)
  let X := switchingFirstExposureMeanPolynomial G p S₀
  let good := fun U : Finset (Fin n) ↦
    |outsideConditionalMeanPolynomial G N U -
      Probability.expectation (1 / 2 : ℝ)
        (Probability.edgePolynomial G)| < radius + tMean
  apply card_outside_states_containing_switchingTuple_and_good_ge_of_firstExposure
    T G labels a S₀ p hpT hp X tMean tRow labelRadius D C q qPrivate
      hq (by simpa only [qPrivate, W, W', outside] using hqPrivate)
      hlabel hRadius hblockPos
      hblockHalf hD hquad (by simpa only [X] using hcoreCount) good
  intro O hO
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let ell : Fin (Fintype.card I) → ℕ := fun k ↦
    switchingRequiredPrivateCount G p O
      (fun j : RawTupleIndex labels a ↦ j.1.1) (e k)
  have hUnion : Finset.univ.biUnion W =
      Finset.univ.biUnion fun i ↦ switchingPrivateNeighbors G p i S₀ := by
    simpa only [W] using biUnion_switchingPrivateBlocksFin G p S₀
  have hdisjW : ∀ i j, i ≠ j → Disjoint (W i) (W j) := by
    intro i j hij
    exact switchingPrivateNeighbors_pairwise_disjoint G p S₀ hp
      (fun h ↦ hij (e.injective h))
  have hprops := switchingFirstExposureGood_core_properties
    G p S₀ X tMean tRow hO
  have hcount := switchingFirstExposureGood_privateCounts
    G p S₀ hp X tMean tRow labelRadius D
      (fun i : RawTupleIndex labels a ↦ i.1.1) hlabel hRadius
      (fun i ↦ (Nat.le_trans (by omega) (hD i))) hO
  have hfixed := card_fixedOutside_privateBlockSlice_centered_window_lower
    W hdisjW O (by simpa only [hUnion] using hprops.1) ell
      (fun k ↦ (hcount (e k)).1)
      (outsideGraph G N) ((AKSGraph.edgeCount G N : ℝ) / 4)
      (fun v ↦ if v ∈ N then 0 else
        (AKSGraph.degreeInto G v N : ℝ) / 2)
      R hR (by simpa only [N, W, X] using hc O hO)
      ((D : ℝ) + 1 / 2) B Δ t hB hΔ ht
      (fun k ↦ abs_natCast_sub_realHalf_le_of_dist_le
        (hcount (e k)).2.1)
  have hProd : (∏ k : Fin (Fintype.card I),
      ((W k).card.choose (ell k) : ℝ)) =
      ∏ i : I, ((switchingPrivateNeighbors G p i S₀).card.choose
        (switchingRequiredPrivateCount G p O
          (fun j : RawTupleIndex labels a ↦ j.1.1) i) : ℝ) := by
    simpa only [W, ell, e, switchingPrivateBlocksFin] using
      e.prod_comp (fun i : I ↦
        ((switchingPrivateNeighbors G p i S₀).card.choose
          (switchingRequiredPrivateCount G p O
            (fun j : RawTupleIndex labels a ↦ j.1.1) i) : ℝ))
  dsimp only at hfixed
  rw [hProd] at hfixed
  have hfirst := (mem_switchingFirstExposureGood.mp hO).2.2.2.1
  have hOMean : |X O - Probability.expectation (1 / 2 : ℝ)
      (Probability.edgePolynomial G)| < tMean := by
    rw [hMean] at hfirst
    simpa only [X] using hfirst
  refine hfixed.trans ?_
  exact_mod_cast Finset.card_le_card (by
    intro U hU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU ⊢
    rcases hU with ⟨hUO, hcounts, hclose⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hUnion] using hUO
    · intro i
      have hi := hcounts (Fintype.equivFin I i)
      change (U ∩ switchingPrivateNeighbors G p
          ((Fintype.equivFin I).symm (Fintype.equivFin I i)) S₀).card =
        switchingRequiredPrivateCount G p O
          (fun j : RawTupleIndex labels a ↦ j.1.1)
            ((Fintype.equivFin I).symm (Fintype.equivFin I i)) at hi
      simpa only [Equiv.symm_apply_apply] using hi
    · dsimp only [good, radius, N]
      have hclose' : |outsideConditionalMeanPolynomial G N U - X O| <
          radius := by
        simpa only [outsideConditionalMeanPolynomial,
          switchingFirstExposureMeanPolynomial, N, W, radius, X] using hclose
      calc
        |outsideConditionalMeanPolynomial G N U -
            Probability.expectation (1 / 2 : ℝ)
              (Probability.edgePolynomial G)| =
          |(outsideConditionalMeanPolynomial G N U - X O) +
            (X O - Probability.expectation (1 / 2 : ℝ)
              (Probability.edgePolynomial G))| := by ring_nf
        _ ≤ |outsideConditionalMeanPolynomial G N U - X O| +
            |X O - Probability.expectation (1 / 2 : ℝ)
              (Probability.edgePolynomial G)| := abs_add_le _ _
        _ < radius + tMean := add_lt_add hclose' hOMean)

/-- Uniform expectation over a product finite type is the iterated uniform
expectation. -/
lemma uniformExpectation_prod_fubini
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A → B → ℝ) :
    uniformExpectation (fun a ↦ uniformExpectation (f a)) =
      uniformExpectation (fun z : A × B ↦ f z.1 z.2) := by
  unfold uniformExpectation
  rw [← Finset.sum_div]
  have hsum : (∑ a : A, ∑ b : B, f a b) =
      ∑ z : A × B, f z.1 z.2 := by
    symm
    calc
      (∑ z : A × B, f z.1 z.2) =
          ∑ z ∈ (Finset.univ : Finset A).product Finset.univ,
            f z.1 z.2 := by simp
      _ = ∑ a ∈ (Finset.univ : Finset A),
          ∑ b ∈ (Finset.univ : Finset B), f a b :=
        Finset.sum_product _ _ _
      _ = _ := by simp
  rw [hsum]
  simp only [Fintype.card_prod]
  push_cast
  field_simp

/-- Uniform expectation is invariant under a finite equivalence. -/
lemma uniformExpectation_equiv
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (e : A ≃ B) (f : A → ℝ) (g : B → ℝ)
    (h : ∀ a, f a = g (e a)) :
    uniformExpectation f = uniformExpectation g := by
  unfold uniformExpectation
  rw [show (∑ a, f a) = ∑ b, g b by
    calc
      (∑ a, f a) = ∑ a, g (e a) := by
        apply Finset.sum_congr rfl
        intro a _ha
        exact h a
      _ = _ := e.sum_comp g]
  rw [Fintype.card_congr e]

/-- Fair Bernoulli expectation factors over two disjoint finite coordinate
sets, with the two subsets combined by union. -/
lemma expectation_half_disjoint_union_fubini
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B : Finset V) (hAB : Disjoint A B) (f : Finset V → ℝ) :
    Probability.expectation (1 / 2 : ℝ)
        (fun SA : Finset (A : Set V) ↦
          Probability.expectation (1 / 2 : ℝ)
            (fun SB : Finset (B : Set V) ↦
              f (BoundedWindow.subtypeSubsetImage A SA ∪
                BoundedWindow.subtypeSubsetImage B SB))) =
      Probability.expectation (1 / 2 : ℝ)
        (fun S : Finset ((A ∪ B : Finset V) : Set V) ↦
          f (BoundedWindow.subtypeSubsetImage (A ∪ B) S)) := by
  let eUnion : (A : Set V) ⊕ (B : Set V) ≃ ((A ∪ B : Finset V) : Set V) :=
    Equiv.Finset.union A B hAB
  let E : Finset ((A ∪ B : Finset V) : Set V) ≃
      Finset (A : Set V) × Finset (B : Set V) :=
    (Equiv.finsetCongr eUnion.symm).trans Finset.sumEquiv.toEquiv
  rw [← Erdos88.BooleanSlices.uniformExpectation_finset_eq_probability_half_finite]
  simp_rw [← Erdos88.BooleanSlices.uniformExpectation_finset_eq_probability_half_finite]
  rw [uniformExpectation_prod_fubini]
  have htransport := uniformExpectation_equiv E
    (fun S : Finset ((A ∪ B : Finset V) : Set V) ↦
      f (BoundedWindow.subtypeSubsetImage (A ∪ B) S))
    (fun z : Finset (A : Set V) × Finset (B : Set V) ↦
      f (BoundedWindow.subtypeSubsetImage A z.1 ∪
        BoundedWindow.subtypeSubsetImage B z.2))
    (by
      intro S
      congr 1
      ext v
      simp only [SetLike.coe_sort_coe, Finset.mem_union]
      constructor
      · rintro ⟨hvA | hvB, hvS⟩
        · exact Or.inl ⟨hvA, by simpa using hvS⟩
        · exact Or.inr ⟨hvB, by simpa using hvS⟩
      · rintro (⟨hvA, hvS⟩ | ⟨hvB, hvS⟩)
        · exact ⟨Or.inl hvA, by simpa using hvS⟩
        · exact ⟨Or.inr hvB, by simpa using hvS⟩)
  exact htransport.symm

/-- The private-block mean is the conditional fair expectation obtained by
adjoining a random subset of the private-block union to the fixed outside
assignment. -/
lemma privateBlockMean_eq_expectation_union
    {n : ℕ} {I : Type*} [Fintype I]
    (W : I → Finset (Fin n)) (G : SimpleGraph (Fin n))
    (e₀ : ℝ) (c : Fin n → ℝ) (O : Finset (Fin n))
    (hO : Disjoint O (Finset.univ.biUnion W)) :
    privateBlockMean W G e₀ c O =
      Probability.expectation (1 / 2 : ℝ)
        (fun S : Finset ((Finset.univ.biUnion W : Finset (Fin n)) : Set (Fin n)) ↦
          Probability.perturbedEdgePolynomial G e₀ c
            (O ∪ BoundedWindow.subtypeSubsetImage
              (Finset.univ.biUnion W) S)) := by
  classical
  let E : Finset (Fin (Finset.univ.biUnion W).card) ≃
      Finset ((Finset.univ.biUnion W : Finset (Fin n)) : Set (Fin n)) :=
    Equiv.finsetCongr (blockUnionVertexEquiv W)
  unfold privateBlockMean
  rw [← Erdos88.BooleanSlices.uniformExpectation_finset_eq_probability_half_finite]
  rw [← Erdos88.BooleanSlices.uniformExpectation_finset_eq_probability_half_finite]
  apply uniformExpectation_equiv E
  intro S
  have hImage : BoundedWindow.subtypeSubsetImage
      (Finset.univ.biUnion W) (E S) = reindexedSubsetImage W S := by
    ext v
    simp [E, BoundedWindow.subtypeSubsetImage, reindexedSubsetImage,
      equivFinsetImage]
  rw [hImage]
  have hOB : Disjoint O (reindexedSubsetImage W S) :=
    hO.mono_right (reindexedSubsetImage_subset W S)
  have hUnion := perturbedEdgePolynomial_union_of_disjoint G e₀ c hOB
  have hReindex := perturbedEdgePolynomial_reindexedSubsetImage
    W G (privateBlockConstant G e₀ c O)
      (fun v ↦ c v + AKSGraph.degreeInto G v O) S
  have hcoeff : privateBlockCoefficient W G c O =
      fun i ↦ c (blockUnionVertexEquiv W i).1 +
        AKSGraph.degreeInto G (blockUnionVertexEquiv W i).1 O := by
    rfl
  calc
    Probability.perturbedEdgePolynomial (privateBlockGraph W G)
        (privateBlockConstant G e₀ c O)
        (privateBlockCoefficient W G c O) S =
      Probability.perturbedEdgePolynomial G
        (privateBlockConstant G e₀ c O)
        (fun v ↦ c v + AKSGraph.degreeInto G v O)
          (reindexedSubsetImage W S) := by
            rw [hcoeff]
            exact hReindex
    _ = Probability.perturbedEdgePolynomial G e₀ c
        (O ∪ reindexedSubsetImage W S) := hUnion.symm

/-- The outside conditional-mean polynomial is supported on the complement
of the common reservoir, so restricting its fair cube to that complement
does not change its expectation. -/
lemma expectation_outsideConditionalMeanPolynomial_restrict
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (N : Finset V) :
    Probability.expectation (1 / 2 : ℝ)
        (fun S : Finset (((Finset.univ : Finset V) \ N : Finset V) : Set V) ↦
          outsideConditionalMeanPolynomial G N
            (BoundedWindow.subtypeSubsetImage
              ((Finset.univ : Finset V) \ N) S)) =
      Probability.expectation (1 / 2 : ℝ)
        (outsideConditionalMeanPolynomial G N) := by
  classical
  let A := (Finset.univ : Finset V) \ N
  let H := outsideGraph G N
  let c : V → ℝ := fun v ↦ if v ∈ N then 0 else
    (AKSGraph.degreeInto G v N : ℝ) / 2
  have hfun :
      (fun S : Finset (A : Set V) ↦
        outsideConditionalMeanPolynomial G N
          (BoundedWindow.subtypeSubsetImage A S)) =
      fun S ↦ Probability.perturbedEdgePolynomial (H.induce (A : Set V))
        ((AKSGraph.edgeCount G N : ℝ) / 4) (fun v ↦ c v.1) S := by
    funext S
    symm
    exact BoundedWindow.perturbedEdgePolynomial_induce_subtypeSubsetImage
      H A ((AKSGraph.edgeCount G N : ℝ) / 4) c S
  have hEdge : (H.induce (A : Set V)).edgeFinset.card = H.edgeFinset.card := by
    have hleft : (H.induce (A : Set V)).edgeFinset.card =
        AKSGraph.edgeCount H A := by
      rw [← H.card_filter_edgeFinset_toFinset_subset A]
      rfl
    rw [hleft]
    unfold AKSGraph.edgeCount
    rw [Finset.filter_eq_self.2]
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        simp only [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] at he
        have huv := (outsideGraph_adj G N u v).mp he
        rw [Sym2.toFinset_mk_eq]
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, huv.2.1⟩
        · rw [Finset.mem_singleton] at hx
          subst x
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, huv.2.2⟩
  have hCoeff : (∑ v : (A : Set V), c v.1) = ∑ v : V, c v := by
    calc
      (∑ v : (A : Set V), c v.1) = ∑ v ∈ A, c v := by
        symm
        apply Finset.sum_subtype
        intro v
        simp
      _ = ∑ v ∈ (Finset.univ : Finset V), c v := by
        apply Finset.sum_subset (Finset.subset_univ A)
        intro v _hv hvA
        have hvN : v ∈ N := by
          by_contra hvN
          exact hvA (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvN⟩)
        simp [c, hvN]
      _ = ∑ v : V, c v := by rfl
  change Probability.expectation (1 / 2 : ℝ)
      (fun S : Finset (A : Set V) ↦
        outsideConditionalMeanPolynomial G N
          (BoundedWindow.subtypeSubsetImage A S)) = _
  rw [hfun]
  unfold outsideConditionalMeanPolynomial
  rw [Probability.expectation_perturbedEdgePolynomial _
      (by norm_num) (by norm_num),
    Probability.expectation_perturbedEdgePolynomial _
      (by norm_num) (by norm_num)]
  rw [hEdge, hCoeff]

/-- The fair expectation of the first-exposure conditional mean is exactly
the global fair induced-edge mean. -/
lemma expectation_switchingFirstExposureMeanPolynomial
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (S₀ : Finset (Fin n)) :
    Probability.expectation (1 / 2 : ℝ)
        (fun R : Finset (switchingFirstExposureDomain G p S₀ : Set (Fin n)) ↦
          switchingFirstExposureMeanPolynomial G p S₀
            (BoundedWindow.subtypeSubsetImage
              (switchingFirstExposureDomain G p S₀) R)) =
      Probability.expectation (1 / 2 : ℝ)
        (Probability.edgePolynomial G) := by
  classical
  let N := switchingCommonNonneighbors G p S₀
  let W := switchingPrivateBlocksFin G p S₀
  let B := Finset.univ.biUnion W
  let A := switchingFirstExposureDomain G p S₀
  let H := outsideGraph G N
  let e₀ := (AKSGraph.edgeCount G N : ℝ) / 4
  let c : Fin n → ℝ := fun v ↦ if v ∈ N then 0 else
    (AKSGraph.degreeInto G v N : ℝ) / 2
  let f := outsideConditionalMeanPolynomial G N
  have hWUnion : B = Finset.univ.biUnion fun i ↦
      switchingPrivateNeighbors G p i S₀ := by
    simpa only [B, W] using biUnion_switchingPrivateBlocksFin G p S₀
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    have hvA' := hvA
    dsimp only [A] at hvA'
    rw [switchingFirstExposureDomain, Finset.mem_sdiff] at hvA'
    exact hvA'.2 (Finset.mem_union_left _ (by simpa only [← hWUnion] using hvB))
  have hBN : Disjoint B N := by
    rw [Finset.disjoint_left]
    intro v hvB hvN
    obtain ⟨k, _hk, hvk⟩ := Finset.mem_biUnion.mp hvB
    exact Finset.disjoint_left.mp
      (switchingCommonNonneighbors_disjoint_private G p S₀
        ((Fintype.equivFin I).symm k)) hvN
      (by simpa only [W, switchingPrivateBlocksFin] using hvk)
  have hA : A = (Finset.univ : Finset (Fin n)) \ (B ∪ N) := by
    simp only [A, switchingFirstExposureDomain, B, N, W]
    rw [biUnion_switchingPrivateBlocksFin G p S₀]
  have hUnion : A ∪ B = (Finset.univ : Finset (Fin n)) \ N := by
    rw [hA]
    ext v
    by_cases hvB : v ∈ B
    · have hvN : v ∉ N := fun hvN ↦
        Finset.disjoint_left.mp hBN hvB hvN
      simp [hvB, hvN]
    · by_cases hvN : v ∈ N <;> simp [hvB, hvN]
  have hpoint (R : Finset (A : Set (Fin n))) :
      switchingFirstExposureMeanPolynomial G p S₀
          (BoundedWindow.subtypeSubsetImage A R) =
        Probability.expectation (1 / 2 : ℝ)
          (fun S : Finset (B : Set (Fin n)) ↦
            f (BoundedWindow.subtypeSubsetImage A R ∪
              BoundedWindow.subtypeSubsetImage B S)) := by
    have hRO : Disjoint (BoundedWindow.subtypeSubsetImage A R) B := by
      exact hAB.mono_left
        (BoundedWindow.subtypeSubsetImage_subset A R)
    have hbase := privateBlockMean_eq_expectation_union
      W H e₀ c (BoundedWindow.subtypeSubsetImage A R) hRO
    simpa only [switchingFirstExposureMeanPolynomial, W, N, H, e₀, c,
      B, f, outsideConditionalMeanPolynomial] using hbase
  change Probability.expectation (1 / 2 : ℝ)
      (fun R : Finset (A : Set (Fin n)) ↦
        switchingFirstExposureMeanPolynomial G p S₀
          (BoundedWindow.subtypeSubsetImage A R)) = _
  calc
    Probability.expectation (1 / 2 : ℝ)
        (fun R : Finset (A : Set (Fin n)) ↦
          switchingFirstExposureMeanPolynomial G p S₀
            (BoundedWindow.subtypeSubsetImage A R)) =
      Probability.expectation (1 / 2 : ℝ)
        (fun R : Finset (A : Set (Fin n)) ↦
          Probability.expectation (1 / 2 : ℝ)
            (fun S : Finset (B : Set (Fin n)) ↦
              f (BoundedWindow.subtypeSubsetImage A R ∪
                BoundedWindow.subtypeSubsetImage B S))) := by
          congr 1
          funext R
          exact hpoint R
    _ = Probability.expectation (1 / 2 : ℝ)
        (fun S : Finset ((A ∪ B : Finset (Fin n)) : Set (Fin n)) ↦
          f (BoundedWindow.subtypeSubsetImage (A ∪ B) S)) :=
      expectation_half_disjoint_union_fubini A B hAB f
    _ = Probability.expectation (1 / 2 : ℝ)
        (fun S : Finset (((Finset.univ : Finset (Fin n)) \ N :
            Finset (Fin n)) : Set (Fin n)) ↦
          f (BoundedWindow.subtypeSubsetImage
            ((Finset.univ : Finset (Fin n)) \ N) S)) := by
              rw [hUnion]
    _ = Probability.expectation (1 / 2 : ℝ) f := by
      simpa only [f, N] using
        expectation_outsideConditionalMeanPolynomial_restrict G N
    _ = Probability.expectation (1 / 2 : ℝ)
        (Probability.edgePolynomial G) := by
      simpa only [f, N] using expectation_outsideConditionalMeanPolynomial G N

/-- Variance on a finite uniform probability space. -/
noncomputable def finiteUniformVariance
    {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) : ℝ :=
  uniformExpectation fun a ↦ (f a - uniformExpectation f) ^ 2

lemma uniformExpectation_mono
    {A : Type*} [Fintype A] [Nonempty A] {f g : A → ℝ}
    (h : ∀ a, f a ≤ g a) : uniformExpectation f ≤ uniformExpectation g := by
  unfold uniformExpectation
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Finset.sum_le_sum fun a _ha ↦ h a

lemma uniformExpectation_sub_const
    {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) (c : ℝ) :
    uniformExpectation (fun a ↦ f a - c) = uniformExpectation f - c := by
  unfold uniformExpectation
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma sq_uniformExpectation_le_uniformExpectation_sq
    {A : Type*} [Fintype A] [Nonempty A] (f : A → ℝ) :
    uniformExpectation f ^ 2 ≤ uniformExpectation (fun a ↦ f a ^ 2) := by
  unfold uniformExpectation
  simpa only [Finset.card_univ] using
    (sum_div_card_sq_le_sum_sq_div_card
      (s := (Finset.univ : Finset A)) (f := f))

/-- Taking a conditional uniform expectation cannot increase variance. -/
lemma finiteUniformVariance_conditional_le
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A → B → ℝ) :
    finiteUniformVariance (fun a ↦ uniformExpectation (f a)) ≤
      finiteUniformVariance (fun z : A × B ↦ f z.1 z.2) := by
  let m := uniformExpectation (fun z : A × B ↦ f z.1 z.2)
  have hmean : uniformExpectation (fun a ↦ uniformExpectation (f a)) = m :=
    uniformExpectation_prod_fubini f
  unfold finiteUniformVariance
  rw [hmean]
  calc
    uniformExpectation (fun a ↦ (uniformExpectation (f a) - m) ^ 2) =
        uniformExpectation (fun a ↦
          uniformExpectation (fun b ↦ f a b - m) ^ 2) := by
            congr 1
            funext a
            rw [uniformExpectation_sub_const]
    _ ≤ uniformExpectation (fun a ↦
        uniformExpectation (fun b ↦ (f a b - m) ^ 2)) := by
          apply uniformExpectation_mono
          intro a
          exact sq_uniformExpectation_le_uniformExpectation_sq _
    _ = uniformExpectation (fun z : A × B ↦ (f z.1 z.2 - m) ^ 2) :=
      uniformExpectation_prod_fubini _

lemma finiteUniformVariance_equiv
    {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (e : A ≃ B) (f : A → ℝ) (g : B → ℝ)
    (h : ∀ a, f a = g (e a)) :
    finiteUniformVariance f = finiteUniformVariance g := by
  have hmean := uniformExpectation_equiv e f g h
  unfold finiteUniformVariance
  apply uniformExpectation_equiv e
  intro a
  rw [h a, hmean]

lemma finiteUniformVariance_finset_eq_variance_half
    {A : Type*} [Fintype A] (f : Finset A → ℝ) :
    finiteUniformVariance f = Probability.variance (1 / 2 : ℝ) f := by
  unfold finiteUniformVariance Probability.variance
  rw [Erdos88.BooleanSlices.uniformExpectation_finset_eq_probability_half_finite]
  rw [Erdos88.BooleanSlices.uniformExpectation_finset_eq_probability_half_finite]

/-- The fair-cube variance of the conditional expectation over one half of a
disjoint coordinate decomposition is at most the variance on the union. -/
lemma variance_half_disjoint_union_conditional_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B : Finset V) (hAB : Disjoint A B) (f : Finset V → ℝ) :
    Probability.variance (1 / 2 : ℝ)
        (fun SA : Finset (A : Set V) ↦
          Probability.expectation (1 / 2 : ℝ)
            (fun SB : Finset (B : Set V) ↦
              f (BoundedWindow.subtypeSubsetImage A SA ∪
                BoundedWindow.subtypeSubsetImage B SB))) ≤
      Probability.variance (1 / 2 : ℝ)
        (fun S : Finset ((A ∪ B : Finset V) : Set V) ↦
          f (BoundedWindow.subtypeSubsetImage (A ∪ B) S)) := by
  let eUnion : (A : Set V) ⊕ (B : Set V) ≃ ((A ∪ B : Finset V) : Set V) :=
    Equiv.Finset.union A B hAB
  let E : Finset ((A ∪ B : Finset V) : Set V) ≃
      Finset (A : Set V) × Finset (B : Set V) :=
    (Equiv.finsetCongr eUnion.symm).trans Finset.sumEquiv.toEquiv
  rw [← finiteUniformVariance_finset_eq_variance_half]
  rw [← finiteUniformVariance_finset_eq_variance_half]
  simp_rw [← Erdos88.BooleanSlices.uniformExpectation_finset_eq_probability_half_finite]
  let F := fun z : Finset (A : Set V) × Finset (B : Set V) ↦
    f (BoundedWindow.subtypeSubsetImage A z.1 ∪
      BoundedWindow.subtypeSubsetImage B z.2)
  have hcond := finiteUniformVariance_conditional_le
    (fun SA : Finset (A : Set V) ↦ fun SB : Finset (B : Set V) ↦
      f (BoundedWindow.subtypeSubsetImage A SA ∪
        BoundedWindow.subtypeSubsetImage B SB))
  refine hcond.trans_eq ?_
  exact (finiteUniformVariance_equiv E
    (fun S : Finset ((A ∪ B : Finset V) : Set V) ↦
      f (BoundedWindow.subtypeSubsetImage (A ∪ B) S)) F
    (by
      intro S
      congr 1
      ext v
      simp only [SetLike.coe_sort_coe, Finset.mem_union]
      constructor
      · rintro ⟨hvA | hvB, hvS⟩
        · exact Or.inl ⟨hvA, by simpa using hvS⟩
        · exact Or.inr ⟨hvB, by simpa using hvS⟩
      · rintro (⟨hvA, hvS⟩ | ⟨hvB, hvS⟩)
        · exact ⟨Or.inl hvA, by simpa using hvS⟩
        · exact ⟨Or.inr hvB, by simpa using hvS⟩)).symm

/-- Adding vertices from the common reservoir does not change the outside
conditional-mean polynomial. -/
lemma outsideConditionalMeanPolynomial_union_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (N O R : Finset V) (hRN : R ⊆ N) :
    outsideConditionalMeanPolynomial G N (O ∪ R) =
      outsideConditionalMeanPolynomial G N O := by
  let H := outsideGraph G N
  let c : V → ℝ := fun v ↦ if v ∈ N then 0 else
    (AKSGraph.degreeInto G v N : ℝ) / 2
  have hedgeSupport : ∀ e ∈ H.edgeFinset, ∀ v ∈ e.toFinset, v ∉ N := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ u v =>
        simp only [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] at he
        have huv := (outsideGraph_adj G N u v).mp he
        rw [Sym2.toFinset_mk_eq]
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact huv.2.1
        · rw [Finset.mem_singleton] at hx
          subst x
          exact huv.2.2
  have hEdge : Probability.edgePolynomial H (O ∪ R) =
      Probability.edgePolynomial H O := by
    rw [Probability.edgePolynomial_eq_sum_prod_bit,
      Probability.edgePolynomial_eq_sum_prod_bit]
    apply Finset.sum_congr rfl
    intro e he
    apply Finset.prod_congr rfl
    intro v hv
    have hvN := hedgeSupport e he v hv
    have hvR : v ∉ R := fun hvR ↦ hvN (hRN hvR)
    simp [Probability.bit, hvR]
  have hLinear : (∑ v, c v * Probability.bit v (O ∪ R)) =
      ∑ v, c v * Probability.bit v O := by
    apply Finset.sum_congr rfl
    intro v _hv
    by_cases hvN : v ∈ N
    · simp [c, hvN]
    · have hvR : v ∉ R := fun hvR ↦ hvN (hRN hvR)
      simp [c, hvN, hvR, Probability.bit]
  unfold outsideConditionalMeanPolynomial Probability.perturbedEdgePolynomial
  rw [hEdge, hLinear]

/-- Removing the inactive common-reservoir coordinates cannot increase the
variance of the outside conditional mean. -/
lemma variance_outsideConditionalMeanPolynomial_restrict_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (N : Finset V) :
    Probability.variance (1 / 2 : ℝ)
        (fun S : Finset (((Finset.univ : Finset V) \ N : Finset V) : Set V) ↦
          outsideConditionalMeanPolynomial G N
            (BoundedWindow.subtypeSubsetImage
              ((Finset.univ : Finset V) \ N) S)) ≤
      Probability.variance (1 / 2 : ℝ)
        (outsideConditionalMeanPolynomial G N) := by
  let A := (Finset.univ : Finset V) \ N
  let f := outsideConditionalMeanPolynomial G N
  have hAN : Disjoint A N := by
    rw [Finset.disjoint_left]
    intro v hvA hvN
    exact (Finset.mem_sdiff.mp hvA).2 hvN
  have hUnion : A ∪ N = (Finset.univ : Finset V) := by
    ext v
    by_cases hv : v ∈ N <;> simp [A, hv]
  have hcond := variance_half_disjoint_union_conditional_le A N hAN f
  have hinner :
      (fun SA : Finset (A : Set V) ↦
        Probability.expectation (1 / 2 : ℝ)
          (fun SB : Finset (N : Set V) ↦
            f (BoundedWindow.subtypeSubsetImage A SA ∪
              BoundedWindow.subtypeSubsetImage N SB))) =
      (fun SA : Finset (A : Set V) ↦
        f (BoundedWindow.subtypeSubsetImage A SA)) := by
    funext SA
    have hpoint :
        (fun SB : Finset (N : Set V) ↦
          f (BoundedWindow.subtypeSubsetImage A SA ∪
            BoundedWindow.subtypeSubsetImage N SB)) =
        (fun _SB : Finset (N : Set V) ↦
          f (BoundedWindow.subtypeSubsetImage A SA)) := by
      funext SB
      apply outsideConditionalMeanPolynomial_union_subset
      exact BoundedWindow.subtypeSubsetImage_subset N SB
    rw [hpoint]
    exact Erdos88.Probability.expectation_const (1 / 2 : ℝ) _
  rw [hinner] at hcond
  rw [hUnion] at hcond
  have hfull :
      Probability.variance (1 / 2 : ℝ)
          (fun S : Finset ((Finset.univ : Finset V) : Set V) ↦
            f (BoundedWindow.subtypeSubsetImage Finset.univ S)) =
        Probability.variance (1 / 2 : ℝ) f := by
    rw [← finiteUniformVariance_finset_eq_variance_half]
    rw [← finiteUniformVariance_finset_eq_variance_half]
    let e : ((Finset.univ : Finset V) : Set V) ≃ V :=
      { toFun := fun v ↦ v.1
        invFun := fun v ↦ ⟨v, Finset.mem_univ v⟩
        left_inv := fun v ↦ Subtype.ext rfl
        right_inv := fun _v ↦ rfl }
    let E : Finset ((Finset.univ : Finset V) : Set V) ≃ Finset V :=
      Equiv.finsetCongr e
    apply finiteUniformVariance_equiv E
    intro S
    congr 1
    ext v
    simp [E, e, BoundedWindow.subtypeSubsetImage]
  exact hcond.trans_eq hfull

/-- The outside conditional-mean polynomial has variance at most `n^3`. -/
lemma variance_outsideConditionalMeanPolynomial_le_cube
    {n : ℕ} (G : SimpleGraph (Fin n)) (N : Finset (Fin n)) :
    Probability.variance (1 / 2 : ℝ)
        (outsideConditionalMeanPolynomial G N) ≤ (n : ℝ) ^ 3 := by
  let H := outsideGraph G N
  let e₀ := (AKSGraph.edgeCount G N : ℝ) / 4
  let c : Fin n → ℝ := fun v ↦ if v ∈ N then 0 else
    (AKSGraph.degreeInto G v N : ℝ) / 2
  have hc : ∀ v, |c v| ≤ (1 : ℝ) * n := by
    intro v
    by_cases hvN : v ∈ N
    · simp [c, hvN]
    · have hdegNat : AKSGraph.degreeInto G v N ≤ n :=
        (AKSGraph.degreeInto_le_card G v N).trans
          (by simpa using Finset.card_le_card (Finset.subset_univ N))
      have hdeg : (AKSGraph.degreeInto G v N : ℝ) ≤ n := by
        exact_mod_cast hdegNat
      have hdeg0 : (0 : ℝ) ≤ AKSGraph.degreeInto G v N := by positivity
      simp only [c, hvN, ↓reduceIte, abs_div, abs_of_nonneg hdeg0, one_mul]
      norm_num
      linarith
  have hvar := variance_perturbedEdgePolynomial_half_le
    H e₀ c 1 (by norm_num) hc
  change Probability.variance (1 / 2 : ℝ)
      (Probability.perturbedEdgePolynomial (outsideGraph G N)
        ((AKSGraph.edgeCount G N : ℝ) / 4)
        (fun v ↦ if v ∈ N then 0 else
          (AKSGraph.degreeInto G v N : ℝ) / 2)) ≤ (n : ℝ) ^ 3
  simpa only [H, e₀, c, one_pow, one_mul] using hvar

/-- The first-exposure conditional mean inherits the same `n^3` variance
bound by two applications of conditional-variance contraction. -/
lemma variance_switchingFirstExposureMeanPolynomial_le_cube
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (S₀ : Finset (Fin n)) :
    Probability.variance (1 / 2 : ℝ)
        (fun R : Finset (switchingFirstExposureDomain G p S₀ : Set (Fin n)) ↦
          switchingFirstExposureMeanPolynomial G p S₀
            (BoundedWindow.subtypeSubsetImage
              (switchingFirstExposureDomain G p S₀) R)) ≤
      (n : ℝ) ^ 3 := by
  classical
  let N := switchingCommonNonneighbors G p S₀
  let W := switchingPrivateBlocksFin G p S₀
  let B := Finset.univ.biUnion W
  let A := switchingFirstExposureDomain G p S₀
  let H := outsideGraph G N
  let e₀ := (AKSGraph.edgeCount G N : ℝ) / 4
  let c : Fin n → ℝ := fun v ↦ if v ∈ N then 0 else
    (AKSGraph.degreeInto G v N : ℝ) / 2
  let f := outsideConditionalMeanPolynomial G N
  have hWUnion : B = Finset.univ.biUnion fun i ↦
      switchingPrivateNeighbors G p i S₀ := by
    simpa only [B, W] using biUnion_switchingPrivateBlocksFin G p S₀
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro v hvA hvB
    have hvA' := hvA
    dsimp only [A] at hvA'
    rw [switchingFirstExposureDomain, Finset.mem_sdiff] at hvA'
    exact hvA'.2 (Finset.mem_union_left _ (by simpa only [← hWUnion] using hvB))
  have hBN : Disjoint B N := by
    rw [Finset.disjoint_left]
    intro v hvB hvN
    obtain ⟨k, _hk, hvk⟩ := Finset.mem_biUnion.mp hvB
    exact Finset.disjoint_left.mp
      (switchingCommonNonneighbors_disjoint_private G p S₀
        ((Fintype.equivFin I).symm k)) hvN
      (by simpa only [W, switchingPrivateBlocksFin] using hvk)
  have hA : A = (Finset.univ : Finset (Fin n)) \ (B ∪ N) := by
    simp only [A, switchingFirstExposureDomain, B, N, W]
    rw [biUnion_switchingPrivateBlocksFin G p S₀]
  have hUnion : A ∪ B = (Finset.univ : Finset (Fin n)) \ N := by
    rw [hA]
    ext v
    by_cases hvB : v ∈ B
    · have hvN : v ∉ N := fun hvN ↦
        Finset.disjoint_left.mp hBN hvB hvN
      simp [hvB, hvN]
    · by_cases hvN : v ∈ N <;> simp [hvB, hvN]
  have hpoint (R : Finset (A : Set (Fin n))) :
      switchingFirstExposureMeanPolynomial G p S₀
          (BoundedWindow.subtypeSubsetImage A R) =
        Probability.expectation (1 / 2 : ℝ)
          (fun S : Finset (B : Set (Fin n)) ↦
            f (BoundedWindow.subtypeSubsetImage A R ∪
              BoundedWindow.subtypeSubsetImage B S)) := by
    have hRO : Disjoint (BoundedWindow.subtypeSubsetImage A R) B :=
      hAB.mono_left (BoundedWindow.subtypeSubsetImage_subset A R)
    have hbase := privateBlockMean_eq_expectation_union
      W H e₀ c (BoundedWindow.subtypeSubsetImage A R) hRO
    simpa only [switchingFirstExposureMeanPolynomial, W, N, H, e₀, c,
      B, f, outsideConditionalMeanPolynomial] using hbase
  have hcond := variance_half_disjoint_union_conditional_le A B hAB f
  have hleft :
      (fun R : Finset (A : Set (Fin n)) ↦
        switchingFirstExposureMeanPolynomial G p S₀
          (BoundedWindow.subtypeSubsetImage A R)) =
      (fun R : Finset (A : Set (Fin n)) ↦
        Probability.expectation (1 / 2 : ℝ)
          (fun S : Finset (B : Set (Fin n)) ↦
            f (BoundedWindow.subtypeSubsetImage A R ∪
              BoundedWindow.subtypeSubsetImage B S))) := by
    funext R
    exact hpoint R
  rw [← hleft] at hcond
  rw [hUnion] at hcond
  refine hcond.trans ?_
  refine (variance_outsideConditionalMeanPolynomial_restrict_le G N).trans ?_
  exact variance_outsideConditionalMeanPolynomial_le_cube G N

/-- Explicit Chebyshev bound for the normalized first-exposure loss. -/
lemma switchingFirstExposureError_le
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (S₀ : Finset (Fin n)) (tMean tRow : ℝ) :
    switchingFirstExposureError G p S₀
        (switchingFirstExposureMeanPolynomial G p S₀) tMean tRow ≤
      (n : ℝ) ^ 3 / tMean ^ 2 +
        (Fintype.card I : ℝ) * (((n : ℝ) / 4) / tRow ^ 2) := by
  unfold switchingFirstExposureError
  apply add_le_add
  · apply div_le_div_of_nonneg_right
      (variance_switchingFirstExposureMeanPolynomial_le_cube G p S₀)
    positivity
  · gcongr
    have hcardNat : (switchingFirstExposureDomain G p S₀).card ≤ n :=
      (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
    exact_mod_cast hcardNat

/-- Any budget below the forced-endpoint mass gives the corresponding
positive lower bound on the surviving first-exposure rate. -/
lemma switchingFirstExposureRate_ge_of_error_budget
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (S₀ : Finset (Fin n)) (tMean tRow q : ℝ)
    (hbudget : q +
        ((n : ℝ) ^ 3 / tMean ^ 2 +
          (Fintype.card I : ℝ) * (((n : ℝ) / 4) / tRow ^ 2)) ≤
      ((2 : ℝ) ^ (2 * Fintype.card I))⁻¹) :
    q ≤ switchingFirstExposureRate G p S₀
      (switchingFirstExposureMeanPolynomial G p S₀) tMean tRow := by
  have herr := switchingFirstExposureError_le G p S₀ tMean tRow
  unfold switchingFirstExposureRate
  linarith

/-- The variance budget gives the exact core count required by the
private-block completion theorem. -/
lemma card_switchingFirstExposureGood_ge_of_error_budget
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (S₀ : Finset (Fin n)) (hp : PairEndpointsDistinct p)
    (tMean tRow q : ℝ) (htMean : 0 < tMean) (htRow : 0 < tRow)
    (hroom : 2 * Fintype.card I ≤
      (switchingFirstExposureDomain G p S₀).card)
    (hbudget : q +
        ((n : ℝ) ^ 3 / tMean ^ 2 +
          (Fintype.card I : ℝ) * (((n : ℝ) / 4) / tRow ^ 2)) ≤
      ((2 : ℝ) ^ (2 * Fintype.card I))⁻¹) :
    q * (2 : ℝ) ^
        (n - ((Finset.univ.biUnion fun i ↦
          switchingPrivateNeighbors G p i S₀) ∪
            switchingCommonNonneighbors G p S₀).card) ≤
      ((switchingFirstExposureGood G p S₀
        (switchingFirstExposureMeanPolynomial G p S₀)
        tMean tRow).card : ℝ) := by
  have hrate := switchingFirstExposureRate_ge_of_error_budget
    G p S₀ tMean tRow q hbudget
  have hcard := card_switchingFirstExposureGood_ge_rate G p S₀ hp
    (switchingFirstExposureMeanPolynomial G p S₀)
    tMean tRow htMean htRow hroom
  rw [card_switchingFirstExposureDomain G p S₀] at hcard
  exact (mul_le_mul_of_nonneg_right hrate (by positivity)).trans hcard

lemma natCube_div_scaled_sqrtCube_sq
    {n : ℕ} (hn : 1 ≤ n) {K : ℝ} (hK : K ≠ 0) :
    (n : ℝ) ^ 3 / (K * Real.sqrt n ^ 3) ^ 2 = 1 / K ^ 2 := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrt : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0
  have hsqrt0 : Real.sqrt (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hnpos)
  field_simp
  rw [show Real.sqrt (n : ℝ) ^ 6 =
      (Real.sqrt (n : ℝ) ^ 2) ^ 3 by ring, hsqrt]

lemma nat_div_four_scaled_sqrt_sq
    {n : ℕ} (hn : 1 ≤ n) {K : ℝ} (hK : K ≠ 0) :
    ((n : ℝ) / 4) / (K * Real.sqrt n) ^ 2 = 1 / (4 * K ^ 2) := by
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrt : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0
  have hsqrt0 : Real.sqrt (n : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hnpos)
  field_simp
  rw [hsqrt]

lemma switchingFirstExposureRate_ge_scaled
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (S₀ : Finset (Fin n)) (hn : 1 ≤ n)
    (KMean KRow q : ℝ) (hKMean : KMean ≠ 0) (hKRow : KRow ≠ 0)
    (hbudget : q +
        (1 / KMean ^ 2 +
          (Fintype.card I : ℝ) * (1 / (4 * KRow ^ 2))) ≤
      ((2 : ℝ) ^ (2 * Fintype.card I))⁻¹) :
    q ≤ switchingFirstExposureRate G p S₀
      (switchingFirstExposureMeanPolynomial G p S₀)
      (KMean * Real.sqrt n ^ 3) (KRow * Real.sqrt n) := by
  apply switchingFirstExposureRate_ge_of_error_budget
  rw [natCube_div_scaled_sqrtCube_sq hn hKMean,
    nat_div_four_scaled_sqrt_sq hn hKRow]
  exact hbudget

lemma canonicalFirstExposureBudget (s : ℕ) :
    let P := (2 : ℝ) ^ (2 * s)
    let K := 4 * (s + 1 : ℕ) * P
    let q := 1 / (4 * P)
    q + (1 / K ^ 2 + (s : ℝ) * (1 / (4 * K ^ 2))) ≤ P⁻¹ := by
  dsimp only
  let P := (2 : ℝ) ^ (2 * s)
  let x := (s : ℝ) + 1
  have hP : 1 ≤ P := by
    dsimp only [P]
    exact one_le_pow₀ (by norm_num)
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  have hs0 : (0 : ℝ) ≤ s := by positivity
  have hx : 1 ≤ x := by
    dsimp only [x]
    linarith
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [show ((s + 1 : ℕ) : ℝ) = x by simp [x],
    show (s : ℝ) = x - 1 by simp [x],
    show (2 : ℝ) ^ (2 * s) = P by rfl]
  rw [inv_eq_one_div]
  field_simp
  nlinarith [mul_pos hx0 hP0,
    mul_nonneg (sub_nonneg.mpr hx) (sq_nonneg P)]

/-- A single explicit scale at which the first-exposure Chebyshev losses use
at most three quarters of the forced-endpoint mass. -/
noncomputable def canonicalFirstExposureScale (s : ℕ) : ℝ :=
  4 * (s + 1 : ℕ) * (2 : ℝ) ^ (2 * s)

noncomputable def canonicalFirstExposureRate (s : ℕ) : ℝ :=
  1 / (4 * (2 : ℝ) ^ (2 * s))

lemma canonicalFirstExposureScale_pos (s : ℕ) :
    0 < canonicalFirstExposureScale s := by
  unfold canonicalFirstExposureScale
  positivity

lemma canonicalFirstExposureRate_pos (s : ℕ) :
    0 < canonicalFirstExposureRate s := by
  unfold canonicalFirstExposureRate
  positivity

lemma switchingFirstExposureRate_ge_canonical
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (S₀ : Finset (Fin n)) (hn : 1 ≤ n) :
    canonicalFirstExposureRate (Fintype.card I) ≤
      switchingFirstExposureRate G p S₀
        (switchingFirstExposureMeanPolynomial G p S₀)
        (canonicalFirstExposureScale (Fintype.card I) * Real.sqrt n ^ 3)
        (canonicalFirstExposureScale (Fintype.card I) * Real.sqrt n) := by
  apply switchingFirstExposureRate_ge_scaled G p S₀ hn
  · exact ne_of_gt (canonicalFirstExposureScale_pos _)
  · exact ne_of_gt (canonicalFirstExposureScale_pos _)
  · simpa only [canonicalFirstExposureScale, canonicalFirstExposureRate]
      using canonicalFirstExposureBudget (Fintype.card I)

/-- The explicit canonical first-exposure parameters satisfy the exact
Chebyshev budget used by the lower fixed-tuple theorem. -/
lemma canonicalFirstExposure_scaled_budget (n s : ℕ) (hn : 1 ≤ n) :
    canonicalFirstExposureRate s +
        ((n : ℝ) ^ 3 /
            (canonicalFirstExposureScale s * Real.sqrt n ^ 3) ^ 2 +
          (s : ℝ) * (((n : ℝ) / 4) /
            (canonicalFirstExposureScale s * Real.sqrt n) ^ 2)) ≤
      ((2 : ℝ) ^ (2 * s))⁻¹ := by
  rw [natCube_div_scaled_sqrtCube_sq hn
      (ne_of_gt (canonicalFirstExposureScale_pos s)),
    nat_div_four_scaled_sqrt_sq hn
      (ne_of_gt (canonicalFirstExposureScale_pos s))]
  simpa only [canonicalFirstExposureScale, canonicalFirstExposureRate]
    using canonicalFirstExposureBudget s

/-- Conditional extension over the common reservoir for an arbitrary selected
family of outside states.  This lets the first-exposure mean-good event be
retained when the bounded-window theorem is applied fibrewise. -/
lemma card_selectedOutside_switchingTuple_and_window_ge_conditional
    {n : ℕ}
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ)
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (S₀ : Finset (Fin n)) (window : Finset (Fin n) → Prop)
    (outsides : Finset (Finset (Fin n))) (windowLower : ℝ)
    (houtside : ∀ O ∈ outsides,
      O ⊆ (Finset.univ : Finset (Fin n)) \
          switchingCommonNonneighbors G p S₀ ∧
        p ∈ switchingTupleFinset T (edgeScore G) labels a O)
    (hwindow : ∀ O ∈ outsides,
      windowLower ≤
        (((switchingCommonNonneighbors G p S₀).powerset.filter fun R ↦
          window (O ∪ R)).card : ℝ)) :
    (outsides.card : ℝ) * windowLower ≤
      (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          window U).card : ℝ) := by
  classical
  let N := switchingCommonNonneighbors G p S₀
  let fullEvent := (Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
    p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧ window U
  let selectedFull := fullEvent.filter fun U ↦ U \ N ∈ outsides
  have hmaps : Set.MapsTo (fun U : Finset (Fin n) ↦ U \ N)
      (selectedFull : Set (Finset (Fin n))) (outsides : Set (Finset (Fin n))) := by
    intro U hU
    exact (Finset.mem_filter.mp hU).2
  have hfiber : ∀ O ∈ outsides, windowLower ≤
      ((selectedFull.filter fun U ↦ U \ N = O).card : ℝ) := by
    intro O hO
    let target := N.powerset.filter fun R ↦ window (O ∪ R)
    have hOdata := houtside O hO
    have hOsub : O ⊆ (Finset.univ : Finset (Fin n)) \ N := by
      simpa only [N] using hOdata.1
    have hON : Disjoint O N := by
      apply Finset.disjoint_left.mpr
      intro x hxO hxN
      exact (Finset.mem_sdiff.mp (hOsub hxO)).2 hxN
    have hmapsTo : Set.MapsTo (fun R : Finset (Fin n) ↦ O ∪ R)
        (target : Set (Finset (Fin n)))
        (selectedFull.filter (fun U ↦ U \ N = O) : Set (Finset (Fin n))) := by
      intro R hR
      have hR' := Finset.mem_filter.mp hR
      have hRsub : R ⊆ N := Finset.mem_powerset.mp hR'.1
      have hsdiff : (O ∪ R) \ N = O := by
        ext x
        constructor
        · intro hx
          have hx' := Finset.mem_sdiff.mp hx
          rcases Finset.mem_union.mp hx'.1 with hxO | hxR
          · exact hxO
          · exact False.elim (hx'.2 (hRsub hxR))
        · intro hxO
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_union_left _ hxO,
              fun hxN ↦ Finset.disjoint_left.mp hON hxO hxN⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, hsdiff⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_, hR'.2⟩
        apply (mem_switchingTupleFinset_sdiff_commonNonneighbors_iff
          T G labels a (O ∪ R) S₀ p).mpr
        simpa only [N, hsdiff] using hOdata.2
      · simpa only [hsdiff] using hO
    have hinj : Set.InjOn (fun R : Finset (Fin n) ↦ O ∪ R)
        (target : Set (Finset (Fin n))) := by
      intro R hR Z hZ hEq
      have hRsub : R ⊆ N :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp hR).1
      have hZsub : Z ⊆ N :=
        Finset.mem_powerset.mp (Finset.mem_filter.mp hZ).1
      ext x
      by_cases hxN : x ∈ N
      · have hxO : x ∉ O := fun hxO ↦
          Finset.disjoint_left.mp hON hxO hxN
        have hx := Finset.ext_iff.mp hEq x
        simpa only [Finset.mem_union, hxO, false_or] using hx
      · have hxR : x ∉ R := fun hxR ↦ hxN (hRsub hxR)
        have hxZ : x ∉ Z := fun hxZ ↦ hxN (hZsub hxZ)
        simp only [hxR, hxZ]
    have hcard : target.card ≤
        (selectedFull.filter fun U ↦ U \ N = O).card :=
      Finset.card_le_card_of_injOn _ hmapsTo hinj
    have hcardReal : (target.card : ℝ) ≤
        ((selectedFull.filter fun U ↦ U \ N = O).card : ℝ) := by
      exact_mod_cast hcard
    have hwindowO : windowLower ≤ (target.card : ℝ) := by
      simpa only [target, N] using hwindow O hO
    exact hwindowO.trans hcardReal
  have hcard := Finset.card_eq_sum_card_fiberwise
    (s := selectedFull) (t := outsides)
    (f := fun U : Finset (Fin n) ↦ U \ N) hmaps
  have hselected : (selectedFull.card : ℝ) ≤ (fullEvent.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  change (outsides.card : ℝ) * windowLower ≤ (fullEvent.card : ℝ)
  calc
    (outsides.card : ℝ) * windowLower =
        ∑ _O ∈ outsides, windowLower := by simp
    _ ≤ ∑ O ∈ outsides,
        ((selectedFull.filter fun U ↦ U \ N = O).card : ℝ) := by
      exact Finset.sum_le_sum fun O hO ↦ hfiber O hO
    _ = (selectedFull.card : ℝ) := by rw [hcard, Nat.cast_sum]
    _ ≤ (fullEvent.card : ℝ) := hselected

/-- Complete first-exposure/private-block lower count, followed by a
fibrewise window extension on the common reservoir. -/
lemma card_states_containing_switchingTuple_and_window_ge_of_firstExposure
    {n : ℕ}
    (T : Finset (Fin n × Fin n)) (G : SimpleGraph (Fin n))
    (labels : Finset ℤ) (a : ℤ → ℕ) (S₀ : Finset (Fin n))
    (p : RawTupleIndex labels a → Fin n × Fin n)
    (hpT : ∀ j, p j ∈ T) (hp : PairEndpointsDistinct p)
    (tMean tRow labelRadius : ℝ)
    (D : ℕ) (C q R B Δ t : ℝ) (hq : 0 ≤ q)
    (hR : 1 ≤ R) (hB : 0 ≤ B) (hΔ : 0 ≤ Δ) (ht : 0 < t)
    (htMean : 0 < tMean) (htRow : 0 < tRow)
    (hroom : 2 * Fintype.card (RawTupleIndex labels a) ≤
      (switchingFirstExposureDomain G p S₀).card)
    (hbudget : q +
        ((n : ℝ) ^ 3 / tMean ^ 2 +
          (Fintype.card (RawTupleIndex labels a) : ℝ) *
            (((n : ℝ) / 4) / tRow ^ 2)) ≤
      ((2 : ℝ) ^
        (2 * Fintype.card (RawTupleIndex labels a)))⁻¹)
    (hqPrivate : 0 ≤
      1 - (R ^ 2 * ((Finset.univ.biUnion
          (switchingPrivateBlocksFin G p S₀)).card : ℝ) ^ 3) / t ^ 2 -
        ((∑ k, binomialTailBound
            (reindexedBlock (switchingPrivateBlocksFin G p S₀) k) Δ) +
          binomialTailBound
            ((Finset.univ : Finset (Fin (Finset.univ.biUnion
              (switchingPrivateBlocksFin G p S₀)).card)) \
                Finset.univ.biUnion
                  (reindexedBlock (switchingPrivateBlocksFin G p S₀))) Δ) -
        binomialTailBound
          ((Finset.univ : Finset (Fin (Finset.univ.biUnion
            (switchingPrivateBlocksFin G p S₀)).card)) \
              Finset.univ.biUnion
                (reindexedBlock (switchingPrivateBlocksFin G p S₀))) B)
    (hlabel : ∀ i, |(i.1.1 : ℝ) -
        ((FiniteES.vertexDegree G (p i).2 : ℝ) -
          (FiniteES.vertexDegree G (p i).1 : ℝ)) / 2| ≤ labelRadius)
    (hRadius : labelRadius + tRow + 1 / 2 ≤ (D : ℝ))
    (hblockPos : ∀ i, 1 ≤ (switchingPrivateNeighbors G p i S₀).card)
    (hblockHalf : ∀ i,
      1 ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hD : ∀ i,
      8 * D ≤ (switchingPrivateNeighbors G p i S₀).card / 2)
    (hquad : ∀ i, (D : ℝ) ^ 2 ≤
      C * ((switchingPrivateNeighbors G p i S₀).card / 2 : ℕ))
    (hc : ∀ O ∈ switchingFirstExposureGood G p S₀
        (switchingFirstExposureMeanPolynomial G p S₀) tMean tRow,
      ∀ v ∈ Finset.univ.biUnion (switchingPrivateBlocksFin G p S₀),
        |(if v ∈ switchingCommonNonneighbors G p S₀ then 0 else
              (AKSGraph.degreeInto G v
                (switchingCommonNonneighbors G p S₀) : ℝ) / 2) +
            AKSGraph.degreeInto
              (outsideGraph G (switchingCommonNonneighbors G p S₀)) v O| ≤
          R * (Finset.univ.biUnion
            (switchingPrivateBlocksFin G p S₀)).card)
    (window : Finset (Fin n) → Prop) (windowLower : ℝ)
    (hwindowLower : 0 ≤ windowLower)
    (hwindow :
      let W := switchingPrivateBlocksFin G p S₀
      let W' := reindexedBlock W
      let outside := (Finset.univ : Finset
        (Fin (Finset.univ.biUnion W).card)) \ Finset.univ.biUnion W'
      let radius := t +
        (((Fintype.card (RawTupleIndex labels a) + 1 : ℕ) : ℝ) *
          (max ((D : ℝ) + 1 / 2) B + Δ)) *
            ((R + 1) * (Finset.univ.biUnion W).card)
      ∀ O ∈ (((Finset.univ : Finset (Fin n)) \
          switchingCommonNonneighbors G p S₀).powerset.filter
        (fun U ↦ p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          |outsideConditionalMeanPolynomial G
              (switchingCommonNonneighbors G p S₀) U -
            Probability.expectation (1 / 2 : ℝ)
              (Probability.edgePolynomial G)| < radius + tMean)),
        windowLower ≤
          (((switchingCommonNonneighbors G p S₀).powerset.filter fun R ↦
            window (O ∪ R)).card : ℝ)) :
    let W := switchingPrivateBlocksFin G p S₀
    let W' := reindexedBlock W
    let outside := (Finset.univ : Finset
      (Fin (Finset.univ.biUnion W).card)) \ Finset.univ.biUnion W'
    let qPrivate := 1 -
        (R ^ 2 * ((Finset.univ.biUnion W).card : ℝ) ^ 3) / t ^ 2 -
        ((∑ k, binomialTailBound (W' k) Δ) +
          binomialTailBound outside Δ) -
        binomialTailBound outside B
    ((qPrivate * q) * ((2 : ℝ) ^
          (n - (switchingCommonNonneighbors G p S₀).card) *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
          Fintype.card (RawTupleIndex labels a))) * windowLower ≤
      (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
        p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
          window U).card : ℝ) := by
  classical
  let W := switchingPrivateBlocksFin G p S₀
  let W' := reindexedBlock W
  let outside := (Finset.univ : Finset
    (Fin (Finset.univ.biUnion W).card)) \ Finset.univ.biUnion W'
  let qPrivate := 1 -
      (R ^ 2 * ((Finset.univ.biUnion W).card : ℝ) ^ 3) / t ^ 2 -
      ((∑ k, binomialTailBound (W' k) Δ) +
        binomialTailBound outside Δ) -
      binomialTailBound outside B
  let radius := t +
    (((Fintype.card (RawTupleIndex labels a) + 1 : ℕ) : ℝ) *
      (max ((D : ℝ) + 1 / 2) B + Δ)) *
        ((R + 1) * (Finset.univ.biUnion W).card)
  let outsides := (((Finset.univ : Finset (Fin n)) \
      switchingCommonNonneighbors G p S₀).powerset.filter
    (fun U ↦ p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
      |outsideConditionalMeanPolynomial G
          (switchingCommonNonneighbors G p S₀) U -
        Probability.expectation (1 / 2 : ℝ)
          (Probability.edgePolynomial G)| < radius + tMean))
  have hcore := card_switchingFirstExposureGood_ge_of_error_budget
    G p S₀ hp tMean tRow q htMean htRow hroom hbudget
  have hout :=
    card_outside_states_containing_switchingTuple_and_mean_close_ge_of_firstExposure
      T G labels a S₀ p hpT hp tMean tRow labelRadius D C q R B Δ t
      hq hR hB hΔ ht hqPrivate hlabel hRadius hblockPos hblockHalf hD hquad
      hcore (expectation_switchingFirstExposureMeanPolynomial G p S₀) hc
  have hselected :=
    card_selectedOutside_switchingTuple_and_window_ge_conditional
      T G labels a p S₀ window outsides windowLower
      (by
        intro O hO
        have hO' := Finset.mem_filter.mp hO
        exact ⟨Finset.mem_powerset.mp hO'.1, hO'.2.1⟩)
      (by simpa only [outsides, radius, W, W', outside] using hwindow)
  have hout' :
      ((qPrivate * q) * ((2 : ℝ) ^
          (n - (switchingCommonNonneighbors G p S₀).card) *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^
          Fintype.card (RawTupleIndex labels a))) ≤ (outsides.card : ℝ) := by
    simpa only [qPrivate, outsides, radius, W, W', outside] using hout
  exact (mul_le_mul_of_nonneg_right hout' hwindowLower).trans hselected

/-- A single linearly large private block controls every coefficient in the
private-block completion polynomial.  The two degree terms cost at most
`n / 2` and `n`, respectively. -/
lemma switchingPrivateCoefficient_le_of_linear_block
    {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (G : SimpleGraph (Fin n)) (p : I → Fin n × Fin n)
    (S₀ O : Finset (Fin n)) (i₀ : I) {eta R : ℝ}
    (heta : 0 < eta)
    (hblock : eta * n ≤
      ((switchingPrivateNeighbors G p i₀ S₀).card : ℝ))
    (hR : 3 / (2 * eta) ≤ R) (v : Fin n) :
    |(if v ∈ switchingCommonNonneighbors G p S₀ then 0 else
          (AKSGraph.degreeInto G v
            (switchingCommonNonneighbors G p S₀) : ℝ) / 2) +
        AKSGraph.degreeInto
          (outsideGraph G (switchingCommonNonneighbors G p S₀)) v O| ≤
      R * (Finset.univ.biUnion
        (switchingPrivateBlocksFin G p S₀)).card := by
  let N := switchingCommonNonneighbors G p S₀
  let W := switchingPrivateBlocksFin G p S₀
  have hNnat : AKSGraph.degreeInto G v N ≤ n :=
    (AKSGraph.degreeInto_le_card G v N).trans <| by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ N)
  have hOnat : AKSGraph.degreeInto (outsideGraph G N) v O ≤ n :=
    (AKSGraph.degreeInto_le_card (outsideGraph G N) v O).trans <| by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ O)
  have hN : (AKSGraph.degreeInto G v N : ℝ) ≤ n := by
    exact_mod_cast hNnat
  have hO : (AKSGraph.degreeInto (outsideGraph G N) v O : ℝ) ≤ n := by
    exact_mod_cast hOnat
  have hcoef :
      |(if v ∈ N then 0 else (AKSGraph.degreeInto G v N : ℝ) / 2) +
          AKSGraph.degreeInto (outsideGraph G N) v O| ≤
        (3 / 2 : ℝ) * n := by
    rw [abs_of_nonneg]
    · split <;> linarith
    · split <;> positivity
  have hblockSub : switchingPrivateNeighbors G p i₀ S₀ ⊆
      Finset.univ.biUnion W := by
    intro x hx
    apply Finset.mem_biUnion.mpr
    refine ⟨Fintype.equivFin I i₀, Finset.mem_univ _, ?_⟩
    simpa only [W, switchingPrivateBlocksFin, Equiv.symm_apply_apply] using hx
  have hblockUnion : ((switchingPrivateNeighbors G p i₀ S₀).card : ℝ) ≤
      ((Finset.univ.biUnion W).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hblockSub
  have hlinear : eta * n ≤ ((Finset.univ.biUnion W).card : ℝ) :=
    hblock.trans hblockUnion
  have hscale : (3 / 2 : ℝ) * n ≤
      R * ((Finset.univ.biUnion W).card : ℝ) := by
    calc
      (3 / 2 : ℝ) * n = (3 / (2 * eta)) * (eta * n) := by
        field_simp
      _ ≤ (3 / (2 * eta)) * ((Finset.univ.biUnion W).card : ℝ) := by
        gcongr
      _ ≤ R * ((Finset.univ.biUnion W).card : ℝ) := by
        gcongr
  simpa only [N, W] using hcoef.trans hscale

/-- Hoeffding's binomial loss is uniform over every coordinate set of
cardinality at most `n` at threshold `K * √n`. -/
lemma binomialTailBound_mul_sqrt_le
    {α : Type*} [Fintype α] [DecidableEq α]
    (I : Finset α) (n : ℕ) (K : ℝ) (hcard : I.card ≤ n) :
    binomialTailBound I (K * Real.sqrt n) ≤
      2 * Real.exp (-2 * K ^ 2) := by
  unfold binomialTailBound
  split_ifs with hI
  · positivity
  · have hIposNat : 0 < I.card := Nat.pos_of_ne_zero hI
    have hIpos : 0 < (I.card : ℝ) := by exact_mod_cast hIposNat
    have hcardReal : (I.card : ℝ) ≤ n := by exact_mod_cast hcard
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hsquare : (K * Real.sqrt n) ^ 2 = K ^ 2 * n := by
      rw [mul_pow, Real.sq_sqrt hn0]
    rw [hsquare]
    gcongr
    rw [div_le_iff₀ hIpos]
    nlinarith [mul_le_mul_of_nonneg_left hcardReal (sq_nonneg K)]

/-- The complete collection of private-block and leftover-coordinate
binomial losses is bounded by `m + 2` copies of the uniform tail. -/
lemma sum_binomialTailBound_mul_sqrt_le
    {N m n : ℕ} (W : Fin m → Finset (Fin N))
    (outside : Finset (Fin N)) (K : ℝ) (hNn : N ≤ n) :
    ((∑ k, binomialTailBound (W k) (K * Real.sqrt n)) +
        binomialTailBound outside (K * Real.sqrt n)) +
      binomialTailBound outside (K * Real.sqrt n) ≤
        2 * (m + 2) * Real.exp (-2 * K ^ 2) := by
  have htail (I : Finset (Fin N)) :
      binomialTailBound I (K * Real.sqrt n) ≤
        2 * Real.exp (-2 * K ^ 2) := by
    apply binomialTailBound_mul_sqrt_le I n K
    exact (Finset.card_le_card (Finset.subset_univ I)).trans <| by
      simpa only [Finset.card_univ, Fintype.card_fin] using hNn
  calc
    ((∑ k, binomialTailBound (W k) (K * Real.sqrt n)) +
          binomialTailBound outside (K * Real.sqrt n)) +
        binomialTailBound outside (K * Real.sqrt n) ≤
      ((∑ _k : Fin m, 2 * Real.exp (-2 * K ^ 2)) +
          2 * Real.exp (-2 * K ^ 2)) +
        2 * Real.exp (-2 * K ^ 2) := by
      gcongr
      all_goals exact htail _
    _ = 2 * (m + 2) * Real.exp (-2 * K ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

/-- With cubic and square-root-scaled deviation thresholds, the private
completion rate retains any constant `q` left after the two dimensionless
losses. -/
lemma privateCompletionRate_ge_scaled
    {N m n : ℕ} (hn : 1 ≤ n) (hNn : N ≤ n)
    (W : Fin m → Finset (Fin N)) (outside : Finset (Fin N))
    (R Kvar Ktail q : ℝ) (hKvar : Kvar ≠ 0)
    (hbudget : q + R ^ 2 / Kvar ^ 2 +
        2 * (m + 2) * Real.exp (-2 * Ktail ^ 2) ≤ 1) :
    q ≤ 1 -
        (R ^ 2 * (N : ℝ) ^ 3) /
          (Kvar * Real.sqrt n ^ 3) ^ 2 -
        ((∑ k, binomialTailBound (W k) (Ktail * Real.sqrt n)) +
          binomialTailBound outside (Ktail * Real.sqrt n)) -
        binomialTailBound outside (Ktail * Real.sqrt n) := by
  have hNpow : (N : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := by
    gcongr
  have hden : 0 ≤ (Kvar * Real.sqrt n ^ 3) ^ 2 := sq_nonneg _
  have hfrac : (N : ℝ) ^ 3 / (Kvar * Real.sqrt n ^ 3) ^ 2 ≤
      1 / Kvar ^ 2 := by
    calc
      (N : ℝ) ^ 3 / (Kvar * Real.sqrt n ^ 3) ^ 2 ≤
          (n : ℝ) ^ 3 / (Kvar * Real.sqrt n ^ 3) ^ 2 :=
        div_le_div_of_nonneg_right hNpow hden
      _ = 1 / Kvar ^ 2 := natCube_div_scaled_sqrtCube_sq hn hKvar
  have hvar : (R ^ 2 * (N : ℝ) ^ 3) /
        (Kvar * Real.sqrt n ^ 3) ^ 2 ≤ R ^ 2 / Kvar ^ 2 := by
    calc
      (R ^ 2 * (N : ℝ) ^ 3) / (Kvar * Real.sqrt n ^ 3) ^ 2 =
          R ^ 2 * ((N : ℝ) ^ 3 / (Kvar * Real.sqrt n ^ 3) ^ 2) := by
        ring
      _ ≤ R ^ 2 * (1 / Kvar ^ 2) :=
        mul_le_mul_of_nonneg_left hfrac (sq_nonneg R)
      _ = R ^ 2 / Kvar ^ 2 := by ring
  have htail := sum_binomialTailBound_mul_sqrt_le
    W outside Ktail hNn
  linarith

/-- Nonnegative-rate specialization of `privateCompletionRate_ge_scaled`. -/
lemma privateCompletionRate_nonneg_scaled
    {N m n : ℕ} (hn : 1 ≤ n) (hNn : N ≤ n)
    (W : Fin m → Finset (Fin N)) (outside : Finset (Fin N))
    (R Kvar Ktail : ℝ) (hKvar : Kvar ≠ 0)
    (hbudget : R ^ 2 / Kvar ^ 2 +
        2 * (m + 2) * Real.exp (-2 * Ktail ^ 2) ≤ 1) :
    0 ≤ 1 -
        (R ^ 2 * (N : ℝ) ^ 3) /
          (Kvar * Real.sqrt n ^ 3) ^ 2 -
        ((∑ k, binomialTailBound (W k) (Ktail * Real.sqrt n)) +
          binomialTailBound outside (Ktail * Real.sqrt n)) -
        binomialTailBound outside (Ktail * Real.sqrt n) := by
  apply privateCompletionRate_ge_scaled hn hNn W outside R Kvar Ktail 0 hKvar
  linarith

/-- A closed-form square-root deviation scale making all `m + 2` binomial
tails cost exactly one quarter in total. -/
lemma exists_binomialTailScale (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧
      2 * (m + 2) * Real.exp (-2 * K ^ 2) = 1 / 4 := by
  let C : ℝ := 8 * (m + 2)
  have hC1 : 1 < C := by
    dsimp only [C]
    have hm : (0 : ℝ) ≤ m := by positivity
    linarith
  have hC0 : 0 < C := zero_lt_one.trans hC1
  let K := Real.sqrt (Real.log C / 2)
  have hlog : 0 < Real.log C := Real.log_pos hC1
  have hK : 0 < K := by
    dsimp only [K]
    exact Real.sqrt_pos.2 (by positivity)
  have hKsq : K ^ 2 = Real.log C / 2 := by
    dsimp only [K]
    rw [Real.sq_sqrt]
    positivity
  refine ⟨K, hK, ?_⟩
  rw [hKsq, show -2 * (Real.log C / 2) = -Real.log C by ring,
    Real.exp_neg, Real.exp_log hC0]
  dsimp only [C]
  field_simp
  ring

/-- A closed-form cubic deviation scale making the private-polynomial
variance loss at most one quarter. -/
noncomputable def privateVarianceScale (R : ℝ) : ℝ :=
  2 * (|R| + 1)

lemma privateVarianceScale_pos (R : ℝ) :
    0 < privateVarianceScale R := by
  unfold privateVarianceScale
  positivity

lemma privateVarianceScale_budget (R : ℝ) :
    R ^ 2 / privateVarianceScale R ^ 2 ≤ 1 / 4 := by
  have hpos := privateVarianceScale_pos R
  rw [div_le_iff₀ (sq_pos_of_pos hpos)]
  unfold privateVarianceScale
  nlinarith [sq_abs R, abs_nonneg R]

/-- Uniform choices of cubic and square-root deviation scales retain at
least half of the private-block completions, independently of `n` and of
the actual block partition. -/
lemma exists_privateCompletionScales (m : ℕ) (R : ℝ) :
    ∃ Kvar Ktail : ℝ, 0 < Kvar ∧ 0 < Ktail ∧
      ∀ {N n : ℕ}, 1 ≤ n → N ≤ n →
      ∀ (W : Fin m → Finset (Fin N)) (outside : Finset (Fin N)),
        1 / 2 ≤ 1 -
          (R ^ 2 * (N : ℝ) ^ 3) /
            (Kvar * Real.sqrt n ^ 3) ^ 2 -
          ((∑ k, binomialTailBound (W k) (Ktail * Real.sqrt n)) +
            binomialTailBound outside (Ktail * Real.sqrt n)) -
          binomialTailBound outside (Ktail * Real.sqrt n) := by
  obtain ⟨Ktail, hKtail, htail⟩ := exists_binomialTailScale m
  refine ⟨privateVarianceScale R, Ktail,
    privateVarianceScale_pos R, hKtail, ?_⟩
  intro N n hn hNn W outside
  apply privateCompletionRate_ge_scaled hn hNn W outside R
    (privateVarianceScale R) Ktail (1 / 2)
    (ne_of_gt (privateVarianceScale_pos R))
  have hvar := privateVarianceScale_budget R
  nlinarith

/-- The degree cluster supplied by KSSS Lemma 13.1 turns bounded switching
labels into the label-to-half-degree-difference estimate required by the
private-block completion step. -/
lemma switchingLabel_degreeDifference_close
    {n : ℕ} {I : Type*} [Fintype I]
    (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (p : I → Fin n × Fin n) (label : I → ℤ) (B : ℝ)
    (hpS : ∀ i, p i ∈ S ×ˢ S)
    (hdegree : ∀ v ∈ S, ∀ w ∈ S,
      |(FiniteES.vertexDegree G v : ℝ) / 2 -
        (FiniteES.vertexDegree G w : ℝ) / 2| ≤ Real.sqrt n)
    (hlabel : ∀ i, |(label i : ℝ)| ≤ B) :
    ∀ i, |(label i : ℝ) -
        ((FiniteES.vertexDegree G (p i).2 : ℝ) -
          (FiniteES.vertexDegree G (p i).1 : ℝ)) / 2| ≤
      B + Real.sqrt n := by
  intro i
  have hpair := hpS i
  simp only [Finset.mem_product] at hpair
  have hdeg := hdegree (p i).1 hpair.1 (p i).2 hpair.2
  calc
    |(label i : ℝ) -
        ((FiniteES.vertexDegree G (p i).2 : ℝ) -
          (FiniteES.vertexDegree G (p i).1 : ℝ)) / 2| =
      |(label i : ℝ) +
        ((FiniteES.vertexDegree G (p i).1 : ℝ) / 2 -
          (FiniteES.vertexDegree G (p i).2 : ℝ) / 2)| := by ring_nf
    _ ≤ |(label i : ℝ)| +
        |(FiniteES.vertexDegree G (p i).1 : ℝ) / 2 -
          (FiniteES.vertexDegree G (p i).2 : ℝ) / 2| := abs_add_le _ _
    _ ≤ B + Real.sqrt n := add_le_add (hlabel i) hdeg

lemma rawTupleIndex_label_abs_le {B : ℕ}
    (a : ℤ → ℕ) (i : RawTupleIndex (switchingLabels B) a) :
    |(i.1.1 : ℝ)| ≤ B := by
  have hi := i.1.2
  simp only [switchingLabels, Finset.mem_Icc] at hi
  rw [abs_le]
  constructor
  · exact_mod_cast hi.1
  · exact_mod_cast hi.2

/-- Canonical square-root scale for all private-count deviations after the
first exposure. -/
noncomputable def canonicalPrivateDeviationScale (B s : ℕ) : ℝ :=
  B + canonicalFirstExposureScale s + 2

noncomputable def canonicalPrivateDeviationCount (B s n : ℕ) : ℕ :=
  ⌈canonicalPrivateDeviationScale B s * Real.sqrt n⌉₊

noncomputable def canonicalPrivateQuadraticConstant
    (eta : ℝ) (B s : ℕ) : ℝ :=
  16 * canonicalPrivateDeviationScale B s ^ 2 / eta

lemma canonicalPrivateDeviationScale_pos (B s : ℕ) :
    0 < canonicalPrivateDeviationScale B s := by
  unfold canonicalPrivateDeviationScale
  have h := canonicalFirstExposureScale_pos s
  positivity

lemma canonicalPrivateQuadraticConstant_pos
    {eta : ℝ} (heta : 0 < eta) (B s : ℕ) :
    0 < canonicalPrivateQuadraticConstant eta B s := by
  unfold canonicalPrivateQuadraticConstant
  exact div_pos (mul_pos (by norm_num)
    (sq_pos_of_pos (canonicalPrivateDeviationScale_pos B s))) heta

/-- The canonical integer count absorbs the label radius, the row-exposure
radius, and the half-integer rounding loss. -/
lemma canonicalPrivateDeviationCount_radius
    (B s n : ℕ) (hn : 1 ≤ n) :
    (B : ℝ) + Real.sqrt n +
          canonicalFirstExposureScale s * Real.sqrt n + 1 / 2 ≤
      (canonicalPrivateDeviationCount B s n : ℝ) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := (Real.one_le_sqrt).2 hnR
  have hB : (0 : ℝ) ≤ B := by positivity
  have hK := canonicalFirstExposureScale_pos s
  calc
    (B : ℝ) + Real.sqrt n +
          canonicalFirstExposureScale s * Real.sqrt n + 1 / 2 ≤
        canonicalPrivateDeviationScale B s * Real.sqrt n := by
      unfold canonicalPrivateDeviationScale
      nlinarith [mul_nonneg hB (sub_nonneg.mpr hsqrt1)]
    _ ≤ (canonicalPrivateDeviationCount B s n : ℝ) := by
      exact Nat.le_ceil _

lemma canonicalPrivateDeviationCount_le
    (B s n : ℕ) (hn : 1 ≤ n) :
    (canonicalPrivateDeviationCount B s n : ℝ) ≤
      2 * canonicalPrivateDeviationScale B s * Real.sqrt n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := (Real.one_le_sqrt).2 hnR
  have hscale : 1 ≤ canonicalPrivateDeviationScale B s := by
    have h := canonicalPrivateDeviationScale_pos B s
    unfold canonicalPrivateDeviationScale at *
    nlinarith [canonicalFirstExposureScale_pos s]
  have hx0 : 0 ≤ canonicalPrivateDeviationScale B s * Real.sqrt n := by
    positivity
  have hceil := (Nat.ceil_lt_add_one hx0).le
  calc
    (canonicalPrivateDeviationCount B s n : ℝ) ≤
        canonicalPrivateDeviationScale B s * Real.sqrt n + 1 := by
      simpa only [canonicalPrivateDeviationCount] using hceil
    _ ≤ 2 * canonicalPrivateDeviationScale B s * Real.sqrt n := by
      nlinarith [mul_le_mul hscale hsqrt1 (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : 0 ≤ canonicalPrivateDeviationScale B s)]

/-- Every block of size at least `eta * n` eventually satisfies all four
private-binomial hypotheses at the canonical square-root scale. -/
lemma exists_privateBlock_geometry_of_linear
    {eta : ℝ} (heta : 0 < eta) (B s : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ b : ℕ, eta * n ≤ (b : ℝ) →
        let D := canonicalPrivateDeviationCount B s n
        1 ≤ b ∧ 1 ≤ b / 2 ∧ 8 * D ≤ b / 2 ∧
          (D : ℝ) ^ 2 ≤
            canonicalPrivateQuadraticConstant eta B s * (b / 2 : ℕ) := by
  let K := canonicalPrivateDeviationScale B s
  have hK : 0 < K := canonicalPrivateDeviationScale_pos B s
  have hsmall : 0 < eta / (32 * K) := by positivity
  obtain ⟨N₀, hN₀⟩ := exists_sqrt_le_mul_natCast _ hsmall
  let N := max 1 N₀
  refine ⟨N, ?_⟩
  intro n hn b hb
  dsimp only
  have hn1 : 1 ≤ n := (le_max_left 1 N₀).trans hn
  have hnN₀ : N₀ ≤ n := (le_max_right 1 N₀).trans hn
  have hsqrt := hN₀ n hnN₀
  have hDreal := canonicalPrivateDeviationCount_le B s n hn1
  have hD : 16 * canonicalPrivateDeviationCount B s n ≤ b := by
    have hreal :
        (16 * canonicalPrivateDeviationCount B s n : ℕ) ≤ b := by
      exact_mod_cast (show
        (16 : ℝ) * canonicalPrivateDeviationCount B s n ≤ b by
          calc
            (16 : ℝ) * canonicalPrivateDeviationCount B s n ≤
                32 * K * Real.sqrt n := by
              calc
                (16 : ℝ) * canonicalPrivateDeviationCount B s n ≤
                    16 * (2 * canonicalPrivateDeviationScale B s *
                      Real.sqrt n) :=
                  mul_le_mul_of_nonneg_left hDreal (by norm_num)
                _ = 32 * K * Real.sqrt n := by simp only [K]; ring
            _ ≤ eta * n := by
              calc
                32 * K * Real.sqrt n ≤
                    32 * K * (eta / (32 * K) * n) := by gcongr
                _ = eta * n := by field_simp
            _ ≤ b := hb)
    exact hreal
  have hDhalf : 8 * canonicalPrivateDeviationCount B s n ≤ b / 2 := by
    omega
  have hDpos : 0 < canonicalPrivateDeviationCount B s n := by
    apply Nat.ceil_pos.mpr
    positivity
  have hbhalf : 1 ≤ b / 2 := by omega
  have hbpos : 1 ≤ b := by omega
  have hbquarter : (b : ℝ) / 4 ≤ ((b / 2 : ℕ) : ℝ) := by
    have hbNat : b ≤ 4 * (b / 2) := by omega
    have hbReal : (b : ℝ) ≤ 4 * ((b / 2 : ℕ) : ℝ) := by exact_mod_cast hbNat
    linarith
  have hDsq : (canonicalPrivateDeviationCount B s n : ℝ) ^ 2 ≤
      4 * K ^ 2 * n := by
    have hsquare := pow_le_pow_left₀ (by positivity) hDreal 2
    have hn0 : (0 : ℝ) ≤ n := by positivity
    calc
      (canonicalPrivateDeviationCount B s n : ℝ) ^ 2 ≤
          (2 * K * Real.sqrt n) ^ 2 := by simpa only [K] using hsquare
      _ = 4 * K ^ 2 * Real.sqrt n ^ 2 := by ring
      _ = 4 * K ^ 2 * n := by rw [Real.sq_sqrt hn0]
  refine ⟨hbpos, hbhalf, hDhalf, hDsq.trans ?_⟩
  calc
    4 * K ^ 2 * n =
        (16 * K ^ 2 / eta) * (eta * n / 4) := by
      field_simp
      norm_num
    _ ≤ (16 * K ^ 2 / eta) * ((b / 2 : ℕ) : ℝ) := by
      gcongr
      exact (div_le_div_of_nonneg_right hb (by norm_num)).trans hbquarter
    _ = canonicalPrivateQuadraticConstant eta B s *
        ((b / 2 : ℕ) : ℝ) := by
      rfl

lemma sqrt_cube_eq_rpow_three_halves (n : ℕ) :
    Real.sqrt n ^ 3 = (n : ℝ) ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

/-- A single ambient `n^(3/2)` coefficient absorbing the first exposure,
private completion, and count-vector perturbation radii. -/
noncomputable def canonicalLowerWindowSlack
    (B s : ℕ) (R Kvar Ktail : ℝ) : ℝ :=
  Kvar + canonicalFirstExposureScale s +
    (s + 1 : ℕ) *
      (2 * canonicalPrivateDeviationScale B s + 1 + 2 * Ktail) * (R + 1)

lemma canonical_completion_radius_le
    (B s n : ℕ) (hn : 1 ≤ n) (R Kvar Ktail : ℝ)
    (hR : 1 ≤ R) (hKtail : 0 ≤ Ktail)
    (U : Finset (Fin n)) :
    Kvar * Real.sqrt n ^ 3 +
          (((s + 1 : ℕ) : ℝ) *
            (max ((canonicalPrivateDeviationCount B s n : ℝ) + 1 / 2)
                (Ktail * Real.sqrt n) + Ktail * Real.sqrt n)) *
            ((R + 1) * U.card) +
          canonicalFirstExposureScale s * Real.sqrt n ^ 3 ≤
      canonicalLowerWindowSlack B s R Kvar Ktail *
        (n : ℝ) ^ (3 / 2 : ℝ) := by
  let Kdev := canonicalPrivateDeviationScale B s
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt n := (Real.one_le_sqrt).2 hnR
  have hsqrt0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hD := canonicalPrivateDeviationCount_le B s n hn
  have hDhalf : (canonicalPrivateDeviationCount B s n : ℝ) + 1 / 2 ≤
      (2 * Kdev + 1) * Real.sqrt n := by
    dsimp only [Kdev]
    nlinarith
  have hA0 : 0 ≤ (canonicalPrivateDeviationCount B s n : ℝ) + 1 / 2 := by
    positivity
  have hB0 : 0 ≤ Ktail * Real.sqrt n := mul_nonneg hKtail hsqrt0
  have hband :
      max ((canonicalPrivateDeviationCount B s n : ℝ) + 1 / 2)
          (Ktail * Real.sqrt n) + Ktail * Real.sqrt n ≤
        (2 * Kdev + 1 + 2 * Ktail) * Real.sqrt n := by
    have hA : (canonicalPrivateDeviationCount B s n : ℝ) + 1 / 2 ≤
        ((2 * Kdev + 1) + Ktail) * Real.sqrt n := by
      calc
        (canonicalPrivateDeviationCount B s n : ℝ) + 1 / 2 ≤
            (2 * Kdev + 1) * Real.sqrt n := hDhalf
        _ ≤ ((2 * Kdev + 1) + Ktail) * Real.sqrt n := by
          apply mul_le_mul_of_nonneg_right _ hsqrt0
          linarith
    have hB : Ktail * Real.sqrt n ≤
        ((2 * Kdev + 1) + Ktail) * Real.sqrt n := by
      have hKdev := canonicalPrivateDeviationScale_pos B s
      apply mul_le_mul_of_nonneg_right _ hsqrt0
      dsimp only [Kdev]
      linarith
    have hmax : max ((canonicalPrivateDeviationCount B s n : ℝ) + 1 / 2)
        (Ktail * Real.sqrt n) ≤
          ((2 * Kdev + 1) + Ktail) * Real.sqrt n := max_le hA hB
    have hadd : max ((canonicalPrivateDeviationCount B s n : ℝ) + 1 / 2)
          (Ktail * Real.sqrt n) + Ktail * Real.sqrt n ≤
        ((2 * Kdev + 1) + Ktail) * Real.sqrt n +
          Ktail * Real.sqrt n := by
      simpa only [add_comm] using
        add_le_add_right hmax (Ktail * Real.sqrt n)
    calc
      _ ≤ _ := hadd
      _ = (2 * Kdev + 1 + 2 * Ktail) * Real.sqrt n := by ring
  have hU : (U.card : ℝ) ≤ n := by
    have hUNat : U.card ≤ n := by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ U)
    exact_mod_cast hUNat
  have hmiddle :
      (((s + 1 : ℕ) : ℝ) *
            (max ((canonicalPrivateDeviationCount B s n : ℝ) + 1 / 2)
                (Ktail * Real.sqrt n) + Ktail * Real.sqrt n)) *
            ((R + 1) * U.card) ≤
        ((s + 1 : ℕ) : ℝ) * (2 * Kdev + 1 + 2 * Ktail) * (R + 1) *
          (Real.sqrt n * n) := by
    calc
      (((s + 1 : ℕ) : ℝ) *
            (max ((canonicalPrivateDeviationCount B s n : ℝ) + 1 / 2)
                (Ktail * Real.sqrt n) + Ktail * Real.sqrt n)) *
            ((R + 1) * U.card) ≤
          (((s + 1 : ℕ) : ℝ) *
            ((2 * Kdev + 1 + 2 * Ktail) * Real.sqrt n)) *
            ((R + 1) * n) := by
        have hKdev := canonicalPrivateDeviationScale_pos B s
        have hC : 0 ≤ 2 * Kdev + 1 + 2 * Ktail := by
          dsimp only [Kdev]
          linarith
        have hL : ((s + 1 : ℕ) : ℝ) *
              (max ((canonicalPrivateDeviationCount B s n : ℝ) + 1 / 2)
                  (Ktail * Real.sqrt n) + Ktail * Real.sqrt n) ≤
            ((s + 1 : ℕ) : ℝ) *
              ((2 * Kdev + 1 + 2 * Ktail) * Real.sqrt n) :=
          mul_le_mul_of_nonneg_left hband (by positivity)
        have hRfac : (R + 1) * (U.card : ℝ) ≤ (R + 1) * n :=
          mul_le_mul_of_nonneg_left hU (by linarith)
        exact mul_le_mul hL hRfac (by positivity) (by positivity)
      _ = ((s + 1 : ℕ) : ℝ) * (2 * Kdev + 1 + 2 * Ktail) * (R + 1) *
          (Real.sqrt n * n) := by ring
  have hroot : Real.sqrt n * n = Real.sqrt n ^ 3 := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    calc
      Real.sqrt n * n = Real.sqrt n * Real.sqrt n ^ 2 := by
        rw [Real.sq_sqrt hn0]
      _ = Real.sqrt n ^ 3 := by ring
  rw [hroot] at hmiddle
  rw [sqrt_cube_eq_rpow_three_halves n]
  dsimp only [canonicalLowerWindowSlack]
  have hmiddle' :
      (((s + 1 : ℕ) : ℝ) *
            (max ((canonicalPrivateDeviationCount B s n : ℝ) + 1 / 2)
                (Ktail * Real.sqrt n) + Ktail * Real.sqrt n)) *
            ((R + 1) * U.card) ≤
        (((s + 1 : ℕ) : ℝ) *
          (2 * canonicalPrivateDeviationScale B s + 1 + 2 * Ktail) *
            (R + 1)) * (n : ℝ) ^ (3 / 2 : ℝ) := by
    simpa only [Kdev, sqrt_cube_eq_rpow_three_halves n] using hmiddle
  calc
    Kvar * (n : ℝ) ^ (3 / 2 : ℝ) +
          (((s + 1 : ℕ) : ℝ) *
            (max ((canonicalPrivateDeviationCount B s n : ℝ) + 1 / 2)
                (Ktail * Real.sqrt n) + Ktail * Real.sqrt n)) *
            ((R + 1) * U.card) +
          canonicalFirstExposureScale s * (n : ℝ) ^ (3 / 2 : ℝ) ≤
        Kvar * (n : ℝ) ^ (3 / 2 : ℝ) +
          (((s + 1 : ℕ) : ℝ) *
            (2 * canonicalPrivateDeviationScale B s + 1 + 2 * Ktail) *
              (R + 1)) * (n : ℝ) ^ (3 / 2 : ℝ) +
          canonicalFirstExposureScale s * (n : ℝ) ^ (3 / 2 : ℝ) := by
      exact add_le_add
        (add_le_add_right hmiddle' (Kvar * (n : ℝ) ^ (3 / 2 : ℝ)))
        (le_refl _)
    _ = (Kvar + canonicalFirstExposureScale s +
          ((s + 1 : ℕ) : ℝ) *
            (2 * canonicalPrivateDeviationScale B s + 1 + 2 * Ktail) *
              (R + 1)) * (n : ℝ) ^ (3 / 2 : ℝ) := by ring

/-- The powers of two from a reservoir and its complement recombine to the
ambient Boolean-cube factor. -/
lemma pow_two_complement_mul_pow_two {n : ℕ} (N : Finset (Fin n)) :
    (2 : ℝ) ^ (n - N.card) * (2 : ℝ) ^ N.card = (2 : ℝ) ^ n := by
  rw [← pow_add, Nat.sub_add_cancel]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    Finset.card_le_card (Finset.subset_univ N)

/-- Uniform ambient normalization of the common-reservoir factor in the
lower switching count. -/
lemma ambient_switching_lower_factor_le
    {n s : ℕ} (N : Finset (Fin n)) (qPrivate q kappa z : ℝ)
    (hNpos : 1 ≤ N.card) (hqPrivate : 0 ≤ qPrivate) (hq : 0 ≤ q)
    (hkappa : 0 ≤ kappa) (hz : 0 ≤ z) :
    (qPrivate * q * kappa) *
          ((2 : ℝ) ^ n * z ^ s * (n : ℝ) ^ (-(3 / 2 : ℝ))) ≤
      ((qPrivate * q) *
          ((2 : ℝ) ^ (n - N.card) * z ^ s)) *
        (kappa * (N.card : ℝ) ^ (-(3 / 2 : ℝ)) *
          (2 : ℝ) ^ N.card) := by
  have hNle : N.card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ N)
  have hNposReal : 0 < (N.card : ℝ) := by exact_mod_cast hNpos
  have hNleReal : (N.card : ℝ) ≤ n := by exact_mod_cast hNle
  have hrpow : (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤
      (N.card : ℝ) ^ (-(3 / 2 : ℝ)) := by
    exact Real.rpow_le_rpow_of_nonpos hNposReal hNleReal (by norm_num)
  have htwo := pow_two_complement_mul_pow_two N
  calc
    (qPrivate * q * kappa) *
          ((2 : ℝ) ^ n * z ^ s * (n : ℝ) ^ (-(3 / 2 : ℝ))) =
        ((qPrivate * q) *
            ((2 : ℝ) ^ (n - N.card) * z ^ s)) *
          (kappa * (n : ℝ) ^ (-(3 / 2 : ℝ)) *
            (2 : ℝ) ^ N.card) := by
      rw [← htwo]
      ring
    _ ≤ ((qPrivate * q) *
          ((2 : ℝ) ^ (n - N.card) * z ^ s)) *
        (kappa * (N.card : ℝ) ^ (-(3 / 2 : ℝ)) *
          (2 : ℝ) ^ N.card) := by
      gcongr

/-- The complete first-exposure/private-block estimate with the common
reservoir supplied by the lower half of `KSSSBoundedWindow`. -/
theorem exists_card_states_containing_switchingTuple_and_boundedWindow_ge_of_firstExposure
    (hBW : KSSSBoundedWindow) (CRam delta base A tau : ℝ)
    (hCRam : 0 < CRam) (hdelta : 0 < delta) (hbase : 0 < base)
    (hA : 0 < A) (htau : 0 ≤ tau) :
    ∃ (Bwin : ℕ) (kappa : ℝ), 0 < Bwin ∧ 0 < kappa ∧ ∃ N₀ : ℕ,
      ∀ n : ℕ, N₀ ≤ n →
      ∀ (G : SimpleGraph (Fin n)), RamseyFree CRam G →
      ∀ (labels : Finset ℤ) (a : ℤ → ℕ)
        (S S₀ : Finset (Fin n))
        (p : RawTupleIndex labels a → Fin n × Fin n) (Dcommon : ℕ),
        HasLargeCommonNonneighbors G S S₀ delta Dcommon →
        2 * Fintype.card (RawTupleIndex labels a) ≤ Dcommon →
        (∀ j, p j ∈ S ×ˢ S) →
        base * n ≤ (S₀.card : ℝ) →
      ∀ (T : Finset (Fin n × Fin n)),
        (∀ j, p j ∈ T) → PairEndpointsDistinct p →
      ∀ (tMean tRow labelRadius : ℝ)
        (Dprivate : ℕ) (CPrivate q R B Δ t : ℝ),
        0 ≤ q → 1 ≤ R → 0 ≤ B → 0 ≤ Δ → 0 < t →
        0 < tMean → 0 < tRow →
        2 * Fintype.card (RawTupleIndex labels a) ≤
          (switchingFirstExposureDomain G p S₀).card →
        q +
            ((n : ℝ) ^ 3 / tMean ^ 2 +
              (Fintype.card (RawTupleIndex labels a) : ℝ) *
                (((n : ℝ) / 4) / tRow ^ 2)) ≤
          ((2 : ℝ) ^
            (2 * Fintype.card (RawTupleIndex labels a)))⁻¹ →
        0 ≤
          1 - (R ^ 2 * ((Finset.univ.biUnion
              (switchingPrivateBlocksFin G p S₀)).card : ℝ) ^ 3) / t ^ 2 -
            ((∑ k, binomialTailBound
                (reindexedBlock (switchingPrivateBlocksFin G p S₀) k) Δ) +
              binomialTailBound
                ((Finset.univ : Finset (Fin (Finset.univ.biUnion
                  (switchingPrivateBlocksFin G p S₀)).card)) \
                    Finset.univ.biUnion
                      (reindexedBlock (switchingPrivateBlocksFin G p S₀))) Δ) -
            binomialTailBound
              ((Finset.univ : Finset (Fin (Finset.univ.biUnion
                (switchingPrivateBlocksFin G p S₀)).card)) \
                  Finset.univ.biUnion
                    (reindexedBlock (switchingPrivateBlocksFin G p S₀))) B →
        (∀ i, |(i.1.1 : ℝ) -
            ((FiniteES.vertexDegree G (p i).2 : ℝ) -
              (FiniteES.vertexDegree G (p i).1 : ℝ)) / 2| ≤ labelRadius) →
        labelRadius + tRow + 1 / 2 ≤ (Dprivate : ℝ) →
        (∀ i, 1 ≤ (switchingPrivateNeighbors G p i S₀).card) →
        (∀ i, 1 ≤ (switchingPrivateNeighbors G p i S₀).card / 2) →
        (∀ i, 8 * Dprivate ≤
          (switchingPrivateNeighbors G p i S₀).card / 2) →
        (∀ i, (Dprivate : ℝ) ^ 2 ≤
          CPrivate * ((switchingPrivateNeighbors G p i S₀).card / 2 : ℕ)) →
        (∀ O ∈ switchingFirstExposureGood G p S₀
            (switchingFirstExposureMeanPolynomial G p S₀) tMean tRow,
          ∀ v ∈ Finset.univ.biUnion (switchingPrivateBlocksFin G p S₀),
            |(if v ∈ switchingCommonNonneighbors G p S₀ then 0 else
                  (AKSGraph.degreeInto G v
                    (switchingCommonNonneighbors G p S₀) : ℝ) / 2) +
                AKSGraph.degreeInto
                  (outsideGraph G (switchingCommonNonneighbors G p S₀)) v O| ≤
              R * (Finset.univ.biUnion
                (switchingPrivateBlocksFin G p S₀)).card) →
      ∀ x : ℤ,
        |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
            (Probability.edgePolynomial G)| ≤ A * (n : ℝ) ^ (3 / 2 : ℝ) →
        t +
              (((Fintype.card (RawTupleIndex labels a) + 1 : ℕ) : ℝ) *
                (max ((Dprivate : ℝ) + 1 / 2) B + Δ)) *
                ((R + 1) * (Finset.univ.biUnion
                  (switchingPrivateBlocksFin G p S₀)).card) + tMean ≤
            tau * (n : ℝ) ^ (3 / 2 : ℝ) →
        let W := switchingPrivateBlocksFin G p S₀
        let W' := reindexedBlock W
        let outside := (Finset.univ : Finset
          (Fin (Finset.univ.biUnion W).card)) \ Finset.univ.biUnion W'
        let qPrivate := 1 -
            (R ^ 2 * ((Finset.univ.biUnion W).card : ℝ) ^ 3) / t ^ 2 -
            ((∑ k, binomialTailBound (W' k) Δ) +
              binomialTailBound outside Δ) -
            binomialTailBound outside B
        (qPrivate * q * kappa) *
            ((2 : ℝ) ^ n *
              (Real.exp (-8 * CPrivate) / (8 * Real.sqrt n)) ^
                Fintype.card (RawTupleIndex labels a) *
              (n : ℝ) ^ (-(3 / 2 : ℝ))) ≤
          (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
            p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
              |edgeScore G U - x| ≤ (Bwin : ℤ)).card : ℝ) := by
  let eta := delta * base
  have heta : 0 < eta := by dsimp only [eta]; positivity
  let Ares := (A + tau) * eta⁻¹ ^ (3 / 2 : ℝ)
  have hAres : 0 < Ares := by
    dsimp only [Ares]
    positivity
  obtain ⟨Bwin, kappa, hBwin, hkappa, Nwindow, hconditional⟩ :=
    exists_conditional_edgeScore_window_lower_of_ksssBoundedWindow
      hBW (2 * CRam) eta⁻¹ Ares (by positivity) (inv_pos.mpr heta) hAres
  obtain ⟨Nsqrt, hsqrt⟩ := exists_sqrt_le_mul_natCast eta heta
  obtain ⟨Nsize, hsize⟩ := exists_nat_rpow_ge
    1 (Nwindow / eta) (by norm_num)
  let N₀ := max 1 (max Nsqrt Nsize)
  refine ⟨Bwin, kappa, hBwin, hkappa, N₀, ?_⟩
  intro n hn G hG labels a S S₀ p Dcommon hcommon hID hpS hS₀
    T hpT hp tMean tRow labelRadius Dprivate CPrivate q R B Δ t hq hR hB hΔ
    ht htMean htRow hroom hbudget hqPrivate hlabel hRadius hblockPos
    hblockHalf hD hquad hc x hx hMeanScale
  have hn1 : 1 ≤ n := by dsimp only [N₀] at hn; omega
  have hnSqrt : Nsqrt ≤ n := by dsimp only [N₀] at hn; omega
  have hnSize : Nsize ≤ n := by dsimp only [N₀] at hn; omega
  let windowLower :=
    kappa * ((switchingCommonNonneighbors G p S₀).card : ℝ) ^
        (-(3 / 2 : ℝ)) *
      (2 : ℝ) ^ (switchingCommonNonneighbors G p S₀).card
  have hwindowLower : 0 ≤ windowLower := by
    dsimp only [windowLower]
    positivity
  have hresult :=
    card_states_containing_switchingTuple_and_window_ge_of_firstExposure
      T G labels a S₀ p hpT hp tMean tRow labelRadius Dprivate CPrivate q R B Δ t
        hq hR hB hΔ ht htMean htRow hroom hbudget hqPrivate hlabel hRadius
        hblockPos hblockHalf hD hquad hc
        (fun U ↦ |edgeScore G U - x| ≤ (Bwin : ℤ)) windowLower
        hwindowLower (by
          dsimp only
          intro O hO
          have hO' := Finset.mem_filter.mp hO
          have hOsub : O ⊆ (Finset.univ : Finset (Fin n)) \
              switchingCommonNonneighbors G p S₀ := Finset.mem_powerset.mp hO'.1
          have hON : Disjoint O (switchingCommonNonneighbors G p S₀) := by
            apply Finset.disjoint_left.mpr
            intro v hvO hvN
            exact (Finset.mem_sdiff.mp (hOsub hvO)).2 hvN
          let N := switchingCommonNonneighbors G p S₀
          have hNlinear : eta * n ≤ (N.card : ℝ) := by
            simpa only [eta, N] using switchingCommonNonneighbors_card_ge_linear
              G S S₀ p delta base Dcommon hdelta.le hcommon hID hpS hS₀
          have hNwindowReal : (Nwindow : ℝ) ≤ eta * n := by
            have hpow := hsize n hnSize
            rw [Real.rpow_one] at hpow
            simpa only [mul_comm] using (div_le_iff₀ heta).mp hpow
          have hNwindow : Nwindow ≤ N.card := by
            exact_mod_cast hNwindowReal.trans hNlinear
          have hdata := switchingCommonNonneighbors_boundedWindow_hypotheses
            G S S₀ p hCRam hn1 hG hdelta hbase hcommon hID hpS hS₀
              (by simpa only [eta] using hsqrt n hnSqrt)
          have hclose :
              |outsideConditionalMeanPolynomial G N O -
                Probability.expectation (1 / 2 : ℝ)
                  (Probability.edgePolynomial G)| <
                tau * (n : ℝ) ^ (3 / 2 : ℝ) := by
            simpa only [N] using hO'.2.2.trans_le hMeanScale
          have hbulk := conditional_bulk_of_outsideConditionalMean_close_scaled
            G N O (by simpa only [N] using hON) (x : ℝ) eta A tau heta
              hA.le htau hNlinear hx hclose
          have hscore : (edgeScore G O : ℝ) =
              (AKSGraph.edgeCount G O : ℝ) := by
            exact_mod_cast edgeScore_eq_edgeCount G O
          have hw := hconditional n G N O (by simpa only [N] using hON)
            hNwindow (by simpa only [N] using hdata.1)
            (by simpa only [eta, N] using hdata.2 O) x
            (by rw [hscore]; simpa only [Ares, N] using hbulk.le)
          convert hw using 1
          norm_cast
          congr 1
          ext Z
          simp only [Finset.mem_filter, Finset.mem_powerset, N])
  dsimp only [windowLower] at hresult
  let N := switchingCommonNonneighbors G p S₀
  have hNlinear : eta * n ≤ (N.card : ℝ) := by
    simpa only [eta, N] using switchingCommonNonneighbors_card_ge_linear
      G S S₀ p delta base Dcommon hdelta.le hcommon hID hpS hS₀
  have hnposReal : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hNposReal : 0 < (N.card : ℝ) :=
    (mul_pos heta hnposReal).trans_le hNlinear
  have hNpos : 1 ≤ N.card := by exact_mod_cast hNposReal
  let W := switchingPrivateBlocksFin G p S₀
  let W' := reindexedBlock W
  let outside := (Finset.univ : Finset
    (Fin (Finset.univ.biUnion W).card)) \ Finset.univ.biUnion W'
  let qPrivate := 1 -
      (R ^ 2 * ((Finset.univ.biUnion W).card : ℝ) ^ 3) / t ^ 2 -
      ((∑ k, binomialTailBound (W' k) Δ) +
        binomialTailBound outside Δ) -
      binomialTailBound outside B
  have hqPrivate' : 0 ≤ qPrivate := by
    simpa only [qPrivate, W, W', outside] using hqPrivate
  have hfactor := ambient_switching_lower_factor_le
    (s := Fintype.card (RawTupleIndex labels a)) N qPrivate q kappa
    (Real.exp (-8 * CPrivate) / (8 * Real.sqrt n)) hNpos hqPrivate' hq
      hkappa.le (by positivity)
  dsimp only [N, qPrivate, W, W', outside] at hfactor
  have hnormalized := hfactor.trans hresult
  dsimp only at ⊢
  convert hnormalized using 1
  all_goals try rfl
  congr 1
  congr 1
  ext U
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The lower half of the bounded-window theorem transported to an induced
reservoir while keeping its already selected common radius fixed.  This is
the quantifier-correct adapter used when the label set and all subsequent
switching parameters are chosen after the radius. -/
lemma conditional_edgeScore_window_lower_of_boundedWindowData
    (C : ℝ) (B : ℕ)
    (hlower : ∀ H A : ℝ, 0 < H → 0 < A →
      ∃ kappa : ℝ, 0 < kappa ∧ ∃ N : ℕ,
        ∀ (V : Type) [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj],
          N ≤ Fintype.card V → FiniteRamseyFree C G →
          ∀ (e₀ : ℝ) (c : V → ℝ),
            (∀ v, 0 ≤ c v ∧ c v ≤ H * Fintype.card V) →
            ∀ x : ℤ,
              |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
                  (Probability.perturbedEdgePolynomial G e₀ c)| ≤
                  A * (Fintype.card V : ℝ) ^ (3 / 2 : ℝ) →
              kappa * (Fintype.card V : ℝ) ^ (-(3 / 2 : ℝ)) ≤
                Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
                  |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B))
    (H A : ℝ) (hH : 0 < H) (hA : 0 < A) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ N₀ : ℕ,
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (N O : Finset (Fin n)),
        Disjoint O N → N₀ ≤ N.card →
        FiniteRamseyFree C (G.induce (N : Set (Fin n))) →
        (∀ v ∈ N,
          (AKSGraph.degreeInto G v O : ℝ) ≤ H * N.card) →
        ∀ x : ℤ,
          |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
              (Probability.perturbedEdgePolynomial
                (G.induce (N : Set (Fin n))) (edgeScore G O : ℝ)
                (fun v ↦ (AKSGraph.degreeInto G v.1 O : ℝ)))| ≤
              A * (N.card : ℝ) ^ (3 / 2 : ℝ) →
          kappa * (N.card : ℝ) ^ (-(3 / 2 : ℝ)) *
              (2 : ℝ) ^ N.card ≤
            ((N.powerset.filter fun R ↦
              |edgeScore G (O ∪ R) - x| ≤ (B : ℤ)).card : ℝ) := by
  obtain ⟨kappa, hkappa, N₀, hN₀⟩ := hlower H A hH hA
  refine ⟨kappa, hkappa, N₀, ?_⟩
  intro n G N O hON hNcard hRamsey hc x hbulk
  classical
  have hsize : N₀ ≤ Fintype.card (N : Set (Fin n)) := by
    simpa only [card_subtype_coe_finset N] using hNcard
  have hcoeff : ∀ v : (N : Set (Fin n)),
      0 ≤ (AKSGraph.degreeInto G v.1 O : ℝ) ∧
        (AKSGraph.degreeInto G v.1 O : ℝ) ≤
          H * Fintype.card (N : Set (Fin n)) := by
    intro v
    constructor
    · positivity
    · simpa only [card_subtype_coe_finset N] using hc v.1 v.2
  have hprob := hN₀ (N : Set (Fin n))
    (G.induce (N : Set (Fin n))) hsize hRamsey
    (edgeScore G O : ℝ)
    (fun v ↦ (AKSGraph.degreeInto G v.1 O : ℝ)) hcoeff x
    (by simpa only [card_subtype_coe_finset N] using hbulk)
  exact card_conditional_edgeScore_window_ge_of_probability
    G N O hON x B
      (kappa * (N.card : ℝ) ^ (-(3 / 2 : ℝ)))
      (by simpa only [card_subtype_coe_finset N] using hprob)

theorem exists_card_states_containing_switchingTuple_and_boundedWindow_ge_of_firstExposure_of_data
    (CRam : ℝ) (Bwin : ℕ)
    (hlower : ∀ H A : ℝ, 0 < H → 0 < A →
      ∃ kappa : ℝ, 0 < kappa ∧ ∃ N : ℕ,
        ∀ (V : Type) [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj],
          N ≤ Fintype.card V → FiniteRamseyFree (2 * CRam) G →
          ∀ (e₀ : ℝ) (c : V → ℝ),
            (∀ v, 0 ≤ c v ∧ c v ≤ H * Fintype.card V) →
            ∀ x : ℤ,
              |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
                  (Probability.perturbedEdgePolynomial G e₀ c)| ≤
                  A * (Fintype.card V : ℝ) ^ (3 / 2 : ℝ) →
              kappa * (Fintype.card V : ℝ) ^ (-(3 / 2 : ℝ)) ≤
                Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
                  |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ Bwin))
    (delta base A tau : ℝ)
    (hCRam : 0 < CRam) (hdelta : 0 < delta) (hbase : 0 < base)
    (hA : 0 < A) (htau : 0 ≤ tau) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ N₀ : ℕ,
      ∀ n : ℕ, N₀ ≤ n →
      ∀ (G : SimpleGraph (Fin n)), RamseyFree CRam G →
      ∀ (labels : Finset ℤ) (a : ℤ → ℕ)
        (S S₀ : Finset (Fin n))
        (p : RawTupleIndex labels a → Fin n × Fin n) (Dcommon : ℕ),
        HasLargeCommonNonneighbors G S S₀ delta Dcommon →
        2 * Fintype.card (RawTupleIndex labels a) ≤ Dcommon →
        (∀ j, p j ∈ S ×ˢ S) →
        base * n ≤ (S₀.card : ℝ) →
      ∀ (T : Finset (Fin n × Fin n)),
        (∀ j, p j ∈ T) → PairEndpointsDistinct p →
      ∀ (tMean tRow labelRadius : ℝ)
        (Dprivate : ℕ) (CPrivate q R B Δ t : ℝ),
        0 ≤ q → 1 ≤ R → 0 ≤ B → 0 ≤ Δ → 0 < t →
        0 < tMean → 0 < tRow →
        2 * Fintype.card (RawTupleIndex labels a) ≤
          (switchingFirstExposureDomain G p S₀).card →
        q +
            ((n : ℝ) ^ 3 / tMean ^ 2 +
              (Fintype.card (RawTupleIndex labels a) : ℝ) *
                (((n : ℝ) / 4) / tRow ^ 2)) ≤
          ((2 : ℝ) ^
            (2 * Fintype.card (RawTupleIndex labels a)))⁻¹ →
        0 ≤
          1 - (R ^ 2 * ((Finset.univ.biUnion
              (switchingPrivateBlocksFin G p S₀)).card : ℝ) ^ 3) / t ^ 2 -
            ((∑ k, binomialTailBound
                (reindexedBlock (switchingPrivateBlocksFin G p S₀) k) Δ) +
              binomialTailBound
                ((Finset.univ : Finset (Fin (Finset.univ.biUnion
                  (switchingPrivateBlocksFin G p S₀)).card)) \
                    Finset.univ.biUnion
                      (reindexedBlock (switchingPrivateBlocksFin G p S₀))) Δ) -
            binomialTailBound
              ((Finset.univ : Finset (Fin (Finset.univ.biUnion
                (switchingPrivateBlocksFin G p S₀)).card)) \
                  Finset.univ.biUnion
                    (reindexedBlock (switchingPrivateBlocksFin G p S₀))) B →
        (∀ i, |(i.1.1 : ℝ) -
            ((FiniteES.vertexDegree G (p i).2 : ℝ) -
              (FiniteES.vertexDegree G (p i).1 : ℝ)) / 2| ≤ labelRadius) →
        labelRadius + tRow + 1 / 2 ≤ (Dprivate : ℝ) →
        (∀ i, 1 ≤ (switchingPrivateNeighbors G p i S₀).card) →
        (∀ i, 1 ≤ (switchingPrivateNeighbors G p i S₀).card / 2) →
        (∀ i, 8 * Dprivate ≤
          (switchingPrivateNeighbors G p i S₀).card / 2) →
        (∀ i, (Dprivate : ℝ) ^ 2 ≤
          CPrivate * ((switchingPrivateNeighbors G p i S₀).card / 2 : ℕ)) →
        (∀ O ∈ switchingFirstExposureGood G p S₀
            (switchingFirstExposureMeanPolynomial G p S₀) tMean tRow,
          ∀ v ∈ Finset.univ.biUnion (switchingPrivateBlocksFin G p S₀),
            |(if v ∈ switchingCommonNonneighbors G p S₀ then 0 else
                  (AKSGraph.degreeInto G v
                    (switchingCommonNonneighbors G p S₀) : ℝ) / 2) +
                AKSGraph.degreeInto
                  (outsideGraph G (switchingCommonNonneighbors G p S₀)) v O| ≤
              R * (Finset.univ.biUnion
                (switchingPrivateBlocksFin G p S₀)).card) →
      ∀ x : ℤ,
        |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
            (Probability.edgePolynomial G)| ≤ A * (n : ℝ) ^ (3 / 2 : ℝ) →
        t +
              (((Fintype.card (RawTupleIndex labels a) + 1 : ℕ) : ℝ) *
                (max ((Dprivate : ℝ) + 1 / 2) B + Δ)) *
                ((R + 1) * (Finset.univ.biUnion
                  (switchingPrivateBlocksFin G p S₀)).card) + tMean ≤
            tau * (n : ℝ) ^ (3 / 2 : ℝ) →
        let W := switchingPrivateBlocksFin G p S₀
        let W' := reindexedBlock W
        let outside := (Finset.univ : Finset
          (Fin (Finset.univ.biUnion W).card)) \ Finset.univ.biUnion W'
        let qPrivate := 1 -
            (R ^ 2 * ((Finset.univ.biUnion W).card : ℝ) ^ 3) / t ^ 2 -
            ((∑ k, binomialTailBound (W' k) Δ) +
              binomialTailBound outside Δ) -
            binomialTailBound outside B
        (qPrivate * q * kappa) *
            ((2 : ℝ) ^ n *
              (Real.exp (-8 * CPrivate) / (8 * Real.sqrt n)) ^
                Fintype.card (RawTupleIndex labels a) *
              (n : ℝ) ^ (-(3 / 2 : ℝ))) ≤
          (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
            p ∈ switchingTupleFinset T (edgeScore G) labels a U ∧
              |edgeScore G U - x| ≤ (Bwin : ℤ)).card : ℝ) := by
  let eta := delta * base
  have heta : 0 < eta := by dsimp only [eta]; positivity
  let Ares := (A + tau) * eta⁻¹ ^ (3 / 2 : ℝ)
  have hAres : 0 < Ares := by
    dsimp only [Ares]
    positivity
  obtain ⟨kappa, hkappa, Nwindow, hconditional⟩ :=
    conditional_edgeScore_window_lower_of_boundedWindowData
      (2 * CRam) Bwin hlower eta⁻¹ Ares (inv_pos.mpr heta) hAres
  obtain ⟨Nsqrt, hsqrt⟩ := exists_sqrt_le_mul_natCast eta heta
  obtain ⟨Nsize, hsize⟩ := exists_nat_rpow_ge
    1 (Nwindow / eta) (by norm_num)
  let N₀ := max 1 (max Nsqrt Nsize)
  refine ⟨kappa, hkappa, N₀, ?_⟩
  intro n hn G hG labels a S S₀ p Dcommon hcommon hID hpS hS₀
    T hpT hp tMean tRow labelRadius Dprivate CPrivate q R B Δ t hq hR hB hΔ
    ht htMean htRow hroom hbudget hqPrivate hlabel hRadius hblockPos
    hblockHalf hD hquad hc x hx hMeanScale
  have hn1 : 1 ≤ n := by dsimp only [N₀] at hn; omega
  have hnSqrt : Nsqrt ≤ n := by dsimp only [N₀] at hn; omega
  have hnSize : Nsize ≤ n := by dsimp only [N₀] at hn; omega
  let windowLower :=
    kappa * ((switchingCommonNonneighbors G p S₀).card : ℝ) ^
        (-(3 / 2 : ℝ)) *
      (2 : ℝ) ^ (switchingCommonNonneighbors G p S₀).card
  have hwindowLower : 0 ≤ windowLower := by
    dsimp only [windowLower]
    positivity
  have hresult :=
    card_states_containing_switchingTuple_and_window_ge_of_firstExposure
      T G labels a S₀ p hpT hp tMean tRow labelRadius Dprivate CPrivate q R B Δ t
        hq hR hB hΔ ht htMean htRow hroom hbudget hqPrivate hlabel hRadius
        hblockPos hblockHalf hD hquad hc
        (fun U ↦ |edgeScore G U - x| ≤ (Bwin : ℤ)) windowLower
        hwindowLower (by
          dsimp only
          intro O hO
          have hO' := Finset.mem_filter.mp hO
          have hOsub : O ⊆ (Finset.univ : Finset (Fin n)) \
              switchingCommonNonneighbors G p S₀ := Finset.mem_powerset.mp hO'.1
          have hON : Disjoint O (switchingCommonNonneighbors G p S₀) := by
            apply Finset.disjoint_left.mpr
            intro v hvO hvN
            exact (Finset.mem_sdiff.mp (hOsub hvO)).2 hvN
          let N := switchingCommonNonneighbors G p S₀
          have hNlinear : eta * n ≤ (N.card : ℝ) := by
            simpa only [eta, N] using switchingCommonNonneighbors_card_ge_linear
              G S S₀ p delta base Dcommon hdelta.le hcommon hID hpS hS₀
          have hNwindowReal : (Nwindow : ℝ) ≤ eta * n := by
            have hpow := hsize n hnSize
            rw [Real.rpow_one] at hpow
            simpa only [mul_comm] using (div_le_iff₀ heta).mp hpow
          have hNwindow : Nwindow ≤ N.card := by
            exact_mod_cast hNwindowReal.trans hNlinear
          have hdata := switchingCommonNonneighbors_boundedWindow_hypotheses
            G S S₀ p hCRam hn1 hG hdelta hbase hcommon hID hpS hS₀
              (by simpa only [eta] using hsqrt n hnSqrt)
          have hclose :
              |outsideConditionalMeanPolynomial G N O -
                Probability.expectation (1 / 2 : ℝ)
                  (Probability.edgePolynomial G)| <
                tau * (n : ℝ) ^ (3 / 2 : ℝ) := by
            simpa only [N] using hO'.2.2.trans_le hMeanScale
          have hbulk := conditional_bulk_of_outsideConditionalMean_close_scaled
            G N O (by simpa only [N] using hON) (x : ℝ) eta A tau heta
              hA.le htau hNlinear hx hclose
          have hscore : (edgeScore G O : ℝ) =
              (AKSGraph.edgeCount G O : ℝ) := by
            exact_mod_cast edgeScore_eq_edgeCount G O
          have hw := hconditional n G N O (by simpa only [N] using hON)
            hNwindow (by simpa only [N] using hdata.1)
            (by simpa only [eta, N] using hdata.2 O) x
            (by rw [hscore]; simpa only [Ares, N] using hbulk.le)
          convert hw using 1
          norm_cast
          congr 1
          ext Z
          simp only [Finset.mem_filter, Finset.mem_powerset, N])
  dsimp only [windowLower] at hresult
  let N := switchingCommonNonneighbors G p S₀
  have hNlinear : eta * n ≤ (N.card : ℝ) := by
    simpa only [eta, N] using switchingCommonNonneighbors_card_ge_linear
      G S S₀ p delta base Dcommon hdelta.le hcommon hID hpS hS₀
  have hnposReal : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hNposReal : 0 < (N.card : ℝ) :=
    (mul_pos heta hnposReal).trans_le hNlinear
  have hNpos : 1 ≤ N.card := by exact_mod_cast hNposReal
  let W := switchingPrivateBlocksFin G p S₀
  let W' := reindexedBlock W
  let outside := (Finset.univ : Finset
    (Fin (Finset.univ.biUnion W).card)) \ Finset.univ.biUnion W'
  let qPrivate := 1 -
      (R ^ 2 * ((Finset.univ.biUnion W).card : ℝ) ^ 3) / t ^ 2 -
      ((∑ k, binomialTailBound (W' k) Δ) +
        binomialTailBound outside Δ) -
      binomialTailBound outside B
  have hqPrivate' : 0 ≤ qPrivate := by
    simpa only [qPrivate, W, W', outside] using hqPrivate
  have hfactor := ambient_switching_lower_factor_le
    (s := Fintype.card (RawTupleIndex labels a)) N qPrivate q kappa
    (Real.exp (-8 * CPrivate) / (8 * Real.sqrt n)) hNpos hqPrivate' hq
      hkappa.le (by positivity)
  dsimp only [N, qPrivate, W, W', outside] at hfactor
  have hnormalized := hfactor.trans hresult
  dsimp only at ⊢
  convert hnormalized using 1
  all_goals try rfl
  congr 1
  congr 1
  ext U
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

noncomputable def canonicalPrivateCoefficientScale (eta : ℝ) : ℝ :=
  max 1 (3 / (2 * eta))

lemma canonicalPrivateCoefficientScale_one_le (eta : ℝ) :
    1 ≤ canonicalPrivateCoefficientScale eta := by
  exact le_max_left _ _

lemma canonicalPrivateCoefficientScale_ratio_le (eta : ℝ) :
    3 / (2 * eta) ≤ canonicalPrivateCoefficientScale eta := by
  exact le_max_right _ _

theorem exists_canonical_goodTuple_state_lower_of_data
    (CRam : ℝ) (Bwin : ℕ)
    (hlower : ∀ H A : ℝ, 0 < H → 0 < A →
      ∃ kappa : ℝ, 0 < kappa ∧ ∃ N : ℕ,
        ∀ (V : Type) [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj],
          N ≤ Fintype.card V → FiniteRamseyFree (2 * CRam) G →
          ∀ (e₀ : ℝ) (c : V → ℝ),
            (∀ v, 0 ≤ c v ∧ c v ≤ H * Fintype.card V) →
            ∀ x : ℤ,
              |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
                  (Probability.perturbedEdgePolynomial G e₀ c)| ≤
                  A * (Fintype.card V : ℝ) ^ (3 / 2 : ℝ) →
              kappa * (Fintype.card V : ℝ) ^ (-(3 / 2 : ℝ)) ≤
                Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
                  |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ Bwin))
    (delta base etaPrivate A : ℝ)
    (hCRam : 0 < CRam) (hdelta : 0 < delta) (hbase : 0 < base)
    (hetaPrivate : 0 < etaPrivate) (hA : 0 < A)
    (a : ℤ → ℕ)
    (hspos : 0 < Fintype.card (RawTupleIndex (switchingLabels Bwin) a)) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ N₀ : ℕ,
      ∀ n : ℕ, N₀ ≤ n →
      ∀ (G : SimpleGraph (Fin n)), RamseyFree CRam G →
      ∀ (S S₀ : Finset (Fin n))
        (p : RawTupleIndex (switchingLabels Bwin) a → Fin n × Fin n)
        (Dcommon : ℕ),
        HasLargeCommonNonneighbors G S S₀ delta Dcommon →
        2 * Fintype.card (RawTupleIndex (switchingLabels Bwin) a) ≤ Dcommon →
        (∀ j, p j ∈ S ×ˢ S) →
        base * n ≤ (S₀.card : ℝ) →
        (∀ v ∈ S, ∀ w ∈ S,
          |(FiniteES.vertexDegree G v : ℝ) / 2 -
            (FiniteES.vertexDegree G w : ℝ) / 2| ≤ Real.sqrt n) →
      ∀ (T : Finset (Fin n × Fin n)),
        (∀ j, p j ∈ T) → PairEndpointsDistinct p →
        (∀ i, etaPrivate * n ≤
          ((switchingPrivateNeighbors G p i S₀).card : ℝ)) →
      ∀ x : ℤ,
        |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
            (Probability.edgePolynomial G)| ≤ A * (n : ℝ) ^ (3 / 2 : ℝ) →
        let s := Fintype.card (RawTupleIndex (switchingLabels Bwin) a)
        let R := canonicalPrivateCoefficientScale etaPrivate
        let Kvar := privateVarianceScale R
        let Ktail := Classical.choose (exists_binomialTailScale s)
        let CPrivate := canonicalPrivateQuadraticConstant etaPrivate Bwin s
        (1 / 2 * canonicalFirstExposureRate s * kappa) *
            ((2 : ℝ) ^ n *
              (Real.exp (-8 * CPrivate) / (8 * Real.sqrt n)) ^ s *
              (n : ℝ) ^ (-(3 / 2 : ℝ))) ≤
          (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
            p ∈ switchingTupleFinset T (edgeScore G)
              (switchingLabels Bwin) a U ∧
              |edgeScore G U - x| ≤ (Bwin : ℤ)).card : ℝ) := by
  let s := Fintype.card (RawTupleIndex (switchingLabels Bwin) a)
  let R := canonicalPrivateCoefficientScale etaPrivate
  let Kvar := privateVarianceScale R
  let Ktail := Classical.choose (exists_binomialTailScale s)
  have hKtail : 0 < Ktail :=
    (Classical.choose_spec (exists_binomialTailScale s)).1
  have htail : 2 * (s + 2) * Real.exp (-2 * Ktail ^ 2) = 1 / 4 :=
    (Classical.choose_spec (exists_binomialTailScale s)).2
  let CPrivate := canonicalPrivateQuadraticConstant etaPrivate Bwin s
  let tau := canonicalLowerWindowSlack Bwin s R Kvar Ktail
  have hR : 1 ≤ R := canonicalPrivateCoefficientScale_one_le _
  have hKvar : 0 < Kvar := privateVarianceScale_pos _
  have hCPrivate : 0 < CPrivate :=
    canonicalPrivateQuadraticConstant_pos hetaPrivate Bwin s
  have htau : 0 ≤ tau := by
    dsimp only [tau, canonicalLowerWindowSlack]
    have hdev := canonicalPrivateDeviationScale_pos Bwin s
    have hfirst := canonicalFirstExposureScale_pos s
    positivity
  obtain ⟨kappa, hkappa, Ndata, hdata⟩ :=
    exists_card_states_containing_switchingTuple_and_boundedWindow_ge_of_firstExposure_of_data
      CRam Bwin hlower delta base A tau hCRam hdelta hbase hA htau
  obtain ⟨Ngeom, hgeom⟩ :=
    exists_privateBlock_geometry_of_linear hetaPrivate Bwin s
  let N₀ := max Ndata Ngeom
  refine ⟨kappa, hkappa, N₀, ?_⟩
  intro n hn G hG S S₀ p Dcommon hcommon hID hpS hS₀ hdegree
    T hpT hp hblock x hx
  have hnData : Ndata ≤ n := (le_max_left _ _).trans hn
  have hnGeom : Ngeom ≤ n := (le_max_right _ _).trans hn
  have hn1 : 1 ≤ n := by
    have hi : Nonempty (RawTupleIndex (switchingLabels Bwin) a) :=
      Fintype.card_pos_iff.mp (by simpa only [s] using hspos)
    let i₀ := Classical.choice hi
    exact (Nat.succ_le_iff).2 (Nat.zero_lt_of_lt (p i₀).1.isLt)
  have hsqrtPos : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  have hgeometry (i : RawTupleIndex (switchingLabels Bwin) a) :=
    hgeom n hnGeom (switchingPrivateNeighbors G p i S₀).card (hblock i)
  let W := switchingPrivateBlocksFin G p S₀
  let W' := reindexedBlock W
  let outside := (Finset.univ : Finset
    (Fin (Finset.univ.biUnion W).card)) \ Finset.univ.biUnion W'
  have hWle : (Finset.univ.biUnion W).card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Finset.univ.biUnion W))
  have hprivate :
      1 / 2 ≤ 1 -
        (R ^ 2 * ((Finset.univ.biUnion W).card : ℝ) ^ 3) /
          (Kvar * Real.sqrt n ^ 3) ^ 2 -
        ((∑ k, binomialTailBound (W' k) (Ktail * Real.sqrt n)) +
          binomialTailBound outside (Ktail * Real.sqrt n)) -
        binomialTailBound outside (Ktail * Real.sqrt n) := by
    apply privateCompletionRate_ge_scaled hn1 hWle W' outside R Kvar Ktail (1 / 2)
    · exact ne_of_gt hKvar
    · have hvar := privateVarianceScale_budget R
      rw [htail]
      nlinarith
  have hmain := hdata n hnData G hG (switchingLabels Bwin) a S S₀ p
    Dcommon hcommon hID hpS hS₀ T hpT hp
    (canonicalFirstExposureScale s * Real.sqrt n ^ 3)
    (canonicalFirstExposureScale s * Real.sqrt n)
    ((Bwin : ℝ) + Real.sqrt n)
    (canonicalPrivateDeviationCount Bwin s n) CPrivate
    (canonicalFirstExposureRate s) R
    (Ktail * Real.sqrt n) (Ktail * Real.sqrt n)
    (Kvar * Real.sqrt n ^ 3)
    (canonicalFirstExposureRate_pos s).le hR
    (mul_nonneg hKtail.le (Real.sqrt_nonneg _))
    (mul_nonneg hKtail.le (Real.sqrt_nonneg _))
    (mul_pos hKvar (pow_pos hsqrtPos _))
    (mul_pos (canonicalFirstExposureScale_pos s) (pow_pos hsqrtPos _))
    (mul_pos (canonicalFirstExposureScale_pos s) hsqrtPos)
    (two_mul_card_le_switchingFirstExposureDomain G p S₀ hp)
    (by simpa only [s] using canonicalFirstExposure_scaled_budget n s hn1)
    (by
      simpa only [W, W', outside] using
        (show 0 ≤ 1 -
            (R ^ 2 * ((Finset.univ.biUnion W).card : ℝ) ^ 3) /
              (Kvar * Real.sqrt n ^ 3) ^ 2 -
            ((∑ k, binomialTailBound (W' k) (Ktail * Real.sqrt n)) +
              binomialTailBound outside (Ktail * Real.sqrt n)) -
            binomialTailBound outside (Ktail * Real.sqrt n) by linarith))
    (switchingLabel_degreeDifference_close G S p (fun i ↦ i.1.1)
      Bwin hpS hdegree (rawTupleIndex_label_abs_le a))
    (by simpa only [s] using canonicalPrivateDeviationCount_radius Bwin s n hn1)
    (fun i ↦ (hgeometry i).1)
    (fun i ↦ (hgeometry i).2.1)
    (fun i ↦ (hgeometry i).2.2.1)
    (fun i ↦ (hgeometry i).2.2.2)
    (by
      intro O hO v hv
      let : Nonempty (RawTupleIndex (switchingLabels Bwin) a) :=
        Fintype.card_pos_iff.mp (by simpa only [s] using hspos)
      let i₀ := Classical.choice
        (inferInstance : Nonempty (RawTupleIndex (switchingLabels Bwin) a))
      exact switchingPrivateCoefficient_le_of_linear_block G p S₀ O i₀
        hetaPrivate (hblock i₀)
        (canonicalPrivateCoefficientScale_ratio_le etaPrivate) v)
    x hx
    (by
      simpa only [s, R, Kvar, CPrivate, tau, W] using
        canonical_completion_radius_le Bwin s n hn1 R Kvar Ktail hR hKtail.le
          (Finset.univ.biUnion W))
  dsimp only at hmain ⊢
  calc
    (1 / 2 * canonicalFirstExposureRate s * kappa) *
          ((2 : ℝ) ^ n *
            (Real.exp (-8 * CPrivate) / (8 * Real.sqrt n)) ^ s *
            (n : ℝ) ^ (-(3 / 2 : ℝ))) ≤
        ((1 -
            (R ^ 2 * ((Finset.univ.biUnion W).card : ℝ) ^ 3) /
              (Kvar * Real.sqrt n ^ 3) ^ 2 -
            ((∑ k, binomialTailBound (W' k) (Ktail * Real.sqrt n)) +
              binomialTailBound outside (Ktail * Real.sqrt n)) -
            binomialTailBound outside (Ktail * Real.sqrt n)) *
          canonicalFirstExposureRate s * kappa) *
          ((2 : ℝ) ^ n *
            (Real.exp (-8 * CPrivate) / (8 * Real.sqrt n)) ^ s *
            (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
      gcongr
      exact (canonicalFirstExposureRate_pos s).le
    _ ≤ _ := by simpa only [s, R, Kvar, CPrivate, W, W', outside] using hmain


lemma canonicalFirstExposure_scaled_budget_of_le
    (n s d : ℕ) (hn : 1 ≤ n) (hsd : s ≤ d) :
    canonicalFirstExposureRate d +
        ((n : ℝ) ^ 3 /
            (canonicalFirstExposureScale d * Real.sqrt n ^ 3) ^ 2 +
          (s : ℝ) * (((n : ℝ) / 4) /
            (canonicalFirstExposureScale d * Real.sqrt n) ^ 2)) ≤
      ((2 : ℝ) ^ (2 * s))⁻¹ := by
  have hcanon := canonicalFirstExposure_scaled_budget n d hn
  have hsreal : (s : ℝ) ≤ d := by exact_mod_cast hsd
  have hleft :
      canonicalFirstExposureRate d +
          ((n : ℝ) ^ 3 /
              (canonicalFirstExposureScale d * Real.sqrt n ^ 3) ^ 2 +
            (s : ℝ) * (((n : ℝ) / 4) /
              (canonicalFirstExposureScale d * Real.sqrt n) ^ 2)) ≤
        canonicalFirstExposureRate d +
          ((n : ℝ) ^ 3 /
              (canonicalFirstExposureScale d * Real.sqrt n ^ 3) ^ 2 +
            (d : ℝ) * (((n : ℝ) / 4) /
              (canonicalFirstExposureScale d * Real.sqrt n) ^ 2)) := by
    gcongr
  have hpow : (2 : ℝ) ^ (2 * s) ≤ (2 : ℝ) ^ (2 * d) := by
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left 2 hsd)
  have hinv : ((2 : ℝ) ^ (2 * d))⁻¹ ≤ ((2 : ℝ) ^ (2 * s))⁻¹ := by
    exact (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
  exact hleft.trans (hcanon.trans hinv)

lemma canonical_completion_radius_le_of_le
    (B s d n : ℕ) (hn : 1 ≤ n) (hsd : s ≤ d)
    (R Kvar Ktail : ℝ) (hR : 1 ≤ R) (hKtail : 0 ≤ Ktail)
    (U : Finset (Fin n)) :
    Kvar * Real.sqrt n ^ 3 +
          (((s + 1 : ℕ) : ℝ) *
            (max ((canonicalPrivateDeviationCount B d n : ℝ) + 1 / 2)
                (Ktail * Real.sqrt n) + Ktail * Real.sqrt n)) *
            ((R + 1) * U.card) +
          canonicalFirstExposureScale d * Real.sqrt n ^ 3 ≤
      canonicalLowerWindowSlack B d R Kvar Ktail *
        (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hsd' : ((s + 1 : ℕ) : ℝ) ≤ (d + 1 : ℕ) := by
    exact_mod_cast Nat.add_le_add_right hsd 1
  have hband : 0 ≤
      max ((canonicalPrivateDeviationCount B d n : ℝ) + 1 / 2)
          (Ktail * Real.sqrt n) + Ktail * Real.sqrt n := by
    have htail : 0 ≤ Ktail * Real.sqrt n := by positivity
    exact add_nonneg (le_trans htail (le_max_right _ _)) htail
  have hfac : 0 ≤ (R + 1) * (U.card : ℝ) := by
    positivity
  calc
    Kvar * Real.sqrt n ^ 3 +
          (((s + 1 : ℕ) : ℝ) *
            (max ((canonicalPrivateDeviationCount B d n : ℝ) + 1 / 2)
                (Ktail * Real.sqrt n) + Ktail * Real.sqrt n)) *
            ((R + 1) * U.card) +
          canonicalFirstExposureScale d * Real.sqrt n ^ 3 ≤
        Kvar * Real.sqrt n ^ 3 +
          (((d + 1 : ℕ) : ℝ) *
            (max ((canonicalPrivateDeviationCount B d n : ℝ) + 1 / 2)
                (Ktail * Real.sqrt n) + Ktail * Real.sqrt n)) *
            ((R + 1) * U.card) +
          canonicalFirstExposureScale d * Real.sqrt n ^ 3 := by
      gcongr
    _ ≤ _ := canonical_completion_radius_le B d n hn R Kvar Ktail
      hR hKtail U

theorem exists_uniform_canonical_goodTuple_state_lower_of_data
    (CRam : ℝ) (Bwin : ℕ)
    (hlower : ∀ H A : ℝ, 0 < H → 0 < A →
      ∃ kappa : ℝ, 0 < kappa ∧ ∃ N : ℕ,
        ∀ (V : Type) [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj],
          N ≤ Fintype.card V → FiniteRamseyFree (2 * CRam) G →
          ∀ (e₀ : ℝ) (c : V → ℝ),
            (∀ v, 0 ≤ c v ∧ c v ≤ H * Fintype.card V) →
            ∀ x : ℤ,
              |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
                  (Probability.perturbedEdgePolynomial G e₀ c)| ≤
                  A * (Fintype.card V : ℝ) ^ (3 / 2 : ℝ) →
              kappa * (Fintype.card V : ℝ) ^ (-(3 / 2 : ℝ)) ≤
                Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
                  |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ Bwin))
    (delta base etaPrivate A : ℝ) (d : ℕ)
    (hCRam : 0 < CRam) (hdelta : 0 < delta) (hbase : 0 < base)
    (hetaPrivate : 0 < etaPrivate) (hA : 0 < A) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ N₀ : ℕ,
      ∀ n : ℕ, N₀ ≤ n →
      ∀ (G : SimpleGraph (Fin n)), RamseyFree CRam G →
      ∀ (a : ℤ → ℕ),
        Fintype.card (RawTupleIndex (switchingLabels Bwin) a) ≤ d →
      ∀ (S S₀ : Finset (Fin n))
        (p : RawTupleIndex (switchingLabels Bwin) a → Fin n × Fin n)
        (Dcommon : ℕ),
        HasLargeCommonNonneighbors G S S₀ delta Dcommon →
        2 * Fintype.card (RawTupleIndex (switchingLabels Bwin) a) ≤ Dcommon →
        (∀ j, p j ∈ S ×ˢ S) →
        base * n ≤ (S₀.card : ℝ) →
        (∀ v ∈ S, ∀ w ∈ S,
          |(FiniteES.vertexDegree G v : ℝ) / 2 -
            (FiniteES.vertexDegree G w : ℝ) / 2| ≤ Real.sqrt n) →
      ∀ (T : Finset (Fin n × Fin n)),
        (∀ j, p j ∈ T) → PairEndpointsDistinct p →
        (∀ i, etaPrivate * n ≤
          ((switchingPrivateNeighbors G p i S₀).card : ℝ)) →
      ∀ x : ℤ,
        |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
            (Probability.edgePolynomial G)| ≤ A * (n : ℝ) ^ (3 / 2 : ℝ) →
        let s := Fintype.card (RawTupleIndex (switchingLabels Bwin) a)
        let R := canonicalPrivateCoefficientScale etaPrivate
        let Kvar := privateVarianceScale R
        let Ktail := Classical.choose (exists_binomialTailScale d)
        let CPrivate := canonicalPrivateQuadraticConstant etaPrivate Bwin d
        (1 / 2 * canonicalFirstExposureRate d * kappa) *
            ((2 : ℝ) ^ n *
              (Real.exp (-8 * CPrivate) / (8 * Real.sqrt n)) ^ s *
              (n : ℝ) ^ (-(3 / 2 : ℝ))) ≤
          (((Finset.univ : Finset (Finset (Fin n))).filter fun U ↦
            p ∈ switchingTupleFinset T (edgeScore G)
              (switchingLabels Bwin) a U ∧
              |edgeScore G U - x| ≤ (Bwin : ℤ)).card : ℝ) := by
  let R := canonicalPrivateCoefficientScale etaPrivate
  let Kvar := privateVarianceScale R
  let Ktail := Classical.choose (exists_binomialTailScale d)
  have hKtail : 0 < Ktail :=
    (Classical.choose_spec (exists_binomialTailScale d)).1
  have htail : 2 * (d + 2) * Real.exp (-2 * Ktail ^ 2) = 1 / 4 :=
    (Classical.choose_spec (exists_binomialTailScale d)).2
  let CPrivate := canonicalPrivateQuadraticConstant etaPrivate Bwin d
  let tau := canonicalLowerWindowSlack Bwin d R Kvar Ktail
  have hR : 1 ≤ R := canonicalPrivateCoefficientScale_one_le _
  have hKvar : 0 < Kvar := privateVarianceScale_pos _
  have htau : 0 ≤ tau := by
    dsimp only [tau, canonicalLowerWindowSlack]
    have hdev := canonicalPrivateDeviationScale_pos Bwin d
    have hfirst := canonicalFirstExposureScale_pos d
    positivity
  obtain ⟨kappa, hkappa, Ndata, hdata⟩ :=
    exists_card_states_containing_switchingTuple_and_boundedWindow_ge_of_firstExposure_of_data
      CRam Bwin hlower delta base A tau hCRam hdelta hbase hA htau
  obtain ⟨Ngeom, hgeom⟩ :=
    exists_privateBlock_geometry_of_linear hetaPrivate Bwin d
  let N₀ := max 1 (max Ndata Ngeom)
  refine ⟨kappa, hkappa, N₀, ?_⟩
  intro n hn G hG a hsd S S₀ p Dcommon hcommon hID hpS hS₀ hdegree
    T hpT hp hblock x hx
  let s := Fintype.card (RawTupleIndex (switchingLabels Bwin) a)
  have hnData : Ndata ≤ n :=
    (le_max_left Ndata Ngeom).trans ((le_max_right 1 _).trans hn)
  have hnGeom : Ngeom ≤ n :=
    (le_max_right Ndata Ngeom).trans ((le_max_right 1 _).trans hn)
  have hn1 : 1 ≤ n := (le_max_left 1 _).trans hn
  have hsqrtPos : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  have hgeometry (i : RawTupleIndex (switchingLabels Bwin) a) :=
    hgeom n hnGeom (switchingPrivateNeighbors G p i S₀).card (hblock i)
  let W := switchingPrivateBlocksFin G p S₀
  let W' := reindexedBlock W
  let outside := (Finset.univ : Finset
    (Fin (Finset.univ.biUnion W).card)) \ Finset.univ.biUnion W'
  have hWle : (Finset.univ.biUnion W).card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Finset.univ.biUnion W))
  have htailLe :
      2 * (s + 2) * Real.exp (-2 * Ktail ^ 2) ≤ 1 / 4 := by
    calc
      2 * (s + 2) * Real.exp (-2 * Ktail ^ 2) ≤
          2 * (d + 2) * Real.exp (-2 * Ktail ^ 2) := by
        gcongr
      _ = 1 / 4 := htail
  have hprivate :
      1 / 2 ≤ 1 -
        (R ^ 2 * ((Finset.univ.biUnion W).card : ℝ) ^ 3) /
          (Kvar * Real.sqrt n ^ 3) ^ 2 -
        ((∑ k, binomialTailBound (W' k) (Ktail * Real.sqrt n)) +
          binomialTailBound outside (Ktail * Real.sqrt n)) -
        binomialTailBound outside (Ktail * Real.sqrt n) := by
    apply privateCompletionRate_ge_scaled hn1 hWle W' outside R Kvar Ktail (1 / 2)
    · exact ne_of_gt hKvar
    · have hvar := privateVarianceScale_budget R
      nlinarith
  have hmain := hdata n hnData G hG (switchingLabels Bwin) a S S₀ p
    Dcommon hcommon hID hpS hS₀ T hpT hp
    (canonicalFirstExposureScale d * Real.sqrt n ^ 3)
    (canonicalFirstExposureScale d * Real.sqrt n)
    ((Bwin : ℝ) + Real.sqrt n)
    (canonicalPrivateDeviationCount Bwin d n) CPrivate
    (canonicalFirstExposureRate d) R
    (Ktail * Real.sqrt n) (Ktail * Real.sqrt n)
    (Kvar * Real.sqrt n ^ 3)
    (canonicalFirstExposureRate_pos d).le hR
    (mul_nonneg hKtail.le (Real.sqrt_nonneg _))
    (mul_nonneg hKtail.le (Real.sqrt_nonneg _))
    (mul_pos hKvar (pow_pos hsqrtPos _))
    (mul_pos (canonicalFirstExposureScale_pos d) (pow_pos hsqrtPos _))
    (mul_pos (canonicalFirstExposureScale_pos d) hsqrtPos)
    (two_mul_card_le_switchingFirstExposureDomain G p S₀ hp)
    (by simpa only [s] using
      canonicalFirstExposure_scaled_budget_of_le n s d hn1 hsd)
    (by
      simpa only [W, W', outside] using
        (show 0 ≤ 1 -
            (R ^ 2 * ((Finset.univ.biUnion W).card : ℝ) ^ 3) /
              (Kvar * Real.sqrt n ^ 3) ^ 2 -
            ((∑ k, binomialTailBound (W' k) (Ktail * Real.sqrt n)) +
              binomialTailBound outside (Ktail * Real.sqrt n)) -
            binomialTailBound outside (Ktail * Real.sqrt n) by linarith))
    (switchingLabel_degreeDifference_close G S p (fun i ↦ i.1.1)
      Bwin hpS hdegree (rawTupleIndex_label_abs_le a))
    (by simpa only using canonicalPrivateDeviationCount_radius Bwin d n hn1)
    (fun i ↦ (hgeometry i).1)
    (fun i ↦ (hgeometry i).2.1)
    (fun i ↦ (hgeometry i).2.2.1)
    (fun i ↦ (hgeometry i).2.2.2)
    (by
      intro O hO v hv
      cases isEmpty_or_nonempty (RawTupleIndex (switchingLabels Bwin) a) with
      | inl hI =>
          let : IsEmpty (RawTupleIndex (switchingLabels Bwin) a) := hI
          have : False := by
            change v ∈ Finset.univ.biUnion
              (switchingPrivateBlocksFin G p S₀) at hv
            rw [biUnion_switchingPrivateBlocksFin] at hv
            simpa using hv
          exact this.elim
      | inr hI =>
          let : Nonempty (RawTupleIndex (switchingLabels Bwin) a) := hI
          let i₀ := Classical.choice
            (inferInstance : Nonempty (RawTupleIndex (switchingLabels Bwin) a))
          exact switchingPrivateCoefficient_le_of_linear_block G p S₀ O i₀
            hetaPrivate (hblock i₀)
            (canonicalPrivateCoefficientScale_ratio_le etaPrivate) v)
    x hx
    (by
      simpa only [s, R, Kvar, CPrivate, tau, W] using
        canonical_completion_radius_le_of_le Bwin s d n hn1 hsd
          R Kvar Ktail hR hKtail.le (Finset.univ.biUnion W))
  dsimp only at hmain ⊢
  calc
    (1 / 2 * canonicalFirstExposureRate d * kappa) *
          ((2 : ℝ) ^ n *
            (Real.exp (-8 * CPrivate) / (8 * Real.sqrt n)) ^ s *
            (n : ℝ) ^ (-(3 / 2 : ℝ))) ≤
        ((1 -
            (R ^ 2 * ((Finset.univ.biUnion W).card : ℝ) ^ 3) /
              (Kvar * Real.sqrt n ^ 3) ^ 2 -
            ((∑ k, binomialTailBound (W' k) (Ktail * Real.sqrt n)) +
              binomialTailBound outside (Ktail * Real.sqrt n)) -
            binomialTailBound outside (Ktail * Real.sqrt n)) *
          canonicalFirstExposureRate d * kappa) *
          ((2 : ℝ) ^ n *
            (Real.exp (-8 * CPrivate) / (8 * Real.sqrt n)) ^ s *
            (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
      gcongr
      exact (canonicalFirstExposureRate_pos d).le
    _ ≤ _ := by simpa only [s, R, Kvar, CPrivate, W, W', outside] using hmain


lemma rawMomentExpectation_lower_of_good_state
    {n d : ℕ} (hn : 1 ≤ n)
    (G : SimpleGraph (Fin n)) (T : Finset (Fin n × Fin n))
    (Bwin : ℕ) (a : ℤ → ℕ) (c z : ℝ)
    (hc : 0 ≤ c) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (hsd : Fintype.card (RawTupleIndex (switchingLabels Bwin) a) ≤ d)
    (x : ℤ)
    (hraw :
      ((T.card : ℝ) ^
          Fintype.card (RawTupleIndex (switchingLabels Bwin) a) / 2) *
        (c * ((2 : ℝ) ^ n *
          (z / Real.sqrt n) ^
            Fintype.card (RawTupleIndex (switchingLabels Bwin) a) *
          (n : ℝ) ^ (-(3 / 2 : ℝ)))) ≤
        rawMoment (Finset.univ : Finset (Finset (Fin n)))
          (fun U ↦ |edgeScore G U - x| ≤ (Bwin : ℤ))
          (fun ell U ↦ (switchingCount T (edgeScore G) ell U : ℝ))
          a (switchingLabels Bwin)) :
    (c / 2 * z ^ d) *
          ((T.card : ℝ) / Real.sqrt n) ^
            Fintype.card (RawTupleIndex (switchingLabels Bwin) a) /
          (n : ℝ) ^ (3 / 2 : ℝ) ≤
      rawMomentExpectation (Finset.univ : Finset (Finset (Fin n)))
        (fun U ↦ |edgeScore G U - x| ≤ (Bwin : ℤ))
        (fun ell U ↦ (switchingCount T (edgeScore G) ell U : ℝ))
        a (switchingLabels Bwin) := by
  let s := Fintype.card (RawTupleIndex (switchingLabels Bwin) a)
  let stateLower := c * ((2 : ℝ) ^ n *
    (z / Real.sqrt n) ^ s * (n : ℝ) ^ (-(3 / 2 : ℝ)))
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hzpow : z ^ d ≤ z ^ s :=
    pow_le_pow_of_le_one hz0 hz1 hsd
  have htwo : 0 < (2 : ℝ) ^ n := by positivity
  rw [rawMomentExpectation]
  have hcard : ((Finset.univ : Finset (Finset (Fin n))).card : ℝ) =
      (2 : ℝ) ^ n := by
    norm_num [Nat.cast_pow]
  rw [hcard]
  apply (le_div_iff₀ htwo).2
  calc
    (c / 2 * z ^ d) * ((T.card : ℝ) / Real.sqrt n) ^ s /
          (n : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ n ≤
        (c / 2 * z ^ s) * ((T.card : ℝ) / Real.sqrt n) ^ s /
          (n : ℝ) ^ (3 / 2 : ℝ) * (2 : ℝ) ^ n := by
      gcongr
    _ = ((T.card : ℝ) ^ s / 2) * stateLower := by
      dsimp only [stateLower]
      simp only [div_pow]
      rw [Real.rpow_neg hnpos.le]
      have hnRpow : (n : ℝ) ^ (3 / 2 : ℝ) ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos hnpos _)
      field_simp
    _ ≤ _ := hraw


/-- The reservoir sizes supplied by Lemma 13.1 imply the quantitative lower bound
on the canonical switching-pair set used in the lower raw-moment argument. -/
lemma eventually_switchingPairs_large_from_lemma131_sizes :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (G : SimpleGraph (Fin n)) (S S₀ : Finset (Fin n))
        (delta rho : ℝ),
        S ⊆ S₀ →
        (n : ℝ) ^ (12 / 25 : ℝ) ≤ S.card →
        RichOn G S₀ delta rho (1 / 5) →
        0 < rho → rho ≤ 1 → delta ≤ rho →
        (S.card : ℝ) * (n : ℝ) ^ (12 / 25 : ℝ) / 2 ≤
          (switchingPairs G S S₀ (switchingThreshold rho S₀)).card := by
  have hgrowth := eventually_const_mul_natCast_rpow_le_rpow
    12 (1 / 5 : ℝ) (7 / 25 : ℝ) (by norm_num)
  filter_upwards [Filter.eventually_ge_atTop 1, hgrowth] with n hn hgrowth
  intro G S S₀ delta rho hSS₀ hS hrich hrho hrho1 hdelta
  let b := ⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hpow1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 5 : ℝ) :=
    Real.one_le_rpow hnR (by norm_num)
  have hb : (b : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 5 : ℝ) := by
    have hceil := (Nat.ceil_lt_add_one
      (Real.rpow_nonneg hnpos.le (1 / 5 : ℝ))).le
    change ((⌈(n : ℝ) ^ (1 / 5 : ℝ)⌉₊ : ℕ) : ℝ) ≤ _
    nlinarith
  have hsmallReal : (6 * b : ℕ) ≤ S.card := by
    exact_mod_cast (show (6 : ℝ) * b ≤ S.card by
      calc
        (6 : ℝ) * b ≤ 12 * (n : ℝ) ^ (1 / 5 : ℝ) := by
          nlinarith [Real.rpow_nonneg hnpos.le (1 / 5 : ℝ)]
        _ ≤ (n : ℝ) ^ (12 / 25 : ℝ) := by
          convert hgrowth using 1 <;> norm_num
        _ ≤ S.card := hS)
  have hS₀n : (S₀.card : ℝ) ≤ n := by
    exact_mod_cast (show S₀.card ≤ n by
      simpa only [Finset.card_univ, Fintype.card_fin] using
        Finset.card_le_card (Finset.subset_univ S₀))
  have hbBudget : (S₀.card : ℝ) ^ (1 / 5 : ℝ) ≤ b := by
    calc
      (S₀.card : ℝ) ^ (1 / 5 : ℝ) ≤
          (n : ℝ) ^ (1 / 5 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hS₀n (by norm_num)
      _ ≤ b := by exact_mod_cast Nat.le_ceil _
  have hpair := switchingPairs_large_of_richOn_threshold G S S₀ delta rho
    (1 / 5 : ℝ) b hSS₀ hrich hrho hrho1 hdelta hbBudget hsmallReal
  have hpairReal : (S.card : ℝ) * S.card ≤
      2 * (switchingPairs G S S₀ (switchingThreshold rho S₀)).card := by
    exact_mod_cast hpair
  have hmul := mul_le_mul_of_nonneg_left hS
    (by positivity : (0 : ℝ) ≤ S.card)
  nlinarith


end Erdos88.Switching
