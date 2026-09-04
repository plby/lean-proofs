/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos622.AlmostBipartite
import ErdosProblems.Erdos622.AlonInduction
import ErdosProblems.Erdos622.BoundedInternal
import ErdosProblems.Erdos622.BalancedCutWindowDKM
import ErdosProblems.Erdos622.ForestTransfer

/-!
# Linear-arboricity input for the two-large-cover case

This file contains the graph-independent part of the DKM key lemma.  It
turns Alon's unconditional asymptotic linear-arboricity theorem into the
exact finite lower bound on a linear forest used after vertex sampling.
The separate almost-bipartite structural lemma supplies the bounded-degree
graphs and the numerical edge lower bounds.
-/

namespace Erdos622

open scoped SimpleGraph

attribute [local instance] Classical.propDecidable

universe u

namespace TwoLargeForest

open Filter Finset Real
open scoped BigOperators Topology

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The sharp bounded-difference constants for intersection with a fixed
set vanish away from that set.  Unlike the deliberately coarsened ambient
bound in `SamplingSuitable`, the variance proxy here is exactly `C.card`;
this is essential when internal maximum degree is only of order `sqrt n`. -/
theorem intersectionCount_hasBoundedDifferences
    (C : Finset V) :
    Erdos76.FiniteNibble.HasBoundedDifferences (Finset.univ : Finset V)
      (SamplingSuitable.intersectionCount C)
      (fun v ↦ if v ∈ C then 1 else 0) := by
  intro e _ T hT
  have heT : e ∉ T := by
    intro heT
    exact (Finset.mem_erase.mp (hT heT)).1 rfl
  by_cases heC : e ∈ C
  · have hnot : e ∉ T ∩ C := fun h ↦ heT (Finset.mem_inter.mp h).1
    simp [SamplingSuitable.intersectionCount, heC, heT, hnot]
  · have heq : insert e T ∩ C = T ∩ C := by
      ext w
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hwT, hwC⟩
        · exact (heC hwC).elim
        · exact ⟨hwT, hwC⟩
      · rintro ⟨hwT, hwC⟩
        exact ⟨Or.inr hwT, hwC⟩
    simp [SamplingSuitable.intersectionCount, heq, heC]

/-- Sharp two-sided intersection-count concentration, with denominator
`C.card` rather than the size of the ambient vertex set. -/
theorem intersectionCount_twoSided
    (C : Finset V) {t : ℝ} (ht : 0 ≤ t) :
    ((((Finset.univ : Finset V).powerset.filter fun S ↦
        t ≤ |SamplingSuitable.intersectionCount C S -
          (C.card : ℝ) / 2|).card : ℝ)) ≤
      2 * (2 : ℝ) ^ Fintype.card V *
        exp (-2 * t ^ 2 / C.card) := by
  have h := SamplingSuitable.countEvent_twoSided_le
    (intersectionCount_hasBoundedDifferences C) ht
  rw [SamplingSuitable.bernoulliExpectation_half_intersectionCount] at h
  simpa using h

/-- Uniformize the sharp intersection bound using a positive common upper
bound on the test-set cardinality. -/
theorem intersectionCount_twoSided_of_card_le
    (C : Finset V) {q : ℕ} {t : ℝ}
    (hq : C.card ≤ q) (hqpos : 0 < q) (ht : 0 < t) :
    ((((Finset.univ : Finset V).powerset.filter fun S ↦
        t ≤ |SamplingSuitable.intersectionCount C S -
          (C.card : ℝ) / 2|).card : ℝ)) ≤
      2 * (2 : ℝ) ^ Fintype.card V *
        exp (-2 * t ^ 2 / q) := by
  by_cases hC : C.card = 0
  · have hCempty : C = ∅ := Finset.card_eq_zero.mp hC
    have hfilter :
        (Finset.univ : Finset V).powerset.filter (fun S ↦
          t ≤ |SamplingSuitable.intersectionCount C S -
            (C.card : ℝ) / 2|) = ∅ := by
      ext S
      simp [hCempty, SamplingSuitable.intersectionCount,
        not_le_of_gt ht]
    rw [hfilter]
    norm_num
    positivity
  · have hCpos : 0 < C.card := Nat.pos_of_ne_zero hC
    have hraw := intersectionCount_twoSided C ht.le
    have hfrac : -2 * t ^ 2 / (C.card : ℝ) ≤
        -2 * t ^ 2 / (q : ℝ) := by
      have hcR : (0 : ℝ) < C.card := by exact_mod_cast hCpos
      have hcqR : (C.card : ℝ) ≤ q := by exact_mod_cast hq
      have hnum : 0 ≤ 2 * t ^ 2 := by positivity
      have hdiv := div_le_div_of_nonneg_left hnum hcR hcqR
      calc
        -2 * t ^ 2 / (C.card : ℝ) =
            -(2 * t ^ 2 / (C.card : ℝ)) := by ring
        _ ≤ -(2 * t ^ 2 / (q : ℝ)) := neg_le_neg hdiv
        _ = -2 * t ^ 2 / (q : ℝ) := by ring
    exact hraw.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr hfrac) (by positivity))

/-- Union bound for a family of sharp intersection-count estimates sharing
a common cardinality upper bound. -/
theorem simultaneous_intersectionCount_twoSided_of_card_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (C : I → Finset V) {q : ℕ} {t : ℝ}
    (hcard : ∀ i, (C i).card ≤ q) (hq : 0 < q) (ht : 0 < t) :
    ((((Finset.univ : Finset V).powerset.filter fun S ↦
        ∃ i : I, t ≤
          |SamplingSuitable.intersectionCount (C i) S -
            ((C i).card : ℝ) / 2|).card : ℝ)) ≤
      Fintype.card I *
        (2 * (2 : ℝ) ^ Fintype.card V *
          exp (-2 * t ^ 2 / q)) := by
  let bad : I → Finset (Finset V) := fun i ↦
    (Finset.univ : Finset V).powerset.filter fun S ↦
      t ≤ |SamplingSuitable.intersectionCount (C i) S -
        ((C i).card : ℝ) / 2|
  have hsub : (Finset.univ : Finset V).powerset.filter (fun S ↦
      ∃ i : I, t ≤
        |SamplingSuitable.intersectionCount (C i) S -
          ((C i).card : ℝ) / 2|) ⊆
      (Finset.univ : Finset I).biUnion bad := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨i, hi⟩ := hS.2
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i,
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS.1, hi⟩⟩
  have hnat : ((Finset.univ : Finset V).powerset.filter (fun S ↦
      ∃ i : I, t ≤
        |SamplingSuitable.intersectionCount (C i) S -
          ((C i).card : ℝ) / 2|)).card ≤
      ∑ i : I, (bad i).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have hreal : ((((Finset.univ : Finset V).powerset.filter fun S ↦
      ∃ i : I, t ≤
        |SamplingSuitable.intersectionCount (C i) S -
          ((C i).card : ℝ) / 2|).card : ℝ)) ≤
      ∑ i : I, ((bad i).card : ℝ) := by
    exact_mod_cast hnat
  calc
    _ ≤ ∑ i : I, ((bad i).card : ℝ) := hreal
    _ ≤ ∑ _i : I,
        2 * (2 : ℝ) ^ Fintype.card V * exp (-2 * t ^ 2 / q) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [bad] using
        intersectionCount_twoSided_of_card_le (C i) (hcard i) hq ht
    _ = _ := by simp

/-- Induced degree is the sampled intersection count of the ambient
neighborhood. -/
theorem degree_induce_eq_intersectionCount
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (S : Finset V) (v : (S : Set V)) :
    ((J.induce (S : Set V)).degree v : ℝ) =
      SamplingSuitable.intersectionCount (J.neighborFinset v.1) S := by
  have himage : Subtype.val ''
      (J.induce (S : Set V)).neighborSet v =
      (S ∩ J.neighborFinset v.1 : Finset V) := by
    ext w
    simp [and_comm, and_left_comm]
  have hncard := congrArg Set.ncard himage
  rw [Set.ncard_image_of_injective _ Subtype.val_injective,
    Set.ncard_coe_finset] at hncard
  have hleft : ((J.induce (S : Set V)).neighborSet v).ncard =
      (J.induce (S : Set V)).degree v := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  have hnat : (J.induce (S : Set V)).degree v =
      (S ∩ J.neighborFinset v.1).card := by
    rw [← hleft]
    exact hncard
  unfold SamplingSuitable.intersectionCount
  exact_mod_cast hnat

/-- The real-valued induced-edge statistic is the invariant edge-set
cardinality of the induced graph. -/
theorem inducedEdgeCount_eq_ncard_induce
    (J : SimpleGraph V) [DecidableRel J.Adj] (S : Finset V) :
    Concentration.inducedEdgeCount J S =
      ((J.induce (S : Set V)).edgeSet.ncard : ℝ) := by
  unfold Concentration.inducedEdgeCount
  rw [J.card_filter_edgeFinset_toFinset_subset S]
  have hncard : (J.induce (S : Set V)).edgeSet.ncard =
      (J.induce (S : Set V)).edgeFinset.card := by
    rw [← (J.induce (S : Set V)).coe_edgeFinset, Set.ncard_coe_finset]
  rw [hncard]

/-- In a bipartite bounded-degree graph whose left class has `d` vertices,
the squared-degree variance proxy is at most `2 d q²`.  The left-class
degree sum counts every edge exactly once; this sharper estimate is what
makes a linear-in-`n` edge deviation exponentially unlikely when
`d,q = O(sqrt n)`. -/
theorem sum_degree_sq_le_bipartite_left_card_mul_sq
    (J : SimpleGraph V) [DecidableRel J.Adj]
    (D E : Finset V) (q : ℕ)
    (hbip : J.IsBipartiteWith (D : Set V) (E : Set V))
    (hdegree : ∀ v, J.degree v ≤ q) :
    ∑ v : V, (J.degree v : ℝ) ^ 2 ≤
      2 * (D.card : ℝ) * (q : ℝ) ^ 2 := by
  have hedgeNat : J.edgeFinset.card ≤ D.card * q := by
    rw [← J.isBipartiteWith_sum_degrees_eq_card_edges hbip]
    calc
      ∑ v ∈ D, J.degree v ≤ ∑ _v ∈ D, q := by
        apply Finset.sum_le_sum
        intro v _hv
        exact hdegree v
      _ = D.card * q := by simp
  have hmaxNat : J.maxDegree ≤ q :=
    J.maxDegree_le_of_forall_degree_le q hdegree
  have hproxy := Concentration.sum_degree_sq_le_maxDegree_mul_edges J
  have hedge : (J.edgeFinset.card : ℝ) ≤ D.card * q := by
    exact_mod_cast hedgeNat
  have hmax : (J.maxDegree : ℝ) ≤ q := by
    exact_mod_cast hmaxNat
  calc
    ∑ v : V, (J.degree v : ℝ) ^ 2 ≤
        2 * (J.maxDegree : ℝ) * J.edgeFinset.card := hproxy
    _ ≤ 2 * (q : ℝ) * (D.card * q) := by gcongr
    _ = 2 * (D.card : ℝ) * (q : ℝ) ^ 2 := by ring

/-- Every vertex on the larger side of a cut in an `(n+1)`-regular graph
has at least `|A|-n+1` neighbours on its own side.  Summing degrees gives
the exact original-internal edge lower bound needed by the intermediate
imbalance Alon argument. -/
theorem large_side_internal_edge_lower
    {n : ℕ} (G : SimpleGraph (Fin (2 * n)))
    (hreg : G.IsRegularOfDegree (n + 1))
    {A B : Finset (Fin (2 * n))}
    (hcut : IsCut A B) (hnA : n ≤ A.card) :
    A.card * (A.card - n + 1) ≤
      2 * (internalGraph G A).edgeFinset.card := by
  let H := internalGraph G A
  have hdegLower : ∀ v ∈ A, A.card - n + 1 ≤ H.degree v := by
    intro v hv
    have hsplit := degreeInto_union_of_disjoint G v hcut.1
    rw [hcut.2, degreeInto_univ, hreg.degree_eq] at hsplit
    have hBle := degreeInto_le_card G v B
    have hcards := hcut.card_add_card
    simp only [Fintype.card_fin] at hcards
    rw [internalGraph_degree_eq_degreeInto_of_mem G A v hv]
    omega
  calc
    A.card * (A.card - n + 1) =
        ∑ _v ∈ A, (A.card - n + 1) := by simp
    _ ≤ ∑ v ∈ A, H.degree v := by
      exact Finset.sum_le_sum fun v hv ↦ hdegLower v hv
    _ ≤ ∑ v, H.degree v := by
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ A)
    _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges

/-- The strengthened internal-degree consequence of the retuned tailored
constant `gamma₀ = 1/256`.  The older public helper deliberately returns
the coarser `n/16` bound used by the cover estimates; the original-side
Alon argument needs the sharp `n/128` value. -/
theorem internalGraph_degree_le_oneTwentyEighth_of_tailored
    {n : ℕ} (G : SimpleGraph (Fin (2 * n)))
    {A : Finset (Fin (2 * n))}
    (hmax : Trichotomy.InternalMaxDegree G A
      (TailoredTrichotomy.gamma0 * (2 * n : ℝ))) :
    ∀ v, (internalGraph G A).degree v ≤ n / 128 := by
  intro v
  by_cases hv : v ∈ A
  · rw [internalGraph_degree_eq_degreeInto_of_mem G A v hv]
    have hr := hmax v hv
    have hr' : (degreeInto G v A : ℝ) * 128 ≤ n := by
      calc
        (degreeInto G v A : ℝ) * 128 ≤
            (TailoredTrichotomy.gamma0 * (2 * n : ℝ)) * 128 :=
          mul_le_mul_of_nonneg_right hr (by norm_num)
        _ = n := by rw [TailoredTrichotomy.gamma0]; ring
    have hn : degreeInto G v A * 128 ≤ n := by exact_mod_cast hr'
    exact (Nat.le_div_iff_mul_le (by omega : 0 < 128)).2 hn
  · have hisolated : (internalGraph G A).IsIsolated v := by
      intro w hadj
      exact hv ((internalGraph_adj G A v w).mp hadj).1
    rw [hisolated.degree_eq_zero]
    exact Nat.zero_le _

/-- Lift a sampled forest from a bounded internal subgraph to the sampled
ambient graph, while recovering support in the corresponding restricted
cut part. -/
theorem ContainsLinearForestWith.mono_induce_internalGraph
    {G J : SimpleGraph V} {A S : Finset V} {r : ℕ}
    (hJ : J ≤ internalGraph G A)
    (hforest : ContainsLinearForestWith
      (J.induce (S : Set V)) Finset.univ r) :
    ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S A) r := by
  obtain ⟨F, hFJ, hlinear, _hsupp, hcard⟩ := hforest
  refine ⟨F, ?_, hlinear, ?_, hcard⟩
  · intro u v huv
    have hjuv : J.Adj u.1 v.1 := hFJ huv
    exact internalGraph_le G A (hJ hjuv)
  · intro u hu
    obtain ⟨v, huv⟩ := hu
    apply mem_restrictedPart.mpr
    have hjuv : J.Adj u.1 v.1 := hFJ huv
    exact (internalGraph_adj G A u.1 v.1).mp (hJ hjuv) |>.1

/-- Two one-sided sampled forest witnesses imply goodness whenever their
capacities contain the sampled cardinality difference.  This is the exact
deterministic bridge from the DKM binomial window to `IsKGoodSample`. -/
theorem IsKGoodSample.of_two_linearForests
    {G : SimpleGraph V} {A B S : Finset V} {left right k : ℕ}
    (hcut : IsCut A B)
    (hleft : ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S A) (k + left))
    (hright : ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S B) (k + right))
    (hleftWindow : (restrictedPart S A).card ≤
      (restrictedPart S B).card + left)
    (hrightWindow : (restrictedPart S B).card ≤
      (restrictedPart S A).card + right) :
    IsKGoodSample G A B S k := by
  refine ⟨restrictedParts_isCut hcut, ?_⟩
  by_cases hBA : (restrictedPart S B).card ≤
      (restrictedPart S A).card
  · left
    refine ⟨hBA, hleft.mono_requirement ?_⟩
    omega
  · right
    have hAB : (restrictedPart S A).card ≤
        (restrictedPart S B).card := Nat.le_of_not_ge hBA
    refine ⟨hAB, hright.mono_requirement ?_⟩
    omega

/-- Combine the random-cover matching and sampled linear-arboricity
witnesses on both sides.  The usable capacities are the two maxima appearing
in DKM's definitions of `m₁,m₂`. -/
theorem IsKGoodSample.of_matchings_and_linearForests
    {G : SimpleGraph V} {A B S : Finset V}
    {matchingLeft forestLeft matchingRight forestRight k : ℕ}
    (hcut : IsCut A B)
    (hmatchingLeft : RandomCover.HasMatchingAtLeast
      (internalGraph G A) S (matchingLeft : ℝ))
    (hforestLeft : ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S A) forestLeft)
    (hmatchingRight : RandomCover.HasMatchingAtLeast
      (internalGraph G B) S (matchingRight : ℝ))
    (hforestRight : ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S B) forestRight)
    (hleftWindow : (restrictedPart S A).card ≤
      (restrictedPart S B).card +
        (Nat.max matchingLeft forestLeft - k))
    (hrightWindow : (restrictedPart S B).card ≤
      (restrictedPart S A).card +
        (Nat.max matchingRight forestRight - k))
    (hkLeft : k ≤ Nat.max matchingLeft forestLeft)
    (hkRight : k ≤ Nat.max matchingRight forestRight) :
    IsKGoodSample G A B S k := by
  have hmatchingLeft' : ContainsLinearForestWith
      (G.induce (S : Set V)) (restrictedPart S A) matchingLeft :=
    hmatchingLeft.induce_internalGraph
  have hmatchingRight' : ContainsLinearForestWith
      (G.induce (S : Set V)) (restrictedPart S B) matchingRight :=
    hmatchingRight.induce_internalGraph
  have hleft : ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S A) (Nat.max matchingLeft forestLeft) := by
    rcases le_total matchingLeft forestLeft with h | h
    · simpa [Nat.max_eq_right h] using hforestLeft
    · simpa [Nat.max_eq_left h] using hmatchingLeft'
  have hright : ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S B) (Nat.max matchingRight forestRight) := by
    rcases le_total matchingRight forestRight with h | h
    · simpa [Nat.max_eq_right h] using hforestRight
    · simpa [Nat.max_eq_left h] using hmatchingRight'
  have hleft' := hleft.mono_requirement
    (s := k + (Nat.max matchingLeft forestLeft - k)) (by omega)
  have hright' := hright.mono_requirement
    (s := k + (Nat.max matchingRight forestRight - k)) (by omega)
  exact IsKGoodSample.of_two_linearForests hcut hleft' hright'
    hleftWindow hrightWindow

/-- The exact pair of numerical properties needed to invoke Alon's theorem
on a sampled induced graph. -/
def IsInducedLinearArboricityGood (J : SimpleGraph V) (S : Finset V)
    (epsilon : ℝ) (D r : ℕ) : Prop :=
  (∀ v, (J.induce (S : Set V)).degree v ≤ D) ∧
    (r : ℝ) * ((1 + epsilon) * (D : ℝ) / 2) ≤
      ((J.induce (S : Set V)).edgeSet.ncard : ℝ)

/-- Explicit uniform exceptional-count bound for the numerical input to
Alon's theorem on `J[S]`.  The degree exponent uses the ambient maximum
degree `q`, while the edge exponent retains the sharper squared-degree
variance proxy. -/
theorem not_isInducedLinearArboricityGood_count_le
    (J : SimpleGraph V) {epsilon tDegree tEdge : ℝ} {q D r : ℕ}
    (hq : 0 < q) (htDegree : 0 < tDegree) (htEdge : 0 ≤ tEdge)
    (hmax : ∀ v, J.degree v ≤ q)
    (hdegreeMargin : ∀ v,
      (J.degree v : ℝ) / 2 + tDegree ≤ D)
    (hedgeMargin :
      (r : ℝ) * ((1 + epsilon) * (D : ℝ) / 2) + tEdge ≤
        (J.edgeFinset.card : ℝ) / 4) :
    ((((Finset.univ : Finset V).powerset.filter fun S ↦
        ¬ IsInducedLinearArboricityGood J S epsilon D r).card : ℝ)) ≤
      Fintype.card V *
          (2 * (2 : ℝ) ^ Fintype.card V *
            exp (-2 * tDegree ^ 2 / q)) +
        2 * (2 : ℝ) ^ Fintype.card V *
          exp (-2 * tEdge ^ 2 /
            (∑ v : V, (J.degree v : ℝ) ^ 2)) := by
  let : DecidableRel J.Adj := Classical.decRel J.Adj
  let badDegree := (Finset.univ : Finset V).powerset.filter fun S ↦
    ∃ v : V, tDegree ≤
      |SamplingSuitable.intersectionCount (J.neighborFinset v) S -
        (J.degree v : ℝ) / 2|
  let badEdge := (Finset.univ : Finset V).powerset.filter fun S ↦
    tEdge ≤ |Concentration.inducedEdgeCount J S -
      (J.edgeFinset.card : ℝ) / 4|
  have hsub : (Finset.univ : Finset V).powerset.filter (fun S ↦
      ¬ IsInducedLinearArboricityGood J S epsilon D r) ⊆
      badDegree ∪ badEdge := by
    intro S hS
    have hmem := Finset.mem_filter.mp hS
    have hSU := Finset.mem_powerset.mp hmem.1
    rw [Finset.mem_union]
    simp only [IsInducedLinearArboricityGood, not_and_or,
      not_forall] at hmem
    rcases hmem.2 with hdeg | hedge
    · left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr hSU, ?_⟩
      obtain ⟨v, hv⟩ := hdeg
      refine ⟨v.1, ?_⟩
      have hvNat : D < (J.induce (S : Set V)).degree v :=
        Nat.lt_of_not_ge hv
      have hvReal : (D : ℝ) < (J.induce (S : Set V)).degree v := by
        exact_mod_cast hvNat
      have hmargin := hdegreeMargin v.1
      have hdiff : tDegree ≤
          ((J.induce (S : Set V)).degree v : ℝ) -
            (J.degree v.1 : ℝ) / 2 := by
        linarith
      rw [degree_induce_eq_intersectionCount J S v] at hdiff
      exact hdiff.trans (le_abs_self _)
    · right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr hSU, ?_⟩
      have hedgeLt : ((J.induce (S : Set V)).edgeSet.ncard : ℝ) <
          (r : ℝ) * ((1 + epsilon) * (D : ℝ) / 2) :=
        lt_of_not_ge hedge
      have hdiff : tEdge ≤ (J.edgeFinset.card : ℝ) / 4 -
          ((J.induce (S : Set V)).edgeSet.ncard : ℝ) := by
        linarith
      rw [← inducedEdgeCount_eq_ncard_induce J S] at hdiff
      have habs := neg_le_abs
        (Concentration.inducedEdgeCount J S -
          (J.edgeFinset.card : ℝ) / 4)
      exact hdiff.trans (by simpa only [neg_sub] using habs)
  have hnat : ((Finset.univ : Finset V).powerset.filter (fun S ↦
      ¬ IsInducedLinearArboricityGood J S epsilon D r)).card ≤
      badDegree.card + badEdge.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hreal : ((((Finset.univ : Finset V).powerset.filter fun S ↦
      ¬ IsInducedLinearArboricityGood J S epsilon D r).card : ℝ)) ≤
      (badDegree.card : ℝ) + (badEdge.card : ℝ) := by
    exact_mod_cast hnat
  have hdegrees := simultaneous_intersectionCount_twoSided_of_card_le
    (fun v : V ↦ J.neighborFinset v) (q := q) (t := tDegree)
    (fun v ↦ by simpa [SimpleGraph.card_neighborFinset_eq_degree] using hmax v)
    hq htDegree
  have hedges := Concentration.inducedEdgeCount_twoSided J htEdge
  calc
    _ ≤ (badDegree.card : ℝ) + (badEdge.card : ℝ) := hreal
    _ ≤ _ := by
      dsimp [badDegree, badEdge] at hdegrees hedges ⊢
      exact add_le_add hdegrees hedges

/-- Replace the graph-dependent squared-degree denominator in the preceding
exceptional-count estimate by any positive explicit upper bound. -/
theorem not_isInducedLinearArboricityGood_count_le_of_variance_bound
    (J : SimpleGraph V) {epsilon tDegree tEdge variance : ℝ} {q D r : ℕ}
    (hq : 0 < q) (htDegree : 0 < tDegree) (htEdge : 0 ≤ tEdge)
    (hmax : ∀ v, J.degree v ≤ q)
    (hdegreeMargin : ∀ v,
      (J.degree v : ℝ) / 2 + tDegree ≤ D)
    (hedgeMargin :
      (r : ℝ) * ((1 + epsilon) * (D : ℝ) / 2) + tEdge ≤
        (J.edgeFinset.card : ℝ) / 4)
    (hvariancePos : 0 < ∑ v : V, (J.degree v : ℝ) ^ 2)
    (hvariance : (∑ v : V, (J.degree v : ℝ) ^ 2) ≤ variance) :
    ((((Finset.univ : Finset V).powerset.filter fun S ↦
        ¬ IsInducedLinearArboricityGood J S epsilon D r).card : ℝ)) ≤
      Fintype.card V *
          (2 * (2 : ℝ) ^ Fintype.card V *
            exp (-2 * tDegree ^ 2 / q)) +
        2 * (2 : ℝ) ^ Fintype.card V *
          exp (-2 * tEdge ^ 2 / variance) := by
  have hraw := not_isInducedLinearArboricityGood_count_le J hq
    htDegree htEdge hmax hdegreeMargin hedgeMargin
  have hvariancePos' : 0 < variance := hvariancePos.trans_le hvariance
  have hnum : 0 ≤ 2 * tEdge ^ 2 := by positivity
  have hdiv : (2 * tEdge ^ 2) / variance ≤
      (2 * tEdge ^ 2) / (∑ v : V, (J.degree v : ℝ) ^ 2) :=
    div_le_div_of_nonneg_left hnum hvariancePos hvariance
  have hexp : exp (-2 * tEdge ^ 2 /
        (∑ v : V, (J.degree v : ℝ) ^ 2)) ≤
      exp (-2 * tEdge ^ 2 / variance) := by
    apply Real.exp_le_exp.mpr
    calc
      -2 * tEdge ^ 2 / (∑ v : V, (J.degree v : ℝ) ^ 2) =
          -((2 * tEdge ^ 2) /
            (∑ v : V, (J.degree v : ℝ) ^ 2)) := by ring
      _ ≤ -((2 * tEdge ^ 2) / variance) := neg_le_neg hdiv
      _ = -2 * tEdge ^ 2 / variance := by ring
  have hmul :
      2 * (2 : ℝ) ^ Fintype.card V *
          exp (-2 * tEdge ^ 2 /
            (∑ v : V, (J.degree v : ℝ) ^ 2)) ≤
        2 * (2 : ℝ) ^ Fintype.card V *
          exp (-2 * tEdge ^ 2 / variance) :=
    mul_le_mul_of_nonneg_left hexp (by positivity)
  exact hraw.trans (add_le_add (le_refl _) hmul)

/-- If half of the expected induced-edge count is left as concentration
slack, the edge-failure exponent can be written using the useful ratio
`e(J) / Δ(J)`.  In particular this tends to infinity for the original
internal graph in the square-root imbalance range, even though its maximum
degree may be linear in the ambient order. -/
theorem not_isInducedLinearArboricityGood_count_le_of_edge_slack
    (J : SimpleGraph V) {epsilon tDegree : ℝ} {q D r : ℕ}
    (hq : 0 < q) (htDegree : 0 < tDegree)
    (hedge : 0 < J.edgeFinset.card)
    (hmax : ∀ v, J.degree v ≤ q)
    (hdegreeMargin : ∀ v,
      (J.degree v : ℝ) / 2 + tDegree ≤ D)
    (hcapacity :
      (r : ℝ) * ((1 + epsilon) * (D : ℝ) / 2) ≤
        (J.edgeFinset.card : ℝ) / 8) :
    ((((Finset.univ : Finset V).powerset.filter fun S ↦
        ¬ IsInducedLinearArboricityGood J S epsilon D r).card : ℝ)) ≤
      ((Fintype.card V : ℝ) * 2 *
          exp (-2 * tDegree ^ 2 / q) +
        2 * exp (-(J.edgeFinset.card : ℝ) / (64 * q))) *
          (2 : ℝ) ^ Fintype.card V := by
  let : DecidableRel J.Adj := Classical.decRel J.Adj
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hedgeR : (0 : ℝ) < J.edgeFinset.card := by exact_mod_cast hedge
  have hsumDegreesPos : 0 < ∑ v : V, J.degree v := by
    rw [J.sum_degrees_eq_twice_card_edges]
    omega
  have hsumDegreesPosR : (0 : ℝ) < ∑ v : V, (J.degree v : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hsumDegreesPos
  have hdegreeLeSq : ∀ v : V,
      (J.degree v : ℝ) ≤ (J.degree v : ℝ) ^ 2 := by
    intro v
    by_cases hv : J.degree v = 0
    · simp [hv]
    · have hvOne : (1 : ℝ) ≤ J.degree v := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hv
      nlinarith [show (0 : ℝ) ≤ J.degree v by positivity]
  have hvariancePos :
      0 < ∑ v : V, (J.degree v : ℝ) ^ 2 :=
    hsumDegreesPosR.trans_le (Finset.sum_le_sum fun v _ ↦ hdegreeLeSq v)
  have hmaxDegree : J.maxDegree ≤ q :=
    J.maxDegree_le_of_forall_degree_le q hmax
  have hvariance :
      (∑ v : V, (J.degree v : ℝ) ^ 2) ≤
        2 * (q : ℝ) * J.edgeFinset.card := by
    calc
      (∑ v : V, (J.degree v : ℝ) ^ 2) ≤
          2 * J.maxDegree * J.edgeFinset.card :=
        Concentration.sum_degree_sq_le_maxDegree_mul_edges J
      _ ≤ 2 * (q : ℝ) * J.edgeFinset.card := by
        gcongr
  have hedgeMargin :
      (r : ℝ) * ((1 + epsilon) * (D : ℝ) / 2) +
          (J.edgeFinset.card : ℝ) / 8 ≤
        (J.edgeFinset.card : ℝ) / 4 := by
    linarith
  have hraw :=
    not_isInducedLinearArboricityGood_count_le_of_variance_bound J hq
      htDegree (by positivity : (0 : ℝ) ≤ J.edgeFinset.card / 8)
      hmax hdegreeMargin hedgeMargin hvariancePos hvariance
  have hexponent :
      -2 * ((J.edgeFinset.card : ℝ) / 8) ^ 2 /
          (2 * (q : ℝ) * J.edgeFinset.card) =
        -(J.edgeFinset.card : ℝ) / (64 * q) := by
    field_simp [ne_of_gt hqR, ne_of_gt hedgeR]
    ring
  rw [hexponent] at hraw
  calc
    _ ≤ (Fintype.card V : ℝ) *
          (2 * (2 : ℝ) ^ Fintype.card V *
            exp (-2 * tDegree ^ 2 / q)) +
        2 * (2 : ℝ) ^ Fintype.card V *
          exp (-(J.edgeFinset.card : ℝ) / (64 * q)) := hraw
    _ = _ := by ring

/-- Normalized corollary of the explicit exceptional-count estimate.  All
asymptotic scalar work is isolated in the two displayed exponential-tail
hypotheses. -/
theorem not_isInducedLinearArboricityGood_count_le_fraction
    (J : SimpleGraph V) {epsilon tDegree tEdge delta : ℝ} {q D r : ℕ}
    (hq : 0 < q) (htDegree : 0 < tDegree) (htEdge : 0 ≤ tEdge)
    (hmax : ∀ v, J.degree v ≤ q)
    (hdegreeMargin : ∀ v,
      (J.degree v : ℝ) / 2 + tDegree ≤ D)
    (hedgeMargin :
      (r : ℝ) * ((1 + epsilon) * (D : ℝ) / 2) + tEdge ≤
        (J.edgeFinset.card : ℝ) / 4)
    (hDegreeTail : (Fintype.card V : ℝ) * 2 *
      exp (-2 * tDegree ^ 2 / q) ≤ delta / 2)
    (hEdgeTail : 2 * exp (-2 * tEdge ^ 2 /
      (∑ v : V, (J.degree v : ℝ) ^ 2)) ≤ delta / 2) :
    ((((Finset.univ : Finset V).powerset.filter fun S ↦
        ¬ IsInducedLinearArboricityGood J S epsilon D r).card : ℝ)) ≤
      delta * (2 : ℝ) ^ Fintype.card V := by
  have hraw := not_isInducedLinearArboricityGood_count_le J hq
    htDegree htEdge hmax hdegreeMargin hedgeMargin
  have hcoef :
      (Fintype.card V : ℝ) * 2 * exp (-2 * tDegree ^ 2 / q) +
          2 * exp (-2 * tEdge ^ 2 /
            (∑ v : V, (J.degree v : ℝ) ^ 2)) ≤ delta := by
    linarith
  calc
    _ ≤ (Fintype.card V : ℝ) *
          (2 * (2 : ℝ) ^ Fintype.card V *
            exp (-2 * tDegree ^ 2 / q)) +
        2 * (2 : ℝ) ^ Fintype.card V *
          exp (-2 * tEdge ^ 2 /
            (∑ v : V, (J.degree v : ℝ) ^ 2)) := hraw
    _ = ((Fintype.card V : ℝ) * 2 *
          exp (-2 * tDegree ^ 2 / q) +
        2 * exp (-2 * tEdge ^ 2 /
          (∑ v : V, (J.degree v : ℝ) ^ 2))) *
            (2 : ℝ) ^ Fintype.card V := by ring
    _ ≤ delta * (2 : ℝ) ^ Fintype.card V :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)

/-- A finite, directly usable consequence of asymptotic linear arboricity.

If a graph of degree at most `D` has enough edges that the average color
class in an Alon decomposition has at least `r` edges, then it contains a
linear forest with at least `r` edges.  The statement keeps the inequality
over `ℝ`; this is the form produced by the sampled edge-count estimates. -/
theorem eventually_containsLinearForestWith_univ
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ D₀ : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (J : SimpleGraph V) (D r : ℕ),
      D₀ ≤ D →
      (∀ v, J.degree v ≤ D) →
      (r : ℝ) * ((1 + epsilon) * (D : ℝ) / 2) ≤
        (J.edgeSet.ncard : ℝ) →
      ContainsLinearForestWith J Finset.univ r := by
  obtain ⟨D₀, hD₀⟩ :=
    AlonInduction.alon_asymptoticLinearArboricity epsilon hepsilon
  refine ⟨D₀, ?_⟩
  intro V instF instD J D r hD hdegree hedge
  let : Fintype V := instF
  let : DecidableEq V := instD
  let : DecidableRel J.Adj := Classical.decRel J.Adj
  obtain ⟨k, hk, hkupper, hd⟩ := hD₀ V J D hD hdegree
  obtain ⟨F, hFJ, hlinear, havg⟩ :=
    hd.some.exists_large_linearForest hk
  refine ⟨F, hFJ, ⟨hlinear.1, hlinear.2⟩, by simp, ?_⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hrnonneg : (0 : ℝ) ≤ r := by positivity
  have hrk : (r : ℝ) * k ≤ (J.edgeSet.ncard : ℝ) := by
    calc
      (r : ℝ) * k ≤
          (r : ℝ) * ((1 + epsilon) * (D : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hkupper hrnonneg
      _ ≤ (J.edgeSet.ncard : ℝ) := hedge
  have hJcard : Fintype.card J.edgeSet = J.edgeSet.ncard := by
    rw [← Set.toFinset_card, Set.ncard_eq_toFinset_card']
  have hravg : (r : ℝ) ≤
      (Fintype.card J.edgeSet : ℝ) / (k : ℝ) := by
    rw [le_div_iff₀ hkR]
    simpa only [hJcard, Nat.cast_ofNat] using hrk
  have hFcard : Fintype.card F.edgeSet = F.edgeSet.ncard := by
    rw [← Set.toFinset_card, Set.ncard_eq_toFinset_card']
  have hFncard : F.edgeSet.ncard = F.edgeFinset.card := by
    rw [← F.coe_edgeFinset, Set.ncard_coe_finset]
  have hrF : (r : ℝ) ≤ (F.edgeFinset.card : ℝ) := by
    calc
      (r : ℝ) ≤ (Fintype.card J.edgeSet : ℝ) / (k : ℝ) := hravg
      _ ≤ (Fintype.card F.edgeSet : ℝ) := havg
      _ = (F.edgeFinset.card : ℝ) := by rw [hFcard, hFncard]
  exact_mod_cast hrF

/-- Sampled-graph adapter for the preceding finite Alon consequence. -/
theorem eventually_containsLinearForestWith_induce
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ D₀ : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (J : SimpleGraph V) (S : Finset V) (D r : ℕ),
      D₀ ≤ D → IsInducedLinearArboricityGood J S epsilon D r →
      ContainsLinearForestWith (J.induce (S : Set V)) Finset.univ r := by
  obtain ⟨D₀, hD₀⟩ := eventually_containsLinearForestWith_univ hepsilon
  refine ⟨D₀, ?_⟩
  intro W instF instD J S D r hD hgood
  let : Fintype W := instF
  let : DecidableEq W := instD
  exact hD₀ (S : Set W) (J.induce (S : Set W)) D r hD hgood.1 hgood.2

/-- Count form of the unconditional sampled Alon consequence, retaining the
sharp `e(J) / Δ(J)` exponent from
`not_isInducedLinearArboricityGood_count_le_of_edge_slack`.  This is the
direct probabilistic interface used for the original internal graph in the
intermediate-imbalance range. -/
theorem eventually_not_containsLinearForestWith_induce_count_le_of_edge_slack
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ D₀ : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (J : SimpleGraph V) (q D r : ℕ) (tDegree : ℝ),
      D₀ ≤ D → 0 < q → 0 < tDegree →
      0 < J.edgeFinset.card →
      (∀ v, J.degree v ≤ q) →
      (∀ v, (J.degree v : ℝ) / 2 + tDegree ≤ D) →
      (r : ℝ) * ((1 + epsilon) * (D : ℝ) / 2) ≤
        (J.edgeFinset.card : ℝ) / 8 →
      ((((Finset.univ : Finset V).powerset.filter fun S : Finset V ↦
          ¬ ContainsLinearForestWith (J.induce (S : Set V))
            Finset.univ r).card : ℝ)) ≤
        ((Fintype.card V : ℝ) * 2 *
            exp (-2 * tDegree ^ 2 / q) +
          2 * exp (-(J.edgeFinset.card : ℝ) / (64 * q))) *
            (2 : ℝ) ^ Fintype.card V := by
  obtain ⟨D₀, hAlon⟩ := eventually_containsLinearForestWith_induce hepsilon
  refine ⟨D₀, ?_⟩
  intro W instF instD J q D r tDegree hD hq htDegree hedge hmax
    hdegreeMargin hcapacity
  let : Fintype W := instF
  let : DecidableEq W := instD
  have hsub : (Finset.univ : Finset W).powerset.filter (fun S : Finset W ↦
      ¬ ContainsLinearForestWith (J.induce (S : Set W))
        Finset.univ r) ⊆
      (Finset.univ : Finset W).powerset.filter (fun S : Finset W ↦
        ¬ IsInducedLinearArboricityGood J S epsilon D r) := by
    intro S hS
    have hm := Finset.mem_filter.mp hS
    apply Finset.mem_filter.mpr
    refine ⟨hm.1, ?_⟩
    intro hgood
    exact hm.2 (hAlon W J S D r hD hgood)
  have hcard :
      ((Finset.univ : Finset W).powerset.filter (fun S : Finset W ↦
        ¬ ContainsLinearForestWith (J.induce (S : Set W))
          Finset.univ r)).card ≤
      ((Finset.univ : Finset W).powerset.filter (fun S : Finset W ↦
        ¬ IsInducedLinearArboricityGood J S epsilon D r)).card :=
    Finset.card_le_card hsub
  have hcardR :
      ((((Finset.univ : Finset W).powerset.filter fun S : Finset W ↦
        ¬ ContainsLinearForestWith (J.induce (S : Set W))
          Finset.univ r).card : ℝ)) ≤
      (((Finset.univ : Finset W).powerset.filter fun S : Finset W ↦
        ¬ IsInducedLinearArboricityGood J S epsilon D r).card : ℝ) := by
    exact_mod_cast hcard
  exact hcardR.trans
    (not_isInducedLinearArboricityGood_count_le_of_edge_slack J hq
      htDegree hedge hmax hdegreeMargin hcapacity)

/-- Combine the exact bounded-internal construction with the sampled Alon
adapter.  The result exposes both DKM edge lower bounds and, for every
sample satisfying the two numerical good events, forests supported in the
two sampled cut parts of the ambient graph. -/
theorem eventually_orientedBoundedInternal_sample_forests
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ D₀ : ℕ, ∀ {n : ℕ} (G : SimpleGraph (Fin (2 * n)))
      (A B C D : Finset (Fin (2 * n))),
      BoundedInternal.OrientedBoundedInternal G A B C D →
      ∃ JA JB : SimpleGraph (Fin (2 * n)),
        (∀ v, JA.degree v ≤ D.card + 1) ∧
        (∀ v, JB.degree v ≤ C.card + 1) ∧
        2 * n ≤ JA.edgeFinset.card + C.card * D.card +
          C.card + 2 * D.card ∧
        n ≤ JB.edgeFinset.card + D.card ∧
        ∀ (S : Finset (Fin (2 * n))) (DA DB rA rB : ℕ),
          D₀ ≤ DA → D₀ ≤ DB →
          IsInducedLinearArboricityGood JA S epsilon DA rA →
          IsInducedLinearArboricityGood JB S epsilon DB rB →
          ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
              (restrictedPart S A) rA ∧
            ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
              (restrictedPart S B) rB := by
  obtain ⟨D₀, hAlon⟩ := eventually_containsLinearForestWith_induce hepsilon
  refine ⟨D₀, ?_⟩
  intro n G A B C D horiented
  rcases horiented with
    ⟨JA, JB, hJAG, hJBG, hJAsupp, hJBsupp, _hJAbip, _hJBbip,
      hJAdeg, hJBdeg, hJAedge, hJBedge⟩
  refine ⟨JA, JB, hJAdeg, hJBdeg, hJAedge, hJBedge, ?_⟩
  intro S DA DB rA rB hDA hDB hgoodA hgoodB
  have hJAint : JA ≤ internalGraph G A := by
    intro u v huv
    apply (internalGraph_adj G A u v).mpr
    exact ⟨hJAsupp ⟨v, huv⟩,
      hJAsupp ⟨u, huv.symm⟩, hJAG huv⟩
  have hJBint : JB ≤ internalGraph G B := by
    intro u v huv
    apply (internalGraph_adj G B u v).mpr
    exact ⟨hJBsupp ⟨v, huv⟩,
      hJBsupp ⟨u, huv.symm⟩, hJBG huv⟩
  have hforestA := hAlon (Fin (2 * n)) JA S DA rA hDA hgoodA
  have hforestB := hAlon (Fin (2 * n)) JB S DB rB hDB hgoodB
  exact ⟨
    Erdos622.TwoLargeForest.ContainsLinearForestWith.mono_induce_internalGraph
      hJAint hforestA,
    Erdos622.TwoLargeForest.ContainsLinearForestWith.mono_induce_internalGraph
      hJBint hforestB⟩

/-- A fixed multiplicative shrink of both one-parameter DKM capacities
still leaves strictly more than half of the Gaussian mass, uniformly when
the normalized first cover size ranges over a compact positive interval.

The common shrink parameter is what absorbs the random-cover error, the
linear-arboricity error, integer rounding, and the vertices moved by the
balancing transfer. -/
theorem exists_uniform_shrunken_normal_window {η M : ℝ}
    (hη : 0 < η) (hηM : η ≤ M) :
    ∃ τ margin : ℝ, 0 < τ ∧ 0 < margin ∧ τ < 1 / 8 ∧
      ∀ α ∈ Set.Icc η M,
        (1 / 2 : ℝ) + margin <
          gaussianWindow
            ((1 / 4 - 2 * τ) * α * Real.sqrt 2)
            ((1 - 2 * τ) / α * Real.sqrt 2) := by
  obtain ⟨m, hm, hbase⟩ := normalWindow_uniform_margin hη hηM
  let f : ℝ × ℝ → ℝ := fun p ↦
    gaussianWindow
      ((1 / 4 - 2 * p.2) * p.1 * Real.sqrt 2)
      ((1 - 2 * p.2) / p.1 * Real.sqrt 2)
  have hf : ContinuousOn f
      (Set.Icc η M ×ˢ Set.Icc (0 : ℝ) (1 / 4)) := by
    intro p hp
    have hpne : p.1 ≠ 0 := (hη.trans_le hp.1.1).ne'
    have hh : Continuous gaussianHalfInterval :=
      intervalIntegral.continuous_primitive
        gaussianKernel_intervalIntegrable 0
    dsimp [f, gaussianWindow]
    fun_prop
  have hcompact : IsCompact
      (Set.Icc η M ×ˢ Set.Icc (0 : ℝ) (1 / 4)) :=
    isCompact_Icc.prod isCompact_Icc
  have huc := hcompact.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hclose⟩ := huc (m / 2) (by linarith)
  let τ : ℝ := min (δ / 2) (1 / 16)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτeighth : τ < 1 / 8 := by
    dsimp [τ]
    have h := min_le_right (δ / 2) (1 / 16)
    norm_num at h ⊢
  refine ⟨τ, m / 2, hτ, by linarith, hτeighth, ?_⟩
  intro α hα
  have hτle : τ ≤ δ / 2 := min_le_left _ _
  have hτltδ : τ < δ := by linarith
  have hp0 : (α, (0 : ℝ)) ∈
      Set.Icc η M ×ˢ Set.Icc (0 : ℝ) (1 / 4) :=
    ⟨hα, by norm_num⟩
  have hpτ : (α, τ) ∈
      Set.Icc η M ×ˢ Set.Icc (0 : ℝ) (1 / 4) :=
    ⟨hα, ⟨hτ.le, by linarith⟩⟩
  have hdist : dist (α, τ) (α, (0 : ℝ)) < δ := by
    rw [Prod.dist_eq]
    simp only [dist_self, Real.dist_eq, sub_zero, abs_of_pos hτ,
      max_lt_iff]
    exact ⟨hδ, hτltδ⟩
  have hfc := hclose (α, τ) hpτ (α, 0) hp0 hdist
  have hf0 : f (α, 0) = normalWindow α := by
    dsimp [f, normalWindow]
    apply congrArg₂ gaussianWindow <;> ring
  have hbaseα := hbase α hα
  rw [hf0] at hfc
  rw [Real.dist_eq] at hfc
  have h := (abs_lt.mp hfc).1
  dsimp [f] at h ⊢
  linarith

/-- Compact-uniform de Moivre--Laplace estimate after a common fixed shrink
of the matching and linear-arboricity capacities. -/
theorem eventually_uniform_shrunken_normal_window {η M : ℝ}
    (hη : 0 < η) (hηM : η ≤ M) :
    ∃ τ margin : ℝ, 0 < τ ∧ 0 < margin ∧ τ < 1 / 8 ∧
      ∀ᶠ N : ℕ in atTop, ∀ α ∈ Set.Icc η M,
        (1 / 2 : ℝ) + margin / 2 <
          (BinomialCLT.fairBinomialWindowCount N
            (-((1 / 4 - 2 * τ) * α * Real.sqrt 2))
            ((1 - 2 * τ) / α * Real.sqrt 2) : ℝ) /
              (2 : ℝ) ^ N := by
  obtain ⟨τ, margin, hτ, hmargin, hτsmall, hgauss⟩ :=
    exists_uniform_shrunken_normal_window hη hηM
  refine ⟨τ, margin, hτ, hmargin, hτsmall, ?_⟩
  let a : ℝ → ℝ := fun α ↦
    -((1 / 4 - 2 * τ) * α * Real.sqrt 2)
  let b : ℝ → ℝ := fun α ↦
    (1 - 2 * τ) / α * Real.sqrt 2
  have ha : ContinuousOn a (Set.Icc η M) := by
    apply Continuous.continuousOn
    dsimp [a]
    fun_prop
  have hb : ContinuousOn b (Set.Icc η M) := by
    intro α hα
    have hαne : α ≠ 0 := (hη.trans_le hα.1).ne'
    dsimp [b]
    fun_prop
  have hinner : ∀ α ∈ Set.Icc η M, ∃ z : ℝ × ℝ,
      a α < z.1 ∧ z.2 < b α ∧ z.1 ≤ z.2 ∧
        (1 / 2 : ℝ) + margin / 2 <
          BinomialCLT.gaussianWindowMass z.1 z.2 := by
    intro α hα
    have hαpos : 0 < α := hη.trans_le hα.1
    have hcoef1 : 0 < 1 / 4 - 2 * τ := by linarith
    have hcoef2 : 0 < 1 - 2 * τ := by linarith
    have hu : 0 < (1 / 4 - 2 * τ) * α * Real.sqrt 2 := by
      positivity
    have hv : 0 < (1 - 2 * τ) / α * Real.sqrt 2 := by
      positivity
    apply exists_strict_inner_gaussian_window hu hv
    have hg := hgauss α hα
    linarith
  simpa only [a, b] using
    (eventually_uniform_compact_windows isCompact_Icc a b
      ((1 / 2 : ℝ) + margin / 2) ha hb hinner)

/-- The preceding compact estimate transported to every balanced cut of the
ambient `2n`-vertex type.  This is the exact cardinality window consumed by
the two-large-cover deterministic forest argument. -/
theorem eventually_uniform_balancedCut_shrunken_normal_difference_count
    {η M : ℝ} (hη : 0 < η) (hηM : η ≤ M) :
    ∃ τ margin : ℝ, 0 < τ ∧ 0 < margin ∧ τ < 1 / 8 ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ A B : Finset (Fin (2 * n)), IsCut A B →
          A.card = n → B.card = n →
          ∀ α ∈ Set.Icc η M,
            (1 / 2 : ℝ) + margin / 2 <
              (almostBipartiteCount
                (Finset.univ : Finset (Fin (2 * n)))
                (fun S ↦ BinomialCLT.standardizedBinomialPoint (2 * n)
                  ((S ∩ A).card + (n - (S ∩ B).card)) ∈
                    Set.Icc
                      (-((1 / 4 - 2 * τ) * α * Real.sqrt 2))
                      ((1 - 2 * τ) / α * Real.sqrt 2)) : ℝ) /
                (2 : ℝ) ^ (2 * n) := by
  obtain ⟨τ, margin, hτ, hmargin, hτsmall, huniform⟩ :=
    eventually_uniform_shrunken_normal_window hη hηM
  refine ⟨τ, margin, hτ, hmargin, hτsmall, ?_⟩
  rw [eventually_atTop] at huniform ⊢
  obtain ⟨N, hN⟩ := huniform
  refine ⟨N, ?_⟩
  intro n hn A B hcut hA hB α hα
  rw [almostBipartiteCount_balancedWindow_eq hcut hA hB]
  apply hN (2 * n) (by omega) α hα

/-- Undo the standardization in the shrunken normal window.  Its two
endpoints are precisely the real capacities `(1-2τ)n/c` and
`(1/4-2τ)c` for the two possible signs of the balanced cardinality
difference. -/
lemma shrunken_normal_window_bounds
    {n c x y : ℕ} {τ : ℝ}
    (hn : 0 < n) (hc : 0 < c) (hy : y ≤ n)
    (hwindow : BinomialCLT.standardizedBinomialPoint (2 * n)
        (x + (n - y)) ∈
      Set.Icc (-((1 / 4 - 2 * τ) *
          ((c : ℝ) / Real.sqrt n) * Real.sqrt 2))
        ((1 - 2 * τ) / ((c : ℝ) / Real.sqrt n) * Real.sqrt 2)) :
    ((x : ℝ) - y ≤ (1 - 2 * τ) * (n : ℝ) / c) ∧
      ((y : ℝ) - x ≤ (1 / 4 - 2 * τ) * c) := by
  have hsqrtn : 0 < Real.sqrt n :=
    Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2pow : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hsqrtnpow : (Real.sqrt n) ^ 2 = n :=
    Real.sq_sqrt (by positivity)
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hnum :
      (2 * (x + (n - y)) : ℝ) - (2 * n : ℝ) =
        2 * ((x : ℝ) - y) := by
    push_cast [Nat.cast_sub hy]
    ring
  constructor
  · have hu := hwindow.2
    unfold BinomialCLT.standardizedBinomialPoint at hu
    norm_num at hu
    rw [Nat.cast_sub hy,
      div_le_iff₀ (mul_pos hsqrt2 hsqrtn), hnum] at hu
    field_simp at hu ⊢
    rw [hsqrtnpow, hsqrt2pow] at hu
    nlinarith
  · have hl := hwindow.1
    unfold BinomialCLT.standardizedBinomialPoint at hl
    norm_num at hl
    rw [Nat.cast_sub hy,
      le_div_iff₀ (mul_pos hsqrt2 hsqrtn), hnum] at hl
    field_simp at hl
    rw [hsqrt2pow] at hl
    nlinarith

/-- A linear union-bound factor is still negligible against exponential
decay on the square-root scale. -/
theorem tendsto_linear_mul_exp_neg_sqrt (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * exp (-c * Real.sqrt n))
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun n : ℕ ↦ c * Real.sqrt (n : ℝ))
      atTop atTop := hsqrt.const_mul_atTop hc
  have h :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hscale
  have hcne : c ≠ 0 := hc.ne'
  convert h.const_mul (1 / c ^ 2) using 1
  · ext n
    simp only [Function.comp_apply]
    rw [show (c * Real.sqrt (n : ℝ)) ^ 2 =
        c ^ 2 * (Real.sqrt (n : ℝ)) ^ 2 by ring,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)]
    field_simp
  · simp

/-- Pure exponential decay on the square-root scale. -/
theorem tendsto_exp_neg_sqrt (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ exp (-c * Real.sqrt n))
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscale : Tendsto (fun n : ℕ ↦ c * Real.sqrt (n : ℝ))
      atTop atTop := hsqrt.const_mul_atTop hc
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale using 1
  ext n
  simp

/-- A graph-independent majorant for the two concentration failures in the
compact cover range.  The first term pays the union bound over all `2n`
vertices; the second uses the bipartite variance bound. -/
noncomputable def compactLAFailureMajorant
    (η M τ gamma : ℝ) (n : ℕ) : ℝ :=
  4 * (n : ℝ) * exp (-(τ ^ 2 * η / 2) * Real.sqrt n) +
    2 * exp (-(gamma ^ 2 / (M * (M + 1) ^ 2)) * Real.sqrt n)

/-- The compact-range linear-arboricity exceptional proportion tends to
zero for every fixed choice of positive parameters. -/
theorem compactLAFailureMajorant_tendsto_zero
    {η M τ gamma : ℝ}
    (hη : 0 < η) (hM : 0 < M) (hτ : 0 < τ)
    (hgamma : 0 < gamma) :
    Tendsto (compactLAFailureMajorant η M τ gamma)
      atTop (nhds 0) := by
  have hcDegree : 0 < τ ^ 2 * η / 2 := by positivity
  have hcEdge : 0 < gamma ^ 2 / (M * (M + 1) ^ 2) := by
    positivity
  have hdegree := tendsto_linear_mul_exp_neg_sqrt
    (τ ^ 2 * η / 2) hcDegree
  have hedge := tendsto_exp_neg_sqrt
    (gamma ^ 2 / (M * (M + 1) ^ 2)) hcEdge
  unfold compactLAFailureMajorant
  convert (hdegree.const_mul 4).add (hedge.const_mul 2) using 1
  · ext n
    ring
  · norm_num

/-- Exact sampled cardinality identity on the side that loses the balancing
set. -/
lemma card_inter_left_balancing
    {A A₀ T S : Finset V} (hTA : T ⊆ A) (hA₀ : A₀ = A \ T) :
    (S ∩ A).card = (S ∩ A₀).card + (S ∩ T).card := by
  have hdisj : Disjoint (S ∩ A₀) (S ∩ T) := by
    rw [Finset.disjoint_left]
    intro v hv0 hvT
    have hvA₀ := (Finset.mem_inter.mp hv0).2
    rw [hA₀] at hvA₀
    exact (Finset.mem_sdiff.mp hvA₀).2 (Finset.mem_inter.mp hvT).2
  have hunion : (S ∩ A₀) ∪ (S ∩ T) = S ∩ A := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter]
    rw [hA₀]
    simp only [Finset.mem_sdiff]
    constructor
    · rintro (⟨hvS, hvA, _hvT⟩ | ⟨hvS, hvT⟩)
      · exact ⟨hvS, hvA⟩
      · exact ⟨hvS, hTA hvT⟩
    · rintro ⟨hvS, hvA⟩
      by_cases hvT : v ∈ T
      · exact Or.inr ⟨hvS, hvT⟩
      · exact Or.inl ⟨hvS, hvA, hvT⟩
  rw [← hunion, Finset.card_union_of_disjoint hdisj]

/-- Exact sampled cardinality identity on the side enlarged by the
balancing set. -/
lemma card_inter_right_balancing
    {A B B₀ T S : Finset V} (hcut : IsCut A B) (hTA : T ⊆ A)
    (hB₀ : B₀ = B ∪ T) :
    (S ∩ B₀).card = (S ∩ B).card + (S ∩ T).card := by
  have hBT : Disjoint B T := by
    rw [Finset.disjoint_left]
    intro v hvB hvT
    exact Finset.disjoint_left.mp hcut.1 (hTA hvT) hvB
  have hdisj : Disjoint (S ∩ B) (S ∩ T) := by
    exact Finset.disjoint_of_subset_right Finset.inter_subset_right
      (Finset.disjoint_of_subset_left Finset.inter_subset_right hBT)
  have hunion : (S ∩ B) ∪ (S ∩ T) = S ∩ B₀ := by
    rw [hB₀, Finset.inter_union_distrib_left]
  rw [← hunion, Finset.card_union_of_disjoint hdisj]

/-- Deterministic original-cut transfer.  The left window explicitly pays
`2|S∩T|`; on the right, the same quantity cancels exactly against the edge
loss incurred by deleting all moved-vertex incidences from the forest. -/
theorem IsKGoodSample.of_balanced_transfer_matching_forest
    {G : SimpleGraph V} {A B T A₀ B₀ S : Finset V}
    {left right : ℕ}
    (hcut : IsCut A B) (hTA : T ⊆ A)
    (hA₀ : A₀ = A \ T) (hB₀ : B₀ = B ∪ T)
    (hmatching : RandomCover.HasMatchingAtLeast
      (internalGraph G A₀) S (left : ℝ))
    (hforest : ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S B₀) right)
    (hleftWindow : (S ∩ A₀).card + 2 * (S ∩ T).card ≤
      (S ∩ B₀).card + left)
    (hrightWindow : (S ∩ B₀).card ≤ (S ∩ A₀).card + right) :
    IsKGoodSample G A B S 0 := by
  have hleft₀ : ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S A₀) left := hmatching.induce_internalGraph
  have hleft : ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S A) left := by
    simpa only [restrictedPart, ForestTransfer.sampledPart] using
      ForestTransfer.ContainsLinearForestWith.transfer_sampled_left
        hA₀ hleft₀
  have hright : ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S B) (right - 2 * (S ∩ T).card) := by
    simpa only [restrictedPart, ForestTransfer.sampledPart] using
      ForestTransfer.ContainsLinearForestWith.transfer_sampled_balancing_right
        hTA hA₀ hB₀ hforest
  have hcardA := card_inter_left_balancing (S := S) hTA hA₀
  have hcardB := card_inter_right_balancing (S := S) hcut hTA hB₀
  apply IsKGoodSample.of_two_linearForests hcut
    (by simpa using hleft) (by simpa using hright)
  · rw [card_restrictedPart, card_restrictedPart]
    omega
  · rw [card_restrictedPart, card_restrictedPart]
    omega

/-- Union-window version of the balancing transfer.  A forest supported on
the original left side and one transferred from the balanced left side may
be combined by taking their maximum capacity.  On the right, the window is
allowed to stop at the balancing point `2|S ∩ T|`; if the original right
side is actually larger, this forces the other branch of the maximum and
the loss from deleting moved-vertex incidences cancels exactly.

This is the deterministic form of the intermediate-imbalance repair: it
uses a union of the two left mechanisms, not their intersection. -/
theorem IsKGoodSample.of_balanced_transfer_three_forests
    {G : SimpleGraph V} {A B T A₀ B₀ S : Finset V}
    {leftBalanced leftOriginal right : ℕ}
    (hcut : IsCut A B) (hTA : T ⊆ A)
    (hA₀ : A₀ = A \ T) (hB₀ : B₀ = B ∪ T)
    (hleftBalanced : ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S A₀) leftBalanced)
    (hleftOriginal : ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S A) leftOriginal)
    (hright : ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S B₀) right)
    (hleftWindow : (S ∩ A₀).card + 2 * (S ∩ T).card ≤
      (S ∩ B₀).card + max leftBalanced leftOriginal)
    (hrightWindow : (S ∩ B₀).card ≤
      (S ∩ A₀).card + max (2 * (S ∩ T).card) right) :
    IsKGoodSample G A B S 0 := by
  have hleftBalanced' : ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S A) leftBalanced := by
    simpa only [restrictedPart, ForestTransfer.sampledPart] using
      ForestTransfer.ContainsLinearForestWith.transfer_sampled_left
        hA₀ hleftBalanced
  have hleft : ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S A) (max leftBalanced leftOriginal) := by
    rcases le_total leftBalanced leftOriginal with hle | hle
    · simpa [max_eq_right hle] using hleftOriginal
    · simpa [max_eq_left hle] using hleftBalanced'
  have hright' : ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S B) (right - 2 * (S ∩ T).card) := by
    simpa only [restrictedPart, ForestTransfer.sampledPart] using
      ForestTransfer.ContainsLinearForestWith.transfer_sampled_balancing_right
        hTA hA₀ hB₀ hright
  have hcardA := card_inter_left_balancing (S := S) hTA hA₀
  have hcardB := card_inter_right_balancing (S := S) hcut hTA hB₀
  refine ⟨restrictedParts_isCut hcut, ?_⟩
  by_cases hBA : (restrictedPart S B).card ≤
      (restrictedPart S A).card
  · left
    refine ⟨hBA, hleft.mono_requirement ?_⟩
    rw [card_restrictedPart, card_restrictedPart]
    omega
  · right
    have hAB : (restrictedPart S A).card ≤
        (restrictedPart S B).card := Nat.le_of_not_ge hBA
    refine ⟨hAB, hright'.mono_requirement ?_⟩
    rw [card_restrictedPart, card_restrictedPart] at hBA ⊢
    omega

end TwoLargeForest

end Erdos622
