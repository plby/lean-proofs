/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, ChatGPT
-/

import ErdosProblems.Erdos543.Model
import ErdosProblems.Erdos543.Asymptotics
import ErdosProblems.Erdos543.PrimeSequence
import ErdosProblems.Erdos543.StratifiedMoment
import ErdosProblems.Erdos543.MissedEvents
import ErdosProblems.Erdos543.BonferroniAnalytic
import ErdosProblems.Erdos543.IIDTransfer
import ErdosProblems.Erdos543.RankCountAsymptotics
import ErdosProblems.Erdos543.PoissonAsymptotics
import ErdosProblems.Erdos543.FactorialTail
import ErdosProblems.Erdos543.PoissonSecondMoment
import ErdosProblems.Erdos543.HalfTransfer
import ErdosProblems.Erdos543.FinalLogic

/-!
# The prime-cyclic obstruction for Erdős Problem 543

This file assembles the finite rank-stratified moment calculation, the
quantitative Bonferroni estimate, and the second-moment argument.  Its public
theorem says that every proposed `o(log log N)` error term fails eventually
on the canonical cofinal sequence of prime cyclic groups.
-/

open scoped BigOperators Topology
open Filter Finset

namespace Erdos543.CoreObstruction

attribute [local instance] Classical.propDecidable

noncomputable section

open FiniteProbability

/-! ## Missed targets in the independent model -/

/-- The unordered range of an ordered independent sample. -/
def tupleRange {p k : ℕ} (a : Fin k → ZMod p) : Finset (ZMod p) :=
  Finset.univ.image a

/-- The finite type of nonzero target residues. -/
abbrev NonzeroTarget (p : ℕ) := {x : ZMod p // x ≠ 0}

/-- A target constrained to a finite target set. -/
abbrev TargetIn {p : ℕ} [Fact p.Prime] (B : Finset (ZMod p)) :=
  Erdos543.TargetIn B

/-- A nonempty coordinate subset paired with a target. -/
abbrev TargetSubsetEvent {p : ℕ} [Fact p.Prime]
    (k : ℕ) (B : Finset (ZMod p)) :=
  Erdos543.TargetSubsetEvent k B

/-- Occurrence of a subset-target equation. -/
abbrev targetSubsetEventOccurs {p k : ℕ} [Fact p.Prime] (B : Finset (ZMod p))
    (e : TargetSubsetEvent k B) (a : Fin k → ZMod p) : Prop :=
  Erdos543.targetSubsetEventOccurs B e a

/-- Number of subset-target equations occurring at a sample. -/
abbrev targetSubsetEventCount {p k : ℕ} [Fact p.Prime] (B : Finset (ZMod p))
    (a : Fin k → ZMod p) : ℕ :=
  Erdos543.targetSubsetEventCount B a

/-- The event that no nonempty indexed subset has sum `x`. -/
def missEvent {p k : ℕ} [Fact p.Prime] (x : NonzeroTarget p) :
    Set (Fin k → ZMod p) :=
  {a | targetSubsetEventCount ({(x : ZMod p)} : Finset (ZMod p)) a = 0}

/-- A target-set incidence count vanishes exactly when none of its events
occurs. -/
lemma targetSubsetEventCount_eq_zero_iff {p k : ℕ} [Fact p.Prime]
    (B : Finset (ZMod p)) (a : Fin k → ZMod p) :
    targetSubsetEventCount B a = 0 ↔
      ∀ (S : NonemptyIndexSet k) (b : ZMod p), b ∈ B →
        ∑ i ∈ (S : Finset (Fin k)), a i ≠ b := by
  classical
  change eventCount (Erdos543.targetSubsetEventOccurs B) a = 0 ↔ _
  rw [eventCount, Finset.card_eq_zero]
  constructor
  · intro hempty S b hb heq
    have hmem : (S, ⟨b, hb⟩) ∈
        (Finset.univ.filter fun e : TargetSubsetEvent k B ↦
          targetSubsetEventOccurs B e a) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact heq
    rw [hempty] at hmem
    simp at hmem
  · intro h
    rw [Finset.filter_eq_empty_iff]
    rintro ⟨S, b⟩ _ hmem
    exact h S b b.property hmem

lemma mem_missEvent_iff {p k : ℕ} [Fact p.Prime]
    (x : NonzeroTarget p) (a : Fin k → ZMod p) :
    a ∈ missEvent x ↔
      ∀ S : NonemptyIndexSet k,
        ∑ i ∈ (S : Finset (Fin k)), a i ≠ (x : ZMod p) := by
  change targetSubsetEventCount ({(x : ZMod p)} : Finset (ZMod p)) a = 0 ↔ _
  rw [targetSubsetEventCount_eq_zero_iff]
  simp

/-- The incidence definition of a missed target is the usual vanishing
indexed representation count. -/
lemma mem_missEvent_iff_hitCount_eq_zero {p k : ℕ} [Fact p.Prime]
    (x : NonzeroTarget p) (a : Fin k → ZMod p) :
    a ∈ missEvent x ↔ IIDModel.hitCount a (x : ZMod p) = 0 := by
  rw [mem_missEvent_iff, IIDModel.hitCount_eq_zero_iff]
  rfl

/-- Vanishing of our subtype-indexed missed count is exactly indexed
completeness in `IIDModel`. -/
lemma missedCount_eq_zero_iff_indexedComplete {p k : ℕ} [Fact p.Prime]
    (a : Fin k → ZMod p) :
    MissedEvents.missedCount (missEvent (p := p) (k := k)) a = 0 ↔
      IIDModel.IndexedComplete a := by
  rw [MissedEvents.missedCount, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  constructor
  · intro h x
    have h' : ∀ y : NonzeroTarget p, a ∉ missEvent y := by
      simpa using h
    by_cases hx : x = 0
    · exact ⟨∅, by simp [hx, IIDModel.indexedSum]⟩
    · have hnot : a ∉ missEvent (⟨x, hx⟩ : NonzeroTarget p) := by
        exact h' ⟨x, hx⟩
      rw [mem_missEvent_iff_hitCount_eq_zero] at hnot
      obtain ⟨S, hS⟩ :=
        (IIDModel.hitCount_ne_zero_iff a x).mp hnot
      exact ⟨S, hS⟩
  · intro h x hx hmem
    rw [mem_missEvent_iff_hitCount_eq_zero] at hmem
    obtain ⟨S, hS⟩ := h x
    have hSne : S.Nonempty := by
      by_contra hEmpty
      rw [Finset.not_nonempty_iff_eq_empty] at hEmpty
      subst S
      simp [IIDModel.indexedSum] at hS
      exact x.property hS.symm
    exact ((IIDModel.hitCount_ne_zero_iff a (x : ZMod p)).mpr
      ⟨⟨S, hSne⟩, hS⟩) hmem

/-- Therefore the zero-miss event used below is literally the indexed
completeness event consumed by the transfer theorem. -/
lemma zeroMissEvent_eq_indexedCompleteEvent {p k : ℕ} [Fact p.Prime] :
    {a | MissedEvents.missedCount
      (missEvent (p := p) (k := k)) a = 0} =
      IIDModel.indexedCompleteEvent (ZMod p) k := by
  ext a
  exact missedCount_eq_zero_iff_indexedComplete a

/-- Missing two distinct targets is the same event as having no incidence
with their two-element target set. -/
lemma missEvent_inter_eq_pairZero {p k : ℕ} [Fact p.Prime]
    (x y : NonzeroTarget p) :
    missEvent (k := k) x ∩ missEvent y =
      {a | targetSubsetEventCount
        ({(x : ZMod p), (y : ZMod p)} : Finset (ZMod p)) a = 0} := by
  ext a
  change (a ∈ missEvent x ∧ a ∈ missEvent y) ↔
    targetSubsetEventCount
      ({(x : ZMod p), (y : ZMod p)} : Finset (ZMod p)) a = 0
  rw [targetSubsetEventCount_eq_zero_iff]
  constructor
  · rintro ⟨hx, hy⟩ S b hb
    rw [mem_missEvent_iff] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact hx S
    · exact hy S
  · intro h
    rw [mem_missEvent_iff, mem_missEvent_iff]
    exact ⟨fun S ↦ h S x (by simp), fun S ↦ h S y (by simp)⟩

/-- Dividing by a positive benchmark and subtracting one is precisely a
relative-error normalization. -/
lemma abs_sub_le_mul_of_abs_div_sub_one_le {a q delta : ℝ} (hq : 0 < q)
    (h : |a / q - 1| ≤ delta) :
    |a - q| ≤ delta * q := by
  have hform : |a / q - 1| = |a - q| / q := by
    rw [div_sub_one hq.ne', abs_div, abs_of_pos hq]
  rw [hform] at h
  exact (div_le_iff₀ hq).mp h

lemma card_nonzeroTarget {p : ℕ} [Fact p.Prime] :
    Fintype.card (NonzeroTarget p) = p - 1 := by
  classical
  rw [Fintype.card_subtype]
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ZMod.card]

instance nonemptyNonzeroTarget (p : ℕ) [Fact p.Prime] :
    Nonempty (NonzeroTarget p) := by
  letI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact ⟨⟨1, one_ne_zero⟩⟩

/-- A finite subset of the range of a tuple can be lifted to a set of
indices without changing its sum.  The lift chooses one index above each
range element, so it is injective even when the tuple itself has collisions. -/
lemma exists_indexSet_sum_eq_of_subset_range {p k : ℕ}
    (a : Fin k → ZMod p) (T : Finset (ZMod p))
    (hT : T ⊆ tupleRange a) :
    ∃ S : Finset (Fin k), ∑ i ∈ S, a i = ∑ x ∈ T, x := by
  classical
  have hex : ∀ x : {x // x ∈ T}, ∃ i : Fin k, a i = x := by
    intro x
    have hx : (x : ZMod p) ∈ Finset.univ.image a := hT x.property
    simpa only [Finset.mem_image, Finset.mem_univ, true_and] using hx
  choose s hs using hex
  have hinj : Function.Injective s := by
    intro x y hxy
    apply Subtype.ext
    calc
      (x : ZMod p) = a (s x) := (hs x).symm
      _ = a (s y) := by rw [hxy]
      _ = (y : ZMod p) := hs y
  let e : {x // x ∈ T} ↪ Fin k := ⟨s, hinj⟩
  refine ⟨Finset.univ.map e, ?_⟩
  rw [Finset.sum_map]
  calc
    ∑ x : {x // x ∈ T}, a (e x) = ∑ x : {x // x ∈ T}, (x : ZMod p) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hs x
    _ = ∑ x ∈ T, x := by
      exact (Finset.sum_subtype T (by simp) (fun x ↦ x)).symm

/-- Completeness of the unordered range forces every nonzero target to have
a nonempty indexed representation. -/
lemma not_mem_missEvent_of_range_complete {p k : ℕ} [Fact p.Prime]
    (a : Fin k → ZMod p) (hcomplete : Model.SubsetSumComplete (tupleRange a))
    (x : NonzeroTarget p) : a ∉ missEvent x := by
  rw [mem_missEvent_iff]
  push_neg
  obtain ⟨T, hTa, hsum⟩ := hcomplete x
  obtain ⟨S, hSsum⟩ := exists_indexSet_sum_eq_of_subset_range a T hTa
  have hSne : S.Nonempty := by
    by_contra hEmpty
    rw [Finset.not_nonempty_iff_eq_empty] at hEmpty
    subst S
    simp only [Finset.sum_empty] at hSsum
    exact x.property (hSsum.trans hsum).symm
  exact ⟨⟨S, hSne⟩, hSsum.trans hsum⟩

/-- Hence a complete range has no missed nonzero target. -/
lemma missedCount_eq_zero_of_range_complete {p k : ℕ} [Fact p.Prime]
    (a : Fin k → ZMod p) (hcomplete : Model.SubsetSumComplete (tupleRange a)) :
    MissedEvents.missedCount (missEvent (p := p) (k := k)) a = 0 := by
  classical
  rw [MissedEvents.missedCount, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro x hx hmem
  exact not_mem_missEvent_of_range_complete a hcomplete x hmem

/-! ## Transfer back to uniform subsets -/

/-- The event that the unordered range of the independent tuple is complete. -/
def iidCompleteEvent {p k : ℕ} [Fact p.Prime] : Set (Fin k → ZMod p) :=
  {a | Model.SubsetSumComplete (tupleRange a)}

lemma prob_iidCompleteEvent_eq {p k : ℕ} [Fact p.Prime] :
    prob (iidCompleteEvent (p := p) (k := k)) =
      (IIDTransfer.iidGoodCount (α := ZMod p) Model.SubsetSumComplete k : ℝ) /
        (p ^ k : ℕ) := by
  classical
  rw [prob]
  have hnum :
      ((Finset.univ : Finset (Fin k → ZMod p)).filter
          (fun a ↦ a ∈ iidCompleteEvent (p := p) (k := k))).card =
        IIDTransfer.iidGoodCount (α := ZMod p) Model.SubsetSumComplete k := by
    rw [IIDTransfer.iidGoodCount]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq]
    change Model.SubsetSumComplete (tupleRange a) ↔
      Model.SubsetSumComplete (IIDTransfer.tupleRange a)
    rw [show tupleRange a = IIDTransfer.tupleRange a by
      ext x
      simp [tupleRange, IIDTransfer.tupleRange]]
  rw [hnum]
  simp [ZMod.card]

lemma prob_iidCompleteEvent_le_prob_noMiss {p k : ℕ} [Fact p.Prime] :
    prob (iidCompleteEvent (p := p) (k := k)) ≤
      prob {a | MissedEvents.missedCount
        (missEvent (p := p) (k := k)) a = 0} := by
  apply prob_mono
  intro a ha
  exact missedCount_eq_zero_of_range_complete a ha

/-- A sub-quarter bound for the no-missed-target event, together with a
sub-quarter collision bound, is more than enough to transfer failure to the
uniform subset model. -/
theorem not_halfComplete_of_prob_noMiss_lt_quarter
    {p k : ℕ} [Fact p.Prime]
    (hmiss : prob {a | MissedEvents.missedCount
        (missEvent (p := p) (k := k)) a = 0} < 1 / 4)
    (hcollision :
      ((IIDTransfer.collisionTuples (ZMod p) k).card : ℝ) /
          (p ^ k : ℕ) < 1 / 4) :
    ¬ Model.HalfComplete (ZMod p) k := by
  apply IIDTransfer.not_halfComplete_of_iidCompleteCount_add_collision_lt
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpkNat : 0 < p ^ k := pow_pos hp _
  have hpk : (0 : ℝ) < (p ^ k : ℕ) := by exact_mod_cast hpkNat
  have hgoodProb :
      (IIDTransfer.iidGoodCount (α := ZMod p) Model.SubsetSumComplete k : ℝ) /
          (p ^ k : ℕ) < 1 / 4 := by
    rw [← prob_iidCompleteEvent_eq]
    exact lt_of_le_of_lt prob_iidCompleteEvent_le_prob_noMiss hmiss
  have hgood :
      (IIDTransfer.iidGoodCount (α := ZMod p) Model.SubsetSumComplete k : ℝ) <
        (p ^ k : ℕ) / 4 := by
    rw [div_lt_iff₀ hpk] at hgoodProb
    nlinarith
  have hcoll : ((IIDTransfer.collisionTuples (ZMod p) k).card : ℝ) <
      (p ^ k : ℕ) / 4 := by
    rw [div_lt_iff₀ hpk] at hcollision
    nlinarith
  have hreal :
      (2 : ℝ) * IIDTransfer.iidGoodCount (α := ZMod p) Model.SubsetSumComplete k +
        (IIDTransfer.collisionTuples (ZMod p) k).card < (p ^ k : ℕ) := by
    nlinarith
  simpa [ZMod.card] using (show
    2 * IIDTransfer.iidGoodCount (α := ZMod p) Model.SubsetSumComplete k +
      (IIDTransfer.collisionTuples (ZMod p) k).card < p ^ k by
        exact_mod_cast hreal)

/-! ## The deterministic small-cube branch -/

lemma not_subsetSumComplete_of_two_pow_card_lt
    {G : Type*} [AddCommGroup G] [Fintype G] (A : Finset G)
    (hsmall : 2 ^ A.card < Fintype.card G) :
    ¬ Model.SubsetSumComplete A := by
  classical
  intro hcomplete
  have huniv : Model.subsetSums A = (Finset.univ : Finset G) :=
    (Model.subsetSumComplete_iff_subsetSums_eq_univ A).mp hcomplete
  have hcard : Fintype.card G ≤ 2 ^ A.card := by
    calc
      Fintype.card G = (Model.subsetSums A).card := by
        rw [huniv, Finset.card_univ]
      _ ≤ A.powerset.card := by
        exact Finset.card_image_le
      _ = 2 ^ A.card := Finset.card_powerset A
  omega

theorem not_halfComplete_of_two_pow_lt_card
    (G : Type*) [AddCommGroup G] [Fintype G] (k : ℕ)
    (hk : k ≤ Fintype.card G) (hsmall : 2 ^ k < Fintype.card G) :
    ¬ Model.HalfComplete G k := by
  classical
  intro hhalf
  have hgood :
      Model.goodSets (Finset.univ : Finset G) Model.SubsetSumComplete k = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro A hA
    rw [Model.goodSets, Finset.mem_filter, Finset.mem_powersetCard] at hA
    exact not_subsetSumComplete_of_two_pow_card_lt A
      (by simpa [hA.1.2] using hsmall) hA.2
  rw [Model.HalfComplete, Model.totalCount, Model.completeCount,
    Finset.card_powersetCard, hgood] at hhalf
  simp only [Finset.card_empty, mul_zero] at hhalf
  exact (Nat.not_succ_le_zero _)
    ((Nat.choose_pos hk).trans_le hhalf)

/-! ## Finite Poisson approximation from the rank calculation -/

/-- The fully instantiated rank estimate, with its explicit coefficient
replaced by any larger relative error `epsilon`. -/
lemma factorialMoment_targetSubsetEventCount_relative_bound
    {p k r : ℕ} [Fact p.Prime] (B : Finset (ZMod p))
    {epsilon : ℝ}
    (hB : B.Nonempty) (hk : 0 < k) (hr : 0 < r)
    (hrk : r ≤ k) (hrM : r ≤ 2 ^ k - 1)
    (hprime : r.factorial < p)
    (hcoeff :
      (r : ℝ) ^ 2 / (2 ^ k - 1 : ℕ) +
          ((r * 2 ^ (r * r) * (2 ^ k) ^ (r - 1) : ℕ) : ℝ) /
            ((2 ^ k - 1 : ℕ) : ℝ) ^ r +
          incidenceLowRankEnvelope p k r B.card /
            (((B.card : ℝ) * (2 ^ k - 1 : ℕ) / p) ^ r) ≤ epsilon) :
    |factorialMoment (Erdos543.targetSubsetEventCount (k := k) B) r -
        (((B.card : ℝ) * (2 ^ k - 1 : ℕ) / p) ^ r)| ≤
      epsilon * (((B.card : ℝ) * (2 ^ k - 1 : ℕ) / p) ^ r) := by
  have hbase := abs_factorialMoment_targetSubsetEventCount_sub_leading_le_explicit
    (p := p) (k := k) (r := r) B hB hk hr hrk hrM hprime
  exact hbase.trans (mul_le_mul_of_nonneg_right hcoeff (by positivity))

/-- A finite Bonferroni wrapper specialized to subset-target events. -/
theorem prob_targetSubsetEventCount_zero_relative_bound
    {p k R s : ℕ} [Fact p.Prime] (B : Finset (ZMod p))
    {lambda epsilon : ℝ}
    (hlambda : lambda = (B.card : ℝ) * (2 ^ k - 1 : ℕ) / p)
    (hlambda0 : 0 ≤ lambda) (hepsilon : 0 ≤ epsilon)
    (htrunc : lambda ≤ (s + 1 : ℕ)) (horder : 2 * s + 1 ≤ R)
    (hmom : ∀ j ≤ R,
      |factorialMoment (Erdos543.targetSubsetEventCount (k := k) B) j -
          lambda ^ j| ≤ epsilon * lambda ^ j) :
    |prob {a | Erdos543.targetSubsetEventCount (k := k) B a = 0} /
        Real.exp (-lambda) - 1| ≤
      Real.exp lambda *
        (2 * lambda ^ (2 * s + 1) / ((2 * s + 1).factorial : ℝ) +
          epsilon * Real.exp lambda) := by
  subst lambda
  exact BonferroniAnalytic.abs_prob_zero_div_exp_neg_sub_one_le_of_le
    (Erdos543.targetSubsetEventCount (k := k) B)
    hlambda0 hepsilon htrunc horder hmom

/-! ## The vanishing common error envelope -/

/-- Relative Poisson error used uniformly for target sets of a fixed size. -/
noncomputable def poissonRelativeError (g : ℕ → ℝ) (m N : ℕ) : ℝ :=
  Real.exp ((m : ℝ) * collisionParameter g N) *
      (2 * ((m : ℝ) * collisionParameter g N) ^
          (2 * poissonCutoff N + 1) /
        ((2 * poissonCutoff N + 1).factorial : ℝ)) +
    3 * (N : ℝ) ^ (-(1 / 5 : ℝ)) *
      Real.exp ((2 * m : ℝ) * collisionParameter g N)

/-- One envelope that simultaneously dominates the singleton and pair
relative errors. -/
noncomputable def commonPoissonError (g : ℕ → ℝ) (N : ℕ) : ℝ :=
  poissonRelativeError g 1 N + poissonRelativeError g 2 N

lemma poissonRelativeError_nonneg (g : ℕ → ℝ) (m N : ℕ) :
    0 ≤ poissonRelativeError g m N := by
  rw [poissonRelativeError]
  apply add_nonneg
  · apply mul_nonneg (Real.exp_pos _).le
    apply div_nonneg
    · exact mul_nonneg (by norm_num)
        (pow_nonneg (mul_nonneg (Nat.cast_nonneg _)
          (collisionParameter_nonneg g N)) _)
    · exact Nat.cast_nonneg _
  · exact mul_nonneg
      (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (Nat.cast_nonneg N) (-(1 / 5 : ℝ))))
      (Real.exp_pos _).le

lemma commonPoissonError_nonneg (g : ℕ → ℝ) (N : ℕ) :
    0 ≤ commonPoissonError g N := by
  rw [commonPoissonError]
  exact add_nonneg (poissonRelativeError_nonneg g 1 N)
    (poissonRelativeError_nonneg g 2 N)

lemma tendsto_poissonRelativeError_zero {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0))
    (m : ℕ) :
    Tendsto (poissonRelativeError g m) atTop (nhds 0) := by
  have htail := tendsto_poisson_taylor_relative_tail_zero_nat_mul hg m
  have hrank := tendsto_rpow_neg_mul_exp_collisionParameter hg m
    (eta := (1 : ℝ) / 5) (by norm_num)
  have hrank3 : Tendsto (fun N : ℕ ↦
      3 * ((N : ℝ) ^ (-(1 / 5 : ℝ)) *
        Real.exp ((2 * m : ℝ) * collisionParameter g N)))
      atTop (nhds 0) := by
    simpa using hrank.const_mul 3
  have hsum := htail.add hrank3
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [] with N
  rw [poissonRelativeError]
  rw [show (2 * m : ℝ) * collisionParameter g N =
      2 * ((m : ℝ) * collisionParameter g N) by
    push_cast
    ring]
  ring

lemma tendsto_commonPoissonError_zero {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0)) :
    Tendsto (commonPoissonError g) atTop (nhds 0) := by
  change Tendsto (fun N ↦
    poissonRelativeError g 1 N + poissonRelativeError g 2 N) atTop (nhds 0)
  simpa only [zero_add] using
    (tendsto_poissonRelativeError_zero hg 1).add
      (tendsto_poissonRelativeError_zero hg 2)

/-- All finite hypotheses needed at a single prime, packaged in the exact
form supplied eventually by the asymptotic helper lemmas. -/
theorem targetSet_poisson_relative_error_at
    {g : ℕ → ℝ} {N m : ℕ} [Fact N.Prime]
    (B : Finset (ZMod N))
    (hcard : B.card = m) (hm : 0 < m)
    (hNq : (N : ℝ) ≤ (2 : ℝ) ^ cutoffSize g N)
    (hk : 0 < cutoffSize g N)
    (hRk : momentRadius N ≤ cutoffSize g N)
    (hRM : momentRadius N ≤ 2 ^ cutoffSize g N - 1)
    (hfac : ∀ j ≤ momentRadius N, j.factorial < N)
    (hcoeff : ∀ j, 1 ≤ j → j ≤ momentRadius N →
      (j : ℝ) ^ 2 / ((2 ^ cutoffSize g N - 1 : ℕ) : ℝ) +
          (((j * 2 ^ (j * j) * (2 ^ cutoffSize g N) ^ (j - 1) : ℕ) : ℝ) /
            (((2 ^ cutoffSize g N - 1 : ℕ) : ℝ) ^ j)) +
          incidenceLowRankEnvelope N (cutoffSize g N) j m /
            (((m : ℝ) * (2 ^ cutoffSize g N - 1 : ℕ) / N) ^ j) ≤
        3 * (N : ℝ) ^ (-(1 / 5 : ℝ)))
    (horder : 2 * poissonCutoff N + 1 ≤ momentRadius N)
    (htrunc : (m : ℝ) * collisionParameter g N ≤
      (poissonCutoff N + 1 : ℕ)) :
    |prob {a | Erdos543.targetSubsetEventCount
          (k := cutoffSize g N) B a = 0} /
        Real.exp (-((m : ℝ) * collisionParameter g N)) - 1| ≤
      poissonRelativeError g m N := by
  have hN : 0 < N := (Fact.out : N.Prime).pos
  have hB : B.Nonempty := Finset.card_pos.mp (by simpa [hcard] using hm)
  have hlambda :
      (m : ℝ) * collisionParameter g N =
        (B.card : ℝ) * (2 ^ cutoffSize g N - 1 : ℕ) / N := by
    rw [hcard, collisionParameter, Nat.cast_sub Nat.one_le_two_pow]
    norm_num
    ring
  have heps : 0 ≤ 3 * (N : ℝ) ^ (-(1 / 5 : ℝ)) := by positivity
  have hmom : ∀ j ≤ momentRadius N,
      |factorialMoment
          (Erdos543.targetSubsetEventCount (k := cutoffSize g N) B) j -
          ((m : ℝ) * collisionParameter g N) ^ j| ≤
        (3 * (N : ℝ) ^ (-(1 / 5 : ℝ))) *
          ((m : ℝ) * collisionParameter g N) ^ j := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      have hsamp : Fintype.card (Fin (cutoffSize g N) → ZMod N) ≠ 0 := by
        simp [ZMod.card, hN.ne']
      have hzero : factorialMoment
          (Erdos543.targetSubsetEventCount (k := cutoffSize g N) B) 0 = 1 := by
        simp [factorialMoment, FiniteProbability.expect, hsamp]
      rw [hzero]
      norm_num
      positivity
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have h := factorialMoment_targetSubsetEventCount_relative_bound
        (p := N) (k := cutoffSize g N) (r := j) B hB hk hjpos
        (hj.trans hRk) (hj.trans hRM) (hfac j hj)
        (by simpa [hcard] using hcoeff j hjpos hj)
      rw [← hlambda] at h
      simpa only [one_div] using h
  have hbonf := prob_targetSubsetEventCount_zero_relative_bound
    (p := N) (k := cutoffSize g N) (R := momentRadius N)
    (s := poissonCutoff N) B
    (lambda := (m : ℝ) * collisionParameter g N)
    (epsilon := 3 * (N : ℝ) ^ (-(1 / 5 : ℝ)))
    hlambda (mul_nonneg (Nat.cast_nonneg m) (collisionParameter_nonneg g N))
    heps htrunc horder hmom
  calc
    |prob {a | Erdos543.targetSubsetEventCount
          (k := cutoffSize g N) B a = 0} /
        Real.exp (-((m : ℝ) * collisionParameter g N)) - 1| ≤
        Real.exp ((m : ℝ) * collisionParameter g N) *
          (2 * ((m : ℝ) * collisionParameter g N) ^
              (2 * poissonCutoff N + 1) /
              ((2 * poissonCutoff N + 1).factorial : ℝ) +
            (3 * (N : ℝ) ^ (-(1 / 5 : ℝ))) *
              Real.exp ((m : ℝ) * collisionParameter g N)) := hbonf
    _ = poissonRelativeError g m N := by
      rw [poissonRelativeError,
        show (2 * m : ℝ) * collisionParameter g N =
          (m : ℝ) * collisionParameter g N +
            (m : ℝ) * collisionParameter g N by
          push_cast
          ring,
        Real.exp_add]
      ring

/-- Uniform eventual Poisson approximation for every target set of a fixed
positive cardinality.  Primality is passed as an explicit argument so the
statement lives on the ordinary `atTop` filter and may later be restricted to
the cofinal prime sequence. -/
theorem eventually_targetSet_poisson_relative_error
    {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0))
    (m : ℕ) (hm : 0 < m) :
    ∀ᶠ N : ℕ in atTop, ∀ hp : N.Prime,
      letI : Fact N.Prime := ⟨hp⟩
      ∀ B : Finset (ZMod N), B.card = m →
      (N : ℝ) ≤ (2 : ℝ) ^ cutoffSize g N →
      |prob {a | Erdos543.targetSubsetEventCount
            (k := cutoffSize g N) B a = 0} /
          Real.exp (-((m : ℝ) * collisionParameter g N)) - 1| ≤
        poissonRelativeError g m N := by
  have hsmall := eventually_collisionParameter_le_mul_poissonCutoff hg
    (epsilon := (1 : ℝ) / (m + 1)) (by positivity)
  filter_upwards [eventually_uniform_explicit_moment_error hg,
      eventually_one_le_cutoffSize hg,
      eventually_momentRadius_le_cutoffSize hg,
      eventually_momentRadius_le_nonemptyCube hg,
      eventually_factorial_lt_nat_of_le_momentRadius,
      eventually_two_mul_poissonCutoff_add_one_le_momentRadius,
      hsmall] with N hcoeff hk hRk hRM hfac horder hsmallN
  intro hp
  letI : Fact N.Prime := ⟨hp⟩
  intro B hcard hNq
  have htrunc : (m : ℝ) * collisionParameter g N ≤
      (poissonCutoff N + 1 : ℕ) := by
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have hmratio : (m : ℝ) / (m + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    calc
      (m : ℝ) * collisionParameter g N ≤
          (m : ℝ) *
            ((1 / (m + 1 : ℝ)) * (poissonCutoff N : ℝ)) :=
        mul_le_mul_of_nonneg_left hsmallN hm0
      _ = ((m : ℝ) / (m + 1)) * (poissonCutoff N : ℝ) := by ring
      _ ≤ (poissonCutoff N : ℝ) :=
        mul_le_of_le_one_left (Nat.cast_nonneg _) hmratio
      _ ≤ (poissonCutoff N + 1 : ℕ) := by norm_num
  exact targetSet_poisson_relative_error_at B hcard hm hNq hk hRk hRM hfac
    (fun j hjpos hj ↦ hcoeff j m hjpos hj hm hNq) horder htrunc

/-! ## The second-moment consequence -/

/-- At one prime in the nontrivial branch `N ≤ 2^k`, the uniform one- and
two-target estimates imply the standard second-moment upper bound for the
probability that every target is hit. -/
theorem prob_zeroMiss_le_secondMoment
    {g : ℕ → ℝ} {N : ℕ} [Fact N.Prime]
    (hone : ∀ B : Finset (ZMod N), B.card = 1 →
      |prob {a | Erdos543.targetSubsetEventCount
            (k := cutoffSize g N) B a = 0} /
          Real.exp (-((1 : ℝ) * collisionParameter g N)) - 1| ≤
        poissonRelativeError g 1 N)
    (htwo : ∀ B : Finset (ZMod N), B.card = 2 →
      |prob {a | Erdos543.targetSubsetEventCount
            (k := cutoffSize g N) B a = 0} /
          Real.exp (-((2 : ℝ) * collisionParameter g N)) - 1| ≤
        poissonRelativeError g 2 N)
    (hdelta : commonPoissonError g N ≤ (1 / 2 : ℝ)) :
    prob {a | MissedEvents.missedCount
        (missEvent (p := N) (k := cutoffSize g N)) a = 0} ≤
      6 / ((Fintype.card (NonzeroTarget N) : ℝ) *
        Real.exp (-collisionParameter g N)) +
      12 * commonPoissonError g N := by
  let lam : ℝ := collisionParameter g N
  let delta : ℝ := commonPoissonError g N
  have hsingle : ∀ x : NonzeroTarget N,
      |prob (missEvent (k := cutoffSize g N) x) - Real.exp (-lam)| ≤
        delta * Real.exp (-lam) := by
    intro x
    have hrel :
        |prob (missEvent (k := cutoffSize g N) x) / Real.exp (-lam) - 1| ≤
          poissonRelativeError g 1 N := by
      simpa [missEvent, lam] using
        hone ({(x : ZMod N)} : Finset (ZMod N)) (by simp)
    have habs := abs_sub_le_mul_of_abs_div_sub_one_le
      (Real.exp_pos (-lam)) hrel
    have heps : poissonRelativeError g 1 N ≤ delta := by
      dsimp [delta, commonPoissonError]
      exact le_add_of_nonneg_right (poissonRelativeError_nonneg g 2 N)
    exact habs.trans
      (mul_le_mul_of_nonneg_right heps (Real.exp_pos (-lam)).le)
  have hpair : ∀ x y : NonzeroTarget N, x ≠ y →
      |prob (missEvent (k := cutoffSize g N) x ∩ missEvent y) -
          Real.exp (-2 * lam)| ≤ delta * Real.exp (-2 * lam) := by
    intro x y hxy
    have hxyval : (x : ZMod N) ≠ (y : ZMod N) := by
      intro h
      exact hxy (Subtype.ext h)
    have hcard :
        ({(x : ZMod N), (y : ZMod N)} : Finset (ZMod N)).card = 2 := by
      simp [hxyval]
    have hrel :
        |prob (missEvent (k := cutoffSize g N) x ∩ missEvent y) /
            Real.exp (-2 * lam) - 1| ≤ poissonRelativeError g 2 N := by
      rw [missEvent_inter_eq_pairZero]
      simpa [lam] using htwo
        ({(x : ZMod N), (y : ZMod N)} : Finset (ZMod N)) hcard
    have habs := abs_sub_le_mul_of_abs_div_sub_one_le
      (Real.exp_pos (-2 * lam)) hrel
    have heps : poissonRelativeError g 2 N ≤ delta := by
      dsimp [delta, commonPoissonError]
      exact le_add_of_nonneg_left (poissonRelativeError_nonneg g 1 N)
    exact habs.trans
      (mul_le_mul_of_nonneg_right heps (Real.exp_pos (-2 * lam)).le)
  have hbound :=
    PoissonSecondMoment.prob_no_missed_le_of_relative_exp_errors
      (missEvent (p := N) (k := cutoffSize g N)) lam delta
      (commonPoissonError_nonneg g N) hdelta hsingle hpair
  simpa [lam, delta] using hbound

/-! ## Assembly on large prime moduli -/

/-- The obstruction already holds uniformly for every sufficiently large
prime modulus.  The proof splits according to the information-theoretic
alternative `2^k < N`; only its complement needs the moment calculation. -/
theorem eventually_not_halfComplete_at_primes
    {g : ℕ → ℝ}
    (hg : Tendsto (fun N ↦ g N / Real.log (Real.log (N : ℝ))) atTop (nhds 0)) :
    ∀ᶠ N : ℕ in atTop, ∀ hp : N.Prime,
      letI : NeZero N := ⟨hp.ne_zero⟩
      ¬ Model.HalfComplete (ZMod N) (cutoffSize g N) := by
  have hone := eventually_targetSet_poisson_relative_error hg 1 (by norm_num)
  have htwo := eventually_targetSet_poisson_relative_error hg 2 (by norm_num)
  have hdeltaSmall : ∀ᶠ N : ℕ in atTop,
      commonPoissonError g N < (1 / 192 : ℝ) :=
    (tendsto_order.1 (tendsto_commonPoissonError_zero hg)).2 _ (by norm_num)
  have hdenomLarge : ∀ᶠ N : ℕ in atTop,
      (192 : ℝ) < (N : ℝ) * Real.exp (-collisionParameter g N) :=
    (tendsto_nat_mul_exp_neg_collisionParameter_atTop hg).eventually
      (eventually_gt_atTop 192)
  have hcollisionSmall : ∀ᶠ N : ℕ in atTop,
      (cutoffSize g N : ℝ) ^ 2 / (N : ℝ) < (1 / 4 : ℝ) :=
    (tendsto_order.1 (tendsto_cutoffSize_sq_div_nat_zero hg)).2 _ (by norm_num)
  filter_upwards [hone, htwo, hdeltaSmall, hdenomLarge, hcollisionSmall]
      with N honeN htwoN hdeltaN hdenomN hcollisionN
  intro hp
  letI : Fact N.Prime := ⟨hp⟩
  letI : NeZero N := ⟨hp.ne_zero⟩
  let k : ℕ := cutoffSize g N
  by_cases hcube : N ≤ 2 ^ k
  · have hNq : (N : ℝ) ≤ (2 : ℝ) ^ k := by
      exact_mod_cast hcube
    have hone' : ∀ B : Finset (ZMod N), B.card = 1 →
        |prob {a | Erdos543.targetSubsetEventCount (k := k) B a = 0} /
            Real.exp (-((1 : ℝ) * collisionParameter g N)) - 1| ≤
          poissonRelativeError g 1 N := by
      intro B hB
      simpa [k] using honeN hp B hB (by simpa [k] using hNq)
    have htwo' : ∀ B : Finset (ZMod N), B.card = 2 →
        |prob {a | Erdos543.targetSubsetEventCount (k := k) B a = 0} /
            Real.exp (-((2 : ℝ) * collisionParameter g N)) - 1| ≤
          poissonRelativeError g 2 N := by
      intro B hB
      simpa [k] using htwoN hp B hB (by simpa [k] using hNq)
    have hdeltaHalf : commonPoissonError g N ≤ (1 / 2 : ℝ) := by
      linarith
    have hsecond := prob_zeroMiss_le_secondMoment
      (g := g) (N := N) hone' htwo' hdeltaHalf
    have hNreal : (2 : ℝ) ≤ N := by exact_mod_cast hp.two_le
    have hcard : (Fintype.card (NonzeroTarget N) : ℝ) = (N : ℝ) - 1 := by
      rw [card_nonzeroTarget, Nat.cast_sub hp.one_le]
      norm_num
    have hhalfCard : (N : ℝ) / 2 ≤
        (Fintype.card (NonzeroTarget N) : ℝ) := by
      rw [hcard]
      linarith
    have hqpos : 0 < Real.exp (-collisionParameter g N) := Real.exp_pos _
    have htargetDenom : (96 : ℝ) <
        (Fintype.card (NonzeroTarget N) : ℝ) *
          Real.exp (-collisionParameter g N) := by
      calc
        (96 : ℝ) = 192 / 2 := by norm_num
        _ < ((N : ℝ) * Real.exp (-collisionParameter g N)) / 2 :=
          div_lt_div_of_pos_right hdenomN (by norm_num)
        _ = ((N : ℝ) / 2) * Real.exp (-collisionParameter g N) := by ring
        _ ≤ (Fintype.card (NonzeroTarget N) : ℝ) *
            Real.exp (-collisionParameter g N) :=
          mul_le_mul_of_nonneg_right hhalfCard hqpos.le
    have hfrac :
        6 / ((Fintype.card (NonzeroTarget N) : ℝ) *
          Real.exp (-collisionParameter g N)) < (1 / 16 : ℝ) := by
      rw [div_lt_iff₀ (lt_trans (by norm_num) htargetDenom)]
      nlinarith
    have herr : 12 * commonPoissonError g N < (1 / 16 : ℝ) := by
      nlinarith
    have hmiss : prob {a | MissedEvents.missedCount
        (missEvent (p := N) (k := k)) a = 0} < (1 / 8 : ℝ) := by
      have hsecond' : prob {a | MissedEvents.missedCount
          (missEvent (p := N) (k := k)) a = 0} ≤
          6 / ((Fintype.card (NonzeroTarget N) : ℝ) *
            Real.exp (-collisionParameter g N)) +
          12 * commonPoissonError g N := by
        simpa [k] using hsecond
      nlinarith
    have hindexed :
        prob (IIDModel.indexedCompleteEvent (ZMod N) k) < (1 / 8 : ℝ) := by
      rw [← zeroMissEvent_eq_indexedCompleteEvent]
      exact hmiss
    exact HalfTransfer.not_halfComplete_zmod_of_prob_indexed_lt_eighth_of_sq_div_lt_quarter
        (by simpa [k] using hindexed) (by simpa [k] using hcollisionN)
  · have hpow : 2 ^ k < N := Nat.lt_of_not_ge hcube
    exact Model.not_halfComplete_zmod_of_two_pow_lt (by simpa [k] using hpow)

/-- The canonical prime-sequence version used by the final logical
contradiction. -/
theorem eventualPrimeCyclicFailure :
    FinalLogic.EventualPrimeCyclicFailure := by
  intro g hg
  have hlarge := PrimeSequence.eventually_primeSeq
    (eventually_not_halfComplete_at_primes hg)
  filter_upwards [hlarge] with i hi
  exact hi (PrimeSequence.primeSeq_prime i)

end

end Erdos543.CoreObstruction
