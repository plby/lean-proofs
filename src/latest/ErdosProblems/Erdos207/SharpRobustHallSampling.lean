/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SimultaneousRobustHallSampling

/-!
# Sharp lower-tail sampling for robust Hall

The group-hitting version of robust Hall is convenient, but its probability
bound discards a factor proportional to the size of the Hall obstruction.
Here we use the exact binomial lower-tail union bound instead.  For every
oriented small Hall obstruction we merely require that more than
`Delta * |S|` of all escaping candidate pairs were sampled.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Exact lower-tail union bound for the intersection of a fixed finite set
with a homogeneous Bernoulli subset. -/
theorem FiniteLaw.independentBits_probability_card_inter_selected_le_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) (S : Finset I) (k : ℕ) :
    (FiniteLaw.independentBits (fun _ : I ↦ sigma) (fun _ ↦ hsigma)).probability
        (fun omega ↦ (S ∩ FiniteLaw.selectedByBits omega).card ≤ k) ≤
      (Nat.choose S.card (S.card - k) : ℝ≥0) *
        (1 - sigma) ^ (S.card - k) := by
  let L := FiniteLaw.independentBits
    (fun _ : I ↦ sigma) (fun _ ↦ hsigma)
  let absentCount := S.card - k
  let P : Finset I → (I → Bool) → Prop := fun T omega ↦
    Disjoint T (FiniteLaw.selectedByBits omega)
  calc
    L.probability
        (fun omega ↦ (S ∩ FiniteLaw.selectedByBits omega).card ≤ k) ≤
      L.probability
        (fun omega ↦ ∃ T ∈ S.powersetCard absentCount, P T omega) := by
          apply L.probability_mono
          intro omega hcard
          have hpartition := card_sdiff_add_card_inter S
            (FiniteLaw.selectedByBits omega)
          have habsent : absentCount ≤
              (S \ FiniteLaw.selectedByBits omega).card := by
            dsimp only [absentCount]
            omega
          obtain ⟨T, hTsub, hTcard⟩ := exists_subset_card_eq habsent
          refine ⟨T, mem_powersetCard.mpr ⟨?_, hTcard⟩, ?_⟩
          · exact hTsub.trans sdiff_subset
          · change Disjoint T (FiniteLaw.selectedByBits omega)
            rw [Finset.disjoint_left]
            intro x hxT hxSelected
            exact (mem_sdiff.mp (hTsub hxT)).2 hxSelected
    _ ≤ ∑ T ∈ S.powersetCard absentCount, L.probability (P T) :=
      L.probability_exists_le (S.powersetCard absentCount) P
    _ = ∑ _T ∈ S.powersetCard absentCount,
          (1 - sigma) ^ absentCount := by
      apply sum_congr rfl
      intro T hT
      have hTcard := (mem_powersetCard.mp hT).2
      rw [show L.probability (P T) = (1 - sigma) ^ T.card by
        simpa only [L, P, prod_const] using
          (FiniteLaw.independentBits_probability_disjoint_selected
            (fun _ : I ↦ sigma) (fun _ ↦ hsigma) T)]
      rw [hTcard]
    _ = (Nat.choose S.card (S.card - k) : ℝ≥0) *
        (1 - sigma) ^ (S.card - k) := by
      simp [absentCount, card_powersetCard]

/-- The exact half-moment of the number of sampled coordinates from `S`.
This is the elementary moment-generating-function identity used for the
Chernoff-quality lower tail below. -/
theorem FiniteLaw.independentBits_expectation_half_pow_card_inter
    {I : Type*} [Fintype I] [DecidableEq I]
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) (S : Finset I) :
    (FiniteLaw.independentBits (fun _ : I ↦ sigma) (fun _ ↦ hsigma)).expectation
        (fun omega ↦ ∏ i ∈ S,
          if omega i = true then (1 / 2 : ℝ≥0) else 1) =
      (1 - sigma / 2) ^ S.card := by
  classical
  let half : ℝ≥0 := 1 / 2
  let L := FiniteLaw.independentBits
    (fun _ : I ↦ sigma) (fun _ ↦ hsigma)
  have hbase : (1 - sigma) + sigma * half = 1 - sigma / 2 := by
    have hsigmaHalf : sigma / 2 ≤ 1 :=
      (div_le_self (zero_le : 0 ≤ sigma) (by norm_num)).trans hsigma
    apply NNReal.eq
    simp only [half, NNReal.coe_add, NNReal.coe_sub hsigma,
      NNReal.coe_mul, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_ofNat, NNReal.coe_sub hsigmaHalf]
    norm_num
    ring
  change ∑ omega : I → Bool,
      (∏ i, FiniteLaw.bernoulliBitMass sigma (omega i)) *
        (∏ i ∈ S, if omega i = true then half else 1) =
      (1 - sigma / 2) ^ S.card
  calc
    _ = ∑ omega : I → Bool, ∏ i,
        FiniteLaw.bernoulliBitMass sigma (omega i) *
          (if i ∈ S then (if omega i = true then half else 1) else 1) := by
      apply Finset.sum_congr rfl
      intro omega _homega
      have hlocal :
          (∏ i ∈ S, if omega i = true then half else 1) =
            ∏ i, if i ∈ S then (if omega i = true then half else 1) else 1 :=
        (Fintype.prod_ite_mem S
          (fun i ↦ if omega i = true then half else 1)).symm
      rw [hlocal, ← Finset.prod_mul_distrib]
    _ = ∏ i, ∑ b : Bool,
        FiniteLaw.bernoulliBitMass sigma b *
          (if i ∈ S then (if b = true then half else 1) else 1) := by
      exact (Fintype.prod_sum fun i b ↦
        FiniteLaw.bernoulliBitMass sigma b *
          (if i ∈ S then (if b = true then half else 1) else 1)).symm
    _ = ∏ i, if i ∈ S then (1 - sigma) + sigma * half else 1 := by
      apply Finset.prod_congr rfl
      intro i _hi
      by_cases hiS : i ∈ S
      · simp [hiS, FiniteLaw.bernoulliBitMass, Fintype.sum_bool,
          add_comm]
      · simpa [hiS, FiniteLaw.bernoulliBitMass, Fintype.sum_bool,
          add_comm] using FiniteLaw.sum_bernoulliBitMass hsigma
    _ = ((1 - sigma) + sigma * half) ^ S.card := by
      rw [Fintype.prod_ite_mem]
      simp
    _ = (1 - sigma / 2) ^ S.card := by rw [hbase]

/-- A Chernoff-quality lower tail for a homogeneous Bernoulli subset.  The
proof is the half-moment method: on the event `|S ∩ R| ≤ k`, the random
variable `(1/2) ^ |S ∩ R|` is at least `(1/2) ^ k`. -/
theorem FiniteLaw.independentBits_probability_card_inter_selected_le_le_half
    {I : Type*} [Fintype I] [DecidableEq I]
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) (S : Finset I) (k : ℕ) :
    (FiniteLaw.independentBits (fun _ : I ↦ sigma) (fun _ ↦ hsigma)).probability
        (fun omega ↦ (S ∩ FiniteLaw.selectedByBits omega).card ≤ k) ≤
      (1 - sigma / 2) ^ S.card / (1 / 2 : ℝ≥0) ^ k := by
  classical
  let half : ℝ≥0 := 1 / 2
  let L := FiniteLaw.independentBits
    (fun _ : I ↦ sigma) (fun _ ↦ hsigma)
  let X : (I → Bool) → ℝ≥0 := fun omega ↦
    ∏ i ∈ S, if omega i = true then half else 1
  have hX (omega : I → Bool) :
      X omega = half ^ (S ∩ FiniteLaw.selectedByBits omega).card := by
    simp only [X, FiniteLaw.selectedByBits, Finset.inter_filter]
    rw [Finset.prod_ite]
    simp
  calc
    L.probability
        (fun omega ↦ (S ∩ FiniteLaw.selectedByBits omega).card ≤ k) ≤
      L.probability (fun omega ↦ half ^ k ≤ X omega) := by
        apply L.probability_mono
        intro omega hcard
        rw [hX]
        exact NNReal.pow_antitone_exp _ _ hcard (by norm_num [half])
    _ ≤ L.expectation X / half ^ k := by
      apply L.probability_le_expectation_div
      positivity
    _ = (1 - sigma / 2) ^ S.card / (1 / 2 : ℝ≥0) ^ k := by
      rw [show L.expectation X = (1 - sigma / 2) ^ S.card by
        simpa only [L, X, half] using
          FiniteLaw.independentBits_expectation_half_pow_card_inter
            sigma hsigma S]

/-- Restricting the relation to a sampled pair set restricts every oriented
Hall candidate family by intersection with that set. -/
lemma orientedSmallHallCandidates_sampled_eq_inter
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (R : Finset (A × B)) (o : OrientedSmallHallObstruction A B) :
    orientedSmallHallCandidates
        (fun a b ↦ r a b ∧ (a, b) ∈ R) o =
      orientedSmallHallCandidates r o ∩ R := by
  classical
  rcases o with o | o
  · ext ab
    rcases ab with ⟨a, b⟩
    simp only [mem_orientedSmallHallCandidates_left, mem_inter]
    tauto
  · ext ab
    rcases ab with ⟨a, b⟩
    simp only [mem_orientedSmallHallCandidates_right, mem_inter]
    tauto

/-- More than `Delta * |S|` sampled candidates for every oriented small
obstruction is exactly the deterministic certificate needed for two-sided
robust matchability. -/
theorem isTwoSidedRobustMatchingSample_of_many_oriented_candidates
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (Delta : ℕ) (hbalanced : Fintype.card A = Fintype.card B)
    (R : Finset (A × B))
    (hmany : ∀ o : OrientedSmallHallObstruction A B,
      Delta * orientedSmallHallSize o <
        (orientedSmallHallCandidates
          (fun a b ↦ r a b ∧ (a, b) ∈ R) o).card) :
    IsTwoSidedRobustMatchingSample r Delta R := by
  classical
  intro deleted _ hleftDegree hrightDegree
  obtain ⟨f, hfbij, hf⟩ :=
    exists_bijective_matching_of_twoSided_many_pairs
      (fun a b ↦ r a b ∧ (a, b) ∈ R) deleted Delta hbalanced
      hleftDegree hrightDegree
      (by
        intro S T hTS hSsmall
        let o : SmallHallObstruction A B := ⟨⟨(S, T), hTS⟩, hSsmall⟩
        simpa [orientedSmallHallSize,
          card_orientedSmallHallCandidates_left] using hmany (Sum.inl o))
      (by
        intro S T hTS hSsmall
        let o : SmallHallObstruction B A := ⟨⟨(S, T), hTS⟩, hSsmall⟩
        simpa [orientedSmallHallSize,
          card_orientedSmallHallCandidates_right] using hmany (Sum.inr o))
  exact ⟨f, hfbij, fun a ↦ ⟨(hf a).1.1, (hf a).1.2, (hf a).2⟩⟩

/-- A sharp finite union bound for failure of two-sided robust Hall, using
the half-moment lower tail for every obstruction. -/
theorem independentBits_probability_not_twoSidedRobust_le_sharp
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (r : A → B → Prop) [DecidableRel r]
    (Delta : ℕ) (hbalanced : Fintype.card A = Fintype.card B)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) :
    (FiniteLaw.independentBits
      (fun _ : A × B ↦ sigma) (fun _ ↦ hsigma)).probability
        (fun omega ↦ ¬ IsTwoSidedRobustMatchingSample r Delta
          (FiniteLaw.selectedByBits omega)) ≤
      ∑ o : OrientedSmallHallObstruction A B,
        (1 - sigma / 2) ^ (orientedSmallHallCandidates r o).card /
          (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize o) := by
  classical
  let L := FiniteLaw.independentBits
    (fun _ : A × B ↦ sigma) (fun _ ↦ hsigma)
  let Bad : OrientedSmallHallObstruction A B →
      ((A × B → Bool) → Prop) := fun o omega ↦
    ((orientedSmallHallCandidates r o) ∩
      FiniteLaw.selectedByBits omega).card ≤
        Delta * orientedSmallHallSize o
  calc
    L.probability (fun omega ↦
        ¬ IsTwoSidedRobustMatchingSample r Delta
          (FiniteLaw.selectedByBits omega)) ≤
      L.probability (fun omega ↦ ∃ o ∈
        (univ : Finset (OrientedSmallHallObstruction A B)), Bad o omega) := by
      apply L.probability_mono
      intro omega hnot
      by_contra hnone
      push Not at hnone
      apply hnot
      apply isTwoSidedRobustMatchingSample_of_many_oriented_candidates
        r Delta hbalanced
      intro o
      rw [orientedSmallHallCandidates_sampled_eq_inter]
      exact Nat.lt_of_not_ge (hnone o (mem_univ o))
    _ ≤ ∑ o ∈ (univ : Finset (OrientedSmallHallObstruction A B)),
        L.probability (Bad o) := L.probability_exists_le univ Bad
    _ ≤ ∑ o ∈ (univ : Finset (OrientedSmallHallObstruction A B)),
        (1 - sigma / 2) ^ (orientedSmallHallCandidates r o).card /
          (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize o) := by
      apply sum_le_sum
      intro o _ho
      exact FiniteLaw.independentBits_probability_card_inter_selected_le_le_half
        sigma hsigma (orientedSmallHallCandidates r o)
          (Delta * orientedSmallHallSize o)
    _ = ∑ o : OrientedSmallHallObstruction A B,
        (1 - sigma / 2) ^ (orientedSmallHallCandidates r o).card /
          (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize o) := by simp

/-- The candidate coordinates of one oriented obstruction, embedded into
the global simultaneous-reservoir coordinate type. -/
def simultaneousOrientedHallCandidates
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    [∀ o, DecidableRel (r o)]
    (o : O)
    (h : OrientedSmallHallObstruction ↥(K o).left ↥(K o).right) :
    Finset (SimultaneousLinkPair O V K) :=
  (orientedSmallHallCandidates (r o) h).map
    (simultaneousLinkPairAtEmbedding K o)

@[simp]
lemma card_simultaneousOrientedHallCandidates
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    [∀ o, DecidableRel (r o)]
    (o : O)
    (h : OrientedSmallHallObstruction ↥(K o).left ↥(K o).right) :
    (simultaneousOrientedHallCandidates K r o h).card =
      (orientedSmallHallCandidates (r o) h).card := by
  simp [simultaneousOrientedHallCandidates]

/-- Restriction of the global selected coordinate set to one embedded
candidate family has the same cardinality as the corresponding local
restriction. -/
lemma card_simultaneous_candidates_inter_selected
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    [∀ o, DecidableRel (r o)]
    (omega : SimultaneousLinkPair O V K → Bool) (o : O)
    (h : OrientedSmallHallObstruction ↥(K o).left ↥(K o).right) :
    (simultaneousOrientedHallCandidates K r o h ∩
        FiniteLaw.selectedByBits omega).card =
      (orientedSmallHallCandidates (r o) h ∩
        simultaneousLinkSelectedPairs K omega o).card := by
  classical
  have heq : simultaneousOrientedHallCandidates K r o h ∩
        FiniteLaw.selectedByBits omega =
      (orientedSmallHallCandidates (r o) h ∩
        simultaneousLinkSelectedPairs K omega o).map
          (simultaneousLinkPairAtEmbedding K o) := by
    ext z
    constructor
    · intro hz
      obtain ⟨ab, hab, rfl⟩ := mem_map.mp (mem_inter.mp hz).1
      apply mem_map.mpr
      refine ⟨ab, mem_inter.mpr ⟨hab, ?_⟩, rfl⟩
      exact mem_simultaneousLinkSelectedPairs_iff.mpr
        (FiniteLaw.mem_selectedByBits_iff.mp (mem_inter.mp hz).2)
    · intro hz
      obtain ⟨ab, hab, rfl⟩ := mem_map.mp hz
      apply mem_inter.mpr
      constructor
      · exact mem_map.mpr ⟨ab, (mem_inter.mp hab).1, rfl⟩
      · exact FiniteLaw.mem_selectedByBits_iff.mpr
          (mem_simultaneousLinkSelectedPairs_iff.mp (mem_inter.mp hab).2)
  rw [heq, card_map]

/-- Simultaneous sharp Hall failure bound.  The sum ranges over centers and
oriented obstructions, and each term retains the full candidate-set lower
tail rather than a single fixed group. -/
theorem independentBits_probability_not_all_twoSidedRobust_le_sharp
    {O V : Type*} [Fintype O] [DecidableEq O]
    [Fintype V] [DecidableEq V]
    (K : O → BipartiteLink V)
    (r : ∀ o, ↥(K o).left → ↥(K o).right → Prop)
    [rDecidable : ∀ o, DecidableRel (r o)]
    (Delta : ℕ)
    (hbalanced : ∀ o, (K o).left.card = (K o).right.card)
    (sigma : ℝ≥0) (hsigma : sigma ≤ 1) :
    (FiniteLaw.independentBits
      (fun _ : SimultaneousLinkPair O V K ↦ sigma)
      (fun _ ↦ hsigma)).probability (fun omega ↦
        ¬ ∀ o, IsTwoSidedRobustMatchingSample (r o) Delta
          (simultaneousLinkSelectedPairs K omega o)) ≤
      ∑ o : O,
        ∑ h : OrientedSmallHallObstruction
            ↥(K o).left ↥(K o).right,
          (1 - sigma / 2) ^
              (orientedSmallHallCandidates (r o) h).card /
            (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize h) := by
  classical
  let L := FiniteLaw.independentBits
    (fun _ : SimultaneousLinkPair O V K ↦ sigma) (fun _ ↦ hsigma)
  let Index := Σ o : O,
    OrientedSmallHallObstruction ↥(K o).left ↥(K o).right
  let Bad : Index → ((SimultaneousLinkPair O V K → Bool) → Prop) :=
    fun z omega ↦
      (simultaneousOrientedHallCandidates K r z.1 z.2 ∩
        FiniteLaw.selectedByBits omega).card ≤
          Delta * orientedSmallHallSize z.2
  calc
    L.probability (fun omega ↦
        ¬ ∀ o, IsTwoSidedRobustMatchingSample (r o) Delta
          (simultaneousLinkSelectedPairs K omega o)) ≤
      L.probability (fun omega ↦ ∃ z ∈ (univ : Finset Index),
        Bad z omega) := by
      apply L.probability_mono
      intro omega hnot
      by_contra hnone
      push Not at hnone
      apply hnot
      intro o
      apply isTwoSidedRobustMatchingSample_of_many_oriented_candidates
        (r o) Delta (by simpa using hbalanced o)
      intro h
      rw [orientedSmallHallCandidates_sampled_eq_inter]
      rw [← card_simultaneous_candidates_inter_selected K r omega o h]
      let z : Index := ⟨o, h⟩
      exact Nat.lt_of_not_ge (hnone z (mem_univ z))
    _ ≤ ∑ z ∈ (univ : Finset Index), L.probability (Bad z) :=
      L.probability_exists_le univ Bad
    _ ≤ ∑ z ∈ (univ : Finset Index),
        (1 - sigma / 2) ^
            (orientedSmallHallCandidates (r z.1) z.2).card /
          (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize z.2) := by
      apply sum_le_sum
      intro z _hz
      simpa only [L, Bad, card_simultaneousOrientedHallCandidates] using
        (FiniteLaw.independentBits_probability_card_inter_selected_le_le_half
          sigma hsigma (simultaneousOrientedHallCandidates K r z.1 z.2)
            (Delta * orientedSmallHallSize z.2))
    _ = ∑ o : O,
        ∑ h : OrientedSmallHallObstruction
            ↥(K o).left ↥(K o).right,
          (1 - sigma / 2) ^
              (orientedSmallHallCandidates (r o) h).card /
            (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize h) := by
      simpa only [Index] using
        (Fintype.sum_sigma (fun z : Index ↦
          (1 - sigma / 2) ^
              (orientedSmallHallCandidates (r z.1) z.2).card /
            (1 / 2 : ℝ≥0) ^ (Delta * orientedSmallHallSize z.2)))

end

end Erdos207
