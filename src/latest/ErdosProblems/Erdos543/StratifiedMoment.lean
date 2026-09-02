/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, ChatGPT
-/

import ErdosProblems.Erdos543.Incidence
import ErdosProblems.Erdos543.FullRankCount
import ErdosProblems.Erdos543.LinearFibers
import ErdosProblems.Erdos543.LowRankSharp
import ErdosProblems.Erdos543.MomentBounds
import ErdosProblems.Erdos543.Moments

/-!
# Rank-stratified factorial moments for subset-sum incidences

This file gives the exact finite expansion used before the analytic estimates
in the Ma--Tang argument.  For a finite target set `B ⊆ ZMod p`, an event is
a pair `(S,b)`, where `S` is a nonempty subset of the independent coordinates
and `b ∈ B`; it occurs when the coordinates indexed by `S` sum to `b`.

The falling-factorial moment of the number of occurring pairs is a sum over
ordered injective tuples of pairs.  Tuples which repeat the subset `S` with two
different targets have empty joint event.  After deleting precisely those
zero terms, the remaining tuples are equivalently:

* an ordered embedding of distinct nonempty subsets, and
* an arbitrary assignment of a target in `B` to each row.

The joint event is an affine fiber of the zero-one incidence matrix.  We group
the surviving terms by matrix rank and consistency of the right-hand side,
obtaining an exact natural-number identity.  A second theorem bounds each
rank stratum by the rational incidence-pattern counts from `Incidence.lean`;
the only extra input it needs is stability of rank under reduction modulo the
prime.
-/

open scoped BigOperators
open Finset

namespace Erdos543

attribute [local instance] Classical.propDecidable

noncomputable section

variable {p r k d : ℕ} [Fact p.Prime]

local instance : NeZero p :=
  ⟨Nat.Prime.ne_zero (show p.Prime from Fact.out)⟩

/-! ## The finite family of subset-target events -/

/-- A target constrained to belong to the finite set `B`. -/
abbrev TargetIn (B : Finset (ZMod p)) := {b : ZMod p // b ∈ B}

/-- An event is a nonempty coordinate subset together with a target in `B`. -/
abbrev TargetSubsetEvent (k : ℕ) (B : Finset (ZMod p)) :=
  NonemptyIndexSet k × TargetIn B

/-- The event `(S,b)` occurs at `a` when `∑ i ∈ S, a i = b`. -/
def targetSubsetEventOccurs (B : Finset (ZMod p))
    (e : TargetSubsetEvent k B) (a : Fin k → ZMod p) : Prop :=
  ∑ i ∈ (e.1 : Finset (Fin k)), a i = (e.2 : ZMod p)

/-- Number of subset-target incidences occurring at the sample point `a`. -/
def targetSubsetEventCount (B : Finset (ZMod p)) (a : Fin k → ZMod p) : ℕ :=
  eventCount (targetSubsetEventOccurs B) a

/-- The subset projections of an ordered tuple of pairs are distinct. -/
def SubsetsInjective (B : Finset (ZMod p))
    (ι : Fin r ↪ TargetSubsetEvent k B) : Prop :=
  Function.Injective (fun i ↦ (ι i).1)

omit [Fact (Nat.Prime p)] in
/-- Repeating one subset in an injective tuple of pairs forces the two targets
to be different. -/
lemma targets_ne_of_repeated_subset (B : Finset (ZMod p))
    (ι : Fin r ↪ TargetSubsetEvent k B) {i j : Fin r} (hij : i ≠ j)
    (hsub : (ι i).1 = (ι j).1) : (ι i).2 ≠ (ι j).2 := by
  intro htarget
  apply hij
  apply ι.injective
  exact Prod.ext hsub htarget

/-- A tuple which uses the same subset for two different rows has no common
sample point, hence contributes zero to the factorial moment. -/
lemma jointEventCount_eq_zero_of_repeated_subset (B : Finset (ZMod p))
    (ι : Fin r ↪ TargetSubsetEvent k B) {i j : Fin r} (hij : i ≠ j)
    (hsub : (ι i).1 = (ι j).1) :
    jointEventCount (targetSubsetEventOccurs B) ι = 0 := by
  classical
  rw [jointEventCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ ha
  have hi := ha i
  have hj := ha j
  apply targets_ne_of_repeated_subset B ι hij hsub
  apply Subtype.ext
  have hsum : (∑ i ∈ ((ι i).1 : Finset (Fin k)), a i) =
      ∑ i ∈ ((ι j).1 : Finset (Fin k)), a i := by
    rw [hsub]
  exact hi.symm.trans (hsum.trans hj)

/-- All terms outside the distinct-subset subfamily vanish. -/
theorem sum_jointEventCount_eq_sum_subsetsInjective
    (B : Finset (ZMod p)) :
    (∑ ι : Fin r ↪ TargetSubsetEvent k B,
        jointEventCount (targetSubsetEventOccurs B) ι) =
      ∑ ι ∈ (Finset.univ : Finset (Fin r ↪ TargetSubsetEvent k B)).filter
          (SubsetsInjective B),
        jointEventCount (targetSubsetEventOccurs B) ι := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro ι hι hnot
  have hninj : ¬ Function.Injective (fun i ↦ (ι i).1) := by
    simpa [SubsetsInjective] using hnot
  obtain ⟨i, j, hsub, hij⟩ := Function.not_injective_iff.mp hninj
  exact jointEventCount_eq_zero_of_repeated_subset B ι hij hsub

/-! ## Splitting the surviving tuples into patterns and target assignments -/

/-- Split a pair tuple with distinct subset projections into its incidence
pattern and its row-wise target assignment. -/
def splitTargetSubsetEmbedding (B : Finset (ZMod p))
    (x : {ι : Fin r ↪ TargetSubsetEvent k B // SubsetsInjective B ι}) :
    (Fin r ↪ NonemptyIndexSet k) × (Fin r → TargetIn B) :=
  (⟨fun i ↦ (x.1 i).1, x.2⟩, fun i ↦ (x.1 i).2)

/-- Combine an incidence pattern and targets into an injective tuple of
subset-target pairs. -/
def mergeTargetSubsetEmbedding (B : Finset (ZMod p))
    (x : (Fin r ↪ NonemptyIndexSet k) × (Fin r → TargetIn B)) :
    Fin r ↪ TargetSubsetEvent k B where
  toFun i := (x.1 i, x.2 i)
  inj' := fun _ _ h ↦ x.1.injective (congrArg Prod.fst h)

omit [Fact (Nat.Prime p)] in
lemma mergeTargetSubsetEmbedding_subsetsInjective (B : Finset (ZMod p))
    (x : (Fin r ↪ NonemptyIndexSet k) × (Fin r → TargetIn B)) :
    SubsetsInjective B (mergeTargetSubsetEmbedding B x) := by
  exact x.1.injective

/-- Exact equivalence after the repeated-subset zero terms are removed. -/
def targetSubsetEmbeddingEquiv (B : Finset (ZMod p)) :
    {ι : Fin r ↪ TargetSubsetEvent k B // SubsetsInjective B ι} ≃
      (Fin r ↪ NonemptyIndexSet k) × (Fin r → TargetIn B) where
  toFun := splitTargetSubsetEmbedding B
  invFun x := ⟨mergeTargetSubsetEmbedding B x,
    mergeTargetSubsetEmbedding_subsetsInjective B x⟩
  left_inv x := by
    apply Subtype.ext
    apply DFunLike.ext _ _
    intro i
    rfl
  right_inv x := by
    apply Prod.ext
    · apply DFunLike.ext _ _
      intro i
      rfl
    · funext i
      rfl

/-! ## The affine system attached to a pattern -/

/-- Right-hand side supplied by the target assignment. -/
def targetVector {B : Finset (ZMod p)}
    (t : Fin r → TargetIn B) : Fin r → ZMod p :=
  fun i ↦ (t i).1

/-- Multiplication by an incidence matrix is the corresponding indexed sum. -/
lemma incidenceMatrix_mulVec_apply (ι : Fin r ↪ NonemptyIndexSet k)
    (a : Fin k → ZMod p) (i : Fin r) :
    (incidenceMatrix (R := ZMod p) ι).mulVec a i =
      ∑ j ∈ (ι i : Finset (Fin k)), a j := by
  classical
  simp [Matrix.mulVec, dotProduct, incidenceMatrix]

lemma all_merged_events_iff_matrix_system (B : Finset (ZMod p))
    (ι : Fin r ↪ NonemptyIndexSet k) (t : Fin r → TargetIn B)
    (a : Fin k → ZMod p) :
    (∀ i, targetSubsetEventOccurs B
        (mergeTargetSubsetEmbedding B (ι, t) i) a) ↔
      (incidenceMatrix (R := ZMod p) ι).mulVec a = targetVector t := by
  rw [funext_iff]
  apply forall_congr'
  intro i
  rw [incidenceMatrix_mulVec_apply]
  change (∑ j ∈ (ι i : Finset (Fin k)), a j = (t i).1) ↔
    ∑ j ∈ (ι i : Finset (Fin k)), a j = (t i).1
  rfl

/-- Joint event counts are exactly affine-fiber cardinalities. -/
theorem jointEventCount_merge_eq_matrixFiber (B : Finset (ZMod p))
    (ι : Fin r ↪ NonemptyIndexSet k) (t : Fin r → TargetIn B) :
    jointEventCount (targetSubsetEventOccurs B)
        (mergeTargetSubsetEmbedding B (ι, t)) =
      (matrixFiber (incidenceMatrix (R := ZMod p) ι) (targetVector t)).card := by
  classical
  apply congrArg Finset.card
  unfold matrixFiber linearFiber
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact all_merged_events_iff_matrix_system B ι t a

end

end Erdos543

namespace Erdos543

attribute [local instance] Classical.propDecidable

noncomputable section

variable {p r k d : ℕ} [Fact p.Prime]

local instance : NeZero p :=
  ⟨Nat.Prime.ne_zero (show p.Prime from Fact.out)⟩

/-! ## Compatible modular-rank strata -/

/-- Rank over the prime field of the incidence pattern. -/
def modularIncidenceRank (p : ℕ) [Fact p.Prime]
    (ι : Fin r ↪ NonemptyIndexSet k) : ℕ :=
  (incidenceMatrix (R := ZMod p) ι).rank

/-- The assigned targets form a consistent affine system. -/
def PatternTargetsConsistent (p : ℕ) [Fact p.Prime]
    {B : Finset (ZMod p)}
    (x : (Fin r ↪ NonemptyIndexSet k) ×
      (Fin r → TargetIn B)) : Prop :=
  targetVector x.2 ∈
    Set.range (incidenceMatrix (R := ZMod p) x.1).mulVecLin

/-- Incidence patterns and target assignments of modular rank `d` whose
right-hand side is attainable. -/
def compatiblePatternTargetsOfRank (p : ℕ) [Fact p.Prime]
    (B : Finset (ZMod p)) (r k d : ℕ) :
    Finset ((Fin r ↪ NonemptyIndexSet k) × (Fin r → TargetIn B)) := by
  classical
  exact Finset.univ.filter fun x ↦
    PatternTargetsConsistent p x ∧ modularIncidenceRank p x.1 = d

@[simp] lemma mem_compatiblePatternTargetsOfRank
    (B : Finset (ZMod p))
    {x : (Fin r ↪ NonemptyIndexSet k) × (Fin r → TargetIn B)} :
    x ∈ compatiblePatternTargetsOfRank p B r k d ↔
      PatternTargetsConsistent p x ∧ modularIncidenceRank p x.1 = d := by
  classical
  simp [compatiblePatternTargetsOfRank]

/-- The joint-event count is zero for an inconsistent right-hand side and is
`p^(k-rank)` for a consistent one. -/
theorem jointEventCount_merge_eq_if_consistent
    (B : Finset (ZMod p)) (ι : Fin r ↪ NonemptyIndexSet k)
    (t : Fin r → TargetIn B) :
    jointEventCount (targetSubsetEventOccurs B)
        (mergeTargetSubsetEmbedding B (ι, t)) =
      if PatternTargetsConsistent p (ι, t) then
        p ^ (k - modularIncidenceRank p ι) else 0 := by
  rw [jointEventCount_merge_eq_matrixFiber]
  by_cases hconsistent : PatternTargetsConsistent p (ι, t)
  · rw [if_pos hconsistent]
    simpa [modularIncidenceRank] using
      card_matrixFiber (incidenceMatrix (R := ZMod p) ι) hconsistent
  · rw [if_neg hconsistent, Finset.card_eq_zero]
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨a, ha⟩
    rw [mem_matrixFiber] at ha
    exact hconsistent ⟨a, ha⟩

/-- Exact deletion-and-reindexing identity for the sum of all joint counts. -/
theorem sum_jointEventCount_eq_sum_patterns_targets
    (B : Finset (ZMod p)) :
    (∑ ι : Fin r ↪ TargetSubsetEvent k B,
        jointEventCount (targetSubsetEventOccurs B) ι) =
      ∑ x : (Fin r ↪ NonemptyIndexSet k) × (Fin r → TargetIn B),
        jointEventCount (targetSubsetEventOccurs B)
          (mergeTargetSubsetEmbedding B x) := by
  rw [sum_jointEventCount_eq_sum_subsetsInjective]
  rw [Finset.sum_subtype (p := SubsetsInjective B)
    ((Finset.univ : Finset (Fin r ↪ TargetSubsetEvent k B)).filter
      (SubsetsInjective B)) (by
        intro ι
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]) (fun ι ↦
        jointEventCount (targetSubsetEventOccurs B) ι)]
  apply Fintype.sum_equiv (targetSubsetEmbeddingEquiv B)
  intro x
  rfl

/-- Modular rank is bounded by the number of rows. -/
lemma modularIncidenceRank_le_rows (p : ℕ) [Fact p.Prime]
    (ι : Fin r ↪ NonemptyIndexSet k) : modularIncidenceRank p ι ≤ r := by
  change (incidenceMatrix (R := ZMod p) ι).rank ≤ r
  simpa using Matrix.rank_le_card_height (incidenceMatrix (R := ZMod p) ι)

lemma jointEventCount_merge_eq_if_consistent_pair
    (B : Finset (ZMod p))
    (x : (Fin r ↪ NonemptyIndexSet k) × (Fin r → TargetIn B)) :
    jointEventCount (targetSubsetEventOccurs B)
        (mergeTargetSubsetEmbedding B x) =
      if PatternTargetsConsistent p x then
        p ^ (k - modularIncidenceRank p x.1) else 0 := by
  rcases x with ⟨ι, t⟩
  exact jointEventCount_merge_eq_if_consistent B ι t

/-- Group the exact joint-count expansion by compatible modular-rank strata. -/
theorem sum_jointEventCount_eq_sum_rank_strata
    (B : Finset (ZMod p)) :
    (∑ ι : Fin r ↪ TargetSubsetEvent k B,
        jointEventCount (targetSubsetEventOccurs B) ι) =
      ∑ d ∈ Finset.range (r + 1),
        (compatiblePatternTargetsOfRank p B r k d).card * p ^ (k - d) := by
  rw [sum_jointEventCount_eq_sum_patterns_targets]
  simp_rw [jointEventCount_merge_eq_if_consistent_pair]
  rw [← Finset.sum_filter]
  let s : Finset ((Fin r ↪ NonemptyIndexSet k) × (Fin r → TargetIn B)) :=
    Finset.univ.filter (PatternTargetsConsistent p)
  have hmaps : ∀ x ∈ s,
      modularIncidenceRank p x.1 ∈ Finset.range (r + 1) := by
    intro x hx
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (modularIncidenceRank_le_rows p x.1)
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps
    (fun x ↦ p ^ (k - modularIncidenceRank p x.1))
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro e he
  have hconst : ∀ x ∈ s.filter (fun x ↦ modularIncidenceRank p x.1 = e),
      p ^ (k - modularIncidenceRank p x.1) = p ^ (k - e) := by
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  rw [Finset.sum_const_nat hconst]
  congr 1
  apply congrArg Finset.card
  ext x
  simp [s, compatiblePatternTargetsOfRank]

/-! ## The exact factorial-moment identity and a rank-stratum bound -/

/-- Exact unnormalised falling-factorial moment, stratified by modular rank
and consistency of the target assignment. -/
theorem sum_descFactorial_targetSubsetEventCount_eq_rank_strata
    (B : Finset (ZMod p)) :
    (∑ a : Fin k → ZMod p,
        (targetSubsetEventCount B a).descFactorial r) =
      ∑ d ∈ Finset.range (r + 1),
        (compatiblePatternTargetsOfRank p B r k d).card * p ^ (k - d) := by
  change (∑ a : Fin k → ZMod p,
      (eventCount (targetSubsetEventOccurs B) a).descFactorial r) = _
  rw [sum_descFactorial_eventCount]
  exact sum_jointEventCount_eq_sum_rank_strata B

/-- If modular and rational rank agree for every incidence pattern, then the
number of compatible rank-`d` pattern/target pairs is at most the number of
rational rank-`d` patterns times `|B|^r`. -/
theorem card_compatiblePatternTargetsOfRank_le
    (B : Finset (ZMod p))
    (hstable : ∀ ι : Fin r ↪ NonemptyIndexSet k,
      modularIncidenceRank p ι = incidenceRank ι) :
    (compatiblePatternTargetsOfRank p B r k d).card ≤
      (incidenceEmbeddingsOfRank r k d).card * B.card ^ r := by
  classical
  let ambient : Finset ((Fin r ↪ NonemptyIndexSet k) × (Fin r → TargetIn B)) :=
    (incidenceEmbeddingsOfRank r k d).product Finset.univ
  have hsubset : compatiblePatternTargetsOfRank p B r k d ⊆ ambient := by
    intro x hx
    rw [mem_compatiblePatternTargetsOfRank] at hx
    change x ∈ (incidenceEmbeddingsOfRank r k d).product Finset.univ
    apply Finset.mem_product.mpr
    constructor
    · rw [mem_incidenceEmbeddingsOfRank, ← hstable x.1]
      exact hx.2
    · exact Finset.mem_univ _
  refine (Finset.card_le_card hsubset).trans_eq ?_
  simp [ambient]

/-- Rank-stability converts the exact modular expansion into the rational
rank-stratum upper bound used with `LowRankCount`. -/
theorem sum_descFactorial_targetSubsetEventCount_le_rational_strata
    (B : Finset (ZMod p))
    (hstable : ∀ ι : Fin r ↪ NonemptyIndexSet k,
      modularIncidenceRank p ι = incidenceRank ι) :
    (∑ a : Fin k → ZMod p,
        (targetSubsetEventCount B a).descFactorial r) ≤
      ∑ d ∈ Finset.range (r + 1),
        (orderedDistinctRowLowRankMatrices r d k).card *
          B.card ^ r * p ^ (k - d) := by
  rw [sum_descFactorial_targetSubsetEventCount_eq_rank_strata]
  apply Finset.sum_le_sum
  intro e he
  rw [← card_incidenceEmbeddingsOfRank_eq]
  exact Nat.mul_le_mul_right (p ^ (k - e))
    (card_compatiblePatternTargetsOfRank_le B hstable)

/-! ## Prime-stable ranks and the normalized moment decomposition -/

/-- The factorial bound `r! < p` makes rational and modular incidence ranks
agree simultaneously for every `r`-row incidence pattern. -/
theorem modularIncidenceRank_eq_incidenceRank_of_factorial_lt
    (hprime : r.factorial < p) (ι : Fin r ↪ NonemptyIndexSet k) :
    modularIncidenceRank p ι = incidenceRank ι := by
  have hfac :
      ((incidenceMatrix (R := ℤ) ι).map (Int.castRingHom ℚ)).rank.factorial < p := by
    rw [incidenceMatrix_map, ← incidenceRank_eq_matrix_rank]
    exact (Nat.factorial_le (incidenceRank_le_rows ι)).trans_lt hprime
  have h := rank_map_zmod_eq_rank_map_rat_of_zero_one
    (p := p) (incidenceMatrix (R := ℤ) ι)
    (incidenceMatrix_zero_or_one ι) hfac
  rw [incidenceMatrix_map, incidenceMatrix_map] at h
  rw [modularIncidenceRank, incidenceRank_eq_matrix_rank]
  exact h

/-- The count of consistent rank-`d` target assignments used as `C d` in
`MomentBounds.lean`. -/
noncomputable def consistentRankCount (p : ℕ) [Fact p.Prime]
    (B : Finset (ZMod p)) (r k d : ℕ) : ℕ :=
  (compatiblePatternTargetsOfRank p B r k d).card

/-- The rational rank-`d` incidence-pattern count used as `T d`. -/
noncomputable def incidencePatternCount (r k d : ℕ) : ℕ :=
  (orderedDistinctRowLowRankMatrices r d k).card

@[simp] lemma incidencePatternCount_eq (r k d : ℕ) :
    incidencePatternCount r k d =
      (incidenceEmbeddingsOfRank r k d).card := by
  rw [incidencePatternCount, card_incidenceEmbeddingsOfRank_eq]

/-- A nonempty ordered incidence pattern has positive rational rank. -/
lemma incidenceRank_pos (hr : 0 < r)
    (ι : Fin r ↪ NonemptyIndexSet k) : 0 < incidenceRank ι := by
  let i : Fin r := ⟨0, hr⟩
  obtain ⟨j, hj⟩ := incidenceMatrix_row_nonzero (R := ℚ) ι i
  have hcolmem : (incidenceMatrix (R := ℚ) ι).col j ∈
      rationalColumnSpan (incidenceMatrix (R := ℚ) ι) :=
    Submodule.subset_span (Set.mem_range_self j)
  have hspan : rationalColumnSpan (incidenceMatrix (R := ℚ) ι) ≠ ⊥ := by
    intro hbot
    have hzero : (incidenceMatrix (R := ℚ) ι).col j = 0 := by
      rw [hbot] at hcolmem
      exact hcolmem
    exact hj (congrFun hzero i)
  rw [incidenceRank, rationalColumnRank]
  exact Nat.pos_of_ne_zero fun hz ↦
    hspan (Submodule.finrank_eq_zero.mp hz)

/-- Rank zero contributes no compatible systems once there is at least one
row. -/
lemma consistentRankCount_zero (B : Finset (ZMod p)) (hr : 0 < r)
    (hstable : ∀ ι : Fin r ↪ NonemptyIndexSet k,
      modularIncidenceRank p ι = incidenceRank ι) :
    consistentRankCount p B r k 0 = 0 := by
  rw [consistentRankCount, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rw [mem_compatiblePatternTargetsOfRank] at hx
  have hzero : incidenceRank x.1 = 0 := by
    rw [← hstable x.1]
    exact hx.2
  exact (Nat.ne_of_gt (incidenceRank_pos hr x.1)) hzero

/-- Exact full-rank compatible count.  Full row rank makes every target
assignment consistent, so the count is `|B|^r` times the number of full-rank
incidence patterns. -/
theorem consistentRankCount_full_eq
    (B : Finset (ZMod p))
    (hstable : ∀ ι : Fin r ↪ NonemptyIndexSet k,
      modularIncidenceRank p ι = incidenceRank ι) :
    consistentRankCount p B r k r =
      fullRankPatternCount r k * B.card ^ r := by
  classical
  let ambient : Finset ((Fin r ↪ NonemptyIndexSet k) × (Fin r → TargetIn B)) :=
    (incidenceEmbeddingsOfRank r k r).product Finset.univ
  have heq : compatiblePatternTargetsOfRank p B r k r = ambient := by
    apply Finset.Subset.antisymm
    · intro x hx
      rw [mem_compatiblePatternTargetsOfRank] at hx
      change x ∈ (incidenceEmbeddingsOfRank r k r).product Finset.univ
      apply Finset.mem_product.mpr
      exact ⟨mem_incidenceEmbeddingsOfRank.mpr ((hstable x.1).symm.trans hx.2),
        Finset.mem_univ _⟩
    · intro x hx
      change x ∈ (incidenceEmbeddingsOfRank r k r).product Finset.univ at hx
      have hrank : incidenceRank x.1 = r :=
        mem_incidenceEmbeddingsOfRank.mp (Finset.mem_product.mp hx).1
      have hmod : modularIncidenceRank p x.1 = r := (hstable x.1).trans hrank
      rw [mem_compatiblePatternTargetsOfRank]
      exact ⟨rhs_mem_range_of_full_row_rank
        (incidenceMatrix (R := ZMod p) x.1) hmod (targetVector x.2), hmod⟩
  rw [consistentRankCount, heq]
  simp [ambient, fullRankPatternCount, ← card_incidenceEmbeddingsOfRank_eq]

/-- Exact normalized rank-stratified factorial moment.  The assumption
`r ≤ k` permits cancellation of `p^(k-d)` uniformly for all displayed
rank strata. -/
theorem factorialMoment_targetSubsetEventCount_eq_rank_strata
    (B : Finset (ZMod p)) (hrk : r ≤ k) :
    FiniteProbability.factorialMoment (targetSubsetEventCount (k := k) B) r =
      ∑ d ∈ Finset.range (r + 1),
        (consistentRankCount p B r k d : ℝ) / (p : ℝ) ^ d := by
  rw [FiniteProbability.factorialMoment, FiniteProbability.expect]
  have hnat := sum_descFactorial_targetSubsetEventCount_eq_rank_strata
    (p := p) (r := r) (k := k) B
  have hcast := congrArg (fun n : ℕ ↦ (n : ℝ)) hnat
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow] at hcast
  rw [hcast]
  simp only [Fintype.card_pi, Fintype.card_fin, ZMod.card,
    Finset.prod_const, Finset.card_univ, Nat.cast_pow, consistentRankCount]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e he
  have her : e ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp he)
  have hek : e ≤ k := her.trans hrk
  have hpR : (p : ℝ) ≠ 0 := by
    exact_mod_cast Nat.Prime.ne_zero (show p.Prime from Fact.out)
  have hpow : (p : ℝ) ^ k = (p : ℝ) ^ (k - e) * (p : ℝ) ^ e := by
    rw [← pow_add, Nat.sub_add_cancel hek]
  rw [hpow]
  field_simp

/-- The precise interface consumed by `MomentBounds`: the normalized moment
is the full-rank term plus the `lowRankContribution` built from the actual
consistent-system counts. -/
theorem factorialMoment_targetSubsetEventCount_eq_full_add_lowRank
    (B : Finset (ZMod p)) (hr : 0 < r) (hrk : r ≤ k)
    (hprime : r.factorial < p) :
    FiniteProbability.factorialMoment (targetSubsetEventCount (k := k) B) r =
      (B.card : ℝ) ^ r * fullRankPatternCount r k / (p : ℝ) ^ r +
        lowRankContribution p r (consistentRankCount p B r k) := by
  let hstable : ∀ ι : Fin r ↪ NonemptyIndexSet k,
      modularIncidenceRank p ι = incidenceRank ι :=
    modularIncidenceRank_eq_incidenceRank_of_factorial_lt hprime
  rw [factorialMoment_targetSubsetEventCount_eq_rank_strata B hrk,
    Finset.sum_range_succ]
  rw [consistentRankCount_full_eq B hstable]
  have hzero := consistentRankCount_zero B hr hstable
  have hrange : Finset.range r = insert 0 (Finset.Ico 1 r) := by
    ext e
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [hrange, Finset.sum_insert, lowRankContribution]
  · rw [hzero]
    simp
    ring
  · simp

/-- The actual count functions satisfy the partition and pointwise count
hypotheses needed by the numerical moment layer. -/
theorem actual_rank_counts_interface
    (B : Finset (ZMod p)) (hprime : r.factorial < p) :
    fullRankPatternCount r k + rankDeficientPatternCount r k =
        (2 ^ k - 1).descFactorial r ∧
      (∀ d ∈ Finset.Ico 1 r,
        consistentRankCount p B r k d ≤
          B.card ^ r * incidencePatternCount r k d) := by
  refine ⟨fullRank_add_rankDeficient_eq_descFactorial r k, ?_⟩
  intro e he
  have hstable : ∀ ι : Fin r ↪ NonemptyIndexSet k,
      modularIncidenceRank p ι = incidenceRank ι :=
    modularIncidenceRank_eq_incidenceRank_of_factorial_lt hprime
  have h := card_compatiblePatternTargetsOfRank_le
    (p := p) (r := r) (k := k) (d := e) B hstable
  simpa [consistentRankCount, incidencePatternCount,
    card_incidenceEmbeddingsOfRank_eq, Nat.mul_comm] using h

/-- Algebraic normalization of the sharp Boolean-cube base. -/
lemma three_mul_two_sub_pow_eq (d k : ℕ) (hd : 2 ≤ d) :
    ((3 : ℝ) * 2 ^ (d - 2)) ^ k =
      ((3 : ℝ) / 4) ^ k * (((2 : ℝ) ^ k) ^ d) := by
  rw [mul_pow, div_pow]
  have h4 : (4 : ℝ) ^ k ≠ 0 := by positivity
  field_simp
  rw [← pow_mul, ← pow_mul]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
  congr 2
  rw [← Nat.add_mul, Nat.sub_add_cancel hd, Nat.mul_comm]

/-- The actual consistent-system count satisfies exactly the pointwise
three-quarters estimate required by `abs_rankStratifiedMoment_sub_leading_le`.
The rank-one case is empty; ranks at least two use `LowRankSharp`. -/
theorem consistentRankCount_le_incidence_moment_envelope
    (B : Finset (ZMod p)) (hprime : r.factorial < p) :
    ∀ d ∈ Finset.Ico 1 r,
      (consistentRankCount p B r k d : ℝ) ≤
        (B.card : ℝ) ^ r * (2 : ℝ) ^ (r * r) *
          ((3 : ℝ) / 4) ^ k * (((2 : ℝ) ^ k) ^ d) := by
  intro e he
  have hed : e < r := (Finset.mem_Ico.mp he).2
  have hstable : ∀ ι : Fin r ↪ NonemptyIndexSet k,
      modularIncidenceRank p ι = incidenceRank ι :=
    modularIncidenceRank_eq_incidenceRank_of_factorial_lt hprime
  have hcount := card_compatiblePatternTargetsOfRank_le
    (p := p) (r := r) (k := k) (d := e) B hstable
  rw [card_incidenceEmbeddingsOfRank_eq] at hcount
  have hcount' : consistentRankCount p B r k e ≤
      B.card ^ r * (orderedDistinctRowLowRankMatrices r e k).card := by
    simpa [consistentRankCount, Nat.mul_comm] using hcount
  have hcountR : (consistentRankCount p B r k e : ℝ) ≤
      (B.card : ℝ) ^ r *
        (orderedDistinctRowLowRankMatrices r e k).card := by
    exact_mod_cast hcount'
  by_cases he2 : 2 ≤ e
  · have hsharp :=
      card_orderedDistinctRowLowRankMatrices_le_sharp r e k hed
    have hsharpR :
        ((orderedDistinctRowLowRankMatrices r e k).card : ℝ) ≤
          (2 : ℝ) ^ (r * r) *
            ((3 : ℝ) * 2 ^ (e - 2)) ^ k := by
      exact_mod_cast hsharp
    calc
      (consistentRankCount p B r k e : ℝ) ≤
          (B.card : ℝ) ^ r *
            (orderedDistinctRowLowRankMatrices r e k).card := hcountR
      _ ≤ (B.card : ℝ) ^ r *
          ((2 : ℝ) ^ (r * r) *
            ((3 : ℝ) * 2 ^ (e - 2)) ^ k) :=
        mul_le_mul_of_nonneg_left hsharpR (by positivity)
      _ = (B.card : ℝ) ^ r * (2 : ℝ) ^ (r * r) *
          ((3 : ℝ) / 4) ^ k * (((2 : ℝ) ^ k) ^ e) := by
        rw [three_mul_two_sub_pow_eq e k he2]
        ring
  · have he1 : e = 1 := by
      have := (Finset.mem_Ico.mp he).1
      omega
    subst e
    have hgen := sharpGenerators_eq_empty_of_lt_two r 1 hed (by omega)
    have hcol : sharpColumnFamilies r 1 k = ∅ := by
      simp [sharpColumnFamilies, hgen]
    have hmat : sharpLowRankMatrices r 1 k = ∅ := by
      simp [sharpLowRankMatrices, hcol]
    have hpattern :
        (orderedDistinctRowLowRankMatrices r 1 k).card = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro M hM
      have hs := orderedDistinctRowLowRankMatrices_subset_sharp r 1 k hM
      rw [hmat] at hs
      exact Finset.notMem_empty M hs
    rw [hpattern] at hcountR
    simp only [Nat.cast_zero, mul_zero] at hcountR
    exact hcountR.trans (by positivity)

/-- Fully instantiated finite factorial-moment estimate for the actual
subset-target event family.  This is the bridge from the exact stratification
in this file to the numerical estimate in `MomentBounds.lean`. -/
theorem abs_factorialMoment_targetSubsetEventCount_sub_leading_le
    (B : Finset (ZMod p)) (hB : B.Nonempty) (hk : 0 < k)
    (hr : 0 < r) (hrk : r ≤ k) (hrM : r ≤ 2 ^ k - 1)
    (hprime : r.factorial < p) :
    |FiniteProbability.factorialMoment
        (targetSubsetEventCount (k := k) B) r -
        (((B.card : ℝ) * (2 ^ k - 1 : ℕ) / p) ^ r)| ≤
      ((r : ℝ) ^ 2 / (2 ^ k - 1 : ℕ) +
          (rankDeficientPatternCount r k : ℝ) /
            ((2 ^ k - 1 : ℕ) : ℝ) ^ r +
          incidenceLowRankEnvelope p k r B.card /
            (((B.card : ℝ) * (2 ^ k - 1 : ℕ) / p) ^ r)) *
        (((B.card : ℝ) * (2 ^ k - 1 : ℕ) / p) ^ r) := by
  have hp : 0 < p := (show p.Prime from Fact.out).pos
  have hm : 0 < B.card := Finset.card_pos.mpr hB
  have hpow : 1 < 2 ^ k := Nat.one_lt_pow hk.ne' (by omega)
  have hM : 0 < 2 ^ k - 1 := Nat.sub_pos_of_lt hpow
  have hpartition := fullRank_add_rankDeficient_eq_descFactorial r k
  have hC := consistentRankCount_le_incidence_moment_envelope
    (p := p) (r := r) (k := k) B hprime
  have hbound := abs_rankStratifiedMoment_sub_leading_le
    (p := p) (k := k) (m := B.card) (M := 2 ^ k - 1)
    (r := r) (F := fullRankPatternCount r k)
    (L := rankDeficientPatternCount r k)
    (C := consistentRankCount p B r k)
    hp hm hM hr hrM hpartition hC
  have hmoment := factorialMoment_targetSubsetEventCount_eq_full_add_lowRank
    (p := p) (r := r) (k := k) B hr hrk hprime
  rw [← hmoment] at hbound
  simpa using hbound

/-- There are no positive-row incidence patterns of rational rank zero. -/
lemma incidencePatternCount_zero (hr : 0 < r) :
    incidencePatternCount r k 0 = 0 := by
  rw [incidencePatternCount_eq, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ι hι
  rw [mem_incidenceEmbeddingsOfRank] at hι
  exact (Nat.ne_of_gt (incidenceRank_pos hr ι)) hι

/-- The rank-deficient count is the `lowerRankPatternCount` expected by the
explicit numerical lemma. -/
lemma rankDeficientPatternCount_eq_lowerRankPatternCount (hr : 0 < r) :
    rankDeficientPatternCount r k =
      lowerRankPatternCount r (incidencePatternCount r k) := by
  rw [rankDeficientPatternCount, lowerRankPatternCount]
  simp_rw [← card_incidenceEmbeddingsOfRank_eq, ← incidencePatternCount_eq]
  have hrange : Finset.range r = insert 0 (Finset.Ico 1 r) := by
    ext e
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [hrange, Finset.sum_insert]
  · rw [incidencePatternCount_zero hr, zero_add]
  · simp

/-- The actual rational-rank pattern counts satisfy the coarse pointwise
majorant used for the full-rank deficit. -/
theorem incidencePatternCount_le_trivial_envelope :
    ∀ d ∈ Finset.Ico 1 r,
      incidencePatternCount r k d ≤
        2 ^ (r * r) * (2 ^ k) ^ d := by
  intro e he
  have hed : e < r := (Finset.mem_Ico.mp he).2
  by_cases he2 : 2 ≤ e
  · have hsharp :=
      card_orderedDistinctRowLowRankMatrices_le_sharp r e k hed
    rw [incidencePatternCount]
    refine hsharp.trans ?_
    apply Nat.mul_le_mul_left
    have hbase : 3 * 2 ^ (e - 2) ≤ 2 ^ e := by
      calc
      3 * 2 ^ (e - 2) ≤ 4 * 2 ^ (e - 2) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 2 ^ e := by
        rw [show e = (e - 2) + 2 by omega, pow_add]
        norm_num [Nat.mul_comm]
    calc
      (3 * 2 ^ (e - 2)) ^ k ≤ (2 ^ e) ^ k :=
        Nat.pow_le_pow_left hbase k
      _ = (2 ^ k) ^ e := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  · have he1 : e = 1 := by
      have := (Finset.mem_Ico.mp he).1
      omega
    subst e
    have hgen := sharpGenerators_eq_empty_of_lt_two r 1 hed (by omega)
    have hcol : sharpColumnFamilies r 1 k = ∅ := by
      simp [sharpColumnFamilies, hgen]
    have hmat : sharpLowRankMatrices r 1 k = ∅ := by
      simp [sharpLowRankMatrices, hcol]
    have hpattern : incidencePatternCount r k 1 = 0 := by
      rw [incidencePatternCount, Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro M hM
      have hs := orderedDistinctRowLowRankMatrices_subset_sharp r 1 k hM
      rw [hmat] at hs
      exact Finset.notMem_empty M hs
    rw [hpattern]
    exact Nat.zero_le _

/-- Explicit version of the preceding finite estimate.  Its error coefficient
is exactly the one used by `RankCountAsymptotics` (the actual deficient count
has been replaced by its closed-form majorant). -/
theorem abs_factorialMoment_targetSubsetEventCount_sub_leading_le_explicit
    (B : Finset (ZMod p)) (hB : B.Nonempty) (hk : 0 < k)
    (hr : 0 < r) (hrk : r ≤ k) (hrM : r ≤ 2 ^ k - 1)
    (hprime : r.factorial < p) :
    |FiniteProbability.factorialMoment
        (targetSubsetEventCount (k := k) B) r -
        (((B.card : ℝ) * (2 ^ k - 1 : ℕ) / p) ^ r)| ≤
      ((r : ℝ) ^ 2 / (2 ^ k - 1 : ℕ) +
          ((r * 2 ^ (r * r) * (2 ^ k) ^ (r - 1) : ℕ) : ℝ) /
            ((2 ^ k - 1 : ℕ) : ℝ) ^ r +
          incidenceLowRankEnvelope p k r B.card /
            (((B.card : ℝ) * (2 ^ k - 1 : ℕ) / p) ^ r)) *
        (((B.card : ℝ) * (2 ^ k - 1 : ℕ) / p) ^ r) := by
  have hp : 0 < p := (show p.Prime from Fact.out).pos
  have hm : 0 < B.card := Finset.card_pos.mpr hB
  have hpow : 1 < 2 ^ k := Nat.one_lt_pow hk.ne' (by omega)
  have hM : 0 < 2 ^ k - 1 := Nat.sub_pos_of_lt hpow
  have hpartition := fullRank_add_rankDeficient_eq_descFactorial r k
  have hL := rankDeficientPatternCount_eq_lowerRankPatternCount
    (r := r) (k := k) hr
  have hT := incidencePatternCount_le_trivial_envelope
    (r := r) (k := k)
  have hC := consistentRankCount_le_incidence_moment_envelope
    (p := p) (r := r) (k := k) B hprime
  have hbound := abs_rankStratifiedMoment_sub_leading_le_explicit
    (p := p) (k := k) (m := B.card) (M := 2 ^ k - 1)
    (r := r) (F := fullRankPatternCount r k)
    (L := rankDeficientPatternCount r k)
    (C := consistentRankCount p B r k) (T := incidencePatternCount r k)
    hp hm hM hr hrM hpartition hL hT hC
  have hmoment := factorialMoment_targetSubsetEventCount_eq_full_add_lowRank
    (p := p) (r := r) (k := k) B hr hrk hprime
  rw [← hmoment] at hbound
  simpa using hbound

end

end Erdos543
