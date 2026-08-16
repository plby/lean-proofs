import ErdosProblems.Erdos920.ProjectiveContainer
import ErdosProblems.Erdos920.TupleBound
import ErdosProblems.Erdos920.Pivot

/-!
# The concrete poor/popular marking for the projective container

This file supplies the rounding-safe marking used in the proof of the
forward-independent tuple bound.  The pivot rank is chosen by maximizing an
exact-rank stratum below the rank of the prospective second coordinate.
All inequalities are cleared of denominators.
-/

open scoped BigOperators LinearAlgebra.Projectivization

namespace Erdos920.MarkedChildren

noncomputable section

open Erdos920.Projective
open Erdos920.ProjectiveContainer
open Erdos920.Container
open Erdos920.Pivot

section Pivot

variable {P : Type*} [Fintype P] [DecidableEq P]

theorem mem_Z_rank (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R]
    (sigma : List (P × P)) {b : P} (hb : b ∈ points) :
    b ∈ Z points C R sigma (prefixRank C R sigma b) := by
  simp [Z, hb]

theorem pivot_Z_nonempty_of_mem (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R]
    (sigma : List (P × P)) {b : P} (hb : b ∈ points) :
    (Z points C R sigma
      (pivotLevel points C R sigma (prefixRank C R sigma b))).Nonempty := by
  have hcard : 1 ≤ (Z points C R sigma (prefixRank C R sigma b)).card :=
    Finset.one_le_card.mpr ⟨b, mem_Z_rank points C R sigma hb⟩
  have hp := Z_card_le_pivot points C R sigma (le_refl (prefixRank C R sigma b))
  exact Finset.card_pos.mp (lt_of_lt_of_le (by omega) (hcard.trans hp))

end Pivot

section ClearedThresholds

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- Cleared-denominator version of the paper's poor-point predicate. -/
def PoorQ (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (q : ℕ) (sigma : List (P × P)) (l : ℕ) (a : P) : Prop :=
  8 * q * (neighborsInStratum points C R sigma l a).card ≤
    (Z points C R sigma l).card

/-- Cleared-denominator version of the paper's popular-point predicate. -/
def PopularQ (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (q : ℕ) (sigma : List (P × P)) (l : ℕ) (b : P) : Prop :=
  (Z points C R sigma l).card ≤
    16 * q * (closureInStratum points C R sigma l b).card

/-- Points outside both exceptional classes raise rank on a positive
fraction of the pivot stratum. -/
theorem pivot_card_lt_mul_rankRaising_of_not_poorQ_not_popularQ
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (q : ℕ) (sigma : List (P × P)) (l : ℕ) (a b : P)
    (ha : ¬ PoorQ points C R q sigma l a)
    (hb : ¬ PopularQ points C R q sigma l b) :
    (Z points C R sigma l).card <
      16 * q * (rankRaisingSet points C R sigma l a b).card := by
  classical
  let Z0 := Z points C R sigma l
  let A := Z0.filter fun y => R a y
  let B := Z0.filter fun y => C.Cl b (generators R sigma y)
  let E := Z0.filter fun y => R a y ∧ ¬ C.Cl b (generators R sigma y)
  have hpoor : Z0.card < 8 * q * A.card := Nat.lt_of_not_ge ha
  have hpopular : 16 * q * B.card < Z0.card := Nat.lt_of_not_ge hb
  have hE : E = A \ B := by
    ext y
    simp only [E, A, B, Finset.mem_filter, Finset.mem_sdiff]
    aesop
  have hinter : (A ∩ B).card ≤ B.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hsplit := Finset.card_sdiff_add_card_inter A B
  rw [← hE] at hsplit
  have hmulE : 16 * q * E.card + 16 * q * (A ∩ B).card =
      2 * (8 * q * A.card) := by
    calc
      16 * q * E.card + 16 * q * (A ∩ B).card =
          16 * q * (E.card + (A ∩ B).card) := by ring
      _ = 16 * q * A.card := by rw [hsplit]
      _ = 2 * (8 * q * A.card) := by ring
  have hB : 16 * q * (A ∩ B).card < Z0.card :=
    (Nat.mul_le_mul_left (16 * q) hinter).trans_lt hpopular
  have htwice : 2 * Z0.card <
      16 * q * E.card + 16 * q * (A ∩ B).card := by
    rw [hmulE]
    omega
  have hz : Z0.card < 16 * q * E.card := by omega
  simpa [Z0, E, rankRaisingSet] using hz

/-- Cleared multiplicative shrinkage at a pivot. -/
theorem U_card_shrink_of_not_poorQ_not_popularQ
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (q t : ℕ) (sigma : List (P × P)) (l : ℕ) (a b : P)
    (hU : (U points C R sigma l).card ≤
      2 * t * (Z points C R sigma l).card)
    (ha : ¬ PoorQ points C R q sigma l a)
    (hb : ¬ PopularQ points C R q sigma l b) :
    (32 * t * q) * (U points C R ((a, b) :: sigma) l).card ≤
      (32 * t * q - 1) * (U points C R sigma l).card := by
  have hrank := pivot_card_lt_mul_rankRaising_of_not_poorQ_not_popularQ
    points C R q sigma l a b ha hb
  have hmono := U_mono_cons points C R (a, b) sigma l
  have hraise := rankRaisingSet_subset_U_diff points C R sigma l a b
  have hdisj : Disjoint (U points C R ((a, b) :: sigma) l)
      (rankRaisingSet points C R sigma l a b) := by
    apply Finset.disjoint_left.mpr
    intro y hyNew hyRaise
    exact (Finset.mem_sdiff.mp (hraise hyRaise)).2 hyNew
  have hunion : U points C R ((a, b) :: sigma) l ∪
      rankRaisingSet points C R sigma l a b ⊆ U points C R sigma l := by
    intro y hy
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hmono hy
    · exact (Finset.mem_sdiff.mp (hraise hy)).1
  have hadd : (U points C R ((a, b) :: sigma) l).card +
      (rankRaisingSet points C R sigma l a b).card ≤
        (U points C R sigma l).card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hunion
  have hcut : (U points C R sigma l).card ≤
      (32 * t * q) * (rankRaisingSet points C R sigma l a b).card := by
    calc
      (U points C R sigma l).card ≤
          2 * t * (Z points C R sigma l).card := hU
      _ ≤ 2 * t * (16 * q *
          (rankRaisingSet points C R sigma l a b).card) :=
        Nat.mul_le_mul_left (2 * t) hrank.le
      _ = (32 * t * q) *
          (rankRaisingSet points C R sigma l a b).card := by ring
  let K := 32 * t * q
  by_cases hK : K = 0
  · simp [K, hK]
  · have hKpos : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr hK
    have hmuladd : K * (U points C R ((a, b) :: sigma) l).card +
          K * (rankRaisingSet points C R sigma l a b).card ≤
        K * (U points C R sigma l).card := by
      simpa [mul_add] using Nat.mul_le_mul_left K hadd
    have hwithU : K * (U points C R ((a, b) :: sigma) l).card +
          (U points C R sigma l).card ≤
        K * (U points C R sigma l).card :=
      (Nat.add_le_add_left hcut _).trans hmuladd
    have hrhs : (K - 1) * (U points C R sigma l).card +
          (U points C R sigma l).card = K * (U points C R sigma l).card := by
      calc
        (K - 1) * (U points C R sigma l).card +
              (U points C R sigma l).card =
            (K - 1) * (U points C R sigma l).card +
              1 * (U points C R sigma l).card := by simp
        _ = ((K - 1) + 1) * (U points C R sigma l).card := by rw [add_mul]
        _ = K * (U points C R sigma l).card := by rw [Nat.sub_add_cancel hKpos]
    apply Nat.le_of_add_le_add_right
    rw [hrhs]
    exact hwithU

end ClearedThresholds

section Marking

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The pivot selected for the rank of a prospective second coordinate. -/
def chosenPivot (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R]
    (sigma : List (P × P)) (p : P × P) : ℕ :=
  pivotLevel points C R sigma (prefixRank C R sigma p.2)

/-- A small pivot is marked wholesale.  This removes all zero and tiny
strata from later cancellations. -/
def SmallPivotQ (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R] (q : ℕ)
    (sigma : List (P × P)) (p : P × P) : Prop :=
  (Z points C R sigma (chosenPivot points C R sigma p)).card < 16 * q

/-- The Boolean poor/popular marking used by the marked tree.  No separate
small-stratum exception is needed: the cleared predicates remain valid for
every nonempty pivot, while an empty pivot makes every first coordinate
poor automatically. -/
def marked (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R] (q : ℕ)
    (sigma : List (P × P)) (p : P × P) : Bool :=
  by
    classical
    exact decide
      (PoorQ points C R q sigma (chosenPivot points C R sigma p) p.1 ∨
       PopularQ points C R q sigma (chosenPivot points C R sigma p) p.2)

theorem marked_eq_false_iff (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R] (q : ℕ)
    (sigma : List (P × P)) (p : P × P) :
    marked points C R q sigma p = false ↔
      ¬ PoorQ points C R q sigma (chosenPivot points C R sigma p) p.1 ∧
      ¬ PopularQ points C R q sigma (chosenPivot points C R sigma p) p.2 := by
  classical
  simp [marked, not_or]

/-- The selected pivot, clipped only to package it in the fixed finite type
of all ambient rank levels.  Under the natural rank cap the clipping is
inactive. -/
def levelIndex (T : ℕ) (points : Finset P) (C : RankClosure P)
    (R : P → P → Prop) [DecidableRel R]
    (sigma : List (P × P)) (p : P × P) : Fin (T + 1) :=
  ⟨min (chosenPivot points C R sigma p) T, by omega⟩

theorem levelIndex_val_of_rank_le (T : ℕ) (points : Finset P)
    (C : RankClosure P) (R : P → P → Prop) [DecidableRel R]
    (sigma : List (P × P)) (p : P × P)
    (hrank : prefixRank C R sigma p.2 ≤ T) :
    (levelIndex T points C R sigma p : ℕ) =
      chosenPivot points C R sigma p := by
  change min (chosenPivot points C R sigma p) T =
    chosenPivot points C R sigma p
  exact Nat.min_eq_left ((pivotLevel_le points C R sigma _).trans hrank)

/-- The selected pivot controls its own monotone `U`-potential with any
uniform upper bound for `j+1`. -/
theorem chosen_U_card_le
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (T : ℕ) (sigma : List (P × P)) (p : P × P)
    (hrank : prefixRank C R sigma p.2 + 1 ≤ T) :
    (U points C R sigma (chosenPivot points C R sigma p)).card ≤
      T * (Z points C R sigma (chosenPivot points C R sigma p)).card := by
  have hU0 := U_card_le_succ_mul_Z_pivot points C R sigma
    (prefixRank C R sigma p.2)
  have hmonoU : U points C R sigma (chosenPivot points C R sigma p) ⊆
      U points C R sigma (prefixRank C R sigma p.2) := by
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hy'.1,
      hy'.2.trans (pivotLevel_le points C R sigma _)⟩
  calc
    (U points C R sigma (chosenPivot points C R sigma p)).card ≤
        (U points C R sigma (prefixRank C R sigma p.2)).card :=
      Finset.card_le_card hmonoU
    _ ≤ (prefixRank C R sigma p.2 + 1) *
        (Z points C R sigma (chosenPivot points C R sigma p)).card := hU0
    _ ≤ T * (Z points C R sigma (chosenPivot points C R sigma p)).card :=
      Nat.mul_le_mul_right _ hrank

/-- Direct cleared-threshold shrinkage, independent of any particular
Boolean marking. -/
theorem chosen_U_shrink_of_not_poorQ_not_popularQ
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (q t : ℕ) (sigma : List (P × P)) (p : P × P)
    (hrank : prefixRank C R sigma p.2 + 1 ≤ 2 * t)
    (hpoor : ¬ PoorQ points C R q sigma
      (chosenPivot points C R sigma p) p.1)
    (hpopular : ¬ PopularQ points C R q sigma
      (chosenPivot points C R sigma p) p.2) :
    (32 * t * q) *
        (U points C R (p :: sigma) (chosenPivot points C R sigma p)).card ≤
      (32 * t * q - 1) *
        (U points C R sigma (chosenPivot points C R sigma p)).card := by
  exact U_card_shrink_of_not_poorQ_not_popularQ points C R q t sigma
    (chosenPivot points C R sigma p) p.1 p.2
    (chosen_U_card_le points C R (2 * t) sigma p hrank) hpoor hpopular

/-- An unmarked extension contracts its chosen `U`-potential.  The
hypothesis `j+1 ≤ 2t` is the only rank-range input. -/
theorem chosen_U_shrink_of_unmarked
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (q t : ℕ) (sigma : List (P × P)) (p : P × P)
    (hrank : prefixRank C R sigma p.2 + 1 ≤ 2 * t)
    (hunmarked : marked points C R q sigma p = false) :
    (32 * t * q) *
        (U points C R (p :: sigma) (chosenPivot points C R sigma p)).card ≤
    (32 * t * q - 1) *
        (U points C R sigma (chosenPivot points C R sigma p)).card := by
  have hfalse := (marked_eq_false_iff points C R q sigma p).mp hunmarked
  exact chosen_U_shrink_of_not_poorQ_not_popularQ points C R q t sigma p
    hrank hfalse.1 hfalse.2

/-- A child whose second coordinate belongs to `points` has a nonempty
chosen potential before it is added. -/
theorem chosen_U_positive_of_second_mem
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (sigma : List (P × P)) (p : P × P)
    (hb : p.2 ∈ points) :
    1 ≤ (U points C R sigma (chosenPivot points C R sigma p)).card := by
  have hpivot := pivot_Z_nonempty_of_mem points C R sigma hb
  apply Finset.one_le_card.mpr
  obtain ⟨y, hy⟩ := hpivot
  refine ⟨y, ?_⟩
  exact Z_subset_U points C R sigma _ hy

end Marking

section ProjectiveCertificate

open Erdos920.TupleBound

attribute [local instance] Classical.propDecidable Classical.decEq

variable {q t : ℕ} [Fact q.Prime]

abbrev PointT (q t : ℕ) [Fact q.Prime] :=
  Projective.Point (ZMod q) (t + 1)

local instance pointFintype (q t : ℕ) [Fact q.Prime] :
    Fintype (PointT q t) := Fintype.ofFinite _

local instance orthogonalDecidable (q t : ℕ) [Fact q.Prime] :
    DecidableRel
      (@Projective.Orthogonal (ZMod q) _ (t + 1)) := Classical.decRel _

/-- All incident projective pairs. -/
def projectiveVertices (q t : ℕ) [Fact q.Prime] : Finset (PointT q t × PointT q t) :=
  ProjectiveContainer.incidentPairs q t

/-- Compatible children for the concrete projective container. -/
def projectiveChildren (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t)) : Finset (PointT q t × PointT q t) :=
  consistentChildren (projectiveVertices q t) Projective.Orthogonal sigma

theorem projectiveChildren_eq_extensionChildren (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t)) :
    projectiveChildren q t sigma =
      extensionChildren (Finset.univ : Finset (PointT q t))
        Projective.Orthogonal sigma := by
  ext p
  simp [projectiveChildren, projectiveVertices, consistentChildren,
    extensionChildren]

/-- The concrete poor/popular marking. -/
def projectiveMarked (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t)) (p : PointT q t × PointT q t) : Bool :=
  marked (Finset.univ : Finset (PointT q t))
    (projectiveRankClosure q t) Projective.Orthogonal q sigma p

/-- The pivot level as an element of the fixed ambient set of ranks
`0, ..., t+1`. -/
def projectiveLevel (q t : ℕ) [Fact q.Prime]
    (sigma : List (PointT q t × PointT q t))
    (p : PointT q t × PointT q t) : Fin (t + 2) :=
  levelIndex (t + 1) (Finset.univ : Finset (PointT q t))
    (projectiveRankClosure q t) Projective.Orthogonal sigma p

/-- Rank of every selected generator span is at most the ambient vector
dimension. -/
theorem projective_prefixRank_le (sigma : List (PointT q t × PointT q t))
    (b : PointT q t) :
    prefixRank (projectiveRankClosure q t) Projective.Orthogonal sigma b ≤ t + 1 := by
  exact projectiveRankClosure_rank_le_dim
    (generators Projective.Orthogonal sigma b)

theorem projectiveLevel_val (sigma : List (PointT q t × PointT q t))
    (p : PointT q t × PointT q t) :
    (projectiveLevel q t sigma p : ℕ) =
      chosenPivot (Finset.univ : Finset (PointT q t))
        (projectiveRankClosure q t) Projective.Orthogonal sigma p := by
  exact levelIndex_val_of_rank_le (t + 1)
    (Finset.univ : Finset (PointT q t)) (projectiveRankClosure q t)
    Projective.Orthogonal sigma p (projective_prefixRank_le sigma p.2)

/-- The concrete projective potentials and the unmarked-step contraction,
packaged for `Container.unmarkedCount_le_of_certificate`. -/
def projectiveShrinkCertificate (q t : ℕ) [Fact q.Prime] (ht : 2 ≤ t) :
    PathShrinkCertificate (L := Fin (t + 2))
      (projectiveChildren q t) (projectiveMarked q t)
      (32 * t * q) (Fintype.card (PointT q t)) where
  potential l sigma :=
    (U (Finset.univ : Finset (PointT q t)) (projectiveRankClosure q t)
      Projective.Orthogonal sigma l.1).card
  level := projectiveLevel q t
  initial_le l := by
    exact Finset.card_le_card (Finset.filter_subset _ _)
  mono l sigma p hp := by
    exact Finset.card_le_card
      (U_mono_cons (Finset.univ : Finset (PointT q t))
        (projectiveRankClosure q t) Projective.Orthogonal p sigma l.1)
  positive sigma p hp hunmarked := by
    rw [projectiveLevel_val sigma p]
    exact chosen_U_positive_of_second_mem
      (Finset.univ : Finset (PointT q t)) (projectiveRankClosure q t)
      Projective.Orthogonal sigma p (Finset.mem_univ _)
  contract sigma p hp hunmarked := by
    have hrank : prefixRank (projectiveRankClosure q t)
        Projective.Orthogonal sigma p.2 + 1 ≤ 2 * t := by
      have hcap := projective_prefixRank_le sigma p.2
      omega
    rw [projectiveLevel_val sigma p]
    exact chosen_U_shrink_of_unmarked
      (Finset.univ : Finset (PointT q t)) (projectiveRankClosure q t)
      Projective.Orthogonal q t sigma p hrank hunmarked

end ProjectiveCertificate

end

end Erdos920.MarkedChildren
