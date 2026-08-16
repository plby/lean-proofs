import ErdosProblems.Erdos920.MarkedChildren
import ErdosProblems.Erdos920.SpanCounts

/-!
# Popular children in the projective container

This file proves the concrete popular-child estimate in Bradač's
projective container.  The popularity predicate has cleared denominators,
so all counting takes place in `ℕ`.
-/

open scoped BigOperators LinearAlgebra.Projectivization

namespace Erdos920.PopularChildren

noncomputable section

open Erdos920.Projective
open Erdos920.ProjectiveContainer
open Erdos920.Container
open Erdos920.MarkedChildren
open Erdos920.Pivot

attribute [local instance] Classical.propDecidable Classical.decEq

section ClearedDoubleCount

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- A double-counting estimate for the cleared popularity predicate.
If the pivot stratum is nonempty and every span occurring over it contains
at most `cap` points, then there are at most `16*q*cap` popular points. -/
theorem popularQ_card_le_of_fibre
    (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
    [DecidableRel R] (q : ℕ) (sigma : List (P × P)) (l cap : ℕ)
    (hz : 0 < (Z points C R sigma l).card)
    (hfibre : ∀ y ∈ Z points C R sigma l,
      (points.filter fun b ↦ C.Cl b (generators R sigma y)).card ≤ cap) :
    (points.filter fun b ↦ PopularQ points C R q sigma l b).card ≤
      16 * q * cap := by
  classical
  let Z0 := Z points C R sigma l
  let pop := points.filter fun b ↦ PopularQ points C R q sigma l b
  have hleft : pop.card * Z0.card ≤
      16 * q * ∑ b ∈ pop,
        (Z0.filter fun y ↦ C.Cl b (generators R sigma y)).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_mul]
    calc
      ∑ _b ∈ pop, 1 * Z0.card = ∑ _b ∈ pop, Z0.card := by simp
      _ ≤ ∑ b ∈ pop,
          16 * q * (Z0.filter fun y ↦ C.Cl b (generators R sigma y)).card := by
        apply Finset.sum_le_sum
        intro b hb
        exact (Finset.mem_filter.mp hb).2
      _ = 16 * q * ∑ b ∈ pop,
          (Z0.filter fun y ↦ C.Cl b (generators R sigma y)).card := by
        rw [Finset.mul_sum]
  have hsub :
      ∑ b ∈ pop, (Z0.filter fun y ↦ C.Cl b (generators R sigma y)).card ≤
        ∑ b ∈ points,
          (Z0.filter fun y ↦ C.Cl b (generators R sigma y)).card := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro b hb
      exact (Finset.mem_filter.mp hb).1
    · intro i hi _
      exact Nat.zero_le _
  have hswap :
      ∑ b ∈ points,
          (Z0.filter fun y ↦ C.Cl b (generators R sigma y)).card =
        ∑ y ∈ Z0,
          (points.filter fun b ↦ C.Cl b (generators R sigma y)).card := by
    exact sum_card_filter_eq_sum_card_filter points Z0
      (fun b y ↦ C.Cl b (generators R sigma y))
  have hright :
      ∑ y ∈ Z0,
          (points.filter fun b ↦ C.Cl b (generators R sigma y)).card ≤
        Z0.card * cap := by
    rw [Finset.card_eq_sum_ones, Finset.sum_mul]
    exact Finset.sum_le_sum fun y hy ↦ by
      simpa [Z0] using hfibre y hy
  have hmul : pop.card * Z0.card ≤ (16 * q * cap) * Z0.card := by
    calc
      pop.card * Z0.card ≤
          16 * q * ∑ b ∈ pop,
            (Z0.filter fun y ↦ C.Cl b (generators R sigma y)).card := hleft
      _ ≤ 16 * q * ∑ b ∈ points,
            (Z0.filter fun y ↦ C.Cl b (generators R sigma y)).card :=
        Nat.mul_le_mul_left (16 * q) hsub
      _ = 16 * q * ∑ y ∈ Z0,
            (points.filter fun b ↦ C.Cl b (generators R sigma y)).card := by
        rw [hswap]
      _ ≤ 16 * q * (Z0.card * cap) := Nat.mul_le_mul_left (16 * q) hright
      _ = (16 * q * cap) * Z0.card := by ring
  exact Nat.le_of_mul_le_mul_right hmul hz

end ClearedDoubleCount

section ProjectiveChildren

variable (q t : ℕ) [Fact q.Prime]

abbrev P := Projective.Point (ZMod q) (t + 1)

local instance pointFintype : Fintype (P q t) := Fintype.ofFinite _
local instance orthogonalDecidable :
    DecidableRel (@Orthogonal (ZMod q) _ (t + 1)) := Classical.decRel _

/-- Rank of the old generator span selected by the prospective second
coordinate of a child. -/
def childRank (sigma : List (P q t × P q t)) (p : P q t × P q t) : ℕ :=
  prefixRank (projectiveRankClosure q t) Orthogonal sigma p.2

/-- The maximum-cardinality stratum chosen below a prescribed child rank. -/
def pivotForRank (sigma : List (P q t × P q t)) (j : ℕ) : ℕ :=
  pivotLevel (Finset.univ : Finset (P q t))
    (projectiveRankClosure q t) Orthogonal sigma j

/-- Popular second coordinates having a prescribed old span rank. -/
def popularSecondsAtRank (sigma : List (P q t × P q t)) (j : ℕ) :
    Finset (P q t) :=
  Finset.univ.filter fun b ↦
    prefixRank (projectiveRankClosure q t) Orthogonal sigma b = j ∧
      PopularQ (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
        Orthogonal q sigma (pivotForRank q t sigma j) b

/-- Consistent incident children which are popular and have prescribed
second-coordinate rank. -/
def popularChildrenAtRank (sigma : List (P q t × P q t)) (j : ℕ) :
    Finset (P q t × P q t) :=
  (TupleBound.consistentChildren (incidentPairs q t) Orthogonal sigma).filter fun p ↦
    childRank q t sigma p = j ∧
      PopularQ (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
        Orthogonal q sigma (pivotForRank q t sigma j) p.2

/-- The first coordinates compatible with the old generators selected by
`b`.  The incidence `a ⊥ b` is intentionally omitted: dropping it only
enlarges the fibre. -/
def compatibleFirsts (sigma : List (P q t × P q t)) (b : P q t) :
    Finset (P q t) :=
  Finset.univ.filter fun a ↦
    ∀ y ∈ generators Orthogonal sigma b, Orthogonal y a

/-- Container compatibility makes the first coordinate orthogonal to every
old generator selected by the second coordinate. -/
theorem orthogonal_generators_of_canExtend
    (sigma : List (P q t × P q t)) (a b : P q t)
    (h : CanExtend Orthogonal (a, b) sigma) :
    ∀ y ∈ generators Orthogonal sigma b, Orthogonal y a := by
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨old, hold, rfl⟩
  have hold' := Finset.mem_filter.mp hold
  have hoa : Orthogonal a old.2 :=
    h.2 old (List.mem_toFinset.mp hold'.1) hold'.2
  exact (orthogonal_comm a old.2).mp hoa

/-- A fixed-rank compatible first-coordinate fibre has the projective
orthogonal-complement bound used in the paper. -/
theorem compatibleFirsts_card_le
    (sigma : List (P q t × P q t)) (b : P q t) (j : ℕ)
    (hrank : prefixRank (projectiveRankClosure q t) Orthogonal sigma b = j) :
    (compatibleFirsts q t sigma b).card ≤ 2 * q ^ (t - j) := by
  have hrank' :
      (rankClosure (F := ZMod q) (d := t + 1)).rank
          (generators Orthogonal sigma b) = j := by
    simpa [prefixRank, projectiveRankClosure] using hrank
  simpa [compatibleFirsts] using
    (Erdos920.SpanCounts.card_filter_orthogonal_to_rankClosure_le_two_mul_pow
      (S := generators Orthogonal sigma b) hrank')

/-- Every actual consistent child has old generator rank at most `t`.
Indeed its first coordinate is a projective point in the orthogonal
complement of that generator span. -/
theorem childRank_le_t_of_mem_children
    (sigma : List (P q t × P q t)) (p : P q t × P q t)
    (hp : p ∈ TupleBound.consistentChildren (incidentPairs q t)
      Orthogonal sigma) :
    childRank q t sigma p ≤ t := by
  have hmem := (TupleBound.mem_consistentChildren_iff
    (incidentPairs q t) Orthogonal p sigma).mp hp
  have horth : ∀ y ∈ generators Orthogonal sigma p.2,
      Orthogonal y p.1 :=
    orthogonal_generators_of_canExtend q t sigma p.1 p.2 hmem.2
  have hpfirst : p.1 ∈ compatibleFirsts q t sigma p.2 := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, horth⟩
  let j := childRank q t sigma p
  have hjdim : j ≤ t + 1 := by
    exact (projectiveRankClosure_rank_le_dim
      (q := q) (t := t) (generators Orthogonal sigma p.2))
  by_contra hj
  have hjeq : j = t + 1 := by omega
  have hrank : Module.finrank (ZMod q)
      (pointSpan (generators Orthogonal sigma p.2)) = t + 1 := by
    simpa [j, childRank, prefixRank, projectiveRankClosure] using hjeq
  have hzero : (compatibleFirsts q t sigma p.2).card = 0 := by
    have hexact :=
      Erdos920.SpanCounts.card_filter_orthogonal_to_span_eq_geomSum
        (S := generators Orthogonal sigma p.2)
    rw [hrank] at hexact
    simpa [compatibleFirsts] using hexact
  have hpos : 0 < (compatibleFirsts q t sigma p.2).card :=
    Finset.card_pos.mpr ⟨p.1, hpfirst⟩
  omega

/-- Nonemptiness of a fixed-rank popular child class forces the selected
pivot stratum to be nonempty. -/
theorem pivot_nonempty_of_popularChildrenAtRank_nonempty
    (sigma : List (P q t × P q t)) (j : ℕ)
    (hne : (popularChildrenAtRank q t sigma j).Nonempty) :
    (Z (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
      Orthogonal sigma (pivotForRank q t sigma j)).Nonempty := by
  obtain ⟨p, hp⟩ := hne
  have hp' := Finset.mem_filter.mp hp
  have hrank : prefixRank (projectiveRankClosure q t) Orthogonal sigma p.2 = j :=
    hp'.2.1
  have hbZ : p.2 ∈ Z (Finset.univ : Finset (P q t))
      (projectiveRankClosure q t) Orthogonal sigma j := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrank⟩
  have hone : 1 ≤ (Z (Finset.univ : Finset (P q t))
      (projectiveRankClosure q t) Orthogonal sigma j).card :=
    Finset.one_le_card.mpr ⟨p.2, hbZ⟩
  have hpivot := Z_card_le_pivot
    (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
      Orthogonal sigma (r := j) (le_refl j)
  exact Finset.card_pos.mp (lt_of_lt_of_le (by omega) (hone.trans hpivot))

/-- For a nonzero pivot rank, at most `32*q^ℓ` second coordinates are
popular.  This is the cleared-denominator incidence double count. -/
theorem popularSecondsAtRank_card_le_of_pivot_pos
    (sigma : List (P q t × P q t)) (j : ℕ)
    (hz : 0 < (Z (Finset.univ : Finset (P q t))
      (projectiveRankClosure q t) Orthogonal sigma
        (pivotForRank q t sigma j)).card)
    (hl : 0 < pivotForRank q t sigma j) :
    (popularSecondsAtRank q t sigma j).card ≤
      32 * q ^ (pivotForRank q t sigma j) := by
  let l := pivotForRank q t sigma j
  have hfibre : ∀ y ∈ Z (Finset.univ : Finset (P q t))
      (projectiveRankClosure q t) Orthogonal sigma l,
      ((Finset.univ : Finset (P q t)).filter fun b ↦
        (projectiveRankClosure q t).Cl b
          (generators Orthogonal sigma y)).card ≤ 2 * q ^ (l - 1) := by
    intro y hy
    have hrank : (rankClosure (F := ZMod q) (d := t + 1)).rank
        (generators Orthogonal sigma y) = l := by
      simpa [prefixRank, projectiveRankClosure] using (Finset.mem_filter.mp hy).2
    exact Erdos920.SpanCounts.card_filter_rankClosure_cl_le_two_mul_pow_pred
      (S := generators Orthogonal sigma y) hrank
  have hall := popularQ_card_le_of_fibre
    (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
      Orthogonal q sigma l (2 * q ^ (l - 1)) hz hfibre
  have hsub : popularSecondsAtRank q t sigma j ⊆
      (Finset.univ : Finset (P q t)).filter fun b ↦
        PopularQ (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
          Orthogonal q sigma l b := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.2⟩
  calc
    (popularSecondsAtRank q t sigma j).card ≤
        ((Finset.univ : Finset (P q t)).filter fun b ↦
          PopularQ (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
            Orthogonal q sigma l b).card := Finset.card_le_card hsub
    _ ≤ 16 * q * (2 * q ^ (l - 1)) := hall
    _ = 32 * q ^ l := by
      have hpow : q ^ (l - 1) * q = q ^ l := by
        rw [← pow_succ]
        congr 1
        omega
      calc
        16 * q * (2 * q ^ (l - 1)) = 32 * (q ^ (l - 1) * q) := by ring
        _ = 32 * q ^ l := by rw [hpow]

/-- At pivot rank zero the old spans are zero-dimensional, hence contain no
projective points, so no second coordinate is popular. -/
theorem popularSecondsAtRank_card_eq_zero_of_pivot_zero
    (sigma : List (P q t × P q t)) (j : ℕ)
    (hz : 0 < (Z (Finset.univ : Finset (P q t))
      (projectiveRankClosure q t) Orthogonal sigma
        (pivotForRank q t sigma j)).card)
    (hl : pivotForRank q t sigma j = 0) :
    (popularSecondsAtRank q t sigma j).card = 0 := by
  let l := pivotForRank q t sigma j
  have hfibre : ∀ y ∈ Z (Finset.univ : Finset (P q t))
      (projectiveRankClosure q t) Orthogonal sigma l,
      ((Finset.univ : Finset (P q t)).filter fun b ↦
        (projectiveRankClosure q t).Cl b
          (generators Orthogonal sigma y)).card ≤ 0 := by
    intro y hy
    have hy' : (projectiveRankClosure q t).rank
        (generators Orthogonal sigma y) = l :=
      (Finset.mem_filter.mp hy).2
    have hl0 : l = 0 := by simpa [l] using hl
    have hrank0 : (projectiveRankClosure q t).rank
        (generators Orthogonal sigma y) = 0 := by
      rw [← hl0]
      exact hy'
    have hrank : (rankClosure (F := ZMod q) (d := t + 1)).rank
        (generators Orthogonal sigma y) = 0 := by
      change (projectiveRankClosure q t).rank
        (generators Orthogonal sigma y) = 0
      exact hrank0
    exact (Erdos920.SpanCounts.card_filter_rankClosure_cl_eq_zero_of_rank_eq_zero
      (S := generators Orthogonal sigma y) hrank).le
  have hall := popularQ_card_le_of_fibre
    (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
      Orthogonal q sigma l 0 hz hfibre
  have hsub : popularSecondsAtRank q t sigma j ⊆
      (Finset.univ : Finset (P q t)).filter fun b ↦
        PopularQ (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
          Orthogonal q sigma l b := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hb).2.2⟩
  have : (popularSecondsAtRank q t sigma j).card ≤ 0 :=
    (Finset.card_le_card hsub).trans (by simpa using hall)
  omega

/-- Uniform second-coordinate estimate, including the zero-pivot case. -/
theorem popularSecondsAtRank_card_le
    (sigma : List (P q t × P q t)) (j : ℕ)
    (hz : 0 < (Z (Finset.univ : Finset (P q t))
      (projectiveRankClosure q t) Orthogonal sigma
        (pivotForRank q t sigma j)).card) :
    (popularSecondsAtRank q t sigma j).card ≤
      32 * q ^ (pivotForRank q t sigma j) := by
  by_cases hl : pivotForRank q t sigma j = 0
  · rw [popularSecondsAtRank_card_eq_zero_of_pivot_zero q t sigma j hz hl]
    exact Nat.zero_le _
  · exact popularSecondsAtRank_card_le_of_pivot_pos q t sigma j hz
      (Nat.pos_of_ne_zero hl)

/-- The fixed-rank popular-child class injects into the union of its
compatible first-coordinate fibres. -/
theorem popularChildrenAtRank_card_le_mul
    (sigma : List (P q t × P q t)) (j : ℕ) :
    (popularChildrenAtRank q t sigma j).card ≤
      (popularSecondsAtRank q t sigma j).card * (2 * q ^ (t - j)) := by
  let B := popularSecondsAtRank q t sigma j
  let A := fun b : P q t ↦ compatibleFirsts q t sigma b
  have hsub : popularChildrenAtRank q t sigma j ⊆
      B.biUnion fun b ↦ (A b).image fun a ↦ (a, b) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hchild := (TupleBound.mem_consistentChildren_iff
      (incidentPairs q t) Orthogonal p sigma).mp hp'.1
    have hb : p.2 ∈ B := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp'.2⟩
    have ha : p.1 ∈ A p.2 := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        orthogonal_generators_of_canExtend q t sigma p.1 p.2 hchild.2⟩
    exact Finset.mem_biUnion.mpr ⟨p.2, hb,
      Finset.mem_image.mpr ⟨p.1, ha, rfl⟩⟩
  calc
    (popularChildrenAtRank q t sigma j).card ≤
        (B.biUnion fun b ↦ (A b).image fun a ↦ (a, b)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ b ∈ B, ((A b).image fun a ↦ (a, b)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ B, 2 * q ^ (t - j) := by
      apply Finset.sum_le_sum
      intro b hb
      exact Finset.card_image_le.trans
        (compatibleFirsts_card_le q t sigma b j (Finset.mem_filter.mp hb).2.1)
    _ = B.card * (2 * q ^ (t - j)) := by simp

/-- For each old-span rank `j ≤ t`, popular extensions contribute at most
`64*q^t` children. -/
theorem popularChildrenAtRank_card_le
    (sigma : List (P q t × P q t)) (j : ℕ) (hj : j ≤ t) :
    (popularChildrenAtRank q t sigma j).card ≤ 64 * q ^ t := by
  by_cases hne : (popularChildrenAtRank q t sigma j).Nonempty
  · have hz := Finset.card_pos.mpr
      (pivot_nonempty_of_popularChildrenAtRank_nonempty q t sigma j hne)
    have hseconds := popularSecondsAtRank_card_le q t sigma j hz
    have hpivot : pivotForRank q t sigma j ≤ j := by
      exact pivotLevel_le
        (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
          Orthogonal sigma j
    calc
      (popularChildrenAtRank q t sigma j).card ≤
          (popularSecondsAtRank q t sigma j).card * (2 * q ^ (t - j)) :=
        popularChildrenAtRank_card_le_mul q t sigma j
      _ ≤ (32 * q ^ (pivotForRank q t sigma j)) * (2 * q ^ (t - j)) :=
        Nat.mul_le_mul_right _ hseconds
      _ = 64 * q ^ (pivotForRank q t sigma j + (t - j)) := by
        rw [pow_add]
        ring
      _ ≤ 64 * q ^ t := by
        exact Nat.mul_le_mul_left 64
          (Nat.pow_le_pow_right (Fact.out : q.Prime).pos (by omega))
  · simp only [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne]

/-- All popular consistent children at a history, with the pivot selected
from the rank of each prospective second coordinate. -/
def popularChildren (sigma : List (P q t × P q t)) :
    Finset (P q t × P q t) :=
  (TupleBound.consistentChildren (incidentPairs q t) Orthogonal sigma).filter fun p ↦
    PopularQ (Finset.univ : Finset (P q t)) (projectiveRankClosure q t)
      Orthogonal q sigma
        (pivotForRank q t sigma (childRank q t sigma p)) p.2

/-- The preceding definition is exactly the popular disjunct used by
`MarkedChildren.marked`; this spelling is convenient for the final union
bound on marked children. -/
theorem popularChildren_eq_markedPopular
    (sigma : List (P q t × P q t)) :
    popularChildren q t sigma =
      (TupleBound.consistentChildren (incidentPairs q t) Orthogonal sigma).filter
        fun p ↦ PopularQ (Finset.univ : Finset (P q t))
          (projectiveRankClosure q t) Orthogonal q sigma
            (chosenPivot (Finset.univ : Finset (P q t))
              (projectiveRankClosure q t) Orthogonal sigma p) p.2 := by
  rfl

/-- Summing the `t+1` possible child ranks gives the uniform popular-child
bound required by the marked-tree argument. -/
theorem popularChildren_card_le (sigma : List (P q t × P q t)) :
    (popularChildren q t sigma).card ≤ 64 * (t + 1) * q ^ t := by
  let S := popularChildren q t sigma
  let Sj := fun j : ℕ ↦ popularChildrenAtRank q t sigma j
  have hsub : S ⊆ (Finset.range (t + 1)).biUnion Sj := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hj : childRank q t sigma p ≤ t :=
      childRank_le_t_of_mem_children q t sigma p hp'.1
    apply Finset.mem_biUnion.mpr
    refine ⟨childRank q t sigma p, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_filter.mpr ⟨hp'.1, rfl, hp'.2⟩
  calc
    (popularChildren q t sigma).card = S.card := rfl
    _ ≤ ((Finset.range (t + 1)).biUnion Sj).card := Finset.card_le_card hsub
    _ ≤ ∑ j ∈ Finset.range (t + 1), (Sj j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Finset.range (t + 1), 64 * q ^ t := by
      exact Finset.sum_le_sum fun j hj ↦
        popularChildrenAtRank_card_le q t sigma j
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = 64 * (t + 1) * q ^ t := by
      simp
      ring

end ProjectiveChildren

end

end Erdos920.PopularChildren
