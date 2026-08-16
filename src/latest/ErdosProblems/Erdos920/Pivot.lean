import ErdosProblems.Erdos920.Container

/-!
# Deterministic pivot strata for the Erdős 920 container argument

For a history `σ`, `Container.U ... σ j` consists of the points whose selected
generator set has rank at most `j`, while `Container.Z ... σ ℓ` is its
exact-rank-`ℓ` stratum.  This file chooses, once and for all, a largest stratum
among `0, ..., j`.  It also records the rounding-safe natural-number threshold
used in the poor/popular dichotomy.

The pivot is represented by `Fin (j + 1)`.  This builds the bound `ℓ ≤ j` into
its type and prevents a later caller from accidentally selecting an irrelevant
stratum.
-/

namespace Erdos920.Pivot

open Erdos920.Container

noncomputable section

variable {P : Type*} [Fintype P] [DecidableEq P]

section Strata

variable (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
  [DecidableRel R] (σ : List (P × P))

/-- A maximum-cardinality exact-rank stratum among `0, ..., j`.  The
primitive recursion makes the choice canonical: when two strata have equal
cardinality, the earlier (smaller) pivot is retained. -/
def pivotLevel : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
      if (Z points C R σ (pivotLevel j)).card <
          (Z points C R σ (j + 1)).card then j + 1
      else pivotLevel j

theorem pivotLevel_mem_range (j : ℕ) :
    pivotLevel points C R σ j < j + 1 := by
  induction j with
  | zero => simp [pivotLevel]
  | succ j ih =>
      rw [pivotLevel]
      split <;> omega

theorem pivotLevel_le (j : ℕ) :
    pivotLevel points C R σ j ≤ j :=
  Nat.le_of_lt_succ (pivotLevel_mem_range points C R σ j)

/-- Every admissible exact-rank stratum is no larger than the pivot stratum. -/
theorem Z_card_le_pivot {r j : ℕ} (hr : r ≤ j) :
    (Z points C R σ r).card ≤
      (Z points C R σ (pivotLevel points C R σ j)).card := by
  induction j with
  | zero =>
      have : r = 0 := by omega
      subst r
      simp [pivotLevel]
  | succ j ih =>
      rw [pivotLevel]
      split_ifs with hnew
      · by_cases hrnew : r = j + 1
        · subst r
          exact le_rfl
        · exact (ih (Nat.le_of_lt_succ (lt_of_le_of_ne hr hrnew))).trans hnew.le
      · by_cases hrnew : r = j + 1
        · subst r
          exact Nat.le_of_not_gt hnew
        · exact ih (Nat.le_of_lt_succ (lt_of_le_of_ne hr hrnew))

/-- The pivot bundled with its proof that it lies in `0, ..., j`. -/
def pivotIndex (j : ℕ) : Fin (j + 1) :=
  ⟨pivotLevel points C R σ j, pivotLevel_mem_range points C R σ j⟩

@[simp] theorem pivotLevel_eq (j : ℕ) :
    pivotLevel points C R σ j = (pivotIndex points C R σ j : ℕ) := rfl

@[simp] theorem pivotIndex_le (j : ℕ) :
    (pivotIndex points C R σ j : ℕ) ≤ j :=
  pivotLevel_le points C R σ j

/-- `Fin`-valued spelling of `Z_card_le_pivot`. -/
theorem card_Z_le_card_Z_pivot (j r : ℕ) (hr : r ≤ j) :
    (Z points C R σ r).card ≤
      (Z points C R σ (pivotIndex points C R σ j : ℕ)).card := by
  exact Z_card_le_pivot points C R σ hr

/-- Membership in `U_j` is exactly membership in one of the exact-rank
strata `Z_0, ..., Z_j`. -/
theorem mem_U_iff_exists_mem_Z (j : ℕ) (y : P) :
    y ∈ U points C R σ j ↔
      ∃ r ∈ Finset.range (j + 1), y ∈ Z points C R σ r := by
  constructor
  · intro hy
    have hy' := Finset.mem_filter.mp hy
    refine ⟨prefixRank C R σ y, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hy'.2), ?_⟩
    exact Finset.mem_filter.mpr ⟨hy'.1, rfl⟩
  · rintro ⟨r, hr, hyr⟩
    have hyr' := Finset.mem_filter.mp hyr
    refine Finset.mem_filter.mpr ⟨hyr'.1, ?_⟩
    rw [hyr'.2]
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hr)

/-- `U_j` is the finite union of its exact-rank strata. -/
theorem U_eq_biUnion_Z (j : ℕ) :
    U points C R σ j =
      (Finset.range (j + 1)).biUnion fun r ↦ Z points C R σ r := by
  ext y
  rw [mem_U_iff_exists_mem_Z points C R σ]
  simp only [Finset.mem_biUnion]

/-- Pigeonholing the `j+1` rank strata: the whole potential is at most
`j+1` times its deterministic pivot stratum. -/
theorem card_U_le_mul_card_Z_pivot (j : ℕ) :
    (U points C R σ j).card ≤
      (j + 1) * (Z points C R σ (pivotIndex points C R σ j : ℕ)).card := by
  rw [U_eq_biUnion_Z points C R σ]
  calc
    ((Finset.range (j + 1)).biUnion fun r ↦ Z points C R σ r).card ≤
        ∑ r ∈ Finset.range (j + 1), (Z points C R σ r).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _r ∈ Finset.range (j + 1),
        (Z points C R σ (pivotIndex points C R σ j : ℕ)).card := by
      exact Finset.sum_le_sum fun r hr ↦
        card_Z_le_card_Z_pivot points C R σ j r
          (Nat.le_of_lt_succ (Finset.mem_range.mp hr))
    _ = (j + 1) *
        (Z points C R σ (pivotIndex points C R σ j : ℕ)).card := by
      simp

/-- Nat-valued spelling matching the notation in the projective container. -/
theorem U_card_le_succ_mul_Z_pivot (j : ℕ) :
    (U points C R σ j).card ≤
      (j + 1) * (Z points C R σ (pivotLevel points C R σ j)).card := by
  exact card_U_le_mul_card_Z_pivot points C R σ j

/-- The form used in Bradač's container calculation.  For a positive rank
budget, `j+1 ≤ 2j`, so the pivot stratum controls `U_j` with the paper's
convenient factor `2j`. -/
theorem card_U_le_two_mul_card_Z_pivot (j : ℕ) (hj : 0 < j) :
    (U points C R σ j).card ≤
      2 * j * (Z points C R σ (pivotIndex points C R σ j : ℕ)).card := by
  refine (card_U_le_mul_card_Z_pivot points C R σ j).trans ?_
  apply Nat.mul_le_mul_right
  omega

end Strata

section IntegerCut

/-- The rounding-safe popularity threshold associated to a stratum of size
`z`.  The maximum with one makes cancellation legitimate even when the
stratum is empty. -/
def pivotCut (q z : ℕ) : ℕ :=
  max 1 (z ⌈/⌉ (32 * q))

@[simp] theorem pivotCut_pos (q z : ℕ) : 0 < pivotCut q z := by
  simp [pivotCut]

theorem ceilDiv_le_pivotCut (q z : ℕ) :
    z ⌈/⌉ (32 * q) ≤ pivotCut q z := by
  exact Nat.le_max_right _ _

/-- The defining lower estimate for the ceiling threshold, with denominators
cleared. -/
theorem card_le_mul_pivotCut {q z : ℕ} (hq : 0 < q) :
    z ≤ (32 * q) * pivotCut q z := by
  exact (le_smul_ceilDiv (by positivity : 0 < 32 * q)).trans
    (Nat.mul_le_mul_left (32 * q) (ceilDiv_le_pivotCut q z))

/-- For a nonempty stratum the rounded threshold never exceeds the stratum
itself. -/
theorem pivotCut_le_card {q z : ℕ} (hq : 0 < q) (hz : 0 < z) :
    pivotCut q z ≤ z := by
  rw [pivotCut, max_le_iff]
  refine ⟨hz, ?_⟩
  rw [ceilDiv_le_iff_le_mul (by positivity : 0 < 32 * q)]
  have hden : 1 ≤ 32 * q := by omega
  simpa using Nat.mul_le_mul_right z hden

/-- Cancellation package used after double-counting popular points.  If
`pop * cut ≤ z * cap`, then the ceiling relation forces
`pop ≤ 32*q*cap`. -/
theorem popular_count_le {q z cut pop cap : ℕ}
    (hcutpos : 0 < cut) (hzcut : z ≤ (32 * q) * cut)
    (hinc : pop * cut ≤ z * cap) :
    pop ≤ (32 * q) * cap := by
  apply Nat.le_of_mul_le_mul_right ?_ hcutpos
  calc
    pop * cut ≤ z * cap := hinc
    _ ≤ ((32 * q) * cut) * cap := Nat.mul_le_mul_right cap hzcut
    _ = ((32 * q) * cap) * cut := by ring

/-- Specialization of `popular_count_le` to the canonical pivot threshold. -/
theorem popular_count_le_of_pivotCut {q z pop cap : ℕ} (hq : 0 < q)
    (hinc : pop * pivotCut q z ≤ z * cap) :
    pop ≤ (32 * q) * cap := by
  exact popular_count_le (pivotCut_pos q z) (card_le_mul_pivotCut hq) hinc

/-- The arithmetic poor/popular dichotomy at the canonical cut.  If neither
exception applies, then the good remainder has at least `cut` elements.
This theorem is independent of the meanings of `A` and `B`, so it can be
reused both for abstract containers and the projective specialization. -/
theorem pivotCut_le_filter_and_not_of_not_poor_not_popular
    {q z : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    (s : Finset S) (A B : S → Prop) [DecidablePred A] [DecidablePred B]
    (hnotPoor : ¬ (s.filter A).card < 2 * pivotCut q z)
    (hnotPopular : ¬ pivotCut q z ≤ (s.filter B).card) :
    pivotCut q z ≤ (s.filter fun x ↦ A x ∧ ¬ B x).card := by
  apply Container.card_filter_and_not_ge
  · exact Nat.le_of_not_gt hnotPoor
  · exact Nat.le_of_lt (Nat.lt_of_not_ge hnotPopular)

end IntegerCut

section ContainerCut

variable (points : Finset P) (C : RankClosure P) (R : P → P → Prop)
  [DecidableRel R] (σ : List (P × P))

/-- The abstract poor/popular subtraction, specialized to the canonical
integer pivot cut. -/
theorem pivotCut_le_rankRaisingSet_of_not_poor_not_popular
    (q ℓ : ℕ) (a b : P)
    (ha : ¬ Poor points C R σ ℓ
      (pivotCut q (Z points C R σ ℓ).card) a)
    (hb : ¬ Popular points C R σ ℓ
      (pivotCut q (Z points C R σ ℓ).card) b) :
    pivotCut q (Z points C R σ ℓ).card ≤
      (rankRaisingSet points C R σ ℓ a b).card := by
  exact rankRaisingSet_card_ge_of_not_poor_not_popular
    points C R σ ℓ (pivotCut q (Z points C R σ ℓ).card) a b ha hb

/-- A canonical-cut version of the projective popularity estimate.  The
only geometric input left to a caller is `hfibre`, the number of points in
each old span. -/
theorem popularInStratum_card_le_of_pivotCut
    (q ℓ cap : ℕ) (hq : 0 < q)
    (hfibre : ∀ y ∈ Z points C R σ ℓ,
      (points.filter fun b ↦ C.Cl b (generators R σ y)).card ≤ cap) :
    (points.filter fun b ↦ Popular points C R σ ℓ
      (pivotCut q (Z points C R σ ℓ).card) b).card ≤
        (32 * q) * cap := by
  apply popular_count_le_of_pivotCut hq
  exact popularInStratum_card_mul_cut_le points C R σ ℓ
    (pivotCut q (Z points C R σ ℓ).card) cap hfibre

end ContainerCut

end

end Erdos920.Pivot
