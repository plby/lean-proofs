import Wikipedia.SzemeredisTheorem.Hypergraph.StrongFullOrderedRegularity
import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedRemoval

/-!
# Strong coarse/fine regularity for ordered partition complexes

The changing-upper-family obstruction disappears if ranks are selected from
top to bottom.  At rank `j`, freeze the already chosen fine rank-`j+1`
partition and run a long tower of rank-`j` refinements.  An energy
pigeonhole then selects nested coarse/fine rank-`j` partitions with small
energy gap against that fixed upper family.  The fine rank-`j` partition
becomes the frozen target for the next lower rank.

This file first proves the fixed-upper one-rank selector, including fully
precomputed tolerance, budget, and complexity schedules.  It then assembles
those selectors recursively into two ordered partition complexes.  The
resulting fine complex is bounded-test preliminarily regular at every rank,
refines the coarse complex, and has a genuinely small
`totalAtomEnergyGap`: every summand is measured against the corresponding
final fine upper layer.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## One fixed-upper regularity step -/

/-- Output of one fixed-budget lower-layer regularization with its explicit
step count and complexity certificate. -/
structure FixedUpperLayerRegularityCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ)
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (budget : ℕ) where
  steps : ℕ
  fine : OrderedFacePartitionSystem G k j
  steps_lt : steps < budget
  refines : OrderedFacePartitionRefines fine lower
  regular : IsPreliminaryOrderedRegular fine upper ε
  complexity :
    ∀ e,
      FacePartition.complexity (fine e) ≤
        (2 ^ (j + 1)) ^ steps *
          FacePartition.complexity (lower e)

theorem FixedUpperLayerRegularityCertificate.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    {ε : ℝ} {budget : ℕ}
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (budget : ℝ) * ε ^ 2) :
    Nonempty
      (FixedUpperLayerRegularityCertificate
        G k j lower upper ε budget) := by
  obtain ⟨steps, fine, hsteps, hrefines,
      hregular, hcomplexity⟩ :=
    exists_preliminaryOrderedRegular_refinement_with_complexity_before
      lower upper hε hlong
  exact ⟨{
    steps := steps
    fine := fine
    steps_lt := hsteps
    refines := hrefines
    regular := hregular
    complexity := hcomplexity }⟩

/-- Canonical choice of one fixed-upper lower-layer regularization. -/
noncomputable def chosenFixedUpperLayerRegularityCertificate
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (lower : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℝ) (budget : ℕ)
    (hε : 0 ≤ ε)
    (hlong :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
        (budget : ℝ) * ε ^ 2) :
    FixedUpperLayerRegularityCertificate
      G k j lower upper ε budget :=
  Classical.choice
    (FixedUpperLayerRegularityCertificate.nonempty
      lower upper hε hlong)

/-! ## Canonical fixed-upper tower -/

/-- A lower-layer tower whose upper atom family remains fixed throughout. -/
noncomputable def fixedUpperLayerRegularityTower
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    ℕ → OrderedFacePartitionSystem G k j
  | 0 => initial
  | n + 1 =>
      (chosenFixedUpperLayerRegularityCertificate
        (fixedUpperLayerRegularityTower
          initial upper ε budget hε hlong n)
        upper (ε n) (budget n)
        (hε n) (hlong n)).fine

@[simp]
theorem fixedUpperLayerRegularityTower_zero
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    fixedUpperLayerRegularityTower
      initial upper ε budget hε hlong 0 = initial :=
  rfl

@[simp]
theorem fixedUpperLayerRegularityTower_succ
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (n : ℕ) :
    fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong (n + 1) =
      (chosenFixedUpperLayerRegularityCertificate
        (fixedUpperLayerRegularityTower
          initial upper ε budget hε hlong n)
        upper (ε n) (budget n)
        (hε n) (hlong n)).fine :=
  rfl

/-- Every fixed-upper tower transition refines its predecessor. -/
theorem fixedUpperLayerRegularityTower_refines
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (n : ℕ) :
    OrderedFacePartitionRefines
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong (n + 1))
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong n) := by
  rw [fixedUpperLayerRegularityTower_succ]
  exact
    (chosenFixedUpperLayerRegularityCertificate
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong n)
      upper (ε n) (budget n)
      (hε n) (hlong n)).refines

/-- Every fixed-upper tower stage refines the initial lower layer. -/
theorem fixedUpperLayerRegularityTower_refines_initial
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    ∀ n,
      OrderedFacePartitionRefines
        (fixedUpperLayerRegularityTower
          initial upper ε budget hε hlong n)
        initial := by
  intro n
  induction n with
  | zero =>
      exact OrderedFacePartitionRefines.refl initial
  | succ n ih =>
      exact OrderedFacePartitionRefines.trans
        (fixedUpperLayerRegularityTower_refines
          initial upper ε budget hε hlong n)
        ih

/-- Stage `n+1` is regular for the fixed upper family at tolerance `ε n`. -/
theorem fixedUpperLayerRegularityTower_regular
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (n : ℕ) :
    IsPreliminaryOrderedRegular
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong (n + 1))
      upper (ε n) := by
  rw [fixedUpperLayerRegularityTower_succ]
  exact
    (chosenFixedUpperLayerRegularityCertificate
      (fixedUpperLayerRegularityTower
        initial upper ε budget hε hlong n)
      upper (ε n) (budget n)
      (hε n) (hlong n)).regular

/-- Recursive complexity factor for a fixed-upper rank-`j` tower. -/
def fixedUpperLayerComplexityFactor
    (j : ℕ) (budget : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      (2 ^ (j + 1)) ^ (budget n) *
        fixedUpperLayerComplexityFactor j budget n

/-- Complexity after `n` fixed-upper stages remains ambient-independent. -/
theorem complexity_fixedUpperLayerRegularityTower_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2) :
    ∀ (n : ℕ) (e : OrderedFace k j),
      FacePartition.complexity
          (fixedUpperLayerRegularityTower
            initial upper ε budget hε hlong n e) ≤
        fixedUpperLayerComplexityFactor j budget n *
          FacePartition.complexity (initial e) := by
  intro n
  induction n with
  | zero =>
      intro e
      simp [fixedUpperLayerComplexityFactor]
  | succ n ih =>
      intro e
      let certificate :=
        chosenFixedUpperLayerRegularityCertificate
          (fixedUpperLayerRegularityTower
            initial upper ε budget hε hlong n)
          upper (ε n) (budget n)
          (hε n) (hlong n)
      have hstep := certificate.complexity e
      have hexponent :
          (2 ^ (j + 1)) ^ certificate.steps ≤
            (2 ^ (j + 1)) ^ (budget n) :=
        Nat.pow_le_pow_right (by positivity)
          (Nat.le_of_lt certificate.steps_lt)
      rw [fixedUpperLayerRegularityTower_succ]
      calc
        FacePartition.complexity (certificate.fine e) ≤
            (2 ^ (j + 1)) ^ certificate.steps *
              FacePartition.complexity
                (fixedUpperLayerRegularityTower
                  initial upper ε budget hε hlong n e) :=
          hstep
        _ ≤
            (2 ^ (j + 1)) ^ (budget n) *
              FacePartition.complexity
                (fixedUpperLayerRegularityTower
                  initial upper ε budget hε hlong n e) :=
          Nat.mul_le_mul_right _ hexponent
        _ ≤
            (2 ^ (j + 1)) ^ (budget n) *
              (fixedUpperLayerComplexityFactor
                  j budget n *
                FacePartition.complexity (initial e)) :=
          Nat.mul_le_mul_left _ (ih e)
        _ =
            fixedUpperLayerComplexityFactor
                j budget (n + 1) *
              FacePartition.complexity (initial e) := by
          simp [fixedUpperLayerComplexityFactor,
            Nat.mul_assoc]

/-! ## Fixed-upper adjacent selection -/

/-- Selected coarse/fine lower layers for one fixed upper atom family. -/
structure FixedUpperLayerCoarseFine
    (G : Type*) [Fintype G] [DecidableEq G]
    (k j : ℕ)
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (length : ℕ) where
  index : ℕ
  index_lt : index < length
  coarse : OrderedFacePartitionSystem G k j
  fine : OrderedFacePartitionSystem G k j
  refines : OrderedFacePartitionRefines fine coarse
  coarse_refines_initial :
    OrderedFacePartitionRefines coarse initial
  fine_regular :
    IsPreliminaryOrderedRegular fine upper (ε index)
  gap_nonneg :
    0 ≤ orderedLayerAtomEnergy fine upper -
      orderedLayerAtomEnergy coarse upper
  gap_le :
    orderedLayerAtomEnergy fine upper -
        orderedLayerAtomEnergy coarse upper ≤
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) /
        (length : ℝ)
  coarse_complexity :
    ∀ e,
      FacePartition.complexity (coarse e) ≤
        fixedUpperLayerComplexityFactor
            j budget index *
          FacePartition.complexity (initial e)
  fine_complexity :
    ∀ e,
      FacePartition.complexity (fine e) ≤
        fixedUpperLayerComplexityFactor
            j budget (index + 1) *
          FacePartition.complexity (initial e)

/-- A bounded real sequence has an adjacent increment at most its endpoint
budget divided by the number of transitions. -/
theorem exists_adjacent_real_sub_le_div
    (E : ℕ → ℝ) {length : ℕ}
    (hlength : 0 < length)
    {B : ℝ}
    (hE0 : 0 ≤ E 0)
    (hElast : E length ≤ B) :
    ∃ i : ℕ, i < length ∧
      E (i + 1) - E i ≤ B / length := by
  have htel :
      ∑ i ∈ Finset.range length,
          (E (i + 1) - E i) =
        E length - E 0 :=
    Finset.sum_range_sub E length
  have hsum :
      ∑ i ∈ Finset.range length,
          (E (i + 1) - E i) ≤
        ∑ _i ∈ Finset.range length,
          B / (length : ℝ) := by
    rw [htel]
    calc
      E length - E 0 ≤ B := by linarith
      _ =
          ∑ _i ∈ Finset.range length,
            B / (length : ℝ) := by
        simp only [Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        field_simp
  obtain ⟨i, hi, hsmall⟩ :=
    Finset.exists_le_of_sum_le
      ⟨0, Finset.mem_range.mpr hlength⟩ hsum
  exact ⟨i, Finset.mem_range.mp hi, hsmall⟩

/-- Fixed-upper strong selection at one rank. -/
theorem FixedUpperLayerCoarseFine.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    {length : ℕ} (hlength : 0 < length) :
    Nonempty
      (FixedUpperLayerCoarseFine
        G k j initial upper ε budget length) := by
  let tower :=
    fixedUpperLayerRegularityTower
      initial upper ε budget hε hlong
  obtain ⟨i, hi, hgap⟩ :=
    exists_adjacent_real_sub_le_div
      (fun n => orderedLayerAtomEnergy
        (tower n) upper)
      hlength
      (orderedLayerAtomEnergy_nonneg
        (tower 0) upper)
      (orderedLayerAtomEnergy_le_card
        (tower length) upper)
  refine ⟨{
    index := i
    index_lt := hi
    coarse := tower i
    fine := tower (i + 1)
    refines := ?_
    coarse_refines_initial := ?_
    fine_regular := ?_
    gap_nonneg := ?_
    gap_le := hgap
    coarse_complexity := ?_
    fine_complexity := ?_ }⟩
  · exact fixedUpperLayerRegularityTower_refines
      initial upper ε budget hε hlong i
  · exact fixedUpperLayerRegularityTower_refines_initial
      initial upper ε budget hε hlong i
  · exact fixedUpperLayerRegularityTower_regular
      initial upper ε budget hε hlong i
  · exact sub_nonneg.mpr
      (orderedLayerAtomEnergy_mono
        (fixedUpperLayerRegularityTower_refines
          initial upper ε budget hε hlong i)
        upper)
  · exact complexity_fixedUpperLayerRegularityTower_le
      initial upper ε budget hε hlong i
  · exact complexity_fixedUpperLayerRegularityTower_le
      initial upper ε budget hε hlong (i + 1)

/-- Canonical fixed-upper coarse/fine choice. -/
noncomputable def chosenFixedUpperLayerCoarseFine
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k j : ℕ}
    (initial : OrderedFacePartitionSystem G k j)
    (upper : OrderedFacePartitionSystem G k (j + 1))
    (ε : ℕ → ℝ) (budget : ℕ → ℕ)
    (hε : ∀ n, 0 ≤ ε n)
    (hlong :
      ∀ n,
        (Fintype.card
          (OrderedFace k (j + 1)) : ℝ) <
          (budget n : ℝ) * (ε n) ^ 2)
    (length : ℕ) (hlength : 0 < length) :
    FixedUpperLayerCoarseFine
      G k j initial upper ε budget length :=
  Classical.choice
    (FixedUpperLayerCoarseFine.nonempty
      initial upper ε budget hε hlong hlength)

/-! ## Top-down all-rank assembly -/

/-- Tolerance selected from the precomputed inner timescale at each rank. -/
def selectedOrderedComplexTolerance
    {r : ℕ}
    (ε : (j : Fin r) → ℕ → ℝ)
    (index : Fin r → ℕ) :
    OrderedRegularityTolerance r :=
  fun j => ε j (index j)

/-- Complete top-down strong regularity certificate. -/
structure StrongOrderedComplexRegularityCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (ε : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ) where
  index : Fin r → ℕ
  coarse : OrderedPartitionComplex G k r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse
  coarse_refines_initial : coarse.Refines initial
  coarse_topLayer_eq :
    coarse.topLayer = initial.topLayer
  fine_topLayer_eq :
    fine.topLayer = initial.topLayer
  index_lt : ∀ j, index j < length j
  regular :
    IsFullyPreliminaryOrderedRegular fine
      (selectedOrderedComplexTolerance ε index)
  gap_nonneg :
    ∀ j : Fin r,
      0 ≤
        orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (fine.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (fine.partition j.succ)
  gap_le :
    ∀ j : Fin r,
      orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (fine.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (fine.partition j.succ) ≤
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
            (length j : ℝ)
  coarse_complexity :
    ∀ (j : Fin r) (e : OrderedFace k j.1),
      FacePartition.complexity
          (coarse.partition j.castSucc e) ≤
        fixedUpperLayerComplexityFactor
            j.1 (budget j) (index j) *
          FacePartition.complexity
            (initial.partition j.castSucc e)
  fine_complexity :
    ∀ (j : Fin r) (e : OrderedFace k j.1),
      FacePartition.complexity
          (fine.partition j.castSucc e) ≤
        fixedUpperLayerComplexityFactor
            j.1 (budget j) (index j + 1) *
          FacePartition.complexity
            (initial.partition j.castSucc e)

namespace StrongOrderedComplexRegularityCertificate

/-- Package the selected complexes as an ordered coarse/fine pair. -/
def toCoarseFine
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length) :
    OrderedCoarseFineComplex G k r where
  coarse := R.coarse
  fine := R.fine
  refines := R.refines

/-- Fine also refines the original input complex. -/
theorem fine_refines_initial
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length) :
    R.fine.Refines initial :=
  OrderedPartitionComplex.Refines.trans
    R.refines R.coarse_refines_initial

/-- Bernoulli reduction upgrades the selected fine complex to bounded-test
regularity at every rank. -/
theorem boundedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length) :
    IsFullyPreliminaryOrderedBoundedRegular R.fine
      (selectedOrderedComplexTolerance ε R.index) :=
  R.regular.toBounded

end StrongOrderedComplexRegularityCertificate

/-! ## Existence by downward rank induction -/

/-- Top-down frozen-upper construction of strong ordered complex
regularity. -/
theorem StrongOrderedComplexRegularityCertificate.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (hε : ∀ j n, 0 ≤ ε j n)
    (hlong :
      ∀ j n,
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
          (budget j n : ℝ) * (ε j n) ^ 2)
    (hlength : ∀ j, 0 < length j) :
    Nonempty
      (StrongOrderedComplexRegularityCertificate
        G k r initial ε budget length) := by
  induction r with
  | zero =>
      let index : Fin 0 → ℕ := fun j => Fin.elim0 j
      refine ⟨{
        index := index
        coarse := initial
        fine := initial
        refines :=
          OrderedPartitionComplex.Refines.refl initial
        coarse_refines_initial :=
          OrderedPartitionComplex.Refines.refl initial
        coarse_topLayer_eq := rfl
        fine_topLayer_eq := rfl
        index_lt := ?_
        regular := ?_
        gap_nonneg := ?_
        gap_le := ?_
        coarse_complexity := ?_
        fine_complexity := ?_ }⟩
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
  | succ r ih =>
      let lowerInitial :
          OrderedFacePartitionSystem G k r :=
        initial.dropTop.topLayer
      let upper :
          OrderedFacePartitionSystem G k (r + 1) :=
        initial.topLayer
      have hεtop :
          ∀ n, 0 ≤ ε (Fin.last r) n :=
        fun n => hε (Fin.last r) n
      have hlongTop :
          ∀ n,
            (Fintype.card
              (OrderedFace k (r + 1)) : ℝ) <
              (budget (Fin.last r) n : ℝ) *
                (ε (Fin.last r) n) ^ 2 := by
        intro n
        have h := hlong (Fin.last r) n
        change
          (Fintype.card
            (OrderedFace k (r + 1)) : ℝ) <
            (budget (Fin.last r) n : ℝ) *
              (ε (Fin.last r) n) ^ 2 at h
        exact h
      let topChoice :=
        chosenFixedUpperLayerCoarseFine
          lowerInitial upper
          (ε (Fin.last r))
          (budget (Fin.last r))
          hεtop hlongTop
          (length (Fin.last r))
          (hlength (Fin.last r))
      let prepared :
          OrderedPartitionComplex G k r :=
        initial.dropTop.withTopLayer topChoice.fine
      let εlower : (j : Fin r) → ℕ → ℝ :=
        fun j => ε j.castSucc
      let budgetLower : (j : Fin r) → ℕ → ℕ :=
        fun j => budget j.castSucc
      let lengthLower : Fin r → ℕ :=
        fun j => length j.castSucc
      have hεlower :
          ∀ j n, 0 ≤ εlower j n :=
        fun j n => hε j.castSucc n
      have hlongLower :
          ∀ j n,
            (Fintype.card
              (OrderedFace k (j.1 + 1)) : ℝ) <
              (budgetLower j n : ℝ) *
                (εlower j n) ^ 2 :=
        fun j n => hlong j.castSucc n
      have hlengthLower :
          ∀ j, 0 < lengthLower j :=
        fun j => hlength j.castSucc
      obtain ⟨lowerCertificate⟩ :=
        ih prepared εlower budgetLower lengthLower
          hεlower hlongLower hlengthLower
      let coarsePrefix :
          OrderedPartitionComplex G k r :=
        lowerCertificate.coarse.withTopLayer
          topChoice.coarse
      let coarse :
          OrderedPartitionComplex G k (r + 1) :=
        coarsePrefix.appendTop upper
      let fine :
          OrderedPartitionComplex G k (r + 1) :=
        lowerCertificate.fine.appendTop upper
      let index : Fin (r + 1) → ℕ :=
        fun j =>
          Fin.lastCases topChoice.index
            lowerCertificate.index j
      have hlowerFineTop :
          lowerCertificate.fine.topLayer =
            topChoice.fine := by
        calc
          lowerCertificate.fine.topLayer =
              prepared.topLayer :=
            lowerCertificate.fine_topLayer_eq
          _ = topChoice.fine :=
            OrderedPartitionComplex.topLayer_withTopLayer
              initial.dropTop topChoice.fine
      have hlowerCoarseTop :
          lowerCertificate.coarse.topLayer =
            topChoice.fine := by
        calc
          lowerCertificate.coarse.topLayer =
              prepared.topLayer :=
            lowerCertificate.coarse_topLayer_eq
          _ = topChoice.fine :=
            OrderedPartitionComplex.topLayer_withTopLayer
              initial.dropTop topChoice.fine
      refine ⟨{
        index := index
        coarse := coarse
        fine := fine
        refines := ?_
        coarse_refines_initial := ?_
        coarse_topLayer_eq := ?_
        fine_topLayer_eq := ?_
        index_lt := ?_
        regular := ?_
        gap_nonneg := ?_
        gap_le := ?_
        coarse_complexity := ?_
        fine_complexity := ?_ }⟩
      · have hprefix :
            lowerCertificate.fine.Refines
              coarsePrefix := by
          intro q e
          cases q using Fin.lastCases with
          | last =>
              simp only [coarsePrefix,
                OrderedPartitionComplex.withTopLayer,
                Fin.lastCases_last]
              change OrderedFace k r at e
              have heq :
                  lowerCertificate.fine.partition
                      (Fin.last r) e =
                    topChoice.fine e :=
                congrFun hlowerFineTop e
              rw [heq]
              exact topChoice.refines e
          | cast i =>
              simp only [coarsePrefix,
                OrderedPartitionComplex.withTopLayer,
                Fin.lastCases_castSucc]
              exact lowerCertificate.refines
                i.castSucc e
        exact OrderedPartitionComplex.appendTop_refines
          hprefix
          (OrderedFacePartitionRefines.refl upper)
      · have hprefix :
            coarsePrefix.Refines initial.dropTop := by
          intro q e
          cases q using Fin.lastCases with
          | last =>
              simp only [coarsePrefix,
                OrderedPartitionComplex.withTopLayer,
                Fin.lastCases_last]
              change OrderedFace k r at e
              exact topChoice.coarse_refines_initial e
          | cast i =>
              simp only [coarsePrefix,
                OrderedPartitionComplex.withTopLayer,
                Fin.lastCases_castSucc]
              have h :=
                lowerCertificate.coarse_refines_initial
                  i.castSucc e
              simpa only [prepared,
                OrderedPartitionComplex.withTopLayer,
                Fin.lastCases_castSucc,
                OrderedPartitionComplex.dropTop] using h
        have happend :=
          OrderedPartitionComplex.appendTop_refines
            hprefix
            (OrderedFacePartitionRefines.refl upper)
        simpa [coarse, upper] using happend
      · simp [coarse, upper]
      · simp [fine, upper]
      · intro q
        cases q using Fin.lastCases with
        | last =>
            simpa [index] using topChoice.index_lt
        | cast i =>
            simpa [index, lengthLower] using
              lowerCertificate.index_lt i
      · intro q
        cases q using Fin.lastCases with
        | last =>
            simp only [fine,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.appendTop_partition_last,
              Fin.succ_last,
              selectedOrderedComplexTolerance,
              index, Fin.lastCases_last]
            change
              @IsPreliminaryOrderedRegular
                G _ _ k r
                (lowerCertificate.fine.partition
                  (Fin.last r))
                upper
                (ε (Fin.last r) topChoice.index)
            have hregular := topChoice.fine_regular
            rw [← hlowerFineTop] at hregular
            exact hregular
        | cast i =>
            have hregular :=
              lowerCertificate.regular i
            simp only [fine,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              Fin.succ_castSucc,
              selectedOrderedComplexTolerance,
              index, Fin.lastCases_castSucc]
            change
              @IsPreliminaryOrderedRegular
                G _ _ k i.1
                (lowerCertificate.fine.partition
                  i.castSucc)
                (lowerCertificate.fine.partition i.succ)
                (ε i.castSucc
                  (lowerCertificate.index i))
            exact hregular
      · intro q
        cases q using Fin.lastCases with
        | last =>
            have hgap := topChoice.gap_nonneg
            simp only [fine, coarse, coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.appendTop_partition_last,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_last, Fin.succ_last]
            change
              0 ≤
                orderedLayerAtomEnergy
                    lowerCertificate.fine.topLayer upper -
                  orderedLayerAtomEnergy
                    topChoice.coarse upper
            rw [hlowerFineTop]
            exact hgap
        | cast i =>
            have hgap :=
              lowerCertificate.gap_nonneg i
            simp only [fine, coarse, coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc,
              Fin.succ_castSucc]
            convert hgap using 1
      · intro q
        cases q using Fin.lastCases with
        | last =>
            have hgap := topChoice.gap_le
            simp only [fine, coarse, coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.appendTop_partition_last,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_last, Fin.succ_last]
            change
              orderedLayerAtomEnergy
                    lowerCertificate.fine.topLayer upper -
                  orderedLayerAtomEnergy
                    topChoice.coarse upper ≤
                (Fintype.card
                  (OrderedFace k (r + 1)) : ℝ) /
                    (length (Fin.last r) : ℝ)
            rw [hlowerFineTop]
            exact hgap
        | cast i =>
            have hgap :=
              lowerCertificate.gap_le i
            simp only [fine, coarse, coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc,
              Fin.succ_castSucc, lengthLower]
            convert hgap using 1 <;> rfl
      · intro q
        cases q using Fin.lastCases with
        | last =>
            intro e
            have hcomplexity :=
              topChoice.coarse_complexity e
            simp only [coarse, coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_last,
              index, Fin.lastCases_last]
            change OrderedFace k r at e
            change
              FacePartition.complexity
                    (topChoice.coarse e) ≤
                fixedUpperLayerComplexityFactor
                    r (budget (Fin.last r))
                    topChoice.index *
                  FacePartition.complexity
                    (initial.partition
                      (Fin.last r).castSucc e)
            exact hcomplexity
        | cast i =>
            intro e
            change OrderedFace k i.1 at e
            have hcomplexity :=
              lowerCertificate.coarse_complexity i e
            simp only [coarse, coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc,
              index, Fin.lastCases_castSucc]
            change
              FacePartition.complexity
                  (lowerCertificate.coarse.partition
                    i.castSucc e) ≤
                fixedUpperLayerComplexityFactor
                    i.1 (budget i.castSucc)
                    (lowerCertificate.index i) *
                  FacePartition.complexity
                    (initial.partition
                      i.castSucc.castSucc e)
            simp only [budgetLower, prepared,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc,
              OrderedPartitionComplex.dropTop] at hcomplexity
            convert hcomplexity using 1
      · intro q
        cases q using Fin.lastCases with
        | last =>
            intro e
            change OrderedFace k r at e
            have hcomplexity :=
              topChoice.fine_complexity e
            simp only [fine,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              index, Fin.lastCases_last]
            change
              FacePartition.complexity
                  (lowerCertificate.fine.partition
                    (Fin.last r) e) ≤
                fixedUpperLayerComplexityFactor
                    r (budget (Fin.last r))
                    (topChoice.index + 1) *
                  FacePartition.complexity
                    (initial.partition
                      (Fin.last r).castSucc e)
            have heq :
                lowerCertificate.fine.partition
                    (Fin.last r) e =
                  topChoice.fine e :=
              congrFun hlowerFineTop e
            rw [heq]
            exact hcomplexity
        | cast i =>
            intro e
            change OrderedFace k i.1 at e
            have hcomplexity :=
              lowerCertificate.fine_complexity i e
            simp only [fine,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              index, Fin.lastCases_castSucc]
            change
              FacePartition.complexity
                  (lowerCertificate.fine.partition
                    i.castSucc e) ≤
                fixedUpperLayerComplexityFactor
                    i.1 (budget i.castSucc)
                    (lowerCertificate.index i + 1) *
                  FacePartition.complexity
                    (initial.partition
                      i.castSucc.castSucc e)
            simp only [budgetLower, prepared,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc,
              OrderedPartitionComplex.dropTop] at hcomplexity
            convert hcomplexity using 1

/-! ## Quantitative consequences -/

namespace StrongOrderedComplexRegularityCertificate

/-- The selected rankwise gaps add up to a genuinely small
frozen-fine-upper total gap. -/
theorem totalAtomEnergyGap_le_sum_div
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length) :
    R.toCoarseFine.totalAtomEnergyGap ≤
      ∑ j : Fin r,
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
            (length j : ℝ) := by
  unfold OrderedCoarseFineComplex.totalAtomEnergyGap
    OrderedCoarseFineComplex.layerAtomEnergyGap
    toCoarseFine
  exact Finset.sum_le_sum fun j _ => R.gap_le j

/-- Nonnegativity of the selected total frozen-upper gap. -/
theorem totalAtomEnergyGap_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length) :
    0 ≤ R.toCoarseFine.totalAtomEnergyGap :=
  R.toCoarseFine.totalAtomEnergyGap_nonneg

/-- At one rank, the local frozen-upper gaps below a fixed top face inject
into the complete layer gap. -/
theorem sum_faceAtomEnergyGap_trans_le_layer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (e : OrderedFace k r) (j : Fin r) :
    (∑ d : OrderedFace r (j.1 + 1),
      R.toCoarseFine.faceAtomEnergyGap
        j (d.trans e)) ≤
      R.toCoarseFine.layerAtomEnergyGap j := by
  classical
  rw [R.toCoarseFine.layerAtomEnergyGap_eq_sum_face j]
  let φ : OrderedFace r (j.1 + 1) →
      OrderedFace k (j.1 + 1) :=
    fun d => d.trans e
  have hφ : Function.Injective φ := by
    intro d₁ d₂ h
    ext i
    exact congrArg Fin.val
      (e.injective
        (congrArg
          (fun f : OrderedFace k (j.1 + 1) => f i) h))
  calc
    (∑ d : OrderedFace r (j.1 + 1),
        R.toCoarseFine.faceAtomEnergyGap j (φ d)) =
        ∑ f ∈
            (Finset.univ :
              Finset (OrderedFace r (j.1 + 1))).image φ,
          R.toCoarseFine.faceAtomEnergyGap j f := by
      rw [Finset.sum_image hφ.injOn]
    _ ≤
        ∑ f : OrderedFace k (j.1 + 1),
          R.toCoarseFine.faceAtomEnergyGap j f := by
      exact
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ _)
          (fun f _ _ =>
            R.toCoarseFine.faceAtomEnergyGap_nonneg j f)

/-- All local gaps occurring below one top face cost at most the single
global frozen-upper gap. -/
theorem sum_faceAtomEnergyGap_trans_le_total
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (e : OrderedFace k r) :
    (∑ q : OrderedPositiveSubface r,
      R.toCoarseFine.faceAtomEnergyGap
        q.1 (q.2.trans e)) ≤
      R.toCoarseFine.totalAtomEnergyGap := by
  unfold OrderedCoarseFineComplex.totalAtomEnergyGap
  let E :=
    Equiv.psigmaEquivSigma
      (fun j : Fin r => OrderedFace r (j.1 + 1))
  calc
    (∑ q : OrderedPositiveSubface r,
        R.toCoarseFine.faceAtomEnergyGap
          q.1 (q.2.trans e)) =
        ∑ q : (Σ j : Fin r,
          OrderedFace r (j.1 + 1)),
          R.toCoarseFine.faceAtomEnergyGap
            q.1 (q.2.trans e) := by
      rw [← E.sum_comp
        (fun q : (Σ j : Fin r,
            OrderedFace r (j.1 + 1)) =>
          R.toCoarseFine.faceAtomEnergyGap
            q.1 (q.2.trans e))]
      rfl
    _ =
        ∑ j : Fin r,
          ∑ d : OrderedFace r (j.1 + 1),
            R.toCoarseFine.faceAtomEnergyGap
              j (d.trans e) := by
      exact
        Fintype.sum_sigma'
          (fun (j : Fin r)
            (d : OrderedFace r (j.1 + 1)) =>
            R.toCoarseFine.faceAtomEnergyGap
              j (d.trans e))
    _ ≤
        ∑ j : Fin r,
          R.toCoarseFine.layerAtomEnergyGap j := by
      exact Finset.sum_le_sum fun j _ =>
        R.sum_faceAtomEnergyGap_trans_le_layer e j

/-- The fine upper partitions occurring below one top face inject into the
global all-rank upper-complexity sum. -/
theorem sum_fineUpperComplexity_trans_le_allRankUpperComplexity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (e : OrderedFace k r) :
    (∑ q : OrderedPositiveSubface r,
      (FacePartition.complexity
        (R.fine.partition q.1.succ
          (q.2.trans e)) : ℝ)) ≤
      orderedAllRankUpperComplexity R.fine := by
  classical
  unfold orderedAllRankUpperComplexity
  let E :=
    Equiv.psigmaEquivSigma
      (fun j : Fin r => OrderedFace r (j.1 + 1))
  calc
    (∑ q : OrderedPositiveSubface r,
        (FacePartition.complexity
          (R.fine.partition q.1.succ
            (q.2.trans e)) : ℝ)) =
        ∑ q : (Σ j : Fin r,
          OrderedFace r (j.1 + 1)),
          (FacePartition.complexity
            (R.fine.partition q.1.succ
              (q.2.trans e)) : ℝ) := by
      rw [← E.sum_comp
        (fun q : (Σ j : Fin r,
            OrderedFace r (j.1 + 1)) =>
          (FacePartition.complexity
            (R.fine.partition q.1.succ
              (q.2.trans e)) : ℝ))]
      rfl
    _ =
        ∑ j : Fin r,
          ∑ d : OrderedFace r (j.1 + 1),
            (FacePartition.complexity
              (R.fine.partition j.succ
                (d.trans e)) : ℝ) := by
      exact
        Fintype.sum_sigma'
          (fun (j : Fin r)
            (d : OrderedFace r (j.1 + 1)) =>
            (FacePartition.complexity
              (R.fine.partition j.succ
                (d.trans e)) : ℝ))
    _ ≤
        ∑ j : Fin r,
          ∑ f : OrderedFace k (j.1 + 1),
            (FacePartition.complexity
              (R.fine.partition j.succ f) : ℝ) := by
      apply Finset.sum_le_sum
      intro j _hj
      let φ : OrderedFace r (j.1 + 1) →
          OrderedFace k (j.1 + 1) :=
        fun d => d.trans e
      have hφ : Function.Injective φ := by
        intro d₁ d₂ h
        ext i
        exact congrArg Fin.val
          (e.injective
            (congrArg
              (fun f : OrderedFace k (j.1 + 1) => f i) h))
      calc
        (∑ d : OrderedFace r (j.1 + 1),
            (FacePartition.complexity
              (R.fine.partition j.succ (φ d)) : ℝ)) =
            ∑ f ∈
                (Finset.univ :
                  Finset (OrderedFace r
                    (j.1 + 1))).image φ,
              (FacePartition.complexity
                (R.fine.partition j.succ f) : ℝ) := by
          rw [Finset.sum_image hφ.injOn]
        _ ≤
            ∑ f : OrderedFace k (j.1 + 1),
              (FacePartition.complexity
                (R.fine.partition j.succ f) : ℝ) := by
          exact
            Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.subset_univ _)
              (fun _ _ _ => Nat.cast_nonneg _)

/-- Sharp constant-threshold cleaning estimate furnished by the strong
pair.  The complexity contribution is local to the selected fine upper
atoms, while all defect contributions below a top face are charged only
once to the global frozen-upper gap. -/
theorem faceDeletionDensity_badBase_constant_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          R.fine R.coarse (fun _ => α) (fun _ => β)) e ≤
      (∑ q : OrderedPositiveSubface r,
        (FacePartition.complexity
          (R.fine.partition q.1.succ
            (q.2.trans e)) : ℝ)) * α +
        R.toCoarseFine.totalAtomEnergyGap / β := by
  let P := R.toCoarseFine
  have hdeletion :
      OrderedPattern.faceDeletionDensity
          (orderedBadBaseDeletionFamily
            R.fine R.coarse (fun _ => α) (fun _ => β)) e ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (R.fine.partition q.1.succ
                (q.2.trans e)) : ℝ) * α +
            P.faceAtomEnergyGap q.1 (q.2.trans e) / β) := by
    convert
      (faceDeletionDensity_orderedBadBaseDeletionFamily_le
        R.refines (fun _ => α) (fun _ => β)
        (fun _ => hα) (fun _ => hβ) e) using 1
    rfl
  calc
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          R.fine R.coarse (fun _ => α) (fun _ => β)) e ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (R.fine.partition q.1.succ
                (q.2.trans e)) : ℝ) * α +
            P.faceAtomEnergyGap q.1 (q.2.trans e) / β) :=
      hdeletion
    _ =
        (∑ q : OrderedPositiveSubface r,
          (FacePartition.complexity
            (R.fine.partition q.1.succ
              (q.2.trans e)) : ℝ)) * α +
          (∑ q : OrderedPositiveSubface r,
            P.faceAtomEnergyGap q.1 (q.2.trans e)) / β := by
      rw [Finset.sum_add_distrib, Finset.sum_mul,
        Finset.sum_div]
    _ ≤
        (∑ q : OrderedPositiveSubface r,
          (FacePartition.complexity
            (R.fine.partition q.1.succ
              (q.2.trans e)) : ℝ)) * α +
          P.totalAtomEnergyGap / β := by
      exact add_le_add (le_refl _)
        (div_le_div_of_nonneg_right
          (R.sum_faceAtomEnergyGap_trans_le_total e) hβ.le)

/-- Fully explicit version of the preceding cleaning estimate: the energy
term is replaced by the chosen reciprocal-timescale budget. -/
theorem faceDeletionDensity_badBase_constant_le_sum_div
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          R.fine R.coarse (fun _ => α) (fun _ => β)) e ≤
      (∑ q : OrderedPositiveSubface r,
        (FacePartition.complexity
          (R.fine.partition q.1.succ
            (q.2.trans e)) : ℝ)) * α +
        (∑ j : Fin r,
          (Fintype.card
            (OrderedFace k (j.1 + 1)) : ℝ) /
              (length j : ℝ)) / β := by
  exact
    (R.faceDeletionDensity_badBase_constant_le hα hβ e).trans
      (add_le_add (le_refl _)
        (div_le_div_of_nonneg_right
          R.totalAtomEnergyGap_le_sum_div hβ.le))

/-- Global-complexity form of the explicit deletion bound.  It is uniform
in the top face and charges the frozen-upper energy gap only once. -/
theorem faceDeletionDensity_badBase_constant_le_globalComplexity_sum_div
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          R.fine R.coarse (fun _ => α) (fun _ => β)) e ≤
      orderedAllRankUpperComplexity R.fine * α +
        (∑ j : Fin r,
          (Fintype.card
            (OrderedFace k (j.1 + 1)) : ℝ) /
              (length j : ℝ)) / β := by
  exact
    (R.faceDeletionDensity_badBase_constant_le_sum_div
      hα hβ e).trans
      (add_le_add
        (mul_le_mul_of_nonneg_right
          (R.sum_fineUpperComplexity_trans_le_allRankUpperComplexity
            e)
          hα)
        (le_refl _))

/-- If `M` bounds the selected fine upper partitions, the complete
per-top-face deletion density has a closed numerical bound.  In particular,
the energy term is not multiplied by the number of subfaces. -/
theorem faceDeletionDensity_badBase_constant_of_complexity_le_sum_div
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r M : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (hcomplex :
      ∀ (j : Fin r) (e : OrderedFace k (j.1 + 1)),
        FacePartition.complexity
          (R.fine.partition j.succ e) ≤ M)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β)
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          R.fine R.coarse (fun _ => α) (fun _ => β)) e ≤
      (Fintype.card (OrderedPositiveSubface r) : ℝ) *
          (M : ℝ) * α +
        (∑ j : Fin r,
          (Fintype.card
            (OrderedFace k (j.1 + 1)) : ℝ) /
              (length j : ℝ)) / β := by
  have hsum :
      (∑ q : OrderedPositiveSubface r,
        (FacePartition.complexity
          (R.fine.partition q.1.succ
            (q.2.trans e)) : ℝ)) ≤
        (Fintype.card
          (OrderedPositiveSubface r) : ℝ) * (M : ℝ) := by
    calc
      (∑ q : OrderedPositiveSubface r,
          (FacePartition.complexity
            (R.fine.partition q.1.succ
              (q.2.trans e)) : ℝ)) ≤
          ∑ _q : OrderedPositiveSubface r,
            (M : ℝ) := by
        apply Finset.sum_le_sum
        intro q _hq
        exact_mod_cast hcomplex q.1 (q.2.trans e)
      _ =
          (Fintype.card
            (OrderedPositiveSubface r) : ℝ) * (M : ℝ) := by
        simp
  exact
    (R.faceDeletionDensity_badBase_constant_le_sum_div
      hα hβ e).trans
      (add_le_add
        (mul_le_mul_of_nonneg_right hsum hα)
        (le_refl _))

end StrongOrderedComplexRegularityCertificate

/-- Strong ordered complex regularity, packaged together with its explicit
total frozen-fine-upper atom-energy estimate. -/
theorem exists_strongOrderedComplexRegularity
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (hε : ∀ j n, 0 ≤ ε j n)
    (hlong :
      ∀ j n,
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
          (budget j n : ℝ) * (ε j n) ^ 2)
    (hlength : ∀ j, 0 < length j) :
    ∃ R : StrongOrderedComplexRegularityCertificate
        G k r initial ε budget length,
      R.toCoarseFine.totalAtomEnergyGap ≤
        ∑ j : Fin r,
          (Fintype.card
            (OrderedFace k (j.1 + 1)) : ℝ) /
              (length j : ℝ) := by
  obtain ⟨R⟩ :=
    StrongOrderedComplexRegularityCertificate.nonempty
      initial ε budget length hε hlong hlength
  exact ⟨R, R.totalAtomEnergyGap_le_sum_div⟩

/-- A prescribed upper bound for the sum of reciprocal rank timescales
immediately gives the desired total atom-energy tolerance. -/
theorem exists_strongOrderedComplexRegularity_of_sum_div_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (γ : ℝ)
    (hε : ∀ j n, 0 ≤ ε j n)
    (hlong :
      ∀ j n,
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
          (budget j n : ℝ) * (ε j n) ^ 2)
    (hlength : ∀ j, 0 < length j)
    (hγ :
      (∑ j : Fin r,
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
            (length j : ℝ)) ≤ γ) :
    ∃ R : StrongOrderedComplexRegularityCertificate
        G k r initial ε budget length,
      R.toCoarseFine.totalAtomEnergyGap ≤ γ := by
  obtain ⟨R, hR⟩ :=
    exists_strongOrderedComplexRegularity
      initial ε budget length hε hlong hlength
  exact ⟨R, hR.trans hγ⟩

/-- Strict reciprocal-timescale control gives a strict total atom-energy
gap, as required by threshold choices in cleaning arguments. -/
theorem exists_strongOrderedComplexRegularity_of_sum_div_lt
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (γ : ℝ)
    (hε : ∀ j n, 0 ≤ ε j n)
    (hlong :
      ∀ j n,
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
          (budget j n : ℝ) * (ε j n) ^ 2)
    (hlength : ∀ j, 0 < length j)
    (hγ :
      (∑ j : Fin r,
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
            (length j : ℝ)) < γ) :
    ∃ R : StrongOrderedComplexRegularityCertificate
        G k r initial ε budget length,
      R.toCoarseFine.totalAtomEnergyGap < γ := by
  obtain ⟨R, hR⟩ :=
    exists_strongOrderedComplexRegularity
      initial ε budget length hε hlong hlength
  exact ⟨R, hR.trans_lt hγ⟩

end Wikipedia.SzemeredisTheorem
