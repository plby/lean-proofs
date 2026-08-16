import Wikipedia.SzemeredisTheorem.Hypergraph.FullOrderedRegularity
import Wikipedia.SzemeredisTheorem.Hypergraph.BoundaryBernoulli

/-!
# Strong all-rank ordered regularity towers

This file iterates the all-rank preliminary regularity theorem using
tolerance and budget schedules fixed before the tower is constructed.
Every transition refines the preceding complex, preserves its top layer,
and is regular for all bounded boundary products at the scheduled
tolerance.  A recursive numerical factor bounds every non-top partition
complexity independently of the ambient type.

For energy selection, the upper atom family must be held fixed.  We
therefore prove an adjacent-gap pigeonhole theorem for an arbitrary fixed
target complex.  The final section records the exact identity relating this
valid fixed-target potential to the moving-upper potential of consecutive
tower stages.  Its extra upper-refinement loss is the precise obstruction
to obtaining Tao's strong coarse/fine conclusion from a naive moving
potential.

All schedules in this file are arguments to the construction; none is
chosen after inspecting an ambient-dependent partition.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Bounded-test all-rank regularity -/

/-- Every adjacent pair is regular against arbitrary `[0,1]`-valued
boundary factors. -/
def IsFullyPreliminaryOrderedBoundedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (ε : OrderedRegularityTolerance r) : Prop :=
  ∀ j : Fin r,
    IsPreliminaryOrderedBoundedRegular
      (C.partition j.castSucc)
      (C.partition j.succ)
      (ε j)

/-- Boolean all-rank preliminary regularity controls bounded boundary
products with no loss. -/
theorem IsFullyPreliminaryOrderedRegular.toBounded
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    {ε : OrderedRegularityTolerance r}
    (h : IsFullyPreliminaryOrderedRegular C ε) :
    IsFullyPreliminaryOrderedBoundedRegular C ε := by
  intro j
  exact (h j).toBounded

/-! ## Canonical precomputed tower -/

/-- Canonical choice of one all-rank fixed-budget certificate. -/
noncomputable def chosenFullOrderedRegularityCertificate
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (ε : OrderedRegularityTolerance r)
    (budget : OrderedRegularityBudget r)
    (hε : ∀ j, 0 ≤ ε j)
    (hbudget :
      IsOrderedRegularityBudget k r ε budget) :
    FullOrderedRegularityCertificate C ε budget :=
  Classical.choice
    (exists_fullOrderedRegularityCertificate
      C ε budget hε hbudget)

/-- An infinite tower whose `n`th transition uses only the schedules
`ε n` and `budget n`, both supplied before construction. -/
noncomputable def strongFullOrderedRegularityTower
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : ℕ → OrderedRegularityTolerance r)
    (budget : ℕ → OrderedRegularityBudget r)
    (hε : ∀ n j, 0 ≤ ε n j)
    (hbudget :
      ∀ n, IsOrderedRegularityBudget
        k r (ε n) (budget n)) :
    ℕ → OrderedPartitionComplex G k r
  | 0 => initial
  | n + 1 =>
      (chosenFullOrderedRegularityCertificate
        (strongFullOrderedRegularityTower
          initial ε budget hε hbudget n)
        (ε n) (budget n) (hε n) (hbudget n)).fine

@[simp]
theorem strongFullOrderedRegularityTower_zero
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : ℕ → OrderedRegularityTolerance r)
    (budget : ℕ → OrderedRegularityBudget r)
    (hε : ∀ n j, 0 ≤ ε n j)
    (hbudget :
      ∀ n, IsOrderedRegularityBudget
        k r (ε n) (budget n)) :
    strongFullOrderedRegularityTower
      initial ε budget hε hbudget 0 = initial :=
  rfl

@[simp]
theorem strongFullOrderedRegularityTower_succ
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : ℕ → OrderedRegularityTolerance r)
    (budget : ℕ → OrderedRegularityBudget r)
    (hε : ∀ n j, 0 ≤ ε n j)
    (hbudget :
      ∀ n, IsOrderedRegularityBudget
        k r (ε n) (budget n))
    (n : ℕ) :
    strongFullOrderedRegularityTower
        initial ε budget hε hbudget (n + 1) =
      (chosenFullOrderedRegularityCertificate
        (strongFullOrderedRegularityTower
          initial ε budget hε hbudget n)
        (ε n) (budget n) (hε n) (hbudget n)).fine :=
  rfl

/-- The actual stopping-time schedule chosen during transition `n`. -/
noncomputable def strongFullOrderedRegularityStepSchedule
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : ℕ → OrderedRegularityTolerance r)
    (budget : ℕ → OrderedRegularityBudget r)
    (hε : ∀ n j, 0 ≤ ε n j)
    (hbudget :
      ∀ n, IsOrderedRegularityBudget
        k r (ε n) (budget n))
    (n : ℕ) :
    OrderedRegularityStepSchedule r :=
  (chosenFullOrderedRegularityCertificate
    (strongFullOrderedRegularityTower
      initial ε budget hε hbudget n)
    (ε n) (budget n) (hε n) (hbudget n)).steps

/-- Every transition is a pointwise refinement. -/
theorem strongFullOrderedRegularityTower_refines
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : ℕ → OrderedRegularityTolerance r)
    (budget : ℕ → OrderedRegularityBudget r)
    (hε : ∀ n j, 0 ≤ ε n j)
    (hbudget :
      ∀ n, IsOrderedRegularityBudget
        k r (ε n) (budget n))
    (n : ℕ) :
    (strongFullOrderedRegularityTower
      initial ε budget hε hbudget (n + 1)).Refines
    (strongFullOrderedRegularityTower
      initial ε budget hε hbudget n) := by
  rw [strongFullOrderedRegularityTower_succ]
  exact
    (chosenFullOrderedRegularityCertificate
      (strongFullOrderedRegularityTower
        initial ε budget hε hbudget n)
      (ε n) (budget n) (hε n) (hbudget n)).refines

/-- Transition `n` preserves the top layer exactly. -/
theorem strongFullOrderedRegularityTower_topLayer_succ
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : ℕ → OrderedRegularityTolerance r)
    (budget : ℕ → OrderedRegularityBudget r)
    (hε : ∀ n j, 0 ≤ ε n j)
    (hbudget :
      ∀ n, IsOrderedRegularityBudget
        k r (ε n) (budget n))
    (n : ℕ) :
    (strongFullOrderedRegularityTower
      initial ε budget hε hbudget (n + 1)).topLayer =
    (strongFullOrderedRegularityTower
      initial ε budget hε hbudget n).topLayer := by
  rw [strongFullOrderedRegularityTower_succ]
  exact
    (chosenFullOrderedRegularityCertificate
      (strongFullOrderedRegularityTower
        initial ε budget hε hbudget n)
      (ε n) (budget n) (hε n) (hbudget n)).topLayer_eq

/-- Every tower stage has the same top layer as the initial complex. -/
theorem strongFullOrderedRegularityTower_topLayer
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : ℕ → OrderedRegularityTolerance r)
    (budget : ℕ → OrderedRegularityBudget r)
    (hε : ∀ n j, 0 ≤ ε n j)
    (hbudget :
      ∀ n, IsOrderedRegularityBudget
        k r (ε n) (budget n)) :
    ∀ n,
      (strongFullOrderedRegularityTower
        initial ε budget hε hbudget n).topLayer =
      initial.topLayer := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [strongFullOrderedRegularityTower_topLayer_succ]
      exact ih

/-- The fine endpoint of transition `n` is all-rank regular at the
precomputed tolerance `ε n`. -/
theorem strongFullOrderedRegularityTower_regular
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : ℕ → OrderedRegularityTolerance r)
    (budget : ℕ → OrderedRegularityBudget r)
    (hε : ∀ n j, 0 ≤ ε n j)
    (hbudget :
      ∀ n, IsOrderedRegularityBudget
        k r (ε n) (budget n))
    (n : ℕ) :
    IsFullyPreliminaryOrderedRegular
      (strongFullOrderedRegularityTower
        initial ε budget hε hbudget (n + 1))
      (ε n) := by
  rw [strongFullOrderedRegularityTower_succ]
  exact
    (chosenFullOrderedRegularityCertificate
      (strongFullOrderedRegularityTower
        initial ε budget hε hbudget n)
      (ε n) (budget n) (hε n) (hbudget n)).regular

/-- The same endpoint is regular against all bounded boundary products. -/
theorem strongFullOrderedRegularityTower_boundedRegular
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : ℕ → OrderedRegularityTolerance r)
    (budget : ℕ → OrderedRegularityBudget r)
    (hε : ∀ n j, 0 ≤ ε n j)
    (hbudget :
      ∀ n, IsOrderedRegularityBudget
        k r (ε n) (budget n))
    (n : ℕ) :
    IsFullyPreliminaryOrderedBoundedRegular
      (strongFullOrderedRegularityTower
        initial ε budget hε hbudget (n + 1))
      (ε n) :=
  (strongFullOrderedRegularityTower_regular
    initial ε budget hε hbudget n).toBounded

/-- The chosen stopping index at transition `n` is below its precomputed
budget at every rank. -/
theorem strongFullOrderedRegularityStepSchedule_lt
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : ℕ → OrderedRegularityTolerance r)
    (budget : ℕ → OrderedRegularityBudget r)
    (hε : ∀ n j, 0 ≤ ε n j)
    (hbudget :
      ∀ n, IsOrderedRegularityBudget
        k r (ε n) (budget n))
    (n : ℕ) (j : Fin r) :
    strongFullOrderedRegularityStepSchedule
        initial ε budget hε hbudget n j <
      budget n j :=
  (chosenFullOrderedRegularityCertificate
    (strongFullOrderedRegularityTower
      initial ε budget hε hbudget n)
    (ε n) (budget n) (hε n) (hbudget n)).steps_lt j

/-! ## Recursive ambient-independent complexity bound -/

/-- Precomputed multiplicative complexity factor through the first `n`
tower transitions at rank `j`. -/
def strongFullOrderedComplexityFactor
    {r : ℕ}
    (budget : ℕ → OrderedRegularityBudget r)
    (j : Fin r) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      (2 ^ (j.1 + 1)) ^ (budget n j) *
        strongFullOrderedComplexityFactor budget j n

@[simp]
theorem strongFullOrderedComplexityFactor_zero
    {r : ℕ}
    (budget : ℕ → OrderedRegularityBudget r)
    (j : Fin r) :
    strongFullOrderedComplexityFactor budget j 0 = 1 :=
  rfl

@[simp]
theorem strongFullOrderedComplexityFactor_succ
    {r : ℕ}
    (budget : ℕ → OrderedRegularityBudget r)
    (j : Fin r) (n : ℕ) :
    strongFullOrderedComplexityFactor budget j (n + 1) =
      (2 ^ (j.1 + 1)) ^ (budget n j) *
        strongFullOrderedComplexityFactor budget j n :=
  rfl

/-- One tower transition obeys the scheduled, rather than merely the
chosen, complexity multiplier. -/
theorem complexity_strongFullOrderedRegularityTower_succ_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : ℕ → OrderedRegularityTolerance r)
    (budget : ℕ → OrderedRegularityBudget r)
    (hε : ∀ n j, 0 ≤ ε n j)
    (hbudget :
      ∀ n, IsOrderedRegularityBudget
        k r (ε n) (budget n))
    (n : ℕ) (j : Fin r)
    (e : OrderedFace k j.1) :
    FacePartition.complexity
        ((strongFullOrderedRegularityTower
          initial ε budget hε hbudget (n + 1)).partition
            j.castSucc e) ≤
      (2 ^ (j.1 + 1)) ^ (budget n j) *
        FacePartition.complexity
          ((strongFullOrderedRegularityTower
            initial ε budget hε hbudget n).partition
              j.castSucc e) := by
  let certificate :=
    chosenFullOrderedRegularityCertificate
      (strongFullOrderedRegularityTower
        initial ε budget hε hbudget n)
      (ε n) (budget n) (hε n) (hbudget n)
  have hchosen := certificate.complexity j e
  have hexponent :
      (2 ^ (j.1 + 1)) ^ (certificate.steps j) ≤
        (2 ^ (j.1 + 1)) ^ (budget n j) :=
    Nat.pow_le_pow_right (by positivity)
      (Nat.le_of_lt (certificate.steps_lt j))
  rw [strongFullOrderedRegularityTower_succ]
  exact hchosen.trans
    (Nat.mul_le_mul_right _ hexponent)

/-- Recursive complexity bound for every non-top layer of every tower
stage. -/
theorem complexity_strongFullOrderedRegularityTower_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (ε : ℕ → OrderedRegularityTolerance r)
    (budget : ℕ → OrderedRegularityBudget r)
    (hε : ∀ n j, 0 ≤ ε n j)
    (hbudget :
      ∀ n, IsOrderedRegularityBudget
        k r (ε n) (budget n)) :
    ∀ (n : ℕ) (j : Fin r)
        (e : OrderedFace k j.1),
      FacePartition.complexity
          ((strongFullOrderedRegularityTower
            initial ε budget hε hbudget n).partition
              j.castSucc e) ≤
        strongFullOrderedComplexityFactor
            budget j n *
          FacePartition.complexity
            (initial.partition j.castSucc e) := by
  intro n
  induction n with
  | zero =>
      intro j e
      simp
  | succ n ih =>
      intro j e
      calc
        FacePartition.complexity
            ((strongFullOrderedRegularityTower
              initial ε budget hε hbudget (n + 1)).partition
                j.castSucc e) ≤
            (2 ^ (j.1 + 1)) ^ (budget n j) *
              FacePartition.complexity
                ((strongFullOrderedRegularityTower
                  initial ε budget hε hbudget n).partition
                    j.castSucc e) :=
          complexity_strongFullOrderedRegularityTower_succ_le
            initial ε budget hε hbudget n j e
        _ ≤
            (2 ^ (j.1 + 1)) ^ (budget n j) *
              (strongFullOrderedComplexityFactor
                  budget j n *
                FacePartition.complexity
                  (initial.partition j.castSucc e)) :=
          Nat.mul_le_mul_left _ (ih j e)
        _ =
            strongFullOrderedComplexityFactor
                budget j (n + 1) *
              FacePartition.complexity
                (initial.partition j.castSucc e) := by
          simp [Nat.mul_assoc]

/-! ## Fixed-upper-family all-rank energy -/

/-- Total atom-energy budget across all adjacent ranks. -/
noncomputable def orderedAllRankAtomEnergyBudget
    (k r : ℕ) : ℝ :=
  ∑ j : Fin r,
    (Fintype.card
      (OrderedFace k (j.1 + 1)) : ℝ)

/-- Observe every upper atom of one fixed target complex from the lower
boundaries of another complex. -/
noncomputable def orderedFixedTargetAtomEnergy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (lower target : OrderedPartitionComplex G k r) : ℝ :=
  ∑ j : Fin r,
    orderedLayerAtomEnergy
      (lower.partition j.castSucc)
      (target.partition j.succ)

theorem orderedFixedTargetAtomEnergy_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (lower target : OrderedPartitionComplex G k r) :
    0 ≤ orderedFixedTargetAtomEnergy lower target := by
  unfold orderedFixedTargetAtomEnergy
  exact Finset.sum_nonneg fun j _ =>
    orderedLayerAtomEnergy_nonneg
      (lower.partition j.castSucc)
      (target.partition j.succ)

theorem orderedFixedTargetAtomEnergy_le_budget
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (lower target : OrderedPartitionComplex G k r) :
    orderedFixedTargetAtomEnergy lower target ≤
      orderedAllRankAtomEnergyBudget k r := by
  unfold orderedFixedTargetAtomEnergy
    orderedAllRankAtomEnergyBudget
  exact Finset.sum_le_sum fun j _ =>
    orderedLayerAtomEnergy_le_card
      (lower.partition j.castSucc)
      (target.partition j.succ)

/-- Refining all lower boundaries raises the energy of a fixed upper atom
family. -/
theorem orderedFixedTargetAtomEnergy_mono
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {fine coarse target :
      OrderedPartitionComplex G k r}
    (hfc : fine.Refines coarse) :
    orderedFixedTargetAtomEnergy coarse target ≤
      orderedFixedTargetAtomEnergy fine target := by
  unfold orderedFixedTargetAtomEnergy
  apply Finset.sum_le_sum
  intro j _
  exact orderedLayerAtomEnergy_mono
    (fun e => hfc j.castSucc e)
    (target.partition j.succ)

/-- Adjacent energy increment with the upper atom family frozen at
`target`. -/
noncomputable def orderedFixedTargetAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (target fine coarse :
      OrderedPartitionComplex G k r) : ℝ :=
  orderedFixedTargetAtomEnergy fine target -
    orderedFixedTargetAtomEnergy coarse target

theorem orderedFixedTargetAtomEnergyGap_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {target fine coarse :
      OrderedPartitionComplex G k r}
    (hfc : fine.Refines coarse) :
    0 ≤ orderedFixedTargetAtomEnergyGap
      target fine coarse :=
  sub_nonneg.mpr
    (orderedFixedTargetAtomEnergy_mono hfc)

/-- Fixed-target adjacent-gap pigeonhole.  This is the exact all-rank
energy argument: the target atom family does not change with the tower
index. -/
theorem exists_adjacent_fixedTargetAtomEnergyGap_le_div
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (tower : ℕ → OrderedPartitionComplex G k r)
    (target : OrderedPartitionComplex G k r)
    (hnested : ∀ n, (tower (n + 1)).Refines (tower n))
    {m : ℕ} (hm : 0 < m) :
    ∃ i : ℕ, i < m ∧
      0 ≤ orderedFixedTargetAtomEnergyGap
        target (tower (i + 1)) (tower i) ∧
      orderedFixedTargetAtomEnergyGap
          target (tower (i + 1)) (tower i) ≤
        orderedAllRankAtomEnergyBudget k r /
          (m : ℝ) := by
  let E : ℕ → ℝ :=
    fun n => orderedFixedTargetAtomEnergy
      (tower n) target
  have htel :
      ∑ i ∈ Finset.range m,
          (E (i + 1) - E i) =
        E m - E 0 :=
    Finset.sum_range_sub E m
  have hsum :
      ∑ i ∈ Finset.range m,
          (E (i + 1) - E i) ≤
        ∑ _i ∈ Finset.range m,
          orderedAllRankAtomEnergyBudget k r /
            (m : ℝ) := by
    rw [htel]
    calc
      E m - E 0 ≤
          orderedAllRankAtomEnergyBudget k r := by
        have h0 :=
          orderedFixedTargetAtomEnergy_nonneg
            (tower 0) target
        have hmBound :=
          orderedFixedTargetAtomEnergy_le_budget
            (tower m) target
        dsimp only [E] at h0 hmBound ⊢
        linarith
      _ =
          ∑ _i ∈ Finset.range m,
            orderedAllRankAtomEnergyBudget k r /
              (m : ℝ) := by
        simp only [Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        field_simp
  obtain ⟨i, hi, hsmall⟩ :=
    Finset.exists_le_of_sum_le
      ⟨0, Finset.mem_range.mpr hm⟩ hsum
  refine ⟨i, Finset.mem_range.mp hi, ?_, ?_⟩
  · exact orderedFixedTargetAtomEnergyGap_nonneg
      (hnested i)
  · exact hsmall

/-- Apply the fixed-target selector to the canonical precomputed tower.
The selected fine endpoint retains its scheduled bounded-test regularity
and its recursive ambient-independent complexity certificate. -/
theorem exists_strongFullOrdered_fixedTarget_pair
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial target : OrderedPartitionComplex G k r)
    (ε : ℕ → OrderedRegularityTolerance r)
    (budget : ℕ → OrderedRegularityBudget r)
    (hε : ∀ n j, 0 ≤ ε n j)
    (hbudget :
      ∀ n, IsOrderedRegularityBudget
        k r (ε n) (budget n))
    {m : ℕ} (hm : 0 < m) :
    ∃ i : ℕ, i < m ∧
      let coarse :=
        strongFullOrderedRegularityTower
          initial ε budget hε hbudget i
      let fine :=
        strongFullOrderedRegularityTower
          initial ε budget hε hbudget (i + 1)
      fine.Refines coarse ∧
      IsFullyPreliminaryOrderedBoundedRegular
        fine (ε i) ∧
      0 ≤ orderedFixedTargetAtomEnergyGap
        target fine coarse ∧
      orderedFixedTargetAtomEnergyGap
          target fine coarse ≤
        orderedAllRankAtomEnergyBudget k r /
          (m : ℝ) ∧
      ∀ (j : Fin r) (e : OrderedFace k j.1),
        FacePartition.complexity
            (fine.partition j.castSucc e) ≤
          strongFullOrderedComplexityFactor
              budget j (i + 1) *
            FacePartition.complexity
              (initial.partition j.castSucc e) := by
  let tower :=
    strongFullOrderedRegularityTower
      initial ε budget hε hbudget
  obtain ⟨i, hi, hgap0, hgap⟩ :=
    exists_adjacent_fixedTargetAtomEnergyGap_le_div
      tower target
      (strongFullOrderedRegularityTower_refines
        initial ε budget hε hbudget)
      hm
  refine ⟨i, hi, ?_, ?_, hgap0, hgap, ?_⟩
  · exact strongFullOrderedRegularityTower_refines
      initial ε budget hε hbudget i
  · exact strongFullOrderedRegularityTower_boundedRegular
      initial ε budget hε hbudget i
  · exact complexity_strongFullOrderedRegularityTower_le
      initial ε budget hε hbudget (i + 1)

/-! ## Moving-upper bridge and the exact loss -/

/-- The tempting moving potential uses each complex as both lower observer
and upper atom target. -/
noncomputable def orderedMovingAtomEnergy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r) : ℝ :=
  orderedFixedTargetAtomEnergy C C

/-- Loss caused solely by replacing the coarse upper atoms by the fine
upper atoms while keeping the coarse lower boundary fixed. -/
noncomputable def orderedUpperRefinementAtomEnergyLoss
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r) : ℝ :=
  orderedFixedTargetAtomEnergy coarse coarse -
    orderedFixedTargetAtomEnergy coarse fine

/-- The frozen-fine-upper energy gap packaged by a coarse/fine complex is
exactly its fixed-target gap with target `fine`. -/
theorem totalAtomEnergyGap_eq_fixedTarget
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r) :
    P.totalAtomEnergyGap =
      orderedFixedTargetAtomEnergyGap
        P.fine P.fine P.coarse := by
  unfold OrderedCoarseFineComplex.totalAtomEnergyGap
    OrderedCoarseFineComplex.layerAtomEnergyGap
    orderedFixedTargetAtomEnergyGap
    orderedFixedTargetAtomEnergy
  rw [Finset.sum_sub_distrib]

/-- Exact bridge identity.  The desired frozen-fine-upper gap is the
adjacent increment of the moving potential plus an upper-refinement loss.
The latter is absent only when the upper atom family is fixed. -/
theorem totalAtomEnergyGap_eq_moving_sub_add_upperLoss
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r) :
    P.totalAtomEnergyGap =
      orderedMovingAtomEnergy P.fine -
        orderedMovingAtomEnergy P.coarse +
      orderedUpperRefinementAtomEnergyLoss
        P.fine P.coarse := by
  rw [totalAtomEnergyGap_eq_fixedTarget]
  unfold orderedFixedTargetAtomEnergyGap
    orderedMovingAtomEnergy
    orderedUpperRefinementAtomEnergyLoss
  ring

/-- The uncontrolled upper-refinement loss has the sharp universal
all-rank atom-energy bound.  This bound is generally order one, so a small
moving adjacent increment alone does not prove strong regularity. -/
theorem orderedUpperRefinementAtomEnergyLoss_le_budget
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r) :
    orderedUpperRefinementAtomEnergyLoss fine coarse ≤
      orderedAllRankAtomEnergyBudget k r := by
  have hleft :=
    orderedFixedTargetAtomEnergy_le_budget
      coarse coarse
  have hright :=
    orderedFixedTargetAtomEnergy_nonneg
      coarse fine
  unfold orderedUpperRefinementAtomEnergyLoss
  linarith

/-- Every partition of a nonempty finite space has at least one atom. -/
theorem one_le_facePartition_complexity
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (P : FacePartition Ω) :
    1 ≤ FacePartition.complexity P := by
  unfold FacePartition.complexity
  exact Finset.card_pos.mpr
    (P.parts_nonempty
      Finset.univ_nonempty.ne_empty)

/-- Sum of all upper-layer atom counts occurring in adjacent rank pairs. -/
noncomputable def orderedAllRankUpperComplexity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r) : ℝ :=
  ∑ j : Fin r,
    ∑ e : OrderedFace k (j.1 + 1),
      (FacePartition.complexity
        (C.partition j.succ e) : ℝ)

/-- The sharp face-count energy budget is no larger than the explicit
upper-atom complexity factor. -/
theorem orderedAllRankAtomEnergyBudget_le_upperComplexity
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r) :
    orderedAllRankAtomEnergyBudget k r ≤
      orderedAllRankUpperComplexity C := by
  unfold orderedAllRankAtomEnergyBudget
    orderedAllRankUpperComplexity
  apply Finset.sum_le_sum
  intro j _
  calc
    (Fintype.card
        (OrderedFace k (j.1 + 1)) : ℝ) =
        ∑ _e : OrderedFace k (j.1 + 1),
          (1 : ℝ) := by simp
    _ ≤
        ∑ e : OrderedFace k (j.1 + 1),
          (FacePartition.complexity
            (C.partition j.succ e) : ℝ) := by
      apply Finset.sum_le_sum
      intro e _
      exact_mod_cast
        one_le_facePartition_complexity
          (C.partition j.succ e)

/-- Complexity-form bridge bound.  It is weaker than the sharp face budget
but displays the exact finite aggregation factor available from a
precomputed tower complexity schedule. -/
theorem orderedUpperRefinementAtomEnergyLoss_le_upperComplexity
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r) :
    orderedUpperRefinementAtomEnergyLoss fine coarse ≤
      orderedAllRankUpperComplexity fine :=
  (orderedUpperRefinementAtomEnergyLoss_le_budget
    fine coarse).trans
      (orderedAllRankAtomEnergyBudget_le_upperComplexity
        fine)

/-- Consequently the naive moving-potential selector loses a whole
all-rank energy budget when converted to the desired frozen-fine target. -/
theorem totalAtomEnergyGap_le_moving_sub_add_budget
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r) :
    P.totalAtomEnergyGap ≤
      orderedMovingAtomEnergy P.fine -
        orderedMovingAtomEnergy P.coarse +
      orderedAllRankAtomEnergyBudget k r := by
  have hidentity :=
    totalAtomEnergyGap_eq_moving_sub_add_upperLoss P
  have hloss :
      orderedUpperRefinementAtomEnergyLoss
          P.fine P.coarse ≤
        orderedAllRankAtomEnergyBudget k r :=
    orderedUpperRefinementAtomEnergyLoss_le_budget
      P.fine P.coarse
  linarith

end Wikipedia.SzemeredisTheorem
