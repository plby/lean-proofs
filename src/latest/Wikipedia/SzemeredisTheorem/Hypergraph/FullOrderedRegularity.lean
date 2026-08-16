import Wikipedia.SzemeredisTheorem.Hypergraph.PreliminaryOrderedRegularity

/-!
# All-rank ordered preliminary regularity

The preliminary energy increment acts on one adjacent pair of ranks: it
refines the shared rank-`j` partitions while keeping rank `j + 1` fixed.
This file assembles those refinements into one compatible partition complex.
The ranks are processed from top to bottom.  Consequently, once the pair
`(j, j + 1)` has been regularized, later steps only change lower ranks and
cannot invalidate it.

The resulting theorem has a separate tolerance and finite energy budget at
every adjacent pair.  It returns an explicit stopping-time schedule, a
refining complex which is preliminarily regular at every rank, and the
ambient-independent complexity multiplier at every non-top layer.

We also package coarse/fine complexes and their boundary atom-energy gap.
The gap uses the atoms of the fine upper layer at both endpoints; with that
choice, refinement of the lower boundary gives honest monotonicity.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace OrderedPartitionComplex

/-- The top shared-face layer of a bounded ordered partition complex. -/
def topLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r) :
    OrderedFacePartitionSystem G k r :=
  C.partition (Fin.last r)

/-- Forget the top layer of a nontrivial ordered partition complex. -/
def dropTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k (r + 1)) :
    OrderedPartitionComplex G k r where
  partition j := C.partition j.castSucc

/-- Append one new top layer to an ordered partition complex. -/
def appendTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    OrderedPartitionComplex G k (r + 1) where
  partition j :=
    Fin.lastCases top (fun i => C.partition i) j

/-- Replace only the top layer of an ordered partition complex. -/
def withTopLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r) :
    OrderedPartitionComplex G k r where
  partition j :=
    Fin.lastCases top (fun i => C.partition i.castSucc) j

@[simp]
theorem topLayer_appendTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    (appendTop C top).topLayer = top := by
  simp [topLayer, appendTop]

@[simp]
theorem dropTop_appendTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    (appendTop C top).dropTop = C := by
  cases C with
  | mk partition =>
      simp [dropTop, appendTop]

@[simp]
theorem topLayer_withTopLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r) :
    (withTopLayer C top).topLayer = top := by
  simp [topLayer, withTopLayer]

@[simp]
theorem withTopLayer_partition_castSucc
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k (r + 1))
    (top : OrderedFacePartitionSystem G k (r + 1))
    (j : Fin (r + 1)) :
    (withTopLayer C top).partition j.castSucc =
      C.partition j.castSucc := by
  simp [withTopLayer]

@[simp]
theorem appendTop_partition_castSucc
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1))
    (j : Fin (r + 1)) :
    (appendTop C top).partition j.castSucc =
      C.partition j := by
  simp [appendTop]

@[simp]
theorem appendTop_partition_last
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    (appendTop C top).partition (Fin.last (r + 1)) =
      top := by
  simp [appendTop]

@[simp]
theorem withTopLayer_partition_castSucc_general
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r)
    (i : Fin r) :
    (withTopLayer C top).partition i.castSucc =
      C.partition i.castSucc := by
  simp [withTopLayer]

@[simp]
theorem appendTop_dropTop_topLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k (r + 1)) :
    appendTop C.dropTop C.topLayer = C := by
  cases C with
  | mk partition =>
      simp only [dropTop, topLayer, appendTop]
      congr 1
      funext j e
      cases j using Fin.lastCases <;>
        simp only [Fin.lastCases_last,
          Fin.lastCases_castSucc]

/-- Dropping the top layer preserves pointwise refinement. -/
theorem dropTop_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {fine coarse : OrderedPartitionComplex G k (r + 1)}
    (hfc : fine.Refines coarse) :
    fine.dropTop.Refines coarse.dropTop := by
  intro j e
  exact hfc j.castSucc e

/-- Appending pointwise-refining top and lower layers preserves refinement
of the whole complex. -/
theorem appendTop_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {fine coarse : OrderedPartitionComplex G k r}
    {fineTop coarseTop :
      OrderedFacePartitionSystem G k (r + 1)}
    (hfc : fine.Refines coarse)
    (htop : OrderedFacePartitionRefines fineTop coarseTop) :
    (appendTop fine fineTop).Refines
      (appendTop coarse coarseTop) := by
  intro j e
  cases j using Fin.lastCases with
  | last =>
      simp only [appendTop, Fin.lastCases_last]
      change OrderedFace k (r + 1) at e
      change fineTop e ≤ coarseTop e
      exact htop e
  | cast i =>
      simp only [appendTop, Fin.lastCases_castSucc]
      change OrderedFace k i.1 at e
      change fine.partition i e ≤ coarse.partition i e
      exact hfc i e

/-- Replacing the top layer by a refinement refines the original complex
and leaves every lower layer unchanged. -/
theorem withTopLayer_refines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r)
    (htop : OrderedFacePartitionRefines top C.topLayer) :
    (withTopLayer C top).Refines C := by
  intro j e
  cases j using Fin.lastCases with
  | last =>
      simp only [withTopLayer, Fin.lastCases_last]
      change OrderedFace k r at e
      change top e ≤ C.partition (Fin.last r) e
      exact htop e
  | cast i =>
      simp only [withTopLayer, Fin.lastCases_castSucc]
      exact le_rfl

end OrderedPartitionComplex

/-! ## Coarse/fine complexes and honest atom-energy gaps -/

/-- A pair of compatible ordered partition complexes, with the fine complex
refining the coarse one at every genuine face. -/
structure OrderedCoarseFineComplex
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) where
  coarse : OrderedPartitionComplex G k r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse

namespace OrderedCoarseFineComplex

/-- Coarse/fine compatibility descends to every induced boundary
partition. -/
theorem boundaryRefines
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r j : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (hj : j < r)
    (e : OrderedFace k (j + 1)) :
    P.fine.boundary hj e ≤ P.coarse.boundary hj e :=
  OrderedPartitionComplex.boundary_mono P.refines hj e

/-- The frozen-upper atom-energy increment at one genuine upper face. -/
noncomputable def faceAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) : ℝ :=
  orderedAtomEnergy
      (P.fine.partition j.castSucc) e
      (P.fine.partition j.succ e) -
    orderedAtomEnergy
      (P.coarse.partition j.castSucc) e
      (P.fine.partition j.succ e)

/-- Every local frozen-upper atom-energy gap is nonnegative. -/
theorem faceAtomEnergyGap_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    0 ≤ P.faceAtomEnergyGap j e := by
  apply sub_nonneg.mpr
  exact orderedAtomEnergy_mono
    (fun f => P.refines j.castSucc f)
    e (P.fine.partition j.succ e)

/-- At rank `j`, compare coarse and fine lower boundaries against the same
family of atoms: the atoms of the fine rank-`j+1` layer.  Freezing this upper
family is what makes the gap monotone. -/
noncomputable def layerAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) : ℝ :=
  orderedLayerAtomEnergy
      (P.fine.partition j.castSucc)
      (P.fine.partition j.succ) -
    orderedLayerAtomEnergy
      (P.coarse.partition j.castSucc)
      (P.fine.partition j.succ)

/-- A layer gap is exactly the sum of its local face gaps. -/
theorem layerAtomEnergyGap_eq_sum_face
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) :
    P.layerAtomEnergyGap j =
      ∑ e : OrderedFace k (j.1 + 1),
        P.faceAtomEnergyGap j e := by
  unfold layerAtomEnergyGap faceAtomEnergyGap
    orderedLayerAtomEnergy
  rw [Finset.sum_sub_distrib]
  rfl

/-- Every frozen-upper-family atom-energy gap is nonnegative. -/
theorem layerAtomEnergyGap_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) :
    0 ≤ P.layerAtomEnergyGap j := by
  apply sub_nonneg.mpr
  exact orderedLayerAtomEnergy_mono
    (fun e => P.refines j.castSucc e)
    (P.fine.partition j.succ)

/-- A single rank gap is bounded by the number of genuine upper faces. -/
theorem layerAtomEnergyGap_le_card
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) :
    P.layerAtomEnergyGap j ≤
      (Fintype.card (OrderedFace k (j.1 + 1)) : ℝ) := by
  have hfine :=
    orderedLayerAtomEnergy_le_card
      (P.fine.partition j.castSucc)
      (P.fine.partition j.succ)
  have hcoarse :=
    orderedLayerAtomEnergy_nonneg
      (P.coarse.partition j.castSucc)
      (P.fine.partition j.succ)
  have hfine' :
      orderedLayerAtomEnergy
          (P.fine.partition j.castSucc)
          (P.fine.partition j.succ) ≤
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) := by
    convert hfine using 1
    rfl
  unfold layerAtomEnergyGap
  linarith

/-- Total frozen-upper-family gap over every adjacent pair of ranks. -/
noncomputable def totalAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r) : ℝ :=
  ∑ j : Fin r, P.layerAtomEnergyGap j

theorem totalAtomEnergyGap_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r) :
    0 ≤ P.totalAtomEnergyGap := by
  exact Finset.sum_nonneg fun j _ =>
    P.layerAtomEnergyGap_nonneg j

/-- One local face gap is bounded by its enclosing layer gap. -/
theorem faceAtomEnergyGap_le_layer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    P.faceAtomEnergyGap j e ≤
      P.layerAtomEnergyGap j := by
  rw [P.layerAtomEnergyGap_eq_sum_face j]
  exact Finset.single_le_sum
    (fun f _ => P.faceAtomEnergyGap_nonneg j f)
    (Finset.mem_univ e)

/-- One layer gap is bounded by the total all-rank gap. -/
theorem layerAtomEnergyGap_le_total
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) :
    P.layerAtomEnergyGap j ≤
      P.totalAtomEnergyGap := by
  unfold totalAtomEnergyGap
  exact Finset.single_le_sum
    (fun i _ => P.layerAtomEnergyGap_nonneg i)
    (Finset.mem_univ j)

/-- Every local face gap is bounded by the total all-rank gap. -/
theorem faceAtomEnergyGap_le_total
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    P.faceAtomEnergyGap j e ≤
      P.totalAtomEnergyGap :=
  (P.faceAtomEnergyGap_le_layer j e).trans
    (P.layerAtomEnergyGap_le_total j)

theorem totalAtomEnergyGap_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r) :
    P.totalAtomEnergyGap ≤
      ∑ j : Fin r,
        (Fintype.card (OrderedFace k (j.1 + 1)) : ℝ) := by
  exact Finset.sum_le_sum fun j _ =>
    P.layerAtomEnergyGap_le_card j

end OrderedCoarseFineComplex

/-! ## Rank schedules and simultaneous preliminary regularity -/

/-- One tolerance for every adjacent rank pair `(j, j + 1)`. -/
abbrev OrderedRegularityTolerance (r : ℕ) := Fin r → ℝ

/-- One finite iteration budget for every adjacent rank pair. -/
abbrev OrderedRegularityBudget (r : ℕ) := Fin r → ℕ

/-- The actual stopping index selected at every adjacent rank pair. -/
abbrev OrderedRegularityStepSchedule (r : ℕ) := Fin r → ℕ

/-- Every adjacent rank pair in a complex is preliminarily regular. -/
def IsFullyPreliminaryOrderedRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (ε : OrderedRegularityTolerance r) : Prop :=
  ∀ j : Fin r,
    IsPreliminaryOrderedRegular
      (C.partition j.castSucc)
      (C.partition j.succ)
      (ε j)

/-- The per-rank budgets strictly exceed the corresponding atom-energy
ceilings after division by the squared tolerances. -/
def IsOrderedRegularityBudget
    (k r : ℕ)
    (ε : OrderedRegularityTolerance r)
    (m : OrderedRegularityBudget r) : Prop :=
  ∀ j : Fin r,
    (Fintype.card (OrderedFace k (j.1 + 1)) : ℝ) <
      (m j : ℝ) * (ε j) ^ 2

/-- The explicit ambient-independent complexity certificate associated to
a stopping-time schedule.  The top layer is deliberately excluded: it is
preserved exactly. -/
def HasOrderedRegularityComplexityBound
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (fine coarse : OrderedPartitionComplex G k r)
    (steps : OrderedRegularityStepSchedule r) : Prop :=
  ∀ (j : Fin r) (e : OrderedFace k j.1),
    FacePartition.complexity
        (fine.partition j.castSucc e) ≤
      (2 ^ (j.1 + 1)) ^ (steps j) *
        FacePartition.complexity
          (coarse.partition j.castSucc e)

/-! ## The top-down all-rank construction -/

/-- Complete output data for the all-rank preliminary regularity pass. -/
structure FullOrderedRegularityCertificate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (coarse : OrderedPartitionComplex G k r)
    (ε : OrderedRegularityTolerance r)
    (m : OrderedRegularityBudget r) where
  steps : OrderedRegularityStepSchedule r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse
  topLayer_eq :
    fine.topLayer = coarse.topLayer
  steps_lt : ∀ j, steps j < m j
  regular :
    IsFullyPreliminaryOrderedRegular fine ε
  complexity :
    HasOrderedRegularityComplexityBound
      fine coarse steps

/-- A top-down pass combines the adjacent-rank energy increments into one
compatible complex.  Each non-top rank is changed exactly during its own
stage.  Thus its final complexity is bounded by its own stopping-time
multiplier, without any factor involving `Fintype.card G`. -/
theorem exists_fullOrderedRegularityCertificate
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (ε : OrderedRegularityTolerance r)
    (m : OrderedRegularityBudget r)
    (hε : ∀ j, 0 ≤ ε j)
    (hbudget : IsOrderedRegularityBudget k r ε m) :
    Nonempty (FullOrderedRegularityCertificate C ε m) := by
  induction r with
  | zero =>
      let steps : OrderedRegularityStepSchedule 0 :=
        fun j => Fin.elim0 j
      refine ⟨{
        steps := steps
        fine := C
        refines := OrderedPartitionComplex.Refines.refl C
        topLayer_eq := rfl
        steps_lt := ?_
        regular := ?_
        complexity := ?_ }⟩
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
      · intro j
        exact Fin.elim0 j
  | succ r ih =>
      let lowerComplex : OrderedPartitionComplex G k r :=
        C.dropTop
      let upper : OrderedFacePartitionSystem G k (r + 1) :=
        C.topLayer
      have hεtop : 0 ≤ ε (Fin.last r) :=
        hε (Fin.last r)
      have hbudgetTop :
          (Fintype.card (OrderedFace k (r + 1)) : ℝ) <
            (m (Fin.last r) : ℝ) *
              (ε (Fin.last r)) ^ 2 := by
        have hb := hbudget (Fin.last r)
        change
          (Fintype.card (OrderedFace k (r + 1)) : ℝ) <
            (m (Fin.last r) : ℝ) *
              (ε (Fin.last r)) ^ 2 at hb
        exact hb
      obtain ⟨n, lower, hn, hlowerRefines,
          hlowerRegular, hlowerComplexity⟩ :=
        exists_preliminaryOrderedRegular_refinement_with_complexity_before
          lowerComplex.topLayer upper hεtop hbudgetTop
      let prepared : OrderedPartitionComplex G k r :=
        lowerComplex.withTopLayer lower
      have hpreparedRefines :
          prepared.Refines lowerComplex := by
        exact OrderedPartitionComplex.withTopLayer_refines
          lowerComplex lower hlowerRefines
      let εlower : OrderedRegularityTolerance r :=
        fun j => ε j.castSucc
      let mlower : OrderedRegularityBudget r :=
        fun j => m j.castSucc
      have hεlower : ∀ j, 0 ≤ εlower j := by
        intro j
        exact hε j.castSucc
      have hbudgetLower :
          IsOrderedRegularityBudget k r εlower mlower := by
        intro j
        exact hbudget j.castSucc
      obtain ⟨lowerCertificate⟩ :=
        ih prepared εlower mlower hεlower hbudgetLower
      let fine : OrderedPartitionComplex G k (r + 1) :=
        lowerCertificate.fine.appendTop upper
      let steps : OrderedRegularityStepSchedule (r + 1) :=
        fun j =>
          Fin.lastCases n lowerCertificate.steps j
      have hlowerCertificateTop :
          lowerCertificate.fine.topLayer = lower := by
        calc
          lowerCertificate.fine.topLayer =
              prepared.topLayer :=
            lowerCertificate.topLayer_eq
          _ = lower :=
            OrderedPartitionComplex.topLayer_withTopLayer
              lowerComplex lower
      refine ⟨{
        steps := steps
        fine := fine
        refines := ?_
        topLayer_eq := ?_
        steps_lt := ?_
        regular := ?_
        complexity := ?_ }⟩
      · have hprefixFinal :
            lowerCertificate.fine.Refines lowerComplex :=
          OrderedPartitionComplex.Refines.trans
            lowerCertificate.refines hpreparedRefines
        have happended :
            fine.Refines
              (lowerComplex.appendTop upper) := by
          exact OrderedPartitionComplex.appendTop_refines
            hprefixFinal
            (OrderedFacePartitionRefines.refl upper)
        simpa [fine, lowerComplex, upper] using happended
      · simp [fine, upper]
      · intro j
        cases j using Fin.lastCases with
        | last =>
            simpa [steps] using hn
        | cast i =>
            simpa [steps] using
              lowerCertificate.steps_lt i
      · intro j
        cases j using Fin.lastCases with
        | last =>
            have htop :
                IsPreliminaryOrderedRegular
                  lowerCertificate.fine.topLayer
                  upper (ε (Fin.last r)) := by
              rw [hlowerCertificateTop]
              exact hlowerRegular
            simp only [fine,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.appendTop_partition_last,
              Fin.succ_last]
            change
              @IsPreliminaryOrderedRegular
                G _ _ k r
                (lowerCertificate.fine.partition
                  (Fin.last r))
                upper (ε (Fin.last r))
            exact htop
        | cast i =>
            have hi := lowerCertificate.regular i
            simp only [fine, εlower,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              Fin.succ_castSucc]
            change
              @IsPreliminaryOrderedRegular
                G _ _ k i.1
                (lowerCertificate.fine.partition i.castSucc)
                (lowerCertificate.fine.partition i.succ)
                (ε i.castSucc)
            exact hi
      · intro j
        cases j using Fin.lastCases with
        | last =>
            intro e
            have htop :
                FacePartition.complexity
                    (lowerCertificate.fine.topLayer e) ≤
                  (2 ^ (r + 1)) ^ n *
                    FacePartition.complexity
                      (lowerComplex.topLayer e) := by
              rw [hlowerCertificateTop]
              exact hlowerComplexity e
            simp only [fine, steps,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              Fin.lastCases_last]
            change OrderedFace k r at e
            change
              FacePartition.complexity
                  (lowerCertificate.fine.partition
                    (Fin.last r) e) ≤
                (2 ^ (r + 1)) ^ n *
                  FacePartition.complexity
                    (C.partition
                      (Fin.last r).castSucc e)
            exact htop
        | cast i =>
            intro e
            change OrderedFace k i.1 at e
            have hi := lowerCertificate.complexity i e
            simp only [prepared, lowerComplex,
              OrderedPartitionComplex.withTopLayer,
              OrderedPartitionComplex.dropTop,
              Fin.lastCases_castSucc] at hi
            simp only [fine, steps, εlower, mlower,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              Fin.lastCases_castSucc]
            change
              FacePartition.complexity
                  (lowerCertificate.fine.partition
                    i.castSucc e) ≤
                (2 ^ (i.1 + 1)) ^
                    lowerCertificate.steps i *
                  FacePartition.complexity
                    (C.partition
                      i.castSucc.castSucc e)
            exact hi

/-- Existential form of the all-rank fixed-budget theorem. -/
theorem exists_fullyPreliminaryOrderedRegular_refinement
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (ε : OrderedRegularityTolerance r)
    (m : OrderedRegularityBudget r)
    (hε : ∀ j, 0 ≤ ε j)
    (hbudget : IsOrderedRegularityBudget k r ε m) :
    ∃ (steps : OrderedRegularityStepSchedule r)
        (fine : OrderedPartitionComplex G k r),
      fine.Refines C ∧
      fine.topLayer = C.topLayer ∧
      (∀ j, steps j < m j) ∧
      IsFullyPreliminaryOrderedRegular fine ε ∧
      HasOrderedRegularityComplexityBound
        fine C steps := by
  obtain ⟨certificate⟩ :=
    exists_fullOrderedRegularityCertificate
      C ε m hε hbudget
  exact ⟨certificate.steps, certificate.fine,
    certificate.refines, certificate.topLayer_eq,
    certificate.steps_lt, certificate.regular,
    certificate.complexity⟩

end Wikipedia.SzemeredisTheorem
