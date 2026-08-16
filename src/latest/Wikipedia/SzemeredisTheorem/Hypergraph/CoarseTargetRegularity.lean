import Wikipedia.SzemeredisTheorem.Hypergraph.CoarseAtomBridge
import Wikipedia.SzemeredisTheorem.Hypergraph.StrongOrderedComplexRegularity

/-!
# Strong ordered regularity with coarse upper targets

The usual top-down strong certificate freezes the final fine upper layer
while selecting the adjacent coarse/fine lower layers.  For coarse
configuration counting and cleaning, the more useful target is instead the
final coarse upper layer.

This file carries out that variant directly.  At the current top rank we
select a coarse/fine lower pair against the unchanged top layer.  The
recursive call is then made with the selected *coarse* lower layer as its
top layer.  After recursion, only the fine prefix's top layer is replaced
by the selected fine layer.  Thus every lower-rank regularity statement and
energy gap keeps the recursively selected coarse upper layer as its target.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A top-down strong regularity certificate in which the observing fine
lower boundary is regular against the final coarse upper layer, and the
rankwise energy gap is measured against that same coarse upper layer. -/
structure CoarseTargetOrderedComplexRegularityCertificate
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
  mixedRegular :
    ∀ j : Fin r,
      IsPreliminaryOrderedRegular
        (fine.partition j.castSucc)
        (coarse.partition j.succ)
        (ε j (index j))
  gap_nonneg :
    ∀ j : Fin r,
      0 ≤
        orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (coarse.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (coarse.partition j.succ)
  gap_le :
    ∀ j : Fin r,
      orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (coarse.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (coarse.partition j.succ) ≤
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

namespace CoarseTargetOrderedComplexRegularityCertificate

/-- Forget the quantitative certificate and retain its compatible
coarse/fine complexes. -/
def toCoarseFine
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial ε budget length) :
    OrderedCoarseFineComplex G k r where
  coarse := R.coarse
  fine := R.fine
  refines := R.refines

/-- The fine output also refines the original input complex. -/
theorem fine_refines_initial
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial ε budget length) :
    R.fine.Refines initial :=
  OrderedPartitionComplex.Refines.trans
    R.refines R.coarse_refines_initial

end CoarseTargetOrderedComplexRegularityCertificate

/-! ## Existence by downward rank induction -/

/-- Top-down construction of a strong certificate whose upper target at
every adjacent rank is the final coarse layer. -/
theorem CoarseTargetOrderedComplexRegularityCertificate.nonempty
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
      (CoarseTargetOrderedComplexRegularityCertificate
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
        mixedRegular := ?_
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
        initial.dropTop.withTopLayer topChoice.coarse
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
        lowerCertificate.coarse
      let finePrefix :
          OrderedPartitionComplex G k r :=
        lowerCertificate.fine.withTopLayer topChoice.fine
      let coarse :
          OrderedPartitionComplex G k (r + 1) :=
        coarsePrefix.appendTop upper
      let fine :
          OrderedPartitionComplex G k (r + 1) :=
        finePrefix.appendTop upper
      let index : Fin (r + 1) → ℕ :=
        fun j =>
          Fin.lastCases topChoice.index
            lowerCertificate.index j
      have hlowerFineTop :
          lowerCertificate.fine.topLayer =
            topChoice.coarse := by
        calc
          lowerCertificate.fine.topLayer =
              prepared.topLayer :=
            lowerCertificate.fine_topLayer_eq
          _ = topChoice.coarse :=
            OrderedPartitionComplex.topLayer_withTopLayer
              initial.dropTop topChoice.coarse
      have hlowerCoarseTop :
          lowerCertificate.coarse.topLayer =
            topChoice.coarse := by
        calc
          lowerCertificate.coarse.topLayer =
              prepared.topLayer :=
            lowerCertificate.coarse_topLayer_eq
          _ = topChoice.coarse :=
            OrderedPartitionComplex.topLayer_withTopLayer
              initial.dropTop topChoice.coarse
      refine ⟨{
        index := index
        coarse := coarse
        fine := fine
        refines := ?_
        coarse_refines_initial := ?_
        coarse_topLayer_eq := ?_
        fine_topLayer_eq := ?_
        index_lt := ?_
        mixedRegular := ?_
        gap_nonneg := ?_
        gap_le := ?_
        coarse_complexity := ?_
        fine_complexity := ?_ }⟩
      · have hprefix :
            finePrefix.Refines coarsePrefix := by
          intro q e
          cases q using Fin.lastCases with
          | last =>
              simp only [finePrefix, coarsePrefix,
                OrderedPartitionComplex.withTopLayer,
                Fin.lastCases_last]
              change OrderedFace k r at e
              have heq :
                  lowerCertificate.coarse.partition
                      (Fin.last r) e =
                    topChoice.coarse e :=
                congrFun hlowerCoarseTop e
              rw [heq]
              exact topChoice.refines e
          | cast i =>
              simp only [finePrefix, coarsePrefix,
                OrderedPartitionComplex.withTopLayer,
                Fin.lastCases_castSucc]
              exact lowerCertificate.refines
                i.castSucc e
        exact OrderedPartitionComplex.appendTop_refines
          hprefix
          (OrderedFacePartitionRefines.refl upper)
      · have hprepared :
            prepared.Refines initial.dropTop := by
          exact OrderedPartitionComplex.withTopLayer_refines
            initial.dropTop topChoice.coarse
            (by
              simpa only [lowerInitial] using
                topChoice.coarse_refines_initial)
        have hprefix :
            coarsePrefix.Refines initial.dropTop :=
          OrderedPartitionComplex.Refines.trans
            lowerCertificate.coarse_refines_initial
            hprepared
        have happend :=
          OrderedPartitionComplex.appendTop_refines
            hprefix
            (OrderedFacePartitionRefines.refl upper)
        simpa [coarse, coarsePrefix, upper] using happend
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
            simp only [fine, finePrefix, coarse,
              coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.appendTop_partition_last,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_last, Fin.succ_last,
              index, Fin.lastCases_last]
            exact topChoice.fine_regular
        | cast i =>
            have hregular :=
              lowerCertificate.mixedRegular i
            simp only [fine, finePrefix, coarse,
              coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc, Fin.succ_castSucc,
              index, Fin.lastCases_castSucc]
            change
              @IsPreliminaryOrderedRegular
                G _ _ k i.1
                (lowerCertificate.fine.partition
                  i.castSucc)
                (lowerCertificate.coarse.partition
                  i.succ)
                (ε i.castSucc
                  (lowerCertificate.index i))
            exact hregular
      · intro q
        cases q using Fin.lastCases with
        | last =>
            have hgap := topChoice.gap_nonneg
            simp only [fine, finePrefix, coarse,
              coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.appendTop_partition_last,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_last, Fin.succ_last]
            change
              0 ≤
                orderedLayerAtomEnergy
                    topChoice.fine upper -
                  orderedLayerAtomEnergy
                    lowerCertificate.coarse.topLayer
                    upper
            rw [hlowerCoarseTop]
            exact hgap
        | cast i =>
            have hgap :=
              lowerCertificate.gap_nonneg i
            simp only [fine, finePrefix, coarse,
              coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc, Fin.succ_castSucc]
            convert hgap using 1
      · intro q
        cases q using Fin.lastCases with
        | last =>
            have hgap := topChoice.gap_le
            simp only [fine, finePrefix, coarse,
              coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.appendTop_partition_last,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_last, Fin.succ_last]
            change
              orderedLayerAtomEnergy
                    topChoice.fine upper -
                  orderedLayerAtomEnergy
                    lowerCertificate.coarse.topLayer
                    upper ≤
                (Fintype.card
                  (OrderedFace k (r + 1)) : ℝ) /
                    (length (Fin.last r) : ℝ)
            rw [hlowerCoarseTop]
            exact hgap
        | cast i =>
            have hgap :=
              lowerCertificate.gap_le i
            simp only [fine, finePrefix, coarse,
              coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc, Fin.succ_castSucc,
              lengthLower]
            convert hgap using 1 <;> rfl
      · intro q
        cases q using Fin.lastCases with
        | last =>
            intro e
            change OrderedFace k r at e
            have hcomplexity :=
              topChoice.coarse_complexity e
            simp only [coarse, coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              index, Fin.lastCases_last]
            change
              FacePartition.complexity
                  (lowerCertificate.coarse.partition
                    (Fin.last r) e) ≤
                fixedUpperLayerComplexityFactor
                    r (budget (Fin.last r))
                    topChoice.index *
                  FacePartition.complexity
                    (initial.partition
                      (Fin.last r).castSucc e)
            have heq :
                lowerCertificate.coarse.partition
                    (Fin.last r) e =
                  topChoice.coarse e :=
              congrFun hlowerCoarseTop e
            rw [heq]
            exact hcomplexity
        | cast i =>
            intro e
            change OrderedFace k i.1 at e
            have hcomplexity :=
              lowerCertificate.coarse_complexity i e
            simp only [coarse, coarsePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
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
            simp only [fine, finePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_last,
              index, Fin.lastCases_last]
            exact hcomplexity
        | cast i =>
            intro e
            change OrderedFace k i.1 at e
            have hcomplexity :=
              lowerCertificate.fine_complexity i e
            simp only [fine, finePrefix,
              OrderedPartitionComplex.appendTop_partition_castSucc,
              OrderedPartitionComplex.withTopLayer,
              Fin.lastCases_castSucc,
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

/-! ## Total coarse-target gap -/

namespace OrderedCoarseFineComplex

/-- Sum of the rankwise energy gaps obtained by freezing the coarse upper
layer at every rank. -/
noncomputable def totalCoarseUpperAtomEnergyGap
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r) : ℝ :=
  ∑ j : Fin r, P.coarseUpperLayerAtomEnergyGap j

/-- The total coarse-upper gap of any coarse/fine complex is nonnegative. -/
theorem totalCoarseUpperAtomEnergyGap_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r) :
    0 ≤ P.totalCoarseUpperAtomEnergyGap := by
  unfold totalCoarseUpperAtomEnergyGap
  exact Finset.sum_nonneg fun j _ =>
    sub_nonneg.mpr
      (orderedLayerAtomEnergy_mono
        (fun e => P.refines j.castSucc e)
        (P.coarse.partition j.succ))

end OrderedCoarseFineComplex

namespace CoarseTargetOrderedComplexRegularityCertificate

/-- The selected rankwise coarse-target gaps add up to the reciprocal
length bound, with no upper-complexity conversion factor. -/
theorem totalCoarseUpperAtomEnergyGap_le_sum_div
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial ε budget length) :
    R.toCoarseFine.totalCoarseUpperAtomEnergyGap ≤
      ∑ j : Fin r,
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
            (length j : ℝ) := by
  unfold OrderedCoarseFineComplex.totalCoarseUpperAtomEnergyGap
    OrderedCoarseFineComplex.coarseUpperLayerAtomEnergyGap
    toCoarseFine
  exact Finset.sum_le_sum fun j _ => R.gap_le j

/-- Nonnegativity of the selected total coarse-target gap. -/
theorem totalCoarseUpperAtomEnergyGap_nonneg
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial ε budget length) :
    0 ≤ R.toCoarseFine.totalCoarseUpperAtomEnergyGap :=
  R.toCoarseFine.totalCoarseUpperAtomEnergyGap_nonneg

end CoarseTargetOrderedComplexRegularityCertificate

/-- Existential form of coarse-target strong ordered regularity, including
the total reciprocal energy-gap estimate. -/
theorem exists_coarseTargetOrderedComplexRegularity
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
    ∃ R : CoarseTargetOrderedComplexRegularityCertificate
        G k r initial ε budget length,
      R.toCoarseFine.totalCoarseUpperAtomEnergyGap ≤
        ∑ j : Fin r,
          (Fintype.card
            (OrderedFace k (j.1 + 1)) : ℝ) /
              (length j : ℝ) := by
  obtain ⟨R⟩ :=
    CoarseTargetOrderedComplexRegularityCertificate.nonempty
      initial ε budget length hε hlong hlength
  exact
    ⟨R,
      R.totalCoarseUpperAtomEnergyGap_le_sum_div⟩

end Wikipedia.SzemeredisTheorem
