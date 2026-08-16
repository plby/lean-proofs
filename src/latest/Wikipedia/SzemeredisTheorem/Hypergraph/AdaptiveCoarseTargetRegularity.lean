import Wikipedia.SzemeredisTheorem.Hypergraph.CoarseTargetRegularity

/-!
# Adaptive top-down coarse-target regularity

The fixed-vector coarse-target theorem chooses one tower index at every
rank, but fixes all tower lengths before any of those choices are known.
For the removal argument this is unnecessarily rigid: after the top-rank
index has been selected, the horizon at the next rank may be chosen as a
function of that index, and so on.

This file packages such data as a finite decision tree.  A node contains
the tolerance, budget, and horizon for the current (highest remaining)
rank, together with one subtree for every admissible index.  Thus a branch
is genuinely path dependent.  A landing is a root-to-leaf branch.  Its
data are flattened in the bottom-up rank order used by
`CoarseTargetOrderedComplexRegularityCertificate`.
-/

namespace Wikipedia.SzemeredisTheorem

/-- A finite tree of top-down regularity schedules.

At a node of height `r + 1`, the displayed schedule is used at rank `r`.
After an index `i : Fin length` is selected, `next i` is the schedule for
the remaining ranks.  In particular, every later horizon may depend on all
earlier selected indices. -/
inductive AdaptiveCoarseTargetSchedule (k : ℕ) : ℕ → Type
  | nil : AdaptiveCoarseTargetSchedule k 0
  | node {r : ℕ}
      (tolerance : ℕ → ℝ)
      (budget : ℕ → ℕ)
      (length : ℕ)
      (next : Fin length → AdaptiveCoarseTargetSchedule k r) :
      AdaptiveCoarseTargetSchedule k (r + 1)

namespace AdaptiveCoarseTargetSchedule

/-- The local energy-increment hypotheses hold at every node of an
adaptive schedule tree. -/
def IsAdmissible {k r : ℕ} :
    AdaptiveCoarseTargetSchedule k r → Prop
  | .nil => True
  | .node tolerance budget length next =>
      (∀ n, 0 ≤ tolerance n) ∧
      (∀ n,
        (Fintype.card (OrderedFace k r) : ℝ) <
          (budget n : ℝ) * (tolerance n) ^ 2) ∧
      0 < length ∧
      ∀ i, (next i).IsAdmissible

/-- A root-to-leaf landing in an adaptive schedule tree. -/
inductive Landing {k : ℕ} :
    {r : ℕ} → AdaptiveCoarseTargetSchedule k r → Type
  | nil : Landing (.nil : AdaptiveCoarseTargetSchedule k 0)
  | node {r : ℕ}
      {tolerance : ℕ → ℝ}
      {budget : ℕ → ℕ}
      {length : ℕ}
      {next : Fin length → AdaptiveCoarseTargetSchedule k r}
      (index : Fin length)
      (lower : Landing (next index)) :
      Landing (.node tolerance budget length next)

namespace Landing

/-- Flatten the tolerances along a landing into bottom-up rank order. -/
def tolerance {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    (j : Fin r) → ℕ → ℝ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node (tolerance := tolerance) _ lower =>
      fun j => Fin.lastCases tolerance lower.tolerance j

/-- Flatten the tower budgets along a landing into bottom-up rank order. -/
def budget {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    (j : Fin r) → ℕ → ℕ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node (budget := budget) _ lower =>
      fun j => Fin.lastCases budget lower.budget j

/-- Flatten the tower horizons along a landing into bottom-up rank order. -/
def length {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    Fin r → ℕ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node (length := length) _ lower =>
      fun j => Fin.lastCases length lower.length j

/-- Flatten the selected indices along a landing into bottom-up rank order. -/
def index {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    Fin r → ℕ :=
  match P with
  | .nil => fun j => Fin.elim0 j
  | .node chosen lower =>
      fun j => Fin.lastCases chosen.1 lower.index j

@[simp]
theorem tolerance_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).tolerance (Fin.last r) =
      tolerance := by
  simp [Landing.tolerance]

@[simp]
theorem tolerance_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).tolerance j.castSucc =
      lower.tolerance j := by
  simp [Landing.tolerance]

@[simp]
theorem budget_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).budget (Fin.last r) =
      budget := by
  simp [Landing.budget]

@[simp]
theorem budget_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).budget j.castSucc =
      lower.budget j := by
  simp [Landing.budget]

@[simp]
theorem length_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).length (Fin.last r) =
      length := by
  simp [Landing.length]

@[simp]
theorem length_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).length j.castSucc =
      lower.length j := by
  simp [Landing.length]

@[simp]
theorem index_node_last
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).index (Fin.last r) =
      chosen.1 := by
  simp [Landing.index]

@[simp]
theorem index_node_castSucc
    {k r : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {length : ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (j : Fin r) :
    (Landing.node
      (tolerance := tolerance) (budget := budget)
      chosen lower).index j.castSucc =
      lower.index j := by
  simp [Landing.index]

/-- Every landing records indices within its path-dependent horizons. -/
theorem index_lt_length {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    ∀ j, P.index j < P.length j := by
  induction P with
  | nil =>
      intro j
      exact Fin.elim0 j
  | node chosen lower ih =>
      intro j
      cases j using Fin.lastCases with
      | last =>
          simp [index, length]
      | cast j =>
          simpa [index, length] using ih j

/-- Admissibility supplies nonnegative tolerances along every landing. -/
theorem tolerance_nonneg {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) (hS : S.IsAdmissible) :
    ∀ j n, 0 ≤ P.tolerance j n := by
  induction P with
  | nil =>
      intro j
      exact Fin.elim0 j
  | @node r tolerance budget length next chosen lower ih =>
      rcases hS with ⟨htolerance, _hbudget, _hlength, hnext⟩
      intro j n
      cases j using Fin.lastCases with
      | last =>
          simpa using htolerance n
      | cast j =>
          simpa using ih (hnext chosen) j n

/-- Admissibility supplies the local regularity-budget inequality along
every landing. -/
theorem budget_spec {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) (hS : S.IsAdmissible) :
    ∀ j n,
      (Fintype.card (OrderedFace k (j.1 + 1)) : ℝ) <
        (P.budget j n : ℝ) * (P.tolerance j n) ^ 2 := by
  induction P with
  | nil =>
      intro j
      exact Fin.elim0 j
  | @node r tolerance budget length next chosen lower ih =>
      rcases hS with ⟨_htolerance, hbudget, _hlength, hnext⟩
      intro j n
      cases j using Fin.lastCases with
      | last =>
          change
            (Fintype.card (OrderedFace k (r + 1)) : ℝ) <
              ((Landing.node
                (tolerance := tolerance) (budget := budget)
                chosen lower).budget (Fin.last r) n : ℕ) *
                (Landing.node
                  (tolerance := tolerance) (budget := budget)
                  chosen lower).tolerance (Fin.last r) n ^ 2
          rw [budget_node_last, tolerance_node_last]
          exact hbudget n
      | cast j =>
          change
            (Fintype.card (OrderedFace k (j.1 + 1)) : ℝ) <
              ((Landing.node
                (tolerance := tolerance) (budget := budget)
                chosen lower).budget j.castSucc n : ℕ) *
                (Landing.node
                  (tolerance := tolerance) (budget := budget)
                  chosen lower).tolerance j.castSucc n ^ 2
          rw [budget_node_castSucc, tolerance_node_castSucc]
          exact ih (hnext chosen) j n

/-- Admissibility supplies positive path-dependent horizons along every
landing. -/
theorem length_pos {k r : ℕ}
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) (hS : S.IsAdmissible) :
    ∀ j, 0 < P.length j := by
  induction P with
  | nil =>
      intro j
      exact Fin.elim0 j
  | @node r tolerance budget length next chosen lower ih =>
      rcases hS with ⟨_htolerance, _hbudget, hlength, hnext⟩
      intro j
      cases j using Fin.lastCases with
      | last =>
          simpa using hlength
      | cast j =>
          simpa using ih (hnext chosen) j

end Landing

/-- A realization of an adaptive schedule is a landing together with an
ordinary coarse-target certificate whose actual selected indices are
exactly the indices of that landing.  Consequently the flattened schedule
used at every lower rank is the subtree chosen by the earlier, higher-rank
certificate indices. -/
structure Realization
    {G : Type*} [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (S : AdaptiveCoarseTargetSchedule k r) where
  landing : S.Landing
  certificate :
    CoarseTargetOrderedComplexRegularityCertificate
      G k r initial
        landing.tolerance landing.budget landing.length
  index_eq : certificate.index = landing.index

/-- Every admissible adaptive schedule has a genuine top-down realization.

The proof is a downward rank induction.  At the current top rank it runs
the fixed-upper adjacent-energy selector, uses the selected index to enter
the corresponding subtree, and only then constructs the lower-rank
certificate.  The concluding equality of index vectors rules out the
spurious interpretation in which a branch is chosen independently of the
regularity certificate. -/
theorem Realization.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (S : AdaptiveCoarseTargetSchedule k r)
    (hS : S.IsAdmissible) :
    Nonempty (Realization k r initial S) := by
  induction r with
  | zero =>
      cases S with
      | nil =>
          let landing :
              (AdaptiveCoarseTargetSchedule.nil :
                AdaptiveCoarseTargetSchedule k 0).Landing :=
            Landing.nil
          let certificate :
              CoarseTargetOrderedComplexRegularityCertificate
                G k 0 initial
                  landing.tolerance landing.budget landing.length := {
            index := landing.index
            coarse := initial
            fine := initial
            refines :=
              OrderedPartitionComplex.Refines.refl initial
            coarse_refines_initial :=
              OrderedPartitionComplex.Refines.refl initial
            coarse_topLayer_eq := rfl
            fine_topLayer_eq := rfl
            index_lt := fun j => Fin.elim0 j
            mixedRegular := fun j => Fin.elim0 j
            gap_nonneg := fun j => Fin.elim0 j
            gap_le := fun j => Fin.elim0 j
            coarse_complexity := fun j => Fin.elim0 j
            fine_complexity := fun j => Fin.elim0 j }
          exact ⟨{
            landing := landing
            certificate := certificate
            index_eq := rfl }⟩
  | succ r ih =>
      cases S with
      | @node _ tolerance budget length next =>
          rcases hS with
            ⟨htolerance, hbudget, hlength, hnext⟩
          let lowerInitial :
              OrderedFacePartitionSystem G k r :=
            initial.dropTop.topLayer
          let upper :
              OrderedFacePartitionSystem G k (r + 1) :=
            initial.topLayer
          let topChoice :=
            chosenFixedUpperLayerCoarseFine
              lowerInitial upper tolerance budget
              htolerance hbudget length hlength
          let chosen : Fin length :=
            ⟨topChoice.index, topChoice.index_lt⟩
          let prepared :
              OrderedPartitionComplex G k r :=
            initial.dropTop.withTopLayer topChoice.coarse
          obtain ⟨lowerRealization⟩ :=
            ih prepared (next chosen) (hnext chosen)
          let lowerLanding := lowerRealization.landing
          let lowerCertificate := lowerRealization.certificate
          have hindexLower :
              lowerCertificate.index = lowerLanding.index :=
            lowerRealization.index_eq
          let landing :
              (AdaptiveCoarseTargetSchedule.node
                tolerance budget length next).Landing :=
            Landing.node
              (tolerance := tolerance) (budget := budget)
              chosen lowerLanding
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
          let certificate :
              CoarseTargetOrderedComplexRegularityCertificate
                G k (r + 1) initial
                  landing.tolerance landing.budget landing.length := {
            index := landing.index
            coarse := coarse
            fine := fine
            refines := by
              have hprefix :
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
            coarse_refines_initial := by
              have hprepared :
                  prepared.Refines initial.dropTop := by
                exact
                  OrderedPartitionComplex.withTopLayer_refines
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
            coarse_topLayer_eq := by
              simp [coarse, upper]
            fine_topLayer_eq := by
              simp [fine, upper]
            index_lt := by
              exact landing.index_lt_length
            mixedRegular := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.appendTop_partition_last,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_last, Fin.succ_last]
                  change
                    IsPreliminaryOrderedRegular
                      topChoice.fine upper
                      (landing.tolerance (Fin.last r)
                        (landing.index (Fin.last r)))
                  simpa [landing, chosen] using
                    topChoice.fine_regular
              | cast i =>
                  have hregular :=
                    lowerCertificate.mixedRegular i
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc, Fin.succ_castSucc]
                  change
                    @IsPreliminaryOrderedRegular
                      G _ _ k i.1
                      (lowerCertificate.fine.partition
                        i.castSucc)
                      (lowerCertificate.coarse.partition
                        i.succ)
                      (landing.tolerance i.castSucc
                        (landing.index i.castSucc))
                  rw [show landing.tolerance i.castSucc =
                      lowerLanding.tolerance i by
                        simp [landing]]
                  rw [show landing.index i.castSucc =
                      lowerLanding.index i by
                        simp [landing]]
                  rw [← congrFun hindexLower i]
                  exact hregular
            gap_nonneg := by
              intro q
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
            gap_le := by
              intro q
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
                          (landing.length (Fin.last r) : ℝ)
                  rw [hlowerCoarseTop]
                  simpa [landing] using hgap
              | cast i =>
                  have hgap :=
                    lowerCertificate.gap_le i
                  simp only [fine, finePrefix, coarse,
                    coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc, Fin.succ_castSucc]
                  change
                    orderedLayerAtomEnergy
                          (lowerCertificate.fine.partition
                            i.castSucc)
                          (lowerCertificate.coarse.partition
                            i.succ) -
                        orderedLayerAtomEnergy
                          (lowerCertificate.coarse.partition
                            i.castSucc)
                          (lowerCertificate.coarse.partition
                            i.succ) ≤
                      (Fintype.card
                        (OrderedFace k (i.1 + 1)) : ℝ) /
                          (landing.length i.castSucc : ℝ)
                  rw [show landing.length i.castSucc =
                      lowerLanding.length i by
                        simp [landing]]
                  exact hgap
            coarse_complexity := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  intro e
                  change OrderedFace k r at e
                  have hcomplexity :=
                    topChoice.coarse_complexity e
                  simp only [coarse, coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc]
                  change
                    FacePartition.complexity
                        (lowerCertificate.coarse.partition
                          (Fin.last r) e) ≤
                      fixedUpperLayerComplexityFactor
                          r (landing.budget (Fin.last r))
                          (landing.index (Fin.last r)) *
                        FacePartition.complexity
                          (initial.partition
                            (Fin.last r).castSucc e)
                  have heq :
                      lowerCertificate.coarse.partition
                          (Fin.last r) e =
                        topChoice.coarse e :=
                    congrFun hlowerCoarseTop e
                  rw [heq]
                  simp only [landing, chosen,
                    Landing.budget_node_last,
                    Landing.index_node_last]
                  convert hcomplexity using 1 <;> rfl
              | cast i =>
                  intro e
                  change OrderedFace k i.1 at e
                  have hcomplexity :=
                    lowerCertificate.coarse_complexity i e
                  simp only [coarse, coarsePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc]
                  change
                    FacePartition.complexity
                        (lowerCertificate.coarse.partition
                          i.castSucc e) ≤
                      fixedUpperLayerComplexityFactor
                          i.1 (landing.budget i.castSucc)
                          (landing.index i.castSucc) *
                        FacePartition.complexity
                          (initial.partition
                            i.castSucc.castSucc e)
                  rw [show landing.budget i.castSucc =
                      lowerLanding.budget i by
                        simp [landing]]
                  rw [show landing.index i.castSucc =
                      lowerLanding.index i by
                        simp [landing]]
                  rw [← congrFun hindexLower i]
                  simp only [prepared,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc,
                    OrderedPartitionComplex.dropTop] at hcomplexity
                  convert hcomplexity using 1
                  all_goals rfl
            fine_complexity := by
              intro q
              cases q using Fin.lastCases with
              | last =>
                  intro e
                  change OrderedFace k r at e
                  have hcomplexity :=
                    topChoice.fine_complexity e
                  simp only [fine, finePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_last]
                  change
                    FacePartition.complexity
                        (topChoice.fine e) ≤
                      fixedUpperLayerComplexityFactor
                          r (landing.budget (Fin.last r))
                          (landing.index (Fin.last r) + 1) *
                        FacePartition.complexity
                          (initial.partition
                            (Fin.last r).castSucc e)
                  simp only [landing, chosen,
                    Landing.budget_node_last,
                    Landing.index_node_last]
                  convert hcomplexity using 1
                  all_goals rfl
              | cast i =>
                  intro e
                  change OrderedFace k i.1 at e
                  have hcomplexity :=
                    lowerCertificate.fine_complexity i e
                  simp only [fine, finePrefix,
                    OrderedPartitionComplex.appendTop_partition_castSucc,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc]
                  change
                    FacePartition.complexity
                        (lowerCertificate.fine.partition
                          i.castSucc e) ≤
                      fixedUpperLayerComplexityFactor
                          i.1 (landing.budget i.castSucc)
                          (landing.index i.castSucc + 1) *
                        FacePartition.complexity
                          (initial.partition
                            i.castSucc.castSucc e)
                  rw [show landing.budget i.castSucc =
                      lowerLanding.budget i by
                        simp [landing]]
                  rw [show landing.index i.castSucc =
                      lowerLanding.index i by
                        simp [landing]]
                  rw [← congrFun hindexLower i]
                  simp only [prepared,
                    OrderedPartitionComplex.withTopLayer,
                    Fin.lastCases_castSucc,
                    OrderedPartitionComplex.dropTop] at hcomplexity
                  convert hcomplexity using 1
                  all_goals rfl }
          exact ⟨{
            landing := landing
            certificate := certificate
            index_eq := rfl }⟩

/-- Explicit existential form of adaptive coarse-target regularity.

This is the principal conversion endpoint for downstream arguments: it
returns an ordinary certificate, so all existing counting and cleaning
lemmas apply unchanged, while the equality identifies its index vector
with the realized decision-tree branch. -/
theorem exists_landing_certificate
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (S : AdaptiveCoarseTargetSchedule k r)
    (hS : S.IsAdmissible) :
    ∃ P : S.Landing,
      ∃ R :
          CoarseTargetOrderedComplexRegularityCertificate
            G k r initial P.tolerance P.budget P.length,
        R.index = P.index := by
  obtain ⟨realization⟩ :=
    Realization.nonempty initial S hS
  exact
    ⟨realization.landing, realization.certificate,
      realization.index_eq⟩

end AdaptiveCoarseTargetSchedule

end Wikipedia.SzemeredisTheorem
