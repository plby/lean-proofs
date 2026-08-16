import Wikipedia.SzemeredisTheorem.Hypergraph.AdaptiveCoarseTargetRegularity
import Wikipedia.SzemeredisTheorem.Hypergraph.TowerDominatingGrowth

/-!
# Source-style full coarse-target regularity

Tao's full regularity lemma does not choose the parameters at the different
ranks independently.  It first fixes a lower scale and then descends through
the ranks with a sufficiently fast auxiliary growth function.  The selected
scales have the shape

```
scaleFloor ≤ M_r,
F(M_{j + 1}) ≤ M_j,
gap_j ≤ 1 / F(M_{j + 1})^2,
regularity_j ≤ 1 / F(M_0).
```

This file isolates the exact adaptive certificate needed for that induction.
A `SourceFullCoarseTargetSchedule` is a finite top-down decision tree together
with numerical scale data on its genuine landings.  Its hypotheses are all
finite and ambient-independent.  The main compiler realizes the tree by
`AdaptiveCoarseTargetSchedule.exists_landing_certificate` and returns an
ordinary `CoarseTargetOrderedComplexRegularityCertificate` carrying the
source-style scale hierarchy.

The rank-zero plan and a genuine successor constructor are proved below.
The successor constructor makes the remaining mathematical obligation
explicit: after the current top index is selected, the lower plan must have
been built with scale floor `F(topScale)`, and the already fixed top
tolerance must be bounded by the common reciprocal attached to every landing
of that lower plan.  Constructing these lower plans uniformly is precisely
the auxiliary faster-growth induction in the source proof.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## Source numerical targets -/

/-- The single preliminary-regularity tolerance used to compare every
selected rank with the largest selected scale `M₀`. -/
noncomputable def sourceFullCommonTolerance
    {r : ℕ} (F : NatGrowthFunction)
    (scale : Fin (r + 1) → ℕ) : ℝ :=
  1 / (F (scale 0) : ℝ)

/-- The source energy-gap target at the lower boundary of a rank-`j + 1`
upper layer. -/
noncomputable def sourceFullRankGap
    {r : ℕ} (F : NatGrowthFunction)
    (scale : Fin (r + 1) → ℕ)
    (j : Fin r) : ℝ :=
  1 / (F (scale j.succ) : ℝ) ^ 2

theorem sourceFullCommonTolerance_pos
    {r : ℕ} (F : NatGrowthFunction)
    (scale : Fin (r + 1) → ℕ) :
    0 < sourceFullCommonTolerance F scale := by
  unfold sourceFullCommonTolerance
  exact one_div_pos.mpr
    (by exact_mod_cast F.positive (scale 0))

theorem sourceFullRankGap_pos
    {r : ℕ} (F : NatGrowthFunction)
    (scale : Fin (r + 1) → ℕ)
    (j : Fin r) :
    0 < sourceFullRankGap F scale j := by
  unfold sourceFullRankGap
  exact one_div_pos.mpr
    (sq_pos_of_pos
      (by exact_mod_cast F.positive (scale j.succ)))

/-! ## Numerical bounds selected by an adaptive landing -/

/-- The coarse-layer complexity bound supplied directly by an adaptive
landing and an initial layerwise bound.  The unchanged top layer keeps its
initial bound; a non-top layer uses the selected fixed-upper tower factor. -/
def adaptiveSelectedCoarseLayerBound
    {k r : ℕ}
    (initialBound : Fin (r + 1) → ℕ)
    {S : AdaptiveCoarseTargetSchedule k r}
    (P : S.Landing) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (initialBound (Fin.last r))
    (fun j =>
      fixedUpperLayerComplexityFactor
          j.1 (P.budget j) (P.index j) *
        initialBound j.castSucc)

/-! ## Adaptive source-full plans -/

/-- Ambient-independent source-full numerical data on an adaptive
coarse-target schedule.

The scales may depend on the genuine landing.  No condition is imposed on a
Cartesian product of unrelated stage indices.  `scaleFloor` is fixed before
the ambient finite type and is forced below the deepest scale on every
landing. -/
structure SourceFullCoarseTargetSchedule
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) where
  schedule : AdaptiveCoarseTargetSchedule k r
  schedule_admissible : schedule.IsAdmissible
  scale : schedule.Landing → Fin (r + 1) → ℕ
  scaleFloor_le_deepest :
    ∀ P, scaleFloor ≤ scale P (Fin.last r)
  scale_hierarchy :
    ∀ P (j : Fin r),
      F (scale P j.succ) ≤ scale P j.castSucc
  selected_tolerance_le_common :
    ∀ P (j : Fin r),
      P.tolerance j (P.index j) ≤
        sourceFullCommonTolerance F (scale P)
  reciprocal_gap_le :
    ∀ P (j : Fin r),
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
            (P.length j : ℝ) ≤
        sourceFullRankGap F (scale P) j
  selected_coarse_bound :
    ∀ P q,
      adaptiveSelectedCoarseLayerBound initialBound P q ≤
        scale P q

namespace SourceFullCoarseTargetSchedule

/-- The scale hierarchy is antitone: deeper scales are no larger than
shallower scales. -/
theorem scale_antitone
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule
      k r initialBound F scaleFloor)
    (P : S.schedule.Landing) :
    Antitone (S.scale P) := by
  rw [Fin.antitone_iff_succ_le]
  intro j
  exact
    (Nat.le_succ _).trans
      ((F.above_diagonal (S.scale P j.succ)).trans
        (S.scale_hierarchy P j))

/-- The fixed scale floor lies below every selected scale, not only the
deepest one. -/
theorem scaleFloor_le
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule
      k r initialBound F scaleFloor)
    (P : S.schedule.Landing)
    (q : Fin (r + 1)) :
    scaleFloor ≤ S.scale P q := by
  exact (S.scaleFloor_le_deepest P).trans
    (S.scale_antitone P (Fin.le_last q))

/-! ## Realized source-full certificates -/

/-- A realized coarse-target certificate with Tao's full-regularity scale
hierarchy.  The ordinary certificate retains all refinement and exact
mixed-regularity data; this wrapper records the common discrepancy, the
rankwise source gaps, and the selected coarse complexity scales. -/
structure Certificate
    {G : Type*} [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) where
  tolerance : (j : Fin r) → ℕ → ℝ
  budget : (j : Fin r) → ℕ → ℕ
  length : Fin r → ℕ
  regularity :
    CoarseTargetOrderedComplexRegularityCertificate
      G k r initial tolerance budget length
  scale : Fin (r + 1) → ℕ
  scaleFloor_le : ∀ q, scaleFloor ≤ scale q
  scale_hierarchy :
    ∀ j : Fin r,
      F (scale j.succ) ≤ scale j.castSucc
  selected_tolerance_nonneg :
    ∀ j : Fin r,
      0 ≤
        selectedOrderedComplexTolerance
          tolerance regularity.index j
  selected_tolerance_le_common :
    ∀ j : Fin r,
      selectedOrderedComplexTolerance
          tolerance regularity.index j ≤
        sourceFullCommonTolerance F scale
  rank_gap_le :
    ∀ j : Fin r,
      regularity.toCoarseFine.coarseUpperLayerAtomEnergyGap j ≤
        sourceFullRankGap F scale j
  coarse_complexity :
    ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
      FacePartition.complexity
          (regularity.coarse.partition q e) ≤
        scale q

/-- Every source-full adaptive plan realizes an ordinary coarse-target
certificate with the advertised source scale hierarchy. -/
theorem certificate_nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : SourceFullCoarseTargetSchedule
      k r initialBound F scaleFloor)
    (initial : OrderedPartitionComplex G k r)
    (hinitial :
      ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
        FacePartition.complexity
            (initial.partition q e) ≤
          initialBound q) :
    Nonempty
      (Certificate k r initial initialBound F scaleFloor) := by
  obtain ⟨P, R, hindex⟩ :=
    S.schedule.exists_landing_certificate
      initial S.schedule_admissible
  refine ⟨{
    tolerance := P.tolerance
    budget := P.budget
    length := P.length
    regularity := R
    scale := S.scale P
    scaleFloor_le := S.scaleFloor_le P
    scale_hierarchy := S.scale_hierarchy P
    selected_tolerance_nonneg := ?_
    selected_tolerance_le_common := ?_
    rank_gap_le := ?_
    coarse_complexity := ?_ }⟩
  · intro j
    simp only [selectedOrderedComplexTolerance]
    rw [congrFun hindex j]
    exact
      P.tolerance_nonneg S.schedule_admissible
        j (P.index j)
  · intro j
    simpa [selectedOrderedComplexTolerance, hindex] using
      S.selected_tolerance_le_common P j
  · intro j
    have hgap := R.gap_le j
    have hreciprocal := S.reciprocal_gap_le P j
    change
      orderedLayerAtomEnergy
            (R.fine.partition j.castSucc)
            (R.coarse.partition j.succ) -
          orderedLayerAtomEnergy
            (R.coarse.partition j.castSucc)
            (R.coarse.partition j.succ) ≤
        sourceFullRankGap F (S.scale P) j
    exact hgap.trans hreciprocal
  · intro q
    cases q using Fin.lastCases with
    | last =>
        intro e
        have htop := congrFun R.coarse_topLayer_eq e
        simp only [OrderedPartitionComplex.topLayer] at htop
        rw [htop]
        calc
          FacePartition.complexity
                (initial.partition (Fin.last r) e) ≤
              initialBound (Fin.last r) :=
            hinitial (Fin.last r) e
          _ =
              adaptiveSelectedCoarseLayerBound
                initialBound P (Fin.last r) := by
            simp [adaptiveSelectedCoarseLayerBound]
          _ ≤ S.scale P (Fin.last r) :=
            S.selected_coarse_bound P (Fin.last r)
    | cast j =>
        intro e
        calc
          FacePartition.complexity
                (R.coarse.partition j.castSucc e) ≤
              fixedUpperLayerComplexityFactor
                    j.1 (P.budget j) (P.index j) *
                FacePartition.complexity
                    (initial.partition j.castSucc e) := by
            rw [← congrFun hindex j]
            exact R.coarse_complexity j e
          _ ≤
              fixedUpperLayerComplexityFactor
                    j.1 (P.budget j) (P.index j) *
                initialBound j.castSucc :=
            Nat.mul_le_mul_left _
              (hinitial j.castSucc e)
          _ =
              adaptiveSelectedCoarseLayerBound
                initialBound P j.castSucc := by
            simp [adaptiveSelectedCoarseLayerBound]
          _ ≤ S.scale P j.castSucc :=
            S.selected_coarse_bound P j.castSucc

/-! ## Rank-zero plan -/

/-- Rank zero has no regularity choices.  The only selected scale is the
maximum of the requested scale floor and the initial top-layer bound. -/
def zero
    (k : ℕ)
    (initialBound : Fin 1 → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) :
    SourceFullCoarseTargetSchedule
      k 0 initialBound F scaleFloor where
  schedule := .nil
  schedule_admissible := trivial
  scale := fun _ _ =>
    max scaleFloor (initialBound 0)
  scaleFloor_le_deepest := by
    intro P
    exact le_max_left _ _
  scale_hierarchy := by
    intro P j
    exact Fin.elim0 j
  selected_tolerance_le_common := by
    intro P j
    exact Fin.elim0 j
  reciprocal_gap_le := by
    intro P j
    exact Fin.elim0 j
  selected_coarse_bound := by
    intro P q
    have hq : q = 0 := Fin.eq_zero q
    subst q
    change initialBound 0 ≤
      max scaleFloor (initialBound 0)
    exact le_max_right _ _

/-- The rank-zero source-full certificate is therefore unconditional for
every requested scale floor. -/
theorem certificate_nonempty_zero
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    (k : ℕ)
    (initial : OrderedPartitionComplex G k 0)
    (initialBound : Fin 1 → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ)
    (hinitial :
      ∀ (q : Fin 1) (e : OrderedFace k q.1),
        FacePartition.complexity
            (initial.partition q e) ≤
          initialBound q) :
    Nonempty
      (Certificate k 0 initial initialBound F scaleFloor) :=
  (zero k initialBound F scaleFloor).certificate_nonempty
    initial hinitial

/-! ## A genuine top-down successor constructor -/

/-- Prepend one deepest scale to the scale vector of a selected lower
landing.  Naming this dependent match separately gives downstream proofs a
stable simplification rule. -/
def nodeScale
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (P :
      (AdaptiveCoarseTargetSchedule.node
        tolerance budget length next).Landing) :
    Fin (r + 2) → ℕ :=
  match P with
  | .node chosen lower =>
      Fin.lastCases topScale
        (lowerScale chosen lower)

@[simp]
theorem nodeScale_node
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    nodeScale (tolerance := tolerance) (budget := budget)
        topScale lowerScale
        (AdaptiveCoarseTargetSchedule.Landing.node
          (tolerance := tolerance) (budget := budget)
          chosen lower) =
      Fin.lastCases topScale
        (lowerScale chosen lower) :=
  rfl

@[simp]
theorem nodeScale_node_last
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    nodeScale (tolerance := tolerance) (budget := budget)
        topScale lowerScale
        (AdaptiveCoarseTargetSchedule.Landing.node
          (tolerance := tolerance) (budget := budget)
          chosen lower)
        (Fin.last (r + 1)) =
      topScale := by
  simp [nodeScale]

@[simp]
theorem nodeScale_node_castSucc
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing)
    (q : Fin (r + 1)) :
    nodeScale (tolerance := tolerance) (budget := budget)
        topScale lowerScale
        (AdaptiveCoarseTargetSchedule.Landing.node
          (tolerance := tolerance) (budget := budget)
          chosen lower)
        q.castSucc =
      lowerScale chosen lower q := by
  simp [nodeScale]

@[simp]
theorem sourceFullCommonTolerance_nodeScale
    {k r length : ℕ}
    {tolerance : ℕ → ℝ}
    {budget : ℕ → ℕ}
    {next : Fin length → AdaptiveCoarseTargetSchedule k r}
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerScale :
      ∀ i : Fin length,
        (next i).Landing → Fin (r + 1) → ℕ)
    (chosen : Fin length)
    (lower : (next chosen).Landing) :
    sourceFullCommonTolerance F
        (nodeScale (tolerance := tolerance) (budget := budget)
          topScale lowerScale
          (AdaptiveCoarseTargetSchedule.Landing.node
            (tolerance := tolerance) (budget := budget)
            chosen lower)) =
      sourceFullCommonTolerance F
        (lowerScale chosen lower) := by
  unfold sourceFullCommonTolerance
  rw [show
    (0 : Fin (r + 2)) =
      (0 : Fin (r + 1)).castSucc by rfl]
  rw [nodeScale_node_castSucc]

/-- Initial layer bounds seen by the lower subtree after the current
top-rank stage `i` has been selected.

The new lower top layer is the selected coarse layer, hence its bound is the
selected fixed-upper tower factor times the old rank-`r` input bound.  All
strictly lower input layers are unchanged. -/
def lowerInitialBound
    {r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (budget : ℕ → ℕ)
    {length : ℕ}
    (i : Fin length) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (fixedUpperLayerComplexityFactor r budget i.1 *
      initialBound (Fin.last r).castSucc)
    (fun q => initialBound q.castSucc.castSucc)

/-- Extend source-full lower plans by one new top rank.

`topScale` is the new deepest scale.  Once the top energy selector chooses
`i`, the construction enters `next i`; that lower plan starts at scale floor
`F(topScale)`, which proves the new hierarchy link.  The only genuinely
source-specific compatibility hypothesis is `htopTolerance`: the top
tolerance fixed at stage `i` must already be no larger than the common
reciprocal attached to every landing of the selected lower plan. -/
def node
    {k r : ℕ}
    {initialBound : Fin (r + 2) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (topScale : ℕ)
    (tolerance : ℕ → ℝ)
    (budget : ℕ → ℕ)
    (length : ℕ)
    (next :
      (i : Fin length) →
        SourceFullCoarseTargetSchedule
          k r (lowerInitialBound initialBound budget i)
            F (F topScale))
    (htolerance : ∀ n, 0 ≤ tolerance n)
    (hbudget :
      ∀ n,
        (Fintype.card
            (OrderedFace k (r + 1)) : ℝ) <
          (budget n : ℝ) * (tolerance n) ^ 2)
    (hlength : 0 < length)
    (hscaleFloor : scaleFloor ≤ topScale)
    (hinitialTop :
      initialBound (Fin.last (r + 1)) ≤ topScale)
    (htopTolerance :
      ∀ (i : Fin length)
          (P : (next i).schedule.Landing),
        tolerance i.1 ≤
          sourceFullCommonTolerance F ((next i).scale P))
    (htopGap :
      (Fintype.card
          (OrderedFace k (r + 1)) : ℝ) /
            (length : ℝ) ≤
        1 / (F topScale : ℝ) ^ 2) :
    SourceFullCoarseTargetSchedule
      k (r + 1) initialBound F scaleFloor where
  schedule :=
    .node tolerance budget length
      (fun i => (next i).schedule)
  schedule_admissible := by
    exact ⟨htolerance, hbudget, hlength,
      fun i => (next i).schedule_admissible⟩
  scale :=
    nodeScale topScale
      (fun i => (next i).scale)
  scaleFloor_le_deepest := by
    intro P
    cases P with
    | node chosen lower =>
        simpa only [nodeScale_node_last] using
          hscaleFloor
  scale_hierarchy := by
    intro P j
    cases P with
    | node chosen lower =>
        cases j using Fin.lastCases with
        | last =>
            simpa only [Fin.succ_last,
              nodeScale_node_last,
              nodeScale_node_castSucc] using
              (next chosen).scaleFloor_le_deepest lower
        | cast q =>
            simpa only [Fin.succ_castSucc,
              nodeScale_node_castSucc] using
              (next chosen).scale_hierarchy lower q
  selected_tolerance_le_common := by
    intro P j
    cases P with
    | node chosen lower =>
        cases j using Fin.lastCases with
        | last =>
            simpa only [
              AdaptiveCoarseTargetSchedule.Landing.tolerance_node_last,
              AdaptiveCoarseTargetSchedule.Landing.index_node_last,
              sourceFullCommonTolerance_nodeScale] using
              htopTolerance chosen lower
        | cast q =>
            simpa only [
              AdaptiveCoarseTargetSchedule.Landing.tolerance_node_castSucc,
              AdaptiveCoarseTargetSchedule.Landing.index_node_castSucc,
              sourceFullCommonTolerance_nodeScale] using
              (next chosen).selected_tolerance_le_common
                lower q
  reciprocal_gap_le := by
    intro P j
    cases P with
    | node chosen lower =>
        cases j using Fin.lastCases with
        | last =>
            simp only [
              AdaptiveCoarseTargetSchedule.Landing.length_node_last,
              sourceFullRankGap, Fin.succ_last,
              nodeScale_node_last, Fin.val_last]
            convert htopGap using 1
        | cast q =>
            simp only [
              AdaptiveCoarseTargetSchedule.Landing.length_node_castSucc,
              sourceFullRankGap, Fin.succ_castSucc,
              nodeScale_node_castSucc,
              Fin.val_castSucc]
            convert
              (next chosen).reciprocal_gap_le lower q using 1
            · congr 1
  selected_coarse_bound := by
    intro P q
    cases P with
    | node chosen lower =>
        cases q using Fin.lastCases with
        | last =>
            simpa [adaptiveSelectedCoarseLayerBound,
              nodeScale_node_last] using
              hinitialTop
        | cast q =>
            cases q using Fin.lastCases with
            | last =>
                simpa [adaptiveSelectedCoarseLayerBound,
                  lowerInitialBound,
                  nodeScale_node_castSucc] using
                  (next chosen).selected_coarse_bound
                    lower (Fin.last r)
            | cast j =>
                simpa [adaptiveSelectedCoarseLayerBound,
                  lowerInitialBound,
                  nodeScale_node_castSucc] using
                  (next chosen).selected_coarse_bound
                    lower j.castSucc

/-! ## The finite faster-growth induction -/

/-- A source-full plan together with a landing-independent upper bound for
its largest selected scale.  The bound is auxiliary: it is used only while
constructing the tolerance at the preceding rank and is erased from the
public existence theorem. -/
structure Bounded
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) where
  plan :
    SourceFullCoarseTargetSchedule
      k r initialBound F scaleFloor
  ceiling : ℕ
  scale_zero_le :
    ∀ P : plan.schedule.Landing,
      plan.scale P 0 ≤ ceiling

namespace Bounded

/-- Transport only the initial-bound index of a bounded plan.  Its
numerical ceiling is definitionally unchanged. -/
def castInitialBound
    {k r : ℕ}
    {initialBound newInitialBound :
      Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (S : Bounded k r initialBound F scaleFloor)
    (h : initialBound = newInitialBound) :
    Bounded k r newInitialBound F scaleFloor where
  plan := h ▸ S.plan
  ceiling := S.ceiling
  scale_zero_le := by
    subst newInitialBound
    exact S.scale_zero_le

end Bounded

/-- The bounded form of the rank-zero plan. -/
def boundedZero
    (k : ℕ)
    (initialBound : Fin 1 → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) :
    Bounded k 0 initialBound F scaleFloor where
  plan := zero k initialBound F scaleFloor
  ceiling := max scaleFloor (initialBound 0)
  scale_zero_le := by
    intro P
    change
      max scaleFloor (initialBound 0) ≤
        max scaleFloor (initialBound 0)
    exact le_rfl

/-- The lower input bound when the already accumulated top-tower
complexity factor is `factor`. -/
def factorLowerInitialBound
    {r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (factor : ℕ) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (factor * initialBound (Fin.last r).castSucc)
    (fun q => initialBound q.castSucc.castSucc)

/-- The accumulated fixed-upper factor before stage `n`.

At stage `n`, the lower plan is first constructed from the factor already
accumulated at stages `< n`.  Its uniform ceiling then determines the
current reciprocal tolerance and hence the current budget.  That new budget
is used only in the factor for stage `n + 1`.  This one-stage shift is the
finite fast-growth device which removes the apparent circularity. -/
noncomputable def sourceFullStageFactor
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale)) :
    ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      let previous :=
        sourceFullStageFactor
          initialBound F topScale lowerBuilder n
      let lower :=
        lowerBuilder
          (factorLowerInitialBound
            initialBound previous)
      let tolerance :=
        growthRegularityStepTolerance
          F lower.ceiling
      let budget :=
        orderedRemovalRegularityBudget
          k r tolerance
      (2 ^ (r + 1)) ^ budget * previous

/-- The lower input bound presented at top-tower stage `n`. -/
noncomputable def sourceFullStageBound
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) :
    Fin (r + 1) → ℕ :=
  factorLowerInitialBound initialBound
    (sourceFullStageFactor
      initialBound F topScale lowerBuilder n)

/-- The bounded lower plan selected before the current top-stage tolerance
and budget are fixed. -/
noncomputable def sourceFullStagePlan
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) :
    Bounded k r
      (sourceFullStageBound
        initialBound F topScale lowerBuilder n)
      F (F topScale) :=
  lowerBuilder
    (sourceFullStageBound
      initialBound F topScale lowerBuilder n)

/-- The current top-stage tolerance, chosen from the already constructed
lower plan's uniform scale ceiling. -/
noncomputable def sourceFullStageTolerance
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) : ℝ :=
  growthRegularityStepTolerance F
    (sourceFullStagePlan
      initialBound F topScale lowerBuilder n).ceiling

/-- The ceiling budget corresponding to the current top-stage tolerance. -/
noncomputable def sourceFullStageBudget
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) : ℕ :=
  orderedRemovalRegularityBudget k r
    (sourceFullStageTolerance
      initialBound F topScale lowerBuilder n)

@[simp]
theorem sourceFullStageFactor_zero
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale)) :
    sourceFullStageFactor
      initialBound F topScale lowerBuilder 0 = 1 :=
  rfl

@[simp]
theorem sourceFullStageFactor_succ
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) :
    sourceFullStageFactor
        initialBound F topScale lowerBuilder (n + 1) =
      (2 ^ (r + 1)) ^
          sourceFullStageBudget
            initialBound F topScale lowerBuilder n *
        sourceFullStageFactor
          initialBound F topScale lowerBuilder n :=
  rfl

/-- The explicitly accumulated stage factor is exactly the standard
fixed-upper tower factor for the recursively chosen budget stream. -/
theorem fixedUpperLayerComplexityFactor_sourceFullStageBudget
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale)) :
    ∀ n,
      fixedUpperLayerComplexityFactor r
          (sourceFullStageBudget
            initialBound F topScale lowerBuilder) n =
        sourceFullStageFactor
          initialBound F topScale lowerBuilder n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        (2 ^ (r + 1)) ^
              sourceFullStageBudget
                initialBound F topScale lowerBuilder n *
            fixedUpperLayerComplexityFactor r
              (sourceFullStageBudget
                initialBound F topScale lowerBuilder) n =
          (2 ^ (r + 1)) ^
              sourceFullStageBudget
                initialBound F topScale lowerBuilder n *
            sourceFullStageFactor
              initialBound F topScale lowerBuilder n
      rw [ih]

/-- Rewriting the accumulated factor identifies the lower input bound used
by the generic successor constructor with the one used to build stage
`i`.  This is the local prefix-invariance statement: the factor at `i`
depends only on budgets at stages `< i`. -/
theorem lowerInitialBound_sourceFullStageBudget
    {k r length : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (i : Fin length) :
    lowerInitialBound initialBound
        (sourceFullStageBudget
          initialBound F topScale lowerBuilder) i =
      sourceFullStageBound
        initialBound F topScale lowerBuilder i.1 := by
  funext q
  cases q using Fin.lastCases with
  | last =>
      simp [lowerInitialBound, sourceFullStageBound,
        factorLowerInitialBound,
        fixedUpperLayerComplexityFactor_sourceFullStageBudget]
  | cast q =>
      simp [lowerInitialBound, sourceFullStageBound,
        factorLowerInitialBound]

/-- The stage-`i` lower plan, transported to the syntactic initial-bound
family expected by `node`. -/
noncomputable def sourceFullStageNext
    {k r length : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (i : Fin length) :
    Bounded k r
      (lowerInitialBound initialBound
        (sourceFullStageBudget
          initialBound F topScale lowerBuilder) i)
      F (F topScale) :=
  (sourceFullStagePlan
      initialBound F topScale lowerBuilder i.1).castInitialBound
    (lowerInitialBound_sourceFullStageBudget
      initialBound F topScale lowerBuilder i).symm

@[simp]
theorem sourceFullStageNext_ceiling
    {k r length : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (i : Fin length) :
    (sourceFullStageNext
      initialBound F topScale lowerBuilder i).ceiling =
      (sourceFullStagePlan
        initialBound F topScale lowerBuilder i.1).ceiling :=
  rfl

theorem sourceFullStageTolerance_pos
    {k r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (F : NatGrowthFunction)
    (topScale : ℕ)
    (lowerBuilder :
      (bound : Fin (r + 1) → ℕ) →
        Bounded k r bound F (F topScale))
    (n : ℕ) :
    0 <
      sourceFullStageTolerance
        initialBound F topScale lowerBuilder n := by
  exact growthRegularityStepTolerance_pos F
    (sourceFullStagePlan
      initialBound F topScale lowerBuilder n).ceiling

/-- Strengthened source-full existence with a uniform upper bound on the
largest scale.  The proof is by rank induction.  Its successor step is a
finite recursion through the top energy horizon, so there is no fixed-point
assumption on `F`. -/
theorem bounded_nonempty
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) :
    Nonempty
      (Bounded k r initialBound F scaleFloor) := by
  induction r generalizing scaleFloor with
  | zero =>
      exact
        ⟨boundedZero
          k initialBound F scaleFloor⟩
  | succ r ih =>
      let topScale : ℕ :=
        max scaleFloor
          (initialBound (Fin.last (r + 1)))
      let gap : ℝ :=
        1 / (F topScale : ℝ) ^ 2
      let length : ℕ :=
        growthRegularityLength k r gap
      let lowerBuilder :
          (bound : Fin (r + 1) → ℕ) →
            Bounded k r bound F (F topScale) :=
        fun bound =>
          Classical.choice
            (ih bound (F topScale))
      let tolerance : ℕ → ℝ :=
        sourceFullStageTolerance
          initialBound F topScale lowerBuilder
      let budget : ℕ → ℕ :=
        sourceFullStageBudget
          initialBound F topScale lowerBuilder
      let next :
          (i : Fin length) →
            Bounded k r
              (lowerInitialBound initialBound budget i)
              F (F topScale) :=
        fun i =>
          sourceFullStageNext
            initialBound F topScale lowerBuilder i
      have hgap_pos : 0 < gap := by
        dsimp only [gap]
        exact one_div_pos.mpr
          (sq_pos_of_pos
            (by exact_mod_cast F.positive topScale))
      let plan :
          SourceFullCoarseTargetSchedule
            k (r + 1) initialBound F scaleFloor :=
        node topScale tolerance budget length
          (fun i => (next i).plan)
          (by
            intro n
            exact
              (sourceFullStageTolerance_pos
                initialBound F topScale lowerBuilder n).le)
          (by
            intro n
            change
              (Fintype.card
                  (OrderedFace k (r + 1)) : ℝ) <
                (sourceFullStageBudget
                    initialBound F topScale lowerBuilder n : ℝ) *
                  (sourceFullStageTolerance
                    initialBound F topScale lowerBuilder n) ^ 2
            exact
              orderedRemovalRegularityBudget_spec
                (sourceFullStageTolerance_pos
                  initialBound F topScale lowerBuilder n))
          (by
            exact growthRegularityLength_pos k r gap)
          (by
            exact le_max_left _ _)
          (by
            exact le_max_right _ _)
          (by
            intro i P
            have hscale :
                (next i).plan.scale P 0 ≤
                  (sourceFullStagePlan
                    initialBound F topScale
                      lowerBuilder i.1).ceiling := by
              exact
                ((next i).scale_zero_le P).trans_eq
                  (sourceFullStageNext_ceiling
                    initialBound F topScale
                      lowerBuilder i)
            change
              growthRegularityStepTolerance F
                    (sourceFullStagePlan
                      initialBound F topScale
                        lowerBuilder i.1).ceiling ≤
                sourceFullCommonTolerance F
                  ((next i).plan.scale P)
            unfold growthRegularityStepTolerance
              sourceFullCommonTolerance
            apply one_div_le_one_div_of_le
            · exact_mod_cast
                F.positive ((next i).plan.scale P 0)
            · exact_mod_cast F.monotone hscale)
          (by
            have hgap :=
              orderedFace_card_div_growthRegularityLength_lt
                (k := k) (j := r) hgap_pos
            exact hgap.le)
      let ceiling : ℕ :=
        finiteMaximum length
          (fun i => (next i).ceiling)
      refine ⟨{
        plan := plan
        ceiling := ceiling
        scale_zero_le := ?_ }⟩
      intro P
      cases P with
      | node chosen lower =>
          dsimp only [plan, ceiling, node]
          change
            nodeScale topScale
                (fun i => (next i).plan.scale)
                (AdaptiveCoarseTargetSchedule.Landing.node
                  chosen lower) 0 ≤
              finiteMaximum length
                (fun i => (next i).ceiling)
          rw [show
            (0 : Fin (r + 2)) =
              (0 : Fin (r + 1)).castSucc by rfl]
          rw [nodeScale_node_castSucc]
          exact
            ((next chosen).scale_zero_le lower).trans
              (le_finiteMaximum
                (fun i => (next i).ceiling) chosen)

/-- Tao's finite faster-growth induction supplies a source-full plan for
every natural growth function, every initial layerwise bound, and every
requested deepest-scale floor. -/
theorem nonempty
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ) :
    Nonempty
      (SourceFullCoarseTargetSchedule
        k r initialBound F scaleFloor) := by
  obtain ⟨S⟩ :=
    bounded_nonempty
      k r initialBound F scaleFloor
  exact ⟨S.plan⟩

/-- End-to-end source-full coarse-target regularity, with the numerical
plan constructed internally by the finite faster-growth induction. -/
theorem certificate_nonempty_full
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (scaleFloor : ℕ)
    (hinitial :
      ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
        FacePartition.complexity
            (initial.partition q e) ≤
          initialBound q) :
    Nonempty
      (Certificate
        k r initial initialBound F scaleFloor) := by
  obtain ⟨S⟩ :=
    nonempty k r initialBound F scaleFloor
  exact S.certificate_nonempty initial hinitial

end SourceFullCoarseTargetSchedule

end Wikipedia.SzemeredisTheorem
