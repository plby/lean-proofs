import Wikipedia.SzemeredisTheorem.Hypergraph.GrowthFunctionRegularity

/-!
# All-rank growth-function ordered regularity

This file has two layers.

First, it records the finite descending hierarchy used in the
growth-function formulation:

```
M_d ≤ F(M_d) = M_{d-1} ≤ ⋯ ≤ M_0.
```

The canonical hierarchy is obtained by iterating `F` upward from `M_d`.

Second, it instantiates the existing top-down fixed-upper composition with
the triangular schedules from `GrowthFunctionRegularity`.  At rank `j`, the
selected fine lower layer is preliminarily regular against the final fine
upper layer with error exactly `1 / F(M_j)`, where `M_j` is the selected
triangular bound at that rank.  The adjacent energy gap is at most the
prescribed rankwise target `γ j`.  Complexity bookkeeping is stated for
every layer, including the unchanged top layer.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## Finite descending growth hierarchies -/

/-- A finite hierarchy indexed from the largest scale `0` down to the
smallest scale `depth`.  Each upper scale is exactly the growth-function
image of the next lower scale. -/
structure DescendingGrowthHierarchy
    (F : NatGrowthFunction) (depth : ℕ) where
  level : Fin (depth + 1) → ℕ
  step_eq :
    ∀ i : Fin depth,
      level i.castSucc = F (level i.succ)

namespace DescendingGrowthHierarchy

/-- The lower member of each adjacent pair is at most its growth-function
image. -/
theorem lower_le_growth
    {F : NatGrowthFunction} {depth : ℕ}
    (H : DescendingGrowthHierarchy F depth)
    (i : Fin depth) :
    H.level i.succ ≤ F (H.level i.succ) := by
  exact (Nat.le_succ _).trans
    (F.above_diagonal (H.level i.succ))

/-- The growth-function image of a lower scale is the preceding upper
scale. -/
theorem growth_eq_upper
    {F : NatGrowthFunction} {depth : ℕ}
    (H : DescendingGrowthHierarchy F depth)
    (i : Fin depth) :
    F (H.level i.succ) = H.level i.castSucc :=
  (H.step_eq i).symm

/-- One adjacent link of the displayed hierarchy
`M_{i+1} ≤ F(M_{i+1}) ≤ M_i`. -/
theorem lower_le_growth_le_upper
    {F : NatGrowthFunction} {depth : ℕ}
    (H : DescendingGrowthHierarchy F depth)
    (i : Fin depth) :
    H.level i.succ ≤ F (H.level i.succ) ∧
      F (H.level i.succ) ≤ H.level i.castSucc := by
  exact ⟨H.lower_le_growth i,
    (H.growth_eq_upper i).le⟩

/-- The hierarchy is antitone in its finite index: later/deeper scales are
no larger than earlier scales. -/
theorem antitone
    {F : NatGrowthFunction} {depth : ℕ}
    (H : DescendingGrowthHierarchy F depth) :
    Antitone H.level := by
  rw [Fin.antitone_iff_succ_le]
  intro i
  exact (H.lower_le_growth i).trans_eq
    (H.growth_eq_upper i)

end DescendingGrowthHierarchy

/-- The canonical descending hierarchy with prescribed bottom scale,
obtained by iterating `F` toward index zero. -/
def canonicalDescendingGrowthHierarchy
    (F : NatGrowthFunction) (depth bottom : ℕ) :
    DescendingGrowthHierarchy F depth where
  level q :=
    (F.toFun ^[depth - q.1]) bottom
  step_eq := by
    intro i
    have hexponent :
        depth - i.castSucc.1 =
          (depth - i.succ.1) + 1 := by
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega
    rw [hexponent]
    exact Function.iterate_succ_apply'
      F.toFun (depth - i.succ.1) bottom

@[simp]
theorem canonicalDescendingGrowthHierarchy_last
    (F : NatGrowthFunction) (depth bottom : ℕ) :
    (canonicalDescendingGrowthHierarchy
      F depth bottom).level (Fin.last depth) =
        bottom := by
  simp [canonicalDescendingGrowthHierarchy]

@[simp]
theorem canonicalDescendingGrowthHierarchy_zero
    (F : NatGrowthFunction) (depth bottom : ℕ) :
    (canonicalDescendingGrowthHierarchy
      F depth bottom).level 0 =
        (F.toFun ^[depth]) bottom := by
  simp [canonicalDescendingGrowthHierarchy]

/-! ## Rankwise triangular schedules -/

/-- Growth-function tolerance schedule at every non-top rank. -/
noncomputable def growthComplexRegularityTolerance
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction) :
    (j : Fin r) → ℕ → ℝ :=
  fun j =>
    growthRegularityTolerance
      k j.1 (initialBound j.castSucc) F

/-- Ceiling preliminary-regularity budget at every non-top rank. -/
noncomputable def growthComplexRegularityBudget
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction) :
    (j : Fin r) → ℕ → ℕ :=
  fun j =>
    growthRegularityBudget
      k j.1 (initialBound j.castSucc) F

/-- Rankwise energy-pigeonhole length associated to the target `γ j`. -/
noncomputable def growthComplexRegularityLength
    (k r : ℕ) (γ : Fin r → ℝ) :
    Fin r → ℕ :=
  fun j =>
    growthRegularityLength k j.1 (γ j)

/-- Selected coarse complexity bound at one non-top rank. -/
noncomputable def selectedGrowthCoarseComplexityBound
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (index : Fin r → ℕ)
    (j : Fin r) : ℕ :=
  growthRegularityComplexity
    k j.1 (initialBound j.castSucc) F (index j)

/-- Selected fine complexity bound at one non-top rank. -/
noncomputable def selectedGrowthFineComplexityBound
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (index : Fin r → ℕ)
    (j : Fin r) : ℕ :=
  growthRegularityComplexity
    k j.1 (initialBound j.castSucc) F (index j + 1)

/-- Bound for every selected coarse layer.  The top layer is unchanged;
every lower layer uses its own selected triangular stage. -/
noncomputable def selectedGrowthCoarseLayerComplexityBound
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (index : Fin r → ℕ) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (initialBound (Fin.last r))
    (fun j =>
      selectedGrowthCoarseComplexityBound
        k r initialBound F index j)

/-- Bound for every selected fine layer, with the same unchanged top layer
and the following triangular stage at every lower rank. -/
noncomputable def selectedGrowthFineLayerComplexityBound
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (index : Fin r → ℕ) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (initialBound (Fin.last r))
    (fun j =>
      selectedGrowthFineComplexityBound
        k r initialBound F index j)

theorem growthComplexRegularityTolerance_pos
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction) :
    ∀ j n,
      0 <
        growthComplexRegularityTolerance
          k r initialBound F j n := by
  intro j n
  exact growthRegularityTolerance_pos
    k j.1 (initialBound j.castSucc) F n

theorem growthComplexRegularityBudget_spec
    (k r : ℕ)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction) :
    ∀ j n,
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
        (growthComplexRegularityBudget
            k r initialBound F j n : ℝ) *
          (growthComplexRegularityTolerance
            k r initialBound F j n) ^ 2 := by
  intro j n
  exact growthRegularityBudget_spec
    k j.1 (initialBound j.castSucc) F n

theorem growthComplexRegularityLength_pos
    (k r : ℕ) (γ : Fin r → ℝ) :
    ∀ j,
      0 <
        growthComplexRegularityLength k r γ j := by
  intro j
  exact growthRegularityLength_pos k j.1 (γ j)

/-! ## All-rank growth-function certificate -/

/-- Top-down all-rank fixed-upper regularity with growth-function errors and
rank-exact complexity bounds. -/
structure GrowthFunctionOrderedComplexRegularityCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (γ : Fin r → ℝ) where
  index : Fin r → ℕ
  coarse : OrderedPartitionComplex G k r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse
  coarse_refines_initial : coarse.Refines initial
  coarse_topLayer_eq :
    coarse.topLayer = initial.topLayer
  fine_topLayer_eq :
    fine.topLayer = initial.topLayer
  index_lt :
    ∀ j : Fin r,
      index j <
        growthRegularityLength k j.1 (γ j)
  regular :
    IsFullyPreliminaryOrderedRegular fine
      (fun j =>
        1 /
          (F (selectedGrowthCoarseComplexityBound
            k r initialBound F index j) : ℝ))
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
        γ j
  coarse_complexity :
    ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
      FacePartition.complexity
          (coarse.partition q e) ≤
        selectedGrowthCoarseLayerComplexityBound
          k r initialBound F index q
  fine_complexity :
    ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
      FacePartition.complexity
          (fine.partition q e) ≤
        selectedGrowthFineLayerComplexityBound
          k r initialBound F index q

namespace GrowthFunctionOrderedComplexRegularityCertificate

/-- Each rank of an all-rank certificate is itself the one-rank
growth-function certificate from `GrowthFunctionRegularity`, with the final
fine layer immediately above it frozen as the upper target. -/
def localCertificate
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) :
    GrowthFunctionFixedUpperCertificate
      G k j.1 (initialBound j.castSucc)
      (initial.partition j.castSucc)
      (R.fine.partition j.succ)
      F (γ j) where
  index := R.index j
  index_lt := R.index_lt j
  coarse := R.coarse.partition j.castSucc
  fine := R.fine.partition j.castSucc
  refines := R.refines j.castSucc
  coarse_refines_initial :=
    R.coarse_refines_initial j.castSucc
  fine_regular := by
    simpa [selectedGrowthCoarseComplexityBound] using
      R.regular j
  gap_nonneg := R.gap_nonneg j
  gap_le := R.gap_le j
  coarse_complexity := by
    intro e
    have h := R.coarse_complexity j.castSucc e
    simp only [selectedGrowthCoarseLayerComplexityBound,
      selectedGrowthCoarseComplexityBound,
      Fin.lastCases_castSucc] at h
    convert h using 1
  fine_complexity := by
    intro e
    have h := R.fine_complexity j.castSucc e
    simp only [selectedGrowthFineLayerComplexityBound,
      selectedGrowthFineComplexityBound,
      Fin.lastCases_castSucc] at h
    convert h using 1

/-- Exact selected bound for the coarse upper layer adjacent to rank `j`.
For the top adjacent rank this reduces to the unchanged initial top bound;
otherwise it is the selected coarse bound at rank `j + 1`. -/
theorem coarse_upper_complexity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    FacePartition.complexity
        (R.coarse.partition j.succ e) ≤
      selectedGrowthCoarseLayerComplexityBound
        k r initialBound F R.index j.succ :=
  R.coarse_complexity j.succ e

/-- Fine-upper analogue of `coarse_upper_complexity`. -/
theorem fine_upper_complexity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound F γ)
    (j : Fin r) (e : OrderedFace k (j.1 + 1)) :
    FacePartition.complexity
        (R.fine.partition j.succ e) ≤
      selectedGrowthFineLayerComplexityBound
        k r initialBound F R.index j.succ :=
  R.fine_complexity j.succ e

end GrowthFunctionOrderedComplexRegularityCertificate

/-! ## Existence by the top-down fixed-upper composition -/

/-- The one-rank growth-function selectors compose down all ranks.  This is
the existing source-faithful frozen-fine-upper recursion, instantiated with
the triangular schedules and with all bounds rewritten into their selected
growth-function form. -/
theorem GrowthFunctionOrderedComplexRegularityCertificate.nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (initial : OrderedPartitionComplex G k r)
    (initialBound : Fin (r + 1) → ℕ)
    (F : NatGrowthFunction)
    (γ : Fin r → ℝ)
    (hγ : ∀ j, 0 < γ j)
    (hinitial :
      ∀ (q : Fin (r + 1)) (e : OrderedFace k q.1),
        FacePartition.complexity
          (initial.partition q e) ≤ initialBound q) :
    Nonempty
      (GrowthFunctionOrderedComplexRegularityCertificate
        G k r initial initialBound F γ) := by
  let τ : (j : Fin r) → ℕ → ℝ :=
    growthComplexRegularityTolerance
      k r initialBound F
  let B : (j : Fin r) → ℕ → ℕ :=
    growthComplexRegularityBudget
      k r initialBound F
  let L : Fin r → ℕ :=
    growthComplexRegularityLength k r γ
  obtain ⟨R⟩ :=
    StrongOrderedComplexRegularityCertificate.nonempty
      initial τ B L
      (fun j n =>
        (growthComplexRegularityTolerance_pos
          k r initialBound F j n).le)
      (growthComplexRegularityBudget_spec
        k r initialBound F)
      (growthComplexRegularityLength_pos k r γ)
  refine ⟨{
    index := R.index
    coarse := R.coarse
    fine := R.fine
    refines := R.refines
    coarse_refines_initial :=
      R.coarse_refines_initial
    coarse_topLayer_eq := R.coarse_topLayer_eq
    fine_topLayer_eq := R.fine_topLayer_eq
    index_lt := ?_
    regular := ?_
    gap_nonneg := R.gap_nonneg
    gap_le := ?_
    coarse_complexity := ?_
    fine_complexity := ?_ }⟩
  · intro j
    simpa [L, growthComplexRegularityLength] using
      R.index_lt j
  · intro j
    have hregular := R.regular j
    simpa [τ, growthComplexRegularityTolerance,
      selectedOrderedComplexTolerance,
      selectedGrowthCoarseComplexityBound,
      growthRegularityTolerance_eq] using hregular
  · intro j
    exact (R.gap_le j).trans
      (by
        simpa [L, growthComplexRegularityLength] using
          (orderedFace_card_div_growthRegularityLength_lt
            (hγ j)).le)
  · intro q
    cases q using Fin.lastCases with
    | last =>
        intro e
        have htop := congrFun R.coarse_topLayer_eq e
        simp only [OrderedPartitionComplex.topLayer] at htop
        rw [htop]
        simpa [selectedGrowthCoarseLayerComplexityBound] using
          hinitial (Fin.last r) e
    | cast i =>
        intro e
        have hcomplexity := R.coarse_complexity i e
        calc
          FacePartition.complexity
              (R.coarse.partition i.castSucc e) ≤
              fixedUpperLayerComplexityFactor
                  i.1 (B i) (R.index i) *
                FacePartition.complexity
                  (initial.partition i.castSucc e) := by
            simpa [B, growthComplexRegularityBudget] using
              hcomplexity
          _ ≤
              fixedUpperLayerComplexityFactor
                  i.1 (B i) (R.index i) *
                initialBound i.castSucc :=
            Nat.mul_le_mul_left _
              (hinitial i.castSucc e)
          _ =
              selectedGrowthCoarseLayerComplexityBound
                k r initialBound F R.index i.castSucc := by
            simp only [
              selectedGrowthCoarseLayerComplexityBound,
              selectedGrowthCoarseComplexityBound,
              Fin.lastCases_castSucc]
            rw [growthRegularityComplexity_eq_factor_mul]
            rfl
  · intro q
    cases q using Fin.lastCases with
    | last =>
        intro e
        have htop := congrFun R.fine_topLayer_eq e
        simp only [OrderedPartitionComplex.topLayer] at htop
        rw [htop]
        simpa [selectedGrowthFineLayerComplexityBound] using
          hinitial (Fin.last r) e
    | cast i =>
        intro e
        have hcomplexity := R.fine_complexity i e
        calc
          FacePartition.complexity
              (R.fine.partition i.castSucc e) ≤
              fixedUpperLayerComplexityFactor
                  i.1 (B i) (R.index i + 1) *
                FacePartition.complexity
                  (initial.partition i.castSucc e) := by
            simpa [B, growthComplexRegularityBudget] using
              hcomplexity
          _ ≤
              fixedUpperLayerComplexityFactor
                  i.1 (B i) (R.index i + 1) *
                initialBound i.castSucc :=
            Nat.mul_le_mul_left _
              (hinitial i.castSucc e)
          _ =
              selectedGrowthFineLayerComplexityBound
                k r initialBound F R.index i.castSucc := by
            simp only [
              selectedGrowthFineLayerComplexityBound,
              selectedGrowthFineComplexityBound,
              Fin.lastCases_castSucc]
            rw [growthRegularityComplexity_eq_factor_mul]
            rfl

end Wikipedia.SzemeredisTheorem
