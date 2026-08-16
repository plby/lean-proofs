import Wikipedia.SzemeredisTheorem.Hypergraph.GrowthFunctionComplexRegularity

/-!
# Finite-stage tower-dominating growth functions

The triangular regularity schedule at rank `j` has one-step map

```
T_{F,j}(M) =
  (2^(j+1))^(orderedRemovalRegularityBudget k j (1 / F(M))) * M.
```

It is circular to ask, without further proof, for one growth function to
dominate the tower map formed from its own reciprocal tolerance.  The finite
regularity argument does not need such a fixed point.  Instead, this file
constructs a sequence

```
F₀ = F,   F_{s+1} = majorant of F_s and every T_{F_s,j}, j < r.
```

The construction first takes bounded maxima in the complexity variable and
then a finite maximum over the relevant ranks.  Consequently every `F_s` is
monotone and strictly above the diagonal, while `F_{s+1}` dominates every
one-step map computed with `F_s`.  This gives the exact stage-shifted
inequality

```
M_{F_s,j}(n+1) ≤ F_{s+1}(M_{F_s,j}(n)).
```

The last section applies this inequality to every selected rank of
`GrowthFunctionOrderedComplexRegularityCertificate` and embeds each selected
coarse/fine pair in an honest one-step `DescendingGrowthHierarchy`.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## The one-step map and bounded envelopes -/

/-- One triangular complexity step at rank `j`, using the reciprocal
tolerance determined by `F` at the current complexity `M`. -/
noncomputable def growthRegularityOneStep
    (k j : ℕ) (F : NatGrowthFunction) (M : ℕ) : ℕ :=
  (2 ^ (j + 1)) ^
      growthRegularityStepBudget k j F M * M

@[simp]
theorem growthRegularityComplexity_succ_eq_oneStep
    (k j initialBound n : ℕ) (F : NatGrowthFunction) :
    growthRegularityComplexity
        k j initialBound F (n + 1) =
      growthRegularityOneStep k j F
        (growthRegularityComplexity
          k j initialBound F n) :=
  rfl

/-- Maximum of the rank-`j` one-step map on the interval `0, ..., M`.
The recursive definition avoids needing any monotonicity theorem for the
ceiling-containing one-step map itself. -/
noncomputable def boundedGrowthRegularityOneStepMaximum
    (k j : ℕ) (F : NatGrowthFunction) : ℕ → ℕ
  | 0 => growthRegularityOneStep k j F 0
  | M + 1 =>
      max
        (boundedGrowthRegularityOneStepMaximum k j F M)
        (growthRegularityOneStep k j F (M + 1))

theorem growthRegularityOneStep_le_boundedMaximum
    (k j : ℕ) (F : NatGrowthFunction)
    {m M : ℕ} (hm : m ≤ M) :
    growthRegularityOneStep k j F m ≤
      boundedGrowthRegularityOneStepMaximum k j F M := by
  induction M generalizing m with
  | zero =>
      have hmzero : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      rfl
  | succ M ih =>
      rw [boundedGrowthRegularityOneStepMaximum]
      by_cases hlast : m = M + 1
      · subst m
        exact le_max_right _ _
      · have hmM : m ≤ M := by omega
        exact (ih hmM).trans (le_max_left _ _)

theorem boundedGrowthRegularityOneStepMaximum_monotone
    (k j : ℕ) (F : NatGrowthFunction) :
    Monotone
      (boundedGrowthRegularityOneStepMaximum k j F) := by
  apply monotone_nat_of_le_succ
  intro M
  rw [boundedGrowthRegularityOneStepMaximum]
  exact le_max_left _ _

/-- Maximum of all bounded one-step envelopes at ranks
`0, ..., r - 1`. -/
noncomputable def finiteRankGrowthRegularityOneStepMaximum
    (k : ℕ) (F : NatGrowthFunction) (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 =>
      max
        (finiteRankGrowthRegularityOneStepMaximum k F M r)
        (boundedGrowthRegularityOneStepMaximum k r F M)

theorem growthRegularityOneStep_le_finiteRankMaximum
    (k : ℕ) (F : NatGrowthFunction)
    {j r m M : ℕ} (hj : j < r) (hm : m ≤ M) :
    growthRegularityOneStep k j F m ≤
      finiteRankGrowthRegularityOneStepMaximum k F M r := by
  induction r generalizing j with
  | zero =>
      omega
  | succ r ih =>
      rw [finiteRankGrowthRegularityOneStepMaximum]
      by_cases hjlast : j = r
      · subst j
        exact
          (growthRegularityOneStep_le_boundedMaximum
            k r F hm).trans (le_max_right _ _)
      · have hjr : j < r := by omega
        exact (ih hjr).trans (le_max_left _ _)

theorem finiteRankGrowthRegularityOneStepMaximum_monotone
    (k r : ℕ) (F : NatGrowthFunction) :
    Monotone
      (fun M =>
        finiteRankGrowthRegularityOneStepMaximum
          k F M r) := by
  intro a b hab
  induction r with
  | zero =>
      simp [finiteRankGrowthRegularityOneStepMaximum]
  | succ r ih =>
      simp only [finiteRankGrowthRegularityOneStepMaximum]
      exact max_le_max ih
        (boundedGrowthRegularityOneStepMaximum_monotone
          k r F hab)

/-! ## One majorant stage -/

/-- The next tower-dominating stage.  At input `M` it simultaneously
dominates `M + 1`, the old value `F M`, and every rank-`j` one-step value
at every input at most `M`, for `j < r`. -/
noncomputable def towerDominatingGrowth
    (k r : ℕ) (F : NatGrowthFunction) :
    NatGrowthFunction where
  toFun M :=
    max (M + 1)
      (max (F M)
        (finiteRankGrowthRegularityOneStepMaximum
          k F M r))
  monotone' := by
    intro a b hab
    exact max_le_max
      (Nat.add_le_add_right hab 1)
      (max_le_max
        (F.monotone hab)
        (finiteRankGrowthRegularityOneStepMaximum_monotone
          k r F hab))
  above_diagonal := by
    intro M
    exact le_max_left _ _

@[simp]
theorem towerDominatingGrowth_apply
    (k r : ℕ) (F : NatGrowthFunction) (M : ℕ) :
    towerDominatingGrowth k r F M =
      max (M + 1)
        (max (F M)
          (finiteRankGrowthRegularityOneStepMaximum
            k F M r)) :=
  rfl

/-- A majorant stage pointwise dominates the preceding growth function. -/
theorem le_towerDominatingGrowth
    (k r : ℕ) (F : NatGrowthFunction) (M : ℕ) :
    F M ≤ towerDominatingGrowth k r F M := by
  rw [towerDominatingGrowth_apply]
  exact (le_max_left _ _).trans (le_max_right _ _)

/-- The stronger bounded-input version of pointwise domination. -/
theorem growthFunction_le_towerDominatingGrowth_of_le
    (k r : ℕ) (F : NatGrowthFunction)
    {m M : ℕ} (hm : m ≤ M) :
    F m ≤ towerDominatingGrowth k r F M := by
  exact (F.monotone hm).trans
    (le_towerDominatingGrowth k r F M)

/-- A majorant stage dominates every relevant one-step map, uniformly for
all inputs below the displayed argument. -/
theorem growthRegularityOneStep_le_towerDominatingGrowth
    (k r : ℕ) (F : NatGrowthFunction)
    (j : Fin r) {m M : ℕ} (hm : m ≤ M) :
    growthRegularityOneStep k j.1 F m ≤
      towerDominatingGrowth k r F M := by
  rw [towerDominatingGrowth_apply]
  exact
    (growthRegularityOneStep_le_finiteRankMaximum
      k F j.isLt hm).trans
      ((le_max_right _ _).trans (le_max_right _ _))

/-! ## Iterated finite-stage closure -/

/-- Iteration of the finite tower-majorant operation, starting from the
requested growth function at stage zero. -/
noncomputable def towerDominatingGrowthIteration
    (k r : ℕ) (F : NatGrowthFunction) :
    ℕ → NatGrowthFunction
  | 0 => F
  | stage + 1 =>
      towerDominatingGrowth k r
        (towerDominatingGrowthIteration k r F stage)

@[simp]
theorem towerDominatingGrowthIteration_zero
    (k r : ℕ) (F : NatGrowthFunction) :
    towerDominatingGrowthIteration k r F 0 = F :=
  rfl

@[simp]
theorem towerDominatingGrowthIteration_succ
    (k r : ℕ) (F : NatGrowthFunction) (stage : ℕ) :
    towerDominatingGrowthIteration k r F (stage + 1) =
      towerDominatingGrowth k r
        (towerDominatingGrowthIteration k r F stage) :=
  rfl

/-- Every finite closure stage pointwise dominates the requested growth
function. -/
theorem le_towerDominatingGrowthIteration
    (k r : ℕ) (F : NatGrowthFunction) :
    ∀ stage M,
      F M ≤ towerDominatingGrowthIteration k r F stage M := by
  intro stage
  induction stage with
  | zero =>
      intro M
      exact le_rfl
  | succ stage ih =>
      intro M
      exact (ih M).trans
        (le_towerDominatingGrowth k r
          (towerDominatingGrowthIteration k r F stage) M)

/-- Consecutive closure stages are pointwise nested. -/
theorem towerDominatingGrowthIteration_le_succ
    (k r : ℕ) (F : NatGrowthFunction)
    (stage M : ℕ) :
    towerDominatingGrowthIteration k r F stage M ≤
      towerDominatingGrowthIteration k r F (stage + 1) M := by
  exact le_towerDominatingGrowth k r
    (towerDominatingGrowthIteration k r F stage) M

/-- The defining stage-shifted domination: the next closure stage
dominates every one-step map formed using the current closure stage. -/
theorem growthRegularityOneStep_le_nextGrowthIteration
    (k r : ℕ) (F : NatGrowthFunction)
    (stage : ℕ) (j : Fin r) {m M : ℕ} (hm : m ≤ M) :
    growthRegularityOneStep k j.1
        (towerDominatingGrowthIteration k r F stage) m ≤
      towerDominatingGrowthIteration k r F (stage + 1) M := by
  exact growthRegularityOneStep_le_towerDominatingGrowth
    k r
    (towerDominatingGrowthIteration k r F stage)
    j hm

/-- Exact coupling of the triangular schedule at stage `stage` to the
growth function at stage `stage + 1`. -/
theorem growthRegularityComplexity_succ_le_nextGrowthIteration
    (k r initialBound : ℕ) (F : NatGrowthFunction)
    (stage n : ℕ) (j : Fin r) :
    growthRegularityComplexity
        k j.1 initialBound
          (towerDominatingGrowthIteration k r F stage)
          (n + 1) ≤
      towerDominatingGrowthIteration k r F (stage + 1)
        (growthRegularityComplexity
          k j.1 initialBound
            (towerDominatingGrowthIteration k r F stage)
            n) := by
  rw [growthRegularityComplexity_succ_eq_oneStep]
  exact growthRegularityOneStep_le_nextGrowthIteration
    k r F stage j le_rfl

/-- Passing to a finite closure stage can only decrease the reciprocal
tolerance relative to the originally requested growth function. -/
theorem towerDominatingGrowthIteration_reciprocal_le
    (k r : ℕ) (F : NatGrowthFunction)
    (stage M : ℕ) :
    1 /
        (towerDominatingGrowthIteration
          k r F stage M : ℝ) ≤
      1 / (F M : ℝ) := by
  apply one_div_le_one_div_of_le
  · exact_mod_cast F.positive M
  · exact_mod_cast
      le_towerDominatingGrowthIteration
        k r F stage M

/-! ## Finite maxima for simultaneous hierarchy bounds -/

/-- Maximum of a finite family of natural numbers.  The recursive
`Fin.lastCases` presentation is convenient for later all-layer bounds and
does not introduce a choice of an optimizing index. -/
def finiteMaximum : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, value =>
      max
        (finiteMaximum n (fun i => value i.castSucc))
        (value (Fin.last n))

/-- Every member of a finite family is bounded by `finiteMaximum`. -/
theorem le_finiteMaximum :
    ∀ {n : ℕ} (value : Fin n → ℕ) (i : Fin n),
      value i ≤ finiteMaximum n value
  | 0, _, i => Fin.elim0 i
  | n + 1, value, i => by
      cases i using Fin.lastCases with
      | last =>
          rw [finiteMaximum]
          exact le_max_right _ _
      | cast i =>
          rw [finiteMaximum]
          exact
            (le_finiteMaximum
              (fun q => value q.castSucc) i).trans
              (le_max_left _ _)

/-! ## Bridge to selected all-rank certificates -/

namespace GrowthFunctionOrderedComplexRegularityCertificate

/-- At every independently selected rank, the fine triangular bound formed
using stage `s` lies below stage `s + 1` applied to the selected coarse
bound. -/
theorem selectedFineComplexity_le_nextGrowthIteration
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (j : Fin r) :
    selectedGrowthFineComplexityBound
        k r initialBound
          (towerDominatingGrowthIteration k r F stage)
          R.index j ≤
      towerDominatingGrowthIteration k r F (stage + 1)
        (selectedGrowthCoarseComplexityBound
          k r initialBound
            (towerDominatingGrowthIteration k r F stage)
            R.index j) := by
  exact growthRegularityComplexity_succ_le_nextGrowthIteration
    k r (initialBound j.castSucc) F stage (R.index j) j

/-- A certificate constructed with a finite closure stage satisfies the
weaker reciprocal tolerance requested from the original growth function,
evaluated at the same selected coarse bounds. -/
theorem regular_with_requestedGrowth
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ) :
    IsFullyPreliminaryOrderedRegular R.fine
      (fun j =>
        1 /
          (F (selectedGrowthCoarseComplexityBound
            k r initialBound
              (towerDominatingGrowthIteration k r F stage)
              R.index j) : ℝ)) := by
  intro j e a b
  exact (R.regular j e a b).trans
    (towerDominatingGrowthIteration_reciprocal_le
      k r F stage
      (selectedGrowthCoarseComplexityBound
        k r initialBound
          (towerDominatingGrowthIteration k r F stage)
          R.index j))

/-- The exact one-link descending hierarchy associated to a selected rank.
Its lower level is the selected coarse bound and its upper level is the next
majorant stage applied to that bound. -/
noncomputable def selectedRankTowerHierarchy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (j : Fin r) :
    DescendingGrowthHierarchy
      (towerDominatingGrowthIteration k r F (stage + 1)) 1 :=
  canonicalDescendingGrowthHierarchy
    (towerDominatingGrowthIteration k r F (stage + 1)) 1
    (selectedGrowthCoarseComplexityBound
      k r initialBound
        (towerDominatingGrowthIteration k r F stage)
        R.index j)

@[simp]
theorem selectedRankTowerHierarchy_last
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (j : Fin r) :
    (selectedRankTowerHierarchy R j).level (Fin.last 1) =
      selectedGrowthCoarseComplexityBound
        k r initialBound
          (towerDominatingGrowthIteration k r F stage)
          R.index j := by
  exact canonicalDescendingGrowthHierarchy_last
    (towerDominatingGrowthIteration k r F (stage + 1)) 1
    (selectedGrowthCoarseComplexityBound
      k r initialBound
        (towerDominatingGrowthIteration k r F stage)
        R.index j)

@[simp]
theorem selectedRankTowerHierarchy_zero
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (j : Fin r) :
    (selectedRankTowerHierarchy R j).level 0 =
      towerDominatingGrowthIteration k r F (stage + 1)
        (selectedGrowthCoarseComplexityBound
          k r initialBound
            (towerDominatingGrowthIteration k r F stage)
            R.index j) := by
  simp [selectedRankTowerHierarchy]

/-- Thus the selected fine bound is genuinely nested below the upper member
of the associated descending hierarchy. -/
theorem selectedFineComplexity_le_selectedRankTowerHierarchy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (j : Fin r) :
    selectedGrowthFineComplexityBound
        k r initialBound
          (towerDominatingGrowthIteration k r F stage)
          R.index j ≤
      (selectedRankTowerHierarchy R j).level 0 := by
  rw [selectedRankTowerHierarchy_zero]
  exact R.selectedFineComplexity_le_nextGrowthIteration j

/-- The actual selected fine partition at rank `j` obeys the same hierarchy
upper bound, not merely its numerical triangular schedule. -/
theorem finePartitionComplexity_le_selectedRankTowerHierarchy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (j : Fin r) (e : OrderedFace k j.1) :
    FacePartition.complexity
        (R.fine.partition j.castSucc e) ≤
      (selectedRankTowerHierarchy R j).level 0 := by
  exact
    ((R.localCertificate j).fine_complexity e).trans
      (R.selectedFineComplexity_le_selectedRankTowerHierarchy j)

/-! ### One hierarchy containing all independently selected layers -/

/-- A single numerical bound containing all selected fine-layer bounds,
including the unchanged top layer. -/
noncomputable def selectedFineLayerMaximum
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ) : ℕ :=
  finiteMaximum (r + 1)
    (selectedGrowthFineLayerComplexityBound
      k r initialBound
        (towerDominatingGrowthIteration k r F stage)
        R.index)

/-- A canonical depth-`r` descending hierarchy whose bottom already
dominates every independently selected fine-layer bound.  This is coarse,
but it is simultaneous and its adjacent growth equalities are exact. -/
noncomputable def selectedAllRankTowerHierarchy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ) :
    DescendingGrowthHierarchy
      (towerDominatingGrowthIteration k r F (stage + 1)) r :=
  canonicalDescendingGrowthHierarchy
    (towerDominatingGrowthIteration k r F (stage + 1)) r
    (selectedFineLayerMaximum R)

@[simp]
theorem selectedAllRankTowerHierarchy_last
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ) :
    (selectedAllRankTowerHierarchy R).level (Fin.last r) =
      selectedFineLayerMaximum R := by
  exact canonicalDescendingGrowthHierarchy_last
    (towerDominatingGrowthIteration k r F (stage + 1)) r
    (selectedFineLayerMaximum R)

/-- Every selected fine-layer numerical bound is nested below the
correspondingly indexed member of the simultaneous hierarchy. -/
theorem selectedFineLayerComplexity_le_allRankTowerHierarchy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (q : Fin (r + 1)) :
    selectedGrowthFineLayerComplexityBound
        k r initialBound
          (towerDominatingGrowthIteration k r F stage)
          R.index q ≤
      (selectedAllRankTowerHierarchy R).level q := by
  calc
    selectedGrowthFineLayerComplexityBound
          k r initialBound
            (towerDominatingGrowthIteration k r F stage)
            R.index q ≤
        selectedFineLayerMaximum R := by
          exact le_finiteMaximum _ q
    _ =
        (selectedAllRankTowerHierarchy R).level
          (Fin.last r) := by
          symm
          exact selectedAllRankTowerHierarchy_last R
    _ ≤
        (selectedAllRankTowerHierarchy R).level q := by
          exact (selectedAllRankTowerHierarchy R).antitone
            (Fin.le_last q)

/-- Consequently every actual partition in the selected fine complex is
bounded by its corresponding level of one simultaneous exact hierarchy. -/
theorem fineComplexity_le_allRankTowerHierarchy
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {γ : Fin r → ℝ}
    {stage : ℕ}
    (R : GrowthFunctionOrderedComplexRegularityCertificate
      G k r initial initialBound
        (towerDominatingGrowthIteration k r F stage) γ)
    (q : Fin (r + 1)) (e : OrderedFace k q.1) :
    FacePartition.complexity
        (R.fine.partition q e) ≤
      (selectedAllRankTowerHierarchy R).level q := by
  exact (R.fine_complexity q e).trans
    (R.selectedFineLayerComplexity_le_allRankTowerHierarchy q)

end GrowthFunctionOrderedComplexRegularityCertificate

end Wikipedia.SzemeredisTheorem
