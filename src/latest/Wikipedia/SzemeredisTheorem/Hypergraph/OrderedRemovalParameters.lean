import Wikipedia.SzemeredisTheorem.Hypergraph.StrongOrderedComplexRegularity
import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedConfigurationCounting

/-!
# Quantitative parameters for ordered hypergraph removal

This file contains only the numerical layer of ordered removal.  Semantic
cover and contradiction arguments live elsewhere.

For a removal allowance `ξ > 0` and a uniform bound `M` on every selected
fine partition, write `S` for the number of positive subfaces of one top
face and `N` for the number of positive faces in the whole ordered
configuration.  We choose

```
ρ = min (1 / 2) (ξ / (4 * (S * M + 1))),
θ = ρ ^ N / (4 * (N + 1)),
α = ρ,   δ = η = θ,   β = θ²,
γ = ξ * β / 4.
```

Then the sharp cleaning error is at most

```
S * M * α + γ / β ≤ ξ / 2 < ξ,
```

whereas the configuration-count lower bound is strictly positive because

```
N * (η + δ) < ρ ^ N.
```

The final sections give ambient-independent ceiling schedules for weak
regularity and frozen-upper energy selection, derive a uniform complexity
bound from `StrongOrderedComplexRegularityCertificate`, and state bridge
theorems.  The bridge makes the remaining diagonal compatibility
transparent: the selected regularity tolerance must be at most `θ`, and
the reciprocal-timescale energy budget must be at most `γ`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Face counts and explicit thresholds -/

/-- Number of positive faces in the complete ordered configuration. -/
noncomputable def orderedRemovalConfigurationFaceCount (k r : ℕ) : ℕ :=
  Fintype.card (PositiveOrderedFace k r)

/-- Number of positive subfaces occurring below one top rank-`r` face. -/
noncomputable def orderedRemovalTopSubfaceCount (r : ℕ) : ℕ :=
  Fintype.card (OrderedPositiveSubface r)

/-- The product `S * M` which multiplies the low-density threshold in the
per-top-face cleaning estimate. -/
noncomputable def orderedRemovalComplexityCoefficient (r M : ℕ) : ℕ :=
  orderedRemovalTopSubfaceCount r * M

/-- Constant density floor and low-density cleaning threshold. -/
noncomputable def orderedRemovalDensityFloor
    (r M : ℕ) (ξ : ℝ) : ℝ :=
  min (1 / 2)
    (ξ /
      (4 *
        ((orderedRemovalComplexityCoefficient r M : ℝ) + 1)))

/-- Equal regularity and square-root defect error reserved for one
configuration-count recurrence step. -/
noncomputable def orderedRemovalCountingError
    (k r M : ℕ) (ξ : ℝ) : ℝ :=
  orderedRemovalDensityFloor r M ξ ^
      orderedRemovalConfigurationFaceCount k r /
    (4 *
      ((orderedRemovalConfigurationFaceCount k r : ℝ) + 1))

/-- Defect threshold used by good atoms. -/
noncomputable def orderedRemovalDefectThreshold
    (k r M : ℕ) (ξ : ℝ) : ℝ :=
  orderedRemovalCountingError k r M ξ ^ 2

/-- Frozen-upper total atom-energy target. -/
noncomputable def orderedRemovalEnergyGapTarget
    (k r M : ℕ) (ξ : ℝ) : ℝ :=
  ξ * orderedRemovalDefectThreshold k r M ξ / 4

/-- Constant rank schedule for low-density cleaning. -/
noncomputable def orderedRemovalAlpha
    (r M : ℕ) (ξ : ℝ) : ℕ → ℝ :=
  fun _ => orderedRemovalDensityFloor r M ξ

/-- Constant rank schedule for the good-atom defect threshold. -/
noncomputable def orderedRemovalBeta
    (k r M : ℕ) (ξ : ℝ) : ℕ → ℝ :=
  fun _ => orderedRemovalDefectThreshold k r M ξ

/-- Constant all-rank regularity tolerance required by counting. -/
noncomputable def orderedRemovalTolerance
    (k r M : ℕ) (ξ : ℝ) :
    OrderedRegularityTolerance r :=
  fun _ => orderedRemovalCountingError k r M ξ

/-- Abstract sharp cleaning error. -/
noncomputable def orderedRemovalDeletionError
    (r M : ℕ) (α gap β : ℝ) : ℝ :=
  (orderedRemovalComplexityCoefficient r M : ℝ) * α +
    gap / β

/-- Abstract lower bound supplied by the configuration-count recurrence. -/
noncomputable def orderedRemovalConfigurationLowerBound
    (k r : ℕ) (ρ η δ : ℝ) : ℝ :=
  ρ ^ orderedRemovalConfigurationFaceCount k r -
    (orderedRemovalConfigurationFaceCount k r : ℝ) *
      (η + δ)

theorem orderedRemovalDensityFloor_pos
    {r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    0 < orderedRemovalDensityFloor r M ξ := by
  unfold orderedRemovalDensityFloor
  apply lt_min
  · norm_num
  · exact div_pos hξ
      (mul_pos (by norm_num)
        (by positivity))

theorem orderedRemovalDensityFloor_nonneg
    {r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    0 ≤ orderedRemovalDensityFloor r M ξ :=
  (orderedRemovalDensityFloor_pos hξ).le

theorem orderedRemovalDensityFloor_le_half
    (r M : ℕ) (ξ : ℝ) :
    orderedRemovalDensityFloor r M ξ ≤ 1 / 2 := by
  unfold orderedRemovalDensityFloor
  exact min_le_left _ _

theorem orderedRemovalDensityFloor_le_fraction
    (r M : ℕ) (ξ : ℝ) :
    orderedRemovalDensityFloor r M ξ ≤
      ξ /
        (4 *
          ((orderedRemovalComplexityCoefficient r M : ℝ) + 1)) := by
  unfold orderedRemovalDensityFloor
  exact min_le_right _ _

theorem orderedRemovalCountingError_pos
    {k r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    0 < orderedRemovalCountingError k r M ξ := by
  unfold orderedRemovalCountingError
  exact div_pos
    (pow_pos (orderedRemovalDensityFloor_pos hξ) _)
    (mul_pos (by norm_num) (by positivity))

theorem orderedRemovalCountingError_nonneg
    {k r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    0 ≤ orderedRemovalCountingError k r M ξ :=
  (orderedRemovalCountingError_pos hξ).le

theorem orderedRemovalDefectThreshold_pos
    {k r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    0 < orderedRemovalDefectThreshold k r M ξ := by
  unfold orderedRemovalDefectThreshold
  exact sq_pos_of_pos
    (orderedRemovalCountingError_pos hξ)

theorem orderedRemovalDefectThreshold_nonneg
    {k r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    0 ≤ orderedRemovalDefectThreshold k r M ξ :=
  (orderedRemovalDefectThreshold_pos hξ).le

theorem orderedRemovalEnergyGapTarget_pos
    {k r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    0 < orderedRemovalEnergyGapTarget k r M ξ := by
  unfold orderedRemovalEnergyGapTarget
  exact div_pos
    (mul_pos hξ (orderedRemovalDefectThreshold_pos hξ))
    (by norm_num)

/-! ## Arithmetic margins -/

/-- The low-density part of cleaning consumes at most one quarter of the
requested removal allowance. -/
theorem orderedRemoval_complexity_mul_densityFloor_le_quarter
    {r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    (orderedRemovalComplexityCoefficient r M : ℝ) *
        orderedRemovalDensityFloor r M ξ ≤
      ξ / 4 := by
  let C : ℝ :=
    (orderedRemovalComplexityCoefficient r M : ℝ)
  have hC : 0 ≤ C := by
    exact Nat.cast_nonneg _
  have hden : 0 < C + 1 := by positivity
  have hfloor :
      orderedRemovalDensityFloor r M ξ ≤
        ξ / (4 * (C + 1)) := by
    exact orderedRemovalDensityFloor_le_fraction r M ξ
  calc
    C * orderedRemovalDensityFloor r M ξ ≤
        C * (ξ / (4 * (C + 1))) :=
      mul_le_mul_of_nonneg_left hfloor hC
    _ = (C / (C + 1)) * (ξ / 4) := by
      field_simp
    _ ≤ 1 * (ξ / 4) := by
      apply mul_le_mul_of_nonneg_right
      · exact (div_le_one hden).2 (by linarith)
      · positivity
    _ = ξ / 4 := one_mul _

/-- The chosen frozen-upper gap contributes exactly one further quarter
after division by the positive defect threshold. -/
theorem orderedRemovalEnergyGapTarget_div_defectThreshold
    {k r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    orderedRemovalEnergyGapTarget k r M ξ /
        orderedRemovalDefectThreshold k r M ξ =
      ξ / 4 := by
  unfold orderedRemovalEnergyGapTarget
  have hβ :
      orderedRemovalDefectThreshold k r M ξ ≠ 0 :=
    (orderedRemovalDefectThreshold_pos hξ).ne'
  field_simp

/-- The explicit thresholds make the abstract sharp cleaning error no
larger than the requested removal allowance. -/
theorem orderedRemovalDeletionError_le
    {k r M : ℕ} {ξ gap : ℝ}
    (hξ : 0 < ξ)
    (hgap :
      gap ≤ orderedRemovalEnergyGapTarget k r M ξ) :
    orderedRemovalDeletionError r M
        (orderedRemovalDensityFloor r M ξ)
        gap
        (orderedRemovalDefectThreshold k r M ξ) ≤
      ξ := by
  unfold orderedRemovalDeletionError
  have hβ :
      0 < orderedRemovalDefectThreshold k r M ξ :=
    orderedRemovalDefectThreshold_pos hξ
  calc
    (orderedRemovalComplexityCoefficient r M : ℝ) *
          orderedRemovalDensityFloor r M ξ +
        gap / orderedRemovalDefectThreshold k r M ξ ≤
        ξ / 4 +
          orderedRemovalEnergyGapTarget k r M ξ /
            orderedRemovalDefectThreshold k r M ξ := by
      exact add_le_add
        (orderedRemoval_complexity_mul_densityFloor_le_quarter hξ)
        (div_le_div_of_nonneg_right hgap hβ.le)
    _ = ξ / 2 := by
      rw [orderedRemovalEnergyGapTarget_div_defectThreshold hξ]
      ring
    _ ≤ ξ := by linarith

/-- The recurrence error reserved for all positive faces is strictly below
the product-density floor. -/
theorem orderedRemoval_counting_margin
    {k r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    (orderedRemovalConfigurationFaceCount k r : ℝ) *
        (orderedRemovalCountingError k r M ξ +
          orderedRemovalCountingError k r M ξ) <
      orderedRemovalDensityFloor r M ξ ^
        orderedRemovalConfigurationFaceCount k r := by
  let N : ℝ :=
    (orderedRemovalConfigurationFaceCount k r : ℝ)
  let p : ℝ :=
    orderedRemovalDensityFloor r M ξ ^
      orderedRemovalConfigurationFaceCount k r
  have hN : 0 ≤ N := by
    exact Nat.cast_nonneg _
  have hp : 0 < p := by
    exact pow_pos (orderedRemovalDensityFloor_pos hξ) _
  have hden : 0 < 4 * (N + 1) := by positivity
  have hcoeff :
      (2 * N) / (4 * (N + 1)) < 1 := by
    apply (div_lt_one hden).2
    linarith
  calc
    N *
        (orderedRemovalCountingError k r M ξ +
          orderedRemovalCountingError k r M ξ) =
        ((2 * N) / (4 * (N + 1))) * p := by
      unfold orderedRemovalCountingError
      dsimp only [N, p]
      ring
    _ < 1 * p :=
      mul_lt_mul_of_pos_right hcoeff hp
    _ = p := one_mul _

theorem orderedRemovalConfigurationLowerBound_pos
    {k r M : ℕ} {ξ : ℝ} (hξ : 0 < ξ) :
    0 <
      orderedRemovalConfigurationLowerBound k r
        (orderedRemovalDensityFloor r M ξ)
        (orderedRemovalCountingError k r M ξ)
        (orderedRemovalCountingError k r M ξ) := by
  unfold orderedRemovalConfigurationLowerBound
  have hmargin :=
    orderedRemoval_counting_margin
      (k := k) (r := r) (M := M) hξ
  linarith

/-! ## Ambient-independent ceiling schedules -/

/-- A ceiling budget which is long enough to run one preliminary
regularity pass at tolerance `τ`. -/
noncomputable def orderedRemovalRegularityBudget
    (k j : ℕ) (τ : ℝ) : ℕ :=
  Nat.ceil
      ((Fintype.card (OrderedFace k (j + 1)) : ℝ) /
        τ ^ 2) +
    1

/-- Apply the ceiling budget independently at every rank and tower stage. -/
noncomputable def orderedRemovalRegularityBudgetSchedule
    (k r : ℕ)
    (τ : (j : Fin r) → ℕ → ℝ) :
    (j : Fin r) → ℕ → ℕ :=
  fun j n => orderedRemovalRegularityBudget k j.1 (τ j n)

theorem orderedRemovalRegularityBudget_pos
    (k j : ℕ) (τ : ℝ) :
    0 < orderedRemovalRegularityBudget k j τ := by
  unfold orderedRemovalRegularityBudget
  omega

/-- The ceiling construction satisfies the strict energy-length
hypothesis of one fixed-upper preliminary regularity pass. -/
theorem orderedRemovalRegularityBudget_spec
    {k j : ℕ} {τ : ℝ} (hτ : 0 < τ) :
    (Fintype.card (OrderedFace k (j + 1)) : ℝ) <
      (orderedRemovalRegularityBudget k j τ : ℝ) * τ ^ 2 := by
  have hsq : 0 < τ ^ 2 := sq_pos_of_pos hτ
  have hquot :
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) /
          τ ^ 2 <
        (orderedRemovalRegularityBudget k j τ : ℝ) := by
    unfold orderedRemovalRegularityBudget
    calc
      (Fintype.card (OrderedFace k (j + 1)) : ℝ) /
            τ ^ 2 ≤
          (Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) /
                τ ^ 2) : ℝ) :=
        Nat.le_ceil _
      _ <
          (Nat.ceil
            ((Fintype.card
              (OrderedFace k (j + 1)) : ℝ) /
                τ ^ 2) : ℝ) + 1 := by
        linarith
      _ =
          ((Nat.ceil
              ((Fintype.card
                (OrderedFace k (j + 1)) : ℝ) /
                  τ ^ 2) + 1 : ℕ) : ℝ) := by
        norm_num
  exact (div_lt_iff₀ hsq).1 hquot

theorem orderedRemovalRegularityBudgetSchedule_spec
    {k r : ℕ}
    {τ : (j : Fin r) → ℕ → ℝ}
    (hτ : ∀ j n, 0 < τ j n) :
    ∀ j n,
      (Fintype.card
        (OrderedFace k (j.1 + 1)) : ℝ) <
        (orderedRemovalRegularityBudgetSchedule
          k r τ j n : ℝ) * (τ j n) ^ 2 := by
  intro j n
  exact orderedRemovalRegularityBudget_spec (hτ j n)

/-- A single common tower length large enough to make the sum of all
rankwise reciprocal energy budgets smaller than `γ`. -/
noncomputable def orderedRemovalEnergyTimescale
    (k r : ℕ) (γ : ℝ) : ℕ :=
  Nat.ceil (orderedAllRankAtomEnergyBudget k r / γ) + 1

/-- Constant rank schedule using `orderedRemovalEnergyTimescale`. -/
noncomputable def orderedRemovalEnergyLength
    (k r : ℕ) (γ : ℝ) : Fin r → ℕ :=
  fun _ => orderedRemovalEnergyTimescale k r γ

theorem orderedRemovalEnergyTimescale_pos
    (k r : ℕ) (γ : ℝ) :
    0 < orderedRemovalEnergyTimescale k r γ := by
  unfold orderedRemovalEnergyTimescale
  omega

theorem orderedRemovalEnergyLength_pos
    (k r : ℕ) (γ : ℝ) :
    ∀ j, 0 < orderedRemovalEnergyLength k r γ j := by
  intro j
  exact orderedRemovalEnergyTimescale_pos k r γ

/-- The common ceiling timescale makes the complete reciprocal-timescale
sum strictly smaller than its prescribed target. -/
theorem orderedRemovalEnergyLength_sum_div_lt
    {k r : ℕ} {γ : ℝ} (hγ : 0 < γ) :
    (∑ j : Fin r,
      (Fintype.card
        (OrderedFace k (j.1 + 1)) : ℝ) /
          (orderedRemovalEnergyLength k r γ j : ℝ)) <
      γ := by
  let B : ℝ := orderedAllRankAtomEnergyBudget k r
  let L : ℕ := orderedRemovalEnergyTimescale k r γ
  have hLNat : 0 < L :=
    orderedRemovalEnergyTimescale_pos k r γ
  have hLCast : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast hLNat
  have hquot : B / γ < (L : ℝ) := by
    dsimp only [B, L]
    unfold orderedRemovalEnergyTimescale
    calc
      orderedAllRankAtomEnergyBudget k r / γ ≤
          (Nat.ceil
            (orderedAllRankAtomEnergyBudget k r / γ) : ℝ) :=
        Nat.le_ceil _
      _ <
          (Nat.ceil
            (orderedAllRankAtomEnergyBudget k r / γ) : ℝ) + 1 := by
        linarith
      _ =
          ((Nat.ceil
              (orderedAllRankAtomEnergyBudget k r / γ) + 1 : ℕ) : ℝ) := by
        norm_num
  have hbudget : B < (L : ℝ) * γ :=
    (div_lt_iff₀ hγ).1 hquot
  unfold orderedRemovalEnergyLength
  change
    (∑ j : Fin r,
      (Fintype.card
        (OrderedFace k (j.1 + 1)) : ℝ) / (L : ℝ)) < γ
  rw [← Finset.sum_div]
  change B / (L : ℝ) < γ
  apply (div_lt_iff₀ hLCast).2
  simpa [mul_comm] using hbudget

/-! ## A uniform complexity bound for the strong certificate -/

/-- The explicit fixed-upper tower complexity factor grows monotonically
with the number of stages. -/
theorem fixedUpperLayerComplexityFactor_monotone
    (j : ℕ) (budget : ℕ → ℕ) :
    Monotone (fixedUpperLayerComplexityFactor j budget) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [fixedUpperLayerComplexityFactor]
  exact Nat.le_mul_of_pos_left _
    (pow_pos (by positivity) _)

/-- A deliberately coarse uniform bound for every rank of the selected
fine complex.  The sum dominates the factor at each non-top rank, while
the leading `1` also covers the unchanged top layer. -/
def orderedRemovalFinePartitionComplexityBound
    (r initialBound : ℕ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ) : ℕ :=
  initialBound *
    (1 +
      ∑ j : Fin r,
        fixedUpperLayerComplexityFactor
          j.1 (budget j) (length j))

theorem fixedUpperLayerComplexityFactor_le_removalBoundFactor
    {r : ℕ}
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ)
    (j : Fin r) :
    fixedUpperLayerComplexityFactor
        j.1 (budget j) (length j) ≤
      1 +
        ∑ i : Fin r,
          fixedUpperLayerComplexityFactor
            i.1 (budget i) (length i) := by
  have hsum :
      fixedUpperLayerComplexityFactor
          j.1 (budget j) (length j) ≤
        ∑ i : Fin r,
          fixedUpperLayerComplexityFactor
            i.1 (budget i) (length i) := by
    exact Finset.single_le_sum
      (fun i _ => Nat.zero_le
        (fixedUpperLayerComplexityFactor
          i.1 (budget i) (length i)))
      (Finset.mem_univ j)
  omega

namespace StrongOrderedComplexRegularityCertificate

/-- The certificate's stage indices and recursive complexity estimates
give one bound valid for every fine partition, including the unchanged top
layer. -/
theorem fine_complexity_le_removalBound
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r initialBound : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (hinitial :
      ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
        FacePartition.complexity
          (initial.partition j e) ≤ initialBound) :
    ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
      FacePartition.complexity
          (R.fine.partition j e) ≤
        orderedRemovalFinePartitionComplexityBound
          r initialBound budget length := by
  intro j
  cases j using Fin.lastCases with
  | last =>
      intro e
      have htop := congrFun R.fine_topLayer_eq e
      simp only [OrderedPartitionComplex.topLayer] at htop
      rw [htop]
      apply (hinitial (Fin.last r) e).trans
      unfold orderedRemovalFinePartitionComplexityBound
      exact Nat.le_mul_of_pos_right initialBound
        (by positivity)
  | cast i =>
      intro e
      have hcertificate := R.fine_complexity i e
      have hindex :
          R.index i + 1 ≤ length i :=
        R.index_lt i
      have hfactor :
          fixedUpperLayerComplexityFactor
              i.1 (budget i) (R.index i + 1) ≤
            fixedUpperLayerComplexityFactor
              i.1 (budget i) (length i) :=
        fixedUpperLayerComplexityFactor_monotone
          i.1 (budget i) hindex
      have hfactorBound :
          fixedUpperLayerComplexityFactor
              i.1 (budget i) (length i) ≤
            1 +
              ∑ q : Fin r,
                fixedUpperLayerComplexityFactor
                  q.1 (budget q) (length q) :=
        fixedUpperLayerComplexityFactor_le_removalBoundFactor
          budget length i
      calc
        FacePartition.complexity
            (R.fine.partition i.castSucc e) ≤
            fixedUpperLayerComplexityFactor
                i.1 (budget i) (R.index i + 1) *
              FacePartition.complexity
                (initial.partition i.castSucc e) :=
          hcertificate
        _ ≤
            fixedUpperLayerComplexityFactor
                i.1 (budget i) (R.index i + 1) *
              initialBound :=
          Nat.mul_le_mul_left _
            (hinitial i.castSucc e)
        _ ≤
            fixedUpperLayerComplexityFactor
                i.1 (budget i) (length i) *
              initialBound :=
          Nat.mul_le_mul_right initialBound hfactor
        _ ≤
            orderedRemovalFinePartitionComplexityBound
              r initialBound budget length := by
          unfold orderedRemovalFinePartitionComplexityBound
          simpa [Nat.mul_comm] using
            Nat.mul_le_mul_left initialBound hfactorBound

end StrongOrderedComplexRegularityCertificate

/-! ## Rank-sensitive target interface

The current counting theorem replaces every density floor by one global
`ρ` and every analytic error by global maxima `η, δ`.  The following
formulas record the sharper rank-dependent target without asserting a new
counting theorem.

* `orderedRemovalRankCleaningError` is the exact rankwise analogue of the
  sharp deletion estimate: upper complexity times `α`, plus the rank gap
  divided by `β`.
* `orderedRemovalRankDensityProduct` is the product of the actual
  rank-dependent density floors over all positive faces.
* `orderedRemovalRankCountingError` is one rank-dependent analytic error
  per positive face.

A rank-sensitive recurrence proving `count ≥ densityProduct - countingError`
would remove the present `min α` / `max ε` collapse.  Whether that interface,
together with a diagonal strong selector, closes the remaining schedule
feedback is deliberately left as a separate mathematical obligation.
-/

/-- Rank-dependent version of the sharp top-face cleaning error. -/
noncomputable def orderedRemovalRankCleaningError
    (r : ℕ)
    (complexity : Fin r → ℕ)
    (α : ℕ → ℝ)
    (gap : Fin r → ℝ)
    (β : ℕ → ℝ) : ℝ :=
  ∑ j : Fin r,
    ((Fintype.card
        (OrderedFace r (j.1 + 1)) : ℝ) *
        (complexity j : ℝ) * α (j.1 + 1) +
      gap j / β (j.1 + 1))

/-- Product of rank-dependent density floors over all positive ordered
faces in the complete configuration. -/
noncomputable def orderedRemovalRankDensityProduct
    (k r : ℕ) (α : ℕ → ℝ) : ℝ :=
  ∏ e : PositiveOrderedFace k r, α e.rank

/-- Sum of rank-dependent regularity and square-root defect errors over
all positive ordered faces. -/
noncomputable def orderedRemovalRankCountingError
    (k r : ℕ)
    (η : Fin r → ℝ)
    (δ : ℕ → ℝ) : ℝ :=
  ∑ e : PositiveOrderedFace k r,
    (η e.lowerRank + δ e.rank)

/-- Compact min/max-free numerical interface for a future rank-sensitive
counting recurrence and a rank-sensitive strong selector. -/
def IsRankSensitiveOrderedRemovalChoice
    (k r : ℕ) (ξ : ℝ)
    (complexity : Fin r → ℕ)
    (α β : ℕ → ℝ)
    (gap : Fin r → ℝ)
    (η : Fin r → ℝ)
    (δ : ℕ → ℝ) : Prop :=
  orderedRemovalRankCleaningError
      r complexity α gap β ≤ ξ ∧
    orderedRemovalRankCountingError k r η δ <
      orderedRemovalRankDensityProduct k r α

/-! ## Bridge from a compatible strong certificate -/

/-- The two explicit numerical obligations not supplied merely by the
current strong-certificate type:

1. its selected regularity tolerances fit below the counting scale derived
   from the uniform fine-complexity bound;
2. its reciprocal-timescale gap budget fits below the cleaning energy
   target derived from the same bound.

This is the precise compatibility target for a future diagonal or
rank-sensitive selector. -/
structure IsStrongOrderedRemovalCompatible
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r initialBound : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (ξ : ℝ) : Prop where
  tolerance_le :
    ∀ j : Fin r,
      selectedOrderedComplexTolerance ε R.index j ≤
        orderedRemovalCountingError k r
          (orderedRemovalFinePartitionComplexityBound
            r initialBound budget length) ξ
  reciprocal_gap_le :
    (∑ j : Fin r,
      (Fintype.card
        (OrderedFace k (j.1 + 1)) : ℝ) /
          (length j : ℝ)) ≤
      orderedRemovalEnergyGapTarget k r
        (orderedRemovalFinePartitionComplexityBound
          r initialBound budget length) ξ

namespace StrongOrderedComplexRegularityCertificate

/-- A compatible strong certificate makes every canonical bad-base
deletion cheaper than the requested removal allowance. -/
theorem faceDeletionDensity_badBase_le_removalAllowance
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r initialBound : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (hinitial :
      ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
        FacePartition.complexity
          (initial.partition j e) ≤ initialBound)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hcompatible :
      IsStrongOrderedRemovalCompatible
        (initialBound := initialBound) R ξ)
    (e : OrderedFace k r) :
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          R.fine R.coarse
          (orderedRemovalAlpha r
            (orderedRemovalFinePartitionComplexityBound
              r initialBound budget length) ξ)
          (orderedRemovalBeta k r
            (orderedRemovalFinePartitionComplexityBound
              r initialBound budget length) ξ)) e ≤
      ξ := by
  let M :=
    orderedRemovalFinePartitionComplexityBound
      r initialBound budget length
  let gap : ℝ :=
    ∑ j : Fin r,
      (Fintype.card
        (OrderedFace k (j.1 + 1)) : ℝ) /
          (length j : ℝ)
  change
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          R.fine R.coarse
          (fun _ => orderedRemovalDensityFloor r M ξ)
          (fun _ =>
            orderedRemovalDefectThreshold k r M ξ)) e ≤
      ξ
  have hdeletion :=
    R.faceDeletionDensity_badBase_constant_of_complexity_le_sum_div
      (M := M)
      (α := orderedRemovalDensityFloor r M ξ)
      (β := orderedRemovalDefectThreshold k r M ξ)
      (fun j e =>
        R.fine_complexity_le_removalBound
          hinitial j.succ e)
      (orderedRemovalDensityFloor_nonneg
        (r := r) (M := M) hξ)
      (orderedRemovalDefectThreshold_pos
        (k := k) (r := r) (M := M) hξ)
      e
  calc
    OrderedPattern.faceDeletionDensity
        (orderedBadBaseDeletionFamily
          R.fine R.coarse
          (fun _ => orderedRemovalDensityFloor r M ξ)
          (fun _ =>
            orderedRemovalDefectThreshold k r M ξ)) e ≤
        (Fintype.card (OrderedPositiveSubface r) : ℝ) *
            (M : ℝ) *
            orderedRemovalDensityFloor r M ξ +
          gap /
            orderedRemovalDefectThreshold k r M ξ := by
      simpa [M, gap] using hdeletion
    _ =
        orderedRemovalDeletionError r M
          (orderedRemovalDensityFloor r M ξ)
          gap
          (orderedRemovalDefectThreshold k r M ξ) := by
      unfold orderedRemovalDeletionError
        orderedRemovalComplexityCoefficient
        orderedRemovalTopSubfaceCount
      push_cast
      ring
    _ ≤ ξ :=
      orderedRemovalDeletionError_le hξ
        hcompatible.reciprocal_gap_le

/-- The explicit arithmetic lower bound is furnished by the current
configuration-count recurrence whenever the selected tolerance satisfies
the compatibility condition. -/
theorem removalConfigurationLowerBound_le_fullConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r initialBound : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (A : ClosedOrderedAtomConfiguration G k r R.fine)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hcompatible :
      IsStrongOrderedRemovalCompatible
        (initialBound := initialBound) R ξ)
    (hgood :
      A.IsGood R.fine R.coarse
        (orderedRemovalAlpha r
          (orderedRemovalFinePartitionComplexityBound
            r initialBound budget length) ξ)
        (orderedRemovalBeta k r
          (orderedRemovalFinePartitionComplexityBound
            r initialBound budget length) ξ)) :
    orderedRemovalConfigurationLowerBound k r
        (orderedRemovalDensityFloor r
          (orderedRemovalFinePartitionComplexityBound
            r initialBound budget length) ξ)
        (orderedRemovalCountingError k r
          (orderedRemovalFinePartitionComplexityBound
            r initialBound budget length) ξ)
        (orderedRemovalCountingError k r
          (orderedRemovalFinePartitionComplexityBound
            r initialBound budget length) ξ) ≤
      fullConfigurationCount A := by
  let M :=
    orderedRemovalFinePartitionComplexityBound
      r initialBound budget length
  unfold orderedRemovalConfigurationLowerBound
    orderedRemovalConfigurationFaceCount
  apply
    fullConfigurationCount_lower_bound
      R.toCoarseFine A
      (orderedRemovalAlpha r M ξ)
      (orderedRemovalBeta k r M ξ)
      hgood
      (selectedOrderedComplexTolerance ε R.index)
      R.regular
      (orderedRemovalDensityFloor_nonneg hξ)
      (orderedRemovalCountingError_nonneg hξ)
      (orderedRemovalCountingError_nonneg hξ)
      (fun _ => le_rfl)
      hcompatible.tolerance_le
      (fun _ =>
        orderedRemovalDefectThreshold_nonneg hξ)
      (fun _ => le_rfl)

/-- Every good closed configuration for a compatible certificate has
strictly positive normalized count. -/
theorem fullConfigurationCount_pos_of_removalParameters
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r initialBound : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial ε budget length)
    (A : ClosedOrderedAtomConfiguration G k r R.fine)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hcompatible :
      IsStrongOrderedRemovalCompatible
        (initialBound := initialBound) R ξ)
    (hgood :
      A.IsGood R.fine R.coarse
        (orderedRemovalAlpha r
          (orderedRemovalFinePartitionComplexityBound
            r initialBound budget length) ξ)
        (orderedRemovalBeta k r
          (orderedRemovalFinePartitionComplexityBound
            r initialBound budget length) ξ)) :
    0 < fullConfigurationCount A := by
  exact
    (orderedRemovalConfigurationLowerBound_pos
      (k := k) (r := r)
      (M := orderedRemovalFinePartitionComplexityBound
        r initialBound budget length) hξ).trans_le
      (R.removalConfigurationLowerBound_le_fullConfigurationCount
        A hξ hcompatible hgood)

end StrongOrderedComplexRegularityCertificate

end Wikipedia.SzemeredisTheorem
