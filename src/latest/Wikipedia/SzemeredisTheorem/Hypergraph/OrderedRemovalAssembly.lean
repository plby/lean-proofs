import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedRemovalParameters
import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedRemovalTheorem

/-!
# Schedule-level assembly of ordered hypergraph removal

The structural regularity theorem accepts a tolerance schedule, a
weak-regularity budget at every stage, and one energy-selection length at
every rank.  `OrderedRemovalParameters` identifies the two numerical
inequalities those schedules must satisfy.  This file performs all remaining
quantifier and semantic assembly.

The main theorem is deliberately conditional on the existence of compatible
ambient-independent schedules.  It proves that such schedules imply
`HasUniformOrderedPatternRemoval`; no fixed point or diagonal selector is
assumed to have been constructed here.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## The canonical pattern complex has complexity at most two -/

/-- Every layer of the canonical edge-monochromatic input complex has at
most two atoms.  Lower layers are indiscrete and the top layer is generated
by one edge predicate. -/
theorem complexity_orderedPatternInitialComplex_le_two
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
      FacePartition.complexity
          ((orderedPatternInitialComplex H).partition j e) ≤ 2 := by
  intro j
  cases j using Fin.lastCases with
  | last =>
      intro e
      change
        FacePartition.complexity
            ((orderedPatternInitialComplex H).topLayer e) ≤ 2
      rw [orderedPatternInitialComplex_topLayer]
      exact complexity_orderedPatternTopPartition_le_two H e
  | cast i =>
      intro e
      simp [orderedPatternInitialComplex,
        indiscreteOrderedPartitionComplex,
        OrderedPartitionComplex.withTopLayer]

/-! ## Ambient-independent compatible schedules -/

/-- A complete schedule whose inequalities are strong enough for the
fine-configuration ordered-removal pipeline.

The bound in `tolerance_le` and `reciprocal_gap_le` uses only the displayed
natural schedules and `initialBound`, so the data are independent of the
ambient finite type and the input pattern. -/
structure OrderedRemovalSchedule
    (k r initialBound : ℕ) (ξ : ℝ) where
  tolerance : (j : Fin r) → ℕ → ℝ
  budget : (j : Fin r) → ℕ → ℕ
  length : Fin r → ℕ
  tolerance_pos : ∀ j n, 0 < tolerance j n
  budget_spec :
    ∀ j n,
      (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) <
        (budget j n : ℝ) * (tolerance j n) ^ 2
  length_pos : ∀ j, 0 < length j
  tolerance_le :
    ∀ j n,
      tolerance j n ≤
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

/-- Existence of one compatible schedule for every positive removal
allowance. -/
def HasOrderedRemovalSchedules
    (k r initialBound : ℕ) : Prop :=
  ∀ ξ : ℝ, 0 < ξ →
    Nonempty (OrderedRemovalSchedule k r initialBound ξ)

namespace OrderedRemovalSchedule

/-- Any certificate selected from a compatible schedule satisfies the
certificate-level compatibility predicate. -/
theorem certificateCompatible
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r initialBound : ℕ} {ξ : ℝ}
    {initial : OrderedPartitionComplex G k r}
    (S : OrderedRemovalSchedule k r initialBound ξ)
    (R : StrongOrderedComplexRegularityCertificate
      G k r initial S.tolerance S.budget S.length) :
    IsStrongOrderedRemovalCompatible
      (initialBound := initialBound) R ξ where
  tolerance_le j :=
    S.tolerance_le j (R.index j)
  reciprocal_gap_le :=
    S.reciprocal_gap_le

/-- A compatible schedule supplies a strong regularity certificate over
every ambient finite type and every initial complex. -/
theorem certificate_nonempty
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r initialBound : ℕ} {ξ : ℝ}
    (S : OrderedRemovalSchedule k r initialBound ξ)
    (initial : OrderedPartitionComplex G k r) :
    Nonempty
      (StrongOrderedComplexRegularityCertificate
        G k r initial S.tolerance S.budget S.length) := by
  exact StrongOrderedComplexRegularityCertificate.nonempty
    initial S.tolerance S.budget S.length
    (fun j n => (S.tolerance_pos j n).le)
    S.budget_spec S.length_pos

end OrderedRemovalSchedule

/-! ## Conditional uniform ordered removal -/

/-- Compatible ambient-independent schedules at successor rank imply the
uniform ordered-pattern removal theorem. -/
theorem hasUniformOrderedPatternRemoval_succ_of_schedules
    (k n : ℕ) (hrank : n + 1 ≤ k)
    (hschedules :
      HasOrderedRemovalSchedules k (n + 1) 2) :
    HasUniformOrderedPatternRemoval k (n + 1) := by
  intro ξ hξ
  let S : OrderedRemovalSchedule k (n + 1) 2 ξ :=
    Classical.choice (hschedules ξ hξ)
  let M : ℕ :=
    orderedRemovalFinePartitionComplexityBound
      (n + 1) 2 S.budget S.length
  let c : ℝ :=
    orderedRemovalConfigurationLowerBound k (n + 1)
      (orderedRemovalDensityFloor (n + 1) M ξ)
      (orderedRemovalCountingError k (n + 1) M ξ)
      (orderedRemovalCountingError k (n + 1) M ξ)
  have hc : 0 < c := by
    exact orderedRemovalConfigurationLowerBound_pos
      (k := k) (r := n + 1) (M := M) hξ
  refine ⟨c, hc, ?_⟩
  intro G instFintype instDecidableEq instNonempty H hcount
  let initial : OrderedPartitionComplex G k (n + 1) :=
    orderedPatternInitialComplex H
  obtain ⟨R⟩ := S.certificate_nonempty initial
  let P : OrderedCoarseFineComplex G k (n + 1) :=
    R.toCoarseFine
  let α : ℕ → ℝ :=
    orderedRemovalAlpha (n + 1) M ξ
  let β : ℕ → ℝ :=
    orderedRemovalBeta k (n + 1) M ξ
  let D : OrderedPattern.DeletionFamily
      (G := G) k (n + 1) :=
    orderedBadBaseDeletionFamily R.fine R.coarse α β
  have hinitial :
      R.fine.Refines (orderedPatternInitialComplex H) := by
    exact R.fine_refines_initial
  have hcompatible :
      IsStrongOrderedRemovalCompatible
        (initialBound := 2) R ξ :=
    S.certificateCompatible R
  have hcover : H.IsCover D := by
    apply orderedBadBaseDeletionFamily_isCover
      hrank H P hinitial α β
      (selectedOrderedComplexTolerance S.tolerance R.index)
      R.regular
      (orderedRemovalDensityFloor_nonneg hξ)
      (orderedRemovalCountingError_nonneg hξ)
      (orderedRemovalCountingError_nonneg hξ)
      (fun _ => le_rfl)
      hcompatible.tolerance_le
      (fun _ => orderedRemovalDefectThreshold_nonneg hξ)
      (fun _ => le_rfl)
    simpa [c, M, orderedRemovalConfigurationLowerBound,
      orderedRemovalConfigurationFaceCount] using hcount
  refine ⟨D, hcover, ?_⟩
  intro e
  exact R.faceDeletionDensity_badBase_le_removalAllowance
    (complexity_orderedPatternInitialComplex_le_two H)
    hξ hcompatible e

end Wikipedia.SzemeredisTheorem
