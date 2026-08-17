/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.Claim44Numerics
import ErdosProblems.Erdos63.Claim46Growth
import ErdosProblems.Erdos63.SourceLemma37Numerics

/-!
# Canonical graph-free parameters for Liu--Montgomery Lemma 4.3

This file puts the numerical interfaces of Claims 4.4--4.6 on one common
choice of parameters.  It contains no graph.  In particular, it separates
the exact finite arithmetic still required by `LM44Scale` and the
source-faithful Lemma 3.7 bridge from the bookkeeping which is automatic.

The end order and deletion budget are the ones consumed by Lemma 4.7.
Candidate adjusters use the source radius `5 * lmGrowthRounds n'`, where
`n'` is the order of the extracted expander.  The three Lemma 3.7 calls use
the distinct source clock `(log log N)^20` and the literal small-sample
multiplicity `r^2`.
-/

open Filter Finset
open scoped BigOperators

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ## The canonical parameters -/

/-- End order required by the corrected Lemma 4.7 induction.  The degree
parameter is retained in the signature so every Lemma 4.3 parameter has the
same `(N,d)` interface. -/
noncomputable def lm43TargetOrder (N d : ℕ) : ℕ :=
  lm47InflatedOrder N

/-- Deletion budget required by the corrected Lemma 4.7 induction. -/
noncomputable def lm43DeletionCap (N d : ℕ) : ℕ :=
  lm47SimpleBudget N

/-- The post-deletion average-degree scale in Claim 4.4. -/
def lm43InitialDegree (N d : ℕ) : ℕ := d / 4

/-- The minimum-degree scale of the expander extracted in Claim 4.4. -/
def lm43CoreDegree (N d : ℕ) : ℕ := d / 64

/-- Candidate radius at an extracted subgraph order `n'`. -/
noncomputable def lm43CoreRadius (n' : ℕ) : ℕ :=
  5 * lmGrowthRounds n'

/-- Lower endpoint for the variable source radius interval. -/
noncomputable def lm43MinRadiusFrom (coreDegree : ℕ) : ℕ :=
  lm43CoreRadius (coreDegree + 1)

/-- Ambient upper endpoint for the variable source radius interval. -/
noncomputable def lm43CandidateRadius (N d : ℕ) : ℕ :=
  lm43CoreRadius N

noncomputable def lm43MinRadius (N d : ℕ) : ℕ :=
  lm43MinRadiusFrom (lm43CoreDegree N d)

noncomputable def lm43MaxRadius (N d : ℕ) : ℕ :=
  lm43CandidateRadius N d

/-- The source avoiding-ball clock `ell₀ = (log log N)^20`. -/
noncomputable def lm43AvoidingRadius (N : ℕ) : ℕ :=
  ⌈Real.log (Real.log (N : ℝ)) ^ 20⌉₊

noncomputable def lm43HighRadius (N d : ℕ) : ℕ :=
  lm43AvoidingRadius N

noncomputable def lm43BallRadius (N d : ℕ) : ℕ :=
  lm43AvoidingRadius N

/-- Radius of the last two-set connectors.  This is the multiplicative
growth clock used by `LM42GrowthSchedule`, distinct from the iterated-log
clock of the preceding Lemma 3.7 ball. -/
noncomputable def lm43FinalConnectorRadius (N d : ℕ) : ℕ :=
  lmGrowthRounds N

/-- Connection radius to the auxiliary target expansion. -/
noncomputable def lm43TargetRadius (N d : ℕ) : ℕ :=
  lm43BallRadius N d + 2 * (lm43FinalConnectorRadius N d + 1)

/-- Separation used by the maximal family. -/
noncomputable def lm43Separation (N d : ℕ) : ℕ :=
  10 * lm43AvoidingRadius N

/-- Radius in the output statement used by the exact-path argument. -/
noncomputable def lm43TotalRadius (N d : ℕ) : ℕ :=
  2 * lm43MaxRadius N d

/-- Source high-degree cutoff `Delta = 200 m D`, using the ambient upper
candidate radius.  It is deliberately not enlarged to `d`: the high-degree
case in Claim 4.4 is part of the argument, and a cutoff depending linearly on
`N` would destroy the forbidden-ball estimate. -/
noncomputable def lm43HighCutoff (N d : ℕ) : ℕ :=
  200 * lm43MaxRadius N d * lm43TargetOrder N d

/-- The Proposition 3.16 threshold used for neighbours in the deleted set. -/
def lm43DegreeInto (N d : ℕ) : ℕ := d / 2

/-- A graph-independent upper budget for
`deleted ∪ manyNeighborsInto deleted (d/2)`. -/
noncomputable def lm43ProtectedCap (N d : ℕ) : ℕ :=
  lm43DeletionCap N d + 100 * lm43TargetOrder N d ^ 2

/-- The survivor count needed by the final cardinality contradiction. -/
noncomputable def lm43FamilyTarget (N d : ℕ) : ℕ :=
  SourceLemma35Numerics.indexCard N

/-- The source parameter `R`; Claim 4.4 constructs at least `4R`
candidates, and Claims 4.5 and 4.6 each discard fewer than `R`. -/
noncomputable def lm43R (N d : ℕ) : ℕ :=
  lm43FamilyTarget N d

/-- Target order for the larger Lemma 3.7 balls used in Claim 4.6 and in the
final two-ended growth step.  Claim 4.5 alone retains `lm43TargetOrder`. -/
noncomputable def lm43BallTarget (N d : ℕ) : ℕ :=
  10 * lm43MaxRadius N d ^ 2 * lm43TargetOrder N d

/-- Fixed forbidden workspace for the last connector. -/
noncomputable def lm43FinalConnectorWorkspace (N d : ℕ) : ℕ :=
  lm43DeletionCap N d + 10 * lm43MaxRadius N d

/-- Bootstrap-aware starting size for the last connector.  If the adaptive
cutoff is no larger than the endpoint target, the connector starts inside
that endpoint.  Otherwise the complementary degree branch pays for the
start and its workspace. -/
noncomputable def lm43FinalConnectorStart (N d : ℕ) : ℕ :=
  max (lm311AdaptiveSeed d) (lm43BallTarget N d)

/-- Exact occupied-seed cap in Claim 4.4. -/
noncomputable def lm43Claim44SeedCap (N d : ℕ) : ℕ :=
  lm43ProtectedCap N d + 4 * lm43R N d *
    (2 * lm43MaxRadius N d ^ 2 + 10 * lm43MaxRadius N d)

/-- Exact forbidden-ball cap in Claim 4.4. -/
noncomputable def lm43Claim44BallCap (N d : ℕ) : ℕ :=
  lm43Claim44SeedCap N d *
    (lm43HighCutoff N d + 1) ^ lm43Separation N d

/-- Exact star-replacement workspace in Claim 4.4. -/
noncomputable def lm43Claim44StarBudget (N d : ℕ) : ℕ :=
  lm43DeletionCap N d + 10 * lm43MaxRadius N d +
    lm43TargetOrder N d + 1

/-- Largest slow-ball size in the source Lemma 3.7 split.  It contains the
source subpolynomial envelope, the cutoff, and both requested targets.
Using merely `cutoff^2` here would be too small for the robust target. -/
noncomputable def lm43MaxSlowSize (N d : ℕ) : ℕ :=
  max (SourceLemma35Numerics.deletionCap N)
    (max (SourceLemma35Numerics.cutoff N)
      (max (lm43TargetOrder N d) (lm43BallTarget N d)))

/-- Source-faithful small-failure sampling multiplicity. -/
def lm43SmallMultiplicity (r : ℕ) : ℕ :=
  lm37SourceSmallSample r

theorem lm43SmallMultiplicity_pos {r : ℕ} (hr : 0 < r) :
    0 < lm43SmallMultiplicity r := by
  simpa [lm43SmallMultiplicity, lm37SourceSmallSample] using
    SourceLemma35Numerics.qSmall_pos hr

theorem lm43TargetOrder_le_maxSlowSize (N d : ℕ) :
    lm43TargetOrder N d ≤ lm43MaxSlowSize N d := by
  simp only [lm43MaxSlowSize]
  omega

theorem lm43BallTarget_le_maxSlowSize (N d : ℕ) :
    lm43BallTarget N d ≤ lm43MaxSlowSize N d := by
  simp only [lm43MaxSlowSize]
  omega

theorem lm43Cutoff_le_maxSlowSize (N d : ℕ) :
    SourceLemma35Numerics.cutoff N ≤ lm43MaxSlowSize N d := by
  simp only [lm43MaxSlowSize]
  omega

/-- Source-faithful Lemma 3.7 package required by Claim 4.5. -/
abbrev LM43Claim45SourceBounds (N d maxSlowSize : ℕ) :=
  LM37SourceReachBounds N d (lm43DeletionCap N d) 2
    (lm43HighRadius N d) (lm43TargetOrder N d) (lm43DegreeInto N d)
    maxSlowSize

/-- Source-faithful Lemma 3.7 package required by Claim 4.6. -/
abbrev LM43Claim46SourceBounds (N d maxSlowSize : ℕ) :=
  LM37SourceReachBounds N d (lm43DeletionCap N d) 2
    (lm43BallRadius N d) (lm43BallTarget N d) (lm43DegreeInto N d)
    maxSlowSize

/-- Source-faithful final two-ended package, with the same larger target
`10 * maxRadius^2 * targetOrder` as Claim 4.6. -/
abbrev LM43FinalSourceBounds (N d maxSlowSize : ℕ) :=
  LM37SourceFinalTwoEndBounds N d (lm43DeletionCap N d) 0
    (lm43BallRadius N d) (lm43MaxRadius N d) (lm43TargetOrder N d)
    (lm43DegreeInto N d) maxSlowSize

/-! ## The top-level graph-free certificate -/

/-- All graph-free certificates consumed by robust Lemma 4.3, with every
source parameter fixed.  This structure deliberately asserts no eventual
existence: its four fields are the exact remaining numerical obligations. -/
structure LM43NumericalPackage (N d : ℕ) where
  claim44 : SmallSimpleAdjusterCandidate.LM44Scale N d
    (lm43TargetOrder N d) (lm43TotalRadius N d) (lm43HighCutoff N d)
    (lm43DeletionCap N d) (lm43ProtectedCap N d) (lm43Separation N d)
    (lm43MinRadius N d) (lm43MaxRadius N d) (lm43R N d)
    ((1 / 64) * (lm43CoreDegree N d : ℝ))
  claim45 : lm37SourceMinSize d < lm43TargetOrder N d →
    LM43Claim45SourceBounds N d (lm43MaxSlowSize N d)
  claim46 : lm37SourceMinSize d < lm43BallTarget N d →
    LM43Claim46SourceBounds N d (lm43MaxSlowSize N d)
  final : lm37SourceMinSize d < lm43BallTarget N d →
    LM43FinalSourceBounds N d (lm43MaxSlowSize N d)

/-- The three finite, candidate-local numerical certificates underlying the
conditional source packages.  The guards are essential: when the retained
radius-one set already meets the target, the corresponding Lemma 3.7 call is
unnecessary and its unconditional `D²` lower-size field need not hold. -/
structure LM43RoutedSourceNumericalPackage (N d : ℕ) : Prop where
  claim45 : lm37SourceMinSize d < lm43TargetOrder N d →
    LM37RoutedSourceNumericalBounds N d (lm43DeletionCap N d)
      (lm43R N d) (lm43MinRadius N d) (lm43HighRadius N d)
      (lm43TargetOrder N d)
      (lm43DegreeInto N d) (lm43MaxSlowSize N d) (lm43R N d)
  claim46 : lm37SourceMinSize d < lm43BallTarget N d →
    LM37RoutedSourceNumericalBounds N d (lm43DeletionCap N d)
      (lm43R N d) (lm43MinRadius N d) (lm43BallRadius N d)
      (lm43BallTarget N d)
      (lm43DegreeInto N d) (lm43MaxSlowSize N d) (lm43R N d)
  final : lm37SourceMinSize d < lm43BallTarget N d →
    LM37RoutedSourceNumericalBounds N d (lm43DeletionCap N d)
      (lm43R N d) (lm43MinRadius N d) (lm43BallRadius N d)
      (lm43BallTarget N d)
      (lm43DegreeInto N d) (lm43MaxSlowSize N d) (lm43R N d)

/-- Complete pointwise construction of `LM43NumericalPackage` from Claim
4.4 and the three honest routed source certificates. -/
noncomputable def LM43RoutedSourceNumericalPackage.toNumericalPackage
    {N d : ℕ} (p : LM43RoutedSourceNumericalPackage N d)
    (claim44 : SmallSimpleAdjusterCandidate.LM44Scale N d
      (lm43TargetOrder N d) (lm43TotalRadius N d) (lm43HighCutoff N d)
      (lm43DeletionCap N d) (lm43ProtectedCap N d) (lm43Separation N d)
      (lm43MinRadius N d) (lm43MaxRadius N d) (lm43R N d)
      ((1 / 64) * (lm43CoreDegree N d : ℝ))) :
    LM43NumericalPackage N d where
  claim44 := claim44
  claim45 := fun hsmall ↦
    concreteLM37RoutedSourceBounds N d (lm43DeletionCap N d) (lm43R N d) 2
      (lm43MinRadius N d) (lm43HighRadius N d) (lm43TargetOrder N d)
      (lm43DegreeInto N d) (lm43MaxSlowSize N d) (lm43R N d)
      (p.claim45 hsmall)
  claim46 := fun hsmall ↦
    concreteLM37RoutedSourceBounds N d (lm43DeletionCap N d) (lm43R N d) 2
      (lm43MinRadius N d) (lm43BallRadius N d) (lm43BallTarget N d)
      (lm43DegreeInto N d) (lm43MaxSlowSize N d) (lm43R N d)
      (p.claim46 hsmall)
  final := fun hsmall ↦
    concreteLM37RoutedSourceBounds N d (lm43DeletionCap N d) (lm43R N d) 0
      (lm43MinRadius N d) (lm43BallRadius N d) (lm43BallTarget N d)
      (lm43DegreeInto N d) (lm43MaxSlowSize N d) (lm43R N d)
      (p.final hsmall)

/-- Honest eventual constructor.  Its premises contain exactly the
conditional source admissibility and the independent Claim 4.4 arithmetic;
no false uniform package is inferred. -/
theorem eventually_lm43NumericalPackage_of_routed
    (d : ℕ → ℕ)
    (hsource : ∀ᶠ N : ℕ in atTop,
      Nonempty (LM43RoutedSourceNumericalPackage N (d N)))
    (hclaim44 : ∀ᶠ N : ℕ in atTop,
      Nonempty (SmallSimpleAdjusterCandidate.LM44Scale N (d N)
        (lm43TargetOrder N (d N)) (lm43TotalRadius N (d N))
        (lm43HighCutoff N (d N)) (lm43DeletionCap N (d N))
        (lm43ProtectedCap N (d N)) (lm43Separation N (d N))
        (lm43MinRadius N (d N)) (lm43MaxRadius N (d N)) (lm43R N (d N))
        ((1 / 64) * (lm43CoreDegree N (d N) : ℝ)))) :
    ∀ᶠ N : ℕ in atTop, Nonempty (LM43NumericalPackage N (d N)) := by
  filter_upwards [hsource, hclaim44] with N hsourceN hclaim44N
  obtain ⟨sourceN⟩ := hsourceN
  obtain ⟨claim44N⟩ := hclaim44N
  exact ⟨sourceN.toNumericalPackage claim44N⟩

/-- Uniform threshold form used by the finite Liu--Montgomery theorem.  This
has the required quantifier spine `∃ d₀, ∀ d ≥ d₀, ∀ N ≥ d`; both
premises retain exactly the same spine, so no diagonal uniformity is hidden. -/
theorem exists_lm43NumericalPackage_threshold_of_routed
    (hsource : ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ N : ℕ, d ≤ N →
      Nonempty (LM43RoutedSourceNumericalPackage N d))
    (hclaim44 : ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ N : ℕ, d ≤ N →
      Nonempty (SmallSimpleAdjusterCandidate.LM44Scale N d
        (lm43TargetOrder N d) (lm43TotalRadius N d) (lm43HighCutoff N d)
        (lm43DeletionCap N d) (lm43ProtectedCap N d) (lm43Separation N d)
        (lm43MinRadius N d) (lm43MaxRadius N d) (lm43R N d)
        ((1 / 64) * (lm43CoreDegree N d : ℝ)))) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ N : ℕ, d ≤ N →
      Nonempty (LM43NumericalPackage N d) := by
  obtain ⟨dSource, hSource⟩ := hsource
  obtain ⟨dClaim44, hClaim44⟩ := hclaim44
  refine ⟨max dSource dClaim44, ?_⟩
  intro d hd N hdN
  obtain ⟨source⟩ := hSource d ((le_max_left _ _).trans hd) N hdN
  obtain ⟨claim44⟩ := hClaim44 d ((le_max_right _ _).trans hd) N hdN
  exact ⟨source.toNumericalPackage claim44⟩

/-- Claim 4.5's general correlated scale, obtained without any further
arithmetic from the source-faithful package. -/
noncomputable def LM43NumericalPackage.claim45Scale
    {N d : ℕ} (p : LM43NumericalPackage N d)
    (hsmall : lm37SourceMinSize d < lm43TargetOrder N d) :
    LM37CorrelatedScale N (lm43DeletionCap N d) (lm43R N d) 2
      (lm43HighRadius N d) (lm43TargetOrder N d) (lm43DegreeInto N d)
      (1 / 1024) ((1 / 64) * (d : ℝ)) :=
  (p.claim45 hsmall).toCorrelatedScale

/-- Claim 4.6's general correlated scale. -/
noncomputable def LM43NumericalPackage.claim46Scale
    {N d : ℕ} (p : LM43NumericalPackage N d)
    (hsmall : lm37SourceMinSize d < lm43BallTarget N d) :
    LM37CorrelatedScale N (lm43DeletionCap N d) (lm43R N d) 2
      (lm43BallRadius N d) (lm43BallTarget N d) (lm43DegreeInto N d)
      (1 / 1024) ((1 / 64) * (d : ℝ)) :=
  (p.claim46 hsmall).toCorrelatedScale

/-- The final correlated scale retains the larger two-ended target
`lm43BallTarget`, rather than specializing it back to `lm43TargetOrder`. -/
noncomputable def LM43NumericalPackage.finalScale
    {N d : ℕ} (p : LM43NumericalPackage N d)
    (hsmall : lm37SourceMinSize d < lm43BallTarget N d) :
    LM37CorrelatedScale N (lm43DeletionCap N d) (lm43R N d) 0
      (lm43BallRadius N d) (lm43BallTarget N d) (lm43DegreeInto N d)
      (1 / 1024) ((1 / 64) * (d : ℝ)) :=
  (p.final hsmall).toCorrelatedScale

/-! ## Pointwise bookkeeping -/

@[simp] theorem lm43DeletionCap_eq (N d : ℕ) :
    lm43DeletionCap N d = 6 * lm43TargetOrder N d := by
  simp [lm43DeletionCap, lm43TargetOrder, lm47SimpleBudget]

theorem lm43DeletionCap_le_ten_target (N d : ℕ) :
    lm43DeletionCap N d ≤ 10 * lm43TargetOrder N d := by
  rw [lm43DeletionCap_eq]
  omega

theorem lm43_radii_eq (N d : ℕ) :
    lm43MaxRadius N d = lm43CoreRadius N ∧
    lm43HighRadius N d = lm43AvoidingRadius N ∧
    lm43BallRadius N d = lm43AvoidingRadius N ∧
    lm43FinalConnectorRadius N d = lmGrowthRounds N := by
  simp [lm43MaxRadius, lm43CandidateRadius, lm43HighRadius, lm43BallRadius,
    lm43FinalConnectorRadius]

theorem lm43_high_radius_separated (N d : ℕ) :
    lm43HighRadius N d + lm43HighRadius N d ≤ lm43Separation N d := by
  simp only [lm43HighRadius, lm43Separation]
  omega

theorem lm43_ball_radius_separated (N d : ℕ) :
    lm43BallRadius N d + lm43BallRadius N d ≤ lm43Separation N d := by
  simp only [lm43BallRadius, lm43Separation]
  omega

theorem lm43_ball_radius_le_high_radius (N d : ℕ) :
    lm43BallRadius N d ≤ lm43HighRadius N d := by
  simp [lm43BallRadius, lm43HighRadius]

theorem lm43_final_radius_exact (N d : ℕ) :
    lm43BallRadius N d + 2 * (lm43FinalConnectorRadius N d + 1) =
      lm43TargetRadius N d := by
  rfl

theorem lm43_right_star_budget (N d : ℕ) :
    0 < lm43TargetOrder N d → 0 < lm43MaxRadius N d →
      lm43HighRadius N d ≤ lm43MaxRadius N d →
      lm43TargetOrder N d +
        (lm43DeletionCap N d + 10 * lm43MaxRadius N d +
          (lm43MaxRadius N d + 1) + (lm43HighRadius N d + 1)) ≤
      lm43HighCutoff N d := by
  intro hD hm hell
  rw [lm43HighCutoff, lm43DeletionCap_eq]
  nlinarith

theorem lm43_left_star_budget (N d : ℕ) :
    0 < lm43TargetOrder N d → 0 < lm43MaxRadius N d →
      lm43TargetOrder N d +
        (lm43DeletionCap N d + 10 * lm43MaxRadius N d +
          lm43TargetOrder N d) ≤ lm43HighCutoff N d := by
  intro hD hm
  rw [lm43HighCutoff, lm43DeletionCap_eq]
  nlinarith

@[simp] theorem lm43Claim44SeedCap_eq (N d : ℕ) :
    lm43Claim44SeedCap N d = lm43ProtectedCap N d +
      4 * lm43R N d *
        (2 * lm43MaxRadius N d ^ 2 + 10 * lm43MaxRadius N d) := by
  rfl

@[simp] theorem lm43Claim44BallCap_eq (N d : ℕ) :
    lm43Claim44BallCap N d = lm43Claim44SeedCap N d *
      (lm43HighCutoff N d + 1) ^ lm43Separation N d := by
  rfl

@[simp] theorem lm43Claim44StarBudget_eq (N d : ℕ) :
    lm43Claim44StarBudget N d = lm43DeletionCap N d +
      10 * lm43MaxRadius N d + lm43TargetOrder N d + 1 := by
  rfl

theorem lm43_claim44_seed_bound (N d : ℕ) :
    lm43ProtectedCap N d + 4 * lm43R N d *
        (2 * lm43MaxRadius N d ^ 2 + 10 * lm43MaxRadius N d) ≤
      lm43Claim44SeedCap N d := by
  exact le_rfl

theorem lm43_claim44_ball_bound (N d : ℕ) :
    lm43Claim44SeedCap N d *
        (lm43HighCutoff N d + 1) ^ lm43Separation N d ≤
      lm43Claim44BallCap N d := by
  exact le_rfl

theorem lm43_claim44_star_workspace (N d : ℕ) :
    lm43DeletionCap N d + 10 * lm43MaxRadius N d +
        lm43TargetOrder N d + 1 ≤ lm43Claim44StarBudget N d := by
  exact le_rfl

theorem lm43_claim44_star_degree (N d : ℕ)
    (hD : 0 < lm43TargetOrder N d) (hm : 0 < lm43MaxRadius N d) :
    lm43TargetOrder N d + lm43Claim44StarBudget N d ≤
      lm43HighCutoff N d := by
  rw [lm43Claim44StarBudget_eq, lm43HighCutoff, lm43DeletionCap_eq]
  nlinarith

theorem lm43TargetOrder_le_ballTarget (N d : ℕ)
    (hm : 0 < lm43MaxRadius N d) :
    lm43TargetOrder N d ≤ lm43BallTarget N d := by
  simp only [lm43BallTarget]
  have hmSq : 1 ≤ lm43MaxRadius N d ^ 2 :=
    one_le_pow₀ (by omega)
  nlinarith

theorem lm43TargetOrder_pos_of_two_le {N d : ℕ} (hN : 2 ≤ N) :
    0 < lm43TargetOrder N d := by
  have hradius : 0 < Parameters.lmRadius (1 / 1024) N := by
    rw [Parameters.lmRadius]
    apply Nat.ceil_pos.mpr
    have hlog : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    positivity
  rw [lm43TargetOrder, lm47InflatedOrder]
  exact Nat.mul_pos (Parameters.lmExpansionOrder_pos (by omega))
    hradius

/-- At every source-sized ambient order, one canonical candidate radius is
already bounded by the final endpoint order. -/
theorem lm43MaxRadius_le_targetOrder {N d : ℕ} (hN : 32 ≤ N) :
    lm43MaxRadius N d ≤ lm43TargetOrder N d := by
  have hm : 5 * lmGrowthRounds N ≤
      Parameters.lmRadius (1 / 1024) N :=
    five_mul_lmGrowthRounds_le_lmRadius hN
  have hD : 0 < Parameters.lmExpansionOrder N :=
    Parameters.lmExpansionOrder_pos (by omega)
  calc
    lm43MaxRadius N d = 5 * lmGrowthRounds N := rfl
    _ ≤ Parameters.lmRadius (1 / 1024) N := hm
    _ ≤ Parameters.lmExpansionOrder N *
        Parameters.lmRadius (1 / 1024) N :=
      Nat.le_mul_of_pos_left _ hD
    _ = lm43TargetOrder N d := rfl

theorem lm43FinalConnectorWorkspace_le_sixteen_target
    {N d : ℕ} (hN : 32 ≤ N) :
    lm43FinalConnectorWorkspace N d ≤ 16 * lm43TargetOrder N d := by
  rw [lm43FinalConnectorWorkspace, lm43DeletionCap_eq]
  nlinarith [lm43MaxRadius_le_targetOrder (d := d) hN]

theorem lm43_final_connector_start_large {N d : ℕ} (hN : 32 ≤ N) :
    2 * lmGrowthDivisor N ≤ lm43FinalConnectorStart N d := by
  have hround : 2 * lmGrowthDivisor N ≤ lmGrowthRounds N := by
    rw [lmGrowthRounds]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hroundPos : 0 < lmGrowthRounds N := by
    have hdiv := lmGrowthDivisor_pos (by omega : 2 ≤ N)
    omega
  have hmaxPos : 0 < lm43MaxRadius N d := by
    rw [lm43MaxRadius, lm43CandidateRadius, lm43CoreRadius]
    omega
  calc
    2 * lmGrowthDivisor N ≤ lmGrowthRounds N := hround
    _ ≤ 5 * lmGrowthRounds N := by omega
    _ = lm43MaxRadius N d := rfl
    _ ≤ lm43TargetOrder N d := lm43MaxRadius_le_targetOrder hN
    _ ≤ lm43BallTarget N d := lm43TargetOrder_le_ballTarget N d hmaxPos
    _ ≤ lm43FinalConnectorStart N d := le_max_right _ _

/-- The final connector workspace is strictly smaller than either endpoint
target once the canonical radius is at least two. -/
theorem lm43FinalConnectorWorkspace_lt_ballTarget (N d : ℕ)
    (hD : 0 < lm43TargetOrder N d) (hm : 2 ≤ lm43MaxRadius N d) :
    lm43FinalConnectorWorkspace N d < lm43BallTarget N d := by
  rw [lm43FinalConnectorWorkspace, lm43BallTarget, lm43DeletionCap_eq]
  have hDm : lm43TargetOrder N d ≤
      lm43MaxRadius N d * lm43TargetOrder N d :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hmD : lm43MaxRadius N d ≤
      lm43MaxRadius N d * lm43TargetOrder N d :=
    Nat.le_mul_of_pos_right _ hD
  calc
    6 * lm43TargetOrder N d + 10 * lm43MaxRadius N d ≤
        16 * (lm43MaxRadius N d * lm43TargetOrder N d) := by
      nlinarith
    _ < 10 * lm43MaxRadius N d ^ 2 * lm43TargetOrder N d := by
      have hcoeff : 16 * lm43MaxRadius N d <
          10 * lm43MaxRadius N d ^ 2 := by nlinarith
      simpa [mul_assoc] using Nat.mul_lt_mul_of_pos_right hcoeff hD

/-- Exact source-or-degree alternative used by the bootstrap version of the
final connector theorem. -/
theorem lm43_final_connector_seed_alternative (N d : ℕ)
    (hD : 0 < lm43TargetOrder N d)
    (hm : 2 ≤ lm43MaxRadius N d) :
    lm43FinalConnectorStart N d ≤ lm43BallTarget N d ∨
      lm43FinalConnectorStart N d + lm43FinalConnectorWorkspace N d ≤
        d := by
  by_cases hseed : lm311AdaptiveSeed d ≤ lm43BallTarget N d
  · left
    simp [lm43FinalConnectorStart, hseed]
  · right
    have htargetSeed : lm43BallTarget N d < lm311AdaptiveSeed d :=
      lt_of_not_ge hseed
    have htargetSeed' : lm43BallTarget N d <
        d / 128 + 1 := by
      simpa [lm311AdaptiveSeed] using htargetSeed
    have hworkspace := lm43FinalConnectorWorkspace_lt_ballTarget N d hD hm
    rw [lm43FinalConnectorStart,
      max_eq_left (Nat.le_of_lt htargetSeed)]
    simp only [lm311AdaptiveSeed]
    have hsum : d / 128 + 1 +
        lm43FinalConnectorWorkspace N d ≤
        2 * (d / 128) := by omega
    have hdiv : 2 * (d / 128) ≤ d := by omega
    exact hsum.trans hdiv

/-- The same alternative applies to any endpoint set of at least the
canonical two-ended target size. -/
theorem lm43_final_connector_seed_alternative_of_target_le
    (N d targetCard : ℕ) (hD : 0 < lm43TargetOrder N d)
    (hm : 2 ≤ lm43MaxRadius N d)
    (hcard : lm43BallTarget N d ≤ targetCard) :
    lm43FinalConnectorStart N d ≤ targetCard ∨
      lm43FinalConnectorStart N d + lm43FinalConnectorWorkspace N d ≤
        d := by
  rcases lm43_final_connector_seed_alternative N d hD hm with h | h
  · exact Or.inl (h.trans hcard)
  · exact Or.inr h

theorem lm43_final_connector_seed_alternative_of_card_large
    {N d targetCard : ℕ} (hN : 32 ≤ N)
    (hcard : lm43BallTarget N d ≤ targetCard) :
    lm43FinalConnectorStart N d ≤ targetCard ∨
      lm43FinalConnectorStart N d + lm43FinalConnectorWorkspace N d ≤ d := by
  exact lm43_final_connector_seed_alternative_of_target_le N d targetCard
    (lm43TargetOrder_pos_of_two_le (by omega))
    (by
      have hdiv := lmGrowthDivisor_pos (by omega : 2 ≤ N)
      have hround : 2 * lmGrowthDivisor N ≤ lmGrowthRounds N := by
        rw [lmGrowthRounds]
        exact Nat.le_mul_of_pos_right _ (by omega)
      change 2 ≤ 5 * lmGrowthRounds N
      omega)
    hcard

/-- With both endpoint sources enlarged to `ballTarget`, the first canonical
growth increment pays the literal deleted-set and adjuster-core workspace. -/
theorem lm43FinalConnectorWorkspace_le_growthGain
    {N d : ℕ} (hN : 2 ≤ N) (hD : 0 < lm43TargetOrder N d) :
    lm43FinalConnectorWorkspace N d ≤
      lmGrowthGain N (lm43FinalConnectorStart N d) := by
  let C := lmGrowthDivisor N
  let r := lmGrowthRounds N
  have hCpos : 0 < C := by simpa [C] using lmGrowthDivisor_pos hN
  have hCr : C ≤ r := by
    calc
      C ≤ 2 * C := by omega
      _ ≤ 2 * C * (Nat.log 2 N + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
      _ = r := by simp [C, r, lmGrowthRounds]
  have hrpos : 0 < r := hCpos.trans_le hCr
  have hrSq : r ≤ r ^ 2 := by nlinarith
  have hproduct : C * lm43FinalConnectorWorkspace N d ≤
      lm43BallTarget N d := by
    calc
      C * lm43FinalConnectorWorkspace N d ≤
          r * lm43FinalConnectorWorkspace N d :=
        Nat.mul_le_mul_right _ hCr
      _ = 6 * r * lm43TargetOrder N d + 50 * r ^ 2 := by
        simp [lm43FinalConnectorWorkspace, lm43DeletionCap_eq,
          lm43MaxRadius, lm43CandidateRadius, lm43CoreRadius, r]
        ring
      _ ≤ 6 * r ^ 2 * lm43TargetOrder N d +
          50 * r ^ 2 * lm43TargetOrder N d := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 6 hrSq))
          (Nat.le_mul_of_pos_right _ hD)
      _ = 56 * r ^ 2 * lm43TargetOrder N d := by ring
      _ ≤ 250 * r ^ 2 * lm43TargetOrder N d :=
        Nat.mul_le_mul_right _
          (Nat.mul_le_mul_right _ (by norm_num))
      _ = lm43BallTarget N d := by
        change 250 * r ^ 2 * lm43TargetOrder N d =
          10 * (5 * r) ^ 2 * lm43TargetOrder N d
        ring
  rw [lmGrowthGain]
  apply (Nat.le_div_iff_mul_le hCpos).2
  calc
    lm43FinalConnectorWorkspace N d * C =
        C * lm43FinalConnectorWorkspace N d := Nat.mul_comm _ _
    _ ≤ lm43BallTarget N d := hproduct
    _ ≤ lm43FinalConnectorStart N d := le_max_right _ _

/-- Concrete final connector schedule with every parameter fixed canonically. -/
noncomputable def concreteLM43FinalConnectorSchedule
    {N d : ℕ} (hN : 32 ≤ N) (hd : 1 ≤ d)
    (hD : 0 < lm43TargetOrder N d) :
    LM42GrowthSchedule N (lm43FinalConnectorStart N d)
      (lm43FinalConnectorWorkspace N d) (lm43FinalConnectorRadius N d)
      (1 / 1024) ((1 / 64) * (d : ℝ)) := by
  rw [lm43FinalConnectorRadius]
  apply concreteLM42GrowthSchedule N d
  · exact hN
  · exact hd
  · exact (lm311AdaptiveSeed_cutoff d).trans (by
      exact_mod_cast (le_max_left
        (lm311AdaptiveSeed d) (lm43BallTarget N d)))
  · exact lm43_final_connector_start_large hN
  · exact lm43FinalConnectorWorkspace_le_growthGain
      (hN.trans' (by omega)) hD

/-- The canonical final connector schedule is eventually available uniformly
for every positive original degree parameter. -/
theorem eventually_concreteLM43FinalConnectorSchedule :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ, 1 ≤ d →
      Nonempty (LM42GrowthSchedule N (lm43FinalConnectorStart N d)
        (lm43FinalConnectorWorkspace N d) (lm43FinalConnectorRadius N d)
        (1 / 1024) ((1 / 64) * (d : ℝ))) := by
  filter_upwards [eventually_ge_atTop (32 : ℕ)] with N hN
  intro d hd
  have hD : 0 < lm43TargetOrder N d :=
    lm43TargetOrder_pos_of_two_le (by omega)
  exact ⟨concreteLM43FinalConnectorSchedule hN hd hD⟩

/-- Graph-facing numerical data for the corrected final connector.  Both
endpoint expansions have the canonical two-ended order `lm43BallTarget`.
The same multiplicative schedule therefore grows either endpoint to more
than half the ambient graph.  If its comparison curve starts above that
endpoint order, the radius-one minimum-degree bootstrap pays both the start
and the fixed forbidden workspace.

This is the adaptive replacement for the incompatible pair consisting of a
fixed connector increment and a linear `radius * increment` reach bound. -/
structure LM43AdaptiveFinalConnectorCertificate (N d : ℕ) : Type where
  schedule : LM42GrowthSchedule N (lm43FinalConnectorStart N d)
    (lm43FinalConnectorWorkspace N d) (lm43FinalConnectorRadius N d)
    (1 / 1024) ((1 / 64) * (d : ℝ))
  ball_seed : lm43FinalConnectorStart N d ≤ lm43BallTarget N d ∨
    lm43FinalConnectorStart N d + lm43FinalConnectorWorkspace N d ≤ d
  target_seed : lm43FinalConnectorStart N d ≤ lm43BallTarget N d ∨
    lm43FinalConnectorStart N d + lm43FinalConnectorWorkspace N d ≤ d
  radius_exact : lm43BallRadius N d +
      2 * (lm43FinalConnectorRadius N d + 1) = lm43TargetRadius N d

/-- Pointwise adaptive connector certificate at every source-sized ambient
order. -/
noncomputable def concreteLM43AdaptiveFinalConnectorCertificate
    {N d : ℕ} (hN : 32 ≤ N) (hd : 1 ≤ d) :
    LM43AdaptiveFinalConnectorCertificate N d := by
  have hD : 0 < lm43TargetOrder N d :=
    lm43TargetOrder_pos_of_two_le (by omega)
  have hseed : lm43FinalConnectorStart N d ≤ lm43BallTarget N d ∨
      lm43FinalConnectorStart N d + lm43FinalConnectorWorkspace N d ≤ d :=
    lm43_final_connector_seed_alternative_of_card_large hN le_rfl
  exact
    { schedule := concreteLM43FinalConnectorSchedule hN hd hD
      ball_seed := hseed
      target_seed := hseed
      radius_exact := lm43_final_radius_exact N d }

/-- One absolute lower threshold supplies the adaptive final connector
uniformly for every `d ≤ N`. -/
theorem exists_lm43AdaptiveFinalConnectorCertificate_threshold :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ N : ℕ, d ≤ N →
      Nonempty (LM43AdaptiveFinalConnectorCertificate N d) := by
  refine ⟨32, ?_⟩
  intro d hd N hdN
  exact ⟨concreteLM43AdaptiveFinalConnectorCertificate
    (hd.trans hdN) (by omega)⟩

theorem lm43MinRadius_pos {N d : ℕ} (hd : 64 ≤ d) :
    0 < lm43MinRadius N d := by
  have hcore : 1 ≤ lm43CoreDegree N d := by
    simp only [lm43CoreDegree]
    omega
  have hn : 2 ≤ lm43CoreDegree N d + 1 := by omega
  have hdiv := lmGrowthDivisor_pos hn
  simp only [lm43MinRadius, lm43MinRadiusFrom, lm43CoreRadius,
    lmGrowthRounds]
  positivity

theorem lm43CoreDegree_ge_32 {N d : ℕ} (hd : 2048 ≤ d) :
    32 ≤ lm43CoreDegree N d := by
  simp only [lm43CoreDegree]
  omega

/-! ## Claim 4.6 growth facts which are genuinely eventual -/

/-- A fixed logarithmic power is eventually below the eighth root, with an
arbitrary fixed positive coefficient. -/
theorem eventually_const_mul_log_pow_le_rpow_eighth
    (C : ℝ) (hC : 0 < C) (k : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      C * Real.log (N : ℝ) ^ k ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by
  have hbound :=
    (isLittleO_log_rpow_rpow_atTop (k : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 8)).bound (inv_pos.mpr hC)
  have hcast : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually hbound, eventually_ge_atTop (1 : ℕ)]
    with N hN hNone
  have hNreal : (0 : ℝ) ≤ (N : ℝ) := by positivity
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hNone)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hlog (k : ℝ)),
    Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hNreal ((1 : ℝ) / 8))] at hN
  have hdiv : Real.log (N : ℝ) ^ (k : ℝ) ≤
      (N : ℝ) ^ ((1 : ℝ) / 8) / C := by
    simpa [div_eq_mul_inv, mul_comm] using hN
  have hmul := (le_div_iff₀ hC).mp hdiv
  simpa [Real.rpow_natCast, mul_comm] using hmul

/-- The sharp Claim 4.6 denominator is eventually smaller than the
quarter-order seed. -/
theorem eventually_lm43_denominator_fits :
    ∀ᶠ N : ℕ in atTop,
      6 * lm43GrowthDenominator N ≤ lm43K N := by
  have hlog := Parameters.eventually_const_mul_log_pow_le_self (24 * 9217) 2
  have hlogNat := tendsto_natCast_atTop_atTop.eventually hlog
  filter_upwards [hlogNat, eventually_ge_atTop (4 : ℕ)] with N hlogN hN
  have hlogNonneg : 0 ≤ Real.log (N : ℝ) ^ 2 := sq_nonneg _
  have hceil : (lm43GrowthDenominator N : ℝ) ≤
      9217 * Real.log (N : ℝ) ^ 2 := by
    rw [lm43GrowthDenominator]
    apply le_of_lt
    calc
      (⌈9216 * Real.log (N : ℝ) ^ 2⌉₊ : ℝ) <
          9216 * Real.log (N : ℝ) ^ 2 + 1 :=
        Nat.ceil_lt_add_one (mul_nonneg (by norm_num) hlogNonneg)
      _ ≤ 9217 * Real.log (N : ℝ) ^ 2 := by
        have hlogOne : 1 ≤ Real.log (N : ℝ) ^ 2 := by
          have : Real.exp 1 ≤ (N : ℝ) := by
            have hexp : Real.exp 1 < 3 :=
              Real.exp_one_lt_d9.trans (by norm_num)
            exact hexp.le.trans (by exact_mod_cast (show 3 ≤ N by omega))
          have := (Real.le_log_iff_exp_le (by positivity)).2 this
          simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) this 2
        linarith
  have hreal : (24 : ℝ) * lm43GrowthDenominator N ≤ N := by
    calc
      (24 : ℝ) * lm43GrowthDenominator N ≤
          (24 : ℝ) * (9217 * Real.log (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hceil (by norm_num)
      _ = (24 * 9217 : ℝ) * Real.log (N : ℝ) ^ 2 := by ring
      _ ≤ N := hlogN
  have hnat : 24 * lm43GrowthDenominator N ≤ N := by exact_mod_cast hreal
  dsimp [lm43K]
  omega

/-- The common candidate radius is eventually positive (in fact it is
positive already in the range supplied by the standard growth package). -/
theorem eventually_lm43_candidateRadius_pos :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ, 0 < lm43CandidateRadius N d := by
  filter_upwards [eventually_lmConcreteGrowthBounds] with N hN
  intro d
  have hn : 2 ≤ N := (hN 1 (by omega)).card_large.trans' (by omega)
  have hdiv : 0 < lmGrowthDivisor N :=
    lmGrowthDivisor_pos hn
  simp only [lm43CandidateRadius, lm43CoreRadius, lmGrowthRounds]
  positivity

/-- The inflated Lemma 4.7 end order is eventually at most the quarter-order
seed used by the sharp Claim 4.6 growth theorem. -/
theorem eventually_lm43_targetOrder_le_K :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ, lm43TargetOrder N d ≤ lm43K N := by
  have htarget :=
    Parameters.eventually_lmExpansionOrder_mul_lmRadius_1024_le_ceil_log14
  have hlogReal :=
    Parameters.eventually_const_mul_log_pow_le_self (8 : ℝ) 14
  have hlogNat := tendsto_natCast_atTop_atTop.eventually hlogReal
  have hlogTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne := hlogTop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [htarget, hlogNat, hlogOne] with N htargetN hlogN hlogOneN
  intro d
  let x := Real.log (N : ℝ) ^ 14
  have hx : 1 ≤ x := by
    exact one_le_pow₀ hlogOneN
  have hceilReal : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
    apply le_of_lt
    calc
      (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one (by positivity)
      _ ≤ 2 * x := by linarith
  have hceilNat : 4 * ⌈x⌉₊ ≤ N := by
    have hreal : ((4 * ⌈x⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by
      push_cast
      calc
        (4 : ℝ) * (⌈x⌉₊ : ℝ) ≤ 8 * x := by nlinarith
        _ ≤ (N : ℝ) := by simpa only [x] using hlogN
    exact_mod_cast hreal
  have htargetNat : lm43TargetOrder N d ≤ ⌈x⌉₊ := by
    simpa only [lm43TargetOrder, lm47InflatedOrder, x] using htargetN
  have hfour : 4 * lm43TargetOrder N d ≤ N :=
    (Nat.mul_le_mul_left 4 htargetNat).trans hceilNat
  rw [lm43K]
  exact (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2 (by
    simpa [mul_comm] using hfour)

theorem eventually_lm43_targetOrder_pos :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ, 0 < lm43TargetOrder N d := by
  filter_upwards [eventually_lm47ScaleBounds] with N hN
  intro d
  have hpos := hN.endpoint_pos
  have hle := hN.shrink_le
  simp only [lm43TargetOrder]
  omega

theorem eventually_lm43_R_pos :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ, 0 < lm43R N d := by
  filter_upwards [SourceLemma35Numerics.eventually_source_ambient_bounds]
    with N hN
  intro d
  have hfloor : (N : ℝ) ^ ((1 : ℝ) / 8) / 2 ≤
      (SourceLemma35Numerics.indexCard N : ℝ) := by
    simpa [SourceLemma35Numerics.indexCard] using
      Parameters.half_le_natFloor hN.2.1
  have hcast : (1 : ℝ) ≤ (SourceLemma35Numerics.indexCard N : ℝ) :=
    (by linarith : (1 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) / 2) |>.trans
      hfloor
  have : 0 < SourceLemma35Numerics.indexCard N := by exact_mod_cast hcast
  simpa [lm43R, lm43FamilyTarget] using this

theorem eventually_lm43_avoidingRadius_pos :
    ∀ᶠ N : ℕ in atTop, 0 < lm43AvoidingRadius N := by
  have hloglog : Tendsto
      (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hloglog.eventually (eventually_gt_atTop (0 : ℝ))]
    with N hN
  rw [lm43AvoidingRadius]
  exact Nat.ceil_pos.mpr (pow_pos hN 20)

/-- The source candidate clock is monotone once its order is nonzero. -/
theorem lmGrowthRounds_mono_of_one_le {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    lmGrowthRounds a ≤ lmGrowthRounds b := by
  have hcast : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have haReal : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hlogNonneg : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg haReal
  have hlog : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
    Real.log_le_log (by positivity) hcast
  have hsq : Real.log (a : ℝ) ^ 2 ≤ Real.log (b : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlogNonneg hlog 2
  have hden : lmGrowthDenominator a ≤ lmGrowthDenominator b := by
    rw [lmGrowthDenominator, lmGrowthDenominator]
    exact Nat.ceil_mono (mul_le_mul_of_nonneg_left hsq (by norm_num))
  have hlogNat : Nat.log 2 a ≤ Nat.log 2 b := Nat.log_mono_right hab
  simp only [lmGrowthRounds, lmGrowthDivisor]
  gcongr

/-- The literal variable radius `5 * lmGrowthRounds n'` lies in the
canonical Claim 4.4 interval for every extracted order `n'`. -/
theorem lm43_core_radius_bounds {N d n' : ℕ}
    (hcore : lm43CoreDegree N d < n') (hn' : n' ≤ N) :
    lm43MinRadius N d ≤ lm43CoreRadius n' ∧
      lm43CoreRadius n' ≤ lm43MaxRadius N d := by
  have hone : 1 ≤ lm43CoreDegree N d + 1 := by omega
  have hlower : lm43CoreDegree N d + 1 ≤ n' := by omega
  have hn'one : 1 ≤ n' := hone.trans hlower
  constructor
  · simpa [lm43MinRadius, lm43MinRadiusFrom, lm43CoreRadius] using
      Nat.mul_le_mul_left 5 (lmGrowthRounds_mono_of_one_le hone hlower)
  · simpa [lm43MaxRadius, lm43CandidateRadius, lm43CoreRadius] using
      Nat.mul_le_mul_left 5 (lmGrowthRounds_mono_of_one_le hn'one hn')

/-- The iterated-logarithm avoiding clock is eventually no larger than one
ambient growth denominator.  Keeping this sharper intermediate estimate
leaves room for both endpoint-bootstrap steps of the final connector. -/
theorem eventually_lm43_avoidingRadius_le_growthDenominator :
    ∀ᶠ N : ℕ in atTop,
      lm43AvoidingRadius N ≤ lmGrowthDenominator N := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto
      (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlog
  filter_upwards
      [Parameters.eventually_const_mul_log_log_pow_le_log 2 20,
        hlog.eventually (eventually_ge_atTop (1 : ℝ)),
        hloglog.eventually (eventually_ge_atTop (1 : ℝ)),
        eventually_ge_atTop (2 : ℕ)]
      with N hsmall hlogOne hloglogOne hN
  let L := Real.log (N : ℝ)
  let ll := Real.log L
  have hllPow : 1 ≤ ll ^ 20 := one_le_pow₀ hloglogOne
  have hell : (lm43AvoidingRadius N : ℝ) ≤ 2 * ll ^ 20 := by
    apply le_of_lt
    calc
      (lm43AvoidingRadius N : ℝ) < ll ^ 20 + 1 := by
        simpa [lm43AvoidingRadius, ll, L] using
          Nat.ceil_lt_add_one (pow_nonneg (zero_le_one.trans hloglogOne) 20)
      _ ≤ 2 * ll ^ 20 := by linarith
  have hdenLower : L ≤ (lmGrowthDenominator N : ℝ) := by
    calc
      L ≤ 9216 * L ^ 2 := by nlinarith [sq_nonneg L]
      _ ≤ (lmGrowthDenominator N : ℝ) := by
        simpa [L] using lmGrowthDenominator_lower N
  have hsmall' : 2 * ll ^ 20 ≤ L := by
    simpa [ll, L] using hsmall
  have hellDen : (lm43AvoidingRadius N : ℝ) ≤
      (lmGrowthDenominator N : ℝ) :=
    hell.trans (hsmall'.trans hdenLower)
  exact_mod_cast hellDen

/-- The avoiding clock fits inside the multiplicative connector clock. -/
theorem eventually_lm43_avoidingRadius_le_growthRounds :
    ∀ᶠ N : ℕ in atTop, lm43AvoidingRadius N ≤ lmGrowthRounds N := by
  filter_upwards [eventually_lm43_avoidingRadius_le_growthDenominator,
      eventually_ge_atTop (2 : ℕ)] with N hell hN
  exact hell.trans (by
    have hdenPos := lmGrowthDenominator_pos hN
    simp only [lmGrowthRounds, lmGrowthDivisor]
    nlinarith)

/-- Two bootstrap edges also fit in the multiplicative connector clock. -/
theorem eventually_lm43_avoidingRadius_add_two_le_growthRounds :
    ∀ᶠ N : ℕ in atTop,
      lm43AvoidingRadius N + 2 ≤ lmGrowthRounds N := by
  filter_upwards [eventually_lm43_avoidingRadius_le_growthDenominator,
      eventually_ge_atTop (2 : ℕ)] with N hell hN
  have hdenPos := lmGrowthDenominator_pos hN
  have hfour : 4 * lmGrowthDenominator N ≤ lmGrowthRounds N := by
    calc
      4 * lmGrowthDenominator N =
          2 * (2 * lmGrowthDenominator N) := by ring
      _ ≤ 2 * (2 * lmGrowthDenominator N) * (Nat.log 2 N + 1) :=
        Nat.le_mul_of_pos_right _ (by omega)
      _ = lmGrowthRounds N := by
        simp [lmGrowthRounds, lmGrowthDivisor]
  exact (by omega : lm43AvoidingRadius N + 2 ≤
    4 * lmGrowthDenominator N) |>.trans hfour

/-- Slightly sharper than the generic factor-two logarithm bound; the
constant is useful because the robust radius has little spare room. -/
theorem natLog_two_le_three_halves_log {N : ℕ} (hN : 1 ≤ N) :
    (Nat.log 2 N : ℝ) ≤ (3 / 2 : ℝ) * Real.log (N : ℝ) := by
  let k := Nat.log 2 N
  have hN0 : N ≠ 0 := by omega
  have hpowNat : 2 ^ k ≤ N := Nat.pow_log_le_self 2 hN0
  have hpowReal : (((2 ^ k : ℕ) : ℝ)) ≤ (N : ℝ) := by
    exact_mod_cast hpowNat
  have hlogPow : (k : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
    have h := Real.log_le_log
      (by positivity : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ)) hpowReal
    simpa [Real.log_pow] using h
  have hlogTwo : (2 / 3 : ℝ) ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  dsimp [k] at hlogPow ⊢
  nlinarith

/-- Five canonical growth clocks fit in one simple-adjuster radius.  This is
the sharp coefficient needed because `lm43TotalRadius = 2 * (5 * rounds)`. -/
theorem eventually_five_mul_lmGrowthRounds_le_lmSimpleRadius :
    ∀ᶠ N : ℕ in atTop,
      5 * lmGrowthRounds N ≤ Parameters.lmSimpleRadius (1 / 1024) N := by
  have hlogTop : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := hlogTop.eventually (eventually_ge_atTop (100 : ℝ))
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with N hL hN
  let L := Real.log (N : ℝ)
  let C := lmGrowthDenominator N
  let k := Nat.log 2 N + 1
  have hL0 : 0 ≤ L := by dsimp [L]; exact Real.log_nonneg (by exact_mod_cast hN)
  have hLsq : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg L]
  have hC : (C : ℝ) ≤ 9217 * L ^ 2 := by
    dsimp [C, lmGrowthDenominator]
    apply le_of_lt
    calc
      (⌈9216 * Real.log (N : ℝ) ^ 2⌉₊ : ℝ) <
          9216 * Real.log (N : ℝ) ^ 2 + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      _ ≤ 9217 * L ^ 2 := by dsimp [L]; nlinarith
  have hk : (k : ℝ) ≤ (151 / 100 : ℝ) * L := by
    have hnatlog := natLog_two_le_three_halves_log hN
    dsimp [k]
    push_cast
    dsimp [L] at hL ⊢
    nlinarith
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hreal : ((5 * lmGrowthRounds N : ℕ) : ℝ) ≤
      (Parameters.lmSimpleRadius (1 / 1024) N : ℝ) := by
    calc
      ((5 * lmGrowthRounds N : ℕ) : ℝ) = 20 * (C : ℝ) * (k : ℝ) := by
        simp only [lmGrowthRounds, lmGrowthDivisor, C, k, Nat.cast_mul,
          Nat.cast_ofNat]
        ring
      _ ≤ 20 * (9217 * L ^ 2) * ((151 / 100 : ℝ) * L) := by
        gcongr
      _ ≤ (400 / (1 / 1024 : ℝ)) * L ^ 3 := by
        nlinarith [pow_nonneg hL0 3]
      _ ≤ (Parameters.lmSimpleRadius (1 / 1024) N : ℝ) := by
        simpa [L] using Parameters.lmSimpleRadius_lower (1 / 1024 : ℝ) N
  exact_mod_cast hreal

/-- Backward-compatible weaker form used by the Claim 4.4 carrier estimate. -/
theorem eventually_three_mul_lmGrowthRounds_le_lmSimpleRadius :
    ∀ᶠ N : ℕ in atTop,
      3 * lmGrowthRounds N ≤ Parameters.lmSimpleRadius (1 / 1024) N := by
  filter_upwards [eventually_five_mul_lmGrowthRounds_le_lmSimpleRadius]
    with N hfive
  exact (Nat.mul_le_mul_right (lmGrowthRounds N) (by omega : 3 ≤ 5)).trans
    hfive

@[simp] theorem lm43TotalRadius_eq_ten_mul_lmGrowthRounds (N d : ℕ) :
    lm43TotalRadius N d = 10 * lmGrowthRounds N := by
  simp [lm43TotalRadius, lm43MaxRadius, lm43CandidateRadius,
    lm43CoreRadius]
  ring

theorem lm43TotalRadius_le_two_mul_lmSimpleRadius_of_five_rounds
    {N d : ℕ}
    (hfive : 5 * lmGrowthRounds N ≤
      Parameters.lmSimpleRadius (1 / 1024) N) :
    lm43TotalRadius N d ≤
      2 * Parameters.lmSimpleRadius (1 / 1024) N := by
  rw [lm43TotalRadius_eq_ten_mul_lmGrowthRounds]
  nlinarith

/-- The canonical output radius is eventually at most the radius allowance
in the robust simple-adjuster supply. -/
theorem eventually_lm43_totalRadius_le_two_mul_lmSimpleRadius :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      lm43TotalRadius N d ≤
        2 * Parameters.lmSimpleRadius (1 / 1024) N := by
  filter_upwards [eventually_five_mul_lmGrowthRounds_le_lmSimpleRadius]
    with N hfive
  intro d
  exact lm43TotalRadius_le_two_mul_lmSimpleRadius_of_five_rounds hfive

/-- The complete per-candidate carrier coefficient in Claim 4.4 is
eventually at most the source family parameter `R = floor(N^(1/8))`. -/
theorem eventually_lm43_claim44_carrier_coefficient_le_R :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      4 * (2 * lm43MaxRadius N d ^ 2 + 10 * lm43MaxRadius N d) ≤
        lm43R N d := by
  let C : ℝ := 112 * 409601 ^ 2
  have hroot := eventually_const_mul_log_pow_le_rpow_eighth
    (2 * C) (by dsimp [C]; positivity) 6
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_three_mul_lmGrowthRounds_le_lmSimpleRadius,
      eventually_lm43_candidateRadius_pos,
      SourceLemma35Numerics.eventually_source_ambient_bounds, hroot,
      hlog.eventually (eventually_ge_atTop (1 : ℝ))]
    with N hthree hr hambient hrootN hL
  intro d
  let r := lmGrowthRounds N
  let s := Parameters.lmSimpleRadius (1 / 1024) N
  let m := lm43MaxRadius N d
  have hrpos : 0 < r := by
    simpa [lm43CandidateRadius, lm43CoreRadius, lm43MaxRadius, r] using hr d
  have hspos : 0 < s := by
    have : 3 * r ≤ s := by simpa [r, s] using hthree
    omega
  have hmle : m ≤ 2 * s := by
    have hthree' : 3 * r ≤ s := by simpa [r, s] using hthree
    dsimp [m, lm43MaxRadius, lm43CandidateRadius, lm43CoreRadius]
    omega
  have hmSq : m ^ 2 ≤ (2 * s) ^ 2 := Nat.pow_le_pow_left hmle 2
  have hsLin : s ≤ s ^ 2 := by nlinarith
  have hcoeffNat : 4 * (2 * m ^ 2 + 10 * m) ≤ 112 * s ^ 2 := by
    nlinarith
  let L := Real.log (N : ℝ)
  have hL3 : 1 ≤ L ^ 3 := one_le_pow₀ hL
  have hsUpper : (s : ℝ) ≤ 409601 * L ^ 3 := by
    apply le_of_lt
    calc
      (s : ℝ) < (400 / (1 / 1024 : ℝ)) * L ^ 3 + 1 := by
        simpa [s, L] using
          (Parameters.lmSimpleRadius_lt_add_one
            (n := N) (by norm_num : (0 : ℝ) < 1 / 1024))
      _ ≤ 409601 * L ^ 3 := by norm_num; linarith
  have hsSq : (s : ℝ) ^ 2 ≤ 409601 ^ 2 * L ^ 6 := by
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg s) hsUpper 2
    calc
      (s : ℝ) ^ 2 ≤ (409601 * L ^ 3) ^ 2 := hp
      _ = 409601 ^ 2 * L ^ 6 := by ring
  have hcoeffReal :
      (4 * (2 * m ^ 2 + 10 * m) : ℕ) ≤ C * L ^ 6 := by
    have hcast : ((4 * (2 * m ^ 2 + 10 * m) : ℕ) : ℝ) ≤
        112 * (s : ℝ) ^ 2 := by exact_mod_cast hcoeffNat
    calc
      ((4 * (2 * m ^ 2 + 10 * m) : ℕ) : ℝ) ≤
          112 * (s : ℝ) ^ 2 := hcast
      _ ≤ 112 * (409601 ^ 2 * L ^ 6) :=
        mul_le_mul_of_nonneg_left hsSq (by norm_num)
      _ = C * L ^ 6 := by dsimp [C]; ring
  have hhalf : C * L ^ 6 ≤ (N : ℝ) ^ ((1 : ℝ) / 8) / 2 := by
    have : 2 * C * L ^ 6 ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := by
      simpa [L, mul_assoc] using hrootN
    linarith
  have hfloor : (N : ℝ) ^ ((1 : ℝ) / 8) / 2 ≤
      (SourceLemma35Numerics.indexCard N : ℝ) := by
    simpa [SourceLemma35Numerics.indexCard] using
      Parameters.half_le_natFloor hambient.2.1
  have hfinal : ((4 * (2 * m ^ 2 + 10 * m) : ℕ) : ℝ) ≤
      (SourceLemma35Numerics.indexCard N : ℝ) :=
    hcoeffReal.trans (hhalf.trans hfloor)
  simpa [m, lm43R, lm43FamilyTarget] using
    (by exact_mod_cast hfinal :
      4 * (2 * m ^ 2 + 10 * m) ≤ SourceLemma35Numerics.indexCard N)

/-- All radius-only premises of Claims 4.5 and 4.6 are eventually automatic
for the canonical choice. -/
theorem eventually_lm43_radius_budgets :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      lm43MaxRadius N d + lm43HighRadius N d + 1 ≤
          lm43TotalRadius N d ∧
      lm43MaxRadius N d + lm43TargetRadius N d +
          2 * lm43FarRadius N ≤ lm43TotalRadius N d ∧
      lm43MaxRadius N d + lm43BallRadius N d ≤
          lm43TotalRadius N d := by
  filter_upwards [eventually_lm43_avoidingRadius_add_two_le_growthRounds,
    eventually_lm43_candidateRadius_pos] with N hell hr
  intro d
  let r := lmGrowthRounds N
  have hfar : lm43FarRadius N ≤ r := by
    have hden : lm43GrowthDenominator N = lmGrowthDenominator N := rfl
    have hlog : Nat.log 2 (lm43K N) ≤ Nat.log 2 N :=
      Nat.log_mono_right (Nat.div_le_self N 4)
    calc
      lm43FarRadius N =
          (3 * lmGrowthDenominator N) * (Nat.log 2 (lm43K N) + 1) := by
        simp [lm43FarRadius, lm43FreshRadius, lm43HalvingRounds, hden]
      _ ≤ (3 * lmGrowthDenominator N) * (Nat.log 2 N + 1) := by
        gcongr
      _ ≤ (4 * lmGrowthDenominator N) * (Nat.log 2 N + 1) := by
        gcongr <;> norm_num
      _ = r := by simp [r, lmGrowthRounds, lmGrowthDivisor]; ring
  have hrpos : 0 < r := by
    simpa [lm43CandidateRadius, lm43CoreRadius, r] using hr d
  have hell' : lm43AvoidingRadius N + 2 ≤ r := by simpa [r] using hell
  simp only [lm43MaxRadius, lm43HighRadius, lm43BallRadius,
    lm43CandidateRadius, lm43CoreRadius, lm43TargetRadius,
    lm43FinalConnectorRadius, lm43TotalRadius]
  constructor
  · omega
  constructor <;> omega

/-- Exact Claim 4.3 bootstrap radius and its eventual absorption by the
output radius. -/
theorem eventually_lm43_final_connector_radius_room :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      lm43BallRadius N d +
          2 * (lm43FinalConnectorRadius N d + 1) =
        lm43TargetRadius N d ∧
      lm43TargetRadius N d ≤ lm43TotalRadius N d := by
  filter_upwards [eventually_lm43_avoidingRadius_add_two_le_growthRounds]
    with N hroom
  intro d
  constructor
  · exact lm43_final_radius_exact N d
  · simp only [lm43TargetRadius, lm43BallRadius,
      lm43FinalConnectorRadius, lm43TotalRadius, lm43MaxRadius,
      lm43CandidateRadius, lm43CoreRadius]
    omega

/-! ## Eventual Claim 4.4 and star bookkeeping -/

/-- The two Claim 4.5 star-replacement budgets fit the literal source
cutoff `200 * maxRadius * targetOrder`. -/
theorem eventually_lm43_star_budgets :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      lm43TargetOrder N d +
          (lm43DeletionCap N d + 10 * lm43MaxRadius N d +
            (lm43MaxRadius N d + 1) + (lm43HighRadius N d + 1)) ≤
        lm43HighCutoff N d ∧
      lm43TargetOrder N d +
          (lm43DeletionCap N d + 10 * lm43MaxRadius N d +
            lm43TargetOrder N d) ≤ lm43HighCutoff N d := by
  filter_upwards [eventually_lm43_targetOrder_pos,
      eventually_lm43_candidateRadius_pos,
      eventually_lm43_avoidingRadius_le_growthRounds]
    with N hD hm hell
  intro d
  have hmax : 0 < lm43MaxRadius N d := by
    simpa [lm43MaxRadius] using hm d
  have hhigh : lm43HighRadius N d ≤ lm43MaxRadius N d := by
    simpa [lm43HighRadius, lm43MaxRadius, lm43CandidateRadius,
      lm43CoreRadius] using hell.trans (Nat.le_mul_of_pos_left _ (by omega))
  exact ⟨lm43_right_star_budget N d (hD d) hmax hhigh,
    lm43_left_star_budget N d (hD d) hmax⟩

theorem eventually_lm43_claim44_star_degree :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      lm43TargetOrder N d + lm43Claim44StarBudget N d ≤
        lm43HighCutoff N d := by
  filter_upwards [eventually_lm43_targetOrder_pos,
      eventually_lm43_candidateRadius_pos] with N hD hm
  intro d
  exact lm43_claim44_star_degree N d (hD d) (by
    simpa [lm43MaxRadius] using hm d)

/-- The easy total-radius fields of `LM44Scale` are eventually automatic. -/
theorem eventually_lm43_total_radius_fields :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      1 ≤ lm43TotalRadius N d ∧
        lm43MaxRadius N d ≤ lm43TotalRadius N d := by
  filter_upwards [eventually_lm43_candidateRadius_pos] with N hN
  intro d
  have hm : 0 < lm43MaxRadius N d := by
    simpa [lm43MaxRadius] using hN d
  simp only [lm43TotalRadius]
  omega

/-! ## The source large-sample admissibility dichotomy -/

/-- Arithmetic condition forced by the lower-size field of the literal
`D²` large sample in `LM37SourceBounds`.  Naming it prevents an accidental
claim that the source package exists uniformly for every `d ≤ N`: for fixed
`D`, the replicated union only has order `D² * cutoff`. -/
def lm43SourceLargeAdmissible (N d : ℕ) : Prop :=
  d ≤ 128 * (lm43MaxSlowSize N d ^ 2 * lm37SourceCutoff N)

/-- If a target is bounded by `D` and the fixed radius-one loss is at most
`D² * cutoff`, then either the retained radius-one neighborhood already has
the requested target size or the literal source large sample reaches the
expander cutoff.

This is the exact complementary branch needed around `LM37SourceBounds`.
It is purely natural-number arithmetic and makes no asymptotic assumption. -/
theorem source_target_or_large_admissible
    {d D cutoff target cost : ℕ}
    (hD : 0 < D) (hcutoff : 0 < cutoff) (htarget : target ≤ D)
    (hcost : cost ≤ D ^ 2 * cutoff) :
    target ≤ d - d / 2 - cost ∨ d ≤ 128 * (D ^ 2 * cutoff) := by
  by_cases hadmissible : d ≤ 128 * (D ^ 2 * cutoff)
  · exact Or.inr hadmissible
  · left
    have hDsq : D ≤ D ^ 2 := by nlinarith
    have hDtoX : D ≤ D ^ 2 * cutoff :=
      hDsq.trans (Nat.le_mul_of_pos_right _ hcutoff)
    have hsum : target + cost ≤ 2 * (D ^ 2 * cutoff) := by omega
    have hdegree : 2 * (target + cost) ≤ d := by omega
    omega

/-- The two literal loss terms used after the radius-one bootstrap. -/
noncomputable def lm43ReachRetainedCost (N d : ℕ) : ℕ :=
  (11 * lm43MaxRadius N d + 1) + 2

noncomputable def lm43FinalRetainedCost (N d : ℕ) : ℕ :=
  10 * lm43MaxRadius N d

/-- Canonical three-call form of `source_target_or_large_admissible`.
Claims 4.5 and 4.6 have the same target and retained loss; the final call has
target `10 * maxRadius² * targetOrder` and loss `10 * maxRadius`.

Thus a caller may handle the direct radius-one branch first.  Only the
complementary branch must construct the `D²` source sample, and that branch
supplies precisely `LM37SourceBounds.large_lower`. -/
theorem lm43_radiusOne_targets_or_sourceLargeAdmissible
    {N d : ℕ} (hTarget : 0 < lm43TargetOrder N d)
    (hRadius : 2 ≤ lm43MaxRadius N d)
    (hCutoff : 0 < lm37SourceCutoff N) :
    (lm43TargetOrder N d ≤
        d - d / 2 - lm43ReachRetainedCost N d ∨
      lm43SourceLargeAdmissible N d) ∧
    (lm43TargetOrder N d ≤
        d - d / 2 - lm43ReachRetainedCost N d ∨
      lm43SourceLargeAdmissible N d) ∧
    (lm43BallTarget N d ≤
        d - d / 2 - lm43FinalRetainedCost N d ∨
      lm43SourceLargeAdmissible N d) := by
  let D := lm43MaxSlowSize N d
  let cutoff := lm37SourceCutoff N
  let m := lm43MaxRadius N d
  have hD : 0 < D := hTarget.trans_le (lm43TargetOrder_le_maxSlowSize N d)
  have hballPos : 0 < lm43BallTarget N d := by
    simp only [lm43BallTarget]
    positivity
  have hreachCostBall : lm43ReachRetainedCost N d ≤ lm43BallTarget N d := by
    dsimp [lm43ReachRetainedCost, lm43BallTarget, m] at hRadius ⊢
    have hmSq : m ≤ m ^ 2 := by nlinarith
    have hM : 1 ≤ lm43TargetOrder N d := hTarget
    nlinarith
  have hfinalCostBall : lm43FinalRetainedCost N d ≤ lm43BallTarget N d := by
    dsimp [lm43FinalRetainedCost, lm43BallTarget, m] at hRadius ⊢
    have hM : 1 ≤ lm43TargetOrder N d := hTarget
    nlinarith
  have hballD : lm43BallTarget N d ≤ D := by
    simpa only [D] using lm43BallTarget_le_maxSlowSize N d
  have hDtoSquare : D ≤ D ^ 2 := by nlinarith
  have hDToProduct : D ≤ D ^ 2 * cutoff := by
    exact hDtoSquare.trans (Nat.le_mul_of_pos_right _ (by simpa [cutoff] using hCutoff))
  have hreachCost : lm43ReachRetainedCost N d ≤ D ^ 2 * cutoff :=
    hreachCostBall.trans (hballD.trans hDToProduct)
  have hfinalCost : lm43FinalRetainedCost N d ≤ D ^ 2 * cutoff :=
    hfinalCostBall.trans (hballD.trans hDToProduct)
  have hreach := source_target_or_large_admissible (d := d) hD
    (by simpa [cutoff] using hCutoff)
    (by simpa [D] using lm43TargetOrder_le_maxSlowSize N d) hreachCost
  have hfinal := source_target_or_large_admissible (d := d) hD
    (by simpa [cutoff] using hCutoff) hballD hfinalCost
  simpa [lm43SourceLargeAdmissible, D, cutoff] using
    And.intro hreach (And.intro hreach hfinal)

end Erdos63
