import Wikipedia.SzemeredisTheorem.Hypergraph.SourceFullBundleCounting
import Wikipedia.SzemeredisTheorem.Hypergraph.SourceFullCoarseTargetRegularity

/-!
# Rankwise source-full bundle counting

The source full-regularity hierarchy supplies a different density and
defect threshold at each positive rank, together with one common
fine-boundary regularity error.  This file assembles those data directly
with the generalized bundle-counting envelope.

Unlike `SourceFullBundleCounting`, no parameter is required to be constant
in the rank.  The final lower bound is quantitative: if the chosen envelope
has error below one half, then every source-full good closed configuration
has count at least one half of the product of its prescribed rankwise
density floors.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## The finite horizon of the initial configuration bundle -/

/-- Every edge of the initial ordered-configuration bundle has cardinality
at most the complex rank. -/
theorem orderedConfigurationInitialBundle_order_le
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).order ≤ r := by
  unfold HypergraphBundle.order
  rw [orderedConfigurationInitialBundle_edges]
  apply Finset.sup_le
  intro e he
  exact (mem_orderedConfigurationBaseEdges_iff e).1 he

/-! ## The source-full regularity certificate as a counting input -/

/-- The selected mixed-regularity tolerances in a source-full certificate
are all bounded by its advertised common reciprocal tolerance. -/
theorem SourceFullCoarseTargetSchedule.Certificate.isFullyMixedPreliminaryOrderedRegular_common
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {initialBound : Fin (r + 1) → ℕ}
    {F : NatGrowthFunction}
    {scaleFloor : ℕ}
    (R : SourceFullCoarseTargetSchedule.Certificate
      k r initial initialBound F scaleFloor) :
    IsFullyMixedPreliminaryOrderedRegular
      R.regularity.toCoarseFine
      (fun _ => sourceFullCommonTolerance F R.scale) := by
  intro j e a b
  exact
    (R.regularity.mixedRegular j e a b).trans
      (R.selected_tolerance_le_common j)

/-! ## Rankwise base-density and one-edge inputs -/

/-- Rankwise source-full goodness supplies the base-density lower bound on
every edge of the ordered-configuration base hypergraph.  Rank zero is the
neutral empty edge and is handled by `α 0 ≤ 1`. -/
theorem orderedConfigurationBaseDensity_ge_of_sourceFullMixedGood_rankwise
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hαzero : α 0 ≤ 1)
    (hgood : A.IsSourceFullMixedGood P α β) :
    ∀ e ∈ orderedConfigurationBaseEdges k r,
      α e.card ≤ orderedConfigurationBaseDensity P A e := by
  intro e he
  by_cases he0 : e = ∅
  · subst e
    simpa using hαzero
  · have hene : e.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr he0
    have her : e.card ≤ r :=
      (mem_orderedConfigurationBaseEdges_iff e).1 he
    have hdensity :=
      (hgood (positiveOrderedFaceOfEdge e hene her)).1
    have hrank :
        (positiveOrderedFaceOfEdge e hene her).rank = e.card := by
      rw [← positiveOrderedFaceEdge_card,
        positiveOrderedFaceEdge_ofEdge]
    rw [hrank] at hdensity
    simpa [sourceFullMixedCoarseDensity,
      orderedConfigurationBaseDensity, hene, her] using hdensity

/-- Rankwise source-full localized defects and a common frozen-uniformity
bound give the one-edge input used by relative generalized counting. -/
theorem hasTaoBundleCountingStep_orderedConfiguration_of_sourceFull_rankwise
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) (τ : ℝ)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ)) :
    HasTaoBundleCountingStep
      (H := orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      β τ := by
  apply HypergraphBundle.hasTaoBundleCountingStep_orderedConfiguration
      P A β τ hβ hτ
  · exact
      HypergraphBundle.hasOrderedConfigurationBundleLocalizedDefect_of_sourceFullMixedGood
        P A α β hgood
  · exact
      HypergraphBundle.hasOrderedConfigurationBundleFrozenUniformity_of_fullyMixed
        P A τ hregular
        (HypergraphBundle.hasOrderedConfigurationBundleFrozenCutRepresentation
          P A)

/-! ## Relative counting with an arbitrary rankwise envelope -/

/-- General source-full relative counting with rankwise density and defect
arrays and an arbitrary valid bundle-counting envelope. -/
theorem abs_bundleCount_orderedConfiguration_sub_main_le_rankwiseEnvelope
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hαzero : α 0 ≤ 1)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (henvelope : IsBundleCountingEnvelope α β μ τ E)
    {K : Type} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (hclosed : B.IsClosedUnderInclusion) :
    |B.bundleCount
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) -
        B.bundleMainProduct
          (orderedConfigurationBaseDensity P A)| ≤
      E B.order B.edges.card *
        B.bundleMainProduct
          (orderedConfigurationBaseDensity P A) := by
  exact
    @abs_bundleCount_pullback_sub_bundleMainProduct_le_envelope
      (Fin k) G inferInstance inferInstance
      (orderedConfigurationBaseEdges k r) inferInstance
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      α β μ τ E
      (orderedConfigurationBaseWeight_unitInterval A)
      (orderedConfigurationBaseWeight_idempotent A)
      (orderedConfigurationBaseWeight_empty A)
      (orderedConfigurationBaseDensity_empty P A)
      (orderedConfigurationBaseDensity_ge_of_sourceFullMixedGood_rankwise
        P A α β hαzero hgood)
      (hasTaoBundleCountingStep_orderedConfiguration_of_sourceFull_rankwise
        P A α β τ hβ hτ hgood hregular)
      henvelope K inferInstance inferInstance B hclosed

/-! ## Initial configuration and a uniform quantitative lower bound -/

/-- The initial ordered-configuration count is bounded below by the
rankwise main-density product times one minus the selected envelope error. -/
theorem one_sub_rankwiseEnvelope_mul_densityProduct_le_fullConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hαzero : α 0 ≤ 1)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (henvelope : IsBundleCountingEnvelope α β μ τ E) :
    (1 - E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card) *
        (∏ e : PositiveOrderedFace k r,
          mixedConfigurationCoarseDensity P A e) ≤
      fullConfigurationCount A := by
  have hcount :=
    abs_bundleCount_orderedConfiguration_sub_main_le_rankwiseEnvelope
      P A α β μ τ E hαzero hβ hτ hgood hregular henvelope
      (orderedConfigurationInitialBundle k r)
      (orderedConfigurationInitialBundle_closed k r)
  rw [orderedConfigurationInitialBundle_bundleCount A,
    orderedConfigurationInitialBundle_bundleMainProduct P A] at hcount
  have hlower :
      - (E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card *
            (∏ e : PositiveOrderedFace k r,
              mixedConfigurationCoarseDensity P A e)) ≤
        fullConfigurationCount A -
          (∏ e : PositiveOrderedFace k r,
            mixedConfigurationCoarseDensity P A e) :=
    neg_le_of_abs_le hcount
  linarith

/-- Error below one half gives a quantitative source-full configuration
count: one half of the product of the prescribed rankwise density floors. -/
theorem half_rankwiseDensityProduct_le_fullConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hα : ∀ d, 0 < α d)
    (hαone : ∀ d, α d ≤ 1)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (henvelope : IsBundleCountingEnvelope α β μ τ E)
    (herror :
      E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card <
        1 / 2) :
    (1 / 2 : ℝ) *
        (∏ e : PositiveOrderedFace k r, α e.rank) ≤
      fullConfigurationCount A := by
  have hlower :=
    one_sub_rankwiseEnvelope_mul_densityProduct_le_fullConfigurationCount
      P A α β μ τ E (hαone 0) hβ hτ hgood hregular henvelope
  have hfloorProduct_nonneg :
      0 ≤ ∏ e : PositiveOrderedFace k r, α e.rank := by
    exact Finset.prod_nonneg fun e _ => (hα e.rank).le
  have hdensityProduct :
      (∏ e : PositiveOrderedFace k r, α e.rank) ≤
        ∏ e : PositiveOrderedFace k r,
          mixedConfigurationCoarseDensity P A e := by
    apply Finset.prod_le_prod
    · intro e _he
      exact (hα e.rank).le
    · intro e _he
      simpa [sourceFullMixedCoarseDensity] using (hgood e).1
  have hone :
      (1 / 2 : ℝ) ≤
        1 - E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card := by
    linarith
  have hone_nonneg :
      0 ≤
        1 - E
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card := by
    linarith
  calc
    (1 / 2 : ℝ) *
          (∏ e : PositiveOrderedFace k r, α e.rank) ≤
        (1 - E
            (orderedConfigurationInitialBundle k r).order
            (orderedConfigurationInitialBundle k r).edges.card) *
          (∏ e : PositiveOrderedFace k r, α e.rank) :=
      mul_le_mul_of_nonneg_right hone hfloorProduct_nonneg
    _ ≤
        (1 - E
            (orderedConfigurationInitialBundle k r).order
            (orderedConfigurationInitialBundle k r).edges.card) *
          (∏ e : PositiveOrderedFace k r,
            mixedConfigurationCoarseDensity P A e) := by
      exact mul_le_mul_of_nonneg_left hdensityProduct hone_nonneg
    _ ≤ fullConfigurationCount A :=
      hlower

/-- It is enough to control the envelope at the ambient complex rank:
the initial configuration bundle has order at most that rank, and every
valid envelope is monotone in its order argument. -/
theorem half_rankwiseDensityProduct_le_fullConfigurationCount_of_rankBound
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hα : ∀ d, 0 < α d)
    (hαone : ∀ d, α d ≤ 1)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (henvelope : IsBundleCountingEnvelope α β μ τ E)
    (herror :
      E r (orderedConfigurationInitialBundle k r).edges.card <
        1 / 2) :
    (1 / 2 : ℝ) *
        (∏ e : PositiveOrderedFace k r, α e.rank) ≤
      fullConfigurationCount A := by
  apply
    half_rankwiseDensityProduct_le_fullConfigurationCount
      P A α β μ τ E hα hαone hβ hτ hgood hregular henvelope
  exact
    (henvelope.error_mono_order
      (orderedConfigurationInitialBundle_order_le k r)).trans_lt
      herror

end Wikipedia.SzemeredisTheorem
