import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleEnvelopeSelection
import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleFrozenCut
import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleSourceGoodnessBridge
import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleConfigurationBridge

/-!
# Source-full generalized bundle counting

This file assembles the source-full goodness and preliminary-regularity
certificates into the relative generalized bundle-counting theorem.  The
common density floor is `a`, while both analytic errors are `t ^ 2`; the
explicit schedule `bundleCommonEnvelopeError a t` then controls every
closed bundle pulled back from the ordered configuration.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## The common density floor on base edges -/

/-- Source-full goodness with constant floor `a` supplies the density
lower bound required by the relative bundle-counting induction, including
the neutral empty edge. -/
theorem orderedConfigurationBaseDensity_ge_of_sourceFullMixedGood
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    {a t : ℝ} (ha_one : a ≤ 1)
    (hgood :
      A.IsSourceFullMixedGood P (fun _ => a) (fun _ => t ^ 2)) :
    ∀ e ∈ orderedConfigurationBaseEdges k r,
      a ≤ orderedConfigurationBaseDensity P A e := by
  intro e he
  by_cases he0 : e = ∅
  · subst e
    simpa using ha_one
  · have hene : e.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr he0
    have her : e.card ≤ r :=
      (mem_orderedConfigurationBaseEdges_iff e).1 he
    have hdensity :=
      (hgood (positiveOrderedFaceOfEdge e hene her)).1
    simpa [sourceFullMixedCoarseDensity,
      orderedConfigurationBaseDensity, hene, her] using hdensity

/-! ## Relative counting for every closed pullback bundle -/

/-- The source-full localized-defect certificate and the frozen-cut
transport of preliminary regularity assemble into Tao's one-edge counting
interface with the common squared error. -/
theorem hasTaoBundleCountingStep_orderedConfiguration_of_sourceFull
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    {a t : ℝ}
    (hgood :
      A.IsSourceFullMixedGood P (fun _ => a) (fun _ => t ^ 2))
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => t ^ 2)) :
    HasTaoBundleCountingStep
      (H := orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      (fun _ => t ^ 2) (t ^ 2) := by
  apply HypergraphBundle.hasTaoBundleCountingStep_orderedConfiguration
      P A (fun _ => t ^ 2) (t ^ 2)
  · intro d
    exact sq_nonneg t
  · exact sq_nonneg t
  · exact
      HypergraphBundle.hasOrderedConfigurationBundleLocalizedDefect_of_sourceFullMixedGood
        P A (fun _ => a) (fun _ => t ^ 2) hgood
  · exact
      HypergraphBundle.hasOrderedConfigurationBundleFrozenUniformity_of_fullyMixed
        P A (t ^ 2) hregular
        (HypergraphBundle.hasOrderedConfigurationBundleFrozenCutRepresentation
          P A)

/-- Source-full mixed goodness and common-tolerance preliminary regularity
give the concrete relative generalized-counting estimate on every closed
bundle over the ordered-configuration base hypergraph. -/
theorem abs_bundleCount_orderedConfiguration_sub_main_le_sourceFullEnvelope
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    {a t : ℝ} (ha : 0 < a) (ha_one : a ≤ 1)
    (hgood :
      A.IsSourceFullMixedGood P (fun _ => a) (fun _ => t ^ 2))
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => t ^ 2))
    {K : Type} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (hclosed : B.IsClosedUnderInclusion) :
    |B.bundleCount
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) -
        B.bundleMainProduct
          (orderedConfigurationBaseDensity P A)| ≤
      bundleCommonEnvelopeError a t B.order B.edges.card *
        B.bundleMainProduct
          (orderedConfigurationBaseDensity P A) := by
  have hstep :
      HasTaoBundleCountingStep
        (H := orderedConfigurationBaseEdges k r)
        (orderedConfigurationBaseWeight A)
        (orderedConfigurationBaseDensity P A)
        (fun _ => t ^ 2) (t ^ 2) :=
    hasTaoBundleCountingStep_orderedConfiguration_of_sourceFull
      P A hgood hregular
  have henvelope :
      IsBundleCountingEnvelope
        (fun _ => a) (fun _ => t ^ 2) (fun _ => a) (t ^ 2)
        (bundleCommonEnvelopeError a t) :=
    bundleCommonEnvelopeError_isEnvelope ha ha_one
  exact
    @abs_bundleCount_pullback_sub_bundleMainProduct_le_envelope
      (Fin k) G inferInstance inferInstance
      (orderedConfigurationBaseEdges k r) inferInstance
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      (fun _ => a) (fun _ => t ^ 2) (fun _ => a) (t ^ 2)
      (bundleCommonEnvelopeError a t)
      (orderedConfigurationBaseWeight_unitInterval A)
      (orderedConfigurationBaseWeight_idempotent A)
      (orderedConfigurationBaseWeight_empty A)
      (orderedConfigurationBaseDensity_empty P A)
      (orderedConfigurationBaseDensity_ge_of_sourceFullMixedGood
        P A ha_one hgood)
      hstep henvelope K inferInstance inferInstance B hclosed

/-! ## Initial bundle and positivity -/

/-- The initial ordered-configuration count is at least the main-density
product multiplied by one minus the concrete source-full envelope error. -/
theorem one_sub_sourceFullEnvelope_mul_densityProduct_le_fullConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    {a t : ℝ} (ha : 0 < a) (ha_one : a ≤ 1)
    (hgood :
      A.IsSourceFullMixedGood P (fun _ => a) (fun _ => t ^ 2))
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => t ^ 2)) :
    (1 - bundleCommonEnvelopeError a t
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card) *
        (∏ e : PositiveOrderedFace k r,
          mixedConfigurationCoarseDensity P A e) ≤
      fullConfigurationCount A := by
  have hcount :=
    abs_bundleCount_orderedConfiguration_sub_main_le_sourceFullEnvelope
      P A ha ha_one hgood hregular
      (orderedConfigurationInitialBundle k r)
      (orderedConfigurationInitialBundle_closed k r)
  rw [orderedConfigurationInitialBundle_bundleCount A,
    orderedConfigurationInitialBundle_bundleMainProduct P A] at hcount
  have hlower :
      - (bundleCommonEnvelopeError a t
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card *
            (∏ e : PositiveOrderedFace k r,
              mixedConfigurationCoarseDensity P A e)) ≤
        fullConfigurationCount A -
          (∏ e : PositiveOrderedFace k r,
            mixedConfigurationCoarseDensity P A e) :=
    neg_le_of_abs_le hcount
  linarith

/-- If the concrete envelope error at the actual order and edge-cardinality
of the initial bundle is below one half, the selected closed configuration
has strictly positive normalized count. -/
theorem fullConfigurationCount_pos_of_sourceFullEnvelope_lt_half
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    {a t : ℝ} (ha : 0 < a) (ha_one : a ≤ 1)
    (hgood :
      A.IsSourceFullMixedGood P (fun _ => a) (fun _ => t ^ 2))
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => t ^ 2))
    (herror :
      bundleCommonEnvelopeError a t
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card < 1 / 2) :
    0 < fullConfigurationCount A := by
  have hlower :=
    one_sub_sourceFullEnvelope_mul_densityProduct_le_fullConfigurationCount
      P A ha ha_one hgood hregular
  have hdensity :
      0 < ∏ e : PositiveOrderedFace k r,
        mixedConfigurationCoarseDensity P A e := by
    apply Finset.prod_pos
    intro e _he
    exact ha.trans_le (by
      simpa [sourceFullMixedCoarseDensity] using (hgood e).1)
  have hone :
      0 < 1 - bundleCommonEnvelopeError a t
          (orderedConfigurationInitialBundle k r).order
          (orderedConfigurationInitialBundle k r).edges.card := by
    linarith
  exact (mul_pos hone hdensity).trans_le hlower

end Wikipedia.SzemeredisTheorem
