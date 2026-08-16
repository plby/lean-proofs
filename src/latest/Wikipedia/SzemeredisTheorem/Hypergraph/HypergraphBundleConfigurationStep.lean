import Wikipedia.SzemeredisTheorem.Hypergraph.ConfigurationWeightedDefect
import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleConfigurationBridge
import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleRelativeCounting

/-!
# The ordered-configuration one-edge bundle step

This file isolates the last analytic bridge between ordered atom
configurations and Tao's generalized bundle-counting induction.

For a nonempty occurrence edge `g₀`, its bundle projection is a nonempty
base edge of cardinality at most `r`, hence has a canonical positive
ordered face.  Pulling the configuration indicator back to `g₀` then has
the exact mixed decomposition

```
indicator = coarse density + boundary defect + fine-boundary residual.
```

The generalized counting file already turns a boundary-localized square
estimate into the required square-root error and turns frozen correlation
bounds into the required uniform error.  The two predicates below state
exactly the remaining transport obligations.

The localized-defect predicate is deliberately *weighted by the complete
strict-boundary bundle count*.  The existing
`ClosedOrderedAtomConfiguration.IsMixedGood` estimate controls the defect
on the canonical coarse boundary atom.  Since a strict bundle boundary
also contains all lower-rank configuration factors, obtaining the
weighted statement is an additional hypothesis; it does not follow merely
by discarding factors from the unweighted localized mass.

The frozen-uniformity predicate is the combinatorial reindexing statement
that, after the outside occurrence variables are fixed, the remaining
bundle product is a bounded cut test on the selected projected face.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

/-! ## The canonical face of a nonempty occurrence edge -/

/-- A nonempty occurrence edge has nonempty projected base edge. -/
theorem projectedEdge_nonempty
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (_hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    (g.image B.projection).Nonempty := by
  exact Finset.image_nonempty.mpr hne

/-- Every projected occurrence edge has cardinality at most the complex
rank. -/
theorem projectedEdge_card_le
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges) :
    (g.image B.projection).card ≤ r := by
  exact
    (mem_orderedConfigurationBaseEdges_iff
      (g.image B.projection)).1
      (B.projection_mem_base g hg)

/-- The positive ordered face canonically enumerating the projection of a
nonempty occurrence edge. -/
noncomputable def orderedConfigurationBundleFace
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    PositiveOrderedFace k r :=
  positiveOrderedFaceOfEdge
    (g.image B.projection)
    (B.projectedEdge_nonempty hg hne)
    (B.projectedEdge_card_le hg)

/-- Transport an occurrence-edge tuple first to the projected base edge
and then to its increasing ordered enumeration. -/
noncomputable def orderedConfigurationBundleFaceTuple
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) → G :=
  orderedConfigurationEdgeTuple
    (g.image B.projection)
    (B.projectedEdge_nonempty hg hne)
    (B.projectedEdge_card_le hg)
    (B.projectedEdgeTuple hg y)

/-! ## The transported mixed decomposition -/

/-- The fine-minus-coarse boundary defect on a selected occurrence edge. -/
noncomputable def orderedConfigurationBundleDefect
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  mixedConfigurationDefect P A
    (B.orderedConfigurationBundleFace hg hne)
    (B.orderedConfigurationBundleFaceTuple hg hne y)

/-- The coarse-upper residual after conditioning on the fine boundary,
transported to a selected occurrence edge. -/
noncomputable def orderedConfigurationBundleUniform
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  mixedConfigurationUniform P A
    (B.orderedConfigurationBundleFace hg hne)
    (B.orderedConfigurationBundleFaceTuple hg hne y)

/-- The projected base density is the mixed coarse density of the
canonical projected face. -/
theorem orderedConfigurationBaseDensity_projectedEdge
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    orderedConfigurationBaseDensity P A
        (g.image B.projection) =
      mixedConfigurationCoarseDensity P A
        (B.orderedConfigurationBundleFace hg hne) := by
  unfold orderedConfigurationBaseDensity
  simp only [
    dif_pos (B.projectedEdge_nonempty hg hne),
    dif_pos (B.projectedEdge_card_le hg)]
  rfl

/-- Exact main/defect/uniform decomposition after pullback to any nonempty
occurrence edge. -/
theorem pullback_orderedConfigurationBaseWeight_decompose
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g y =
      orderedConfigurationBaseDensity P A
          (g.image B.projection) +
        B.orderedConfigurationBundleDefect P A hg hne y +
        B.orderedConfigurationBundleUniform P A hg hne y := by
  rw [B.pullbackBaseEdgeWeight_of_mem
    (orderedConfigurationBaseWeight A) hg y]
  rw [B.orderedConfigurationBaseDensity_projectedEdge
    P A hg hne]
  unfold orderedConfigurationBaseWeight
  simp only [
    dif_pos (B.projectedEdge_nonempty hg hne),
    dif_pos (B.projectedEdge_card_le hg)]
  exact
    mixedConfigurationFaceWeight_decompose P A
      (B.orderedConfigurationBundleFace hg hne)
      (B.orderedConfigurationBundleFaceTuple hg hne y)

/-! ## The two exact transport obligations -/

/-- The selected defect multiplied by the complete strict-boundary
configuration indicator. -/
noncomputable def orderedConfigurationBundleLocalizedDefect
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) : ℝ :=
  B.orderedConfigurationBundleDefect P A hg hne y *
    B.strictBoundaryLocalProduct g
      (B.pullbackBaseEdgeWeight
        (orderedConfigurationBaseWeight A)) y

/-- Missing weighted localization statement for ordered configurations in
arbitrary closed bundles.

This is stronger than the currently available unweighted localized defect
bound: the right side is the actual strict-boundary bundle count, not the
mass of the containing coarse boundary atom. -/
def HasOrderedConfigurationBundleLocalizedDefect
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (β : ℕ → ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r)),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (hne : g₀.Nonempty) →
      mean (fun y =>
        B.orderedConfigurationBundleLocalizedDefect
            P A hg₀ hne y ^ 2) ≤
        β g₀.card *
          (B.strictBoundary g₀).bundleCount
            ((B.strictBoundary g₀).pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A))

/-- Missing frozen-cut transport statement for ordered configurations in
arbitrary bundles.  It says precisely that every frozen remainder is a
bounded face cut covered by the common mixed preliminary regularity
tolerance. -/
def HasOrderedConfigurationBundleFrozenUniformity
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : ℝ) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r)),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (hne : g₀.Nonempty) →
      ∀ z : EdgeComplement g₀ → G,
        |B.frozenEdgeCorrelation g₀
            (B.orderedConfigurationBundleUniform
              P A hg₀ hne)
            (B.pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A)) z| ≤
          τ

/-! ## Assembly of the one-edge input -/

/-- The two transport obligations, together with the exact decomposition,
give the analytic one-edge hypothesis consumed by the relative generalized
bundle-counting induction. -/
theorem hasTaoBundleCountingStep_orderedConfiguration
    [Nonempty G]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (β : ℕ → ℝ) (τ : ℝ)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hlocalized :
      HasOrderedConfigurationBundleLocalizedDefect P A β)
    (hfrozen :
      HasOrderedConfigurationBundleFrozenUniformity P A τ) :
    HasTaoBundleCountingStep
      (H := orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      β τ := by
  intro K _instK _decK B hclosed g₀ hg₀ hmax
  by_cases hne : g₀.Nonempty
  · let W :=
      B.pullbackBaseEdgeWeight
        (orderedConfigurationBaseWeight A)
    let p :=
      orderedConfigurationBaseDensity P A
        (g₀.image B.projection)
    let b :=
      B.orderedConfigurationBundleDefect
        P A hg₀ hne
    let c :=
      B.orderedConfigurationBundleUniform
        P A hg₀ hne
    let bLocalized :=
      B.orderedConfigurationBundleLocalizedDefect
        P A hg₀ hne
    have hdecomp :
        ∀ y, W g₀ y = p + b y + c y := by
      intro y
      simpa only [W, p, b, c] using
        B.pullback_orderedConfigurationBaseWeight_decompose
          P A hg₀ hne y
    have hcount :
        B.bundleCount W =
          p * (B.eraseEdge g₀).bundleCount W +
            B.edgeContribution g₀ b W +
            B.edgeContribution g₀ c W :=
      B.bundleCount_decompose_edge
        W hg₀ p b c hdecomp
    have herase :
        (B.eraseEdge g₀).bundleCount W =
          (B.eraseEdge g₀).bundleCount
            ((B.eraseEdge g₀).pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A)) := by
      exact
        B.eraseEdge_bundleCount_pullback g₀
          (orderedConfigurationBaseWeight A)
    have hIdempotent :
        B.WeightsIdempotent W := by
      exact B.pullbackBaseEdgeWeight_weightsIdempotent
        (orderedConfigurationBaseWeight A)
        (orderedConfigurationBaseWeight_idempotent A)
    have hlocalizeContribution :
        B.edgeContribution g₀ b W =
          B.edgeContribution g₀ bLocalized W := by
      change B.edgeContribution g₀ b W =
        B.edgeContribution g₀
          (fun y =>
            b y * B.strictBoundaryLocalProduct g₀ W y) W
      exact B.edgeContribution_mul_strictBoundaryLocalProduct
        g₀ b W hIdempotent
    have hdefect :
        |B.edgeContribution g₀ b W| ≤
          Real.sqrt
            ((β g₀.card *
                (B.strictBoundary g₀).bundleCount
                  ((B.strictBoundary g₀).pullbackBaseEdgeWeight
                      (orderedConfigurationBaseWeight A))) *
              ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
                  (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight
                      (orderedConfigurationBaseWeight A))) := by
      rw [hlocalizeContribution]
      exact
        B.abs_edgeContribution_pullback_le_sqrt_boundary_mul_lowerOrder
          hclosed hg₀ hmax
          (orderedConfigurationBaseWeight A)
          (orderedConfigurationBaseWeight_unitInterval A)
          (orderedConfigurationBaseWeight_idempotent A)
          bLocalized (hβ g₀.card)
          (hlocalized K B hclosed hg₀ hmax hne)
    have huniform :
        |B.edgeContribution g₀ c W| ≤ τ := by
      exact B.abs_edgeContribution_le_of_frozen
        g₀ c W
        (hfrozen K B hclosed hg₀ hmax hne)
    rw [hcount, herase]
    calc
      |p *
              (B.eraseEdge g₀).bundleCount
                ((B.eraseEdge g₀).pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A)) +
            B.edgeContribution g₀ b W +
            B.edgeContribution g₀ c W -
          p *
              (B.eraseEdge g₀).bundleCount
                ((B.eraseEdge g₀).pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A))| =
          |B.edgeContribution g₀ b W +
            B.edgeContribution g₀ c W| := by
        congr 1
        ring
      _ ≤
          |B.edgeContribution g₀ b W| +
            |B.edgeContribution g₀ c W| :=
        abs_add_le _ _
      _ ≤
          Real.sqrt
              ((β g₀.card *
                  (B.strictBoundary g₀).bundleCount
                    ((B.strictBoundary g₀).pullbackBaseEdgeWeight
                        (orderedConfigurationBaseWeight A))) *
                ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleCount
                    (((B.lowerOrder g₀.card).duplicateOutside g₀).pullbackBaseEdgeWeight
                        (orderedConfigurationBaseWeight A))) +
            τ :=
        add_le_add hdefect huniform
  · have hg₀empty : g₀ = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    subst g₀
    let W :=
      B.pullbackBaseEdgeWeight
        (orderedConfigurationBaseWeight A)
    have hweight :
        ∀ y, W ∅ y = 1 := by
      intro y
      dsimp only [W]
      rw [B.pullbackBaseEdgeWeight_of_mem
        (orderedConfigurationBaseWeight A) hg₀ y]
      simp only [Finset.image_empty]
      exact orderedConfigurationBaseWeight_empty A
        (B.projectedEdgeTuple hg₀ y)
    have hcount :
        B.bundleCount W =
          (B.eraseEdge ∅).bundleCount
            ((B.eraseEdge ∅).pullbackBaseEdgeWeight
              (orderedConfigurationBaseWeight A)) := by
      calc
        B.bundleCount W =
            B.edgeContribution ∅ (W ∅) W :=
          B.bundleCount_eq_edgeContribution W hg₀
        _ =
            B.edgeContribution ∅ (fun _ => 1) W := by
          apply congrArg
            (fun q => B.edgeContribution ∅ q W)
          funext y
          exact hweight y
        _ = (B.eraseEdge ∅).bundleCount W := by
          rw [B.edgeContribution_const]
          simp
        _ =
            (B.eraseEdge ∅).bundleCount
              ((B.eraseEdge ∅).pullbackBaseEdgeWeight
                (orderedConfigurationBaseWeight A)) :=
          B.eraseEdge_bundleCount_pullback ∅
            (orderedConfigurationBaseWeight A)
    rw [hcount, Finset.image_empty,
      orderedConfigurationBaseDensity_empty,
      one_mul, sub_self, abs_zero]
    exact add_nonneg (Real.sqrt_nonneg _) hτ

end HypergraphBundle

end Wikipedia.SzemeredisTheorem
