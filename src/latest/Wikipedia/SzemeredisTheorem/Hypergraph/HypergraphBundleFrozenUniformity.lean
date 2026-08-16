import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleConfigurationStep

/-!
# Frozen bundle uniformity

This file records the exact interface between mixed preliminary
regularity and the frozen-uniformity input of generalized bundle
counting.

For a selected occurrence edge `g₀`, preliminary regularity applies on
the canonically enumerated projected face.  What remains is a purely
combinatorial representation statement: after the occurrence variables
outside `g₀` have been fixed, the erased bundle product is a bounded
lower-face cut test on that projected face.

The representation is separated from the analytic implication for two
reasons.

* It makes explicit that no stronger analytic regularity lemma is needed.
  Ordinary bounded face-cut regularity is exactly the required norm.
* It gives the source-style regularity certificate a precise target while
  the dependent reindexing of arbitrary bundle vertices is developed.

The key combinatorial fact behind the representation is that every
remaining occurrence edge omits a vertex of `g₀`: if it contained all of
`g₀`, maximality of `g₀` would force equality, contradicting its presence
in the erased edge family.  Injectivity of the bundle projection on
`g₀` transports such a missing occurrence vertex to a missing coordinate
of the canonical positive ordered face.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

/-! ## A missing selected vertex -/

/-- Every edge left after erasing a maximum-cardinality edge omits at
least one vertex of the selected edge.  This is the structural reason that
each frozen remainder factor belongs to a proper-face cut coordinate. -/
theorem exists_selectedVertex_not_mem_of_mem_erase
    {J K : Type*} [DecidableEq J] [DecidableEq K]
    {H : Finset (Finset J)}
    (B : HypergraphBundle J K H)
    {g₀ g : Finset K}
    (hg : g ∈ B.edges.erase g₀)
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card) :
    ∃ v ∈ g₀, v ∉ g := by
  classical
  by_contra hmissing
  have hsubset : g₀ ⊆ g := by
    intro v hv
    by_contra hvg
    exact hmissing ⟨v, hv, hvg⟩
  have hgB : g ∈ B.edges :=
    Finset.mem_of_mem_erase hg
  have heq : g₀ = g :=
    Finset.eq_of_subset_of_card_le hsubset (hmax g hgB)
  exact (Finset.mem_erase.mp hg).1 heq.symm

/-! ## The selected face regularity state -/

/-- The fine-boundary regularity state on the canonical projected face of
an occurrence edge. -/
noncomputable def orderedConfigurationBundleFaceState
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    FaceRegularityState
      (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
        G) :=
  ⟨orderedBoundaryPartition
    (positiveFaceLowerLayer P.fine
      (B.orderedConfigurationBundleFace hg hne))
    (B.orderedConfigurationBundleFace hg hne).face⟩

/-- The coarse upper atom whose fine-boundary residual is the selected
bundle uniform function. -/
noncomputable def orderedConfigurationBundleFaceTarget
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
      G) → ℝ :=
  partitionAtomIndicator
    (P.coarse.partition
      (B.orderedConfigurationBundleFace hg hne).lowerRank.succ
      (B.orderedConfigurationBundleFace hg hne).face)
    (A.atom
      (B.orderedConfigurationBundleFace hg hne).lowerRank.succ
      (B.orderedConfigurationBundleFace hg hne).face)

/-! ## The exact combinatorial transport obligation -/

/-- Every frozen bundle remainder has a bounded cut representation on
the selected projected face.

This predicate contains no analytic estimate.  Its equality is the
dependent reindexing theorem: the selected occurrence tuple is transported
through `projectionEquiv` and the increasing enumeration of its projected
edge, while every remaining occurrence-edge factor is assigned to one
coordinate that it omits. -/
def HasOrderedConfigurationBundleFrozenCutRepresentation
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r)),
    B.IsClosedUnderInclusion →
    ∀ {g₀ : Finset K}, (hg₀ : g₀ ∈ B.edges) →
      (∀ g ∈ B.edges, g.card ≤ g₀.card) →
      (hne : g₀.Nonempty) →
      ∀ z : EdgeComplement g₀ → G,
        ∃ u :
            CutTestFamily G
              ((B.orderedConfigurationBundleFace
                hg₀ hne).lowerRank.1 + 1),
          IsBoundedCutTest u ∧
            B.frozenEdgeCorrelation g₀
                (B.orderedConfigurationBundleUniform
                  P A hg₀ hne)
                (B.pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A)) z =
              (B.orderedConfigurationBundleFaceState
                  P hg₀ hne).faceCutCorrelation
                (B.orderedConfigurationBundleFaceTarget
                  P A hg₀ hne)
                u

/-! ## Preliminary regularity gives the frozen estimate -/

/-- Common-tolerance mixed preliminary regularity gives frozen bundle
uniformity once the remainder has been reindexed as a bounded face cut. -/
theorem hasOrderedConfigurationBundleFrozenUniformity_of_fullyMixed
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : ℝ)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (hcut :
      HasOrderedConfigurationBundleFrozenCutRepresentation P A) :
    HasOrderedConfigurationBundleFrozenUniformity P A τ := by
  intro K _instK _decK B hclosed g₀ hg₀ hmax hne z
  obtain ⟨u, hu, hreindex⟩ :=
    hcut K B hclosed hg₀ hmax hne z
  rw [hreindex]
  exact
    mixedConfigurationFace_isFaceCutRegular
      P A (fun _ => τ) hregular
      (B.orderedConfigurationBundleFace hg₀ hne)
      u hu

/-! ## Source-full certificate -/

/-- Minimal source-full preliminary regularity package needed by the
bundle uniformity step.  The first field is the existing all-rank analytic
certificate.  The second is the combinatorial frozen-cut representation,
so it does not ask the regularity selector to prove any new estimate. -/
structure IsSourceFullBundlePreliminaryOrderedRegular
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : ℝ) : Prop where
  fullyMixed :
    IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ)
  frozenCut :
    HasOrderedConfigurationBundleFrozenCutRepresentation P A

/-- The source-full package supplies the exact frozen-uniformity predicate
consumed by the ordered-configuration bundle step. -/
theorem IsSourceFullBundlePreliminaryOrderedRegular.frozenUniformity
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : ℝ)
    (h : IsSourceFullBundlePreliminaryOrderedRegular P A τ) :
    HasOrderedConfigurationBundleFrozenUniformity P A τ :=
  hasOrderedConfigurationBundleFrozenUniformity_of_fullyMixed
    P A τ h.fullyMixed h.frozenCut

end HypergraphBundle

end Wikipedia.SzemeredisTheorem
