import Wikipedia.NoExoticSixSphere.CompactSupportEquivalence
import Wikipedia.NoExoticSixSphere.PartialSupportEvaluation
import Wikipedia.NoExoticSixSphere.CompactEuclideanSupportDetection

/-!
# Compact supports in the original manifold charts

The proved Euclidean support properties are transported along the
original partial chart. The compact support is arbitrary inside the
source; it need not be a ball or have a convex chart image.
-/

noncomputable section

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [T2Space M] [T2Space N] [ChartedSpace E M] [ChartedSpace E N]

/-- The actual partial-homeomorphism equivalence transports compact-support properties. -/
theorem CompactFundamentalSupport.of_partialHomeomorph (e : OpenPartialHomeomorph M N)
    {K : Set M} {L : Set N} (hK : IsCompact K)
    (hKs : K ⊆ e.source) (hLt : L ⊆ e.target)
    (hKL : ∀ x ∈ e.source, x ∈ K ↔ e x ∈ L)
    (hL : CompactFundamentalSupport (E := E) n L) :
    CompactFundamentalSupport (E := E) n K := by
  apply CompactFundamentalSupport.of_evaluation_equivalences n hK
    (partialSupportPoints e hKs hLt hKL)
    (fun k => partialHomeomorphEquiv 2 (by decide) e hK.isClosed hL.compact.isClosed
      hKs hLt hKL k)
    (fun x => localPartialHomeomorphEquiv 2 (by decide) e x (hKs x.property) (n + 3))
    (fun x a => evaluate_partialHomeomorphEquiv 2 (by decide) e hK.isClosed hL.compact.isClosed
      hKs hLt hKL x x.property (n + 3) a) hL

/-- Every compact subset of an actual Euclidean chart has the full proved support properties. -/
theorem compact_chart_fundamentalSupport (e : OpenPartialHomeomorph M E)
    (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source) :
    CompactFundamentalSupport (E := E) n K := by
  let L : Set E := e '' K
  have hL : IsCompact L := hK.image_of_continuousOn (e.continuousOn.mono hKs)
  have hLt : L ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source (hKs hx)
  have hKL : ∀ x ∈ e.source, x ∈ K ↔ e x ∈ L := by
    intro x hx
    constructor
    · exact fun h => ⟨x, h, rfl⟩
    · rintro ⟨y, hy, he⟩
      have hyx : y = x := e.injOn (hKs hy) hx he
      exact hyx ▸ hy
  exact CompactFundamentalSupport.of_partialHomeomorph n e hK hKs hLt hKL
    (compactEuclidean_fundamentalSupport n L hL)

end NoExoticSixSphere.SupportedRelativeHomology
