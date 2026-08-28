import Wikipedia.NoExoticSixSphere.FiniteChartFundamentalSupport
import Wikipedia.NoExoticSixSphere.LocalFundamentalNeighborhood

/-!
# Fundamental classes on arbitrary compact manifold supports

Cover the given compact subset by the interiors of actual compact chart
balls and choose a finite subcover. Its intersections with those closed
chart balls are compact, chart-contained supports whose union is the
original subset. The proved finite-union theorem assembles all support
properties, without assuming agreement of classes on the intersections.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace NoExoticSixSphere.SupportedRelativeHomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

/-- Every compact subset of the original manifold has all proved compact-support properties. -/
theorem compactManifold_fundamentalSupport (K : Set M) (hK : IsCompact K) :
    CompactFundamentalSupport (E := E) n K := by
  classical
  let e (x : K) := chartAt E (x : M)
  have hballs : ∀ x : K, ∃ B : Set M,
      IsCompact B ∧ (x : M) ∈ interior B ∧ B ⊆ (e x).source := by
    intro x
    have hx : (x : M) ∈ (e x).source := mem_chart_source E (x : M)
    obtain ⟨R, hR, hB, _⟩ := ChartClosedBall.exists_support_subset (e x) x hx univ univ_mem
    refine ⟨ChartClosedBall.support (e x) (e x x) R,
      ChartClosedBall.support_isCompact (e x) (e x x) R hB, ?_,
      ChartClosedBall.support_subset_source (e x) (e x x) R hB⟩
    exact mem_interior_iff_mem_nhds.mpr (ChartClosedBall.support_mem_nhds (e x) x hx R hR hB)
  choose B hB hxB hBS using hballs
  have hcover : K ⊆ ⋃ x : K, interior (B x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxB ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => interior (B x))
    (fun _ => isOpen_interior) hcover
  have h := finiteUnion_compactChart_support n s e (fun x => K ∩ B x)
    (fun x _ => hK.inter_right (hB x).isClosed)
    (fun x _ => inter_subset_right.trans (hBS x))
  have he : (⋃ x ∈ s, K ∩ B x) = K := by
    apply Subset.antisymm
    · intro y hy
      obtain ⟨x, _, hx⟩ := mem_iUnion₂.mp hy
      exact hx.1
    · intro y hy
      obtain ⟨x, hx, hyB⟩ := mem_iUnion₂.mp (hs hy)
      exact mem_iUnion₂.mpr ⟨x, hx, hy, interior_subset hyB⟩
  simpa only [he] using h

/-- Every compact support has a unique actual relative mod-two fundamental class. -/
theorem compactManifold_existsUnique_fundamentalClass (K : Set M) (hK : IsCompact K) :
    ∃! c : Homology (ModuleCat.of ℤ (ZMod 2)) K (n + 3), IsFundamentalOn (E := E) n K c :=
  CompactFundamentalSupport.existsUnique n (compactManifold_fundamentalSupport (E := E) n K hK)

include E in
/-- Supported relative homology of every compact subset vanishes above manifold dimension. -/
theorem compactManifold_above_subsingleton (K : Set M) (hK : IsCompact K)
    (k : ℕ) (hk : n + 3 < k) : Subsingleton (Homology (ModuleCat.of ℤ (ZMod 2)) K k) :=
  (compactManifold_fundamentalSupport (E := E) n K hK).above k hk

include E in
/-- Original point evaluations detect top-degree classes on every compact manifold support. -/
theorem compactManifold_detected (K : Set M) (hK : IsCompact K)
    (a b : Homology (ModuleCat.of ℤ (ZMod 2)) K (n + 3))
    (hab : ∀ (x : M) (hx : x ∈ K),
      evaluate (ModuleCat.of ℤ (ZMod 2)) K x hx (n + 3) a =
        evaluate (ModuleCat.of ℤ (ZMod 2)) K x hx (n + 3) b) : a = b :=
  (compactManifold_fundamentalSupport (E := E) n K hK).detected a b hab

end NoExoticSixSphere.SupportedRelativeHomology
