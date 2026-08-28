import Wikipedia.NoExoticSixSphere.LocalLoweringData
import Wikipedia.NoExoticSixSphere.OrthogonalLevelLoweringNeighborhood

/-!
# Actual polygon lowering data for the finite construction

The package is built from the proved critical/noncritical lowering theorem.
Its homotopies, quantitative bounds, and protected sublevel are not postulated.
-/

open Set Module
open scoped ContDiff Manifold Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalVertexSpace FiniteControlledLowering

variable {B H M : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [T2Space M] {n m : ℕ}

include I

theorem exists_localLoweringData (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ)
    (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : Space n m) (hv : v ∈ shortDomain a b m)
    (hanti : (a⁻¹ * b).1.1 = -(1 : Vector n →L[ℝ] Vector n))
    (habove : (n : ℝ) * Real.pi ^ 2 < energy a b τ v)
    (l ε : ℝ) (hl : l < energy a b τ v) (hε : 0 < ε) (hd : finrank ℝ B + 2 < n) :
    ∃ D : LocalLoweringData M (energy a b τ) (admissible a b m) l
        (energy a b τ v) (energy a b τ v + ε), v ∈ D.domain := by
  obtain ⟨V, hV, hvV, hVsub, hVabove, k, hlk, hk, hcross⟩ :=
    exists_quantitative_lowering_neighborhood (I := I) (M := M) a b τ hτ hzero hone v hv
      hanti habove univ isOpen_univ (mem_univ _) l ε hl hε hd
  refine ⟨{
    domain := V
    open_domain := hV
    domain_subset := hVsub.trans inter_subset_left
    domain_above := hVabove
    threshold := k
    floor_lt_threshold := hlk
    threshold_lt_level := hk
    control := ?_ }, hvV⟩
  intro ρ hρ
  obtain ⟨ζ, hζ, hcrossζ⟩ := hcross ρ hρ
  refine ⟨ζ, hζ, ?_⟩
  intro ξ hξ hξζ p hp K hK hKV
  obtain ⟨q, hq, G, hG⟩ := hcrossζ ξ hξ hξζ p hp K hK hKV
  exact ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, (hG t x).2.1, (hG t x).2.2.2.1.le,
    fun hLoss ↦ ((hG t x).2.2.2.2 hLoss).le⟩⟩

end NoExoticSixSphere.OrthogonalPolygon
