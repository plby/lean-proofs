import Wikipedia.NoExoticSixSphere.OrthogonalCutoffDescent

/-!
# A margin below a noncritical polygon energy band

The critical locus inside a compact sublevel is compact. If all its energies
are strictly below a target level, compactness separates them uniformly from
that level. This supplies the lower cutoff threshold for the deformation.
-/

open Set
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalVertexSpace

variable {n m : ℕ}

theorem exists_noncritical_margin (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (k E : ℝ) (hcompact : IsCompact (energySublevel a b τ E))
    (hn : ∀ v ∈ energyBand a b τ k E,
      mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v ≠ 0) :
    ∃ l < k, ∀ v ∈ energyBand a b τ l E,
      mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v ≠ 0 := by
  let C := energySublevel a b τ E ∩ jumpSquareNorm a b τ ⁻¹' ({0} : Set ℝ)
  have hj : ContinuousOn (jumpSquareNorm a b τ) (energySublevel a b τ E) :=
    fun v hv ↦ (continuousAt_jumpSquareNorm a b τ hv.1).continuousWithinAt
  have hC : IsCompact C :=
    (hj.preimage_isClosed_of_isClosed hcompact.isClosed isClosed_singleton).isCompact
  have he : ContinuousOn (energy a b τ) C :=
    (contMDiffOn_energy a b τ).continuousOn.mono (fun _ hv ↦ hv.1.1)
  have hbelow : ∀ v ∈ C, energy a b τ v < k := by
    intro v hv
    by_contra h
    have hzero : jumpSquareNorm a b τ v = 0 := hv.2
    exact hn v ⟨hv.1, le_of_not_gt h⟩
      ((mfderiv_energy_eq_zero_iff a b τ v hv.1.1).mpr
        ((jumpSquareNorm_eq_zero_iff a b τ v).mp hzero))
  obtain ⟨u, hu, hub⟩ : ∃ u : ℝ, u < k ∧ ∀ v ∈ C, energy a b τ v ≤ u :=
    IsCompact.exists_forall_le' (α := OrderDual ℝ) hC he hbelow
  refine ⟨(u + k) / 2, by linarith, ?_⟩
  intro v hv hzero
  have hvC : v ∈ C := ⟨hv.1,
    (jumpSquareNorm_eq_zero_iff a b τ v).mpr
      ((mfderiv_energy_eq_zero_iff a b τ v hv.1.1).mp hzero)⟩
  have hh := hub v hvC
  have hlo : (u + k) / 2 ≤ energy a b τ v := hv.2
  linarith

end NoExoticSixSphere.OrthogonalPolygon
