import Wikipedia.SmoothSixDPoincare.ParametrizedSubmanifoldCrossing
import Wikipedia.SmoothSixDPoincare.TransverseCornerPatch

/-!
# Clean transverse corners in prescribed actual sheet coordinates

The sheet parametrizations may be tubular coordinates of already constructed
arcs. Their exact axis formulas are retained by the corner, avoiding any
requirement to prescribe the arc's endpoint germ before constructing the arc.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.SmoothSixDPoincare

variable {E M D Z N P A B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace N] [ChartedSpace D N]
  [TopologicalSpace P] [ChartedSpace Z P]

/-- The corner retains the exact axes of the given native sheet parametrizations. -/
theorem exists_native_clean_corner_of_parametrizations {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : IsEmbedding F) (hembG : IsEmbedding G)
    (c : PartialDiffeomorph 𝓘(ℝ, A) 𝓘(ℝ, D) A N ∞)
    (d : PartialDiffeomorph 𝓘(ℝ, B) 𝓘(ℝ, Z) B P ∞)
    (hc0 : (0 : A) ∈ c.source) (hd0 : (0 : B) ∈ d.source)
    (hxy : G (d 0) = F (c 0))
    (hdim : Module.finrank ℝ A + Module.finrank ℝ B = Module.finrank ℝ E)
    (ht : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c 0)).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))))
    {u : A} {v : B} (hu : u ≠ 0) (hv : v ≠ 0)
    {O : Set M} (hO : IsOpen O) (hxO : F (c 0) ∈ O) :
    ∃ W : Set (ℝ × ℝ), IsOpen W ∧ (0 : ℝ × ℝ) ∈ W ∧ ∃ k : (ℝ × ℝ) → M,
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧ InjOn k W ∧ MapsTo k W O ∧
      k 0 = F (c 0) ∧
      (∀ p ∈ W, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
      (∀ p ∈ W, (k p ∈ range F ↔ p.2 = 0) ∧ (k p ∈ range G ↔ p.1 = 0)) ∧
      (∀ s, (s, 0) ∈ W → k (s, 0) = F (c (s • u))) ∧
      (∀ t, (0, t) ∈ W → k (0, t) = G (d (t • v))) := by
  obtain ⟨a, ha, Φ, hprod, _, htarget, hcenter, hleft, hright, himages⟩ :=
    exists_clean_crossingChart_of_parametrizations hF hG hembF hembG c d hc0 hd0
      hxy hdim ht hO hxO
  let L := TransverseCoordinates.cornerLinear u v
  let W := L ⁻¹' Φ.source
  let k := TransverseCoordinates.cornerMap Φ u v
  have h0W : (0 : ℝ × ℝ) ∈ W := by
    change L 0 ∈ Φ.source
    rw [map_zero]
    exact hprod ⟨mem_closedBall_self ha.le, mem_closedBall_self ha.le⟩
  refine ⟨W, Φ.open_source.preimage L.continuous, h0W, k,
    TransverseCoordinates.contMDiffOn_cornerMap Φ u v,
    TransverseCoordinates.injOn_cornerMap Φ hu hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact htarget (Φ.map_source' hp)
  · change Φ (L 0) = F (c 0)
    rw [map_zero]
    exact hcenter
  · intro p hp
    exact TransverseCoordinates.injective_mfderiv_cornerMap Φ hu hv hp
  · intro p hp
    have him := himages (L p) hp
    simpa only [L, k, TransverseCoordinates.cornerMap, comp_apply,
      TransverseCoordinates.cornerLinear_apply, smul_eq_zero, hu, hv, or_false] using him
  · intro s hs
    have haxis : (s • u, 0) ∈ Φ.source := by
      change L (s, 0) ∈ Φ.source at hs
      simpa only [L, TransverseCoordinates.cornerLinear_apply, zero_smul] using hs
    simpa only [k, TransverseCoordinates.cornerMap, comp_apply,
      TransverseCoordinates.cornerLinear_apply, zero_smul] using hleft (s • u) haxis
  · intro t ht
    have haxis : (0, t • v) ∈ Φ.source := by
      change L (0, t) ∈ Φ.source at ht
      simpa only [L, TransverseCoordinates.cornerLinear_apply, zero_smul] using ht
    simpa only [k, TransverseCoordinates.cornerMap, comp_apply,
      TransverseCoordinates.cornerLinear_apply, zero_smul] using hright (t • v) haxis

end Wikipedia.SmoothSixDPoincare
