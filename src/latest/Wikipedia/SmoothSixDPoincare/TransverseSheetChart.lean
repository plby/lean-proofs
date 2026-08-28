import Wikipedia.SmoothSixDPoincare.TransverseSheetCoordinates
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Simultaneous straightening at a transverse sheet intersection

For two smooth local maps whose dimensions add to the manifold dimension and
whose actual native tangent maps span the tangent space, construct one smooth
partial diffeomorphism taking the two coordinate axes exactly to the two maps.
The chart contains a positive-radius closed product and can be kept in any
given open target neighborhood. No local chart or corner model is an input.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.TransverseCoordinates

variable {D Z E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ E]

theorem isInvertible_coprod_of_surjective (F : D →L[ℝ] E) (G : Z →L[ℝ] E)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht : Surjective (F.coprod G)) : (F.coprod G).IsInvertible := by
  have hd : Module.finrank ℝ (D × Z) = Module.finrank ℝ E := by
    simpa only [Module.finrank_prod] using hdim
  have hi : Injective (F.coprod G) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mpr ht
  let L := (LinearEquiv.ofBijective (F.coprod G).toLinearMap ⟨hi, ht⟩).toContinuousLinearEquiv
  exact ⟨L, rfl⟩

end Wikipedia.SmoothSixDPoincare.TransverseCoordinates

namespace Wikipedia.SmoothSixDPoincare

variable {E M D Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- An actual native chart simultaneously straightens the two transverse local sheet maps. -/
theorem exists_simultaneous_sheetChart {f : D → M} {g : Z → M}
    {U : Set D} {V : Set Z} (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : D) ∈ U) (h0V : (0 : Z) ∈ V)
    (hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f U)
    (hg : ContMDiffOn 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ g V) (hzero : g 0 = f 0)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f 0).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) g 0)))
    {O : Set M} (hO : IsOpen O) (h0O : f 0 ∈ O) :
    ∃ a : ℝ, 0 < a ∧ ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (D × Z) M ∞,
      closedBall (0 : D) a ×ˢ closedBall (0 : Z) a ⊆ Φ.source ∧
      Φ.source ⊆ U ×ˢ V ∧ Φ.target ⊆ O ∧
      (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = f x) ∧
      (∀ z, (0, z) ∈ Φ.source → Φ (0, z) = g z) := by
  let : Nonempty M := ⟨f 0⟩
  obtain ⟨e⟩ := nonempty_nativeEuclideanEmbedding (E := E) (M := M)
  obtain ⟨r⟩ := e.nonempty_smoothRetraction
  let W₀ := r.sheetCoordinateDomain f g U V
  have hW₀ : IsOpen W₀ := r.isOpen_sheetCoordinateDomain hU hV hf hg
  have hs : ContMDiffOn 𝓘(ℝ, D × Z) 𝓘(ℝ, E) ∞ (r.sheetCoordinates f g) W₀ :=
    r.contMDiffOn_sheetCoordinates hf hg
  let W := W₀ ∩ r.sheetCoordinates f g ⁻¹' O
  have hW : IsOpen W := hs.continuousOn.isOpen_inter_preimage hW₀ hO
  have h0W : (0, 0) ∈ W := by
    refine ⟨r.zero_mem_sheetCoordinateDomain f g h0U h0V, ?_⟩
    change r.sheetCoordinates f g (0, 0) ∈ O
    rw [r.sheetCoordinates_left f g hzero]
    exact h0O
  have hinv : (mfderiv 𝓘(ℝ, D × Z) 𝓘(ℝ, E) (r.sheetCoordinates f g) (0, 0)).IsInvertible := by
    rw [r.mfderiv_sheetCoordinates_zero hzero (hf.contMDiffAt (hU.mem_nhds h0U))
      (hg.contMDiffAt (hV.mem_nhds h0V))]
    exact TransverseCoordinates.isInvertible_coprod_of_surjective
      (D := D) (Z := Z) (E := E) _ _ hdim ht
  obtain ⟨Φ, h0Φ, hΦW, heq⟩ := exists_partialDiffeomorph_into_manifold
    hW h0W (hs.mono inter_subset_left) hinv
  obtain ⟨a, ha, hball⟩ := nhds_basis_closedBall.mem_iff.mp (Φ.open_source.mem_nhds h0Φ)
  refine ⟨a, ha, Φ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [closedBall_prod_same]
    exact hball
  · intro q hq
    exact (hΦW hq).1.1
  · intro y hy
    have hq := Φ.map_target' hy
    have hmem := (hΦW hq).2
    change r.sheetCoordinates f g (Φ.invFun y) ∈ O at hmem
    rw [heq hq] at hmem
    exact (Φ.right_inv' hy) ▸ hmem
  · intro x hx
    exact (heq hx).symm.trans (r.sheetCoordinates_left f g hzero x)
  · intro z hz
    exact (heq hz).symm.trans (r.sheetCoordinates_right f g z)

end Wikipedia.SmoothSixDPoincare
