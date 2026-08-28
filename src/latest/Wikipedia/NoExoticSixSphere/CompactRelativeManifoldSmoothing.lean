import Wikipedia.NoExoticSixSphere.CompactTubularRetraction
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Relative smoothing near a compact source without a compact target assumption

An actual embedded manifold-valued map on a compact source has a continuous
ambient extension. Relative approximation of that extension, followed by the
constructed compact-image tubular retraction, gives a smooth manifold-valued
map near the source. Protected values stay fixed. A second compact source
region can be required to stay in a specified open part of the manifold.
-/

noncomputable section

open Set Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [Nonempty M]
  (e : EuclideanEmbedding n M)

theorem exists_smooth_near_compact_relative {K L S U : Set E}
    (hK : IsCompact K) (hL : IsCompact L) (hLK : L ⊆ K)
    (G : C(K, M)) (B : C(E, EuclideanSpace ℝ (Fin e.ambientDimension)))
    (hB : ∀ x : K, B x.val = e.toFun (G x))
    (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S) (hBs : ContDiffOn ℝ ∞ B U)
    (V : Set M) (hV : IsOpen V) (hGV : ∀ x : K, x.val ∈ L → G x ∈ V) :
    ∃ g : E → M,
      (∀ x ∈ K, ContMDiffAt 𝓘(ℝ, E) (𝓡 n) ∞ g x) ∧
      (∀ x : K, x.val ∈ S → g x.val = G x) ∧ ∀ x ∈ L, g x ∈ V := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨r⟩ := e.nonempty_retractionNear (isCompact_range G.continuous)
  have hbase (x : K) : G x ∈ r.base := r.covers ⟨x, rfl⟩
  have hBK : B '' K ⊆ r.domain := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hB ⟨x, hx⟩]
    exact r.contains ⟨G ⟨x, hx⟩, hbase ⟨x, hx⟩, rfl⟩
  obtain ⟨δ, hδ, hδU⟩ :=
    (hK.image B.continuous).exists_thickening_subset_open r.domain.isOpen hBK
  let W : Set (EuclideanSpace ℝ (Fin e.ambientDimension)) :=
    (r.domain : Set _) ∩ r.toFun ⁻¹' V
  have hW : IsOpen W :=
    r.smooth.continuousOn.isOpen_inter_preimage r.domain.isOpen hV
  have hBL : B '' L ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hBK ⟨x, hLK hx, rfl⟩, ?_⟩
    change r.toFun (B x) ∈ V
    rw [hB ⟨x, hLK hx⟩, r.fixes _ (hbase ⟨x, hLK hx⟩)]
    exact hGV ⟨x, hLK hx⟩ hx
  obtain ⟨ε, hε, hεW⟩ :=
    (hL.image B.continuous).exists_thickening_subset_open hW hBL
  obtain ⟨A, hAs, hAclose, hAeq, -⟩ := B.continuous.exists_contDiff_approx_and_eqOn
    (⊤ : ℕ∞) continuous_const (fun _ ↦ lt_min hδ hε) hS hU hBs
  have hAdomain (x : E) (hx : x ∈ K) : A x ∈ r.domain := by
    apply hδU
    exact mem_thickening_iff.mpr ⟨B x, ⟨x, hx, rfl⟩,
      (hAclose x).trans_le (min_le_left _ _)⟩
  refine ⟨r.toFun ∘ A, ?_, ?_, ?_⟩
  · intro x hx
    exact (r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds (hAdomain x hx))).comp x
      hAs.contMDiff.contMDiffAt
  · intro x hx
    change r.toFun (A x.val) = G x
    rw [hAeq hx, hB x, r.fixes _ (hbase x)]
  · intro x hx
    have hAW : A x ∈ W := hεW (mem_thickening_iff.mpr
      ⟨B x, ⟨x, hx, rfl⟩, (hAclose x).trans_le (min_le_right _ _)⟩)
    exact hAW.2

end NoExoticSixSphere.EuclideanEmbedding
