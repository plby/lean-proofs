import Wikipedia.NoExoticSixSphere.SphereThreeChartFrameCoordinates
import Wikipedia.NoExoticSixSphere.ManifoldNormalChartCoordinates
import Wikipedia.NoExoticSixSphere.ManifoldChartLinkParity

/-!
# The actual global spatial derivative in local source and target coordinates

The target-coordinate factorization is proved as an equality of germs on
the valid chart domains. The quaternionic source-coordinate comparison then
gives the exact operator identity, including at a singular point of the family.
-/

noncomputable section

open Set Function Filter Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization ManifoldAffineSphereFamily SphereThreeTangentFrame

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)

theorem fderiv_embedding_in_charts (f : Sphere 3 → M)
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (s : SourceChart) (c : TargetChart 6 M)
    (x : s.source) (hx : f x.val ∈ c.source) :
    fderiv ℝ ((e.toFun ∘ f) ∘ s.symm) (s x.val) =
      (e.chartEmbeddingDerivative c ⟨f x.val, hx⟩).comp
        (fderiv ℝ (fun z ↦ c (f (s.symm z))) (s x.val)) := by
  let G : Vector 3 → M := f ∘ s.symm
  let F : Vector 3 → Vector 6 := c ∘ G
  let H : Vector 6 → Vector e.ambientDimension := e.toFun ∘ c.symm
  have hs : s.symm (s x.val) = x.val := s.left_inv x.property
  have hI : MDifferentiableAt (𝓡 3) (𝓡 3) s.symm (s x.val) :=
    (s.contMDiffOn_invFun.contMDiffAt
      (s.open_target.mem_nhds (s.map_source x.property))).mdifferentiableAt (by simp)
  have hfS : MDifferentiableAt (𝓡 3) (𝓡 6) f (s.symm (s x.val)) :=
    hf.mdifferentiableAt (by simp)
  have hG : MDifferentiableAt (𝓡 3) (𝓡 6) G (s x.val) := hfS.comp _ hI
  have hF0 : F (s x.val) = c (f x.val) := by change c (f (s.symm (s x.val))) = _; rw [hs]
  have hc : MDifferentiableAt (𝓡 6) (𝓡 6) c (G (s x.val)) := by
    change MDifferentiableAt (𝓡 6) (𝓡 6) c (f (s.symm (s x.val)))
    rw [hs]
    exact (c.contMDiffOn_toFun.contMDiffAt
      (c.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
  have hF : DifferentiableAt ℝ F (s x.val) := (hc.comp _ hG).differentiableAt
  have hH : DifferentiableAt ℝ H (c (f x.val)) :=
    (e.smooth.contMDiffAt.comp _ (c.contMDiffOn_invFun.contMDiffAt
      (c.open_target.mem_nhds (c.map_source hx)))).contDiffAt.differentiableAt (by simp)
  have hNc : ∀ᶠ z in 𝓝 (s x.val), G z ∈ c.source := by
    apply hG.continuousAt.preimage_mem_nhds
    apply c.open_source.mem_nhds
    change f (s.symm (s x.val)) ∈ c.source
    rwa [hs]
  have he : e.toFun ∘ G =ᶠ[𝓝 (s x.val)] H ∘ F := by
    filter_upwards [hNc] with z hz
    change e.toFun (G z) = e.toFun (c.symm (c (G z)))
    exact congrArg e.toFun (c.left_inv hz).symm
  have hHF : DifferentiableAt ℝ H (F (s x.val)) := by rw [hF0]; exact hH
  change fderiv ℝ (e.toFun ∘ G) (s x.val) = _
  rw [he.fderiv_eq, fderiv_comp _ hHF hF, hF0]
  rfl

theorem framedDerivative_embedding_in_charts (f : Sphere 3 → M)
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f) (s : SourceChart) (c : TargetChart 6 M)
    (x : s.source) (hx : f x.val ∈ c.source) :
    framedDerivative (e.toFun ∘ f) x.val =
      (e.chartEmbeddingDerivative c ⟨f x.val, hx⟩).comp
        ((fderiv ℝ (fun z ↦ c (f (s.symm z))) (s x.val)).comp
          (chartCoordinates s x).symm.toContinuousLinearMap) := by
  rw [framedDerivative_in_chart s _ (e.smooth.comp hf),
    e.fderiv_embedding_in_charts f hf s c x hx, ContinuousLinearMap.comp_assoc]

theorem familyTangentOperator_in_charts (g : ℝ → Sphere 3 → M)
    (hg : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))
    (s : SourceChart) (c : TargetChart 6 M) (p : ℝ × Sphere 3)
    (hs : p.2 ∈ s.source) (hc : g p.1 p.2 ∈ c.source) :
    e.familyTangentOperator g p =
      (e.chartEmbeddingDerivative c ⟨g p.1 p.2, hc⟩).comp
        ((SphereFamily.spatialInCharts g s c p).comp
          (chartCoordinates s ⟨p.2, hs⟩).symm.toContinuousLinearMap) :=
  e.framedDerivative_embedding_in_charts (g p.1)
    (hg.comp (contMDiff_const.prodMk contMDiff_id)) s c ⟨p.2, hs⟩ hc

end NoExoticSixSphere.EuclideanEmbedding
