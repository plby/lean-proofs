import Wikipedia.NoExoticSixSphere.ManifoldAffineSingularities
import Wikipedia.NoExoticSixSphere.LocalOperatorContribution
import Wikipedia.NoExoticSixSphere.SphereChartBall

/-!
# Local parity-one balls for intrinsic singularities of the manifold family

The parameter ball is embedded in time times the original three-sphere.
It stays inside genuine source and target chart domains and contains exactly
the selected intrinsic singularity. Its linking-sphere operators are the actual
chart derivatives of the perturbed manifold family and have parity one.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization EuclideanEmbedding SphereFamily GenericLocalParity Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (p : Parameters e) (S : Set SourceChart) (C : Set (TargetChart 6 M))
  (hgen : GenericInCharts e r f hf S C p)

include hgen

theorem hasLocalContributionOn_chartJet (s : SourceChart) (hs : s ∈ S)
    (c : TargetChart 6 M) (hc : c ∈ C) (q : ℝ × Vector 3)
    (hq : (p, q) ∈ chartDomain e r f hf s c)
    (hJ : ¬ Injective (chartJet e r f s c (p, q))) :
    HasLocalContributionOn (fun z : ℝ × Vector 3 ↦ chartJet e r f s c (p, z))
      {z | (p, z) ∈ chartDomain e r f hf s c} q := by
  apply hasLocalContributionOn_of_regular_residual _
    ((chartDomain e r f hf s c).isOpen.preimage (continuous_const.prodMk continuous_id))
    ((contDiffOn_chartJet e r f hf s c).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz ↦ hz)) q hq
  exact (hgen.1 s hs c hc).residual_regular q hq hJ

theorem exists_local_contribution_at_intrinsic_singularity
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry (map e r f p)))
    (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (hp : ∀ t x, ambient e f p t x ∈ r.domain)
    (q : ℝ × Sphere 3) (ht : q.1 ∈ Ioo (0 : ℝ) 1)
    (hq : q ∈ singularParameters (n := 6) (map e r f p)) :
    ∃ s ∈ S, ∃ c ∈ C, ∃ b : Vector 4 → ℝ × Vector 3,
      MapsTo b (closedBall (0 : Vector 4) 1)
        {z | (p, z) ∈ chartDomain e r f hf s c} ∧
      liftChartBall s b 0 = q ∧
      ContMDiffOn (𝓡 4) (𝓘(ℝ, ℝ).prod (𝓡 3)) ∞ (liftChartBall s b)
        (closedBall (0 : Vector 4) 1) ∧
      IsClosedEmbedding (fun z : closedBall (0 : Vector 4) 1 ↦ liftChartBall s b z.val) ∧
      (∀ z ∈ closedBall (0 : Vector 4) 1,
        liftChartBall s b z ∈ singularParameters (n := 6) (map e r f p) ↔ z = 0) ∧
      ∃ L : C(Sphere 3, Monomorphism.Space 6 3),
        (∀ v, (L v).val = chartJet e r f s c (p, b v.val)) ∧
        Monomorphism.sphereParity 1 L = 1 := by
  obtain ⟨s, hs, hqs⟩ := hS q.2
  obtain ⟨c, hc, hqc⟩ := hC (map e r f p q.1 q.2)
  have hleft : s.symm (s q.2) = q.2 := s.left_inv hqs
  have hqU : (p, q.1, s q.2) ∈ chartDomain e r f hf s c := by
    change ((s q.2 ∈ s.target ∧ q.1 ∈ Ioo (0 : ℝ) 1) ∧
      ambient e f p q.1 (s.symm (s q.2)) ∈ r.domain) ∧
        map e r f p q.1 (s.symm (s q.2)) ∈ c.source
    rw [hleft]
    exact ⟨⟨⟨s.map_source hqs, ht⟩, hp _ _⟩, hqc⟩
  have hJ : ¬ Injective (chartJet e r f s c (p, q.1, s q.2)) := by
    have h := injective_chartJet_iff e r f hf p hg s c (q.1, s q.2) hqU
    rw [hleft] at h
    exact h.not.mpr hq
  obtain ⟨b, hb0, hbU, hbs, hbe, hsing, L, hL, hparity⟩ :=
    hasLocalContributionOn_chartJet e r f hf p S C hgen s hs c hc (q.1, s q.2) hqU hJ
  have htarget : ∀ z ∈ closedBall (0 : Vector 4) 1, (b z).2 ∈ s.target :=
    fun _ hz ↦ (hbU hz).1.1.1
  refine ⟨s, hs, c, hc, b, hbU, liftChartBall_center s b q hqs hb0,
    contMDiffOn_liftChartBall s b hbs htarget,
    isClosedEmbedding_liftChartBall s b hbs htarget hbe, ?_, L, hL, hparity⟩
  intro z hz
  have hiff := injective_chartJet_iff e r f hf p hg s c (b z) (hbU hz)
  exact hiff.not.symm.trans (hsing z hz)

end NoExoticSixSphere.ManifoldAffineSphereFamily
