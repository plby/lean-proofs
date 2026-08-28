import Wikipedia.NoExoticSixSphere.ManifoldParityBall
import Wikipedia.NoExoticSixSphere.ManifoldAffineLocalContribution

/-!
# Arbitrarily small actual charted parity-one balls

The residual inverse-function chart is constructed inside the preimage of a
prescribed open neighborhood in the original parameter manifold. The resulting
partial diffeomorphism contains the whole closed unit ball in its source and
its linking operators are exactly the spatial derivatives in the chosen charts.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization EuclideanEmbedding SphereFamily GenericLocalParity Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (p : Parameters e)

theorem spatialInCharts_liftChartBall (s : SourceChart) (c : TargetChart 6 M)
    (b : Vector 4 → ℝ × Vector 3) (z : Vector 4) (hz : (b z).2 ∈ s.target) :
    spatialInCharts (map e r f p) s c (liftChartBall s b z) =
      chartJet e r f s c (p, b z) := by
  have he : s (s.symm (b z).2) = (b z).2 := s.right_inv hz
  change fderiv ℝ (fun y ↦ c (map e r f p (b z).1 (s.symm y)))
    (s (s.symm (b z).2)) = _
  rw [he]
  rfl

variable (S : Set SourceChart) (C : Set (TargetChart 6 M))
  (hgen : GenericInCharts e r f hf S C p)

include hgen in
theorem exists_parityBall_in_neighborhood
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry (map e r f p)))
    (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (hp : ∀ t x, ambient e f p t x ∈ r.domain)
    (q : ℝ × Sphere 3) (ht : q.1 ∈ Ioo (0 : ℝ) 1)
    (hq : q ∈ singularParameters (n := 6) (map e r f p))
    (N : Set (ℝ × Sphere 3)) (hN : IsOpen N) (hqN : q ∈ N) :
    ∃ B : ParityBall (map e r f p) q, B.closedRegion ⊆ N := by
  obtain ⟨s, hs, hqs⟩ := hS q.2
  obtain ⟨c, hc, hqc⟩ := hC (map e r f p q.1 q.2)
  have hleft : s.symm (s q.2) = q.2 := s.left_inv hqs
  let U : Set (ℝ × Vector 3) := {z | (p, z) ∈ chartDomain e r f hf s c}
  have hU : IsOpen U := (chartDomain e r f hf s c).isOpen.preimage
    (continuous_const.prodMk continuous_id)
  have hqU : (q.1, s q.2) ∈ U := by
    change ((s q.2 ∈ s.target ∧ q.1 ∈ Ioo (0 : ℝ) 1) ∧
      ambient e f p q.1 (s.symm (s q.2)) ∈ r.domain) ∧
        map e r f p q.1 (s.symm (s q.2)) ∈ c.source
    rw [hleft]
    exact ⟨⟨⟨s.map_source hqs, ht⟩, hp _ _⟩, hqc⟩
  have hJ : ¬ Injective (chartJet e r f s c (p, q.1, s q.2)) := by
    have h := injective_chartJet_iff e r f hf p hg s c (q.1, s q.2) hqU
    rw [hleft] at h
    exact h.not.mpr hq
  let V : Set (ℝ × Vector 3) := U ∩ (timeChart s).symm ⁻¹' N
  have hUV : U ⊆ (timeChart s).symm.source :=
    fun _ hz ↦ ⟨mem_univ _, hz.1.1.1⟩
  have hcont := (timeChart s).contMDiffOn_invFun.continuousOn.mono hUV
  have hV : IsOpen V := hcont.isOpen_inter_preimage hU hN
  have hqV : (q.1, s q.2) ∈ V := by
    refine ⟨hqU, ?_⟩
    change (q.1, s.symm (s q.2)) ∈ N
    rwa [hleft]
  have hD : ContDiffOn ℝ ∞
      (fun z : ℝ × Vector 3 ↦ chartJet e r f s c (p, z)) V :=
    ((contDiffOn_chartJet e r f hf s c).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hz ↦ hz)).mono
        inter_subset_left
  obtain ⟨b, hball, hb0, hbV, hsing, L, hL, hparity⟩ :=
    hasChartedLocalContributionOn_of_regular_residual _ hV hD (q.1, s q.2) hqV
      ((hgen.1 s hs c hc).residual_regular _ hqU hJ)
  have hbU : MapsTo b (closedBall (0 : Vector 4) 1) U :=
    fun _ hz ↦ (hbV hz).1
  have htarget : ∀ z ∈ closedBall (0 : Vector 4) 1, (b z).2 ∈ s.target :=
    fun _ hz ↦ (hbU hz).1.1.1
  let B : ParityBall (map e r f p) q := {
    sourceChart := s
    targetChart := c
    chart := liftBallChart s b
    ball_source := closedBall_subset_liftBallChart_source s b hball htarget
    center := liftChartBall_center s b q hqs hb0
    chart_valid := fun z hz ↦
      ⟨(hbU hz).1.1.2, s.map_target (htarget z hz), (hbU hz).2⟩
    singular_iff := fun z hz ↦
      (injective_chartJet_iff e r f hf p hg s c (b z) (hbU hz)).not.symm.trans
        (hsing z hz)
    link := L
    link_value := fun v ↦ (hL v).trans
      (spatialInCharts_liftChartBall e r f p s c b v.val
        (htarget v.val (sphere_subset_closedBall v.property))).symm
    parity_one := hparity }
  refine ⟨B, ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact (hbV hz).2

end NoExoticSixSphere.ManifoldAffineSphereFamily
