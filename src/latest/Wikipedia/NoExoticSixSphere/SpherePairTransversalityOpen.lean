import Wikipedia.NoExoticSixSphere.SpatialIntersectionNativeTransversality

/-!
# Openness of native spatial transversality along sphere coincidences

The spatial derivative of the actual chart difference varies continuously.
Its invertibility is open, and the exact chart factorization reflects its
surjectivity back to the original tangent maps at nearby coincidences.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.IntersectionTrace

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (f g : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))

def spatialDifferenceDerivative (s z : SphereChart) (c : ManifoldChart M)
    (q : PairModel) : (Vector 3 × Vector 3) →L[ℝ] Vector 6 :=
  fderiv ℝ (fun p ↦ coordinateDifference f g s z c (q.1, p)) q.2

include hf hg in
theorem contDiffOn_spatialDifferenceDerivative (s z : SphereChart) (c : ManifoldChart M) :
    ContDiffOn ℝ ∞ (spatialDifferenceDerivative f g s z c)
      (fullCoordinateDomain f g s z c) := by
  intro q hq
  have hF := (contDiffOn_coordinateDifference_full f g hf hg s z c).contDiffAt
    ((isOpen_fullCoordinateDomain f g hf hg s z c).mem_nhds hq)
  have hLift : ContDiff ℝ ∞
      (fun v : PairModel × (Vector 3 × Vector 3) ↦ (v.1.1, v.2)) := by fun_prop
  have hH := hF.comp (q, q.2) hLift.contDiffAt
  have hD : ContDiffAt ℝ ∞ (spatialDifferenceDerivative f g s z c) q :=
    hH.fderiv contDiff_snd.contDiffAt (by simp)
  exact hD.contDiffWithinAt

include hf hg in
theorem eventually_native_transverse_of_charts (a : ℝ × (Sphere 3 × Sphere 3))
    (s z : SphereChart) (c : ManifoldChart M)
    (hx : a.2.1 ∈ s.source) (hy : a.2.2 ∈ z.source) (hc : f a.1 a.2.1 ∈ c.source)
    (hxy : f a.1 a.2.1 = g a.1 a.2.2)
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) (f a.1) a.2.1).coprod
      (mfderiv (𝓡 3) (𝓡 6) (g a.1) a.2.2))) :
    ∀ᶠ b in 𝓝 a, f b.1 b.2.1 = g b.1 b.2.2 → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) (f b.1) b.2.1).coprod
        (mfderiv (𝓡 3) (𝓡 6) (g b.1) b.2.2)) := by
  let q : PairModel := (a.1, (s a.2.1, z a.2.2))
  let D := spatialDifferenceDerivative f g s z c
  have hs : s.symm (s a.2.1) = a.2.1 := s.left_inv hx
  have hz : z.symm (z a.2.2) = a.2.2 := z.left_inv hy
  have hq : q ∈ fullCoordinateDomain f g s z c := by
    change (s a.2.1 ∈ s.target ∧ z a.2.2 ∈ z.target) ∧
      (f a.1 (s.symm (s a.2.1)) ∈ c.source ∧
        g a.1 (z.symm (z a.2.2)) ∈ c.source)
    rw [hs, hz]
    exact ⟨⟨s.map_source hx, z.map_source hy⟩, hc, hxy ▸ hc⟩
  have hD : ContinuousAt D q :=
    ((contDiffOn_spatialDifferenceDerivative f g hf hg s z c).contDiffAt
      ((isOpen_fullCoordinateDomain f g hf hg s z c).mem_nhds hq)).continuousAt
  have hbij : Bijective (D q) := bijective_fderiv_spatial_difference
    f g hf hg a.1 a.2.1 a.2.2 s z c hx hy hc hxy ht
  have hopen : IsOpen {L : (Vector 3 × Vector 3) →L[ℝ] Vector 6 | L.IsInvertible} :=
    ContinuousLinearEquiv.isOpen
  have hinv : (D q).IsInvertible := ⟨ContinuousLinearEquiv.ofBijective (D q)
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2), rfl⟩
  have hnear : ∀ᶠ v in 𝓝 q, Surjective (D v) := by
    filter_upwards [hD (hopen.mem_nhds hinv)] with v hv
    obtain ⟨L, hL⟩ := hv
    rw [← hL]
    exact L.surjective
  let χ : ℝ × (Sphere 3 × Sphere 3) → PairModel :=
    fun b ↦ (b.1, (s b.2.1, z b.2.2))
  have hχ : ContinuousAt χ a := continuous_fst.continuousAt.prodMk
    (((s.contMDiffOn_toFun.continuousOn.continuousAt (s.open_source.mem_nhds hx)).comp
      (f := fun b : ℝ × (Sphere 3 × Sphere 3) ↦ b.2.1)
      continuous_snd.fst.continuousAt).prodMk
      ((z.contMDiffOn_toFun.continuousOn.continuousAt (z.open_source.mem_nhds hy)).comp
        (f := fun b : ℝ × (Sphere 3 × Sphere 3) ↦ b.2.2)
        continuous_snd.snd.continuousAt))
  have hcnear : ∀ᶠ b : ℝ × (Sphere 3 × Sphere 3) in 𝓝 a,
      f b.1 b.2.1 ∈ c.source :=
    (hf.continuous.comp (continuous_fst.prodMk continuous_snd.fst)).continuousAt
      (c.open_source.mem_nhds hc)
  filter_upwards [hχ hnear,
    continuous_snd.fst.continuousAt (s.open_source.mem_nhds hx),
    continuous_snd.snd.continuousAt (z.open_source.mem_nhds hy), hcnear] with b hb hbx hby hbc
  intro he
  exact native_transverse_of_spatial_regular f g hf hg b.1 b.2.1 b.2.2
    s z c hbx hby hbc he hb

include hf hg in
theorem eventually_native_transverse [IsManifold (𝓡 6) ∞ M]
    (a : ℝ × (Sphere 3 × Sphere 3))
    (hxy : f a.1 a.2.1 = g a.1 a.2.2)
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) (f a.1) a.2.1).coprod
      (mfderiv (𝓡 3) (𝓡 6) (g a.1) a.2.2))) :
    ∀ᶠ b in 𝓝 a, f b.1 b.2.1 = g b.1 b.2.2 → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) (f b.1) b.2.1).coprod
        (mfderiv (𝓡 3) (𝓡 6) (g b.1) b.2.2)) := by
  let s : SphereChart := modelChartPartialDiffeomorph (I := 𝓡 3) a.2.1
  let z : SphereChart := modelChartPartialDiffeomorph (I := 𝓡 3) a.2.2
  let c : ManifoldChart M := modelChartPartialDiffeomorph (I := 𝓡 6) (f a.1 a.2.1)
  exact eventually_native_transverse_of_charts f g hf hg a s z c
    (mem_extChartAt_source _) (mem_extChartAt_source _) (mem_extChartAt_source _) hxy ht

end NoExoticSixSphere.IntersectionTrace
