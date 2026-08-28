import Wikipedia.HopfProblem.OrbitPairNativeCenteredChart
import Wikipedia.HopfProblem.OrbitPairTrackNormalDerivative

/-!
# Derivatives of centered native coordinate germs

The centered source and target parametrizations have identity derivative.
Consequently an actual local coordinate expression has exactly the native
derivative at its center, rather than merely an isomorphic derivative.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeCenteredChart

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

theorem coordinate_germ_derivative {F : M → N} {q : M} {f : E → G}
    (hF : MDifferentiableAt I J F q) (hf : DifferentiableAt ℝ f 0)
    (hfzero : f 0 = 0)
    (he : F ∘ chart (I := I) q =ᶠ[𝓝 0] chart (I := J) (F q) ∘ f) :
    fderiv ℝ f 0 = (mfderiv I J F q : E →L[ℝ] G) := by
  let c := chart (I := I) q
  let Φ := chart (I := J) (F q)
  let A : E →L[ℝ] G := mfderiv I J F q
  let L : E →L[ℝ] G := mfderiv 𝓘(ℝ, E) J (F ∘ c) 0
  let R : E →L[ℝ] G := mfderiv 𝓘(ℝ, E) J (Φ ∘ f) 0
  have hc0 : c 0 = q := chart_zero q
  have hΦ0 : (0 : G) ∈ Φ.source := zero_mem_source (F q)
  have hc : MDifferentiableAt 𝓘(ℝ, E) I c 0 :=
    c.mdifferentiableAt (by simp) (zero_mem_source q)
  have hFc : MDifferentiableAt I J F (c 0) := hc0.symm ▸ hF
  have hL : L = A := by
    have hd := mfderiv_comp 0 hFc hc
    rw [hc0, mfderiv_chart_zero] at hd
    change L = A.comp (ContinuousLinearMap.id ℝ E) at hd
    simpa only [ContinuousLinearMap.comp_id] using hd
  have hΦf : MDifferentiableAt 𝓘(ℝ, G) J Φ (f 0) := by
    rw [hfzero]
    exact Φ.mdifferentiableAt (by simp) hΦ0
  have hR : R = fderiv ℝ f 0 := by
    have hd := mfderiv_comp 0 hΦf hf.mdifferentiableAt
    rw [hfzero, mfderiv_chart_zero, mfderiv_eq_fderiv] at hd
    change R = (ContinuousLinearMap.id ℝ G).comp (fderiv ℝ f 0) at hd
    simpa only [ContinuousLinearMap.id_comp] using hd
  have hLR : L = R := he.mfderiv_eq
  exact hR.symm.trans (hLR.symm.trans hL)

def coordinates (F : M → N) (q : M) : E → G :=
  (chart (I := J) (F q)).symm ∘ F ∘ chart (I := I) q

theorem coordinates_zero (F : M → N) (q : M) : coordinates (I := I) (J := J) F q 0 = 0 := by
  let Φ := chart (I := J) (F q)
  change Φ.symm (F (chart (I := I) q 0)) = 0
  rw [chart_zero]
  have hzero : Φ 0 = F q := chart_zero (F q)
  rw [← hzero]
  exact Φ.left_inv' (zero_mem_source (F q))

theorem coordinates_contDiffAt {F : M → N} (q : M)
    (hF : ContMDiffAt I J ∞ F q) : ContDiffAt ℝ ∞ (coordinates (I := I) (J := J) F q) 0 := by
  let c := chart (I := I) q
  let Φ := chart (I := J) (F q)
  have hct : ContMDiffAt 𝓘(ℝ, E) I ∞ c 0 :=
    c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds (zero_mem_source q))
  have hFc : ContMDiffAt 𝓘(ℝ, E) J ∞ (F ∘ c) 0 := by
    apply ContMDiffAt.comp 0 _ hct
    simpa only [c, chart_zero] using hF
  have hy : F q ∈ Φ.target := by
    have hh := Φ.map_source' (zero_mem_source (I := J) (F q))
    simpa only [Φ, chart_zero] using hh
  have hΦ : ContMDiffAt J 𝓘(ℝ, G) ∞ Φ.symm (F q) :=
    Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hy)
  have hs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, G) ∞ (coordinates (I := I) (J := J) F q) 0 := by
    apply ContMDiffAt.comp 0 _ hFc
    simpa only [comp_apply, c, chart_zero] using hΦ
  exact hs.contDiffAt

theorem coordinates_germ {F : M → N} (q : M) (hF : ContinuousAt F q) :
    F ∘ chart (I := I) q =ᶠ[𝓝 0]
      chart (I := J) (F q) ∘ coordinates (I := I) (J := J) F q := by
  let c := chart (I := I) q
  let Φ := chart (I := J) (F q)
  have hc : ContinuousAt c 0 :=
    c.contMDiffOn_toFun.continuousOn.continuousAt (c.open_source.mem_nhds (zero_mem_source q))
  have hFc : ContinuousAt (F ∘ c) 0 := by
    have hF' : ContinuousAt F (c 0) := by
      simpa only [c, chart_zero] using hF
    exact hF'.comp hc
  have hy : F (c 0) ∈ Φ.target := by
    have hh := Φ.map_source' (zero_mem_source (I := J) (F q))
    simpa only [Φ, c, chart_zero] using hh
  filter_upwards [hFc.preimage_mem_nhds (Φ.open_target.mem_nhds hy)] with u hu
  exact (Φ.right_inv' hu).symm

theorem fderiv_coordinates {F : M → N} (q : M) (hF : ContMDiffAt I J ∞ F q) :
    fderiv ℝ (coordinates (I := I) (J := J) F q) 0 =
      (mfderiv I J F q : E →L[ℝ] G) :=
  coordinate_germ_derivative (hF.mdifferentiableAt (by simp))
    ((coordinates_contDiffAt q hF).differentiableAt (by simp))
    (coordinates_zero F q) (coordinates_germ q hF.continuousAt)

end Wikipedia.HopfProblem.OrbitPair.NativeCenteredChart
