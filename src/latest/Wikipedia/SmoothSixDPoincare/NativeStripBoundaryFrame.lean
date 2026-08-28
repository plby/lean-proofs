import Wikipedia.SmoothSixDPoincare.StripCoordinateDifferential
import Wikipedia.SmoothSixDPoincare.TubularNormalKernel

/-!
# The actual sheet frame in tubular disk-normal coordinates

Differentiate the transition from the retained sheet chart to the genuine
tubular normal coordinate. The two chart directions complementary to the arc
then give a smooth full-rank field wherever the disk retains the strip germ.
This constructs a frame along one boundary arc; joining the two boundary
conditions still requires the Whitney intersection-sign argument.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.StripNormalData

variable {A B Z E M : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
  (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞)

/-- The actual transition derivative on the sheet directions complementary to its arc. -/
def normalFrame (t : ℝ) : A →L[ℝ] Z :=
  (fderiv ℝ (TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
    (StripCoordinates.center t)).comp StripCoordinates.sheetTransverseInclusion

/-- The ordinary transition derivative agrees with the composition of actual native derivatives. -/
theorem normalFrame_eq_native_comp {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    d.normalFrame Ψ t =
      ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Z) (TransverseCoordinates.normalCoordinate Ψ)
        (d.chart (StripCoordinates.center t))).comp
        (mfderiv 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) d.chart
          (StripCoordinates.center t))).comp StripCoordinates.sheetTransverseInclusion := by
  have hnormal := (TransverseCoordinates.contMDiffOn_normalCoordinate Ψ).contMDiffAt
    (Ψ.open_target.mem_nhds htarget)
  unfold normalFrame
  rw [← mfderiv_eq_fderiv, mfderiv_comp (StripCoordinates.center t)
    (hnormal.mdifferentiableAt (by simp)) (d.chart.mdifferentiableAt (by simp) (d.line ht))]
  rfl

/-- The transition and its derivative are smooth wherever both actual charts apply. -/
theorem contDiffOn_normalFrame :
    ContDiffOn ℝ ∞ (d.normalFrame Ψ)
      {t | StripCoordinates.center t ∈ d.chart.source ∧
        d.chart (StripCoordinates.center t) ∈ Ψ.target} := by
  intro t ht
  have hnormal := (TransverseCoordinates.contMDiffOn_normalCoordinate Ψ).contMDiffAt
    (Ψ.open_target.mem_nhds ht.2)
  have hchart := d.chart.contMDiffOn_toFun.contMDiffAt (d.chart.open_source.mem_nhds ht.1)
  have htransition : ContDiffAt ℝ ∞
      (TransverseCoordinates.normalCoordinate Ψ ∘ d.chart) (StripCoordinates.center t) :=
    (hnormal.comp (StripCoordinates.center t) hchart).contDiffAt
  have hcenter : ContDiff ℝ ∞ (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (contDiff_id.prodMk contDiff_const).prodMk contDiff_const
  exact (((htransition.fderiv_right (by simp)).comp t hcenter.contDiffAt).clm_comp
    contDiffAt_const).contDiffWithinAt

/-- The actual chart overlap gives an open interval neighborhood of smooth frame values. -/
theorem exists_open_normalFrame_domain
    (htarget : ∀ t ∈ Icc (0 : ℝ) 1, d.chart (StripCoordinates.center t) ∈ Ψ.target) :
    ∃ U : Set ℝ, IsOpen U ∧ Icc (0 : ℝ) 1 ⊆ U ∧
      ContDiffOn ℝ ∞ (d.normalFrame Ψ) U := by
  have hcenter : Continuous (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hW : IsOpen (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    d.chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage
      d.chart.open_source Ψ.open_target
  refine ⟨StripCoordinates.center ⁻¹' (d.chart.source ∩ d.chart ⁻¹' Ψ.target),
    hW.preimage hcenter, fun t ht => ⟨d.line ht, htarget t ht⟩, ?_⟩
  exact d.contDiffOn_normalFrame Ψ

/-- A preserved strip germ makes the actual tubular normal derivative annihilate its arc. -/
theorem normalDerivative_kills_arc_of_strip_germ {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0))
    {f : (ℝ × ℝ) → M} (hzero : ∀ x, Ψ (x, 0) = f x)
    {p : ℝ × ℝ} (hp : (p, 0) ∈ Ψ.source)
    {c : (ℝ × ℝ) → (ℝ × ℝ)} (hc : ContDiffAt ℝ ∞ c p)
    (hcp : c p = (t, 0)) (hcs : Surjective (fderiv ℝ c p))
    (hgerm : f =ᶠ[𝓝 p] k ∘ c) :
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Z) (TransverseCoordinates.normalCoordinate Ψ) (f p))
      ((mfderiv 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) d.chart
        (StripCoordinates.center t)) (StripCoordinates.center 1)) = 0 := by
  let Q : E →L[ℝ] Z :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Z) (TransverseCoordinates.normalCoordinate Ψ) (f p)
  let K : (ℝ × ℝ) →L[ℝ] E := mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k (t, 0)
  have hk' : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (c p) := by
    rw [hcp]
    exact hk
  have hker : Q.ker = K.range := by
    have heq := TransverseCoordinates.ker_normalDerivative_eq_range_of_germ Ψ hzero hp hc
      hk' hcs hgerm
    rw [hcp] at heq
    exact heq
  have hmem : K (1, 0) ∈ Q.ker := by
    rw [hker]
    exact ⟨(1, 0), rfl⟩
  have hhorizontal : K (1, 0) =
      (mfderiv 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) d.chart
        (StripCoordinates.center t)) (StripCoordinates.center 1) := by
    change (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k (t, 0)) (1, 0) = _
    rw [d.native_derivative_factor ht hk]
    change (mfderiv 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) d.chart
      (StripCoordinates.center t)) (fderiv ℝ d.coordinateMap (t, 0) (1, 0)) = _
    rw [d.horizontal_coordinateDerivative ht hk]
  change Q _ = 0
  rw [← hhorizontal]
  exact hmem

/-- A preserved full strip germ makes the actual tubular-normal sheet frame injective. -/
theorem injective_normalFrame_of_strip_germ {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0))
    {f : (ℝ × ℝ) → M} (hzero : ∀ x, Ψ (x, 0) = f x)
    {p : ℝ × ℝ} (hp : (p, 0) ∈ Ψ.source)
    {c : (ℝ × ℝ) → (ℝ × ℝ)} (hc : ContDiffAt ℝ ∞ c p)
    (hcp : c p = (t, 0)) (hcs : Surjective (fderiv ℝ c p))
    (hgerm : f =ᶠ[𝓝 p] k ∘ c) : Injective (d.normalFrame Ψ t) := by
  let T : StripCoordinates.Space A B →L[ℝ] E :=
    mfderiv 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) d.chart (StripCoordinates.center t)
  let L : (ℝ × ℝ) →L[ℝ] StripCoordinates.Space A B := fderiv ℝ d.coordinateMap (t, 0)
  let Q : E →L[ℝ] Z :=
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, Z) (TransverseCoordinates.normalCoordinate Ψ) (f p)
  let J : (ℝ × ℝ) →L[ℝ] E := mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p
  let K : (ℝ × ℝ) →L[ℝ] E := mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k (t, 0)
  have hfp : f p = d.chart (StripCoordinates.center t) := by
    have heq := hgerm.eq_of_nhds
    dsimp only [Function.comp_apply] at heq
    rw [hcp, d.center t] at heq
    exact heq
  have htarget : f p ∈ Ψ.target := by
    have h := Ψ.map_source' hp
    rwa [hzero p] at h
  have hk' : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (c p) := by
    rw [hcp]
    exact hk
  have hdf : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p =
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k (t, 0)).comp (fderiv ℝ c p) := by
    rw [hgerm.mfderiv_eq, mfderiv_comp p (hk'.mdifferentiableAt (by simp))
      (hc.contMDiffAt.mdifferentiableAt (by simp)), hcp, mfderiv_eq_fderiv]
    rfl
  have hker : Q.ker = (T.comp L).range := by
    have h1 : Q.ker = J.range :=
      TransverseCoordinates.ker_normalDerivative_eq_range_zero_section Ψ hzero hp
    have h2 : J.range = K.range := by
      change (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) f p).range = K.range
      rw [hdf]
      exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hcs)
    have h3 : K.range = (T.comp L).range := by
      change (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k (t, 0)).range = (T.comp L).range
      rw [d.native_derivative_factor ht hk]
      rfl
    exact h1.trans (h2.trans h3)
  have hT : Injective T := (PartialChart.bijective_mfderiv d.chart (d.line ht)).1
  have hinj : Injective ((Q.comp T).comp StripCoordinates.sheetTransverseInclusion) :=
    StripCoordinates.injective_sheetTransverse_normalQuotient L (Q.comp T)
      (d.horizontal_coordinateDerivative ht hk) (d.normal_coordinateDerivative_nonzero ht hk)
      (StripCoordinates.ker_comp_eq_range_of_injective T L Q hT hker)
  have hnormal := (TransverseCoordinates.contMDiffOn_normalCoordinate Ψ).contMDiffAt
    (Ψ.open_target.mem_nhds htarget)
  have hnormal' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, Z) ∞
      (TransverseCoordinates.normalCoordinate Ψ) (d.chart (StripCoordinates.center t)) := by
    rw [← hfp]
    exact hnormal
  have htransition : fderiv ℝ (TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
      (StripCoordinates.center t) = Q.comp T := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp (StripCoordinates.center t)
      (hnormal'.mdifferentiableAt (by simp)) (d.chart.mdifferentiableAt (by simp) (d.line ht))]
    rw [← hfp]
    rfl
  change Injective ((fderiv ℝ (TransverseCoordinates.normalCoordinate Ψ ∘ d.chart)
    (StripCoordinates.center t)).comp StripCoordinates.sheetTransverseInclusion)
  rw [htransition]
  exact hinj

end Wikipedia.SmoothSixDPoincare.StripNormalData
