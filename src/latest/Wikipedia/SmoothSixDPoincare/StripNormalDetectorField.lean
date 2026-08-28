import Wikipedia.SmoothSixDPoincare.StripChartComplement

/-!
# A fixed native normal map in the actual tubular coordinates

Along a retained strip chart, a smooth normal map on the original manifold
has a smooth ordinary differential in the tube chart. If the original map
is a submersion and vanishes on the sheet, these actual coordinate
differentials are surjective and annihilate the retained sheet tangent map.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.StripNormalData

variable {A B Z E M N : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup N] [NormedSpace ℝ N]
  [TopologicalSpace M] [ChartedSpace E M]
  {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)
  (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞)
  (q : M → N)

/-- The original normal map's actual differential in the inverse tube coordinates. -/
def normalDetector (t : ℝ) : ((ℝ × ℝ) × Z) →L[ℝ] N :=
  fderiv ℝ (q ∘ Ψ) (Ψ.symm (d.chart (StripCoordinates.center t)))

theorem contDiffAt_normalMap_in_tube {t : ℝ}
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (StripCoordinates.center t))) :
    ContDiffAt ℝ ∞ (q ∘ Ψ) (Ψ.symm (d.chart (StripCoordinates.center t))) := by
  have hinv : Ψ (Ψ.symm (d.chart (StripCoordinates.center t))) =
      d.chart (StripCoordinates.center t) := Ψ.right_inv' htarget
  have hq' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q
      (Ψ (Ψ.symm (d.chart (StripCoordinates.center t)))) := hinv.symm ▸ hq
  exact (hq'.comp _ (Ψ.contMDiffOn_toFun.contMDiffAt
    (Ψ.open_source.mem_nhds (Ψ.map_target' htarget)))).contDiffAt

theorem contDiffOn_normalDetector {O : Set M} (hO : IsOpen O)
    (hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q O)
    (htarget : ∀ t ∈ Icc (0 : ℝ) 1, d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hcenter : ∀ t ∈ Icc (0 : ℝ) 1, d.chart (StripCoordinates.center t) ∈ O) :
    ContDiffOn ℝ ∞ (d.normalDetector Ψ q) (Icc (0 : ℝ) 1) := by
  intro t ht
  have hqΨ := d.contDiffAt_normalMap_in_tube Ψ q (htarget t ht)
    (hq.contMDiffAt (hO.mem_nhds (hcenter t ht)))
  have hc : ContDiff ℝ ∞ (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (contDiff_id.prodMk contDiff_const).prodMk contDiff_const
  have hx : ContDiffAt ℝ ∞ (fun s => Ψ.symm (d.chart (StripCoordinates.center s))) t :=
    (d.contDiffAt_tubularTransition Ψ ht (htarget t ht)).comp t hc.contDiffAt
  exact ((hqΨ.fderiv_right (by simp)).comp t hx).contDiffWithinAt

theorem normalDetector_eq_native {t : ℝ}
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (StripCoordinates.center t))) :
    d.normalDetector Ψ q t =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) q (d.chart (StripCoordinates.center t)) : E →L[ℝ] N).comp
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) Ψ
          (Ψ.symm (d.chart (StripCoordinates.center t))) : ((ℝ × ℝ) × Z) →L[ℝ] E) := by
  have hinv : Ψ (Ψ.symm (d.chart (StripCoordinates.center t))) =
      d.chart (StripCoordinates.center t) := Ψ.right_inv' htarget
  have hq' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, N) q
      (Ψ (Ψ.symm (d.chart (StripCoordinates.center t)))) :=
    hinv.symm ▸ hq.mdifferentiableAt (by simp)
  unfold normalDetector
  rw [← mfderiv_eq_fderiv, mfderiv_comp _ hq'
    (Ψ.mdifferentiableAt (by simp) (Ψ.map_target' htarget)), hinv]

theorem surjective_normalDetector {t : ℝ}
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (StripCoordinates.center t)))
    (hqs : Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) q
      (d.chart (StripCoordinates.center t)))) : Surjective (d.normalDetector Ψ q t) := by
  rw [d.normalDetector_eq_native Ψ q htarget hq]
  exact hqs.comp (PartialChart.bijective_mfderiv Ψ (Ψ.map_target' htarget)).surjective

/-- Vanishing of the original normal map on the sheet kills its actual retained tangent columns. -/
theorem normalDetector_comp_sheet_eq_zero {O : Set M} (hO : IsOpen O)
    (hq : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q O)
    (hzero : ∀ y ∈ S ∩ O, q y = 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hcenter : d.chart (StripCoordinates.center t) ∈ O) :
    (d.normalDetector Ψ q t).comp (d.sheetDifferential Ψ t) = 0 := by
  let i := ContinuousLinearMap.inl ℝ (ℝ × A) B
  have hi : ContinuousAt i (t, 0) := i.continuous.continuousAt
  have hdc : ContinuousAt d.chart (i (t, 0)) :=
    d.chart.contMDiffOn_toFun.continuousOn.continuousAt
      (d.chart.open_source.mem_nhds (d.line ht))
  have hd : ContinuousAt (d.chart ∘ i) (t, 0) :=
    ContinuousAt.comp (g := d.chart) (f := i) hdc hi
  have hnearS : ∀ᶠ w : ℝ × A in 𝓝 (t, 0), i w ∈ d.chart.source :=
    hi.preimage_mem_nhds (d.chart.open_source.mem_nhds (d.line ht))
  have hnear : ∀ᶠ w : ℝ × A in 𝓝 (t, 0), d.chart (i w) ∈ Ψ.target ∩ O :=
    hd.preimage_mem_nhds ((Ψ.open_target.inter hO).mem_nhds ⟨htarget, hcenter⟩)
  have hvanish : ((q ∘ Ψ) ∘ d.sheetTransition Ψ) =ᶠ[𝓝 (t, (0 : A))] (fun _ => 0) := by
    filter_upwards [hnearS, hnear] with w hw hwo
    change q (Ψ (Ψ.symm (d.chart (i w)))) = 0
    have hinv : Ψ (Ψ.symm (d.chart (i w))) = d.chart (i w) := Ψ.right_inv' hwo.1
    rw [hinv]
    exact hzero _ ⟨(d.sheet _ hw).mpr rfl, hwo.2⟩
  have hqΨ := d.contDiffAt_normalMap_in_tube Ψ q htarget
    (hq.contMDiffAt (hO.mem_nhds hcenter))
  have hsheet := d.contDiffAt_sheetTransition Ψ ht htarget
  have hchain := fderiv_comp (t, (0 : A)) (hqΨ.differentiableAt (by simp))
    (hsheet.differentiableAt (by simp))
  have hder : fderiv ℝ ((q ∘ Ψ) ∘ d.sheetTransition Ψ) (t, (0 : A)) = 0 := by
    rw [hvanish.fderiv_eq]
    exact (hasFDerivAt_const (𝕜 := ℝ) (0 : N) (t, (0 : A))).fderiv
  exact hchain.symm.trans hder

/-- The normal detector on the retained tangent columns is the derivative in that sheet chart. -/
theorem normalDetector_comp_sheet {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (htarget : d.chart (StripCoordinates.center t) ∈ Ψ.target)
    (hq : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ q (d.chart (StripCoordinates.center t))) :
    (d.normalDetector Ψ q t).comp (d.sheetDifferential Ψ t) =
      fderiv ℝ (fun w : ℝ × A => q (d.chart (w, 0))) (t, 0) := by
  let i := ContinuousLinearMap.inl ℝ (ℝ × A) B
  have hi : ContinuousAt i (t, 0) := i.continuous.continuousAt
  have hdc : ContinuousAt d.chart (i (t, 0)) :=
    d.chart.contMDiffOn_toFun.continuousOn.continuousAt
      (d.chart.open_source.mem_nhds (d.line ht))
  have hd : ContinuousAt (d.chart ∘ i) (t, 0) :=
    ContinuousAt.comp (g := d.chart) (f := i) hdc hi
  have hnear : ∀ᶠ w : ℝ × A in 𝓝 (t, 0), d.chart (i w) ∈ Ψ.target :=
    hd.preimage_mem_nhds (Ψ.open_target.mem_nhds htarget)
  have heq : ((q ∘ Ψ) ∘ d.sheetTransition Ψ) =ᶠ[𝓝 (t, (0 : A))]
      (fun w : ℝ × A => q (d.chart (w, 0))) := by
    filter_upwards [hnear] with w hw
    exact congrArg q (Ψ.right_inv' hw)
  have hqΨ := d.contDiffAt_normalMap_in_tube Ψ q htarget hq
  have hsheet := d.contDiffAt_sheetTransition Ψ ht htarget
  have hchain := fderiv_comp (t, (0 : A)) (hqΨ.differentiableAt (by simp))
    (hsheet.differentiableAt (by simp))
  exact hchain.symm.trans heq.fderiv_eq

end Wikipedia.SmoothSixDPoincare.StripNormalData
