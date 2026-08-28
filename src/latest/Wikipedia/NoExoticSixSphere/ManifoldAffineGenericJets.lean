import Wikipedia.NoExoticSixSphere.ManifoldAffineChartDomain
import Wikipedia.NoExoticSixSphere.GenericThreeSixSubmersion

/-!
# Almost-everywhere regular spatial jets on genuine manifold chart domains

Joint chart-coordinate smoothness gives smoothness of the actual spatial jet.
Its proved parameter submersion implies a full derivative submersion, so the
general operator theorem applies on the actual coupled open domain.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)

def chartJet (s : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × Vector 3)) : Vector 3 →L[ℝ] Vector n :=
  fderiv ℝ (fun x ↦ chartCoordinates e r f s c (q.1, q.2.1, x)) q.2.2

theorem contDiffOn_chartJet
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (s : SourceChart) (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (chartJet e r f s c) (chartDomain e r f hf s c) := by
  intro q hq
  have hF := (contDiffOn_chartCoordinates e r f hf s c).contDiffAt
    ((chartDomain e r f hf s c).isOpen.mem_nhds hq)
  have hLift : ContDiff ℝ ∞
      (fun z : (Parameters e × (ℝ × Vector 3)) × Vector 3 ↦ (z.1.1, z.1.2.1, z.2)) := by
    fun_prop
  have hH := hF.comp (q, q.2.2) hLift.contDiffAt
  have hJ : ContDiffAt ℝ ∞ (chartJet e r f s c) q :=
    hH.fderiv (contDiff_snd.comp contDiff_snd).contDiffAt (by simp)
  exact hJ.contDiffWithinAt

theorem surjective_fderiv_chartJet
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (s : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × Vector 3)) (hq : q ∈ chartDomain e r f hf s c) :
    Surjective (fderiv ℝ (chartJet e r f s c) q) := by
  have hp : Surjective (fderiv ℝ (fun p : Parameters e ↦ chartJet e r f s c (p, q.2)) q.1) :=
    surjective_fderiv_chart_spatial_parameter e r f hf s c q.1 q.2.1 q.2.2
      hq.1.1.2 hq.1.1.1 hq.1.2 hq.2
  have hJ := ((contDiffOn_chartJet e r f hf s c).contDiffAt
    ((chartDomain e r f hf s c).isOpen.mem_nhds hq)).differentiableAt (by simp)
  have ht : HasFDerivAt (fun p : Parameters e ↦ (p, q.2))
      (ContinuousLinearMap.inl ℝ (Parameters e) (ℝ × Vector 3)) q.1 :=
    (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
  have he := (hJ.hasFDerivAt.comp q.1 ht).fderiv
  change fderiv ℝ (fun p : Parameters e ↦ chartJet e r f s c (p, q.2)) q.1 = _ at he
  rw [he] at hp
  intro L
  obtain ⟨v, hv⟩ := hp L
  exact ⟨(v, 0), hv⟩

theorem ae_regular_chart_jets [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
    (hn : n = 6) (s : SourceChart) (c : TargetChart n M) :
    ∀ᵐ p ∂μ, OperatorRank.RegularThreeSixOn
      (fun z : ℝ × Vector 3 ↦ chartJet e r f s c (p, z))
      {z | (p, z) ∈ chartDomain e r f hf s c} :=
  OperatorRank.ae_regular_three_six_of_submersion μ (chartJet e r f s c)
    (chartDomain e r f hf s c) (contDiffOn_chartJet e r f hf s c)
    (surjective_fderiv_chartJet e r f hf s c)
    (by simp [GLOrthonormalization.Vector]) (by simp [GLOrthonormalization.Vector])
    (by simp [GLOrthonormalization.Vector, hn])

end NoExoticSixSphere.ManifoldAffineSphereFamily
