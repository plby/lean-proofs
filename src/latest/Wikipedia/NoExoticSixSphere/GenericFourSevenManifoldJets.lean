import Wikipedia.NoExoticSixSphere.CompactRetractionAffineFamily
import Wikipedia.NoExoticSixSphere.GenericFourSevenOperators

/-!
# Generic four-disk jets in the original seven-manifold charts

These are derivatives of the actual protected, retracted affine maps, not
independently chosen operators. One parameter is regular in every chart of
any specified countable collection. The conclusions apply only on the
actual coupled domains, where the cutoff is nonzero and the retraction and
target chart are valid. Double-point regularity and parity are not asserted.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CompactRetractionAffineFamily

open GLOrthonormalization EuclideanEmbedding

variable {d n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) {K : Set M} (r : e.RetractionNear K)
  (f : Vector d → M) (χ : Vector d → ℝ)

def chartJet (c : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)
    (q : Parameters d e × Vector d) : Vector d →L[ℝ] Vector n :=
  fderiv ℝ (fun x ↦ chartCoordinates e r f χ c (q.1, x)) q.2

variable (U : TopologicalSpace.Opens (Vector d))
  (hf : ContMDiffOn (𝓡 d) (𝓡 n) ∞ f U) (hχ : ContDiff ℝ ∞ χ)
  (c : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)

theorem contDiffOn_chartJet : ContDiffOn ℝ ∞ (chartJet e r f χ c)
    (chartDomain e r f χ U hf hχ c) := by
  intro q hq
  have hF := (contDiffOn_chartCoordinates e r f χ U hf hχ c).contDiffAt
    ((chartDomain e r f χ U hf hχ c).isOpen.mem_nhds hq)
  have hLift : ContDiff ℝ ∞
      (fun z : (Parameters d e × Vector d) × Vector d ↦ (z.1.1, z.2)) := by
    fun_prop
  have hH := hF.comp (q, q.2) hLift.contDiffAt
  have hJ : ContDiffAt ℝ ∞ (chartJet e r f χ c) q :=
    hH.fderiv contDiff_snd.contDiffAt (by simp)
  exact hJ.contDiffWithinAt

theorem surjective_fderiv_chartJet (q : Parameters d e × Vector d)
    (hq : q ∈ activeChartDomain e r f χ U hf hχ c) :
    Surjective (fderiv ℝ (chartJet e r f χ c) q) := by
  have hp : Surjective (fderiv ℝ
      (fun p : Parameters d e ↦ chartJet e r f χ c (p, q.2)) q.1) :=
    surjective_fderiv_chart_spatial_parameter e r f χ U hf hχ c q.1 q.2
      hq.1.1.1 hq.2 hq.1.1.2 hq.1.2
  have hJ := ((contDiffOn_chartJet e r f χ U hf hχ c).contDiffAt
    ((chartDomain e r f χ U hf hχ c).isOpen.mem_nhds hq.1)).differentiableAt (by simp)
  have ht : HasFDerivAt (fun p : Parameters d e ↦ (p, q.2))
      (ContinuousLinearMap.inl ℝ (Parameters d e) (Vector d)) q.1 :=
    (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
  have he := (hJ.hasFDerivAt.comp q.1 ht).fderiv
  change fderiv ℝ (fun p : Parameters d e ↦ chartJet e r f χ c (p, q.2)) q.1 = _ at he
  rw [he] at hp
  intro L
  obtain ⟨v, hv⟩ := hp L
  exact ⟨(v, 0), hv⟩

theorem ae_regular_chart_jets [MeasurableSpace (Parameters d e)]
    [BorelSpace (Parameters d e)] (μ : Measure (Parameters d e)) [IsAddHaarMeasure μ]
    (hd : d = 4) (hn : n = 7) :
    ∀ᵐ p ∂μ, OperatorRank.RegularFourSevenOn
      (fun x ↦ chartJet e r f χ c (p, x))
      {x | (p, x) ∈ activeChartDomain e r f χ U hf hχ c} :=
  OperatorRank.ae_regular_four_seven_of_submersion μ (chartJet e r f χ c)
    (activeChartDomain e r f χ U hf hχ c)
    ((contDiffOn_chartJet e r f χ U hf hχ c).mono inter_subset_left)
    (surjective_fderiv_chartJet e r f χ U hf hχ c)
    (by simp [GLOrthonormalization.Vector, hd])
    (by simp [GLOrthonormalization.Vector, hd]) (by simp [GLOrthonormalization.Vector, hn])

theorem ae_regular_in_charts [MeasurableSpace (Parameters d e)]
    [BorelSpace (Parameters d e)] (μ : Measure (Parameters d e)) [IsAddHaarMeasure μ]
    (hd : d = 4) (hn : n = 7)
    (C : Set (PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)) (hC : C.Countable) :
    ∀ᵐ p ∂μ, ∀ c ∈ C, OperatorRank.RegularFourSevenOn
      (fun x ↦ chartJet e r f χ c (p, x))
      {x | (p, x) ∈ activeChartDomain e r f χ U hf hχ c} := by
  let : Countable C := hC.to_subtype
  have ha : ∀ᵐ p ∂μ, ∀ c : C, OperatorRank.RegularFourSevenOn
      (fun x ↦ chartJet e r f χ c.val (p, x))
      {x | (p, x) ∈ activeChartDomain e r f χ U hf hχ c.val} :=
    ae_all_iff.mpr fun c ↦ ae_regular_chart_jets e r f χ U hf hχ c.val μ hd hn
  exact ha.mono fun p hp c hc ↦ hp ⟨c, hc⟩

end NoExoticSixSphere.CompactRetractionAffineFamily
