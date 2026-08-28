import Wikipedia.NoExoticSixSphere.CompactRetractionPairSubmersion

/-!
# Coupled domains for actual protected disk double points

Both distinct source points lie in the original source region, their
perturbed images lie in the original tubular domain and one common target
chart, and at least one cutoff is nonzero. The coordinate-difference zeros
are exactly the actual image coincidences on this domain.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CompactRetractionAffineFamily

open GLOrthonormalization EuclideanEmbedding

variable {d n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) {K : Set M} (r : e.RetractionNear K)
  (f : Vector d → M) (χ : Vector d → ℝ)

def pairLeft (q : Parameters d e × (Vector d × Vector d)) : Parameters d e × Vector d :=
  (q.1, q.2.1)

def pairRight (q : Parameters d e × (Vector d × Vector d)) : Parameters d e × Vector d :=
  (q.1, q.2.2)

theorem contDiff_pairLeft : ContDiff ℝ ∞ (pairLeft (d := d) e) :=
  contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)

theorem contDiff_pairRight : ContDiff ℝ ∞ (pairRight (d := d) e) :=
  contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)

variable (U : Opens (Vector d)) (hf : ContMDiffOn (𝓡 d) (𝓡 n) ∞ f U)
  (hχ : ContDiff ℝ ∞ χ) (c : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)

def pairDomain : Opens (Parameters d e × (Vector d × Vector d)) :=
  ⟨(pairLeft e ⁻¹' (chartDomain e r f χ U hf hχ c : Set _) ∩
      pairRight e ⁻¹' (chartDomain e r f χ U hf hχ c : Set _)) ∩
      {q | q.2.1 ≠ q.2.2},
    (((chartDomain e r f χ U hf hχ c).isOpen.preimage (contDiff_pairLeft e).continuous).inter
      ((chartDomain e r f χ U hf hχ c).isOpen.preimage
        (contDiff_pairRight e).continuous)).inter
      (isClosed_eq (continuous_fst.comp continuous_snd)
        (continuous_snd.comp continuous_snd)).isOpen_compl⟩

def activePairDomain : Opens (Parameters d e × (Vector d × Vector d)) :=
  ⟨(pairDomain e r f χ U hf hχ c : Set _) ∩ {q | χ q.2.1 ≠ 0 ∨ χ q.2.2 ≠ 0},
    (pairDomain e r f χ U hf hχ c).isOpen.inter
      ((isClosed_eq (hχ.continuous.comp (continuous_fst.comp continuous_snd))
        continuous_const).isOpen_compl.union
      (isClosed_eq (hχ.continuous.comp (continuous_snd.comp continuous_snd))
        continuous_const).isOpen_compl)⟩

def chartDifference (q : Parameters d e × (Vector d × Vector d)) : Vector n :=
  chartCoordinates e r f χ c (pairLeft e q) - chartCoordinates e r f χ c (pairRight e q)

theorem contDiffOn_chartDifference : ContDiffOn ℝ ∞ (chartDifference e r f χ c)
    (pairDomain e r f χ U hf hχ c) :=
  ((contDiffOn_chartCoordinates e r f χ U hf hχ c).comp (contDiff_pairLeft e).contDiffOn
    (fun _ hq ↦ hq.1.1)).sub
      ((contDiffOn_chartCoordinates e r f χ U hf hχ c).comp (contDiff_pairRight e).contDiffOn
        (fun _ hq ↦ hq.1.2))

theorem chartDifference_zero_iff (q : Parameters d e × (Vector d × Vector d))
    (hq : q ∈ pairDomain e r f χ U hf hχ c) :
    chartDifference e r f χ c q = 0 ↔ map e r f χ q.1 q.2.1 = map e r f χ q.1 q.2.2 := by
  change c (map e r f χ q.1 q.2.1) - c (map e r f χ q.1 q.2.2) = 0 ↔ _
  rw [sub_eq_zero]
  exact ⟨c.toPartialEquiv.injOn hq.1.1.2 hq.1.2.2, congrArg c⟩

end NoExoticSixSphere.CompactRetractionAffineFamily
