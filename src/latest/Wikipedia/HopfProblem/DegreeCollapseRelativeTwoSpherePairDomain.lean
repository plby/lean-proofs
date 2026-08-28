import Wikipedia.HopfProblem.DegreeCollapseRelativeTwoSphereChartDomain
import Wikipedia.HopfProblem.DegreeCollapseTwoSpherePairDomain

/-!
# Actual two-point domains allowing a protected source point

The two source points must be distinct and both images must lie in the same
valid target chart. The active domain requires only one nonzero cutoff, so
it includes mixed pairs with exactly one protected source point.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere

open NoExoticSixSphere

open GLOrthonormalization EuclideanEmbedding
open TwoSpherePerturbation (Parameters SourceChart TargetChart pairLeft pairRight
  pairSource contDiff_pairLeft contDiff_pairRight)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f : ℝ → Sphere 2 → M) (χ : Sphere 2 → ℝ)

def pairBaseDomain
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s z : SourceChart) (c : TargetChart n M) :
    Opens (Parameters e × (ℝ × (Vector 2 × Vector 2))) :=
  ⟨pairLeft e ⁻¹' (chartDomain e r f χ hf hχ s c : Set _) ∩
      pairRight e ⁻¹' (chartDomain e r f χ hf hχ z c : Set _),
    ((chartDomain e r f χ hf hχ s c).isOpen.preimage (contDiff_pairLeft e).continuous).inter
      ((chartDomain e r f χ hf hχ z c).isOpen.preimage (contDiff_pairRight e).continuous)⟩

theorem contMDiffOn_pairSource
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s z : SourceChart) (c : TargetChart n M) :
    ContMDiffOn 𝓘(ℝ, Parameters e × (ℝ × (Vector 2 × Vector 2)))
      ((𝓡 2).prod (𝓡 2)) ∞ (pairSource e s z) (pairBaseDomain e r f χ hf hχ s z c) := by
  have hleft : ContDiff ℝ ∞
      (fun q : Parameters e × (ℝ × (Vector 2 × Vector 2)) ↦ q.2.2.1) := by fun_prop
  have hright : ContDiff ℝ ∞
      (fun q : Parameters e × (ℝ × (Vector 2 × Vector 2)) ↦ q.2.2.2) := by fun_prop
  exact (s.contMDiffOn_invFun.comp hleft.contMDiff.contMDiffOn (fun _ hq ↦ hq.1.1.1.1)).prodMk
    (z.contMDiffOn_invFun.comp hright.contMDiff.contMDiffOn (fun _ hq ↦ hq.2.1.1.1))

def pairDomain
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s z : SourceChart) (c : TargetChart n M) :
    Opens (Parameters e × (ℝ × (Vector 2 × Vector 2))) :=
  ⟨(pairBaseDomain e r f χ hf hχ s z c : Set _) ∩
      pairSource e s z ⁻¹' {w : Sphere 2 × Sphere 2 | w.1 ≠ w.2},
    (contMDiffOn_pairSource e r f χ hf hχ s z c).continuousOn.isOpen_inter_preimage
      (pairBaseDomain e r f χ hf hχ s z c).isOpen
      (isClosed_eq continuous_fst continuous_snd).isOpen_compl⟩

def activePairDomain
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s z : SourceChart) (c : TargetChart n M) :
    Opens (Parameters e × (ℝ × (Vector 2 × Vector 2))) :=
  ⟨(pairDomain e r f χ hf hχ s z c : Set _) ∩
      pairSource e s z ⁻¹' {w : Sphere 2 × Sphere 2 | χ w.1 ≠ 0 ∨ χ w.2 ≠ 0}, by
    have ho : IsOpen {w : Sphere 2 × Sphere 2 | χ w.1 ≠ 0 ∨ χ w.2 ≠ 0} :=
      (isClosed_eq (hχ.continuous.comp continuous_fst) continuous_const).isOpen_compl.union
        (isClosed_eq (hχ.continuous.comp continuous_snd) continuous_const).isOpen_compl
    have hsrc : ContinuousOn (pairSource e s z) (pairDomain e r f χ hf hχ s z c) :=
      (contMDiffOn_pairSource e r f χ hf hχ s z c).continuousOn.mono inter_subset_left
    exact hsrc.isOpen_inter_preimage (pairDomain e r f χ hf hχ s z c).isOpen ho⟩

def chartDifference (s z : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × (Vector 2 × Vector 2))) : Vector n :=
  chartCoordinates e r f χ s c (pairLeft e q) -
    chartCoordinates e r f χ z c (pairRight e q)

theorem contDiffOn_chartDifference
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s z : SourceChart) (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (chartDifference e r f χ s z c) (pairDomain e r f χ hf hχ s z c) :=
  ((contDiffOn_chartCoordinates e r f χ hf hχ s c).comp (contDiff_pairLeft e).contDiffOn
    (fun _ hq ↦ hq.1.1)).sub
      ((contDiffOn_chartCoordinates e r f χ hf hχ z c).comp (contDiff_pairRight e).contDiffOn
        (fun _ hq ↦ hq.1.2))

theorem chartDifference_zero_iff
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    (s z : SourceChart) (c : TargetChart n M)
    (q : Parameters e × (ℝ × (Vector 2 × Vector 2)))
    (hq : q ∈ pairDomain e r f χ hf hχ s z c) :
    chartDifference e r f χ s z c q = 0 ↔
      map e r f χ q.1 q.2.1 (s.symm q.2.2.1) =
        map e r f χ q.1 q.2.1 (z.symm q.2.2.2) := by
  change c (map e r f χ q.1 q.2.1 (s.symm q.2.2.1)) -
      c (map e r f χ q.1 q.2.1 (z.symm q.2.2.2)) = 0 ↔ _
  rw [sub_eq_zero]
  exact ⟨c.toPartialEquiv.injOn hq.1.1.2 hq.1.2.2, congrArg c⟩

end Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere
