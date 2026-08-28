import Wikipedia.HopfProblem.DegreeCollapseLowSphereAffineChartDomain

/-!

# Genuine two-source-chart domains for manifold double points

Both images lie in one target chart, while the two source points may use
different source charts. The actual sphere points are required to be distinct.
On this open domain the coordinate difference is smooth and vanishes exactly
when the two actual manifold-valued images agree.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSphereAffine

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding

variable {d n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere d → M)

def pairLeft (q : Parameters e d × (ℝ × (Vector d × Vector d))) :
    Parameters e d × (ℝ × Vector d) := (q.1, q.2.1, q.2.2.1)

def pairRight (q : Parameters e d × (ℝ × (Vector d × Vector d))) :
    Parameters e d × (ℝ × Vector d) := (q.1, q.2.1, q.2.2.2)

theorem contDiff_pairLeft : ContDiff ℝ ∞ (pairLeft (d := d) e) := by unfold pairLeft; fun_prop

theorem contDiff_pairRight : ContDiff ℝ ∞ (pairRight (d := d) e) := by unfold pairRight; fun_prop

def pairSource (s z : (SourceChart d)) (q : Parameters e d × (ℝ × (Vector d × Vector d))) :
    Sphere d × Sphere d := (s.symm q.2.2.1, z.symm q.2.2.2)

def pairBaseDomain
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 n) ∞ (uncurry f))
    (s z : (SourceChart d)) (c : TargetChart n M) :
    Opens (Parameters e d × (ℝ × (Vector d × Vector d))) :=
  ⟨pairLeft (d := d) e ⁻¹' (chartDomain e r f hf s c : Set _) ∩
      pairRight (d := d) e ⁻¹' (chartDomain e r f hf z c : Set _),
    ((chartDomain e r f hf s c).isOpen.preimage (contDiff_pairLeft (d := d) e).continuous).inter
      ((chartDomain e r f hf z c).isOpen.preimage (contDiff_pairRight (d := d) e).continuous)⟩

theorem contMDiffOn_pairSource
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 n) ∞ (uncurry f))
    (s z : (SourceChart d)) (c : TargetChart n M) :
    ContMDiffOn 𝓘(ℝ, Parameters e d × (ℝ × (Vector d × Vector d)))
      ((𝓡 d).prod (𝓡 d)) ∞ (pairSource e s z) (pairBaseDomain e r f hf s z c) := by
  have hleft : ContDiff ℝ ∞
      (fun q : Parameters e d × (ℝ × (Vector d × Vector d)) ↦ q.2.2.1) := by fun_prop
  have hright : ContDiff ℝ ∞
      (fun q : Parameters e d × (ℝ × (Vector d × Vector d)) ↦ q.2.2.2) := by fun_prop
  exact (s.contMDiffOn_invFun.comp hleft.contMDiff.contMDiffOn (fun _ hq ↦ hq.1.1.1.1)).prodMk
    (z.contMDiffOn_invFun.comp hright.contMDiff.contMDiffOn (fun _ hq ↦ hq.2.1.1.1))

def pairDomain
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 n) ∞ (uncurry f))
    (s z : (SourceChart d)) (c : TargetChart n M) :
    Opens (Parameters e d × (ℝ × (Vector d × Vector d))) :=
  ⟨(pairBaseDomain e r f hf s z c : Set _) ∩
      pairSource e s z ⁻¹' {w : Sphere d × Sphere d | w.1 ≠ w.2},
    (contMDiffOn_pairSource e r f hf s z c).continuousOn.isOpen_inter_preimage
      (pairBaseDomain e r f hf s z c).isOpen
      (isClosed_eq continuous_fst continuous_snd).isOpen_compl⟩

def chartDifference (s z : (SourceChart d)) (c : TargetChart n M)
    (q : Parameters e d × (ℝ × (Vector d × Vector d))) : Vector n :=
  chartCoordinates e r f s c (pairLeft (d := d) e q) -
    chartCoordinates e r f z c (pairRight (d := d) e q)

theorem contDiffOn_chartDifference
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 n) ∞ (uncurry f))
    (s z : (SourceChart d)) (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (chartDifference e r f s z c) (pairDomain e r f hf s z c) :=
  ((contDiffOn_chartCoordinates e r f hf s c).comp (contDiff_pairLeft (d := d) e).contDiffOn
    (fun _ hq ↦ hq.1.1)).sub
      ((contDiffOn_chartCoordinates e r f hf z c).comp (contDiff_pairRight (d := d) e).contDiffOn
        (fun _ hq ↦ hq.1.2))

theorem chartDifference_zero_iff
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 n) ∞ (uncurry f))
    (s z : (SourceChart d)) (c : TargetChart n M)
    (q : Parameters e d × (ℝ × (Vector d × Vector d))) (hq : q ∈ pairDomain e r f hf s z c) :
    chartDifference e r f s z c q = 0 ↔
      map e r f q.1 q.2.1 (s.symm q.2.2.1) = map e r f q.1 q.2.1 (z.symm q.2.2.2) := by
  change c (map e r f q.1 q.2.1 (s.symm q.2.2.1)) -
      c (map e r f q.1 q.2.1 (z.symm q.2.2.2)) = 0 ↔ _
  rw [sub_eq_zero]
  exact ⟨c.toPartialEquiv.injOn hq.1.1.2 hq.1.2.2, congrArg c⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowSphereAffine
