import Wikipedia.HopfProblem.DegreeCollapseLowSphereAffineChartDomain
import Wikipedia.NoExoticSixSphere.ManifoldChartDerivative

/-!

# Smooth actual spatial jets and their native derivative comparison

On the proved coupled chart domain, differentiating in the sphere coordinate
gives a smooth operator-valued map. Injectivity of this actual chart jet is
equivalent to injectivity of the original manifold derivative. No replacement
atlas or assumption of genericity is used.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSphereAffine

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding

variable {d n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere d → M)

def chartJet (s : SourceChart d) (c : TargetChart n M)
    (q : Parameters e d × (ℝ × Vector d)) : Vector d →L[ℝ] Vector n :=
  fderiv ℝ (fun x ↦ chartCoordinates e r f s c (q.1, q.2.1, x)) q.2.2

theorem contDiffOn_chartJet
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 n) ∞ (uncurry f))
    (s : SourceChart d) (c : TargetChart n M) :
    ContDiffOn ℝ ∞ (chartJet e r f s c) (chartDomain e r f hf s c) := by
  intro q hq
  have hF := (contDiffOn_chartCoordinates e r f hf s c).contDiffAt
    ((chartDomain e r f hf s c).isOpen.mem_nhds hq)
  have hLift : ContDiff ℝ ∞
      (fun z : (Parameters e d × (ℝ × Vector d)) × Vector d ↦
        (z.1.1, z.1.2.1, z.2)) := by fun_prop
  have hH := hF.comp (q, q.2.2) hLift.contDiffAt
  have hJ : ContDiffAt ℝ ∞ (chartJet e r f s c) q :=
    hH.fderiv (contDiff_snd.comp contDiff_snd).contDiffAt (by simp)
  exact hJ.contDiffWithinAt

theorem injective_chartJet_iff
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 n) ∞ (uncurry f)) (p : Parameters e d)
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 d)) (𝓡 n) ∞ (uncurry (map e r f p)))
    (s : SourceChart d) (c : TargetChart n M) (x : ℝ × Vector d)
    (hx : (p, x) ∈ chartDomain e r f hf s c) :
    Injective (chartJet e r f s c (p, x)) ↔
      Injective (mfderiv (𝓡 d) (𝓡 n) (map e r f p x.1) (s.symm x.2)) := by
  have hslice : ContMDiff (𝓡 d) (𝓡 n) ∞ (map e r f p x.1) :=
    hg.comp (contMDiff_const.prodMk contMDiff_id)
  exact ManifoldCoordinates.injective_fderiv_in_charts_iff
    (map e r f p x.1) s c x.2 hx.1.1.1 hx.2 (hslice.mdifferentiableAt (by simp))

end Wikipedia.HopfProblem.DegreeCollapse.LowSphereAffine
