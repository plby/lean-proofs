import Wikipedia.NoExoticSixSphere.SphereChartBall

/-!
# Genuine product charts for time times the original three-sphere

The partial diffeomorphism retains time and uses the given sphere chart.
Composing its inverse with a coordinate-ball chart retains an actual manifold
partial diffeomorphism on an open neighborhood of the whole closed ball.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily

open GLOrthonormalization ManifoldAffineSphereFamily

def timeChart (s : SourceChart) :
    PartialDiffeomorph (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ × Vector 3)
      (ℝ × Sphere 3) (ℝ × Vector 3) ∞ where
  toPartialEquiv := ((OpenPartialHomeomorph.refl ℝ).prod s.toOpenPartialHomeomorph).toPartialEquiv
  open_source := isOpen_univ.prod s.open_source
  open_target := isOpen_univ.prod s.open_target
  contMDiffOn_toFun := by
    have ht : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × Sphere 3 ↦ q.1) (univ ×ˢ s.source) := contMDiff_fst.contMDiffOn
    have hx : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
        (fun q : ℝ × Sphere 3 ↦ s q.2) (univ ×ˢ s.source) :=
      s.contMDiffOn_toFun.comp contMDiff_snd.contMDiffOn (fun _ hq ↦ hq.2)
    exact ht.prodMk_space hx
  contMDiffOn_invFun := by
    have ht : ContMDiffOn 𝓘(ℝ, ℝ × Vector 3) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × Vector 3 ↦ q.1) (univ ×ˢ s.target) :=
      contDiff_fst.contMDiff.contMDiffOn
    have hx : ContMDiffOn 𝓘(ℝ, ℝ × Vector 3) (𝓡 3) ∞
        (fun q : ℝ × Vector 3 ↦ s.symm q.2) (univ ×ˢ s.target) :=
      s.contMDiffOn_invFun.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hq ↦ hq.2)
    exact ht.prodMk hx

theorem timeChart_apply (s : SourceChart) (q : ℝ × Sphere 3) :
    timeChart s q = (q.1, s q.2) := rfl

theorem timeChart_symm_apply (s : SourceChart) (q : ℝ × Vector 3) :
    (timeChart s).symm q = (q.1, s.symm q.2) := rfl

def liftBallChart (s : SourceChart)
    (b : PartialDiffeomorph (𝓡 4) 𝓘(ℝ, ℝ × Vector 3) (Vector 4) (ℝ × Vector 3) ∞) :
    PartialDiffeomorph (𝓡 4) (𝓘(ℝ, ℝ).prod (𝓡 3)) (Vector 4) (ℝ × Sphere 3) ∞ :=
  b.trans (timeChart s).symm

theorem liftBallChart_apply (s : SourceChart)
    (b : PartialDiffeomorph (𝓡 4) 𝓘(ℝ, ℝ × Vector 3) (Vector 4) (ℝ × Vector 3) ∞)
    (z : Vector 4) : liftBallChart s b z = liftChartBall s b z := rfl

theorem closedBall_subset_liftBallChart_source (s : SourceChart)
    (b : PartialDiffeomorph (𝓡 4) 𝓘(ℝ, ℝ × Vector 3) (Vector 4) (ℝ × Vector 3) ∞)
    (hb : closedBall (0 : Vector 4) 1 ⊆ b.source)
    (hs : ∀ z ∈ closedBall (0 : Vector 4) 1, (b z).2 ∈ s.target) :
    closedBall (0 : Vector 4) 1 ⊆ (liftBallChart s b).source := by
  intro z hz
  exact ⟨hb hz, mem_univ _, hs z hz⟩

end NoExoticSixSphere.SphereFamily
