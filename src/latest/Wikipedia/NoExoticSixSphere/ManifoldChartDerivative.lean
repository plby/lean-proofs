import Wikipedia.NoExoticSixSphere.ManifoldAffineChartDomain

/-!
# Intrinsic derivatives and genuine manifold coordinates

The derivative of a map in source and target charts is the intrinsic
derivative composed with the two chart differentials. Since those
differentials are bijective, coordinates preserve injectivity. The charted
spaces here are the given ones; no smooth structure is transported or replaced.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldCoordinates

open GLOrthonormalization

variable {k n : ℕ} {X M : Type*}
  [TopologicalSpace X] [ChartedSpace (Vector k) X]
  [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (g : X → M)
  (s : PartialDiffeomorph (𝓡 k) (𝓡 k) X (Vector k) ∞)
  (c : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)
  (x : Vector k) (hs : x ∈ s.target) (hc : g (s.symm x) ∈ c.source)

include hs hc

theorem fderiv_in_charts
    (hg : MDifferentiableAt (𝓡 k) (𝓡 n) g (s.symm x)) :
    fderiv ℝ (fun z ↦ c (g (s.symm z))) x =
      (mfderiv (𝓡 n) (𝓡 n) c (g (s.symm x))).comp
        ((mfderiv (𝓡 k) (𝓡 n) g (s.symm x)).comp
          (mfderiv (𝓡 k) (𝓡 k) s.symm x)) := by
  have hsmooth := s.contMDiffOn_invFun.contMDiffAt (s.open_target.mem_nhds hs)
  have hcsmooth := c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hc)
  have hsd := hsmooth.mdifferentiableAt (by simp)
  have hcd := hcsmooth.mdifferentiableAt (by simp)
  change fderiv ℝ (c ∘ (g ∘ s.symm)) x = _
  rw [← mfderiv_eq_fderiv, mfderiv_comp x hcd (hg.comp x hsd),
    mfderiv_comp x hg hsd]
  rfl

theorem injective_fderiv_in_charts_iff
    (hg : MDifferentiableAt (𝓡 k) (𝓡 n) g (s.symm x)) :
    Injective (fderiv ℝ (fun z ↦ c (g (s.symm z))) x) ↔
      Injective (mfderiv (𝓡 k) (𝓡 n) g (s.symm x)) := by
  have hslocal : IsLocalDiffeomorphAt (𝓡 k) (𝓡 k) ∞ s.symm x :=
    ⟨s.symm, hs, fun _ _ ↦ rfl⟩
  have hclocal : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ c (g (s.symm x)) :=
    ⟨c, hc, fun _ _ ↦ rfl⟩
  have hsbij := (hslocal.mfderivToContinuousLinearEquiv (by simp)).bijective
  have hcbij := (hclocal.mfderivToContinuousLinearEquiv (by simp)).bijective
  change Bijective (mfderiv (𝓡 k) (𝓡 k) s.symm x) at hsbij
  change Bijective (mfderiv (𝓡 n) (𝓡 n) c (g (s.symm x))) at hcbij
  rw [fderiv_in_charts g s c x hs hc hg]
  let A : Vector k →L[ℝ] Vector k := mfderiv (𝓡 k) (𝓡 k) s.symm x
  let D : Vector k →L[ℝ] Vector n := mfderiv (𝓡 k) (𝓡 n) g (s.symm x)
  let B : Vector n →L[ℝ] Vector n := mfderiv (𝓡 n) (𝓡 n) c (g (s.symm x))
  change Injective (B.comp (D.comp A)) ↔ Injective D
  change Bijective A at hsbij
  change Bijective B at hcbij
  constructor
  · intro hi u v huv
    obtain ⟨a, ha⟩ := hsbij.2 u
    obtain ⟨b, hb⟩ := hsbij.2 v
    have hab : a = b := hi (by
      simpa only [ContinuousLinearMap.comp_apply, ha, hb] using congrArg B huv)
    exact ha.symm.trans ((congrArg A hab).trans hb)
  · intro hi
    exact hcbij.1.comp (hi.comp hsbij.1)

end NoExoticSixSphere.ManifoldCoordinates
