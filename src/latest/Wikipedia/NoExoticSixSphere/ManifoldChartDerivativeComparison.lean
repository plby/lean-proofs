import Wikipedia.NoExoticSixSphere.ManifoldChartDerivative

/-!
# Equality of native derivatives from equality in genuine charts

For two maps with the same value, equality of their actual chart derivatives
gives equality of their native manifold derivatives. The source and target
chart differentials are cancelled using their proved bijectivity.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldCoordinates

open GLOrthonormalization

variable {k n : ℕ} {X M : Type*}
  [TopologicalSpace X] [ChartedSpace (Vector k) X]
  [TopologicalSpace M] [ChartedSpace (Vector n) M]

theorem mfderiv_eq_of_fderiv_in_charts_eq (g h : X → M)
    (s : PartialDiffeomorph (𝓡 k) (𝓡 k) X (Vector k) ∞)
    (c : PartialDiffeomorph (𝓡 n) (𝓡 n) M (Vector n) ∞)
    (x : Vector k) (hs : x ∈ s.target) (hc : g (s.symm x) ∈ c.source)
    (hg : MDifferentiableAt (𝓡 k) (𝓡 n) g (s.symm x))
    (hh : MDifferentiableAt (𝓡 k) (𝓡 n) h (s.symm x))
    (he : g (s.symm x) = h (s.symm x))
    (hD : fderiv ℝ (fun z ↦ c (g (s.symm z))) x =
      fderiv ℝ (fun z ↦ c (h (s.symm z))) x) :
    mfderiv (𝓡 k) (𝓡 n) g (s.symm x) = mfderiv (𝓡 k) (𝓡 n) h (s.symm x) := by
  have hc' : h (s.symm x) ∈ c.source := he ▸ hc
  have hslocal : IsLocalDiffeomorphAt (𝓡 k) (𝓡 k) ∞ s.symm x :=
    ⟨s.symm, hs, fun _ _ ↦ rfl⟩
  have hclocal : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ c (h (s.symm x)) :=
    ⟨c, hc', fun _ _ ↦ rfl⟩
  have hsurj := (hslocal.mfderivToContinuousLinearEquiv (by simp)).surjective
  have hinj := (hclocal.mfderivToContinuousLinearEquiv (by simp)).injective
  change Surjective (mfderiv (𝓡 k) (𝓡 k) s.symm x) at hsurj
  change Injective (mfderiv (𝓡 n) (𝓡 n) c (h (s.symm x))) at hinj
  rw [fderiv_in_charts g s c x hs hc hg, fderiv_in_charts h s c x hs hc' hh] at hD
  have hC : (mfderiv (𝓡 n) (𝓡 n) c (g (s.symm x)) : Vector n →L[ℝ] Vector n) =
      mfderiv (𝓡 n) (𝓡 n) c (h (s.symm x)) := by rw [he]
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨w, hw⟩ := hsurj v
  apply hinj
  have hev := congrArg (fun L : Vector k →L[ℝ] Vector n ↦ L w) hD
  change (mfderiv (𝓡 n) (𝓡 n) c (g (s.symm x)))
      ((mfderiv (𝓡 k) (𝓡 n) g (s.symm x)) ((mfderiv (𝓡 k) (𝓡 k) s.symm x) w)) =
    (mfderiv (𝓡 n) (𝓡 n) c (h (s.symm x)))
      ((mfderiv (𝓡 k) (𝓡 n) h (s.symm x)) ((mfderiv (𝓡 k) (𝓡 k) s.symm x) w)) at hev
  rw [hC, hw] at hev
  exact hev

end NoExoticSixSphere.ManifoldCoordinates
