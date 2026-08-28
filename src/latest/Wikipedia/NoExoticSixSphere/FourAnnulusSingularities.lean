import Wikipedia.NoExoticSixSphere.FourDiskSingularities
import Wikipedia.NoExoticSixSphere.SphereAnnulusCoordinates

/-!
# Finitely many intrinsic singularities in the original closed annulus

Chartwise genericity isolates the actual manifold singularities. Their
closed set in the compact annulus is compact, and the protected immersive
collars place every singularity in the open generic region. Thus the
singular set is finite. Its cardinality is not asserted to be even here.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourAnnulus

open GLOrthonormalization SphereAnnulus

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]

theorem finite_singular_of_chart_jets (e : EuclideanEmbedding 7 M) (g : Vector 4 → M)
    (hg : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
    (r₀ r₁ : ℝ) (hr₀ : 1 < r₀) (hr₁ : r₁ < 2)
    (hi : ∀ x ∈ domain 3, ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖ →
      Injective (fderiv ℝ (e.toFun ∘ g) x))
    (C : Set (PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞))
    (hcov : ∀ y : M, ∃ c ∈ C, y ∈ c.source)
    (hgen : ∀ c ∈ C, OperatorRank.RegularFourSevenOn
      (fun x ↦ fderiv ℝ (c ∘ g) x) {x | (r₀ < ‖x‖ ∧ ‖x‖ < r₁) ∧ g x ∈ c.source}) :
    (domain 3 ∩ {x | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)}).Finite := by
  let S := domain 3 ∩ {x | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g x)}
  have he : S = domain 3 ∩ {x | ¬ Injective (fderiv ℝ (e.toFun ∘ g) x)} := by
    ext x
    apply and_congr_right
    intro hx
    exact (GenericFourDisk.injective_embedded_derivative_iff e g x
      ((hg x hx).mdifferentiableAt (by simp))).not.symm
  have hD : ContinuousOn (fderiv ℝ (e.toFun ∘ g)) (domain 3) :=
    fun x hx ↦ ((e.smooth.contMDiffAt.comp x (hg x hx)).contDiffAt.continuousAt_fderiv
      (by simp)).continuousWithinAt
  have hclosed : IsClosed S := by
    rw [he]
    exact hD.preimage_isClosed_of_isClosed (isClosed_domain 3)
      ContinuousLinearMap.isOpen_injective.isClosed_compl
  have hcompact : IsCompact S := (isCompact_domain 3).of_isClosed_subset hclosed inter_subset_left
  have hdis := GenericFourDisk.isDiscrete_singular_of_chart_jets g
    {x | r₀ < ‖x‖ ∧ ‖x‖ < r₁}
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const))
    (fun x hx ↦ hg x ⟨(hr₀.trans hx.1).le, (hx.2.trans hr₁).le⟩) C hcov hgen
  exact hcompact.finite (hdis.mono (by
    intro x hx
    have hnot : ¬ (‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖) := by
      intro hend
      exact hx.2 ((GenericFourDisk.injective_embedded_derivative_iff e g x
        ((hg x hx.1).mdifferentiableAt (by simp))).mp (hi x hx.1 hend))
    exact ⟨⟨lt_of_not_ge (fun h ↦ hnot (Or.inl h)),
      lt_of_not_ge (fun h ↦ hnot (Or.inr h))⟩, hx.2⟩))

end NoExoticSixSphere.GenericFourAnnulus
