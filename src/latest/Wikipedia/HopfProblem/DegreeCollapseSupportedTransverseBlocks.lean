import Wikipedia.HopfProblem.DegreeCollapseTransverseBlockFactorization
import Wikipedia.HopfProblem.DegreeCollapseSupportedLowerShear
import Wikipedia.SmoothSixDPoincare.SupportedRelativeIsotopy

/-!
# Supported reduction of a transverse coordinate germ to diagonal blocks

The nonlinear correction is supported in the target. A supported source
shear fixes the entire first coordinate plane, and a supported target
shear retains the first projection. Their actual native diffeomorphisms
reduce the complete germ to its two invertible diagonal blocks, without
adding any intersection. Both common-support isotopies are retained.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

/-- Reduce the full transverse coordinate germ by two actual supported
relative isotopies, preserving the original source, target, and unique intersection. -/
theorem exists_supported_transverse_block_reduction
    (Φ : PartialDiffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
    (hzero : (0 : A × B) ∈ Φ.source) (hΦzero : Φ 0 = 0)
    (P : A ≃L[ℝ] A) (hP : ∀ x : A, (fderiv ℝ Φ 0 (x, 0)).1 = P x)
    (hunique : ∀ x : A, (x, (0 : B)) ∈ Φ.source → ((Φ (x, 0)).1 = 0 ↔ x = 0)) :
    ∃ (S : B ≃L[ℝ] B)
      (Dₛ Dₜ : Diffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞)
      (Kₛ Kₜ : Set (A × B)),
      IsCompact Kₛ ∧ Kₛ ⊆ Φ.source ∧ IsCompact Kₜ ∧ Kₜ ⊆ Φ.target ∧
      Nonempty (SupportedRelativeIsotopy Dₛ Kₛ {p : A × B | p.2 = 0}) ∧
      Nonempty (SupportedRelativeIsotopy Dₜ Kₜ {(0 : A × B)}) ∧
      MapsTo Dₛ Φ.source Φ.source ∧ MapsTo Dₜ Φ.target Φ.target ∧
      (∀ x : A, (x, (0 : B)) ∈ Φ.source →
        ((Dₜ (Φ (Dₛ (x, 0)))).1 = 0 ↔ x = 0)) ∧
      (fun p => Dₜ (Φ (Dₛ p))) =ᶠ[𝓝 (0 : A × B)] (fun p => (P p.1, S p.2)) := by
  obtain ⟨C, H, K₁, hC, hK₁, hK₁target, hH, hH0, hHdiff, hHfix, hHorigin,
      hHunique, -, hHgerm⟩ :=
    exists_supported_transverse_germ_linearization Φ hzero hΦzero P hP hunique
  have hCP (x : A) : (C (x, 0)).1 = P x := by
    change (C.toContinuousLinearMap (x, 0)).1 = P x
    rw [hC]
    exact hP x
  obtain ⟨Q, R, S, hfactor⟩ := exists_transverse_block_factorization C P hCP
  obtain ⟨J, K₂, hK₂, hK₂source, hJ, hJ0, hJdiff, hJfix, -, hJcore, hJgerm⟩ :=
    exists_supported_shear_isotopy (-Q) Φ.open_source hzero
  have htzero : (0 : A × B) ∈ Φ.target := by
    have hh := Φ.map_source' hzero
    rwa [hΦzero] at hh
  obtain ⟨L, K₃, hK₃, hK₃target, hL, hL0, hLdiff, hLfix, hLfirst, hLcore, hLgerm⟩ :=
    exists_supported_lower_shear_isotopy (-R) Φ.open_target htzero
  obtain ⟨Dₕ, hDₕ⟩ := hHdiff 1
  obtain ⟨Dₛ, hDₛ⟩ := hJdiff 1
  obtain ⟨Dₗ, hDₗ⟩ := hLdiff 1
  let Dₜ := Dₕ.trans Dₗ
  let Kₜ := K₁ ∪ K₃
  have hKₜ : IsCompact Kₜ := hK₁.union hK₃
  have hKₜtarget : Kₜ ⊆ Φ.target := union_subset hK₁target hK₃target
  have hsrc : SupportedRelativeIsotopy Dₛ K₂ {p : A × B | p.2 = 0} := by
    refine ⟨J, hJ, hJ0, fun p => (hDₛ p).symm, hJdiff, hJfix, ?_⟩
    rintro t ⟨x, y⟩ hy
    change y = 0 at hy
    subst y
    exact hJcore t x
  have htgt : SupportedRelativeIsotopy Dₜ Kₜ {(0 : A × B)} := by
    let T : ℝ × (A × B) → A × B := fun p => L (p.1, H p)
    have hT : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, A × B)) 𝓘(ℝ, A × B) ∞ T :=
      hL.comp (contMDiff_fst.prodMk hH)
    refine ⟨T, hT, ?_, ?_, ?_, ?_, ?_⟩
    · intro p
      change L (0, H (0, p)) = p
      rw [hH0, hL0]
    · intro p
      change L (1, H (1, p)) = Dₗ (Dₕ p)
      rw [hDₗ, hDₕ]
    · intro t
      obtain ⟨Eₕ, hEₕ⟩ := hHdiff t
      obtain ⟨Eₗ, hEₗ⟩ := hLdiff t
      refine ⟨Eₕ.trans Eₗ, ?_⟩
      intro p
      change Eₗ (Eₕ p) = L (t, H (t, p))
      rw [hEₗ, hEₕ]
    · intro t p hp
      change L (t, H (t, p)) = p
      rw [hHfix t p (fun h => hp (Or.inl h)), hLfix t p (fun h => hp (Or.inr h))]
    · intro t p hp
      have hp0 : p = 0 := mem_singleton_iff.mp hp
      subst p
      change L (t, H (t, 0)) = 0
      rw [hHorigin]
      exact hLcore t 0
  have hsrczero : Dₛ (0 : A × B) = 0 := hsrc.endpoint_fixed_on 0 rfl
  have hsrctend : Tendsto Dₛ (𝓝 (0 : A × B)) (𝓝 0) := by
    have hh := Dₛ.continuous.tendsto (0 : A × B)
    rwa [hsrczero] at hh
  refine ⟨S, Dₛ, Dₜ, K₂, Kₜ, hK₂, hK₂source, hKₜ, hKₜtarget, ⟨hsrc⟩, ⟨htgt⟩,
    mapsTo_source Φ Dₛ.toEquiv hK₂source hsrc.endpoint_fixed_outside,
    mapsTo_source Φ.symm Dₜ.toEquiv hKₜtarget htgt.endpoint_fixed_outside, ?_, ?_⟩
  · intro x hx
    have hfixed : Dₛ (x, (0 : B)) = (x, 0) := hsrc.endpoint_fixed_on (x, 0) rfl
    rw [hfixed]
    change (Dₗ (Dₕ (Φ (x, 0)))).1 = 0 ↔ x = 0
    rw [hDₗ, hLfirst, hDₕ]
    exact hHunique 1 x hx
  · have hCtend : Tendsto (fun p => C (Dₛ p)) (𝓝 (0 : A × B)) (𝓝 0) := by
      have hh : Tendsto C (𝓝 (0 : A × B)) (𝓝 0) := by
        simpa only [map_zero] using C.continuous.tendsto (0 : A × B)
      exact hh.comp hsrctend
    filter_upwards [hHgerm.comp_tendsto hsrctend, hLgerm.comp_tendsto hCtend, hJgerm]
      with p hpH hpL hpJ
    change H (1, Φ (Dₛ p)) = C (Dₛ p) at hpH
    change L (1, C (Dₛ p)) = ((C (Dₛ p)).1, (C (Dₛ p)).2 + (-R) (C (Dₛ p)).1) at hpL
    change J (1, p) = (p.1 + (-Q) p.2, p.2) at hpJ
    change Dₗ (Dₕ (Φ (Dₛ p))) = (P p.1, S p.2)
    rw [hDₗ, hDₕ, hpH, hpL, hDₛ, hpJ]
    have hmodel (z : A × B) : C z =
        (P (z.1 + Q z.2), S z.2 + R (P (z.1 + Q z.2))) := by
      have hh := congrArg (fun T : (A × B) →L[ℝ] (A × B) => T z) hfactor
      exact hh
    rw [hmodel]
    simp only [neg_apply, add_neg_cancel_right, neg_add_cancel_right]

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
