import Wikipedia.SmoothSixDPoincare.SupportedShearGerm

/-!
# Supported lower shears retaining the transverse projection

Conjugating the constructed supported upper shear by the genuine product
commutation diffeomorphism gives the complementary shear. Its first
projection is unchanged at every point and time, so it cannot create or
remove intersections with the second coordinate plane.
-/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

/-- Realize the lower shear in any prescribed open neighborhood, with
native smooth inverses and the exact first projection retained globally. -/
theorem exists_supported_lower_shear_isotopy (R : A →L[ℝ] B)
    {U : Set (A × B)} (hU : IsOpen U) (hzero : (0 : A × B) ∈ U) :
    ∃ (H : ℝ × (A × B) → A × B) (K : Set (A × B)),
      IsCompact K ∧ K ⊆ U ∧
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, A × B)) 𝓘(ℝ, A × B) ∞ H ∧
      (∀ p, H (0, p) = p) ∧
      (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, A × B) 𝓘(ℝ, A × B) (A × B) (A × B) ∞,
        ∀ p, D p = H (t, p)) ∧
      (∀ t p, p ∉ K → H (t, p) = p) ∧
      (∀ t p, (H (t, p)).1 = p.1) ∧
      (∀ t y, H (t, ((0 : A), y)) = (0, y)) ∧
      (fun p => H (1, p)) =ᶠ[𝓝 (0 : A × B)] (fun p => (p.1, p.2 + R p.1)) := by
  let e := ContinuousLinearEquiv.prodComm ℝ A B
  let U' := e.symm ⁻¹' U
  have hU' : IsOpen U' := hU.preimage e.symm.continuous
  have hzero' : (0 : B × A) ∈ U' := by simpa only [U', mem_preimage, map_zero] using hzero
  obtain ⟨J, K', hK', hK'U', hJ, hJ0, hdiff, hfix, hsecond, hcore, hgerm⟩ :=
    SupportedDiffeomorph.exists_supported_shear_isotopy R hU' hzero'
  let H : ℝ × (A × B) → A × B := fun p => e.symm (J (p.1, e p.2))
  let K := e.symm '' K'
  have hK : IsCompact K := hK'.image e.symm.continuous
  have hKU : K ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    exact hK'U' hy
  have hH : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, A × B)) 𝓘(ℝ, A × B) ∞ H :=
    e.symm.contDiff.contMDiff.comp (hJ.comp
      (contMDiff_fst.prodMk (e.contDiff.contMDiff.comp contMDiff_snd)))
  refine ⟨H, K, hK, hKU, hH, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    change e.symm (J (0, e p)) = p
    rw [hJ0, e.symm_apply_apply]
  · intro t
    obtain ⟨D, hD⟩ := hdiff t
    refine ⟨(e.toDiffeomorph.trans D).trans e.symm.toDiffeomorph, ?_⟩
    intro p
    change e.symm (D (e p)) = e.symm (J (t, e p))
    rw [hD]
  · intro t p hp
    have hnot : e p ∉ K' := fun h => hp ⟨e p, h, e.symm_apply_apply p⟩
    change e.symm (J (t, e p)) = p
    rw [hfix t _ hnot, e.symm_apply_apply]
  · intro t p
    exact hsecond t (e p)
  · intro t y
    change e.symm (J (t, (y, (0 : A)))) = (0, y)
    rw [hcore]
    rfl
  · have ht : Tendsto e (𝓝 (0 : A × B)) (𝓝 0) := by
      simpa only [map_zero] using e.continuous.tendsto (0 : A × B)
    filter_upwards [hgerm.comp_tendsto ht] with p hp
    change J (1, e p) = ((e p).1 + R (e p).2, (e p).2) at hp
    change e.symm (J (1, e p)) = (p.1, p.2 + R p.1)
    rw [hp]
    rfl

end Wikipedia.HopfProblem.DegreeCollapse.TransverseGerms
