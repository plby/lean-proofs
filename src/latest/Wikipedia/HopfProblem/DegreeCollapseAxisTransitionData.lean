import Wikipedia.HopfProblem.DegreeCollapseAxisDerivativeBlock

/-!
# Smooth derivative data from the actual native endpoint transition

When two native charts have the same whole axis germ, their actual
transition fixes that germ. On a constructed open interval its derivative
has smooth shear and invertible transverse blocks. No independent frame
family is supplied in place of the native transition.
-/

noncomputable section

open Set Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.AxisCoordinates

variable {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Extract smooth block data of the original transition near a matching axis germ. -/
theorem exists_native_axis_transition_data
    (Φ Ψ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞)
    {s₀ : ℝ} (hΦ : (s₀, (0 : V)) ∈ Φ.source) (hΨ : (s₀, (0 : V)) ∈ Ψ.source)
    (haxis : (fun s : ℝ => Φ (s, 0)) =ᶠ[𝓝 s₀] (fun s => Ψ (s, 0))) :
    ∃ U : Set ℝ, IsOpen U ∧ s₀ ∈ U ∧
      (∀ s ∈ U, (s, (0 : V)) ∈ (Φ.trans Ψ.symm).source) ∧
      (∀ s ∈ U, Ψ.symm (Φ (s, 0)) = (s, 0)) ∧
      ContDiffOn ℝ ∞ (fun s => tangentShear (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0))) U ∧
      ContDiffOn ℝ ∞ (fun s => transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0))) U ∧
      (∀ s ∈ U, (transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0))).IsInvertible) ∧
      ∀ s ∈ U, fderiv ℝ (Ψ.symm ∘ Φ) (s, 0) =
        FrameField.shearedBlock (tangentShear (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0)))
          (transverseBlock (fderiv ℝ (Ψ.symm ∘ Φ) (s, 0))) := by
  let R := Φ.trans Ψ.symm
  have hR0 : (s₀, (0 : V)) ∈ R.source := by
    refine ⟨hΦ, ?_⟩
    change Φ (s₀, 0) ∈ Ψ.target
    rw [haxis.eq_of_nhds]
    exact Ψ.map_source' hΨ
  have hRsource : ∀ᶠ s in 𝓝 s₀, (s, (0 : V)) ∈ R.source :=
    (continuous_id.prodMk continuous_const).continuousAt (R.open_source.mem_nhds hR0)
  have hΨsource : ∀ᶠ s in 𝓝 s₀, (s, (0 : V)) ∈ Ψ.source :=
    (continuous_id.prodMk continuous_const).continuousAt (Ψ.open_source.mem_nhds hΨ)
  have hRaxis : ∀ᶠ s in 𝓝 s₀, R (s, (0 : V)) = (s, 0) := by
    filter_upwards [haxis, hΨsource] with s hs hsΨ
    change Ψ.symm (Φ (s, 0)) = (s, 0)
    rw [hs]
    exact Ψ.left_inv' hsΨ
  obtain ⟨U, hUN, hU, hs₀⟩ := mem_nhds_iff.mp (hRsource.and hRaxis)
  have hdf : ContDiffOn ℝ ∞ (fun s : ℝ => fderiv ℝ R (s, (0 : V))) U :=
    (R.contMDiffOn_toFun.contDiffOn.fderiv_of_isOpen R.open_source (m := ∞) (by simp)).comp
      (contDiff_id.prodMk contDiff_const).contDiffOn (fun s hs => (hUN hs).1)
  have hfix (s : ℝ) (hs : s ∈ U) : fderiv ℝ R (s, (0 : V)) (1, 0) = (1, 0) := by
    apply derivative_fixes_axis
      (R.contMDiffOn_toFun.contDiffOn.contDiffAt (R.open_source.mem_nhds (hUN hs).1))
    filter_upwards [hU.mem_nhds hs] with r hr
    exact (hUN hr).2
  refine ⟨U, hU, hs₀, fun s hs => (hUN hs).1, fun s hs => (hUN hs).2,
    (contDiff_tangentShear (V := V)).contDiffOn.comp hdf (fun _ _ => mem_univ _),
    (contDiff_transverseBlock (V := V)).contDiffOn.comp hdf (fun _ _ => mem_univ _), ?_, ?_⟩
  · intro s hs
    have hl : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × V) 𝓘(ℝ, ℝ × V) ∞ R (s, 0) :=
      ⟨R, (hUN hs).1, fun _ _ => rfl⟩
    have hi : (fderiv ℝ R (s, 0)).IsInvertible := by
      refine ⟨hl.mfderivToContinuousLinearEquiv (by simp), ?_⟩
      have he := hl.mfderivToContinuousLinearEquiv_coe (by simp)
      rw [mfderiv_eq_fderiv] at he
      exact he
    exact isInvertible_transverseBlock _ (hfix s hs) hi
  · intro s hs
    exact axis_block_eq _ (hfix s hs)

end Wikipedia.HopfProblem.DegreeCollapse.AxisCoordinates
