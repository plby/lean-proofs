import Wikipedia.SmoothSixDPoincare.ShearedFrameChart
import Wikipedia.SmoothSixDPoincare.ReframedTubularChart

/-!
# An actual native tubular chart with a prescribed tangent shear

The constructed compact shear chart composes with the original native chart.
The global formula, zero section, and exact full transition derivative are
retained, and the source contains a uniform positive-radius fiber product.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FrameField

variable {X Z F E M : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Construct the genuine native chart with both disk and normal components of its fiber columns. -/
theorem exists_sheared_tubular_chart
    (Ψ : PartialDiffeomorph 𝓘(ℝ, X × F) 𝓘(ℝ, E) (X × F) M ∞)
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hzero : K ×ˢ {(0 : F)} ⊆ Ψ.source)
    {A : X → (Z →L[ℝ] X)} {T : X → (Z →L[ℝ] F)}
    (hA : ContDiffOn ℝ ∞ A U) (hT : ContDiffOn ℝ ∞ T U)
    (hi : ∀ x ∈ K, (T x).IsInvertible) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, X × Z) 𝓘(ℝ, E) (X × Z) M ∞,
        K ×ˢ Metric.closedBall (0 : Z) ε ⊆ Φ.source ∧
        (∀ p, Φ p = Ψ (shearedMap A T p)) ∧ Φ.target ⊆ Ψ.target ∧
        (∀ x ∈ K, (Ψ.symm ∘ Φ) =ᶠ[𝓝 (x, (0 : Z))] shearedMap A T) ∧
        ∀ x ∈ K, HasFDerivAt (Ψ.symm ∘ Φ) (shearedBlock (A x) (T x)) (x, 0) := by
  obtain ⟨χ, hzeroχ, -, hχ⟩ := exists_sheared_frame_chart hK hU hKU hA hT hi
  let Φ := χ.trans Ψ
  have hzeroΦ : K ×ˢ {(0 : Z)} ⊆ Φ.source := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    have hz0 : z = 0 := hz
    subst z
    refine ⟨hzeroχ ⟨hx, rfl⟩, ?_⟩
    change χ (x, 0) ∈ Ψ.source
    rw [hχ, shearedMap_zero]
    exact hzero ⟨hx, rfl⟩
  obtain ⟨ε, hε, hprod⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset hK Φ.open_source hzeroΦ
  have hgerm : ∀ x ∈ K, (Ψ.symm ∘ Φ) =ᶠ[𝓝 (x, (0 : Z))] shearedMap A T := by
    intro x hx
    filter_upwards [Φ.open_source.mem_nhds (hzeroΦ ⟨hx, rfl⟩)] with p hp
    change Ψ.symm (Ψ (χ p)) = shearedMap A T p
    have hpΨ : χ p ∈ Ψ.source := hp.2
    exact (Ψ.left_inv' hpΨ).trans (congrFun hχ p)
  refine ⟨ε, hε, Φ, hprod, ?_, fun _ hy => hy.1, hgerm, ?_⟩
  · intro p
    change Ψ (χ p) = Ψ (shearedMap A T p)
    rw [hχ]
  · intro x hx
    apply (hgerm x hx).hasFDerivAt_iff.mpr
    exact hasFDerivAt_shearedMap_zero
      ((hA.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))
      ((hT.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))

end Wikipedia.SmoothSixDPoincare.FrameField
