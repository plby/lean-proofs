import Wikipedia.SmoothSixDPoincare.FiberwiseFrameChart
import Wikipedia.SmoothSixDPoincare.DiskTubularNeighborhood

/-!
# Reframe an actual tubular chart around its compact zero section

Compose the original native chart with the constructed fiberwise partial
diffeomorphism. Compactness gives a positive uniform fiber radius. The global
formula is retained, and the transition back into the original tubular chart
has exactly the prescribed derivative along the zero section.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FrameField

variable {X Z F E M : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Construct a positive-radius reframed native chart, with the exact transition derivative. -/
theorem exists_reframed_tubular_chart
    (Ψ : PartialDiffeomorph 𝓘(ℝ, X × F) 𝓘(ℝ, E) (X × F) M ∞)
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hzero : K ×ˢ {(0 : F)} ⊆ Ψ.source)
    {T : X → (Z →L[ℝ] F)} (hT : ContDiffOn ℝ ∞ T U)
    (hi : ∀ x ∈ U, (T x).IsInvertible) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, X × Z) 𝓘(ℝ, E) (X × Z) M ∞,
        K ×ˢ Metric.closedBall (0 : Z) ε ⊆ Φ.source ∧
        (∀ p, Φ p = Ψ (fiberMap T p)) ∧ Φ.target ⊆ Ψ.target ∧
        (∀ x ∈ K, (Ψ.symm ∘ Φ) =ᶠ[𝓝 (x, (0 : Z))] fiberMap T) ∧
        ∀ x ∈ K, HasFDerivAt (Ψ.symm ∘ Φ)
          ((ContinuousLinearMap.id ℝ X).prodMap (T x)) (x, 0) := by
  let χ := fiberwiseFrameChart hU hT hi
  let Φ := χ.trans Ψ
  have hzeroΦ : K ×ˢ {(0 : Z)} ⊆ Φ.source := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    have hz0 : z = 0 := hz
    subst z
    refine ⟨hKU hx, ?_⟩
    change fiberMap T (x, 0) ∈ Ψ.source
    rw [fiberMap_zero]
    exact hzero ⟨hx, rfl⟩
  obtain ⟨ε, hε, hprod⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset hK Φ.open_source hzeroΦ
  have hgerm : ∀ x ∈ K, (Ψ.symm ∘ Φ) =ᶠ[𝓝 (x, (0 : Z))] fiberMap T := by
    intro x hx
    filter_upwards [Φ.open_source.mem_nhds (hzeroΦ ⟨hx, rfl⟩)] with p hp
    change Ψ.symm (Ψ (fiberMap T p)) = fiberMap T p
    exact Ψ.left_inv' hp.2
  refine ⟨ε, hε, Φ, hprod, fun _ => rfl, fun _ hy => hy.1, hgerm, ?_⟩
  intro x hx
  apply (hgerm x hx).hasFDerivAt_iff.mpr
  exact hasFDerivAt_fiberMap_zero
    ((hT.contDiffAt (hU.mem_nhds (hKU hx))).differentiableAt (by simp))

end Wikipedia.SmoothSixDPoincare.FrameField
