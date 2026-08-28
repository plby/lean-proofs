import Wikipedia.HopfProblem.DegreeCollapseConvexHeightProfiles
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Supported increasing time profiles on the original source manifold

A scalar interval diffeomorphism can be blended with the identity using a
native spatial cutoff. The resulting smooth time profile has positive time
derivative, fixes every exterior time and every exterior source point, and
has a prescribed full translation germ on a selected closed source set.

This is the source reparametrization input for time alignment. Applying it
to a family and restoring the new time coordinate still requires separate
control of new collisions and spatial immersion.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

open DegreeCollapse.MorseRearrangement

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

theorem exists_supported_time_profile {C U : Set M}
    (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    {a b t₀ t₁ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (ht₁ : t₁ ∈ Ioo a b) :
    ∃ τ : ℝ × M → ℝ, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ τ ∧
      (∀ x t, 0 < deriv (fun s => τ (s, x)) t) ∧
      (∀ t x, x ∉ U ∨ t ∉ Ioo a b → τ (t, x) = t) ∧
      (∀ x ∈ C, τ =ᶠ[𝓝 (t₀, x)] fun p => p.1 + (t₁ - t₀)) ∧
      (∀ x ∈ C, τ (t₀, x) = t₁) := by
  have hdisjoint : Disjoint Uᶜ C := disjoint_left.mpr (fun x hx hxc => hx (hCU hxc))
  obtain ⟨β, hβout, hβone, hβrange⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed I hU.isClosed_compl hC hdisjoint (n := ⊤)
  obtain ⟨D, hDfix, hDgerm, -, -, hDpos⟩ :=
    exists_increasing_interval_translation ht₀ ht₁
  let τ : ℝ × M → ℝ := fun p => blendHeight (β p.2) D id p.1
  have hτ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ τ :=
    contMDiff_blended_height contMDiff_fst (β.contMDiff.comp contMDiff_snd)
      D.contMDiff.contDiff contDiff_id
  have hgerm (x : M) (hx : x ∈ C) :
      τ =ᶠ[𝓝 (t₀, x)] fun p => p.1 + (t₁ - t₀) := by
    have hnear : ∀ᶠ y in 𝓝 x, β y = 1 := hβone.filter_mono (nhds_le_nhdsSet hx)
    have hβ := (continuous_snd.tendsto (t₀, x)).eventually hnear
    have hD := hDgerm.comp_tendsto (continuous_fst.continuousAt (x := (t₀, x)))
    filter_upwards [hβ, hD] with p hpβ hpD
    change blendHeight (β p.2) D id p.1 = p.1 + (t₁ - t₀)
    rw [hpβ, blendHeight_one]
    exact hpD
  refine ⟨τ, hτ, ?_, ?_, hgerm, ?_⟩
  · intro x t
    have hD := (D.mdifferentiable (by simp) t).differentiableAt.hasDerivAt
    have hd : HasDerivAt (fun s => τ (s, x))
        (β x * deriv D t + (1 - β x) * 1) t := by
      simpa only [id_eq, mul_one] using hasDerivAt_blended_height
        (hasDerivAt_id t) (hasDerivAt_const t (β x)) hD (hasDerivAt_id t)
    rw [hd.deriv]
    exact positive_blended_slope (hβrange x) (hDpos t) (by norm_num)
  · intro t x h
    rcases h with hx | ht
    · have hb : β x = 0 := (hβout.filter_mono (nhds_le_nhdsSet hx)).self_of_nhds
      change blendHeight (β x) D id t = t
      rw [hb, blendHeight_zero]
      rfl
    · exact blendHeight_fixed (hDfix t ht) rfl (β x)
  · intro x hx
    have hh := (hgerm x hx).eq_of_nhds
    change τ (t₀, x) = t₀ + (t₁ - t₀) at hh
    linarith

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
