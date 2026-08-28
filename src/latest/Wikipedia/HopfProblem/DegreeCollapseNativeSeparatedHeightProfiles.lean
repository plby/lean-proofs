import Wikipedia.HopfProblem.DegreeCollapseConvexHeightProfiles
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Native scalar profiles separated on the two closed basin sections

Smooth separation of disjoint closed subsets of the actual compact level
manifold gives a weight with full zero and one neighborhoods. Blending
the constructed scalar profiles retains positive height derivative,
all exterior heights, and the prescribed full translation germs on the
two selected section-height sets. No replacement level atlas is used.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N] [CompactSpace N]

theorem exists_native_separated_height_profiles {A B : Set N}
    (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B)
    {a b p p' q q' : ℝ}
    (hp : p ∈ Ioo a b) (hp' : p' ∈ Ioo a b)
    (hq : q ∈ Ioo a b) (hq' : q' ∈ Ioo a b) :
    ∃ Φ : N × ℝ → ℝ,
      ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ Φ ∧
      (∀ x s, 0 < deriv (fun t => Φ (x, t)) s) ∧
      (∀ x s, s ∉ Ioo a b → Φ (x, s) = s) ∧
      (∀ x ∈ A, Φ =ᶠ[𝓝 (x, q)] fun z => z.2 + (q' - q)) ∧
      (∀ x ∈ B, Φ =ᶠ[𝓝 (x, p)] fun z => z.2 + (p' - p)) ∧
      ∀ x s, s ∉ Ioo a b → Φ =ᶠ[𝓝 (x, s)] Prod.snd := by
  obtain ⟨θ, hθA, hθB, hθrange⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed I hA hB hAB (n := ⊤)
  obtain ⟨P, hPfix, hPgerm, -, -, hPpos, hPout⟩ :=
    exists_increasing_interval_translation_with_exterior_germs hp hp'
  obtain ⟨Q, hQfix, hQgerm, -, -, hQpos, hQout⟩ :=
    exists_increasing_interval_translation_with_exterior_germs hq hq'
  let Φ : N × ℝ → ℝ := fun z => blendHeight (θ z.1) P Q z.2
  have hΦ : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ Φ :=
    contMDiff_blended_height contMDiff_snd (θ.contMDiff.comp contMDiff_fst)
      P.contMDiff.contDiff Q.contMDiff.contDiff
  refine ⟨Φ, hΦ, ?_, ?_, ?_, ?_, ?_⟩
  · intro x s
    have hPd := (P.mdifferentiable (by simp) s).differentiableAt.hasDerivAt
    have hQd := (Q.mdifferentiable (by simp) s).differentiableAt.hasDerivAt
    have hd : HasDerivAt (fun t => Φ (x, t))
        (θ x * deriv P s + (1 - θ x) * deriv Q s) s := by
      simpa only [Φ, id_eq, mul_one] using
        hasDerivAt_blended_height (hasDerivAt_id s) (hasDerivAt_const s (θ x)) hPd hQd
    rw [hd.deriv]
    exact positive_blended_slope (hθrange x) (hPpos s) (hQpos s)
  · intro x s hs
    exact blendHeight_fixed (hPfix s hs) (hQfix s hs) (θ x)
  · intro x hx
    have hθpoint : ∀ᶠ y in 𝓝 x, θ y = 0 := hθA.filter_mono (nhds_le_nhdsSet hx)
    have hθnear : ∀ᶠ z : N × ℝ in 𝓝 (x, q), θ z.1 = 0 :=
      (continuous_fst.tendsto (x, q)).eventually hθpoint
    have hQnear : ∀ᶠ z : N × ℝ in 𝓝 (x, q), Q z.2 = z.2 + (q' - q) :=
      (continuous_snd.tendsto (x, q)).eventually hQgerm
    filter_upwards [hθnear, hQnear] with z hzθ hzQ
    change blendHeight (θ z.1) P Q z.2 = z.2 + (q' - q)
    rw [hzθ, blendHeight_zero, hzQ]
  · intro x hx
    have hθpoint : ∀ᶠ y in 𝓝 x, θ y = 1 := hθB.filter_mono (nhds_le_nhdsSet hx)
    have hθnear : ∀ᶠ z : N × ℝ in 𝓝 (x, p), θ z.1 = 1 :=
      (continuous_fst.tendsto (x, p)).eventually hθpoint
    have hPnear : ∀ᶠ z : N × ℝ in 𝓝 (x, p), P z.2 = z.2 + (p' - p) :=
      (continuous_snd.tendsto (x, p)).eventually hPgerm
    filter_upwards [hθnear, hPnear] with z hzθ hzP
    change blendHeight (θ z.1) P Q z.2 = z.2 + (p' - p)
    rw [hzθ, blendHeight_one, hzP]
  · intro x s hs
    have hPnear : ∀ᶠ z : N × ℝ in 𝓝 (x, s), P z.2 = z.2 :=
      (continuous_snd.tendsto (x, s)).eventually (hPout s hs)
    have hQnear : ∀ᶠ z : N × ℝ in 𝓝 (x, s), Q z.2 = z.2 :=
      (continuous_snd.tendsto (x, s)).eventually (hQout s hs)
    filter_upwards [hPnear, hQnear] with z hzP hzQ
    exact blendHeight_fixed hzP hzQ (θ z.1)

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
