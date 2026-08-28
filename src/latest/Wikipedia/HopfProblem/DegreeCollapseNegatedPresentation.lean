import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenExcellentMorse
import Wikipedia.HopfProblem.DegreeCollapseNativeMorseIndexNegation

/-!
# Negate a supported sublevel replacement back onto the original state

The input changes the negated presentation only below zero, retains its
literal strict sublevel, and fixes the whole closed upper germ. Negating
back gives an excellent presentation of the SAME original state. Its
time, positive half, zero boundary, and native atlases are not reversed.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem negated_sublevel_pathConnected :
    PathConnectedSpace {x : S.Space // -P.function x ≤ 0} := by
  have hsets : {x : S.Space | -P.function x ≤ 0} = {x : S.Space | 0 ≤ S.time x} := by
    ext x
    change (-P.function x ≤ 0 ↔ 0 ≤ S.time x)
    rw [neg_nonpos]
    exact P.nonnegative_iff x
  let e : {x : S.Space // -P.function x ≤ 0} ≃ₜ S.Half :=
    Homeomorph.setCongr hsets
  exact pathConnectedSpace_of_homotopyEquiv e.toHomotopyEquiv

def replaceByNegatedSublevel (g : S.Space → ℝ)
    (hg : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ g) (hm : IsMorse (Vector 7) g)
    (hinj : InjOn g (criticalPoints (Vector 7) g))
    (hkeep : ∀ x, 0 ≤ -P.function x → g =ᶠ[𝓝 x] (fun y => -P.function y))
    (hcut : ∀ x, g x < 0 ↔ -P.function x < 0) : S.ExcellentMorsePresentation := by
  have hsign (x : S.Space) : (-g x = 0 ↔ P.function x = 0) ∧
      (0 ≤ -g x ↔ 0 ≤ P.function x) ∧ (0 < -g x ↔ 0 < P.function x) := by
    by_cases hx : 0 < P.function x
    · have hgx : 0 < -g x := neg_pos.mpr ((hcut x).mpr (neg_neg_of_pos hx))
      exact ⟨iff_of_false (ne_of_gt hgx) (ne_of_gt hx),
        iff_of_true hgx.le hx.le, iff_of_true hgx hx⟩
    · rw [(hkeep x (neg_nonneg.mpr (le_of_not_gt hx))).self_of_nhds, neg_neg]
      exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩
  have hnegative (x : S.Space) (hx : S.time x ≤ 0) :
      (fun y => -g y) =ᶠ[𝓝 x] P.function := by
    have hpx : P.function x ≤ 0 :=
      le_of_not_gt (fun h => (not_lt_of_ge hx) ((P.positive_iff x).mp h))
    filter_upwards [hkeep x (neg_nonneg.mpr hpx)] with y hy
    simp only [hy, neg_neg]
  refine {
    function := ⟨fun x => -g x, hg.continuous.neg⟩
    smooth := hg.neg
    morse := isMorse_neg hm
    regular := ?_
    zero_iff := fun x => (hsign x).1.trans (P.zero_iff x)
    nonnegative_iff := fun x => (hsign x).2.1.trans (P.nonnegative_iff x)
    positive_iff := fun x => (hsign x).2.2.trans (P.positive_iff x)
    boundary_germ := ?_
    distinct := ?_ }
  · intro x hx
    have hpx := (hsign x).1.mp hx
    change Surjective (mfderiv (𝓡 7) 𝓘(ℝ, ℝ) (fun y => -g y) x)
    rw [(hnegative x ((P.zero_iff x).mp hpx).le).mfderiv_eq]
    exact P.regular x hpx
  · intro x hx
    exact (hnegative x hx.le).trans (P.boundary_germ x hx)
  · intro x hx y hy hxy
    change x ∈ criticalPoints (Vector 7) (fun z => -g z) at hx
    change y ∈ criticalPoints (Vector 7) (fun z => -g z) at hy
    rw [criticalPoints_neg] at hx hy
    exact hinj hx hy (neg_injective hxy)

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
