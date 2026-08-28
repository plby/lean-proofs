import Wikipedia.HopfProblem.DegreeCollapseNegatedPresentation
import Wikipedia.HopfProblem.DegreeCollapseSublevelMinimumReduction

/-!
# Two positive maxima admit a supported reduction on the same state

Use the ORIGINAL positive half as the zero sublevel of the negated
function. Its proved connectedness supplies bounded zero/one cancellation.
Negating the result back fixes the entire original nonpositive germ and
removes two critical points, with all surviving native indices retained.
The state time and the protected half are never exchanged.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_reduction_of_two_positive_maxima
    (p₀ p₁ : criticalPoints (Vector 7) P.function)
    (hp₀ : 0 < P.function p₀) (hp₁ : 0 < P.function p₁)
    (hindex₀ : nativeMorseIndex (Vector 7) P.function p₀ = 7)
    (hindex₁ : nativeMorseIndex (Vector 7) P.function p₁ = 7) (hne : p₀ ≠ p₁) :
    ∃ Q : S.ExcellentMorsePresentation,
      (criticalPoints (Vector 7) Q.function).ncard + 2 =
        (criticalPoints (Vector 7) P.function).ncard ∧
      (∀ x ∈ criticalPoints (Vector 7) Q.function,
        x ∈ criticalPoints (Vector 7) P.function ∧
        nativeMorseIndex (Vector 7) Q.function x = nativeMorseIndex (Vector 7) P.function x) ∧
      ∀ x, S.time x ≤ 0 → Q.function =ᶠ[𝓝 x] P.function := by
  let f : S.Space → ℝ := fun x => -P.function x
  have hf : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ f := P.smooth.neg
  have hm : IsMorse (Vector 7) f := isMorse_neg P.morse
  have hcrit : criticalPoints (Vector 7) f = criticalPoints (Vector 7) P.function :=
    criticalPoints_neg P.function
  have hinj : InjOn f (criticalPoints (Vector 7) f) := by
    intro x hx y hy hxy
    exact P.distinct (hcrit ▸ hx) (hcrit ▸ hy) (neg_injective hxy)
  have hregular (x : S.Space) (hx : f x = 0) : x ∉ criticalPoints (Vector 7) f := by
    rw [hcrit]
    exact RegularTimeMorse.regular_zero_not_critical P.regular x (neg_eq_zero.mp hx)
  let p₀n : criticalPoints (Vector 7) f := ⟨p₀.val, hcrit.symm ▸ p₀.property⟩
  let p₁n : criticalPoints (Vector 7) f := ⟨p₁.val, hcrit.symm ▸ p₁.property⟩
  have hindex (p : criticalPoints (Vector 7) P.function)
      (hp : nativeMorseIndex (Vector 7) P.function p = 7) :
      nativeMorseIndex (Vector 7) f p = 0 := by
    obtain ⟨c⟩ := nonempty_signedMorseChart P.smooth P.morse p p.property
    have hs := nativeMorseIndex_neg_add c
    change nativeMorseIndex (Vector 7) (fun x => -P.function x) p = 0
    simp only [GLOrthonormalization.Vector, finrank_euclideanSpace_fin] at hs hp ⊢
    omega
  let : PathConnectedSpace {x : S.Space // f x ≤ 0} := P.negated_sublevel_pathConnected
  obtain ⟨g, hg, hmg, hinjg, hcount, hsurv, hkeep, hcut⟩ :=
    exists_reduction_of_two_minima_below_cut hf hm hinj hregular p₀n p₁n
      (neg_neg_of_pos hp₀) (neg_neg_of_pos hp₁) (hindex p₀ hindex₀) (hindex p₁ hindex₁)
      (fun h => hne (Subtype.ext
        (congrArg (fun z : criticalPoints (Vector 7) f => z.val) h)))
  let Q := P.replaceByNegatedSublevel g hg hmg hinjg hkeep hcut
  refine ⟨Q, ?_, ?_, ?_⟩
  · change (criticalPoints (Vector 7) (fun x => -g x)).ncard + 2 = _
    rw [criticalPoints_neg]
    exact hcount.trans (congrArg Set.ncard hcrit)
  · intro x hx
    change x ∈ criticalPoints (Vector 7) (fun y => -g y) at hx
    rw [criticalPoints_neg] at hx
    obtain ⟨hxf, hidx⟩ := hsurv x hx
    have hxP : x ∈ criticalPoints (Vector 7) P.function := hcrit ▸ hxf
    refine ⟨hxP, ?_⟩
    obtain ⟨cg⟩ := nonempty_signedMorseChart hg hmg x hx
    obtain ⟨cP⟩ := nonempty_signedMorseChart P.smooth P.morse x hxP
    have hsumg := nativeMorseIndex_neg_add cg
    have hsumP := nativeMorseIndex_neg_add cP
    change nativeMorseIndex (Vector 7) (fun y => -g y) x = _
    change nativeMorseIndex (Vector 7) g x =
      nativeMorseIndex (Vector 7) (fun y => -P.function y) x at hidx
    simp only [GLOrthonormalization.Vector] at hsumg hsumP hidx ⊢
    omega
  · intro x hx
    have hpx : P.function x ≤ 0 :=
      le_of_not_gt (fun h => (not_lt_of_ge hx) ((P.positive_iff x).mp h))
    change (fun y => -g y) =ᶠ[𝓝 x] P.function
    filter_upwards [hkeep x (neg_nonneg.mpr hpx)] with y hy
    change g y = -P.function y at hy
    simp only [hy, neg_neg]

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
