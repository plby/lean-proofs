import Wikipedia.HopfProblem.DegreeCollapseSublevelIndexCut
import Wikipedia.HopfProblem.DegreeCollapseSublevelFlowWindows
import Wikipedia.HopfProblem.DegreeCollapsePositiveUniqueMaximum
import Wikipedia.HopfProblem.DegreeCollapsePositiveFiberCirclePlacement

/-!
# Construct the actual dual two/three cut inside the positive half

Positive ordering of the original presentation becomes below-zero
ordering for its negation. An original index-six point supplies an actual
index-one point there. The bounded index cut stays negative and separates
the negated indices at most two from those at least three below zero.

In the original presentation this is a positive four/five cut. It meets
the already proved native circle-isotopy bounds, so that geometry can be
transferred to the negated fiber without reversing the protected half.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_negated_two_three_cut
    (horder : ∀ p q : criticalPoints (Vector 7) P.function,
      0 < P.function p → P.function p < P.function q →
        nativeMorseIndex (Vector 7) P.function p ≤ nativeMorseIndex (Vector 7) P.function q)
    (p₀ : criticalPoints (Vector 7) P.function) (hp₀ : 0 < P.function p₀)
    (hindex₀ : nativeMorseIndex (Vector 7) P.function p₀ = 6) :
    ∃ (T : AdaptedSurgeryWindows (Vector 7) (fun y => -P.function y)) (a : ℝ),
      a < 0 ∧ -P.function p₀ < a ∧
      (∀ y, -P.function y = a → y ∉ criticalPoints (Vector 7) (fun z => -P.function z)) ∧
      (∀ p : criticalPoints (Vector 7) (fun z => -P.function z),
        a ≤ -P.function p → -P.function p < 0 →
          3 ≤ nativeMorseIndex (Vector 7) (fun z => -P.function z) p) ∧
      (∀ p : criticalPoints (Vector 7) (fun z => -P.function z),
        -P.function p ≤ a → nativeMorseIndex (Vector 7) (fun z => -P.function z) p ≤ 2) ∧
      (∀ p : criticalPoints (Vector 7) (fun z => -P.function z),
        -P.function p < 0 → T.toSurgeryWindows.upper p < 0) ∧
      (∀ y, P.function y = -a → y ∉ criticalPoints (Vector 7) P.function) ∧
      (∀ p : criticalPoints (Vector 7) P.function, -a ≤ P.function p →
        5 ≤ nativeMorseIndex (Vector 7) P.function p) ∧
      ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p → P.function p ≤ -a →
        nativeMorseIndex (Vector 7) P.function p ≤ 4 := by
  let f : S.Space → ℝ := fun x => -P.function x
  have hf : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ f := P.smooth.neg
  have hm : IsMorse (Vector 7) f := isMorse_neg P.morse
  have hcrit : criticalPoints (Vector 7) f = criticalPoints (Vector 7) P.function :=
    criticalPoints_neg P.function
  have hinj : InjOn f (criticalPoints (Vector 7) f) := by
    intro x hx y hy hxy
    exact P.distinct (hcrit ▸ hx) (hcrit ▸ hy) (neg_injective hxy)
  have hsum (p : criticalPoints (Vector 7) f) :
      nativeMorseIndex (Vector 7) f p + nativeMorseIndex (Vector 7) P.function p = 7 := by
    obtain ⟨c⟩ := nonempty_signedMorseChart P.smooth P.morse p (hcrit ▸ p.property)
    simpa only [f, GLOrthonormalization.Vector, finrank_euclideanSpace_fin] using
      nativeMorseIndex_neg_add c
  have hnegorder (p q : criticalPoints (Vector 7) f) (hq : f q < 0) (hpq : f p < f q) :
      nativeMorseIndex (Vector 7) f p ≤ nativeMorseIndex (Vector 7) f q := by
    let pP : criticalPoints (Vector 7) P.function := ⟨p.val, hcrit ▸ p.property⟩
    let qP : criticalPoints (Vector 7) P.function := ⟨q.val, hcrit ▸ q.property⟩
    have hqP : 0 < P.function qP := neg_neg_iff_pos.mp hq
    have hqp : P.function qP < P.function pP := neg_lt_neg_iff.mp hpq
    have hh := horder qP pP hqP hqp
    have hpidx := hsum p
    have hqidx := hsum q
    change nativeMorseIndex (Vector 7) P.function q ≤
      nativeMorseIndex (Vector 7) P.function p at hh
    omega
  let q : criticalPoints (Vector 7) f := ⟨p₀.val, hcrit.symm ▸ p₀.property⟩
  have hqindex : nativeMorseIndex (Vector 7) f q ≤ 2 := by
    have hh := hsum q
    change nativeMorseIndex (Vector 7) f q + nativeMorseIndex (Vector 7) P.function p₀ = 7 at hh
    omega
  obtain ⟨T₀⟩ := nonempty_adaptedSurgeryWindows hf hm hinj
  obtain ⟨T, _, _, _, hupper⟩ := T₀.exists_same_flow_windows_below_cut hf hm 0
  obtain ⟨a, ha, hreg, hqa, hhigh, hlow⟩ :=
    T.exists_ordered_index_cut_below 0 hnegorder hupper q (neg_neg_of_pos hp₀) hqindex
  refine ⟨T, a, ha, hqa, hreg, hhigh, hlow, hupper, ?_, ?_, ?_⟩
  · intro y hy hcy
    exact hreg y (by change -P.function y = a; linarith) (hcrit.symm ▸ hcy)
  · intro p hp
    let pN : criticalPoints (Vector 7) f := ⟨p.val, hcrit.symm ▸ p.property⟩
    have hh := hlow pN (show -P.function p ≤ a by linarith)
    have hs := hsum pN
    change nativeMorseIndex (Vector 7) f pN + nativeMorseIndex (Vector 7) P.function p = 7 at hs
    simp only [GLOrthonormalization.Vector] at hs hh ⊢
    omega
  · intro p hp hpa
    let pN : criticalPoints (Vector 7) f := ⟨p.val, hcrit.symm ▸ p.property⟩
    have hh := hhigh pN (show a ≤ -P.function p by linarith) (neg_neg_of_pos hp)
    have hs := hsum pN
    change nativeMorseIndex (Vector 7) f pN + nativeMorseIndex (Vector 7) P.function p = 7 at hs
    simp only [GLOrthonormalization.Vector] at hs hh ⊢
    omega

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
