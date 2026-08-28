import Wikipedia.HopfProblem.DegreeCollapseUniformFlowEscape
import Wikipedia.SmoothSixDPoincare.MorseCompactStability

/-!
# Constructing a no-return neighborhood from the maximal band invariant set

The full invariant set inside a closed height band is retained explicitly.
Uniform finite-time escape on the compact complement of an outer neighborhood
and a compact time-window neighborhood of the invariant set construct an
inner neighborhood. A monotone-height orbit cannot leave the outer set and
then return to the inner one.
-/

noncomputable section

open Set
open scoped Topology
open Wikipedia.SmoothSixDPoincare.MorsePerturbation

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Actual no-return neighborhoods, with no uniform time or separation margin assumed. -/
theorem exists_flow_no_return_neighborhood (F : Flow ℝ X) {f : X → ℝ}
    (hf : Continuous f) (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    {c d : ℝ} {K U : Set X} (hU : IsOpen U) (hKU : K ⊆ U)
    (hband : ∀ x ∈ K, f x ∈ Icc c d)
    (hinvariant : ∀ t x, x ∈ K → F t x ∈ K)
    (hmaximal : ∀ x, (∀ t : ℝ, f (F t x) ∈ Icc c d) → x ∈ K) :
    ∃ N : Set X, IsOpen N ∧ K ⊆ N ∧ N ⊆ U ∧
      ∀ x ∈ N, ∀ t : ℝ, 0 ≤ t → F t x ∈ N →
        ∀ s ∈ Icc (0 : ℝ) t, F s x ∈ U := by
  have hescape : ∀ x ∈ Uᶜ, ∃ t : ℝ, f (F t x) ∉ Icc c d := by
    intro x hx
    by_contra hh
    apply hx
    apply hKU
    apply hmaximal x
    intro t
    by_contra ht
    exact hh ⟨t, ht⟩
  obtain ⟨T, hT, δ, hδ, hEsc⟩ :=
    exists_uniform_flow_escape F hf hU.isClosed_compl.isCompact hescape
  let N : Set X := {x | ∀ s ∈ Icc (-T) T, F s x ∈ U} ∩ f ⁻¹' Ioo (c - δ) (d + δ)
  have hN : IsOpen N :=
    (isOpen_forall_mem_compact isCompact_Icc
      (hU.preimage (F.continuous continuous_snd continuous_fst))).inter
        (isOpen_Ioo.preimage hf)
  have hKN : K ⊆ N := by
    intro x hx
    refine ⟨fun s _ => hKU (hinvariant s x hx), ?_⟩
    have hh := hband x hx
    constructor <;> linarith [hh.1, hh.2]
  have hNU : N ⊆ U := by
    intro x hx
    have hh := hx.1 0 (show (0 : ℝ) ∈ Icc (-T) T from ⟨by linarith, hT.le⟩)
    simpa only [F.map_zero_apply] using hh
  refine ⟨N, hN, hKN, hNU, ?_⟩
  intro x hx t ht htx s hs
  by_cases hshort : s ≤ T
  · exact hx.1 s ⟨by linarith [hs.1], hshort⟩
  have hTs : T < s := lt_of_not_ge hshort
  by_cases hshort' : t - s ≤ T
  · have hh := htx.1 (s - t) (show s - t ∈ Icc (-T) T from
        ⟨by linarith, by linarith [hs.2]⟩)
    rw [← F.map_add, sub_add_cancel] at hh
    exact hh
  have hTs' : T < t - s := lt_of_not_ge hshort'
  by_contra hout
  obtain ⟨v, hv, hleave⟩ := hEsc (F s x) hout
  have htime : s + v ∈ Icc (0 : ℝ) t := ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hlo := hmono x htime.1
  have hhi := hmono x htime.2
  change f (F (s + v) x) ≤ f (F 0 x) at hlo
  change f (F t x) ≤ f (F (s + v) x) at hhi
  rw [F.map_zero_apply] at hlo
  rw [← F.map_add, add_comm v s] at hleave
  have hxheight : f x ∈ Ioo (c - δ) (d + δ) := hx.2
  have htheight : f (F t x) ∈ Ioo (c - δ) (d + δ) := htx.2
  rcases hleave with h | h
  · linarith [htheight.1]
  · linarith [hxheight.2]

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
