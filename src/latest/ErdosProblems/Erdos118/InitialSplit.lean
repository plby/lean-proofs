import ErdosProblems.Erdos118.WholeCutRun

/-!
Start the conservative decoding directly from two actual mutual projections.
Separated words give a complete run; otherwise the first joint cut and its
exact initial run are constructed, rather than supplied as hypotheses.
-/

namespace Erdos118.InitialSplit

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open CutIndices DecisionStates
open PrefixRealization (below)

theorem jointCut_of_position_eq {P F : Pending} {U : Stem}
    {hU : U.done.length = U.root} {y : ℕ} (hF : F.position = P.position)
    (hcut : JointCut P U hU y) : JointCut F U hU y := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hF]
    exact hcut.ordinary
  · rw [hF]
    exact hcut.decorated
  · refine ⟨?_, ?_⟩
    · intro C hC
      apply hcut.labels.root C
      simpa only [Frame.rootLabel, hF] using hC
    · change F.position.bodyLabels <+: U.bodyLabels
      rw [hF]
      exact hcut.labels.bodies

theorem initial {H K L : Set ℕ} (hL : L.Infinite) (hLK : L ⊆ K) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (hguard : FiniteGuards.Sparse H K (GraphPayoff.payoff B o))
    (b : ℕ) (hb : b ∈ K) (hpos : 1 ≤ b) (htail : ∀ x ∈ L, b < x)
    (s t : G2) (U V : Stem) (hU : U.done.length = U.root) (hV : V.done.length = V.root)
    (A : Projection (LabelledRealization.output hL s).stem
      (LabelledRealization.output hL s).full (LabelledRealization.output hL t).stem.ordinary U hU)
    (J : Projection (LabelledRealization.output hL t).stem
      (LabelledRealization.output hL t).full (LabelledRealization.output hL s).stem.ordinary V hV)
    (hroot : U.root < V.root) :
    ConservativeRuns.Run H (GraphPayoff.payoff B o) (.initial, .initial)
      (.complete ⟨U, hU⟩, .complete ⟨V, hV⟩) ∨
    ∃ F : Pending, ExactSlots.Exact (.leaf F) ∧ JointCut F U hU V.root ∧
      ConservativeRuns.Run H (GraphPayoff.payoff B o)
        (.initial, .initial) (.leaf F, .initial) := by
  have hUL : ∀ x ∈ U.decorated, x ∈ L :=
    fun x hx ↦ LabelledRealization.output_supported hL s x (A.decorated.subset hx)
  have hVL : ∀ x ∈ V.decorated, x ∈ L :=
    fun x hx ↦ LabelledRealization.output_supported hL t x (J.decorated.subset hx)
  have hexactUV : ExactAnnotations U V := exactAnnotations_congr_other J.ordinary
    (projection_exact (T := (LabelledRealization.output hL t).stem) A)
  by_cases hwhole : below V.root U.ordinary = U.ordinary
  · left
    have hbefore : ∀ x ∈ U.ordinary, x < V.root := by
      intro x hx
      have hm : x ∈ below V.root U.ordinary := hwhole.symm ▸ hx
      exact of_decide_eq_true (List.mem_takeWhile_imp (p := fun z ↦ decide (z < V.root)) hm)
    have hexactVU : ExactAnnotations V U := exactAnnotations_congr_other A.ordinary
      (projection_exact (T := (LabelledRealization.output hL s).stem) J)
    exact WholeCutRun.separated_run hKH (GraphPayoff.payoff B o) hguard
      ⟨U, hU⟩ ⟨V, hV⟩ hexactUV hexactVU hbefore
      (fun x hx ↦ hLK (hUL x (U.ordinary_sublist.subset hx)))
      (fun x hx ↦ hLK (hVL x (V.ordinary_sublist.subset hx))) b hb
      (fun x hx ↦ htail x (hUL x (U.ordinary_sublist.subset hx)))
      (fun x hx ↦ htail x (hVL x (V.ordinary_sublist.subset hx)))
  · right
    have hp : ProperBelow V.root U := ⟨by simp [below, Stem.ordinary, hroot], hwhole⟩
    have hpSource : ProperBelow V.root (LabelledRealization.output hL s).stem := by
      simpa only [ProperBelow, A.ordinary] using hp
    have hy : V.root ∈ (LabelledRealization.output hL t).stem.ordinary := by
      rw [J.root]
      exact List.mem_cons_self ..
    obtain ⟨P, hcut⟩ := A.cuts V.root hy hpSource
    obtain ⟨F, hF, he, hrun⟩ := FirstCutRun.initial hL hLK hKH B o hguard
      b hb hpos htail s U V hU A P hcut hexactUV
    exact ⟨F, he, jointCut_of_position_eq hF hcut, hrun⟩

end Erdos118.InitialSplit
