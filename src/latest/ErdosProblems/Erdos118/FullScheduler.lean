import ErdosProblems.Erdos118.FrontierSteps

/-!
A complete conservative run for actual mutually projected chronological
outputs. The pending scheduler terminates by the sum of the two remaining
ordinary lengths; it never changes the ambient guard alphabet or payoff.
-/

namespace Erdos118.FullScheduler

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open CutIndices DecisionStates AdaptiveGame ClearPairs
open PreparedRelays (pair)

theorem projection_jointCuts {H : Set ℕ} (hH : H.Infinite) (s t : G2)
    (S T : Completed)
    (A : Projection (LabelledRealization.output hH s).stem
      (LabelledRealization.output hH s).full
      (LabelledRealization.output hH t).stem.ordinary S.stem S.full)
    (J : Projection (LabelledRealization.output hH t).stem
      (LabelledRealization.output hH t).full
      (LabelledRealization.output hH s).stem.ordinary T.stem T.full) :
    JointCuts S.stem S.full T.stem := by
  intro y hy hp
  apply A.cuts y (J.ordinary ▸ hy)
  simpa only [ProperBelow, A.ordinary] using hp

theorem pending {H K L : Set ℕ} (hL : L.Infinite) (hLK : L ⊆ K) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (hguard : FiniteGuards.Sparse H K (GraphPayoff.payoff B o))
    (b : ℕ) (hb : b ∈ K) (htail : ∀ x ∈ L, b < x)
    (s t : G2) (S T : Completed)
    (A : Projection (LabelledRealization.output hL s).stem
      (LabelledRealization.output hL s).full
      (LabelledRealization.output hL t).stem.ordinary S.stem S.full)
    (J : Projection (LabelledRealization.output hL t).stem
      (LabelledRealization.output hL t).full
      (LabelledRealization.output hL s).stem.ordinary T.stem T.full)
    (hclear : ClearPair S.stem T.stem) (right : Bool)
    (P Q : Pending) {a z : ℕ} (hP : JointCut P S.stem S.full a)
    (hQ : JointCut Q T.stem T.full z)
    (heP : ExactSlots.Exact (.leaf P)) (heQ : ExactSlots.Exact (.leaf Q))
    (u : List ℕ) (hsplit : S.stem.ordinary = P.position.ordinary ++ z :: u) :
    ConservativeRuns.Run H (GraphPayoff.payoff B o) (pair right (.leaf P) (.leaf Q))
      (pair right (.complete S) (.complete T)) := by
  have hSL : ∀ x ∈ S.stem.decorated, x ∈ L :=
    fun x hx ↦ LabelledRealization.output_supported hL s x (A.decorated.subset hx)
  have hTL : ∀ x ∈ T.stem.decorated, x ∈ L :=
    fun x hx ↦ LabelledRealization.output_supported hL t x (J.decorated.subset hx)
  have hSK : ∀ x ∈ S.stem.decorated, x ∈ K := fun x hx ↦ hLK (hSL x hx)
  have hTK : ∀ x ∈ T.stem.decorated, x ∈ K := fun x hx ↦ hLK (hTL x hx)
  have hbaseS : ∀ x ∈ S.stem.decorated, b < x := fun x hx ↦ htail x (hSL x hx)
  have hbaseT : ∀ x ∈ T.stem.decorated, b < x := fun x hx ↦ htail x (hTL x hx)
  have hcuts := projection_jointCuts hL s t S T A J
  obtain ⟨w, v, htsplit⟩ := FrontierSteps.split_joint T Q hQ
  by_cases hlast : P.roots = [] ∧ P.leaves = []
  · exact FrontierSteps.finish hKH (GraphPayoff.payoff B o) hguard right S T hclear
      hSK hTK b hb hbaseS hbaseT P Q hP hQ heP heQ u v w hsplit htsplit hlast.1 hlast.2
  have hadvance : ∃ F : Pending, ExactSlots.Exact (.leaf F) ∧
      JointCut F S.stem S.full w ∧
      P.position.ordinary.length < F.position.ordinary.length ∧
      ConservativeRuns.Run H (GraphPayoff.payoff B o) (pair right (.leaf P) (.leaf Q))
        (pair right (.leaf F) (.leaf Q)) := by
    cases hleaves : P.leaves with
    | cons j rest =>
      exact FrontierSteps.advance_leaf hKH (GraphPayoff.payoff B o) hguard right S T
        hclear hcuts hSK hTK b hb hbaseS P Q hP hQ heP u v w hsplit htsplit j rest hleaves
    | nil =>
      cases hroots : P.roots with
      | nil => exact (hlast ⟨hroots, hleaves⟩).elim
      | cons c rest =>
        exact FrontierSteps.advance_body hL hLK hKH B o hguard b hb htail s S T A
          hclear hcuts hTK right P Q hP hQ heP u v w hsplit htsplit c rest hroots hleaves
  obtain ⟨F, heF, hF, hlong, hrun⟩ := hadvance
  have hFlen := CutFrontiers.joint_cut_length hF
  have hrest := pending hL hLK hKH B o hguard b hb htail t s T S J A hclear.symm
    (!right) Q F hQ hF heQ heF v htsplit
  rw [FrontierSteps.pair_swap, FrontierSteps.pair_swap] at hrest
  exact hrun.trans hrest
termination_by (S.stem.ordinary.length - P.position.ordinary.length) +
  (T.stem.ordinary.length - Q.position.ordinary.length)
decreasing_by omega

theorem initial {H K L : Set ℕ} (hL : L.Infinite) (hLK : L ⊆ K) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (hguard : FiniteGuards.Sparse H K (GraphPayoff.payoff B o))
    (b : ℕ) (hb : b ∈ K) (hpos : 1 ≤ b) (htail : ∀ x ∈ L, b < x)
    (s t : G2) (S T : Completed)
    (A : Projection (LabelledRealization.output hL s).stem
      (LabelledRealization.output hL s).full
      (LabelledRealization.output hL t).stem.ordinary S.stem S.full)
    (J : Projection (LabelledRealization.output hL t).stem
      (LabelledRealization.output hL t).full
      (LabelledRealization.output hL s).stem.ordinary T.stem T.full)
    (hclear : ClearPair S.stem T.stem) (hroot : S.stem.root < T.stem.root) :
    ConservativeRuns.Run H (GraphPayoff.payoff B o) (.initial, .initial)
      (.complete S, .complete T) := by
  rcases InitialSplit.initial hL hLK hKH B o hguard b hb hpos htail s t S.stem T.stem
    S.full T.full A J hroot with hdone | ⟨P, heP, hP, hfirst⟩
  · exact hdone
  obtain ⟨z, u, hsplit⟩ := FrontierSteps.split_joint S P hP
  rcases SecondOpening.initial hL hLK hKH B o hguard b hb hpos htail s t S.stem T.stem
    S.full T.full A J hclear P hP z u hsplit with ⟨hbefore, hsecond⟩ | ⟨Q, heQ, hQ, hsecond⟩
  · have hSL : ∀ x ∈ S.stem.decorated, x ∈ L :=
      fun x hx ↦ LabelledRealization.output_supported hL s x (A.decorated.subset hx)
    have hTL : ∀ x ∈ T.stem.decorated, x ∈ L :=
      fun x hx ↦ LabelledRealization.output_supported hL t x (J.decorated.subset hx)
    have hlast := TerminalFrontiers.finish_after_complete hKH (GraphPayoff.payoff B o)
      hguard false S T hclear P hP heP z u hsplit hbefore
      (fun x hx ↦ hLK (hSL x hx)) (fun x hx ↦ hLK (hTL x hx)) b hb
      (fun x hx ↦ htail x (hSL x hx))
    exact (hfirst.trans hsecond).tail hlast
  · exact (hfirst.trans hsecond).trans
      (pending hL hLK hKH B o hguard b hb htail s t S T A J hclear false
        P Q hP hQ heP heQ u hsplit)

end Erdos118.FullScheduler
