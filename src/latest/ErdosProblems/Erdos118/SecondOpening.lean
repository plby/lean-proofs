import ErdosProblems.Erdos118.OpeningRun

/-!
Open the second actual projected word after the first pending cut. Either
it finishes as a whole response or reaches its first proper joint cut.
-/

namespace Erdos118.SecondOpening

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open CutIndices DecisionStates AdaptiveGame ClearPairs
open PrefixRealization (below)

theorem initial {H K L : Set ℕ} (hL : L.Infinite) (hLK : L ⊆ K) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (hguard : FiniteGuards.Sparse H K (GraphPayoff.payoff B o))
    (b : ℕ) (hb : b ∈ K) (hpos : 1 ≤ b) (htail : ∀ x ∈ L, b < x)
    (s t : G2) (U V : Stem) (hU : U.done.length = U.root) (hV : V.done.length = V.root)
    (A : Projection (LabelledRealization.output hL s).stem
      (LabelledRealization.output hL s).full (LabelledRealization.output hL t).stem.ordinary U hU)
    (J : Projection (LabelledRealization.output hL t).stem
      (LabelledRealization.output hL t).full (LabelledRealization.output hL s).stem.ordinary V hV)
    (hclear : ClearPair U V) (P : Pending) (hP : JointCut P U hU V.root)
    (z : ℕ) (u : List ℕ) (hsplit : U.ordinary = P.position.ordinary ++ z :: u) :
    ((∀ x ∈ V.ordinary, x < z) ∧
      ConservativeRuns.Run H (GraphPayoff.payoff B o) (.leaf P, .initial)
        (.leaf P, .complete ⟨V, hV⟩)) ∨
    ∃ Q : Pending, ExactSlots.Exact (.leaf Q) ∧ JointCut Q V hV z ∧
      ConservativeRuns.Run H (GraphPayoff.payoff B o) (.leaf P, .initial) (.leaf P, .leaf Q) := by
  have hzU : z ∈ U.ordinary := by
    rw [hsplit]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  have hbP := below_split_bounds V.root P.position.ordinary (z :: u)
    (hsplit ▸ U.increasing.sublist U.ordinary_sublist) (by rw [← hsplit]; exact hP.ordinary.symm)
  have hrootz : V.root < z := Nat.lt_of_le_of_ne (hbP.2 z (List.mem_cons_self ..))
    (foreign_ne hclear.disjoint (List.mem_cons_self ..) (U.ordinary_sublist.subset hzU))
  have hUL : ∀ x ∈ U.decorated, x ∈ L :=
    fun x hx ↦ LabelledRealization.output_supported hL s x (A.decorated.subset hx)
  have hVL : ∀ x ∈ V.decorated, x ∈ L :=
    fun x hx ↦ LabelledRealization.output_supported hL t x (J.decorated.subset hx)
  have hPL : ∀ x ∈ P.position.decorated, x ∈ L := by
    intro x hx
    apply hUL x
    apply (List.takeWhile_sublist (fun a ↦ decide (a < V.root))).subset
    change x ∈ below V.root U.decorated
    exact hP.decorated ▸ hx
  have hbefore : ∀ x ∈ P.position.decorated, ∀ y ∈ V.decorated, x < y := by
    intro x hx y hy
    obtain ⟨w, hw, hxw⟩ := DecoratedFrontiers.position_dominated P.position x hx
    have hwU : w ∈ U.ordinary := by
      rw [hsplit]
      exact List.mem_append_left _ hw
    apply hxw.trans_lt
    apply DecoratedFrontiers.whole_after_foreign V U hclear.separatedRight w hwU _ y hy
    intro a ha
    have hroota : V.root ≤ a := by
      have hp := (V.increasing.sublist V.ordinary_sublist).imp Nat.le_of_lt
      simpa only [Stem.ordinary, List.head_cons] using hp.rel_head ha
    exact (hbP.1 w hw).trans_le hroota
  by_cases hwhole : below z V.ordinary = V.ordinary
  · left
    have hVz : ∀ x ∈ V.ordinary, x < z := by
      intro x hx
      have hm : x ∈ below z V.ordinary := hwhole.symm ▸ hx
      exact of_decide_eq_true (List.mem_takeWhile_imp (p := fun a ↦ decide (a < z)) hm)
    have hno : ∀ i j, ¬ Cut V U i j := by
      rintro i j ⟨w, hw, hp, _⟩
      rw [hsplit] at hw
      rcases List.mem_append.mp hw with hw | hw
      · apply hp.1
        simp [below, Stem.ordinary, Nat.not_lt.mpr (hbP.1 w hw).le]
      · have htailInc := (List.pairwise_append.mp
          (hsplit ▸ U.increasing.sublist U.ordinary_sublist)).2.1
        have hzw : z ≤ w := by
          simpa only [List.head_cons] using (htailInc.imp Nat.le_of_lt).rel_head hw
        exact hp.2 (PrefixRealization.below_eq_self w V.ordinary
          (fun x hx ↦ (hVz x hx).trans_le hzw))
    obtain ⟨hroot, hbodies⟩ := WholeCutRun.annotations_empty_of_no_cuts V U hclear.exactRight hno
    have hs := WholeCutRun.whole_step hKH (GraphPayoff.payoff B o) hguard true (.leaf P)
      ⟨V, hV⟩ rfl hroot hbodies (fun x hx ↦ hLK (hPL x hx))
      (fun x hx ↦ hLK (hVL x (V.ordinary_sublist.subset hx))) b hb
      (fun x hx ↦ htail x (hVL x (V.ordinary_sublist.subset hx)))
      (fun x hx y hy ↦ hbefore x hx y (V.ordinary_sublist.subset hy))
    exact ⟨hVz, Relation.ReflTransGen.single hs⟩
  · right
    have hp : ProperBelow z V := ⟨by simp [below, Stem.ordinary, hrootz], hwhole⟩
    have hpSource : ProperBelow z (LabelledRealization.output hL t).stem := by
      simpa only [ProperBelow, J.ordinary] using hp
    have hzSource : z ∈ (LabelledRealization.output hL s).stem.ordinary := A.ordinary ▸ hzU
    obtain ⟨Q, hQ⟩ := J.cuts z hzSource hpSource
    have hmin := OpeningFronts.cut_minimal_of_split V U hV Q z hQ P.position.ordinary u
      hsplit hbP.1
    obtain ⟨F, hF, he, hrun⟩ := OpeningRun.initial hL hLK hKH B o hguard
      b hb hpos htail t V U hV J Q hQ hclear.exactRight hmin true (.leaf P) rfl
      (fun x hx ↦ hLK (hPL x hx)) hbefore
    exact ⟨F, he, InitialSplit.jointCut_of_position_eq hF hQ, hrun⟩

end Erdos118.SecondOpening
