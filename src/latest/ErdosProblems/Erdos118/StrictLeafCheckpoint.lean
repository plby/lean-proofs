import ErdosProblems.Erdos118.SelectedLeafCheckpoint
import ErdosProblems.Erdos118.StrictEndpoint
import ErdosProblems.Erdos118.LabelRanks

/-! Reach the localized critical leaf in an actual run and recover the
simultaneous penultimate left endpoint from exact suffix balance. -/

namespace Erdos118.StrictLeafCheckpoint

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open BlueRuns InsideCounts LastBodyRefinement CriticalPair

structure Reached (K H : Set ℕ) (B : SimpleGraph G) (P Q : Pending) (j d : ℕ) where
  left : Pending
  right : Pending
  sameBody : CurrentBody.SameBody Q right
  leftExact : ExactSlots.Exact (.leaf left)
  rightExact : ExactSlots.Exact (.leaf right)
  index : right.position.entries.length = j
  run : ConservativeRuns.Run K (GraphPayoff.payoff B .inside)
    (.leaf P, .leaf Q) (.leaf left, .leaf right)
  blue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf left, .leaf right)) true
  command : LeftBlue H (GraphPayoff.payoff B .inside) (.leaf left, .leaf right)
  fresh : FreshCheckpoints.FreshExtension K d (.leaf P, .leaf Q) (.leaf left, .leaf right)
  before : ∀ x ∈ left.position.decorated, x < right.position.ordinary.getLastD 0
  order : left.position.ordinary.getLastD 0 < right.position.ordinary.getLastD 0
  criticalLeft : ∃ c : ℕ, left.roots = [c] ∧ left.leaves = []
  futureRoots : right.roots ≠ []
  twoRoots : right.leaves = [] → 2 ≤ right.roots.length
  criticalPair : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
    SkippedCuts.StateExtension (.leaf left) (.complete S) →
    SkippedCuts.StateExtension (.leaf right) (.complete T) →
    CriticalPair.pair T.stem (lastLabel S).length =
      ⟨right.position.stem.done.length, right.position.entries.length⟩

theorem right {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S < beforeLast T)
    (P Q : Pending) (hP : ExactSlots.Exact (.leaf P)) (hQ : ExactSlots.Exact (.leaf Q))
    (hPlen : 1 < P.position.stem.rootLabel.length) (j value d : ℕ)
    (hj : j ∈ Q.position.label) (hij : Q.position.entries.length ≤ j)
    (hrank : LabelRanks.rank Q.position.label j = value)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true)
    (hcommand : LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q))
    (hbefore : ∀ x ∈ P.position.decorated, x < Q.position.ordinary.getLastD 0)
    (hbody : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      SkippedCuts.StateExtension (.leaf P) (.complete S) →
      SkippedCuts.StateExtension (.leaf Q) (.complete T) →
      (CriticalPair.pair T.stem (lastLabel S).length).1 = Q.position.stem.done.length)
    (hcolor : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      SkippedCuts.StateExtension (.leaf P) (.complete S) →
      SkippedCuts.StateExtension (.leaf Q) (.complete T) →
      leafRank T.stem (lastLabel S).length = value) :
    Nonempty (Reached K H B P Q j d) := by
  have hH := hK.mono hKH
  obtain ⟨V, Y, hsame, hV, hvj, hrun, hb, hh, hf, hentry⟩ :=
    SelectedLeafCheckpoint.right_entry hK hKH B .inside Q hQ (.leaf P) j d hj hij
      hblue (fun _ ↦ hcommand)
  have hnobody : ∀ D : BodyDecision, Y ≠ .body D := by
    rcases hentry with he | he
    · have hY : Y = .leaf P := congrArg Prod.fst he
      simp [hY]
    · exact he.1
  have hY : ∃ U : Pending, Y = .leaf U := by
    cases Y with
    | initial =>
      have hlen := (SkippedCuts.run_extensions hrun).1.ordinary.length_le
      simp [State.ordinary, Position.ordinary, Stem.ordinary] at hlen
    | body D => exact (hnobody D rfl).elim
    | complete S =>
      exact (InsideEndgame.complete_incomplete_not_blue hH B S (.leaf V) (by simp) hb).elim
    | leaf U => exact ⟨U, rfl⟩
  obtain ⟨U, rfl⟩ := hY
  have hU := ExactSlots.run_exact_left hrun hP
  obtain ⟨heP, heQ⟩ := SkippedCuts.run_extensions hrun
  have hUV : ∀ x ∈ U.position.decorated, x < V.position.ordinary.getLastD 0 := by
    rcases hentry with he | he
    · have hUeq := State.leaf.inj (congrArg Prod.fst he)
      have hVeq := State.leaf.inj (congrArg Prod.snd he)
      simpa only [hUeq, hVeq] using hbefore
    · exact he.2
  have horder : U.position.ordinary.getLastD 0 < V.position.ordinary.getLastD 0 := by
    apply hUV
    apply U.position.ordinary_sublist.subset
    have hne : U.position.ordinary ≠ [] := by simp [Position.ordinary, Stem.ordinary]
    simpa only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne,
      Option.getD_some] using List.getLast_mem hne
  have hcanonical : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      SkippedCuts.StateExtension (.leaf U) (.complete S) →
      SkippedCuts.StateExtension (.leaf V) (.complete T) →
      CriticalPair.pair T.stem (lastLabel S).length =
        ⟨V.position.stem.done.length, V.position.entries.length⟩ := by
    intro S T hp heU heV
    have heS := heP.trans heU
    have heT := heQ.trans heV
    have hSroot : S.stem.rootLabel = P.position.stem.rootLabel :=
      Option.some.inj (heS.labels.root _ rfl)
    have hSL : 1 < S.stem.rootLabel.length := hSroot ▸ hPlen
    obtain ⟨_, hspec, _, _, _, _⟩ := StrictCriticalBounds.terminal B S T hp hSL (hall S T hp)
    have hindex : (CriticalPair.pair T.stem (lastLabel S).length).1 =
        V.position.stem.done.length := by
      rw [hsame.stem]
      exact hbody S T hp heS heT
    have hlabel := CriticalCursor.current_label V T heV
    have hmem : (CriticalPair.pair T.stem (lastLabel S).length).2 ∈ V.position.label := by
      have hm := (Finset.mem_sigma.mp hspec.1).2
      rw [hindex, hlabel] at hm
      exact List.mem_toFinset.mp hm
    have hval := hcolor S T hp heS heT
    change LabelRanks.rank (T.stem.bodyLabels.getD
      (CriticalPair.pair T.stem (lastLabel S).length).1 [])
      (CriticalPair.pair T.stem (lastLabel S).length).2 = value at hval
    rw [hindex, hlabel] at hval
    have hrankV : LabelRanks.rank V.position.label V.position.entries.length = value := by
      rw [hsame.label, hvj]
      exact hrank
    have hleaf := LabelRanks.rank_injective hmem V.leafSelected (hval.trans hrankV.symm)
    exact Sigma.ext hindex (heq_of_eq hleaf)
  obtain ⟨S, T, hp, heU, heV, hbalance⟩ :=
    PendingSuffixBalance.exists_completion hH B U V horder hb
  have heS := heP.trans heU
  have hSroot : S.stem.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (heS.labels.root _ rfl)
  obtain ⟨_, hspec, _, _, _, _⟩ := StrictCriticalBounds.terminal B S T hp
    (hSroot ▸ hPlen) (hall S T hp)
  have hpair := hcanonical S T hp heU heV
  rw [hpair] at hspec
  have hcount : (LeafSuffixCounts.remaining T.stem
      V.position.stem.done.length V.position.entries.length).card = (lastLabel S).length := hspec.2
  have hc := ((GraphPayoff.payoff_true_iff B .inside S T).mp hp).2.1
  have hleft : ∃ c : ℕ, U.roots = [c] ∧ U.leaves = [] :=
    (PendingEndpointCounts.criterion U S T.stem hc.exactLeft hU heU).mp (by omega)
  obtain ⟨hroots, htwo⟩ := StrictEndpoint.future_roots hH B hall U V hU hV hleft horder hb
  exact ⟨{
    left := U, right := V, sameBody := hsame, leftExact := hU, rightExact := hV, index := hvj
    run := hrun, blue := hb, command := hh, fresh := hf, before := hUV, order := horder
    criticalLeft := hleft, futureRoots := hroots, twoRoots := htwo, criticalPair := hcanonical }⟩

end Erdos118.StrictLeafCheckpoint
