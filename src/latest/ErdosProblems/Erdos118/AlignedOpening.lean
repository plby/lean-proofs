import ErdosProblems.Erdos118.AlignedRootCounts
import ErdosProblems.Erdos118.AlignedRootPreparation

/-! The actual initial blue game supplies both positive root parameters,
the aligned critical pair, the left insertion reserve, and the saved
initial game's first-body replay on the right ordinary word. -/

namespace Erdos118.AlignedOpening

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays
open ManagedRelays (Initial)

theorem initial_critical_replay {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (hfirst : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (FirstBodyRefinement.firstLabel S).length ≠ 1)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      InsideCounts.beforeLast S = InsideCounts.beforeLast T) :
    ∃ I : Initial H B .inside, 0 < I.size ∧ ∃ P Q : Pending, ∃ a c : ℕ,
      Nonempty (RootBuffer.Reserve H I.bound I.size P.position.stem) ∧
      P.roots = [a] ∧ P.leaves = [] ∧ Q.roots = [c] ∧ Q.leaves = [] ∧
      ExactSlots.Exact (.leaf P) ∧ ExactSlots.Exact (.leaf Q) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q) ∧
      (∀ x ∈ P.position.ordinary, x ∈ H ∧ I.bound < x) ∧
      Nonempty (AlignedRootPreparation.Replay I Q) := by
  obtain ⟨k, b, hk, hroot⟩ := InsideSingleton.initial_root_setups_at_least_two hH B hB hinit
  let I : Initial H B .inside := ⟨k, b, hroot⟩
  obtain ⟨A₀, Z₀, hA₀⟩ := RootBuffer.root_reserved hH b k
  let D := ofRoot A₀
  have hD : ExactSlots.Exact (.body D) :=
    ExactSlots.step_exact (DecisionStates.Step.root A₀) trivial
  have hbD := hroot A₀ (fun x hx ↦ (hA₀ x hx).1) (fun x hx ↦ (hA₀ x hx).2)
  have hhD : LeftBlue H (GraphPayoff.payoff B .inside) (.body D, .initial) := by
    rcases blue_command (GraphPayoff.payoff B .inside) (.body D, .initial) rfl hbD with hl | hr
    · exact hl
    · obtain ⟨n, R, ha, _⟩ := hr
      simp [allowedSide] at ha
  obtain ⟨m, F, _, _, hhF, hF⟩ := respond_body hH B .inside false D .initial hhD b
  let P₀ := applyBody D F
  have hP₀ : ExactSlots.Exact (.leaf P₀) :=
    ExactSlots.step_exact (DecisionStates.Step.body D F) hD
  have hP₀root : P₀.position.stem.root = A₀.stem.root := by
    change F.position.stem.root = A₀.stem.root
    rw [F.stem_eq]
    rfl
  have hP₀label : P₀.position.stem.rootLabel = A₀.stem.rootLabel := by
    change F.position.stem.rootLabel = A₀.stem.rootLabel
    rw [F.stem_eq]
    rfl
  have hPlen : 1 < P₀.position.stem.rootLabel.length := by
    rw [hP₀label, A₀.label_length]
    omega
  have hfP₀ : ∀ x ∈ P₀.position.ordinary, x ∈ H ∧ b < x := by
    change ∀ x ∈ F.position.ordinary, x ∈ H ∧ b < x
    rw [BodyResponses.setup_ordinary]
    intro x hx
    exact (List.mem_append.mp hx).elim
      (fun hx ↦ hA₀ x (A₀.stem.ordinary_sublist.subset hx))
      (fun hx ↦ hF x (List.mem_append_right _ hx))
  obtain ⟨l, b₂, hl, hb₂⟩ :=
    AlignedRootCounts.second_root_setups hH B hB hinit hall P₀ hPlen hhF
  obtain ⟨A, Z, hA⟩ := AlignedRootReserve.root_reserved hH (max b b₂) l k hl hk
  let ZI : AlignedRootReserve.Reserve H I.bound I.size A.stem :=
    Z.weaken b (le_max_left _ _)
  have hbA := hb₂ A (fun x hx ↦ (hA x hx).1)
    (fun x hx ↦ (le_max_right _ _).trans_lt (hA x hx).2)
  have hfA : ∀ x ∈ A.stem.ordinary, x ∈ H ∧ I.bound < x := by
    intro x hx
    have hf := hA x (A.stem.ordinary_sublist.subset hx)
    exact ⟨hf.1, (le_max_left _ _).trans_lt hf.2⟩
  obtain ⟨P, Q, a, c, hPR, hPL, hQR, hQL, hP, hQ, hrun, hb, hh, hf, hrep⟩ :=
    AlignedRootPreparation.checkpoint hH Set.Subset.rfl B I hfirst hall P₀ hP₀ A ZI hfA hbA b
  obtain ⟨u, v, hu, _, huf, _⟩ := hf
  have hext := (SkippedCuts.run_extensions hrun).1
  have hPlabel : P.position.stem.rootLabel = P₀.position.stem.rootLabel :=
    Option.some.inj (hext.labels.root _ rfl)
  have hProot : P.position.stem.root = P₀.position.stem.root :=
    (List.cons_prefix_cons.mp hext.ordinary).1.symm
  let ZP := Z₀.move P.position.stem (hProot.trans hP₀root) (hPlabel.trans hP₀label)
  have hfP : ∀ x ∈ P.position.ordinary, x ∈ H ∧ I.bound < x := by
    intro x hx
    change x ∈ State.ordinary (.leaf P) at hx
    rw [hu] at hx
    exact (List.mem_append.mp hx).elim (hfP₀ x) (huf x)
  exact ⟨I, hk, P, Q, a, c, ⟨ZP⟩, hPR, hPL, hQR, hQL, hP, hQ, hb, hh, hfP, hrep⟩

end Erdos118.AlignedOpening
