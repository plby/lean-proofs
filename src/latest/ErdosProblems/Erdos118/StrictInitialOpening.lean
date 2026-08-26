import ErdosProblems.Erdos118.StrictReservedLeafOpening
import ErdosProblems.Erdos118.InsideSingleton
import ErdosProblems.Erdos118.RootBuffer

/-! Construct the reserved strict two-game opening from the actual
initial blue hypothesis, retaining the left insertion reserve. -/

namespace Erdos118.StrictInitialOpening

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays InsideCounts
open ManagedRelays (Initial)

structure Opening (H : Set ℕ) (B : SimpleGraph G) where
  initial : Initial H B .inside
  positive : 0 < initial.size
  first : Pending
  firstExact : ExactSlots.Exact (.leaf first)
  firstRoot : 1 < first.position.stem.rootLabel.length
  alphabet : Set ℕ
  subset : alphabet ⊆ H
  infinite : alphabet.Infinite
  graph : SimpleGraph G
  subgraph : graph ≤ B
  triangleFree : graph.CliqueFree 3
  rootSize : ℕ
  rank : ℕ
  rootSetup : RootResponses.Setup rootSize
  prepared : StrictLocalization.Prepared alphabet graph first rootSetup rank initial.bound
  reserve : RankedRootReserve.Reserve H initial.bound rootSize initial.size rank prepared.body.stem
  target : RankedRootPreparation.Target initial prepared.body reserve
  opening : StrictReservedLeafOpening.Opening prepared target initial.bound
  buffer : RootBuffer.Reserve H initial.bound initial.size opening.checkpoint.left.position.stem
  freshLeft : ∀ x ∈ opening.checkpoint.left.position.ordinary, x ∈ H ∧ initial.bound < x

theorem exists_opening {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (hfirst : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (FirstBodyRefinement.firstLabel S).length ≠ 1)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S < beforeLast T) : Nonempty (Opening H B) := by
  obtain ⟨k, b, hk, hroot⟩ := InsideSingleton.initial_root_setups_at_least_two hH B hB hinit
  let I : Initial H B .inside := ⟨k, b, hroot⟩
  obtain ⟨A₀, R₀, hA₀⟩ := RootBuffer.root_reserved hH b k
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
  obtain ⟨n, K, hKH, hK, C, hCB, hC, _, v, hv, hvn, b₂, hcert, _, hcolor⟩ :=
    StrictBodyLocalization.exists_root hH B hB hinit hall P₀ hPlen hhF
  obtain ⟨A, R, hA⟩ := RankedRootReserve.root_reserved hK (max b b₂) n k v hv hvn hk
  let RI : RankedRootReserve.Reserve H I.bound n I.size v A.stem :=
    R.rebase hKH (le_max_left _ _)
  have hbA := hcert A (fun x hx ↦ (hA x hx).1)
    (fun x hx ↦ (le_max_right _ _).trans_lt (hA x hx).2)
  have hfA : ∀ x ∈ A.stem.ordinary, x ∈ H ∧ I.bound < x := by
    intro x hx
    have hf := hA x (A.stem.ordinary_sublist.subset hx)
    exact ⟨hKH hf.1, (le_max_left _ _).trans_lt hf.2⟩
  have hstrict : ∀ S T, GraphPayoff.payoff C .inside S T = true → beforeLast S < beforeLast T :=
    fun S T hp ↦ hall S T (LastMarkerRefinement.payoff_true_mono hCB .inside S T hp)
  obtain ⟨Z⟩ := StrictLocalization.at_root hK C hC hstrict P₀ hP₀ hPlen n v hv hvn.le
    (fun S T hp hS hT ↦ (hcolor S T hp hS hT).1) A hbA I.bound
  obtain ⟨RD, _, ht⟩ := RankedRootPreparation.at_localized hKH I hfirst Z RI le_rfl hfA
  obtain ⟨T⟩ := ht
  obtain ⟨O⟩ := StrictReservedLeafOpening.exists_opening hKH Z T hPlen hstrict I.bound
  have he₀ := (SkippedCuts.run_extensions Z.run).1
  have he₁ := (SkippedCuts.run_extensions O.sourceRun).1
  have heP := he₀.trans he₁
  have hProot : O.checkpoint.left.position.stem.root = P₀.position.stem.root :=
    (List.cons_prefix_cons.mp heP.ordinary).1.symm
  have hPlabel : O.checkpoint.left.position.stem.rootLabel = P₀.position.stem.rootLabel :=
    Option.some.inj (heP.labels.root _ rfl)
  let RP := R₀.move O.checkpoint.left.position.stem (hProot.trans hP₀root) (hPlabel.trans hP₀label)
  have hfP : ∀ x ∈ O.checkpoint.left.position.ordinary, x ∈ H ∧ I.bound < x := by
    obtain ⟨u, w, hu, _, huf, _⟩ := Z.fresh
    obtain ⟨z, t, hz, _, hzf, _⟩ := O.sourceFresh
    intro x hx
    change x ∈ State.ordinary (.leaf O.checkpoint.left) at hx
    rw [hz, hu, List.append_assoc] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hfP₀ x hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact ⟨hKH (huf x hx).1, (huf x hx).2⟩
      · exact ⟨hKH (Z.subset (hzf x hx).1), (hzf x hx).2⟩
  exact ⟨{
    initial := I, positive := hk, first := P₀, firstExact := hP₀, firstRoot := hPlen
    alphabet := K, subset := hKH, infinite := hK, graph := C, subgraph := hCB, triangleFree := hC
    rootSize := n, rank := v, rootSetup := A, prepared := Z, reserve := RD, target := T
    opening := O, buffer := RP, freshLeft := hfP }⟩

end Erdos118.StrictInitialOpening
