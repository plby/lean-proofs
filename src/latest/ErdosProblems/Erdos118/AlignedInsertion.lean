import ErdosProblems.Erdos118.AlignedOpening
import ErdosProblems.Erdos118.AlignedRightPreparation

/-! An inserted initial game reaches the aligned critical checkpoint.
The entire inserted left suffix exceeds the old saved bound, and the
right word has an actual replay against the fixed third-game word. -/

namespace Erdos118.AlignedInsertion

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays
open ManagedRelays (Initial)
open AlignedRightPreparation (RootCertificate Replay)

theorem inserted_checkpoint {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      InsideCounts.beforeLast S = InsideCounts.beforeLast T)
    (I : Initial H B .inside) (hk : 0 < I.size)
    (P T₁ : Pending) (c : ℕ) (hPR : P.roots = [c])
    (hP : ExactSlots.Exact (.leaf P)) (Z : RootBuffer.Reserve H I.bound I.size P.position.stem)
    (hOrd : ∀ x ∈ P.position.ordinary, x ∈ H ∧ I.bound < x)
    (hTlen : 1 < T₁.position.stem.rootLabel.length)
    (hTright : RightBlue H (GraphPayoff.payoff B .inside) (.leaf T₁, .initial)) (d : ℕ) :
    ∃ J : RootCertificate H B T₁, 0 < J.size ∧ ∃ R U : Pending, ∃ f : ℕ,
      R.roots = [c] ∧ R.leaves = [] ∧ U.roots = [f] ∧ U.leaves = [] ∧
      ExactSlots.Exact (.leaf R) ∧ ExactSlots.Exact (.leaf U) ∧
      R.position.stem.root = P.position.stem.root ∧ R.position.stem.rootLabel = Z.label ∧
      (∃ v : List ℕ, R.position.ordinary = P.position.ordinary ++ v ∧
        ∀ x ∈ v, x ∈ H ∧ d < x) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf R, .leaf U)) true ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf R, .leaf U) ∧
      Nonempty (Replay J U) := by
  obtain ⟨A, v, hAord, hAroot, hAlabel, hv, hAfresh⟩ := Z.buffer hH P hP hPR hOrd d
  let D := ofRoot A
  have hD : ExactSlots.Exact (.body D) :=
    ExactSlots.step_exact (DecisionStates.Step.root A) trivial
  have hbD := I.rootBlue A (fun x hx ↦ (hAfresh x hx).1) (fun x hx ↦ (hAfresh x hx).2)
  have hcD : LeftBlue H (GraphPayoff.payoff B .inside) (.body D, .initial) := by
    rcases blue_command (GraphPayoff.payoff B .inside) (.body D, .initial) rfl hbD with hl | hr
    · exact hl
    · obtain ⟨n, R, hs, _⟩ := hr
      simp [allowedSide] at hs
  let K := H \ Set.Iic d
  have hK : K.Infinite := hH.sdiff (Set.finite_Iic d)
  have hKH : K ⊆ H := fun _ hx ↦ hx.1
  obtain ⟨m, A₁, _, _, hh₁, hA₁⟩ := respond_body_on hK hKH B .inside false D .initial hcD d
  let S := applyBody D A₁
  have hS : ExactSlots.Exact (.leaf S) :=
    ExactSlots.step_exact (DecisionStates.Step.body D A₁) hD
  have hSroot : S.position.stem.root = P.position.stem.root := by
    change A₁.position.stem.root = _
    rw [A₁.stem_eq]
    exact hAroot
  have hSlabel : S.position.stem.rootLabel = Z.label := by
    change A₁.position.stem.rootLabel = _
    rw [A₁.stem_eq]
    exact hAlabel
  have hSlen : 1 < S.position.stem.rootLabel.length := by
    rw [hSlabel, Z.card]
    omega
  have hfS : ∃ w : List ℕ, S.position.ordinary = P.position.ordinary ++ w ∧
      ∀ x ∈ w, x ∈ H ∧ d < x := by
    refine ⟨v ++ A₁.position.size :: A₁.position.entries, ?_, ?_⟩
    · change A₁.position.ordinary = _
      rw [BodyResponses.setup_ordinary]
      change A.stem.ordinary ++ A₁.position.size :: A₁.position.entries = _
      rw [hAord, List.append_assoc]
    · intro x hx
      exact (List.mem_append.mp hx).elim (hv x)
        (fun hx ↦ ⟨hKH (hA₁ x (List.mem_append_right _ hx)).1,
          (hA₁ x (List.mem_append_right _ hx)).2⟩)
  obtain ⟨l, bT, hl, hbT⟩ :=
    AlignedRootCounts.second_root_setups hH B hB hinit hall T₁ hTlen hTright
  let J : RootCertificate H B T₁ := ⟨l, bT, hbT⟩
  obtain ⟨kU, bU, hkU, hbU⟩ :=
    AlignedRootCounts.second_root_setups hH B hB hinit hall S hSlen hh₁
  let M := max bT (max bU d)
  obtain ⟨Aᵤ, Zᵤ, hAᵤ⟩ := AlignedRootReserve.root_reserved hH M kU l hkU hl
  let ZJ : AlignedRootReserve.Reserve H J.bound J.size Aᵤ.stem :=
    Zᵤ.weaken bT (le_max_left _ _)
  have hstart := hbU Aᵤ (fun x hx ↦ (hAᵤ x hx).1)
    (fun x hx ↦ ((le_max_left bU d).trans (le_max_right bT _)).trans_lt (hAᵤ x hx).2)
  have hfAᵤ : ∀ x ∈ Aᵤ.stem.ordinary, x ∈ H ∧ J.bound < x := by
    intro x hx
    have h := hAᵤ x (Aᵤ.stem.ordinary_sublist.subset hx)
    exact ⟨h.1, (le_max_left _ _).trans_lt h.2⟩
  obtain ⟨R, U, c', f, hRR, hRL, hUR, hUL, hR, hU, hrun, hb, hh, hf, hrep⟩ :=
    AlignedRightPreparation.checkpoint hK hKH B T₁ J hall S hS Aᵤ ZJ hfAᵤ hstart d
  have hext := (SkippedCuts.run_extensions hrun).1
  have hRlabel : R.position.stem.rootLabel = Z.label :=
    (Option.some.inj (hext.labels.root _ rfl)).trans hSlabel
  have hRroot : R.position.stem.root = P.position.stem.root :=
    (List.cons_prefix_cons.mp hext.ordinary).1.symm.trans hSroot
  have hcc : c' = c := by
    have h := ExactSlots.pending_next_last_root R hR hRR
    rw [hRlabel, Z.sameLast, ExactSlots.pending_next_last_root P hP hPR] at h
    exact h.symm
  subst c'
  obtain ⟨w, hw, hwf⟩ := hfS
  obtain ⟨z, _, hz, _, hzf, _⟩ := hf
  refine ⟨J, hl, R, U, f, hRR, hRL, hUR, hUL, hR, hU, hRroot, hRlabel, ?_, hb, hh, hrep⟩
  refine ⟨w ++ z, ?_, ?_⟩
  · change R.position.ordinary = S.position.ordinary ++ z at hz
    rw [hz, hw, List.append_assoc]
  · intro x hx
    exact (List.mem_append.mp hx).elim (hwf x)
      (fun hx ↦ ⟨hKH (hzf x hx).1, (hzf x hx).2⟩)

end Erdos118.AlignedInsertion
