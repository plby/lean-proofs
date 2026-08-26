import ErdosProblems.Erdos118.FrameAnchors

/-!
The actual creation edges and numerical bounds of projected labels in the
chronological realization. No conservative pair history is assumed or asserted.
-/

namespace Erdos118.LabelOrigins

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelledRealization
open PrefixRealization (Phase run_append live_of_next_ne_dead live_ne_dead)

private theorem run_root_only_nil (p : List ℕ) (h : Phase.root.run p = .root) : p = [] := by
  have hnext : ∀ (q : Phase) (a : ℕ), q.next a ≠ .root := by
    intro q a
    cases q with
    | root => simp [Phase.next]
    | pending r l => cases r <;> cases l <;> simp [Phase.next]
    | terminal => simp [Phase.next]
    | dead => simp [Phase.next]
  cases p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p a =>
    rw [run_append] at h
    exact (hnext _ _ h).elim

theorem output_root_label_length {K : Set ℕ} (hK : K.Infinite) (s : G2) :
    (output hK s).stem.rootLabel.length = s.length + 1 := by
  obtain ⟨C, hC, hlen⟩ := (frame_budget hK [] s.length).root (frame_nil hK)
  have hp : [s.length] <+: word s ++ [0] :=
    ⟨s.flatMap levelWord ++ [0], rfl⟩
  have he := (frame_prefix hK hp (by simp [PrefixRealization.run_word_terminal])).labels.root C hC
  rw [← output_frame] at he
  change some (output hK s).stem.rootLabel = some C at he
  rw [Option.some.inj he]
  exact hlen

private theorem rootLabel_mem (F : Frame) (C : List ℕ) (hC : F.rootLabel = some C) :
    ∀ x ∈ C, x ∈ F.decorated := by
  cases F with
  | initial => simp [Frame.rootLabel] at hC
  | dead => simp [Frame.rootLabel] at hC
  | pending P =>
    have he : P.position.stem.rootLabel = C := Option.some.inj hC
    intro x hx
    rw [← he] at hx
    simp [Frame.decorated, Position.decorated, Stem.decorated, hx]
  | terminal S hS =>
    have he : S.rootLabel = C := Option.some.inj hC
    intro x hx
    rw [← he] at hx
    simp [Frame.decorated, Stem.decorated, hx]

theorem output_root_label_block {K : Set ℕ} (hK : K.Infinite) (s : G2) :
    ∀ x ∈ (output hK s).stem.rootLabel, x ∈ decoratedBlock hK [] s.length := by
  obtain ⟨C, hC, _⟩ := (frame_budget hK [] s.length).root (frame_nil hK)
  have hp : [s.length] <+: word s ++ [0] :=
    ⟨s.flatMap levelWord ++ [0], rfl⟩
  have he := (frame_prefix hK hp (by simp [PrefixRealization.run_word_terminal])).labels.root C hC
  rw [← output_frame] at he
  change some (output hK s).stem.rootLabel = some C at he
  rw [Option.some.inj he]
  simpa [decoratedBlock, Frame.decorated] using rootLabel_mem _ C hC

theorem output_root_projected_command {K L : Set ℕ} (hL : L.Infinite) (hLK : L ⊆ K)
    (b : ℕ) (hb : b ∈ K) (hpos : 1 ≤ b) (htail : ∀ x ∈ L, b < x)
    (s : G2) (C : List ℕ) (hC : C.Sublist (output hL s).stem.rootLabel) :
    ∃ q ∈ K, C.length ≤ q ∧ ∀ x ∈ C, q < x := by
  have hlen : C.length ≤ s.length + 1 :=
    hC.length_le.trans_eq (output_root_label_length hL s)
  cases hs : s.length with
  | zero =>
    refine ⟨b, hb, ?_, ?_⟩
    · rw [hs] at hlen
      exact hlen.trans hpos
    · intro x hx
      exact htail x (output_supported hL s x (List.mem_append_left _ (hC.subset hx)))
  | succ a =>
    obtain ⟨q, hq, hqa, hqx⟩ := FrameAnchors.root_sibling_anchor hL a
    refine ⟨q, hLK hq, ?_, ?_⟩
    · rw [hs] at hlen
      exact hlen.trans hqa
    · intro x hx
      apply hqx x
      simpa only [hs] using output_root_label_block hL s x (hC.subset hx)

theorem frame_body_origin {K : Set ℕ} (hK : K.Infinite) (p : List ℕ)
    (hp : Phase.root.run p ≠ .dead) (D : List ℕ) (hD : D ∈ (frame hK p).bodyLabels)
    (hne : D ≠ []) :
    ∃ q : List ℕ, ∃ a : ℕ, q ++ [a] <+: p ∧ (Phase.root.run q).live ∧
      (Phase.root.run q = .root ∨ ∃ r : ℕ, Phase.root.run q = .pending (r + 1) 0) ∧
      D.length ≤ a + 1 ∧ ∀ x ∈ D, x ∈ decoratedBlock hK q a := by
  induction p using List.reverseRecOn with
  | nil => simp [Frame.bodyLabels] at hD
  | append_singleton p a ih =>
    have hnext : (Phase.root.run p).next a ≠ .dead := by
      simpa only [run_append, Phase.run] using hp
    have hlive := live_of_next_ne_dead _ _ hnext
    have hs := block_spec hK p a hlive
    obtain ⟨rest, hrest⟩ := hs.labels.bodies
    rw [← hrest] at hD
    rcases List.mem_append.mp hD with hD | hD
    · obtain ⟨q, c, hqp, hq, hphase, hlen, hblock⟩ := ih (live_ne_dead _ hlive) hD
      exact ⟨q, c, hqp.trans (List.prefix_append p [a]), hq, hphase, hlen, hblock⟩
    · have hnew : D ∈ (frame hK (p ++ [a])).bodyLabels.drop (frame hK p).bodyLabels.length := by
        rw [← hrest, List.drop_append_of_le_length le_rfl, List.drop_length, List.nil_append]
        exact hD
      have hb := frame_budget hK p a
      refine ⟨p, a, List.prefix_rfl, hlive, ?_, hb.bodies D hnew, hb.bodyFresh D hnew⟩
      simpa only [frame_phase] using hb.bodyPhase D hnew hne

theorem output_body_label_origin {K : Set ℕ} (hK : K.Infinite) (s : G2)
    (D : List ℕ) (hD : D ∈ (output hK s).stem.bodyLabels) (hne : D ≠ []) :
    ∃ p : List ℕ, ∃ a : ℕ, p ++ [a] <+: word s ++ [0] ∧ (Phase.root.run p).live ∧
      (Phase.root.run p = .root ∨ ∃ r : ℕ, Phase.root.run p = .pending (r + 1) 0) ∧
      D.length ≤ a + 1 ∧ ∀ x ∈ D, x ∈ decoratedBlock hK p a := by
  apply frame_body_origin hK _ (by simp [PrefixRealization.run_word_terminal]) D _ hne
  rw [← output_frame]
  exact hD

theorem output_body_projected_command {K : Set ℕ} (hK : K.Infinite) (s : G2)
    (D E : List ℕ) (hD : D ∈ (output hK s).stem.bodyLabels)
    (hE : E.Sublist D) (hEne : E ≠ []) :
    E.length - 1 = 0 ∨ ∃ q ∈ K, E.length - 1 ≤ q ∧ ∀ x ∈ E, q < x := by
  have hDne : D ≠ [] := by intro he; rw [he] at hE; exact hEne (List.sublist_nil.mp hE)
  obtain ⟨p, a, _, _, hphase, hlen, hblock⟩ := output_body_label_origin hK s D hD hDne
  have hEL := hE.length_le.trans hlen
  cases a with
  | zero => left; omega
  | succ a =>
    right
    have hanchor : ∃ q ∈ K, a + 2 ≤ q ∧ ∀ x ∈ decoratedBlock hK p (a + 1), q < x := by
      rcases hphase with hroot | ⟨r, hr⟩
      · have hp := run_root_only_nil p hroot
        subst p
        exact FrameAnchors.root_sibling_anchor hK a
      · exact FrameAnchors.body_sibling_anchor hK p r a hr
    obtain ⟨q, hq, hqa, hqx⟩ := hanchor
    refine ⟨q, hq, ?_, fun x hx ↦ hqx x (hblock x (hE.subset hx))⟩
    omega

end Erdos118.LabelOrigins
