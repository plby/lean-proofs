import ErdosProblems.Erdos118.LabelledExtensions
import ErdosProblems.Erdos118.SizedExtensions
import ErdosProblems.Erdos118.PrefixRealization

/-!
Labelled parser frames retain actual successor indices and all unused slots.
Every live transition is constructed above an arbitrary bound. There is no
assumed coloring, game strategy, or global partition theorem.
-/

namespace Erdos118.LabelledFrames

open Negative Negative.Exact LabelledExtensions
open PrefixRealization (Phase)

structure Slots (lo hi : ℕ) (label remaining : List ℕ) : Prop where
  increasing : remaining.Pairwise (· < ·)
  bounded : ∀ x ∈ remaining, lo < x ∧ x < hi ∧ x ∈ label

theorem Slots.nil (lo hi : ℕ) (label : List ℕ) : Slots lo hi label [] :=
  ⟨by simp, by simp⟩

theorem Slots.tail {lo hi : ℕ} {label : List ℕ} {a : ℕ} {r : List ℕ}
    (h : Slots lo hi label (a :: r)) : Slots a hi label r := by
  have hp := List.pairwise_cons.mp h.increasing
  refine ⟨hp.2, ?_⟩
  intro x hx
  exact ⟨hp.1 x hx, (h.bounded x (List.mem_cons_of_mem a hx)).2⟩

theorem label_tail_slots (label : List ℕ) (hi : ℕ)
    (hpair : label.Pairwise (· < ·)) (hbound : ∀ x ∈ label, x < hi) :
    Slots (label.headD 0) hi label label.tail := by
  cases label with
  | nil => exact Slots.nil _ _ _
  | cons a r =>
    have hp := List.pairwise_cons.mp hpair
    refine ⟨hp.2, ?_⟩
    intro x hx
    have hmem : x ∈ a :: r := List.mem_cons_of_mem a hx
    exact ⟨hp.1 x hx, hbound x hmem, hmem⟩

theorem first_mem {label : List ℕ} (h : label ≠ []) : label.headD 0 ∈ label := by
  cases label with
  | nil => exact (h rfl).elim
  | cons a r => exact List.mem_cons_self ..

structure Pending where
  position : Position
  roots : List ℕ
  leaves : List ℕ
  rootSlots : Slots (position.stem.done.length + 1) position.stem.root
    position.stem.rootLabel roots
  leafSlots : Slots position.entries.length position.size position.label leaves
  rootSelected : position.stem.done.length + 1 ∈ position.stem.rootLabel
  leafSelected : position.entries.length ∈ position.label

theorem start_pending_budget {H : Set ℕ} (hH : H.Infinite) (b r : ℕ) :
    ∃ F : Pending, F.roots.length = r ∧ F.leaves.length = 0 ∧
      (∀ z ∈ F.position.decorated, z ∈ H ∧ b < z) ∧
      F.position.stem.rootLabel.length = r + 1 ∧
      ∀ D ∈ F.position.bodyLabels, D.length ≤ r + 1 := by
  obtain ⟨P, hCsize, hDsize, hbody, hleaf, _, _, hfresh, e, he⟩ :=
    SizedExtensions.start_labels hH b r
  have hCne : P.stem.rootLabel ≠ [] := by intro he; simp [he] at hCsize
  have hDne : P.label ≠ [] := by intro he; simp [he] at hDsize
  let F : Pending :=
    { position := P, roots := P.stem.rootLabel.tail, leaves := P.label.tail
      rootSlots := by
        rw [hbody]
        exact label_tail_slots _ _ P.stem.label_pairwise P.stem.label_before_root
      leafSlots := by
        rw [hleaf]
        exact label_tail_slots _ _ P.label_pairwise P.label_before_marker
      rootSelected := hbody ▸ first_mem hCne
      leafSelected := hleaf ▸ first_mem hDne }
  refine ⟨F, ?_, ?_, hfresh, hCsize, ?_⟩
  · simp [F, List.length_tail, hCsize]
  · simp [F, List.length_tail, hDsize]
  · intro D hD
    change D ∈ P.stem.bodyLabels ++ [P.label] at hD
    rw [he] at hD
    rcases List.mem_append.mp hD with hD | hD
    · have hnil := List.eq_of_mem_replicate hD
      subst D
      exact Nat.zero_le _
    · have hlabel := List.mem_singleton.mp hD
      rw [hlabel, hDsize]
      omega

theorem start_pending {H : Set ℕ} (hH : H.Infinite) (b r : ℕ) :
    ∃ F : Pending, F.roots.length = r ∧ F.leaves.length = 0 ∧
      ∀ z ∈ F.position.decorated, z ∈ H ∧ b < z := by
  obtain ⟨F, hr, hl, hfresh, _⟩ := start_pending_budget hH b r
  exact ⟨F, hr, hl, hfresh⟩

inductive Frame
  | initial
  | pending (F : Pending)
  | terminal (S : Stem) (full : S.done.length = S.root)
  | dead

def Frame.phase : Frame → Phase
  | .initial => .root
  | .pending F => .pending F.roots.length F.leaves.length
  | .terminal _ _ => .terminal
  | .dead => .dead

def Frame.decorated : Frame → List ℕ
  | .initial | .dead => []
  | .pending F => F.position.decorated
  | .terminal S _ => S.decorated

def Frame.ordinary : Frame → List ℕ
  | .initial | .dead => []
  | .pending F => F.position.ordinary
  | .terminal S _ => S.ordinary

def Frame.rootLabel : Frame → Option (List ℕ)
  | .initial | .dead => none
  | .pending F => some F.position.stem.rootLabel
  | .terminal S _ => some S.rootLabel

def Frame.bodyLabels : Frame → List (List ℕ)
  | .initial | .dead => []
  | .pending F => F.position.bodyLabels
  | .terminal S _ => S.bodyLabels

/-- Existing root and body annotations retain their values and positions. -/
structure LabelsExtend (F G : Frame) : Prop where
  root : ∀ C : List ℕ, F.rootLabel = some C → G.rootLabel = some C
  bodies : F.bodyLabels <+: G.bodyLabels

theorem LabelsExtend.refl (F : Frame) : LabelsExtend F F :=
  ⟨fun _ h ↦ h, List.prefix_rfl⟩

theorem LabelsExtend.trans {F G K : Frame} (hFG : LabelsExtend F G)
    (hGK : LabelsExtend G K) : LabelsExtend F K :=
  ⟨fun C hC ↦ hGK.root C (hFG.root C hC), hFG.bodies.trans hGK.bodies⟩

theorem LabelsExtend.initial (F : Frame) : LabelsExtend .initial F := by
  refine ⟨?_, List.nil_prefix⟩
  intro C hC
  simp [Frame.rootLabel] at hC

theorem LabelsExtend.pending (P Q : Pending)
    (hroot : Q.position.stem.rootLabel = P.position.stem.rootLabel)
    (hlabels : P.position.bodyLabels <+: Q.position.bodyLabels) :
    LabelsExtend (.pending P) (.pending Q) := by
  refine ⟨?_, hlabels⟩
  intro C hC
  change some Q.position.stem.rootLabel = some C
  rw [hroot]
  exact hC

theorem LabelsExtend.terminal (P : Pending) (S : Stem) (hS : S.done.length = S.root)
    (hroot : S.rootLabel = P.position.stem.rootLabel)
    (hlabels : P.position.bodyLabels <+: S.bodyLabels) :
    LabelsExtend (.pending P) (.terminal S hS) := by
  refine ⟨?_, hlabels⟩
  intro C hC
  change some S.rootLabel = some C
  rw [hroot]
  exact hC

structure LabelBudget (F : Frame) (a : ℕ) (G : Frame) : Prop where
  root : F = .initial → ∃ C : List ℕ, G.rootLabel = some C ∧ C.length = a + 1
  bodies : ∀ D ∈ G.bodyLabels.drop F.bodyLabels.length, D.length ≤ a + 1
  bodyPhase : ∀ D ∈ G.bodyLabels.drop F.bodyLabels.length, D ≠ [] →
    F.phase = .root ∨ ∃ r : ℕ, F.phase = .pending (r + 1) 0
  bodyFresh : ∀ D ∈ G.bodyLabels.drop F.bodyLabels.length,
    ∀ x ∈ D, x ∈ G.decorated.drop F.decorated.length

private theorem position_label_mem (P : Position) :
    ∀ D ∈ P.bodyLabels, ∀ x ∈ D, x ∈ P.decorated := by
  intro D hD x hx
  change D ∈ P.stem.done.map Body.label ++ [P.label] at hD
  rcases List.mem_append.mp hD with hD | hD
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hD
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
      (List.mem_cons_of_mem _ (List.mem_flatMap.mpr
        ⟨a, ha, List.mem_append_left _ hx⟩)))))
  · have he := List.mem_singleton.mp hD
    subst D
    exact List.mem_append.mpr (Or.inr (List.mem_append_left _ hx))

theorem step_budget_exists {H : Set ℕ} (hH : H.Infinite) (F : Frame) (a b : ℕ) :
    ∃ F' : Frame, F'.phase = F.phase.next a ∧
      (F.phase.live → ∃ d v : List ℕ,
        F'.decorated = F.decorated ++ d ∧ F'.ordinary = F.ordinary ++ v ∧
        v ≠ [] ∧ v.Sublist d ∧ (∀ z ∈ d, z ∈ H ∧ b < z) ∧ LabelsExtend F F') ∧
      LabelBudget F a F' := by
  cases F with
  | initial =>
    obtain ⟨P, hroots, hleaves, hfresh, hrootSize, hbodySizes⟩ := start_pending_budget hH b a
    refine ⟨.pending P, ?_, (fun _ ↦ ?_), ?_⟩
    · simp only [Frame.phase, Phase.next, hroots, hleaves]
    · exact ⟨P.position.decorated, P.position.ordinary, rfl, rfl,
        by simp [Position.ordinary, Stem.ordinary], P.position.ordinary_sublist,
        hfresh, LabelsExtend.initial _⟩
    · exact ⟨fun _ ↦ ⟨P.position.stem.rootLabel, rfl, hrootSize⟩,
        hbodySizes, (fun _ _ _ ↦ Or.inl rfl), position_label_mem P.position⟩
  | pending F =>
    cases hL : F.leaves with
    | cons d L =>
      have hslot := F.leafSlots.bounded d (by rw [hL]; exact List.mem_cons_self ..)
      obtain ⟨Q, v, hstem, hsize, hlabel, hlen, hdec, hord, hvne, hv⟩ :=
        advance_leaf F.position hH b d hslot.1 hslot.2.1
      have htail : Slots d F.position.size F.position.label L := by
        apply Slots.tail
        simpa only [hL] using F.leafSlots
      let P : Pending :=
        { position := Q, roots := F.roots, leaves := L
          rootSlots := by rw [hstem]; exact F.rootSlots
          leafSlots := by rw [hlen, hsize, hlabel]; exact htail
          rootSelected := by rw [hstem]; exact F.rootSelected
          leafSelected := by rw [hlen, hlabel]; exact hslot.2.2 }
      have hlabels : LabelsExtend (.pending F) (.pending P) := by
        apply LabelsExtend.pending
        · change Q.stem.rootLabel = F.position.stem.rootLabel
          rw [hstem]
        · change F.position.bodyLabels <+: Q.bodyLabels
          simp only [Position.bodyLabels, hstem, hlabel]
          exact List.prefix_rfl
      refine ⟨.pending P, ?_, (fun _ ↦
        ⟨v, v, hdec, hord, hvne, List.Sublist.refl _, hv, hlabels⟩), ?_⟩
      · simp [Frame.phase, P, hL, Phase.next]
      · refine ⟨by simp, ?_, ?_, ?_⟩
        · simp [Frame.bodyLabels, P, Position.bodyLabels, hstem, hlabel]
        · simp [Frame.bodyLabels, P, Position.bodyLabels, hstem, hlabel]
        · simp [Frame.bodyLabels, P, Position.bodyLabels, hstem, hlabel]
    | nil =>
      cases hR : F.roots with
      | nil =>
        obtain ⟨S, hS, v, _, hC, _, hlabels, hdec, hord, hvne, hv, e, he⟩ :=
          SizedExtensions.complete_labels F.position hH b
        refine ⟨.terminal S hS, ?_, (fun _ ↦ ?_), ?_⟩
        · simp [Frame.phase, hR, hL, Phase.next]
        · exact ⟨v, v, hdec, (S.toGood_word hS).symm.trans hord,
            hvne, List.Sublist.refl _, hv, LabelsExtend.terminal F S hS hC hlabels⟩
        · refine ⟨by simp, ?_, ?_, ?_⟩
          · change ∀ D ∈ S.bodyLabels.drop F.position.bodyLabels.length, _
            rw [he, List.drop_append_of_le_length le_rfl, List.drop_length, List.nil_append]
            intro D hD
            have hnil := List.eq_of_mem_replicate hD
            subst D
            exact Nat.zero_le _
          · simp [Frame.bodyLabels, he]
          · simp [Frame.bodyLabels, he]
      | cons c R =>
        have hslot := F.rootSlots.bounded c (by rw [hR]; exact List.mem_cons_self ..)
        obtain ⟨Q, d, v, hroot, hC, hbody, _, hlabels, hDsize, hleaf, _, hdec, hord,
          hvne, hvd, hfresh, hDsub, e, he⟩ :=
          SizedExtensions.advance_body_labels F.position hH b c a hslot.1 hslot.2.1
        have htail : Slots c F.position.stem.root F.position.stem.rootLabel R := by
          apply Slots.tail
          simpa only [hR] using F.rootSlots
        have hDne : Q.label ≠ [] := by intro he; simp [he] at hDsize
        let P : Pending :=
          { position := Q, roots := R, leaves := Q.label.tail
            rootSlots := by rw [hbody, hroot, hC]; exact htail
            leafSlots := by
              rw [hleaf]
              exact label_tail_slots _ _ Q.label_pairwise Q.label_before_marker
            rootSelected := by rw [hbody, hC]; exact hslot.2.2
            leafSelected := hleaf ▸ first_mem hDne }
        refine ⟨.pending P, ?_, (fun _ ↦
          ⟨d, v, hdec, hord, hvne, hvd, hfresh, LabelsExtend.pending F P hC hlabels⟩), ?_⟩
        · simp [Frame.phase, P, hR, hL, Phase.next, List.length_tail, hDsize]
        · refine ⟨by simp, ?_, ?_, ?_⟩
          · change ∀ D ∈ Q.bodyLabels.drop F.position.bodyLabels.length, _
            rw [he, List.append_assoc, List.drop_append_of_le_length le_rfl,
              List.drop_length, List.nil_append]
            intro D hD
            rcases List.mem_append.mp hD with hD | hD
            · have hnil := List.eq_of_mem_replicate hD
              subst D
              exact Nat.zero_le _
            · have hlabel := List.mem_singleton.mp hD
              rw [hlabel, hDsize]
          · exact fun _ _ _ ↦ Or.inr ⟨R.length, by simp [Frame.phase, hR, hL]⟩
          · change ∀ D ∈ Q.bodyLabels.drop F.position.bodyLabels.length,
              ∀ x ∈ D, x ∈ Q.decorated.drop F.position.decorated.length
            rw [he, List.append_assoc, List.drop_append_of_le_length le_rfl,
              List.drop_length, List.nil_append]
            intro D hD x hx
            rcases List.mem_append.mp hD with hD | hD
            · have hnil := List.eq_of_mem_replicate hD
              subst D
              simp at hx
            · have hlabel := List.mem_singleton.mp hD
              subst D
              rw [hdec, List.drop_append_of_le_length le_rfl, List.drop_length, List.nil_append]
              exact hDsub.subset hx
  | terminal S hS => exact ⟨.dead, rfl, (fun h ↦ h.elim),
      ⟨by simp, by simp [Frame.bodyLabels], by simp [Frame.bodyLabels],
        by simp [Frame.bodyLabels]⟩⟩
  | dead => exact ⟨.dead, rfl, (fun h ↦ h.elim),
      ⟨by simp, by simp [Frame.bodyLabels], by simp [Frame.bodyLabels],
        by simp [Frame.bodyLabels]⟩⟩

theorem step_preserving_exists {H : Set ℕ} (hH : H.Infinite) (F : Frame) (a b : ℕ) :
    ∃ F' : Frame, F'.phase = F.phase.next a ∧
      (F.phase.live → ∃ d v : List ℕ,
        F'.decorated = F.decorated ++ d ∧ F'.ordinary = F.ordinary ++ v ∧
        v ≠ [] ∧ v.Sublist d ∧ (∀ z ∈ d, z ∈ H ∧ b < z) ∧ LabelsExtend F F') := by
  obtain ⟨F', hphase, hstep, _⟩ := step_budget_exists hH F a b
  exact ⟨F', hphase, hstep⟩

/-- The original local-availability interface follows from the stronger
annotation-preserving construction. -/
theorem step_exists {H : Set ℕ} (hH : H.Infinite) (F : Frame) (a b : ℕ) :
    ∃ F' : Frame, F'.phase = F.phase.next a ∧
      (F.phase.live → ∃ d v : List ℕ,
        F'.decorated = F.decorated ++ d ∧ F'.ordinary = F.ordinary ++ v ∧
        v ≠ [] ∧ v.Sublist d ∧ ∀ z ∈ d, z ∈ H ∧ b < z) := by
  obtain ⟨F', hphase, hstep⟩ := step_preserving_exists hH F a b
  refine ⟨F', hphase, ?_⟩
  intro hF
  obtain ⟨d, v, hdec, hord, hvne, hvd, hfresh, _⟩ := hstep hF
  exact ⟨d, v, hdec, hord, hvne, hvd, hfresh⟩

end Erdos118.LabelledFrames
