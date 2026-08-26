import ErdosProblems.Erdos118.BodyResponses

/-!
Exact root-setup responses stop before the first selected body. This exposes
a stem decision at which the next body's label cardinality can be chosen.
No coloring theorem or adaptive-game outcome is assumed.
-/

namespace Erdos118.RootResponses

open LabelledExtensions Negative Negative.Exact Erdos590.Larson

structure Setup (k : ℕ) where
  stem : Stem
  label_length : stem.rootLabel.length = k + 1
  first_body : stem.done.length + 1 = stem.rootLabel.headD 0
  plain : ∀ a ∈ stem.done, a.label = []

theorem bodies_eq_plain (p : List Body) (h : ∀ a ∈ p, a.label = []) :
    p = (p.map Body.values).map LabelledExtensions.plain := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    have ha : a.label = [] := h a (List.mem_cons_self ..)
    have he : a = LabelledExtensions.plain a.values := by
      cases a with
      | mk values label =>
        change label = [] at ha
        cases ha
        rfl
    have hp := ih (fun b hb ↦ h b (List.mem_cons_of_mem a hb))
    simp only [List.map_cons, ← he, ← hp]

theorem setup_eq_of_prefix {k : ℕ} (P Q : Setup k)
    (h : P.stem.decorated <+: Q.stem.decorated) : P = Q := by
  obtain ⟨v, hv⟩ := h
  have hlen : P.stem.rootLabel.length = Q.stem.rootLabel.length :=
    P.label_length.trans Q.label_length.symm
  have he : P.stem.rootLabel ++ (P.stem.root :: (P.stem.done.flatMap Body.decorated ++ v)) =
      Q.stem.rootLabel ++ (Q.stem.root :: Q.stem.done.flatMap Body.decorated) := by
    simpa only [Stem.decorated, List.append_assoc, List.cons_append] using hv
  obtain ⟨hC, htail⟩ := List.append_inj he hlen
  obtain ⟨hr, hbodies⟩ := List.cons.inj htail
  have hcount : P.stem.done.length = Q.stem.done.length := by
    have hp := P.first_body
    have hq := Q.first_body
    rw [hC] at hp
    omega
  have hp := bodies_eq_plain P.stem.done P.plain
  have hq := bodies_eq_plain Q.stem.done Q.plain
  have hpword : P.stem.done.flatMap Body.decorated =
      (P.stem.done.map Body.values).flatMap levelWord :=
    (congrArg (List.flatMap Body.decorated) hp).trans (plain_decorated _)
  have hqword : Q.stem.done.flatMap Body.decorated =
      (Q.stem.done.map Body.values).flatMap levelWord :=
    (congrArg (List.flatMap Body.decorated) hq).trans (plain_decorated _)
  have hprefix : (P.stem.done.map Body.values).flatMap levelWord <+:
      (Q.stem.done.map Body.values).flatMap levelWord := by
    have hw : P.stem.done.flatMap Body.decorated <+: Q.stem.done.flatMap Body.decorated :=
      ⟨v, hbodies⟩
    rw [← hpword, ← hqword]
    exact hw
  have hvalues := WordResponses.flatMap_prefix_rigid
    (by simpa only [List.length_map] using hcount) hprefix
  have hdone : P.stem.done = Q.stem.done :=
    hp.trans ((congrArg (List.map plain) hvalues).trans hq.symm)
  have stem_ext : ∀ s t : Stem, s.root = t.root → s.rootLabel = t.rootLabel →
      s.done = t.done → s = t := by
    intro s t
    cases s
    cases t
    intro hr hC hd
    cases hr
    cases hC
    cases hd
    rfl
  have hstem := stem_ext P.stem Q.stem hr hC hdone
  cases P with
  | mk p _ _ _ =>
    cases Q with
    | mk q _ _ _ =>
      change p = q at hstem
      cases hstem
      rfl

theorem Setup.room {k : ℕ} (P : Setup k) : P.stem.done.length + 1 < P.stem.root := by
  have hCne : P.stem.rootLabel ≠ [] := by
    intro he
    have hlen := P.label_length
    simp [he] at hlen
  rw [P.first_body]
  exact P.stem.label_before_root _ (LabelledFrames.first_mem hCne)

def support {k : ℕ} (P : Setup k) : Finset ℕ := P.stem.decorated.toFinset

theorem support_injective (k : ℕ) : Function.Injective (support (k := k)) := by
  intro P Q hPQ
  have hpInc : P.stem.decorated.Pairwise (· < ·) := P.stem.increasing
  have hqInc : Q.stem.decorated.Pairwise (· < ·) := Q.stem.increasing
  have hw : P.stem.decorated = Q.stem.decorated := by
    rw [← sort_toFinset_eq_self_of_pairwise hpInc,
      ← sort_toFinset_eq_self_of_pairwise hqInc]
    exact congrArg (fun a : Finset ℕ ↦ a.sort (· ≤ ·)) hPQ
  exact setup_eq_of_prefix P Q (hw ▸ List.prefix_rfl)

def family (k : ℕ) : Set (Finset ℕ) := Set.range (support (k := k))

theorem family_thin (k : ℕ) : NashWilliams.FinThin (family k) := by
  rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩ hPQ
  have hp := (pairwise_isPrefix_iff_initSeg P.stem.increasing Q.stem.increasing).2 hPQ
  exact congrArg support (setup_eq_of_prefix P Q hp)

theorem setup_above (k : ℕ) {H : Set ℕ} (hH : H.Infinite) (b : ℕ) :
    ∃ P : Setup k, ∀ x ∈ P.stem.decorated, x ∈ H ∧ b < x := by
  obtain ⟨E, hE, hlen, hpositive, hfresh⟩ := empty_stem hH b k
  have hCne : E.rootLabel ≠ [] := by intro he; simp [he] at hlen
  have hcpos : 0 < E.rootLabel.headD 0 := hpositive _ (LabelledFrames.first_mem hCne)
  have hcroot : E.rootLabel.headD 0 < E.root :=
    E.label_before_root _ (LabelledFrames.first_mem hCne)
  obtain ⟨S, v, _, hC, hcount, _, hdec, _, hv, p, hp⟩ :=
    fill_stem_plain E hH b (E.rootLabel.headD 0 - 1)
      (by simp [hE]) (by omega)
  let P : Setup k :=
    { stem := S
      label_length := by rw [hC]; exact hlen
      first_body := by rw [hcount, hC]; omega
      plain := by
        intro a ha
        rw [hp, hE, List.nil_append] at ha
        obtain ⟨u, _, rfl⟩ := List.mem_map.mp ha
        rfl }
  refine ⟨P, ?_⟩
  intro x hx
  change x ∈ S.decorated at hx
  rw [hdec] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hfresh x hx
  · exact hv x hx

theorem family_hits (k : ℕ) {H : Set ℕ} (hH : H.Infinite) :
    ∃ a ∈ family k, (↑a : Set ℕ) ⊆ H := by
  obtain ⟨P, hP⟩ := setup_above k hH 0
  exact ⟨support P, ⟨P, rfl⟩, fun x hx ↦ (hP x (List.mem_toFinset.mp hx)).1⟩

def responseFamily (k : ℕ) : RamseyGame.ResponseFamily where
  members := family k
  thin := family_thin k
  hits := fun _ hH ↦ family_hits k hH

noncomputable def supportEquiv (k : ℕ) : Setup k ≃ family k :=
  Equiv.ofInjective support (support_injective k)

@[simp] theorem supportEquiv_apply {k : ℕ} (P : Setup k) :
    (supportEquiv k P).1 = support P := rfl

@[simp] theorem support_symm {k : ℕ} (a : family k) :
    support ((supportEquiv k).symm a) = a.1 :=
  congrArg Subtype.val ((supportEquiv k).apply_symm_apply a)

def toPending {k n : ℕ} (P : Setup k) (Q : BodyResponses.Setup P.stem n) :
    LabelledFrames.Pending where
  position := Q.position
  roots := P.stem.rootLabel.tail
  leaves := Q.position.label.tail
  rootSlots := by
    rw [Q.stem_eq, P.first_body]
    exact LabelledFrames.label_tail_slots _ _ P.stem.label_pairwise P.stem.label_before_root
  leafSlots := by
    rw [Q.entries_length]
    exact LabelledFrames.label_tail_slots _ _ Q.position.label_pairwise
      Q.position.label_before_marker
  rootSelected := by
    rw [Q.stem_eq, P.first_body]
    apply LabelledFrames.first_mem
    intro he
    have hlen := P.label_length
    simp [he] at hlen
  leafSelected := by
    rw [Q.entries_length]
    apply LabelledFrames.first_mem
    intro he
    have hlen := Q.label_length
    simp [he] at hlen

theorem toPending_phase {k n : ℕ} (P : Setup k) (Q : BodyResponses.Setup P.stem n) :
    (LabelledFrames.Frame.pending (toPending P Q)).phase = PrefixRealization.Phase.pending k n := by
  simp [LabelledFrames.Frame.phase, toPending, List.length_tail, P.label_length, Q.label_length]

end Erdos118.RootResponses
