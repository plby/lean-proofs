import ErdosProblems.Erdos118.LabelOverlays
import ErdosProblems.Erdos118.AdaptiveGame

/-!
Root/body responses with a second label reserved before the common marker.
Exact support decoders connect these constructed fronts to the actual game.
No three-game synchronization or coloring preservation by relabeling is assumed.
-/

namespace Erdos118.ReservedResponses

open Negative Negative.Exact LabelledExtensions LabelOverlays DecisionStates AdaptiveGame
open Erdos590.Larson

structure Reserve (C : List ℕ) (marker l : ℕ) where
  label : List ℕ
  card : label.length = l + 1
  increasing : label.Pairwise (· < ·)
  first : label.headD 0 = C.getLastD 0
  below : ∀ x ∈ label, x < marker
  shared : ∀ x, x ∈ C ∧ x ∈ label ↔ x = C.getLastD 0

theorem root_reserved {H : Set ℕ} (hH : H.Infinite) (b k l : ℕ) :
    ∃ A : RootResponses.Setup k, ∃ R : Reserve A.stem.rootLabel A.stem.root l,
      (∀ x ∈ A.stem.decorated, x ∈ H ∧ b < x) ∧
      ∀ x ∈ R.label, x ∈ H ∧ b < x := by
  obtain ⟨C, D, c, hCcard, hDcard, hCinc, hDinc, hClast, hDhead, _, _,
    hshared, hC, hD⟩ := shared_extreme_labels hH b k l
  obtain ⟨m, hmH, hm⟩ := hH.exists_gt (max b (max C.sum D.sum))
  have hbm : b < m := (le_max_left _ _).trans_lt hm
  have hCm : ∀ x ∈ C, x < m := fun x hx ↦
    (nat_le_sum_of_mem hx).trans_lt
      (((le_max_left C.sum D.sum).trans (le_max_right b _)).trans_lt hm)
  have hDm : ∀ x ∈ D, x < m := fun x hx ↦
    (nat_le_sum_of_mem hx).trans_lt
      (((le_max_right C.sum D.sum).trans (le_max_right b _)).trans_lt hm)
  let E : Stem :=
    { root := m, rootLabel := C, done := [], count := Nat.zero_le _
      increasing := List.pairwise_append.mpr
        ⟨hCinc, by simp, fun x hx y hy ↦ (List.mem_singleton.mp hy) ▸ hCm x hx⟩ }
  have hE : ∀ x ∈ E.decorated, x ∈ H ∧ b < x := by
    intro x hx
    change x ∈ C ++ [m] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ⟨(hC x hx).1, (hC x hx).2.1⟩
    · have he := List.mem_singleton.mp hx
      subst x
      exact ⟨hmH, hbm⟩
  have hCne : C ≠ [] := by intro he; simp [he] at hCcard
  have hhead := LabelledFrames.first_mem hCne
  have hpos : 0 < C.headD 0 := (Nat.zero_le b).trans_lt (hC _ hhead).2.1
  have hheadm : C.headD 0 < m := hCm _ hhead
  obtain ⟨S, v, hr, hlabel, hcount, _, hdec, _, hv, p, hp⟩ :=
    fill_stem_plain E hH b (C.headD 0 - 1) (by simp [E]) (by dsimp [E]; omega)
  let A : RootResponses.Setup k :=
    { stem := S
      label_length := by rw [hlabel]; exact hCcard
      first_body := by rw [hcount, hlabel]; change C.headD 0 - 1 + 1 = C.headD 0; omega
      plain := by
        intro a ha
        rw [hp] at ha
        change a ∈ p.map LabelledExtensions.plain at ha
        obtain ⟨u, _, rfl⟩ := List.mem_map.mp ha
        rfl }
  let R : Reserve A.stem.rootLabel A.stem.root l :=
    { label := D, card := hDcard, increasing := hDinc
      first := by
        change D.headD 0 = S.rootLabel.getLastD 0
        rw [hlabel]
        exact hDhead.trans hClast.symm
      below := by intro x hx; change x < S.root; rw [hr]; exact hDm x hx
      shared := by intro x; change x ∈ S.rootLabel ∧ x ∈ D ↔ x = S.rootLabel.getLastD 0
                   rw [hlabel]; change x ∈ C ∧ x ∈ D ↔ x = C.getLastD 0
                   rw [hClast]; exact hshared x }
  refine ⟨A, R, ?_, fun x hx ↦ ⟨(hD x hx).1, (hD x hx).2.1⟩⟩
  intro x hx
  change x ∈ S.decorated at hx
  rw [hdec] at hx
  exact (List.mem_append.mp hx).elim (hE x) (hv x)

theorem body_reserved (S : Stem) (hroom : S.done.length + 1 < S.root)
    {H : Set ℕ} (hH : H.Infinite) (b k l : ℕ) :
    ∃ A : BodyResponses.Setup S k, ∃ R : Reserve A.position.label A.position.size l,
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H ∧ b < x) ∧
      (∀ x ∈ R.label, x ∈ H ∧ b < x) ∧
      ∀ x ∈ S.decorated, ∀ y ∈ R.label, x < y := by
  let L := max b S.decorated.sum
  obtain ⟨D, E, c, hDcard, hEcard, hDinc, hEinc, hDlast, hEhead, _, _,
    hshared, hD, hE⟩ := shared_extreme_labels hH L k l
  obtain ⟨n, hnH, hn⟩ := hH.exists_gt (max L (max D.sum E.sum))
  have hLn : L < n := (le_max_left _ _).trans_lt hn
  have hDn : ∀ x ∈ D, x < n := fun x hx ↦
    (nat_le_sum_of_mem hx).trans_lt
      (((le_max_left D.sum E.sum).trans (le_max_right L _)).trans_lt hn)
  have hEn : ∀ x ∈ E, x < n := fun x hx ↦
    (nat_le_sum_of_mem hx).trans_lt
      (((le_max_right D.sum E.sum).trans (le_max_right L _)).trans_lt hn)
  have hDne : D ≠ [] := by intro he; simp [he] at hDcard
  have hhead := LabelledFrames.first_mem hDne
  have hdpos : 0 < D.headD 0 := (Nat.zero_le L).trans_lt (hD _ hhead).2.1
  have hdn : D.headD 0 < n := hDn _ hhead
  obtain ⟨u, huCard, huInc, hu⟩ := InteriorWords.fresh_list hH n (D.headD 0)
  have hSbound : ∀ x ∈ S.decorated, x ≤ L := fun x hx ↦
    (nat_le_sum_of_mem hx).trans (le_max_right b S.decorated.sum)
  have htail : (n :: u).Pairwise (· < ·) :=
    List.pairwise_cons.mpr ⟨fun x hx ↦ (hu x hx).2, huInc⟩
  have hnewInc : (D ++ n :: u).Pairwise (· < ·) := by
    apply List.pairwise_append.mpr
    refine ⟨hDinc, htail, ?_⟩
    intro x hx y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hDn x hx
    · exact (hDn x hx).trans (hu y hy).2
  let P : Position :=
    { stem := S, size := n, label := D, entries := u, room := hroom
      started := by rw [huCard]; exact hdpos
      unfinished := by rw [huCard]; exact hdn
      increasing := by
        apply List.pairwise_append.mpr
        refine ⟨S.increasing, hnewInc, ?_⟩
        intro x hx y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact (hSbound x hx).trans_lt (hD y hy).2.1
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact (hSbound x hx).trans_lt hLn
          · exact ((hSbound x hx).trans_lt hLn).trans (hu y hy).2 }
  let A : BodyResponses.Setup S k := ⟨P, rfl, hDcard, huCard⟩
  let R : Reserve A.position.label A.position.size l :=
    { label := E, card := hEcard, increasing := hEinc
      first := hEhead.trans hDlast.symm
      below := hEn
      shared := by intro x; change x ∈ D ∧ x ∈ E ↔ x = D.getLastD 0
                   rw [hDlast]; exact hshared x }
  have hbL : b ≤ L := le_max_left _ _
  refine ⟨A, R, ?_, fun x hx ↦ ⟨(hE x hx).1, hbL.trans_lt (hE x hx).2.1⟩,
    fun x hx y hy ↦ (hSbound x hx).trans_lt (hE y hy).2.1⟩
  intro x hx
  change x ∈ D ++ n :: u at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact ⟨(hD x hx).1, hbL.trans_lt (hD x hx).2.1⟩
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hnH, hbL.trans_lt hLn⟩
    · exact ⟨(hu x hx).1, (hbL.trans_lt hLn).trans (hu x hx).2⟩

theorem before_plain_overlay (S : Stem) (C D : List ℕ) (hC : C.Pairwise (· < ·))
    (hCr : ∀ x ∈ C, x < S.root)
    (hbefore : ∀ x ∈ S.decorated, ∀ y ∈ D, x < y) :
    ∀ x ∈ (plainStem S C hC hCr).decorated, ∀ y ∈ D, x < y := by
  rw [plainStem_decorated]
  intro x hx y hy
  rcases List.mem_append.mp hx with hx | hx
  · exact (hCr x hx).trans (hbefore S.root
      (List.mem_append_right _ (List.mem_cons_self ..)) y hy)
  · exact hbefore x (S.ordinary_sublist.subset hx) y hy

noncomputable def rootMember {k : ℕ} (b : ℕ) (A : RootResponses.Setup k)
    (h : ∀ x ∈ A.stem.decorated, b < x) : (rootResponse k b).family.members :=
  ⟨(RootResponses.supportEquiv k A).1, (RootResponses.supportEquiv k A).2,
    fun x hx ↦ h x (List.mem_toFinset.mp hx)⟩

@[simp] theorem rootMember_value {k : ℕ} (b : ℕ) (A : RootResponses.Setup k)
    (h : ∀ x ∈ A.stem.decorated, b < x) : (rootMember b A h).1 = A.stem.decorated.toFinset := rfl

theorem rootMember_result {k : ℕ} (b : ℕ) (A : RootResponses.Setup k)
    (h : ∀ x ∈ A.stem.decorated, b < x) :
    (rootResponse k b).result (rootMember b A h) = .body (ofRoot A) := by
  change State.body (ofRoot ((RootResponses.supportEquiv k).symm
    ((RootResponses.supportEquiv k) A))) = _
  rw [Equiv.symm_apply_apply]

noncomputable def bodyMember (D : BodyDecision) {k : ℕ} (b : ℕ)
    (A : BodyResponses.Setup D.stem k) (h : ∀ x ∈ BodyResponses.newWord A.position, b < x) :
    (bodyResponse D k b).family.members :=
  ⟨(BodyResponses.supportEquiv D.stem k A).1, (BodyResponses.supportEquiv D.stem k A).2,
    fun x hx ↦ h x (List.mem_toFinset.mp hx)⟩

@[simp] theorem bodyMember_value (D : BodyDecision) {k : ℕ} (b : ℕ)
    (A : BodyResponses.Setup D.stem k) (h : ∀ x ∈ BodyResponses.newWord A.position, b < x) :
    (bodyMember D b A h).1 = (BodyResponses.newWord A.position).toFinset := rfl

theorem bodyMember_result (D : BodyDecision) {k : ℕ} (b : ℕ)
    (A : BodyResponses.Setup D.stem k) (h : ∀ x ∈ BodyResponses.newWord A.position, b < x) :
    (bodyResponse D k b).result (bodyMember D b A h) = .leaf (applyBody D A) := by
  change State.leaf (applyBody D ((BodyResponses.supportEquiv D.stem k).symm
    ((BodyResponses.supportEquiv D.stem k) A))) = _
  rw [Equiv.symm_apply_apply]

noncomputable def finishMember (P : LabelledFrames.Pending) (hR : P.roots = [])
    (hL : P.leaves = []) (b : ℕ)
    (A : StemResponses.Setup P.position P.position.stem.root)
    (h : ∀ x ∈ A.newWord, b < x) : (finishResponse P hR hL b).family.members :=
  ⟨(StemResponses.supportEquiv P.position P.position.stem.root A).1,
    (StemResponses.supportEquiv P.position P.position.stem.root A).2,
    fun x hx ↦ h x (List.mem_toFinset.mp hx)⟩

@[simp] theorem finishMember_value (P : LabelledFrames.Pending) (hR : P.roots = [])
    (hL : P.leaves = []) (b : ℕ)
    (A : StemResponses.Setup P.position P.position.stem.root)
    (h : ∀ x ∈ A.newWord, b < x) : (finishMember P hR hL b A h).1 = A.newWord.toFinset := rfl

theorem finishMember_result (P : LabelledFrames.Pending) (hR : P.roots = [])
    (hL : P.leaves = []) (b : ℕ)
    (A : StemResponses.Setup P.position P.position.stem.root)
    (h : ∀ x ∈ A.newWord, b < x) :
    (finishResponse P hR hL b).result (finishMember P hR hL b A h) =
      .complete (ofCompletion P A) := by
  change State.complete (ofCompletion P ((StemResponses.supportEquiv P.position
    P.position.stem.root).symm
      ((StemResponses.supportEquiv P.position P.position.stem.root) A))) = _
  rw [Equiv.symm_apply_apply]

end Erdos118.ReservedResponses
