import ErdosProblems.Erdos118.SharedLast

/-!
An initial root response buffered inside an older next-body response.
The two root labels share their last selected body. Only the new suffix
must satisfy the later bound; the complete new front uses its old bound.
-/

namespace Erdos118.RootBuffer

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open Erdos590.Larson

structure Reserve (H : Set ℕ) (b k : ℕ) (S : Stem) where
  label : List ℕ
  card : label.length = k + 1
  increasing : label.Pairwise (· < ·)
  sameLast : label.getLastD 0 = S.rootLabel.getLastD 0
  early : ∀ x ∈ S.rootLabel, x < S.rootLabel.getLastD 0 → x < label.headD 0
  below : ∀ x ∈ label, x < S.root
  fresh : ∀ x ∈ label, x ∈ H ∧ b < x

def Reserve.move {H : Set ℕ} {b k : ℕ} {S : Stem} (Z : Reserve H b k S)
    (T : Stem) (hroot : T.root = S.root) (hlabel : T.rootLabel = S.rootLabel) :
    Reserve H b k T where
  label := Z.label
  card := Z.card
  increasing := Z.increasing
  sameLast := by rw [hlabel]; exact Z.sameLast
  early := by rw [hlabel]; exact Z.early
  below := by rw [hroot]; exact Z.below
  fresh := Z.fresh

theorem root_reserved {H : Set ℕ} (hH : H.Infinite) (b k : ℕ) :
    ∃ A : RootResponses.Setup k, ∃ _Z : Reserve H b k A.stem,
      ∀ x ∈ A.stem.decorated, x ∈ H ∧ b < x := by
  obtain ⟨C, D, hCk, hDk, hCi, hDi, hlast, hearly, hC, hD⟩ := SharedLast.labels hH b k
  obtain ⟨m, hmH, hm⟩ := hH.exists_gt (max b (max C.sum D.sum))
  have hbm : b < m := (le_max_left _ _).trans_lt hm
  have hCm : ∀ x ∈ C, x < m := fun x hx ↦ (nat_le_sum_of_mem hx).trans_lt
    (((le_max_left C.sum D.sum).trans (le_max_right b _)).trans_lt hm)
  have hDm : ∀ x ∈ D, x < m := fun x hx ↦ (nat_le_sum_of_mem hx).trans_lt
    (((le_max_right C.sum D.sum).trans (le_max_right b _)).trans_lt hm)
  let E : Stem :=
    { root := m, rootLabel := C, done := [], count := Nat.zero_le _
      increasing := List.pairwise_append.mpr
        ⟨hCi, by simp, fun x hx y hy ↦ (List.mem_singleton.mp hy) ▸ hCm x hx⟩ }
  have hE : ∀ x ∈ E.decorated, x ∈ H ∧ b < x := by
    intro x hx
    change x ∈ C ++ [m] at hx
    exact (List.mem_append.mp hx).elim (hC x)
      (fun hx ↦ (List.mem_singleton.mp hx).symm ▸ ⟨hmH, hbm⟩)
  have hCne : C ≠ [] := by intro hnil; simp [hnil] at hCk
  have hhead := first_mem hCne
  have hpos : 0 < C.headD 0 := (Nat.zero_le b).trans_lt (hC _ hhead).2
  have hheadm := hCm _ hhead
  obtain ⟨S, v, hr, hlabel, hcount, _, hdec, _, hv, p, hp⟩ :=
    fill_stem_plain E hH b (C.headD 0 - 1) (by simp [E]) (by dsimp [E]; omega)
  let A : RootResponses.Setup k :=
    { stem := S
      label_length := by rw [hlabel]; exact hCk
      first_body := by rw [hcount, hlabel]; change C.headD 0 - 1 + 1 = C.headD 0; omega
      plain := by
        intro a ha
        rw [hp] at ha
        change a ∈ p.map LabelledExtensions.plain at ha
        obtain ⟨u, _, rfl⟩ := List.mem_map.mp ha
        rfl }
  let Z : Reserve H b k A.stem :=
    { label := D, card := hDk, increasing := hDi
      sameLast := by change D.getLastD 0 = S.rootLabel.getLastD 0; rw [hlabel]; exact hlast.symm
      early := by change ∀ x ∈ S.rootLabel, x < S.rootLabel.getLastD 0 → x < D.headD 0
                  rw [hlabel]; exact hearly
      below := by intro x hx; change x < S.root; rw [hr]; exact hDm x hx
      fresh := hD }
  refine ⟨A, Z, ?_⟩
  intro x hx
  change x ∈ S.decorated at hx
  rw [hdec] at hx
  exact (List.mem_append.mp hx).elim (hE x) (hv x)

theorem Reserve.buffer {H : Set ℕ} (hH : H.Infinite) {b k : ℕ} (P : Pending)
    (Z : Reserve H b k P.position.stem) (hP : ExactSlots.Exact (.leaf P)) {c : ℕ}
    (hR : P.roots = [c]) (hOrd : ∀ x ∈ P.position.ordinary, x ∈ H ∧ b < x) (d : ℕ) :
    ∃ A : RootResponses.Setup k, ∃ v : List ℕ,
      A.stem.ordinary = P.position.ordinary ++ v ∧
      A.stem.root = P.position.stem.root ∧ A.stem.rootLabel = Z.label ∧
      (∀ x ∈ v, x ∈ H ∧ d < x) ∧
      (∀ x ∈ A.stem.decorated, x ∈ H ∧ b < x) := by
  have hc := ExactSlots.pending_next_last_root P hP hR
  have hslot := P.rootSlots.bounded c (hR ▸ List.mem_singleton_self _)
  have hfirst : P.position.stem.done.length + 1 < Z.label.headD 0 :=
    Z.early _ P.rootSelected (hc ▸ hslot.1)
  have hne : Z.label ≠ [] := by intro hnil; have h := Z.card; simp [hnil] at h
  have hlast := Z.below _ (first_mem hne)
  have hmore : P.position.stem.done.length < Z.label.headD 0 - 1 := by omega
  have hroot : Z.label.headD 0 - 1 ≤ P.position.stem.root := by omega
  obtain ⟨A₀, hv⟩ := StemResponses.setup_above P.position (Z.label.headD 0 - 1)
    hmore hroot hH (max b d)
  have hbelow : ∀ x ∈ Z.label, x < A₀.stem.root := by rw [A₀.root_eq]; exact Z.below
  have hcount : A₀.stem.done.length + 1 = Z.label.headD 0 := by rw [A₀.count]; omega
  let A := LabelOverlays.rootSetup A₀.stem Z.label Z.increasing hbelow k Z.card hcount
  have hord : A.stem.ordinary = P.position.ordinary ++ A₀.newWord :=
    (LabelOverlays.plainStem_ordinary A₀.stem Z.label Z.increasing hbelow).trans A₀.ordinary
  refine ⟨A, A₀.newWord, hord, A₀.root_eq, rfl,
    fun x hx ↦ ⟨(hv x hx).1, (le_max_right _ _).trans_lt (hv x hx).2⟩, ?_⟩
  change ∀ x ∈ (LabelOverlays.plainStem A₀.stem Z.label Z.increasing hbelow).decorated,
    x ∈ H ∧ b < x
  apply LabelOverlays.plainStem_supported _ _ _ _ Z.fresh
  rw [A₀.ordinary]
  intro x hx
  exact (List.mem_append.mp hx).elim (hOrd x)
    (fun hx ↦ ⟨(hv x hx).1, (le_max_left _ _).trans_lt (hv x hx).2⟩)

end Erdos118.RootBuffer
