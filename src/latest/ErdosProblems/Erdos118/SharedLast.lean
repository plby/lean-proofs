import ErdosProblems.Erdos118.LeafReplay
import ErdosProblems.Erdos118.ExactSlots

/-!
Two body labels with the same last index. The second label starts after
every nonlast old index, and is chosen before the common body marker.
A later old penultimate position can begin the second body response.
-/

namespace Erdos118.SharedLast

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open Erdos590.Larson

theorem labels_sizes {H : Set ℕ} (hH : H.Infinite) (b k l : ℕ) :
    ∃ C D : List ℕ, C.length = k + 1 ∧ D.length = l + 1 ∧
      C.Pairwise (· < ·) ∧ D.Pairwise (· < ·) ∧ C.getLastD 0 = D.getLastD 0 ∧
      (∀ x ∈ C, x < C.getLastD 0 → x < D.headD 0) ∧
      (∀ x ∈ C, x ∈ H ∧ b < x) ∧ (∀ x ∈ D, x ∈ H ∧ b < x) := by
  obtain ⟨A, hAk, hAi, hA⟩ := InteriorWords.fresh_list hH b k
  obtain ⟨E, hEk, hEi, hE⟩ := InteriorWords.fresh_list hH (max b A.sum) l
  obtain ⟨j, hjH, hj⟩ := hH.exists_gt (max b (max A.sum E.sum))
  have hbj : b < j := (le_max_left _ _).trans_lt hj
  have hAj : ∀ x ∈ A, x < j := fun x hx ↦ (nat_le_sum_of_mem hx).trans_lt
    (((le_max_left A.sum E.sum).trans (le_max_right b _)).trans_lt hj)
  have hEj : ∀ x ∈ E, x < j := fun x hx ↦ (nat_le_sum_of_mem hx).trans_lt
    (((le_max_right A.sum E.sum).trans (le_max_right b _)).trans_lt hj)
  have hAE : ∀ x ∈ A, ∀ y ∈ E, x < y := fun x hx y hy ↦
    ((nat_le_sum_of_mem hx).trans (le_max_right b _)).trans_lt (hE y hy).2
  refine ⟨A ++ [j], E ++ [j], by simp [hAk], by simp [hEk], ?_, ?_, by simp, ?_, ?_, ?_⟩
  · exact List.pairwise_append.mpr ⟨hAi, by simp,
      fun x hx y hy ↦ (List.mem_singleton.mp hy) ▸ hAj x hx⟩
  · exact List.pairwise_append.mpr ⟨hEi, by simp,
      fun x hx y hy ↦ (List.mem_singleton.mp hy) ▸ hEj x hx⟩
  · intro x hx hlt
    have hxA : x ∈ A := by
      rcases List.mem_append.mp hx with hx | hx
      · exact hx
      · have he := List.mem_singleton.mp hx
        simp [he] at hlt
    have hd : (E ++ [j]).headD 0 ∈ E ++ [j] := first_mem (by simp)
    rcases List.mem_append.mp hd with hd | hd
    · exact hAE x hxA _ hd
    · exact (List.mem_singleton.mp hd).symm ▸ hAj x hxA
  · intro x hx
    exact (List.mem_append.mp hx).elim (hA x)
      (fun hx ↦ (List.mem_singleton.mp hx).symm ▸ ⟨hjH, hbj⟩)
  · intro x hx
    exact (List.mem_append.mp hx).elim
      (fun hx ↦ ⟨(hE x hx).1, (le_max_left _ _).trans_lt (hE x hx).2⟩)
      (fun hx ↦ (List.mem_singleton.mp hx).symm ▸ ⟨hjH, hbj⟩)

theorem labels {H : Set ℕ} (hH : H.Infinite) (b k : ℕ) :
    ∃ C D : List ℕ, C.length = k + 1 ∧ D.length = k + 1 ∧
      C.Pairwise (· < ·) ∧ D.Pairwise (· < ·) ∧ C.getLastD 0 = D.getLastD 0 ∧
      (∀ x ∈ C, x < C.getLastD 0 → x < D.headD 0) ∧
      (∀ x ∈ C, x ∈ H ∧ b < x) ∧ (∀ x ∈ D, x ∈ H ∧ b < x) :=
  labels_sizes hH b k k

structure Reserve (H : Set ℕ) (b k : ℕ) (P : Position) where
  label : List ℕ
  card : label.length = k + 1
  increasing : label.Pairwise (· < ·)
  sameLast : label.getLastD 0 = P.label.getLastD 0
  early : ∀ x ∈ P.label, x < P.label.getLastD 0 → x < label.headD 0
  below : ∀ x ∈ label, x < P.size
  before : ∀ x ∈ P.stem.decorated, ∀ y ∈ label, x < y
  fresh : ∀ x ∈ label, x ∈ H ∧ b < x
  markerFresh : P.size ∈ H ∧ b < P.size

def Reserve.move {H : Set ℕ} {b k : ℕ} {P : Position} (Z : Reserve H b k P)
    (Q : Position) (hstem : Q.stem = P.stem) (hsize : Q.size = P.size)
    (hlabel : Q.label = P.label) : Reserve H b k Q where
  label := Z.label
  card := Z.card
  increasing := Z.increasing
  sameLast := by rw [hlabel]; exact Z.sameLast
  early := by rw [hlabel]; exact Z.early
  below := by rw [hsize]; exact Z.below
  before := by rw [hstem]; exact Z.before
  fresh := Z.fresh
  markerFresh := by rw [hsize]; exact Z.markerFresh

theorem body_reserved_sizes (S : Stem) (hroom : S.done.length + 1 < S.root)
    {H : Set ℕ} (hH : H.Infinite) (b k l : ℕ) :
    ∃ A : BodyResponses.Setup S k, ∃ _Z : Reserve H b l A.position,
      ∀ x ∈ BodyResponses.newWord A.position, x ∈ H ∧ b < x := by
  let L := max b S.decorated.sum
  obtain ⟨C, D, hCk, hDk, hCi, hDi, hlast, hearly, hC, hD⟩ := labels_sizes hH L k l
  obtain ⟨n, hnH, hn⟩ := hH.exists_gt (max L (max C.sum D.sum))
  have hLn : L < n := (le_max_left _ _).trans_lt hn
  have hCn : ∀ x ∈ C, x < n := fun x hx ↦ (nat_le_sum_of_mem hx).trans_lt
    (((le_max_left C.sum D.sum).trans (le_max_right L _)).trans_lt hn)
  have hDn : ∀ x ∈ D, x < n := fun x hx ↦ (nat_le_sum_of_mem hx).trans_lt
    (((le_max_right C.sum D.sum).trans (le_max_right L _)).trans_lt hn)
  have hCne : C ≠ [] := by intro hnil; simp [hnil] at hCk
  have hhead := first_mem hCne
  have hheadPos : 0 < C.headD 0 := (Nat.zero_le L).trans_lt (hC _ hhead).2
  obtain ⟨u, huk, hui, hu⟩ := InteriorWords.fresh_list hH n (C.headD 0)
  have hS : ∀ x ∈ S.decorated, x ≤ L :=
    fun x hx ↦ (nat_le_sum_of_mem hx).trans (le_max_right _ _)
  have htail : (n :: u).Pairwise (· < ·) :=
    List.pairwise_cons.mpr ⟨fun x hx ↦ (hu x hx).2, hui⟩
  have hnew : (C ++ n :: u).Pairwise (· < ·) := by
    refine List.pairwise_append.mpr ⟨hCi, htail, ?_⟩
    intro x hx y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hCn x hx
    · exact (hCn x hx).trans (hu y hy).2
  let P : Position :=
    { stem := S, size := n, label := C, entries := u, room := hroom
      started := by rw [huk]; exact hheadPos
      unfinished := by rw [huk]; exact hCn _ hhead
      increasing := by
        refine List.pairwise_append.mpr ⟨S.increasing, hnew, ?_⟩
        intro x hx y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact (hS x hx).trans_lt (hC y hy).2
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact (hS x hx).trans_lt hLn
          · exact ((hS x hx).trans_lt hLn).trans (hu y hy).2 }
  let A : BodyResponses.Setup S k := ⟨P, rfl, hCk, huk⟩
  let Z : Reserve H b l P :=
    { label := D, card := hDk, increasing := hDi, sameLast := hlast.symm
      early := hearly, below := hDn
      before := fun x hx y hy ↦ (hS x hx).trans_lt (hD y hy).2
      fresh := fun x hx ↦ ⟨(hD x hx).1, (le_max_left _ _).trans_lt (hD x hx).2⟩
      markerFresh := ⟨hnH, (le_max_left _ _).trans_lt hLn⟩ }
  refine ⟨A, Z, ?_⟩
  intro x hx
  change x ∈ C ++ n :: u at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact ⟨(hC x hx).1, (le_max_left _ _).trans_lt (hC x hx).2⟩
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact Z.markerFresh
    · exact ⟨(hu x hx).1, Z.markerFresh.2.trans (hu x hx).2⟩

theorem body_reserved (S : Stem) (hroom : S.done.length + 1 < S.root)
    {H : Set ℕ} (hH : H.Infinite) (b k : ℕ) :
    ∃ A : BodyResponses.Setup S k, ∃ _Z : Reserve H b k A.position,
      ∀ x ∈ BodyResponses.newWord A.position, x ∈ H ∧ b < x :=
  body_reserved_sizes S hroom hH b k k

private def replace_label (P : Position) (D : List ℕ) (hD : D.Pairwise (· < ·))
    (hDn : ∀ x ∈ D, x < P.size)
    (hbefore : ∀ x ∈ P.stem.decorated, ∀ y ∈ D, x < y) : Position where
  stem := P.stem
  size := P.size
  label := D
  entries := P.entries
  room := P.room
  started := P.started
  unfinished := P.unfinished
  increasing := by
    have htail := (List.pairwise_append.mp (List.pairwise_append.mp P.increasing).2.1).2.1
    have hnew : (D ++ P.size :: P.entries).Pairwise (· < ·) := by
      refine List.pairwise_append.mpr ⟨hD, htail, ?_⟩
      intro x hx y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hDn x hx
      · exact (hDn x hx).trans ((List.pairwise_cons.mp htail).1 y hy)
    refine List.pairwise_append.mpr ⟨P.stem.increasing, hnew, ?_⟩
    intro x hx y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hbefore x hx y hy
    · exact (List.pairwise_append.mp P.increasing).2.2 x hx y (List.mem_append_right _ hy)

theorem Reserve.buffer {H : Set ℕ} (hH : H.Infinite) {b k : ℕ} (P : Pending)
    (Z : Reserve H b k P.position) (hP : ExactSlots.Exact (.leaf P)) {j : ℕ}
    (hL : P.leaves = [j]) (hentries : ∀ x ∈ P.position.entries, x ∈ H) (d : ℕ) :
    ∃ A : BodyResponses.Setup P.position.stem k, ∃ v : List ℕ,
      A.position.ordinary = P.position.ordinary ++ v ∧
      A.position.entries = P.position.entries ++ v ∧
      A.position.size = P.position.size ∧ A.position.label = Z.label ∧
      (∀ x ∈ v, x ∈ H ∧ d < x) ∧
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H ∧ b < x) := by
  have hj := ExactSlots.pending_next_last P hP hL
  have hslot := P.leafSlots.bounded j (hL ▸ List.mem_singleton_self _)
  have hfirst : P.position.entries.length < Z.label.headD 0 :=
    Z.early _ P.leafSelected (hj ▸ hslot.1)
  have hne : Z.label ≠ [] := by intro hnil; have h := Z.card; simp [hnil] at h
  have hlast : Z.label.headD 0 < P.position.size := Z.below _ (first_mem hne)
  obtain ⟨A₀, hv⟩ := LeafResponses.setup_above P.position (Z.label.headD 0) hH d
  let Q₀ := LeafResponses.position A₀ hfirst hlast
  let Q := replace_label Q₀ Z.label Z.increasing Z.below Z.before
  let A : BodyResponses.Setup P.position.stem k :=
    ⟨Q, rfl, Z.card, LeafResponses.position_length A₀ hfirst hlast⟩
  have hQord : Q.ordinary = P.position.ordinary ++ A₀.newWord :=
    LeafResponses.position_ordinary A₀ hfirst hlast
  refine ⟨A, A₀.newWord, hQord, rfl, rfl, rfl, hv, ?_⟩
  intro x hx
  change x ∈ Z.label ++ P.position.size :: (P.position.entries ++ A₀.newWord) at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact Z.fresh x hx
  · rcases List.mem_cons.mp hx with rfl | hx
    · exact Z.markerFresh
    · have htail := (List.pairwise_append.mp (List.pairwise_append.mp Q.increasing).2.1).2.1
      have hlarge : b < x := Z.markerFresh.2.trans ((List.pairwise_cons.mp htail).1 x hx)
      exact ⟨(List.mem_append.mp hx).elim (hentries x) (fun hx ↦ (hv x hx).1), hlarge⟩

end Erdos118.SharedLast
