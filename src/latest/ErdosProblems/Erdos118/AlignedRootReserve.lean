import ErdosProblems.Erdos118.RootBuffer

/-!
Independent root sizes with the lower penultimate index equal to the
upper first index and with a common last index. The saved labels are
installed only by actual root-setup decoders, not by transporting colors.
-/

namespace Erdos118.AlignedRootReserve

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open Erdos590.Larson

theorem labels {H : Set ℕ} (hH : H.Infinite) (b k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    ∃ C D : List ℕ, ∃ r c : ℕ,
      C.length = k + 1 ∧ D.length = l + 1 ∧
      C.Pairwise (· < ·) ∧ D.Pairwise (· < ·) ∧
      C.getLastD 0 = c ∧ D.getLastD 0 = c ∧ D.headD 0 = r ∧ r ∈ C ∧ r < c ∧
      (∀ x ∈ C, x < c → x ≤ r) ∧
      (∀ x, x ∈ C ∧ x ∈ D ↔ x = r ∨ x = c) ∧
      (∀ x ∈ C, x ∈ H ∧ b < x) ∧ (∀ x ∈ D, x ∈ H ∧ b < x) := by
  obtain ⟨A, E, r, hAk, hEl, hAi, hEi, hAr, hEr, hrA, hrE, hAE, hA, hE⟩ :=
    LabelOverlays.shared_extreme_labels hH b (k - 1) (l - 1)
  obtain ⟨c, hcH, hc⟩ := hH.exists_gt (max b (max A.sum E.sum))
  have hbc : b < c := (le_max_left _ _).trans_lt hc
  have hAc : ∀ x ∈ A, x < c := fun x hx ↦ (nat_le_sum_of_mem hx).trans_lt
    (((le_max_left A.sum E.sum).trans (le_max_right b _)).trans_lt hc)
  have hEc : ∀ x ∈ E, x < c := fun x hx ↦ (nat_le_sum_of_mem hx).trans_lt
    (((le_max_right A.sum E.sum).trans (le_max_right b _)).trans_lt hc)
  have hEne : E ≠ [] := List.ne_nil_of_mem hrE
  have hhead : (E ++ [c]).headD 0 = r := by
    obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil hEne
    simpa only [he, List.cons_append, List.headD_cons] using hEr
  refine ⟨A ++ [c], E ++ [c], r, c, ?_, ?_, ?_, ?_, by simp, by simp,
    hhead, List.mem_append_left _ hrA, hAc r hrA, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton, hAk]
    omega
  · simp only [List.length_append, List.length_singleton, hEl]
    omega
  · exact List.pairwise_append.mpr ⟨hAi, by simp,
      fun x hx y hy ↦ (List.mem_singleton.mp hy) ▸ hAc x hx⟩
  · exact List.pairwise_append.mpr ⟨hEi, by simp,
      fun x hx y hy ↦ (List.mem_singleton.mp hy) ▸ hEc x hx⟩
  · intro x hx hxc
    rcases List.mem_append.mp hx with hx | hx
    · exact (hA x hx).2.2
    · exact ((List.mem_singleton.mp hx).not_lt hxc).elim
  · intro x
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro ⟨ha | hc, he | hc'⟩
      · exact Or.inl ((hAE x).mp ⟨ha, he⟩)
      · exact Or.inr hc'
      · exact Or.inr hc
      · exact Or.inr hc
    · rintro (rfl | rfl)
      · exact ⟨Or.inl hrA, Or.inl hrE⟩
      · exact ⟨Or.inr rfl, Or.inr rfl⟩
  · intro x hx
    exact (List.mem_append.mp hx).elim (fun hx ↦ ⟨(hA x hx).1, (hA x hx).2.1⟩)
      (fun hx ↦ (List.mem_singleton.mp hx).symm ▸ ⟨hcH, hbc⟩)
  · intro x hx
    exact (List.mem_append.mp hx).elim (fun hx ↦ ⟨(hE x hx).1, (hE x hx).2.1⟩)
      (fun hx ↦ (List.mem_singleton.mp hx).symm ▸ ⟨hcH, hbc⟩)

structure Reserve (H : Set ℕ) (b l : ℕ) (S : Stem) where
  label : List ℕ
  card : label.length = l + 1
  increasing : label.Pairwise (· < ·)
  shared : ℕ
  first : label.headD 0 = shared
  sameLast : label.getLastD 0 = S.rootLabel.getLastD 0
  shared_mem : shared ∈ S.rootLabel
  shared_lt_last : shared < S.rootLabel.getLastD 0
  early : ∀ x ∈ S.rootLabel, x < S.rootLabel.getLastD 0 → x ≤ shared
  below : ∀ x ∈ label, x < S.root
  fresh : ∀ x ∈ label, x ∈ H ∧ b < x

def Reserve.move {H : Set ℕ} {b l : ℕ} {S : Stem} (Z : Reserve H b l S)
    (T : Stem) (hroot : T.root = S.root) (hlabel : T.rootLabel = S.rootLabel) :
    Reserve H b l T where
  label := Z.label
  card := Z.card
  increasing := Z.increasing
  shared := Z.shared
  first := Z.first
  sameLast := by rw [hlabel]; exact Z.sameLast
  shared_mem := by rw [hlabel]; exact Z.shared_mem
  shared_lt_last := by rw [hlabel]; exact Z.shared_lt_last
  early := by rw [hlabel]; exact Z.early
  below := by rw [hroot]; exact Z.below
  fresh := Z.fresh

def Reserve.weaken {H : Set ℕ} {b l : ℕ} {S : Stem} (Z : Reserve H b l S)
    (a : ℕ) (ha : a ≤ b) : Reserve H a l S where
  label := Z.label
  card := Z.card
  increasing := Z.increasing
  shared := Z.shared
  first := Z.first
  sameLast := Z.sameLast
  shared_mem := Z.shared_mem
  shared_lt_last := Z.shared_lt_last
  early := Z.early
  below := Z.below
  fresh := fun x hx ↦ ⟨(Z.fresh x hx).1, ha.trans_lt (Z.fresh x hx).2⟩

theorem root_reserved {H : Set ℕ} (hH : H.Infinite) (b k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    ∃ A : RootResponses.Setup k, ∃ _Z : Reserve H b l A.stem,
      ∀ x ∈ A.stem.decorated, x ∈ H ∧ b < x := by
  obtain ⟨C, D, r, c, hCk, hDl, hCi, hDi, hCl, hDl', hDf, hrC, hrc,
    hearly, _, hC, hD⟩ := labels hH b k l hk hl
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
  let Z : Reserve H b l A.stem :=
    { label := D, card := hDl, increasing := hDi, shared := r, first := hDf
      sameLast := by
        change D.getLastD 0 = S.rootLabel.getLastD 0
        rw [hlabel]
        exact hDl'.trans hCl.symm
      shared_mem := by change r ∈ S.rootLabel; rw [hlabel]; exact hrC
      shared_lt_last := by change r < S.rootLabel.getLastD 0; rw [hlabel]; exact hCl ▸ hrc
      early := by change ∀ x ∈ S.rootLabel, x < S.rootLabel.getLastD 0 → x ≤ r
                  rw [hlabel]; change ∀ x ∈ C, x < C.getLastD 0 → x ≤ r
                  rw [hCl]; exact hearly
      below := by intro x hx; change x < S.root; rw [hr]; exact hDm x hx
      fresh := hD }
  refine ⟨A, Z, ?_⟩
  intro x hx
  change x ∈ S.decorated at hx
  rw [hdec] at hx
  exact (List.mem_append.mp hx).elim (hE x) (hv x)

theorem Reserve.above_shared {H : Set ℕ} {b l : ℕ} {S : Stem} (Z : Reserve H b l S) :
    ExactSlots.above S.rootLabel Z.shared = [S.rootLabel.getLastD 0] := by
  have hne := List.ne_nil_of_mem Z.shared_mem
  have hlast : S.rootLabel.getLastD 0 ∈ S.rootLabel := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
    exact List.getLast_mem hne
  apply List.Pairwise.eq_of_mem_iff (S.label_pairwise.sublist List.filter_sublist)
    (by simp)
  intro x
  simp only [List.mem_filter, decide_eq_true_eq, List.mem_singleton]
  constructor
  · rintro ⟨hx, hxs⟩
    have hxlast := (S.label_pairwise.imp Nat.le_of_lt).rel_getLast hx
    have hlastD : S.rootLabel.getLastD 0 = S.rootLabel.getLast hne := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hne]
      rfl
    rw [← hlastD] at hxlast
    by_contra hn
    have hlt : x < S.rootLabel.getLastD 0 := lt_of_le_of_ne hxlast hn
    exact (not_lt_of_ge (Z.early x hx hlt)) hxs
  · rintro rfl
    exact ⟨hlast, Z.shared_lt_last⟩

theorem Reserve.pending_iff {H : Set ℕ} {b l : ℕ} (P : Pending)
    (Z : Reserve H b l P.position.stem) (hP : ExactSlots.Exact (.leaf P)) :
    P.roots = [P.position.stem.rootLabel.getLastD 0] ↔
      P.position.stem.done.length + 1 = Z.shared := by
  constructor
  · intro hR
    have hslot := (P.rootSlots.bounded _ (hR ▸ List.mem_singleton_self _)).1
    have hle := Z.early _ P.rootSelected hslot
    apply le_antisymm hle
    by_contra hn
    have hlt : P.position.stem.done.length + 1 < Z.shared := lt_of_not_ge hn
    have hm : Z.shared ∈ P.roots := by
      rw [hP.1]
      exact List.mem_filter.mpr ⟨Z.shared_mem, decide_eq_true hlt⟩
    rw [hR, List.mem_singleton] at hm
    exact Z.shared_lt_last.ne hm
  · intro he
    rw [hP.1, he]
    exact Z.above_shared

def Reserve.rootSetup {H : Set ℕ} {b l : ℕ} {S : Stem} (Z : Reserve H b l S)
    (hindex : S.done.length + 1 = Z.shared) : RootResponses.Setup l :=
  LabelOverlays.rootSetup S Z.label Z.increasing Z.below l Z.card (hindex.trans Z.first.symm)

theorem Reserve.rootSetup_ordinary {H : Set ℕ} {b l : ℕ} {S : Stem}
    (Z : Reserve H b l S) (hindex : S.done.length + 1 = Z.shared) :
    (Z.rootSetup hindex).stem.ordinary = S.ordinary :=
  LabelOverlays.plainStem_ordinary S Z.label Z.increasing Z.below

theorem Reserve.rootSetup_supported {H : Set ℕ} {b l : ℕ} {S : Stem}
    (Z : Reserve H b l S) (hindex : S.done.length + 1 = Z.shared)
    (hf : ∀ x ∈ S.ordinary, x ∈ H ∧ b < x) :
    ∀ x ∈ (Z.rootSetup hindex).stem.decorated, x ∈ H ∧ b < x :=
  LabelOverlays.plainStem_supported S Z.label Z.increasing Z.below Z.fresh hf

end Erdos118.AlignedRootReserve
