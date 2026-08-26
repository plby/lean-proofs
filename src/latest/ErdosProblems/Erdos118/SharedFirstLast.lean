import ErdosProblems.Erdos118.SharedLast

/-! Independently sized positive body labels with common first and last
indices, installed on two exact stems with one literal ordinary response. -/

namespace Erdos118.SharedFirstLast

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open Erdos590.Larson

theorem labels_separated {H : Set ℕ} (hH : H.Infinite) (b k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    ∃ C D : List ℕ, C.length = k + 1 ∧ D.length = l + 1 ∧
      C.Pairwise (· < ·) ∧ D.Pairwise (· < ·) ∧
      C.headD 0 = D.headD 0 ∧ C.getLastD 0 = D.getLastD 0 ∧
      (∀ x ∈ C, x < C.getLastD 0 → x < D.tail.headD 0) ∧
      (∀ x ∈ C, x ∈ H ∧ b < x) ∧ (∀ x ∈ D, x ∈ H ∧ b < x) := by
  obtain ⟨r, hrH, hbr⟩ := hH.exists_gt b
  obtain ⟨A, E, hAk, hEl, hAi, hEi, hlast, hsep, hA, hE⟩ :=
    SharedLast.labels_sizes hH r (k - 1) (l - 1)
  have hAne : A ≠ [] := by intro he; simp [he] at hAk
  have hEne : E ≠ [] := by intro he; simp [he] at hEl
  refine ⟨r :: A, r :: E, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_cons, hAk]
    omega
  · simp only [List.length_cons, hEl]
    omega
  · exact List.pairwise_cons.mpr ⟨fun x hx ↦ (hA x hx).2, hAi⟩
  · exact List.pairwise_cons.mpr ⟨fun x hx ↦ (hE x hx).2, hEi⟩
  · rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?,
      List.getLast?_cons_of_ne_nil hAne, List.getLast?_cons_of_ne_nil hEne]
    simpa only [List.getLastD_eq_getLast?] using hlast
  · intro x hx hlt
    change x < E.headD 0
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (hE _ (first_mem hEne)).2
    · have hlastA : (r :: A).getLastD 0 = A.getLastD 0 := by
        rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?,
          List.getLast?_cons_of_ne_nil hAne]
      exact hsep x hx (hlastA ▸ hlt)
  · intro x hx
    exact (List.mem_cons.mp hx).elim (fun he ↦ he.symm ▸ ⟨hrH, hbr⟩)
      (fun hx ↦ ⟨(hA x hx).1, hbr.trans (hA x hx).2⟩)
  · intro x hx
    exact (List.mem_cons.mp hx).elim (fun he ↦ he.symm ▸ ⟨hrH, hbr⟩)
      (fun hx ↦ ⟨(hE x hx).1, hbr.trans (hE x hx).2⟩)

theorem labels {H : Set ℕ} (hH : H.Infinite) (b k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    ∃ C D : List ℕ, C.length = k + 1 ∧ D.length = l + 1 ∧
      C.Pairwise (· < ·) ∧ D.Pairwise (· < ·) ∧
      C.headD 0 = D.headD 0 ∧ C.getLastD 0 = D.getLastD 0 ∧
      (∀ x ∈ C, x ∈ H ∧ b < x) ∧ (∀ x ∈ D, x ∈ H ∧ b < x) := by
  obtain ⟨C, D, hC, hD, hCi, hDi, hf, hl, _, hc, hd⟩ := labels_separated hH b k l hk hl
  exact ⟨C, D, hC, hD, hCi, hDi, hf, hl, hc, hd⟩

private def setup (S : Stem) (hroom : S.done.length + 1 < S.root)
    (C : List ℕ) (n : ℕ) (u : List ℕ) (k : ℕ) (hcard : C.length = k + 1)
    (hfirst : u.length = C.headD 0) (hpos : 0 < u.length) (hsmall : u.length < n)
    (hinc : (S.decorated ++ (C ++ n :: u)).Pairwise (· < ·)) : BodyResponses.Setup S k :=
  { position :=
      { stem := S, size := n, label := C, entries := u, room := hroom
        started := hpos, unfinished := hsmall, increasing := hinc }
    stem_eq := rfl, label_length := hcard, entries_length := hfirst }

theorem body_pair_of_labels {H : Set ℕ} (hH : H.Infinite)
    (S E : Stem) (hSroom : S.done.length + 1 < S.root) (hEroom : E.done.length + 1 < E.root)
    (hord : S.ordinary = E.ordinary) (b k l : ℕ) (C D : List ℕ)
    (hCk : C.length = k + 1) (hDl : D.length = l + 1)
    (hCi : C.Pairwise (· < ·)) (hDi : D.Pairwise (· < ·))
    (hfirst : C.headD 0 = D.headD 0)
    (hC : ∀ x ∈ C, x ∈ H ∧ max b (max S.decorated.sum E.decorated.sum) < x)
    (hD : ∀ x ∈ D, x ∈ H ∧ max b (max S.decorated.sum E.decorated.sum) < x) :
    ∃ A : BodyResponses.Setup S k, ∃ F : BodyResponses.Setup E l,
      A.position.ordinary = F.position.ordinary ∧ A.position.size = F.position.size ∧
      A.position.entries = F.position.entries ∧
      A.position.label = C ∧ F.position.label = D ∧
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H ∧ b < x) ∧
      (∀ x ∈ BodyResponses.newWord F.position, x ∈ H ∧ b < x) := by
  let L := max b (max S.decorated.sum E.decorated.sum)
  obtain ⟨n, hnH, hn⟩ := hH.exists_gt (max L (max C.sum D.sum))
  have hLn : L < n := (le_max_left _ _).trans_lt hn
  have hCn : ∀ x ∈ C, x < n := fun x hx ↦ (nat_le_sum_of_mem hx).trans_lt
    (((le_max_left C.sum D.sum).trans (le_max_right L _)).trans_lt hn)
  have hDn : ∀ x ∈ D, x < n := fun x hx ↦ (nat_le_sum_of_mem hx).trans_lt
    (((le_max_right C.sum D.sum).trans (le_max_right L _)).trans_lt hn)
  have hCne : C ≠ [] := by intro he; simp [he] at hCk
  have hhead := first_mem hCne
  have hpos : 0 < C.headD 0 := (Nat.zero_le L).trans_lt (hC _ hhead).2
  obtain ⟨u, hul, hui, hu⟩ := InteriorWords.fresh_list hH n (C.headD 0)
  have huPos : 0 < u.length := hul ▸ hpos
  have huSmall : u.length < n := hul ▸ hCn _ hhead
  have huD : u.length = D.headD 0 := hul.trans hfirst
  have htail : (n :: u).Pairwise (· < ·) :=
    List.pairwise_cons.mpr ⟨fun x hx ↦ (hu x hx).2, hui⟩
  have hnewInc : ∀ V : List ℕ, V.Pairwise (· < ·) → (∀ x ∈ V, x < n) →
      (V ++ n :: u).Pairwise (· < ·) := by
    intro V hi hv
    refine List.pairwise_append.mpr ⟨hi, htail, ?_⟩
    intro x hx y hy
    exact (List.mem_cons.mp hy).elim (fun he ↦ he.symm ▸ hv x hx)
      (fun hy ↦ (hv x hx).trans (hu y hy).2)
  have hnewFresh : ∀ V : List ℕ, (∀ x ∈ V, x ∈ H ∧ L < x) →
      ∀ x ∈ V ++ n :: u, x ∈ H ∧ L < x := by
    intro V hv x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hv x hx
    · exact (List.mem_cons.mp hx).elim (fun he ↦ he.symm ▸ ⟨hnH, hLn⟩)
        (fun hx ↦ ⟨(hu x hx).1, hLn.trans (hu x hx).2⟩)
  have hCf := hnewFresh C hC
  have hDf := hnewFresh D hD
  have hSi : (S.decorated ++ (C ++ n :: u)).Pairwise (· < ·) := by
    refine List.pairwise_append.mpr ⟨S.increasing, hnewInc C hCi hCn, ?_⟩
    intro x hx y hy
    exact ((nat_le_sum_of_mem hx).trans
      ((le_max_left S.decorated.sum E.decorated.sum).trans (le_max_right b _))).trans_lt
      (hCf y hy).2
  have hEi : (E.decorated ++ (D ++ n :: u)).Pairwise (· < ·) := by
    refine List.pairwise_append.mpr ⟨E.increasing, hnewInc D hDi hDn, ?_⟩
    intro x hx y hy
    exact ((nat_le_sum_of_mem hx).trans
      ((le_max_right S.decorated.sum E.decorated.sum).trans (le_max_right b _))).trans_lt
      (hDf y hy).2
  let A := setup S hSroom C n u k hCk hul huPos huSmall hSi
  let F := setup E hEroom D n u l hDl huD huPos huSmall hEi
  refine ⟨A, F, ?_, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · change S.ordinary ++ n :: u = E.ordinary ++ n :: u
    rw [hord]
  · intro x hx
    exact ⟨(hCf x hx).1, (le_max_left _ _).trans_lt (hCf x hx).2⟩
  · intro x hx
    exact ⟨(hDf x hx).1, (le_max_left _ _).trans_lt (hDf x hx).2⟩

theorem body_pair_separated {H : Set ℕ} (hH : H.Infinite)
    (S E : Stem) (hSroom : S.done.length + 1 < S.root) (hEroom : E.done.length + 1 < E.root)
    (hord : S.ordinary = E.ordinary) (b k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    ∃ A : BodyResponses.Setup S k, ∃ F : BodyResponses.Setup E l,
      A.position.ordinary = F.position.ordinary ∧ A.position.size = F.position.size ∧
      A.position.entries = F.position.entries ∧
      A.position.label.headD 0 = F.position.label.headD 0 ∧
      A.position.label.getLastD 0 = F.position.label.getLastD 0 ∧
      (∀ x ∈ A.position.label, x < A.position.label.getLastD 0 →
        x < F.position.label.tail.headD 0) ∧
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H ∧ b < x) ∧
      (∀ x ∈ BodyResponses.newWord F.position, x ∈ H ∧ b < x) := by
  obtain ⟨C, D, hCk, hDl, hCi, hDi, hfirst, hlast, hsep, hC, hD⟩ :=
    labels_separated hH (max b (max S.decorated.sum E.decorated.sum)) k l hk hl
  obtain ⟨A, F, hord, hmarker, hentries, hAC, hFD, hAf, hFf⟩ :=
    body_pair_of_labels hH S E hSroom hEroom hord b k l C D hCk hDl hCi hDi hfirst hC hD
  exact ⟨A, F, hord, hmarker, hentries, by rw [hAC, hFD]; exact hfirst,
    by rw [hAC, hFD]; exact hlast, by rw [hAC, hFD]; exact hsep, hAf, hFf⟩

theorem body_pair {H : Set ℕ} (hH : H.Infinite)
    (S E : Stem) (hSroom : S.done.length + 1 < S.root) (hEroom : E.done.length + 1 < E.root)
    (hord : S.ordinary = E.ordinary) (b k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    ∃ A : BodyResponses.Setup S k, ∃ F : BodyResponses.Setup E l,
      A.position.ordinary = F.position.ordinary ∧ A.position.size = F.position.size ∧
      A.position.entries = F.position.entries ∧
      A.position.label.headD 0 = F.position.label.headD 0 ∧
      A.position.label.getLastD 0 = F.position.label.getLastD 0 ∧
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H ∧ b < x) ∧
      (∀ x ∈ BodyResponses.newWord F.position, x ∈ H ∧ b < x) := by
  obtain ⟨A, F, hord, hm, he, hf, hl, _, hA, hF⟩ :=
    body_pair_separated hH S E hSroom hEroom hord b k l hk hl
  exact ⟨A, F, hord, hm, he, hf, hl, hA, hF⟩

end Erdos118.SharedFirstLast
