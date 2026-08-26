import ErdosProblems.Erdos118.LabelledExtensions

/-! Fresh local constructions retaining the labels of all plain filler bodies. -/

namespace Erdos118.SizedExtensions

open Negative Negative.Exact LabelledExtensions Erdos590.Larson

private theorem plain_labels (S T : Stem) (p : G2)
    (h : T.done = S.done ++ p.map plain) :
    T.bodyLabels = S.bodyLabels ++ List.replicate p.length [] := by
  simp [Stem.bodyLabels, h, plain, List.map_map, Function.comp_def]

theorem fill_to_stem_labels (P : Position) {H : Set ℕ} (hH : H.Infinite)
    (b j : ℕ) (hpj : P.stem.done.length < j) (hjm : j ≤ P.stem.root) :
    ∃ T : Stem, ∃ v : List ℕ, T.root = P.stem.root ∧ T.rootLabel = P.stem.rootLabel ∧
      T.done.length = j ∧ P.stem.done <+: T.done ∧
      P.bodyLabels <+: T.bodyLabels ∧
      T.decorated = P.decorated ++ v ∧ T.ordinary = P.ordinary ++ v ∧
      v ≠ [] ∧ (∀ z ∈ v, z ∈ H ∧ b < z) ∧
      ∃ e : ℕ, T.bodyLabels = P.bodyLabels ++ List.replicate e [] := by
  obtain ⟨S, u, hroot, hlabel, hlen, hpref, hlabels, hdec, hord, hune, hu⟩ :=
    finish_body P hH b
  have hlabelsEq : S.bodyLabels = P.bodyLabels :=
    (hlabels.eq_of_length (by simp [Position.bodyLabels, Stem.bodyLabels, hlen])).symm
  have hij : S.done.length ≤ j := by rw [hlen]; omega
  have hjS : j ≤ S.root := hroot.symm ▸ hjm
  obtain ⟨T, v, hroot', hlabel', hlen', hpref', hdec', hord', hv, p, hp⟩ :=
    fill_stem_plain S hH b j hij hjS
  have hTlabels : T.bodyLabels = P.bodyLabels ++ List.replicate p.length [] := by
    rw [plain_labels S T p hp, hlabelsEq]
  refine ⟨T, u ++ v, hroot'.trans hroot, hlabel'.trans hlabel, hlen',
    hpref.trans hpref', ?_, ?_, ?_, ?_, ?_, p.length, hTlabels⟩
  · rw [hTlabels]
    exact List.prefix_append _ _
  · rw [hdec', hdec, List.append_assoc]
  · rw [hord', hord, List.append_assoc]
  · intro he
    exact hune (List.append_eq_nil_iff.mp he).1
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hu z hz
    · exact hv z hz

theorem complete_labels (P : Position) {H : Set ℕ} (hH : H.Infinite) (b : ℕ) :
    ∃ T : Stem, ∃ hT : T.done.length = T.root, ∃ v : List ℕ,
      T.root = P.stem.root ∧ T.rootLabel = P.stem.rootLabel ∧ P.stem.done <+: T.done ∧
      P.bodyLabels <+: T.bodyLabels ∧
      T.decorated = P.decorated ++ v ∧ word (T.toGood hT).1 = P.ordinary ++ v ∧
      v ≠ [] ∧ (∀ z ∈ v, z ∈ H ∧ b < z) ∧
      ∃ e : ℕ, T.bodyLabels = P.bodyLabels ++ List.replicate e [] := by
  have hpm : P.stem.done.length < P.stem.root := by have h := P.room; omega
  obtain ⟨T, v, hroot, hlabel, hlen, hpref, hlabels, hdec, hord, hvne, hv, he⟩ :=
    fill_to_stem_labels P hH b P.stem.root hpm le_rfl
  have hT : T.done.length = T.root := hlen.trans hroot.symm
  exact ⟨T, hT, v, hroot, hlabel, hpref, hlabels, hdec,
    (T.toGood_word hT).trans hord, hvne, hv, he⟩

theorem start_labels {H : Set ℕ} (hH : H.Infinite) (b r : ℕ) :
    ∃ P : Position, P.stem.rootLabel.length = r + 1 ∧ P.label.length = 1 ∧
      P.stem.done.length + 1 = P.stem.rootLabel.headD 0 ∧
      P.entries.length = P.label.headD 0 ∧
      (∀ z ∈ P.stem.rootLabel, 0 < z) ∧ (∀ z ∈ P.label, 0 < z) ∧
      (∀ z ∈ P.decorated, z ∈ H ∧ b < z) ∧
      ∃ e : ℕ, P.stem.bodyLabels = List.replicate e [] := by
  obtain ⟨S, hSdone, hCsize, hCpos, hS⟩ := empty_stem hH b r
  have hCne : S.rootLabel ≠ [] := by intro he; simp [he] at hCsize
  have hc : S.rootLabel.headD 0 ∈ S.rootLabel := by
    obtain ⟨c, C, hC⟩ := List.exists_cons_of_ne_nil hCne
    simp [hC]
  have hcpos : 0 < S.rootLabel.headD 0 := hCpos _ hc
  have hcm : S.rootLabel.headD 0 < S.root := S.label_before_root _ hc
  have hcount : S.done.length ≤ S.rootLabel.headD 0 - 1 := by simp [hSdone]
  obtain ⟨T, u, hroot, hC, hlen, _, hdec, _, hu, p, hp⟩ :=
    fill_stem_plain S hH b (S.rootLabel.headD 0 - 1) hcount (by omega)
  have hroom : T.done.length + 1 < T.root := by rw [hlen, hroot]; omega
  obtain ⟨P, v, hP, hDsize, hentries, hDpos, _, hPdec, _, _, hv⟩ :=
    start_body T hH b 0 hroom
  refine ⟨P, ?_, hDsize, ?_, hentries, ?_, hDpos, ?_, p.length, ?_⟩
  · rw [hP, hC]
    exact hCsize
  · rw [hP, hlen, hC]
    omega
  · rw [hP, hC]
    exact hCpos
  · intro z hz
    rw [hPdec, hdec] at hz
    rcases List.mem_append.mp hz with hz | hz
    · rcases List.mem_append.mp hz with hz | hz
      · exact hS z hz
      · exact hu z hz
    · exact hv z hz
  · rw [hP, plain_labels S T p hp]
    simp [Stem.bodyLabels, hSdone]

theorem advance_body_labels (P : Position) {H : Set ℕ} (hH : H.Infinite)
    (b j k : ℕ) (hpj : P.stem.done.length + 1 < j) (hjm : j < P.stem.root) :
    ∃ Q : Position, ∃ d v : List ℕ,
      Q.stem.root = P.stem.root ∧ Q.stem.rootLabel = P.stem.rootLabel ∧
      Q.stem.done.length + 1 = j ∧ P.stem.done <+: Q.stem.done ∧
      P.bodyLabels <+: Q.bodyLabels ∧
      Q.label.length = k + 1 ∧ Q.entries.length = Q.label.headD 0 ∧
      (∀ z ∈ Q.label, 0 < z) ∧ Q.decorated = P.decorated ++ d ∧
      Q.ordinary = P.ordinary ++ v ∧ v ≠ [] ∧ v.Sublist d ∧
      (∀ z ∈ d, z ∈ H ∧ b < z) ∧ Q.label.Sublist d ∧
      ∃ e : ℕ, Q.bodyLabels = P.bodyLabels ++ List.replicate e [] ++ [Q.label] := by
  have hbefore : P.stem.done.length < j - 1 := by omega
  obtain ⟨T, u, hroot, hC, hlen, hpref, hlabels, hdec, hord, hune, hu, e, he⟩ :=
    fill_to_stem_labels P hH b (j - 1) hbefore (by omega)
  have hroom : T.done.length + 1 < T.root := by rw [hlen, hroot]; omega
  obtain ⟨Q, v, hQ, hDlen, hentries, hDpos, _, hQdec, hQord, _, hv⟩ :=
    start_body T hH b k hroom
  refine ⟨Q, u ++ (Q.label ++ v), u ++ v, ?_, ?_, ?_, ?_, ?_,
    hDlen, hentries, hDpos, ?_, ?_, ?_, ?_, ?_, ?_, e, ?_⟩
  · rw [hQ]
    exact hroot
  · rw [hQ]
    exact hC
  · rw [hQ, hlen]
    omega
  · rw [hQ]
    exact hpref
  · change P.bodyLabels <+: Q.stem.bodyLabels ++ [Q.label]
    rw [hQ]
    exact hlabels.trans (List.prefix_append _ _)
  · rw [hQdec, hdec, List.append_assoc]
  · rw [hQord, hord, List.append_assoc]
  · intro he
    exact hune (List.append_eq_nil_iff.mp he).1
  · exact (List.sublist_append_right Q.label v).append_left u
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hu z hz
    · exact hv z hz
  · exact (List.sublist_append_left _ _).trans (List.sublist_append_right _ _)
  · change Q.stem.bodyLabels ++ [Q.label] = _
    rw [hQ, he]

end Erdos118.SizedExtensions
