import ErdosProblems.Erdos118.InteriorWords

/-!
Literal partial words with labels inserted before their markers. Decorated
increase controls labels as well as nodes; deleting labels retains the exact
ordinary word. No coloring theorem is assumed here.
-/

namespace Erdos118.LabelledExtensions

open Negative Negative.Exact Erdos590.Larson

structure Body where
  values : List ℕ
  label : List ℕ

def Body.ordinary (a : Body) : List ℕ := levelWord a.values
def Body.decorated (a : Body) : List ℕ := a.label ++ a.ordinary
def plain (a : List ℕ) : Body := ⟨a, []⟩

theorem ordinary_sublist_decorated (p : List Body) :
    (p.flatMap Body.ordinary).Sublist (p.flatMap Body.decorated) := by
  induction p with
  | nil => exact List.Sublist.refl _
  | cons a p ih =>
    exact (List.sublist_append_right a.label a.ordinary).append ih

@[simp] theorem plain_decorated (p : G2) :
    (p.map plain).flatMap Body.decorated = p.flatMap levelWord := by
  simp [List.flatMap_map, plain, Body.decorated, Body.ordinary]

@[simp] theorem plain_ordinary (p : G2) :
    (p.map plain).flatMap Body.ordinary = p.flatMap levelWord := by
  simp [List.flatMap_map, plain, Body.ordinary]

structure Stem where
  root : ℕ
  rootLabel : List ℕ
  done : List Body
  count : done.length ≤ root
  increasing : (rootLabel ++ (root :: done.flatMap Body.decorated)).Pairwise (· < ·)

def Stem.decorated (S : Stem) : List ℕ :=
  S.rootLabel ++ (S.root :: S.done.flatMap Body.decorated)

def Stem.ordinary (S : Stem) : List ℕ := S.root :: S.done.flatMap Body.ordinary

def Stem.bodyLabels (S : Stem) : List (List ℕ) := S.done.map Body.label

theorem Stem.bodyLabels_prefix {S T : Stem} (h : S.done <+: T.done) :
    S.bodyLabels <+: T.bodyLabels := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r.map Body.label, ?_⟩
  change S.done.map Body.label ++ r.map Body.label = T.done.map Body.label
  rw [← List.map_append, hr]

theorem Stem.ordinary_sublist (S : Stem) : S.ordinary.Sublist S.decorated := by
  exact ((ordinary_sublist_decorated S.done).cons_cons S.root).trans
    (List.sublist_append_right S.rootLabel _)

theorem Stem.label_before_root (S : Stem) : ∀ x ∈ S.rootLabel, x < S.root := by
  intro x hx
  exact (List.pairwise_append.mp S.increasing).2.2 x hx _ (List.mem_cons_self ..)

theorem Stem.label_pairwise (S : Stem) : S.rootLabel.Pairwise (· < ·) :=
  (List.pairwise_append.mp S.increasing).1

structure Position where
  stem : Stem
  size : ℕ
  label : List ℕ
  entries : List ℕ
  room : stem.done.length + 1 < stem.root
  started : 0 < entries.length
  unfinished : entries.length < size
  increasing : (stem.decorated ++ (label ++ size :: entries)).Pairwise (· < ·)

def Position.decorated (P : Position) : List ℕ :=
  P.stem.decorated ++ (P.label ++ P.size :: P.entries)

def Position.ordinary (P : Position) : List ℕ :=
  P.stem.ordinary ++ (P.size :: P.entries)

def Position.bodyLabels (P : Position) : List (List ℕ) := P.stem.bodyLabels ++ [P.label]

theorem Position.ordinary_sublist (P : Position) : P.ordinary.Sublist P.decorated :=
  P.stem.ordinary_sublist.append (List.sublist_append_right P.label _)

theorem Position.label_before_marker (P : Position) : ∀ x ∈ P.label, x < P.size := by
  intro x hx
  exact (List.pairwise_append.mp (List.pairwise_append.mp P.increasing).2.1).2.2
    x hx _ (List.mem_cons_self ..)

theorem Position.label_pairwise (P : Position) : P.label.Pairwise (· < ·) :=
  (List.pairwise_append.mp (List.pairwise_append.mp P.increasing).2.1).1

def Position.toInterior (P : Position) : InteriorWords.Position where
  root := P.stem.root
  done := P.stem.done.map Body.values
  size := P.size
  entries := P.entries
  room := by simpa using P.room
  started := P.started
  unfinished := P.unfinished
  increasing := by
    rw [PartialWordResponses.partialWord, List.flatMap_map]
    exact P.increasing.sublist P.ordinary_sublist

theorem Position.toInterior_word (P : Position) : P.toInterior.word = P.ordinary := by
  change PartialWordResponses.partialWord P.stem.root (P.stem.done.map Body.values)
    P.size P.entries = P.ordinary
  rw [PartialWordResponses.partialWord, List.flatMap_map]
  rfl

theorem empty_stem {H : Set ℕ} (hH : H.Infinite) (b k : ℕ) :
    ∃ S : Stem, S.done = [] ∧ S.rootLabel.length = k + 1 ∧
      (∀ z ∈ S.rootLabel, 0 < z) ∧
      ∀ z ∈ S.decorated, z ∈ H ∧ b < z := by
  obtain ⟨C, hlen, hpair, hC⟩ := InteriorWords.fresh_list hH b (k + 1)
  obtain ⟨m, hmH, hm⟩ := hH.exists_gt (max b C.sum)
  have hbm : b < m := (le_max_left _ _).trans_lt hm
  have hCm : ∀ z ∈ C, z < m := fun z hz ↦
    (nat_le_sum_of_mem hz).trans_lt ((le_max_right _ _).trans_lt hm)
  let S : Stem :=
    { root := m, rootLabel := C, done := [], count := Nat.zero_le _
      increasing := by
        apply List.pairwise_append.mpr
        refine ⟨hpair, by simp, ?_⟩
        intro z hz y hy
        have he : y = m := by simpa using hy
        exact he ▸ hCm z hz }
  refine ⟨S, rfl, hlen, fun z hz ↦ (Nat.zero_le b).trans_lt (hC z hz).2, ?_⟩
  intro z hz
  change z ∈ C ++ [m] at hz
  rcases List.mem_append.mp hz with hz | hz
  · exact hC z hz
  · have he : z = m := by simpa using hz
    subst z
    exact ⟨hmH, hbm⟩

theorem fill_stem_plain (S : Stem) {H : Set ℕ} (hH : H.Infinite)
    (b j : ℕ) (hij : S.done.length ≤ j) (hjm : j ≤ S.root) :
    ∃ T : Stem, ∃ v : List ℕ,
      T.root = S.root ∧ T.rootLabel = S.rootLabel ∧ T.done.length = j ∧
      S.done <+: T.done ∧ T.decorated = S.decorated ++ v ∧
      T.ordinary = S.ordinary ++ v ∧ (∀ z ∈ v, z ∈ H ∧ b < z) ∧
      ∃ p : G2, T.done = S.done ++ p.map plain := by
  let L := max b S.decorated.sum
  let f := enumOf H
  have hf : StrictMono f := enumOf_strictMono hH
  let t := CoordinateModel.normalizeTail f L (List.replicate (j - S.done.length) [])
  have htlen : t.length = j - S.done.length := by simp [t]
  have ht := CoordinateModel.normalizeTail_spec hf L (List.replicate (j - S.done.length) [])
  let d := S.done ++ t.map plain
  have hdlen : d.length = j := by simp [d, htlen, Nat.add_sub_of_le hij]
  have hdec : S.rootLabel ++ (S.root :: d.flatMap Body.decorated) =
      S.decorated ++ t.flatMap levelWord := by
    simp [d, Stem.decorated, List.append_assoc]
  have hord : S.root :: d.flatMap Body.ordinary = S.ordinary ++ t.flatMap levelWord := by
    simp [d, Stem.ordinary]
  let T : Stem :=
    { root := S.root, rootLabel := S.rootLabel, done := d
      count := hdlen ▸ hjm
      increasing := by
        rw [hdec]
        refine List.pairwise_append.mpr ⟨S.increasing, ht.2.1, ?_⟩
        intro x hx y hy
        exact ((nat_le_sum_of_mem hx).trans (le_max_right _ _)).trans_lt (ht.1 y hy) }
  refine ⟨T, t.flatMap levelWord, rfl, rfl, hdlen, List.prefix_append _ _, hdec, hord,
    ?_, t, rfl⟩
  intro z hz
  obtain ⟨i, hi⟩ := ht.2.2 z hz
  exact ⟨hi ▸ enumOf_mem hH i, (le_max_left _ _).trans_lt (ht.1 z hz)⟩

theorem fill_stem (S : Stem) {H : Set ℕ} (hH : H.Infinite)
    (b j : ℕ) (hij : S.done.length ≤ j) (hjm : j ≤ S.root) :
    ∃ T : Stem, ∃ v : List ℕ,
      T.root = S.root ∧ T.rootLabel = S.rootLabel ∧ T.done.length = j ∧
      S.done <+: T.done ∧ T.decorated = S.decorated ++ v ∧
      T.ordinary = S.ordinary ++ v ∧ ∀ z ∈ v, z ∈ H ∧ b < z := by
  obtain ⟨T, v, hr, hC, hlen, hprefix, hdec, hord, hfresh, _⟩ :=
    fill_stem_plain S hH b j hij hjm
  exact ⟨T, v, hr, hC, hlen, hprefix, hdec, hord, hfresh⟩

/-- The label is chosen only after the entire old stem. Its first coordinate
is an actual positive leaf count, strictly below the new body marker. -/
theorem start_body (S : Stem) {H : Set ℕ} (hH : H.Infinite) (b k : ℕ)
    (hroom : S.done.length + 1 < S.root) :
    ∃ P : Position, ∃ v : List ℕ, P.stem = S ∧ P.label.length = k + 1 ∧
      P.entries.length = P.label.headD 0 ∧ (∀ z ∈ P.label, 0 < z) ∧
      P.label.Pairwise (· < ·) ∧
      P.decorated = S.decorated ++ (P.label ++ v) ∧
      P.ordinary = S.ordinary ++ v ∧ v ≠ [] ∧
      ∀ z ∈ P.label ++ v, z ∈ H ∧ b < z := by
  let L := max b S.decorated.sum
  obtain ⟨D, hDlen, hDpair, hD⟩ := InteriorWords.fresh_list hH L (k + 1)
  have hDne : D ≠ [] := by intro he; simp [he] at hDlen
  obtain ⟨d, D, rfl⟩ := List.exists_cons_of_ne_nil hDne
  obtain ⟨n, hnH, hn⟩ := hH.exists_gt (max L (d :: D).sum)
  have hLn : L < n := (le_max_left _ _).trans_lt hn
  have hDn : ∀ z ∈ d :: D, z < n := fun z hz ↦
    (nat_le_sum_of_mem hz).trans_lt ((le_max_right _ _).trans_lt hn)
  have hdpos : 0 < d := (Nat.zero_le L).trans_lt (hD d (List.mem_cons_self ..)).2
  have hdn : d < n := hDn d (List.mem_cons_self ..)
  obtain ⟨u, hulen, hupair, hu⟩ := InteriorWords.fresh_list hH n d
  have hnupair : (n :: u).Pairwise (· < ·) :=
    List.pairwise_cons.mpr ⟨fun z hz ↦ (hu z hz).2, hupair⟩
  have hnewpair : ((d :: D) ++ n :: u).Pairwise (· < ·) := by
    refine List.pairwise_append.mpr ⟨hDpair, hnupair, ?_⟩
    intro x hx y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hDn x hx
    · exact (hDn x hx).trans (hu y hy).2
  have hnew : ∀ z ∈ (d :: D) ++ n :: u, z ∈ H ∧ L < z := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hD z hz
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨hnH, hLn⟩
      · exact ⟨(hu z hz).1, hLn.trans (hu z hz).2⟩
  let P : Position :=
    { stem := S, size := n, label := d :: D, entries := u
      room := hroom, started := hulen ▸ hdpos, unfinished := hulen ▸ hdn
      increasing := by
        refine List.pairwise_append.mpr ⟨S.increasing, hnewpair, ?_⟩
        intro x hx y hy
        exact ((nat_le_sum_of_mem hx).trans (le_max_right _ _)).trans_lt (hnew y hy).2 }
  refine ⟨P, n :: u, rfl, hDlen, hulen,
    fun z hz ↦ (Nat.zero_le L).trans_lt (hD z hz).2,
    hDpair, rfl, rfl, List.cons_ne_nil _ _, ?_⟩
  exact fun z hz ↦ ⟨(hnew z hz).1, (le_max_left _ _).trans_lt (hnew z hz).2⟩

theorem advance_leaf (P : Position) {H : Set ℕ} (hH : H.Infinite)
    (b j : ℕ) (huj : P.entries.length < j) (hjn : j < P.size) :
    ∃ Q : Position, ∃ v : List ℕ, Q.stem = P.stem ∧ Q.size = P.size ∧
      Q.label = P.label ∧ Q.entries.length = j ∧
      Q.decorated = P.decorated ++ v ∧ Q.ordinary = P.ordinary ++ v ∧
      v ≠ [] ∧ ∀ z ∈ v, z ∈ H ∧ b < z := by
  let L := max b P.decorated.sum
  obtain ⟨v, hvlen, hvpair, hv⟩ := InteriorWords.fresh_list hH L (j - P.entries.length)
  have hlen : (P.entries ++ v).length = j := by
    simp only [List.length_append, hvlen]
    omega
  have hdec : P.stem.decorated ++ (P.label ++ P.size :: (P.entries ++ v)) =
      P.decorated ++ v := by simp [Position.decorated, List.append_assoc]
  let Q : Position :=
    { stem := P.stem, size := P.size, label := P.label, entries := P.entries ++ v
      room := P.room, started := by rw [hlen]; omega
      unfinished := hlen ▸ hjn
      increasing := by
        rw [hdec]
        refine List.pairwise_append.mpr ⟨P.increasing, hvpair, ?_⟩
        intro x hx y hy
        exact ((nat_le_sum_of_mem hx).trans (le_max_right _ _)).trans_lt (hv y hy).2 }
  refine ⟨Q, v, rfl, rfl, rfl, hlen, hdec, ?_, ?_, ?_⟩
  · simp [Q, Position.ordinary, List.append_assoc]
  · intro he
    simp [he] at hvlen
    omega
  · exact fun z hz ↦ ⟨(hv z hz).1, (le_max_left _ _).trans_lt (hv z hz).2⟩

/-- Closing the current body preserves its label and its numerical marker. -/
theorem finish_body (P : Position) {H : Set ℕ} (hH : H.Infinite) (b : ℕ) :
    ∃ S : Stem, ∃ v : List ℕ, S.root = P.stem.root ∧ S.rootLabel = P.stem.rootLabel ∧
      S.done.length = P.stem.done.length + 1 ∧ P.stem.done <+: S.done ∧
      P.bodyLabels <+: S.bodyLabels ∧
      S.decorated = P.decorated ++ v ∧ S.ordinary = P.ordinary ++ v ∧
      v ≠ [] ∧ ∀ z ∈ v, z ∈ H ∧ b < z := by
  let L := max b P.decorated.sum
  obtain ⟨v, hvlen, hvpair, hv⟩ := InteriorWords.fresh_list hH L (P.size - P.entries.length)
  have hlen : (P.entries ++ v).length = P.size := by
    simp only [List.length_append, hvlen]
    have h := P.unfinished
    omega
  let a : Body := ⟨P.entries ++ v, P.label⟩
  let d := P.stem.done ++ [a]
  have hdlen : d.length = P.stem.done.length + 1 := by simp [d]
  have hdec : P.stem.rootLabel ++ (P.stem.root :: d.flatMap Body.decorated) =
      P.decorated ++ v := by
    simp [d, a, Body.decorated, Body.ordinary, levelWord, hlen,
      Position.decorated, Stem.decorated, List.append_assoc]
  have hord : P.stem.root :: d.flatMap Body.ordinary = P.ordinary ++ v := by
    simp [d, a, Body.ordinary, levelWord, hlen, Position.ordinary, Stem.ordinary,
      List.append_assoc]
  let S : Stem :=
    { root := P.stem.root, rootLabel := P.stem.rootLabel, done := d
      count := hdlen ▸ P.room.le
      increasing := by
        rw [hdec]
        refine List.pairwise_append.mpr ⟨P.increasing, hvpair, ?_⟩
        intro x hx y hy
        exact ((nat_le_sum_of_mem hx).trans (le_max_right _ _)).trans_lt (hv y hy).2 }
  refine ⟨S, v, rfl, rfl, hdlen, List.prefix_append _ _, ?_, hdec, hord, ?_, ?_⟩
  · simp [Position.bodyLabels, Stem.bodyLabels, S, d, a]
  · intro he
    simp [he] at hvlen
    have h := P.unfinished
    omega
  · exact fun z hz ↦ ⟨(hv z hz).1, (le_max_left _ _).trans_lt (hv z hz).2⟩

theorem fill_to_stem (P : Position) {H : Set ℕ} (hH : H.Infinite)
    (b j : ℕ) (hpj : P.stem.done.length < j) (hjm : j ≤ P.stem.root) :
    ∃ T : Stem, ∃ v : List ℕ, T.root = P.stem.root ∧ T.rootLabel = P.stem.rootLabel ∧
      T.done.length = j ∧ P.stem.done <+: T.done ∧
      P.bodyLabels <+: T.bodyLabels ∧
      T.decorated = P.decorated ++ v ∧ T.ordinary = P.ordinary ++ v ∧
      v ≠ [] ∧ ∀ z ∈ v, z ∈ H ∧ b < z := by
  obtain ⟨S, u, hroot, hlabel, hlen, hpref, hlabels, hdec, hord, hune, hu⟩ := finish_body P hH b
  have hij : S.done.length ≤ j := by rw [hlen]; omega
  have hjS : j ≤ S.root := hroot.symm ▸ hjm
  obtain ⟨T, v, hroot', hlabel', hlen', hpref', hdec', hord', hv⟩ :=
    fill_stem S hH b j hij hjS
  refine ⟨T, u ++ v, hroot'.trans hroot, hlabel'.trans hlabel, hlen',
    hpref.trans hpref', hlabels.trans (Stem.bodyLabels_prefix hpref'), ?_, ?_, ?_, ?_⟩
  · rw [hdec', hdec, List.append_assoc]
  · rw [hord', hord, List.append_assoc]
  · intro he
    exact hune (List.append_eq_nil_iff.mp he).1
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hu z hz
    · exact hv z hz

def Stem.toGood (S : Stem) (hfull : S.done.length = S.root) : G :=
  ⟨S.done.map Body.values, by
    rw [word, List.length_map, hfull, List.flatMap_map]
    exact S.increasing.sublist S.ordinary_sublist⟩

theorem Stem.toGood_word (S : Stem) (hfull : S.done.length = S.root) :
    word (S.toGood hfull).1 = S.ordinary := by
  change word (S.done.map Body.values) = S.ordinary
  rw [word, List.length_map, hfull, List.flatMap_map]
  rfl

theorem complete (P : Position) {H : Set ℕ} (hH : H.Infinite) (b : ℕ) :
    ∃ T : Stem, ∃ hT : T.done.length = T.root, ∃ v : List ℕ,
      T.root = P.stem.root ∧ T.rootLabel = P.stem.rootLabel ∧ P.stem.done <+: T.done ∧
      P.bodyLabels <+: T.bodyLabels ∧
      T.decorated = P.decorated ++ v ∧ word (T.toGood hT).1 = P.ordinary ++ v ∧
      v ≠ [] ∧ ∀ z ∈ v, z ∈ H ∧ b < z := by
  have hpm : P.stem.done.length < P.stem.root := by have h := P.room; omega
  obtain ⟨T, v, hroot, hlabel, hlen, hpref, hlabels, hdec, hord, hvne, hv⟩ :=
    fill_to_stem P hH b P.stem.root hpm (le_refl _)
  have hT : T.done.length = T.root := hlen.trans hroot.symm
  exact ⟨T, hT, v, hroot, hlabel, hpref, hlabels, hdec,
    (T.toGood_word hT).trans hord, hvne, hv⟩

/-- Start at the first one-based body slot of the freshly chosen root label,
and at the sole leaf slot of the initial body label. -/
theorem start {H : Set ℕ} (hH : H.Infinite) (b r : ℕ) :
    ∃ P : Position, P.stem.rootLabel.length = r + 1 ∧ P.label.length = 1 ∧
      P.stem.done.length + 1 = P.stem.rootLabel.headD 0 ∧
      P.entries.length = P.label.headD 0 ∧
      (∀ z ∈ P.stem.rootLabel, 0 < z) ∧ (∀ z ∈ P.label, 0 < z) ∧
      ∀ z ∈ P.decorated, z ∈ H ∧ b < z := by
  obtain ⟨S, hSdone, hCsize, hCpos, hS⟩ := empty_stem hH b r
  have hCne : S.rootLabel ≠ [] := by intro he; simp [he] at hCsize
  have hc : S.rootLabel.headD 0 ∈ S.rootLabel := by
    obtain ⟨c, C, hC⟩ := List.exists_cons_of_ne_nil hCne
    simp [hC]
  have hcpos : 0 < S.rootLabel.headD 0 := hCpos _ hc
  have hcm : S.rootLabel.headD 0 < S.root := S.label_before_root _ hc
  have hcount : S.done.length ≤ S.rootLabel.headD 0 - 1 := by simp [hSdone]
  obtain ⟨T, u, hroot, hC, hlen, _, hdec, _, hu⟩ :=
    fill_stem S hH b (S.rootLabel.headD 0 - 1) hcount (by omega)
  have hroom : T.done.length + 1 < T.root := by rw [hlen, hroot]; omega
  obtain ⟨P, v, hP, hDsize, hentries, hDpos, _, hPdec, _, _, hv⟩ :=
    start_body T hH b 0 hroom
  refine ⟨P, ?_, hDsize, ?_, hentries, ?_, hDpos, ?_⟩
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

/-- Move to a prescribed later one-based body slot, choosing the new leaf
label only after all intervening filler. Both appended words are explicit. -/
theorem advance_body (P : Position) {H : Set ℕ} (hH : H.Infinite)
    (b j k : ℕ) (hpj : P.stem.done.length + 1 < j) (hjm : j < P.stem.root) :
    ∃ Q : Position, ∃ d v : List ℕ,
      Q.stem.root = P.stem.root ∧ Q.stem.rootLabel = P.stem.rootLabel ∧
      Q.stem.done.length + 1 = j ∧ P.stem.done <+: Q.stem.done ∧
      P.bodyLabels <+: Q.bodyLabels ∧
      Q.label.length = k + 1 ∧ Q.entries.length = Q.label.headD 0 ∧
      (∀ z ∈ Q.label, 0 < z) ∧ Q.decorated = P.decorated ++ d ∧
      Q.ordinary = P.ordinary ++ v ∧ v ≠ [] ∧ v.Sublist d ∧
      ∀ z ∈ d, z ∈ H ∧ b < z := by
  have hbefore : P.stem.done.length < j - 1 := by omega
  obtain ⟨T, u, hroot, hC, hlen, hpref, hlabels, hdec, hord, hune, hu⟩ :=
    fill_to_stem P hH b (j - 1) hbefore (by omega)
  have hroom : T.done.length + 1 < T.root := by rw [hlen, hroot]; omega
  obtain ⟨Q, v, hQ, hDlen, hentries, hDpos, _, hQdec, hQord, _, hv⟩ :=
    start_body T hH b k hroom
  refine ⟨Q, u ++ (Q.label ++ v), u ++ v, ?_, ?_, ?_, ?_, ?_,
    hDlen, hentries, hDpos, ?_, ?_, ?_, ?_, ?_⟩
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

end Erdos118.LabelledExtensions
