/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Alternating
import ErdosProblems.Erdos518.Rotation

/-!
# A long monochromatic path

This file proves the diagonal case of the Gerencsér--Gyárfás path Ramsey theorem.  In a
red--blue colouring of the complete graph on `V` (represented by `G` and `Gᶜ`) one of the
two colours has a path on at least `⌊2 * |V| / 3⌋ + 1` vertices.
-/

open scoped SimpleGraph

namespace Erdos518

universe u

variable {V : Type u}

private lemma isPath_prepend_one [DecidableEq V] {H : SimpleGraph V}
    {p : List V} (hp : IsPath H p) {x : V}
    (hx : x ∉ p) (hxp : H.Adj x (p.head hp.1)) : IsPath H (x :: p) := by
  cases p with
  | nil => exact (hp.1 rfl).elim
  | cons y p =>
    simp only [List.head_cons] at hxp
    exact ⟨by simp, hp.2.1.cons hx, .cons_cons hxp hp.2.2⟩

private lemma closed_path_extend_at [DecidableEq V] {H : SimpleGraph V}
    {p : List V} (hp : IsPath H p)
    (hclosed : H.Adj (p.head hp.1) (p.getLast hp.1))
    {x v : V} (hx : x ∉ p) (hv : v ∈ p) (hxv : H.Adj x v) :
    ∃ q : List V, IsPath H q ∧ q.length = p.length + 1 := by
  obtain ⟨l, r, hpEq, _⟩ := List.eq_append_cons_of_mem hv
  subst p
  cases l with
  | nil =>
      refine ⟨x :: v :: r, ?_, by simp⟩
      apply isPath_prepend_one hp
      · exact hx
      · simpa using hxv
  | cons a l =>
      let core : List V := (v :: r) ++ a :: l
      have hperm : List.Perm core ((a :: l) ++ v :: r) := by
        exact List.perm_append_comm
      have hcoreN : core.Nodup := hperm.nodup_iff.mpr hp.2.1
      have hsplit := List.isChain_split.mp hp.2.2
      have hprefix : (a :: l).IsChain H.Adj := by
        have := hsplit.1.dropLast
        change List.IsChain H.Adj (((a :: l) ++ [v]).dropLast) at this
        rw [List.dropLast_concat] at this
        exact this
      have hclosed' : H.Adj a ((v :: r).getLast (by simp)) := by
        change H.Adj a (((a :: l) ++ (v :: r)).getLast (by simp)) at hclosed
        rw [List.getLast_append_of_ne_nil] at hclosed
        exact hclosed
      have hcoreC : core.IsChain H.Adj := by
        apply hsplit.2.append hprefix
        intro z hz w hw
        rw [List.getLast?_eq_some_getLast (by simp)] at hz
        rw [List.head?_eq_some_head (by simp)] at hw
        simp only [Option.mem_some_iff] at hz hw
        subst z
        subst w
        simpa using hclosed'.symm
      have hcore : IsPath H core := ⟨by simp [core], hcoreN, hcoreC⟩
      have hxcore : x ∉ core := by
        intro h
        exact hx (hperm.mem_iff.mp h)
      refine ⟨x :: core, isPath_prepend_one hcore hxcore ?_, ?_⟩
      · simpa [core] using hxv
      · simp [core]
        omega

lemma compl_cross_of_closed_longest [DecidableEq V] {H : SimpleGraph V}
    {p : List V} (hp : IsPath H p) (hmax : IsGloballyLongestMonoPath H p)
    (hclosed : H.Adj (p.head hp.1) (p.getLast hp.1))
    {x y : V} (hx : x ∉ p) (hy : y ∈ p) : Hᶜ.Adj x y := by
  rw [SimpleGraph.compl_adj]
  refine ⟨fun hxy ↦ hx (hxy ▸ hy), ?_⟩
  intro hxy
  obtain ⟨q, hq, hlen⟩ := closed_path_extend_at hp hclosed hx hy hxy
  have hle := hmax.2 q (Or.inl hq)
  omega

private lemma card_compl_pathVertices [Fintype V] [DecidableEq V]
    {p : List V} (hp : p.Nodup) :
    (Finset.univ \ p.toFinset).card = Fintype.card V - p.length := by
  rw [Finset.card_sdiff]
  simp [List.toFinset_card_of_nodup hp]

private lemma closed_longest_two_thirds [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {p : List V} (hp : IsPath H p)
    (hmax : IsGloballyLongestMonoPath H p)
    (hclosed : H.Adj (p.head hp.1) (p.getLast hp.1)) :
    Fintype.card V * 2 / 3 + 1 ≤ p.length := by
  by_contra hbound
  have hshort : p.length < Fintype.card V * 2 / 3 + 1 := Nat.lt_of_not_ge hbound
  have hplen : p.length ≤ Fintype.card V := hp.2.1.length_le_card
  have hp2 : 2 ≤ p.length := by
    cases p with
    | nil => exact (hp.1 rfl).elim
    | cons a p =>
      cases p with
      | nil => simpa using hclosed
      | cons b p => simp
  let O : Finset V := Finset.univ \ p.toFinset
  have hOcard : O.card = Fintype.card V - p.length := by
    simpa [O] using card_compl_pathVertices hp.2.1
  have hOlarge : (p.length + 1) / 2 ≤ O.card := by
    rw [hOcard]
    omega
  rcases Nat.even_or_odd p.length with heven | hodd
  · rcases heven with ⟨t, ht⟩
    have hYle : t ≤ O.card := by omega
    have hXle : t + 1 ≤ p.toFinset.card := by
      rw [List.toFinset_card_of_nodup hp.2.1]
      omega
    obtain ⟨Y, hYO, hYcard⟩ := Finset.exists_subset_card_eq hYle
    obtain ⟨X, hXp, hXcard⟩ := Finset.exists_subset_card_eq hXle
    have hdisj : Disjoint X Y := Finset.disjoint_left.mpr fun z hzX hzY ↦ by
      have hzp : z ∈ p.toFinset := hXp hzX
      have hzO : z ∈ O := hYO hzY
      exact (Finset.mem_sdiff.mp hzO).2 hzp
    have hadj : ∀ x ∈ X, ∀ y ∈ Y, Hᶜ.Adj x y := by
      intro x hxX y hyY
      apply (compl_cross_of_closed_longest hp hmax hclosed ?_ ?_).symm
      · exact fun hyp ↦ (Finset.mem_sdiff.mp (hYO hyY)).2 (List.mem_toFinset.mpr hyp)
      · exact List.mem_toFinset.mp (hXp hxX)
    have hcard : X.card = Y.card + 1 := by omega
    have hq : IsPath Hᶜ (alternateFinsets X Y) :=
      isPath_alternateFinsets_of_card_eq_add_one hcard hdisj hadj
    have hle := hmax.2 (alternateFinsets X Y) (Or.inr hq)
    simp only [length_alternateFinsets, hXcard, hYcard] at hle
    omega
  · rcases hodd with ⟨t, ht⟩
    have hYle : t + 1 ≤ O.card := by omega
    have hXle : t + 1 ≤ p.toFinset.card := by
      rw [List.toFinset_card_of_nodup hp.2.1]
      omega
    obtain ⟨Y, hYO, hYcard⟩ := Finset.exists_subset_card_eq hYle
    obtain ⟨X, hXp, hXcard⟩ := Finset.exists_subset_card_eq hXle
    have hdisj : Disjoint X Y := Finset.disjoint_left.mpr fun z hzX hzY ↦ by
      have hzp : z ∈ p.toFinset := hXp hzX
      have hzO : z ∈ O := hYO hzY
      exact (Finset.mem_sdiff.mp hzO).2 hzp
    have hadj : ∀ x ∈ X, ∀ y ∈ Y, Hᶜ.Adj x y := by
      intro x hxX y hyY
      apply (compl_cross_of_closed_longest hp hmax hclosed ?_ ?_).symm
      · exact fun hyp ↦ (Finset.mem_sdiff.mp (hYO hyY)).2 (List.mem_toFinset.mpr hyp)
      · exact List.mem_toFinset.mp (hXp hxX)
    have hcard : X.card = Y.card := by omega
    have hX0 : X.Nonempty := Finset.card_pos.mp (by omega)
    have hq : IsPath Hᶜ (alternateFinsets X Y) :=
      isPath_alternateFinsets_of_card_eq hcard hX0 hdisj hadj
    have hle := hmax.2 (alternateFinsets X Y) (Or.inr hq)
    simp only [length_alternateFinsets, hXcard, hYcard] at hle
    omega

private lemma outside_add_inter_le_path_length [Fintype V] [DecidableEq V]
    {p q : List V} (hq : q.Nodup) {B : Finset V}
    (hBout : B ⊆ Finset.univ \ p.toFinset)
    (hBq : ∀ y ∈ B, y ∈ q) :
    B.card + (q.toFinset ∩ p.toFinset).card ≤ q.length := by
  have hdisj : Disjoint B (q.toFinset ∩ p.toFinset) := Finset.disjoint_left.mpr fun z hzB hz ↦
    (Finset.mem_sdiff.mp (hBout hzB)).2 (Finset.mem_inter.mp hz).2
  have hsub : B ∪ (q.toFinset ∩ p.toFinset) ⊆ q.toFinset := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzB | hzI
    · exact List.mem_toFinset.mpr (hBq z hzB)
    · exact (Finset.mem_inter.mp hzI).1
  calc
    B.card + (q.toFinset ∩ p.toFinset).card =
        (B ∪ (q.toFinset ∩ p.toFinset)).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ q.toFinset.card := Finset.card_le_card hsub
    _ = q.length := List.toFinset_card_of_nodup hq

private lemma two_le_length_of_globally_longest [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {p : List V} (hmax : IsGloballyLongestMonoPath H p)
    (hcard : 2 ≤ Fintype.card V) : 2 ≤ p.length := by
  obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
  have hmono : IsMonochromaticPath H [x, y] := by
    by_cases hadj : H.Adj x y
    · exact Or.inl ⟨by simp, by simpa using hxy, by simpa using hadj⟩
    · have hcompl : Hᶜ.Adj x y := by
        rw [SimpleGraph.compl_adj]
        exact ⟨hxy, hadj⟩
      exact Or.inr ⟨by simp, by simpa using hxy, by simpa using hcompl⟩
  have := hmax.2 [x, y] hmono
  simpa using this

private lemma globally_longest_two_thirds_of_rotations [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {p : List V} (hp : IsPath H p)
    (hmax : IsGloballyLongestMonoPath H p) (_hp2 : 2 ≤ p.length)
    (hstrict : ∀ B : Finset V,
      B ⊆ Finset.univ \ p.toFinset → B.card < (p.length + 1) / 2 →
      ∃ q : List V, IsPath Hᶜ q ∧ (∀ y ∈ B, y ∈ q) ∧
        B.card + 2 ≤ (q.toFinset ∩ p.toFinset).card)
    (heven : Even p.length → ∀ B : Finset V,
      B ⊆ Finset.univ \ p.toFinset → B.card = p.length / 2 →
      ∃ q : List V, IsPath Hᶜ q ∧ (∀ y ∈ B, y ∈ q) ∧
        B.card + 1 ≤ (q.toFinset ∩ p.toFinset).card) :
    Fintype.card V * 2 / 3 + 1 ≤ p.length := by
  by_contra hbound
  have hshort : p.length < Fintype.card V * 2 / 3 + 1 := Nat.lt_of_not_ge hbound
  have hplen : p.length ≤ Fintype.card V := hp.2.1.length_le_card
  let O : Finset V := Finset.univ \ p.toFinset
  have hOcard : O.card = Fintype.card V - p.length := by
    simpa [O] using card_compl_pathVertices hp.2.1
  have hOlarge : p.length / 2 ≤ O.card := by
    rw [hOcard]
    omega
  rcases Nat.even_or_odd p.length with hev | hodd
  · rcases hev with ⟨t, ht⟩
    have htO : t ≤ O.card := by omega
    obtain ⟨B, hBO, hBcard⟩ := Finset.exists_subset_card_eq htO
    have hBhalf : B.card = p.length / 2 := by omega
    obtain ⟨q, hq, hBq, hinter⟩ := heven ⟨t, ht⟩ B (by simpa [O] using hBO) hBhalf
    have hsum := outside_add_inter_le_path_length hq.2.1
      (by simpa [O] using hBO) hBq
    have hle := hmax.2 q (Or.inr hq)
    omega
  · rcases hodd with ⟨t, ht⟩
    have htO : t ≤ O.card := by omega
    obtain ⟨B, hBO, hBcard⟩ := Finset.exists_subset_card_eq htO
    have hBstrict : B.card < (p.length + 1) / 2 := by omega
    obtain ⟨q, hq, hBq, hinter⟩ := hstrict B (by simpa [O] using hBO) hBstrict
    have hsum := outside_add_inter_le_path_length hq.2.1
      (by simpa [O] using hBO) hBq
    have hle := hmax.2 q (Or.inr hq)
    omega

private lemma globally_longest_two_thirds_of_not_cut [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {p : List V} (hp : IsPath H p)
    (hmax : IsGloballyLongestMonoPath H p) (hncut : ¬ IsCutColoring H) :
    Fintype.card V * 2 / 3 + 1 ≤ p.length := by
  by_cases hcard : 2 ≤ Fintype.card V
  · have hp2 : 2 ≤ p.length := two_le_length_of_globally_longest hmax hcard
    apply globally_longest_two_thirds_of_rotations hp hmax hp2
    · intro B hBout hBsmall
      have hdis : Disjoint B p.toFinset := by
        rw [Finset.disjoint_left]
        intro x hxB hxP
        exact (Finset.mem_sdiff.mp (hBout hxB)).2 hxP
      exact rotation_strict hp hmax hncut hp2 B hdis hBsmall
    · intro heven B hBout hBcard
      have hdis : Disjoint B p.toFinset := by
        rw [Finset.disjoint_left]
        intro x hxB hxP
        exact (Finset.mem_sdiff.mp (hBout hxB)).2 hxP
      exact rotation_even hp hmax hncut hp2 B hdis heven hBcard
  · have hcard' : Fintype.card V ≤ 1 := by omega
    have hp1 : 1 ≤ p.length := List.length_pos_of_ne_nil hp.1
    omega

private lemma globally_longest_two_thirds_of_cut [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {p : List V} (hpmax : IsGloballyLongestMonoPath H p)
    (hcut : IsCutColoring H) : Fintype.card V * 2 / 3 + 1 ≤ p.length := by
  obtain ⟨q, hqmax, hqclosed⟩ := hcut
  have hqp : q.length ≤ p.length := hpmax.2 q hqmax.1
  rcases hqclosed with hqclosed | hqclosed
  · obtain ⟨hq, hclosed⟩ := hqclosed
    exact (closed_longest_two_thirds hq hqmax hclosed).trans hqp
  · obtain ⟨hq, hclosed⟩ := hqclosed
    have hqmax' : IsGloballyLongestMonoPath Hᶜ q :=
      (isGloballyLongestMonoPath_compl_iff H q).2 hqmax
    exact (closed_longest_two_thirds hq hqmax' hclosed).trans hqp

/-- In every two-colouring of the complete graph on a nonempty finite vertex type,
one colour contains a path on at least `⌊2 |V| / 3⌋ + 1` vertices. -/
theorem exists_long_monochromatic_path [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) :
    ∃ p : List V, (IsPath G p ∨ IsPath Gᶜ p) ∧
      Fintype.card V * 2 / 3 + 1 ≤ p.length := by
  obtain ⟨p, hpmax⟩ := exists_globally_longest_mono_path G
  refine ⟨p, hpmax.1, ?_⟩
  by_cases hcut : IsCutColoring G
  · exact globally_longest_two_thirds_of_cut hpmax hcut
  · rcases hpmax.1 with hp | hp
    · exact globally_longest_two_thirds_of_not_cut hp hpmax hcut
    · have hpmax' : IsGloballyLongestMonoPath Gᶜ p :=
        (isGloballyLongestMonoPath_compl_iff G p).2 hpmax
      have hncut' : ¬ IsCutColoring Gᶜ := by simpa using hcut
      exact globally_longest_two_thirds_of_not_cut hp hpmax' hncut'

end Erdos518
