/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Setup
import ErdosProblems.Erdos518.RotationGap
import ErdosProblems.Erdos518.Alternating

/-!
# The Erdős--Gyárfás rotation lemma

This file proves the finite rotation lemma from Erdős--Gyárfás (1995).  The
chosen path is longest among *both* colours.  In a non-cut colouring, a
small set outside it can be absorbed by a path of the other colour.  We use
list paths throughout, as in `Erdos518.Defs`.
-/

open scoped SimpleGraph List

namespace Erdos518

universe u

variable {V : Type u}

/-- The finite support of a list path. -/
abbrev pathVertices [DecidableEq V] (p : List V) : Finset V := p.toFinset

/-- The conclusion of the strict rotation lemma, strengthened by remembering
the consecutive copy of the endpoint edge.  This extra information is what
turns the strict statement into the even equality statement. -/
def IsStrictRotation [DecidableEq V]
    (G : SimpleGraph V) (p q : List V) (B : Finset V) : Prop :=
  IsPath Gᶜ q ∧
    (∀ y ∈ B, y ∈ q) ∧
    (∀ y ∈ q, y ∈ p ∨ y ∈ B) ∧
    B.card + 2 ≤ (q.toFinset ∩ p.toFinset).card ∧
    ∃ hp : IsPath G p,
      ∃ l r : List V,
        q = l ++ p.head hp.1 :: p.getLast hp.1 :: r ∨
          q = l ++ p.getLast hp.1 :: p.head hp.1 :: r

private lemma isPath_insert_between {G : SimpleGraph V} {l r : List V} {x y z : V}
    (hp : IsPath G (l ++ x :: z :: r)) (hy : y ∉ l ++ x :: z :: r)
    (hxy : G.Adj x y) (hyz : G.Adj y z) :
    IsPath G (l ++ x :: y :: z :: r) := by
  rcases hp with ⟨hne, hnodup, hchain⟩
  constructor
  · simp
  constructor
  · have hold := List.nodup_append'.mp hnodup
    refine List.nodup_append'.mpr ⟨hold.1, ?_, ?_⟩
    · simp only [List.nodup_cons] at hold ⊢
      simp only [List.mem_append, List.mem_cons, not_or] at hy
      aesop
    · simp only [List.disjoint_cons_right] at hold ⊢
      simp only [List.mem_append, List.mem_cons, not_or] at hy
      aesop
  · rw [List.isChain_append_cons_cons] at hchain ⊢
    exact ⟨hchain.1, hxy, List.isChain_cons_cons.mpr ⟨hyz, hchain.2.2⟩⟩

private lemma path_length_insert_between {l r : List V} {x y z : V} :
    (l ++ x :: y :: z :: r).length = (l ++ x :: z :: r).length + 1 := by
  simp only [List.length_append, List.length_cons]
  omega

private lemma isPath_cons_of_adj {G : SimpleGraph V} {p : List V} {x y : V}
    (hp : IsPath G (y :: p)) (hx : x ∉ y :: p) (h : G.Adj x y) :
    IsPath G (x :: y :: p) := by
  refine ⟨by simp, hp.2.1.cons hx, ?_⟩
  exact List.IsChain.cons_cons h hp.2.2

/-- An outside vertex is joined in the opposite colour to both endpoints of
a globally longest path. -/
lemma compl_adj_endpoints_of_longest {G : SimpleGraph V} {p : List V}
    (hp : IsPath G p) (hmax : IsGloballyLongestMonoPath G p)
    {y : V} (hy : y ∉ p) :
    Gᶜ.Adj (p.head hp.1) y ∧ Gᶜ.Adj y (p.getLast hp.1) := by
  have hfirst : ¬G.Adj (p.head hp.1) y := by
    intro h
    obtain ⟨x, p', hpEq⟩ := List.exists_cons_of_ne_nil hp.1
    have hp' : IsPath G (x :: p') := by simpa [hpEq] using hp
    have hy' : y ∉ x :: p' := by simpa [hpEq] using hy
    have h' : G.Adj y x := by simpa [hpEq] using h.symm
    have hpath : IsPath G (y :: x :: p') := isPath_cons_of_adj hp' hy' h'
    have hle := hmax.2 (y :: x :: p') (Or.inl hpath)
    simp [hpEq] at hle
  have hlast : ¬G.Adj y (p.getLast hp.1) := by
    intro h
    have hnotrev : y ∉ p.reverse := by simpa using hy
    have hpRev : IsPath G p.reverse := isPath_reverse hp
    obtain ⟨x, q, hrevEq⟩ := List.exists_cons_of_ne_nil hpRev.1
    have hpRev' : IsPath G (x :: q) := by simpa [hrevEq] using hpRev
    have hnotrev' : y ∉ x :: q := by simpa [hrevEq] using hnotrev
    have hxlast : x = p.getLast hp.1 := by
      have := congrArg (fun l : List V ↦ l.head? ) hrevEq
      have hsome : p.getLast? = some x := by simpa using this
      rw [List.getLast?_eq_some_getLast hp.1] at hsome
      exact (Option.some.inj hsome).symm
    have hrev : IsPath G (y :: p.reverse) := by
      rw [hrevEq]
      apply isPath_cons_of_adj hpRev' hnotrev'
      simpa [hxlast] using h
    have hpath : IsPath G (p ++ [y]) := by simpa using isPath_reverse hrev
    have hle := hmax.2 (p ++ [y]) (Or.inl hpath)
    simp at hle
  have hheadmem : p.head hp.1 ∈ p := List.head_mem hp.1
  have hlastmem : p.getLast hp.1 ∈ p := List.getLast_mem hp.1
  constructor
  · rw [SimpleGraph.compl_adj]
    exact ⟨fun h ↦ hy (h ▸ hheadmem), hfirst⟩
  · rw [SimpleGraph.compl_adj]
    exact ⟨fun h ↦ hy (h ▸ hlastmem), hlast⟩

/-- In a non-cut colouring the two endpoints of every globally longest path
are adjacent in the other colour. -/
lemma compl_adj_endpoints_of_not_cut {G : SimpleGraph V} {p : List V}
    (hp : IsPath G p) (hmax : IsGloballyLongestMonoPath G p)
    (hncut : ¬ IsCutColoring G) (hlen : 2 ≤ p.length) :
    Gᶜ.Adj (p.head hp.1) (p.getLast hp.1) := by
  have hnot : ¬G.Adj (p.head hp.1) (p.getLast hp.1) := by
    intro h
    apply hncut
    exact ⟨p, hmax, Or.inl ⟨hp, h⟩⟩
  have hne : p.head hp.1 ≠ p.getLast hp.1 := by
    intro h
    obtain ⟨x, hx⟩ := (hp.2.1.head_eq_getLast_iff hp.1).mp h
    subst p
    simp at hlen
  rw [SimpleGraph.compl_adj]
  exact ⟨hne, hnot⟩

/-- A path with at least two vertices has an endpoint--interior--endpoint
decomposition. -/
lemma exists_endpoint_decomposition {G : SimpleGraph V} {p : List V}
    (hp : IsPath G p) (hlen : 2 ≤ p.length) :
    ∃ x z : V, ∃ C : List V,
      p = x :: C ++ [z] ∧ x = p.head hp.1 ∧ z = p.getLast hp.1 := by
  obtain ⟨x, r, hpEq⟩ := List.exists_cons_of_ne_nil hp.1
  have hr : r ≠ [] := by
    intro hr
    subst r
    simp [hpEq] at hlen
  let C := r.dropLast
  let z := r.getLast hr
  have hrEq : r = C ++ [z] := (List.dropLast_append_getLast hr).symm
  refine ⟨x, z, C, by simpa [hrEq] using hpEq, ?_, ?_⟩
  · simp [hpEq]
  · have hlast : p.getLast? = some z := by
      rw [hpEq, hrEq, List.getLast?_cons_of_ne_nil (by simp : C ++ [z] ≠ [])]
      simp
    rw [List.getLast?_eq_some_getLast hp.1] at hlast
    exact (Option.some.inj hlast).symm

/-- A consecutive pair of the longest path cannot have a common neighbour
outside the path in the path's own colour. -/
lemma no_common_adj_consecutive_of_longest {G : SimpleGraph V} {p : List V}
    (hp : IsPath G p) (hmax : IsGloballyLongestMonoPath G p)
    {l r : List V} {x z y : V} (hsplit : p = l ++ x :: z :: r)
    (hy : y ∉ p) : ¬(G.Adj x y ∧ G.Adj y z) := by
  rintro ⟨hxy, hyz⟩
  have hpath : IsPath G (l ++ x :: y :: z :: r) :=
    isPath_insert_between (hsplit ▸ hp) (hsplit ▸ hy) hxy hyz
  have hle := hmax.2 _ (Or.inl hpath)
  rw [hsplit] at hle
  simpa [path_length_insert_between] using hle

/-- The local three-vertex observation used in the two-maximal-path proof:
one member of every consecutive pair sends opposite-colour edges to at least
two of any three outside vertices. -/
lemma rotation_triple_observation {G : SimpleGraph V} {p : List V}
    (hp : IsPath G p) (hmax : IsGloballyLongestMonoPath G p)
    {l r : List V} {x z a b c : V} (hsplit : p = l ++ x :: z :: r)
    (ha : a ∉ p) (hb : b ∉ p) (hc : c ∉ p)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ((Gᶜ.Adj x a ∧ Gᶜ.Adj x b) ∨
      (Gᶜ.Adj x a ∧ Gᶜ.Adj x c) ∨
      (Gᶜ.Adj x b ∧ Gᶜ.Adj x c)) ∨
    ((Gᶜ.Adj z a ∧ Gᶜ.Adj z b) ∨
      (Gᶜ.Adj z a ∧ Gᶜ.Adj z c) ∨
      (Gᶜ.Adj z b ∧ Gᶜ.Adj z c)) := by
  have hxa : x ≠ a := fun h ↦ ha (hsplit ▸ by simp [h])
  have hxb : x ≠ b := fun h ↦ hb (hsplit ▸ by simp [h])
  have hxc : x ≠ c := fun h ↦ hc (hsplit ▸ by simp [h])
  have hza : z ≠ a := fun h ↦ ha (hsplit ▸ by simp [h])
  have hzb : z ≠ b := fun h ↦ hb (hsplit ▸ by simp [h])
  have hzc : z ≠ c := fun h ↦ hc (hsplit ▸ by simp [h])
  have hnoa := no_common_adj_consecutive_of_longest hp hmax hsplit ha
  have hnob := no_common_adj_consecutive_of_longest hp hmax hsplit hb
  have hnoc := no_common_adj_consecutive_of_longest hp hmax hsplit hc
  have hnoa' : ¬(G.Adj x a ∧ G.Adj z a) := by
    simpa only [SimpleGraph.adj_comm] using hnoa
  have hnob' : ¬(G.Adj x b ∧ G.Adj z b) := by
    simpa only [SimpleGraph.adj_comm] using hnob
  have hnoc' : ¬(G.Adj x c ∧ G.Adj z c) := by
    simpa only [SimpleGraph.adj_comm] using hnoc
  have cx_a (h : ¬G.Adj x a) : Gᶜ.Adj x a := by
    rw [SimpleGraph.compl_adj]
    exact ⟨hxa, h⟩
  have cx_b (h : ¬G.Adj x b) : Gᶜ.Adj x b := by
    rw [SimpleGraph.compl_adj]
    exact ⟨hxb, h⟩
  have cx_c (h : ¬G.Adj x c) : Gᶜ.Adj x c := by
    rw [SimpleGraph.compl_adj]
    exact ⟨hxc, h⟩
  have cz_a (h : ¬G.Adj z a) : Gᶜ.Adj z a := by
    rw [SimpleGraph.compl_adj]
    exact ⟨hza, h⟩
  have cz_b (h : ¬G.Adj z b) : Gᶜ.Adj z b := by
    rw [SimpleGraph.compl_adj]
    exact ⟨hzb, h⟩
  have cz_c (h : ¬G.Adj z c) : Gᶜ.Adj z c := by
    rw [SimpleGraph.compl_adj]
    exact ⟨hzc, h⟩
  by_cases hxaG : G.Adj x a
  · have hzaC : Gᶜ.Adj z a := cz_a (fun hzaG ↦ hnoa' ⟨hxaG, hzaG⟩)
    by_cases hxbG : G.Adj x b
    · have hzbC : Gᶜ.Adj z b := cz_b (fun hzbG ↦ hnob' ⟨hxbG, hzbG⟩)
      exact Or.inr (Or.inl ⟨hzaC, hzbC⟩)
    · by_cases hxcG : G.Adj x c
      · have hzcC : Gᶜ.Adj z c := cz_c (fun hzcG ↦ hnoc' ⟨hxcG, hzcG⟩)
        exact Or.inr (Or.inr (Or.inl ⟨hzaC, hzcC⟩))
      · exact Or.inl (Or.inr (Or.inr ⟨cx_b hxbG, cx_c hxcG⟩))
  · have hxaC := cx_a hxaG
    by_cases hxbG : G.Adj x b
    · by_cases hxcG : G.Adj x c
      · have hzbC : Gᶜ.Adj z b := cz_b (fun hzbG ↦ hnob' ⟨hxbG, hzbG⟩)
        have hzcC : Gᶜ.Adj z c := cz_c (fun hzcG ↦ hnoc' ⟨hxcG, hzcG⟩)
        exact Or.inr (Or.inr (Or.inr ⟨hzbC, hzcC⟩))
      · exact Or.inl (Or.inr (Or.inl ⟨hxaC, cx_c hxcG⟩))
    · exact Or.inl (Or.inl ⟨hxaC, cx_b hxbG⟩)

/-- If a set meets every consecutive pair in a duplicate-free ordered list,
then it contains at least half of the list.  This is the counting step in
the maximal-two-path argument. -/
lemma half_length_le_card_inter_of_pair_cover [DecidableEq V]
    (s : Finset V) (p : List V) (hp : p.Nodup)
    (hpair : ∀ (l r : List V) (x y : V),
      p = l ++ x :: y :: r → x ∈ s ∨ y ∈ s) :
    p.length / 2 ≤ (s ∩ p.toFinset).card := by
  induction p using List.twoStepInduction with
  | nil => simp
  | singleton x => simp
  | cons_cons x y r ih =>
      have hp' := List.nodup_cons.mp hp
      have hptail : (y :: r).Nodup := hp'.2
      have hptail' := List.nodup_cons.mp hptail
      have hr : r.Nodup := hptail'.2
      have hpairR : ∀ (l r' : List V) (a b : V),
          r = l ++ a :: b :: r' → a ∈ s ∨ b ∈ s := by
        intro l r' a b h
        apply hpair (x :: y :: l) r' a b
        simp [h]
      have hih := ih hr hpairR
      have hxy : x ∈ s ∨ y ∈ s := hpair [] r x y (by simp)
      have hxr : x ∉ r := by
        intro h
        exact hp'.1 (by simp [h])
      have hyr : y ∉ r := hptail'.1
      let T := s ∩ r.toFinset
      have hTsub : T ⊆ s ∩ (x :: y :: r).toFinset := by
        intro z hz
        simp only [T, Finset.mem_inter, List.mem_toFinset] at hz ⊢
        exact ⟨hz.1, by simp [hz.2]⟩
      have hcard : T.card + 1 ≤ (s ∩ (x :: y :: r).toFinset).card := by
        rcases hxy with hx | hy
        · have hxT : x ∉ T := by simp [T, hxr]
          have hins : insert x T ⊆ s ∩ (x :: y :: r).toFinset := by
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz
            · simp [hx]
            · exact hTsub hz
          simpa [Finset.card_insert_of_notMem hxT] using Finset.card_le_card hins
        · have hyT : y ∉ T := by simp [T, hyr]
          have hins : insert y T ⊆ s ∩ (x :: y :: r).toFinset := by
            intro z hz
            rcases Finset.mem_insert.mp hz with rfl | hz
            · simp [hy]
            · exact hTsub hz
          simpa [Finset.card_insert_of_notMem hyT] using Finset.card_le_card hins
      change (r.length + 2) / 2 ≤ _
      rw [Nat.add_div_right]
      · exact (Nat.add_le_add_right hih 1).trans hcard
      · omega

/-! ## Even and odd positions in the internal path -/

/-- Vertices in zero-based even positions of a list. -/
def evenIndexedVertices [DecidableEq V] : List V → Finset V
  | [] => ∅
  | [a] => {a}
  | a :: _ :: r => insert a (evenIndexedVertices r)

lemma evenIndexedVertices_subset_toFinset [DecidableEq V] (C : List V) :
    evenIndexedVertices C ⊆ C.toFinset := by
  induction C using List.twoStepInduction with
  | nil => simp [evenIndexedVertices]
  | singleton a => simp [evenIndexedVertices]
  | cons_cons a b r ih _ =>
      intro x hx
      simp only [evenIndexedVertices, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · simp
      · have := ih hx
        simp only [List.mem_toFinset] at this ⊢
        simp [this]

lemma card_oddIndexedVertices [DecidableEq V] (C : List V) (hC : C.Nodup) :
    (oddIndexedVertices C).card = C.length / 2 := by
  induction C using List.twoStepInduction with
  | nil => simp [oddIndexedVertices]
  | singleton a => simp [oddIndexedVertices]
  | cons_cons a b r ih _ =>
      have ht := List.nodup_cons.mp hC
      have hb := List.nodup_cons.mp ht.2
      have hbr : b ∉ oddIndexedVertices r := by
        intro h
        have : b ∈ r.toFinset := oddIndexedVertices_subset_toFinset r h
        exact hb.1 (List.mem_toFinset.mp this)
      rw [show oddIndexedVertices (a :: b :: r) =
        insert b (oddIndexedVertices r) from rfl,
        Finset.card_insert_of_notMem hbr, ih hb.2]
      simp only [List.length_cons]
      omega

lemma evenIndexedVertices_disjoint_oddIndexedVertices [DecidableEq V]
    (C : List V) (hC : C.Nodup) :
    Disjoint (evenIndexedVertices C) (oddIndexedVertices C) := by
  induction C using List.twoStepInduction with
  | nil => simp [evenIndexedVertices, oddIndexedVertices]
  | singleton a => simp [evenIndexedVertices, oddIndexedVertices]
  | cons_cons a b r ih _ =>
      have ht := List.nodup_cons.mp hC
      have hb := List.nodup_cons.mp ht.2
      rw [Finset.disjoint_left]
      intro x hxE hxO
      simp only [evenIndexedVertices, oddIndexedVertices, Finset.mem_insert] at hxE hxO
      rcases hxE with rfl | hxE
      · rcases hxO with h | hxO
        · exact ht.1 (by simp [h])
        · exact ht.1 (by
            right
            exact List.mem_toFinset.mp (oddIndexedVertices_subset_toFinset r hxO))
      · rcases hxO with rfl | hxO
        · exact hb.1 (List.mem_toFinset.mp (evenIndexedVertices_subset_toFinset r hxE))
        · exact Finset.disjoint_left.mp (ih hb.2) hxE hxO

/-- Every odd-positioned vertex is immediately preceded, within the list,
by an even-positioned vertex. -/
lemma oddIndexedVertices_has_even_predecessor [DecidableEq V]
    {C : List V} {z : V} (hz : z ∈ oddIndexedVertices C) :
    ∃ l r : List V, ∃ x : V,
      C = l ++ x :: z :: r ∧ x ∈ evenIndexedVertices C := by
  induction C using List.twoStepInduction with
  | nil => simp [oddIndexedVertices] at hz
  | singleton a => simp [oddIndexedVertices] at hz
  | cons_cons a b r ih _ =>
      simp only [oddIndexedVertices, Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact ⟨[], r, a, by simp, by simp [evenIndexedVertices]⟩
      · obtain ⟨l, s, x, hrs, hx⟩ := ih hz
        refine ⟨a :: b :: l, s, x, ?_, ?_⟩
        · simp [hrs]
        · simp [evenIndexedVertices, hx]

private lemma compl_adj_oddIndexed_of_no_even_edge [DecidableEq V]
    {G : SimpleGraph V} {p C : List V} {a d y z : V}
    (hp : IsPath G p) (hmax : IsGloballyLongestMonoPath G p)
    (hpEq : p = a :: C ++ [d]) (hy : y ∉ p)
    (hno : ∀ x ∈ evenIndexedVertices C, ¬ Gᶜ.Adj x y)
    (hz : z ∈ oddIndexedVertices C) : Gᶜ.Adj z y := by
  obtain ⟨l, r, x, hCsplit, hxE⟩ := oddIndexedVertices_has_even_predecessor hz
  have hsplit : p = (a :: l) ++ x :: z :: (r ++ [d]) := by
    simp [hpEq, hCsplit]
  have hxmem : x ∈ p := by simp [hsplit]
  have hzmem : z ∈ p := by simp [hsplit]
  have hxyne : x ≠ y := fun h ↦ hy (h ▸ hxmem)
  have hzyne : z ≠ y := fun h ↦ hy (h ▸ hzmem)
  have hxyG : G.Adj x y := by
    have hn := hno x hxE
    rw [SimpleGraph.compl_adj] at hn
    tauto
  have hnotzy : ¬ G.Adj z y := by
    intro hzy
    exact no_common_adj_consecutive_of_longest hp hmax hsplit hy
      ⟨hxyG, hzy.symm⟩
  rw [SimpleGraph.compl_adj]
  exact ⟨hzyne, hnotzy⟩

/-- In the unique odd borderline case, some outside vertex has an
opposite-colour edge to an even-positioned internal vertex.  Otherwise the
odd positions together with the two endpoints alternate with all of `B` to
form a closed globally-longest opposite-colour path. -/
lemma exists_compl_even_edge_of_odd_borderline
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} {p C : List V}
    {a d : V} (hp : IsPath G p) (hmax : IsGloballyLongestMonoPath G p)
    (hncut : ¬ IsCutColoring G) (hpEq : p = a :: C ++ [d])
    (B : Finset V) (hB : Disjoint B p.toFinset)
    (hodd : Odd p.length) (hcard : B.card + 1 = (p.length + 1) / 2) :
    ∃ x ∈ evenIndexedVertices C, ∃ y ∈ B, Gᶜ.Adj x y := by
  classical
  by_contra hex
  push_neg at hex
  have hpN : (a :: C ++ [d]).Nodup := hpEq ▸ hp.2.1
  have htailN := List.nodup_cons.mp hpN
  have hCN : C.Nodup := (List.nodup_append.mp htailN.2).1
  have haC : a ∉ C := fun h ↦ htailN.1 (by simp [h])
  have hdC : d ∉ C := by
    have := (List.nodup_append.mp htailN.2).2.2
    intro h
    exact this d h d (by simp) rfl
  have had : a ≠ d := fun h ↦ htailN.1 (by simp [h])
  let O := oddIndexedVertices C
  let xs : List V := a :: O.toList ++ [d]
  let ys : List V := B.toList
  have hClen : C.length + 2 = p.length := by simp [hpEq]
  have hOcard : O.card = C.length / 2 := card_oddIndexedVertices C hCN
  rcases hodd with ⟨k, hk⟩
  have hkpos : 1 ≤ k := by omega
  have hOeq : O.card = k - 1 := by rw [hOcard]; omega
  have hBeq : B.card = k := by omega
  have hlen : xs.length = ys.length + 1 := by
    simp [xs, ys, hOeq, hBeq, Nat.sub_add_cancel hkpos]
  have hxsN : xs.Nodup := by
    have haO : a ∉ O := by
      intro h
      exact haC (List.mem_toFinset.mp (oddIndexedVertices_subset_toFinset C h))
    have hdO : d ∉ O := by
      intro h
      exact hdC (List.mem_toFinset.mp (oddIndexedVertices_subset_toFinset C h))
    apply List.Nodup.cons
    · simp [haO, had]
    · simpa using (Finset.nodup_toList O).concat (by simpa using hdO)
  have hysN : ys.Nodup := by exact Finset.nodup_toList B
  have hdisj : xs.Disjoint ys := by
    rw [List.disjoint_iff_ne]
    intro x hx y hy
    have hxP : x ∈ p := by
      have hx' : x = a ∨ x ∈ O.toList ∨ x = d := by simpa [xs] using hx
      rcases hx' with rfl | (hx | rfl)
      · simp [hpEq]
      · have hxC : x ∈ C := List.mem_toFinset.mp
          (oddIndexedVertices_subset_toFinset C (by simpa [O] using hx))
        simp [hpEq, hxC]
      · simp [hpEq]
    have hyB : y ∈ B := by simpa [ys] using hy
    intro hxy
    subst y
    exact Finset.disjoint_left.mp hB hyB (List.mem_toFinset.mpr hxP)
  have hcross : CrossAdjacent Gᶜ xs ys := by
    intro x hx y hy
    have hyB : y ∈ B := by simpa [ys] using hy
    have hyP : y ∉ p := by
      intro hyp
      exact Finset.disjoint_left.mp hB hyB (List.mem_toFinset.mpr hyp)
    have hx' : x = a ∨ x ∈ O.toList ∨ x = d := by simpa [xs] using hx
    rcases hx' with rfl | (hx | rfl)
    · simpa [hpEq] using
        (compl_adj_endpoints_of_longest hp hmax (y := y) hyP).1
    · apply compl_adj_oddIndexed_of_no_even_edge hp hmax hpEq hyP
        (fun e he ↦ hex e he y hyB)
      simpa [O] using hx
    · simpa [hpEq] using
        (compl_adj_endpoints_of_longest hp hmax (y := y) hyP).2.symm
  let q := alternate xs ys
  have hq : IsPath Gᶜ q := by
    dsimp [q]
    exact isPath_alternate_of_length_eq_add_one hlen hxsN hysN hdisj hcross
  have he := endpoints_alternate_of_length_eq_add_one hlen
  have hheadOpt : q.head? = some a := by
    dsimp [q]
    rw [he.1]
    simp [xs]
  have hlastOpt : q.getLast? = some d := by
    dsimp [q]
    rw [he.2]
    simp only [xs, List.getLast?_cons, List.getLast?_append]
    simp
  rw [List.head?_eq_some_head hq.1] at hheadOpt
  rw [List.getLast?_eq_some_getLast hq.1] at hlastOpt
  have hhead : q.head hq.1 = a := Option.some.inj hheadOpt
  have hlast : q.getLast hq.1 = d := Option.some.inj hlastOpt
  have hysLen : ys.length = k := by
    simpa only [ys, Finset.length_toList] using hBeq
  have hxsLen : xs.length = k + 1 := by omega
  have hlenq : q.length = p.length := by
    rw [show q.length = xs.length + ys.length by simp [q], hxsLen, hysLen, hk]
    omega
  have hqmax : IsGloballyLongestMonoPath G q := by
    refine ⟨Or.inr hq, ?_⟩
    intro r hr
    rw [hlenq]
    exact hmax.2 r hr
  apply hncut
  refine ⟨q, hqmax, Or.inr ⟨hq, ?_⟩⟩
  simpa [hhead, hlast, hpEq] using
    compl_adj_endpoints_of_not_cut hp hmax hncut (by
      simp [hpEq])


/-! ## The two maximal alternating paths -/

variable {V : Type u}

/-- A list in blocks `B,C,B,C,...`; in particular its two sides have equal
cardinality and its endpoints lie in different parts. -/
inductive AlternatesBC [DecidableEq V] (C B : Finset V) : List V → Prop
  | one (b c : V) (hb : b ∈ B) (hc : c ∈ C) : AlternatesBC C B [b, c]
  | more (b c : V) {p : List V} (hb : b ∈ B) (hc : c ∈ C)
      (hp : AlternatesBC C B p) : AlternatesBC C B (b :: c :: p)

namespace AlternatesBC

variable [DecidableEq V] {C B : Finset V} {p q : List V}

lemma ne_nil (hp : AlternatesBC C B p) : p ≠ [] := by
  cases hp <;> simp

lemma length_two_le (hp : AlternatesBC C B p) : 2 ≤ p.length := by
  cases hp <;> simp

lemma head_mem_B (hp : AlternatesBC C B p) : p.head hp.ne_nil ∈ B := by
  cases hp <;> simp_all

lemma getLast_mem_C (hp : AlternatesBC C B p) : p.getLast hp.ne_nil ∈ C := by
  induction hp with
  | one b c hb hc => simpa using hc
  | more b c hb hc hp ih =>
      rw [List.getLast_cons_cons, List.getLast_cons hp.ne_nil]
      exact ih

lemma mem_union (hp : AlternatesBC C B p) {x : V} (hx : x ∈ p) : x ∈ B ∨ x ∈ C := by
  induction hp with
  | one b c hb hc =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact Or.inl hb
      · have : x = c := by simpa using hx
        subst x
        exact Or.inr hc
  | more b c hb hc hp ih =>
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact Or.inl hb
      · exact Or.inr hc
      · exact ih hx

lemma filter_length_eq (hCB : Disjoint C B) (hp : AlternatesBC C B p) :
    (p.filter fun x ↦ decide (x ∈ C)).length =
      (p.filter fun x ↦ decide (x ∈ B)).length := by
  induction hp with
  | one b c hb hc =>
      have hbC : b ∉ C := fun h ↦ Finset.disjoint_left.mp hCB h hb
      have hcB : c ∉ B := fun h ↦ Finset.disjoint_left.mp hCB hc h
      simp [hb, hc, hbC, hcB]
  | more b c hb hc hp ih =>
      have hbC : b ∉ C := fun h ↦ Finset.disjoint_left.mp hCB h hb
      have hcB : c ∉ B := fun h ↦ Finset.disjoint_left.mp hCB hc h
      simp [hb, hc, hbC, hcB, ih]

lemma cons_pair (hp : AlternatesBC C B p) {b c : V} (hb : b ∈ B) (hc : c ∈ C) :
    AlternatesBC C B (b :: c :: p) :=
  .more b c hb hc hp

/-- Delete the final `C` vertex of `q`, reverse the remainder, add a fresh
`C` bridge, and continue with `p`.  The result again starts in `B` and ends
in `C`. -/
lemma merge (hq : AlternatesBC C B q) (hp : AlternatesBC C B p)
    {c : V} (hc : c ∈ C) :
    AlternatesBC C B (q.dropLast.reverse ++ c :: p) := by
  induction hq generalizing p c with
  | one b d hb hd =>
      simpa using hp.cons_pair hb hc
  | @more b d tail hb hd htail ih =>
      have htail0 : tail ≠ [] := htail.ne_nil
      simpa [List.dropLast_cons_of_ne_nil htail0, List.reverse_cons,
        List.append_assoc] using ih (c := d) (hp.cons_pair hb hc) hd

end AlternatesBC

def AltBCPath [DecidableEq V] (H : SimpleGraph V) (C B : Finset V) (p : List V) : Prop :=
  IsPath H p ∧ AlternatesBC C B p

private lemma card_inter_eq_filter_length [DecidableEq V]
    (S : Finset V) {l : List V} (hl : l.Nodup) :
    (l.toFinset ∩ S).card = (l.filter fun x ↦ decide (x ∈ S)).length := by
  rw [← List.toFinset_card_of_nodup (hl.filter _)]
  congr 1
  ext x
  simp [and_comm]

private lemma isPath_prepend_BC [DecidableEq V] {H : SimpleGraph V}
    {p : List V} (hp : IsPath H p) {b c : V}
    (hb : b ∉ p) (hc : c ∉ p) (hbc : H.Adj b c)
    (hcp : H.Adj c (p.head hp.1)) : IsPath H (b :: c :: p) := by
  cases p with
  | nil => exact (hp.1 rfl).elim
  | cons x p =>
    simp only [List.head_cons] at hcp
    rcases hp with ⟨_, hpN, hpC⟩
    refine ⟨by simp, ?_, .cons_cons hbc (.cons_cons hcp hpC)⟩
    simp only [List.mem_cons, not_or] at hb hc
    exact .cons (by aesop) (.cons (by aesop) hpN)

/-- The list-level join used when the bridge vertex sees both `B` endpoints.
It removes the final `C` endpoint of `q`, reverses what remains, and joins it
to `p` through `c`. -/
private lemma isPath_merge [DecidableEq V] {H : SimpleGraph V}
    {p q : List V} (hp : IsPath H p) (hq : IsPath H q)
    (hq2 : 2 ≤ q.length) {c : V} (hc : c ∉ p) (hcq : c ∉ q)
    (hpq : (p ++ q).Nodup)
    (hqc : H.Adj (q.head hq.1) c) (hcp : H.Adj c (p.head hp.1)) :
    IsPath H (q.dropLast.reverse ++ c :: p) := by
  have hqd0 : q.dropLast ≠ [] := by
    intro heq
    have hlen := congrArg List.length heq
    simp only [List.length_dropLast, List.length_nil] at hlen
    omega
  refine ⟨by simp [hp.1, hqd0], ?_, ?_⟩
  · have hsubq : ∀ x ∈ q.dropLast.reverse, x ∈ q := by
      intro x hx
      exact List.mem_of_mem_dropLast (by simpa using hx)
    have hsubp : ∀ x ∈ p, x ∈ p ++ q := fun x hx ↦ by simp [hx]
    have hsubqd : ∀ x ∈ q.dropLast.reverse, x ∈ p ++ q := by
      intro x hx
      exact by simp [hsubq x hx]
    have hqdN : q.dropLast.reverse.Nodup := by
      rw [List.nodup_reverse]
      exact (List.dropLast_sublist q).nodup hq.2.1
    have hcpN : (c :: p).Nodup := .cons hc hp.2.1
    apply List.nodup_append.mpr
    refine ⟨hqdN, hcpN, ?_⟩
    intro x hx y hy hxy
    subst y
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hyp
    · exact hcq (hsubq x hx)
    · have hdisj := List.nodup_append.mp hpq |>.2.2
      exact hdisj x hyp x (hsubq x hx) rfl
  · have hleft : q.dropLast.reverse.IsChain H.Adj := by
      rw [List.isChain_reverse]
      exact hq.2.2.dropLast.imp fun _ _ h ↦ h.symm
    have hright : (c :: p).IsChain H.Adj := by
      exact hp.2.2.cons_of_ne_nil hp.1 hcp
    apply hleft.append hright
    intro x hx y hy
    simp only [List.head?_cons, Option.mem_some_iff] at hy
    subst y
    have hxhead : x = q.head hq.1 := by
      have hx' : x ∈ q.dropLast.head? := by simpa using hx
      rw [List.head?_eq_some_head hqd0] at hx'
      simp only [Option.mem_some_iff] at hx'
      have heq : q.dropLast.head hqd0 = q.head hq.1 := by
        cases q with
        | nil => contradiction
        | cons a q =>
            simp only [List.head_cons]
            cases q with
            | nil => simp at hq2
            | cons d q => simp
      exact hx'.symm.trans heq
    simpa [hxhead] using hqc

private lemma exists_lex_maximal_pair [Fintype V]
    (P : List V → List V → Prop)
    (hP : ∃ p q, P p q)
    (hbound : ∀ p q, P p q → p.length ≤ Fintype.card V ∧ q.length ≤ Fintype.card V) :
    ∃ p q, P p q ∧
      (∀ r s, P r s → r.length ≤ p.length) ∧
      (∀ r s, P r s → r.length = p.length → s.length ≤ q.length) := by
  classical
  let Q : ℕ → Prop := fun n ↦ ∃ p q, P p q ∧ p.length = n
  obtain ⟨p₀, q₀, hpq₀⟩ := hP
  have hQ₀ : Q p₀.length := ⟨p₀, q₀, hpq₀, rfl⟩
  have hQmax : Q (Nat.findGreatest Q (Fintype.card V)) :=
    Nat.findGreatest_spec (hbound _ _ hpq₀).1 hQ₀
  obtain ⟨p₁, q₁, hpq₁, hp₁⟩ := hQmax
  let R : ℕ → Prop := fun n ↦
    ∃ p q, P p q ∧ p.length = Nat.findGreatest Q (Fintype.card V) ∧ q.length = n
  have hR₁ : R q₁.length := ⟨p₁, q₁, hpq₁, hp₁, rfl⟩
  have hRmax : R (Nat.findGreatest R (Fintype.card V)) :=
    Nat.findGreatest_spec (hbound _ _ hpq₁).2 hR₁
  obtain ⟨p, q, hpq, hpmax, hqmax⟩ := hRmax
  refine ⟨p, q, hpq, ?_, ?_⟩
  · intro r s hrs
    have hle := (hbound _ _ hrs).1
    have hQr : Q r.length := ⟨r, s, hrs, rfl⟩
    rw [hpmax]
    exact Nat.le_findGreatest hle hQr
  · intro r s hrs hre
    have hRs : R s.length := ⟨r, s, hrs, by simpa [hpmax] using hre, rfl⟩
    rw [hqmax]
    exact Nat.le_findGreatest (hbound _ _ hrs).2 hRs

/-- Generic maximal-two-path engine for the strict rotation argument.

`cpath` is the ordered internal part of the longest path, `B` is the outside
set, and `R` is an optional set of distinguished internal vertices which the
first alternating path is required to contain.  `hgap` is precisely the
ordered-list counting input: any sufficiently small used set containing `R`
misses two consecutive entries.  The two local adjacency hypotheses are the
one- and three-outside-vertex consequences of longestness.

The conclusion gives one nonempty alternating path and an optional second
one.  They are disjoint and together cover `B`. -/
theorem exists_two_altBCPath_cover
    [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (cpath : List V) (B R : Finset V)
    (hCB : Disjoint cpath.toFinset B)
    (hR : R ⊆ cpath.toFinset)
    (hseed : ∃ p, AltBCPath H cpath.toFinset B p ∧ R ⊆ p.toFinset)
    (hgap : ∀ U : Finset V, U ⊆ cpath.toFinset → R ⊆ U →
      U.card ≤ B.card - 1 →
      ∃ l r : List V, ∃ x z : V,
        cpath = l ++ x :: z :: r ∧ x ∉ U ∧ z ∉ U)
    (hone : ∀ (l r : List V) (x z y : V),
      cpath = l ++ x :: z :: r → y ∈ B → H.Adj x y ∨ H.Adj z y)
    (hthree : ∀ (l r : List V) (x z a b c : V),
      cpath = l ++ x :: z :: r → a ∈ B → b ∈ B → c ∈ B →
      a ≠ b → a ≠ c → b ≠ c →
      (((H.Adj x a ∧ H.Adj x b) ∨
          (H.Adj x a ∧ H.Adj x c) ∨
          (H.Adj x b ∧ H.Adj x c)) ∨
        ((H.Adj z a ∧ H.Adj z b) ∨
          (H.Adj z a ∧ H.Adj z c) ∨
          (H.Adj z b ∧ H.Adj z c)))) :
    ∃ p q : List V,
      AltBCPath H cpath.toFinset B p ∧
      (q = [] ∨ AltBCPath H cpath.toFinset B q) ∧
      (p ++ q).Nodup ∧
      ∀ y ∈ B, y ∈ p ∨ y ∈ q := by
  classical
  let Pair : List V → List V → Prop := fun p q ↦
    AltBCPath H cpath.toFinset B p ∧
      (q = [] ∨ AltBCPath H cpath.toFinset B q) ∧
      (p ++ q).Nodup ∧ R ⊆ p.toFinset
  have hPair : ∃ p q, Pair p q := by
    obtain ⟨p, hp, hRp⟩ := hseed
    refine ⟨p, [], hp, Or.inl rfl, ?_, hRp⟩
    simpa using hp.1.2.1
  have hbound : ∀ p q, Pair p q →
      p.length ≤ Fintype.card V ∧ q.length ≤ Fintype.card V := by
    intro p q hpq
    have hlen : p.length + q.length ≤ Fintype.card V := by
      rw [← List.length_append]
      exact hpq.2.2.1.length_le_card
    omega
  obtain ⟨p, q, hpq, hpmax, hqmax⟩ :=
    exists_lex_maximal_pair Pair hPair hbound
  refine ⟨p, q, hpq.1, hpq.2.1, hpq.2.2.1, ?_⟩
  intro y hyB
  by_contra hycover
  simp only [not_or] at hycover
  have hyp : y ∉ p := hycover.1
  have hyq : y ∉ q := hycover.2
  let U : Finset V := (p ++ q).toFinset ∩ cpath.toFinset
  have hUsub : U ⊆ cpath.toFinset := Finset.inter_subset_right
  have hRU : R ⊆ U := by
    intro x hxR
    have hxp : x ∈ p := by
      exact List.mem_toFinset.mp (hpq.2.2.2 hxR)
    exact Finset.mem_inter.mpr ⟨by simp [hxp], hR hxR⟩
  have hcount : U.card = ((p ++ q).toFinset ∩ B).card := by
    rw [card_inter_eq_filter_length cpath.toFinset hpq.2.2.1,
      card_inter_eq_filter_length B hpq.2.2.1]
    simp only [List.filter_append, List.length_append]
    have hpcount := hpq.1.2.filter_length_eq hCB
    rcases hpq.2.1 with hq0 | hqalt
    · subst q
      simpa using hpcount
    · have hqcount := hqalt.2.filter_length_eq hCB
      omega
  have hBsub : (p ++ q).toFinset ∩ B ⊆ B.erase y := by
    intro x hx
    have hxsupp : x ∈ p ++ q := List.mem_toFinset.mp (Finset.mem_inter.mp hx).1
    have hxB : x ∈ B := (Finset.mem_inter.mp hx).2
    refine Finset.mem_erase.mpr ⟨?_, hxB⟩
    intro hxy
    subst x
    rcases List.mem_append.mp hxsupp with h | h
    · exact hyp h
    · exact hyq h
  have hUcard : U.card ≤ B.card - 1 := by
    rw [hcount]
    calc
      ((p ++ q).toFinset ∩ B).card ≤ (B.erase y).card :=
        Finset.card_le_card hBsub
      _ = B.card - 1 := Finset.card_erase_of_mem hyB
  obtain ⟨l, r, x, z, hsplit, hxU, hzU⟩ := hgap U hUsub hRU hUcard
  have hxC : x ∈ cpath.toFinset := by simp [hsplit]
  have hzC : z ∈ cpath.toFinset := by simp [hsplit]
  have hxp : x ∉ p := by
    intro h
    exact hxU (Finset.mem_inter.mpr ⟨by simp [h], hxC⟩)
  have hxq : x ∉ q := by
    intro h
    exact hxU (Finset.mem_inter.mpr ⟨by simp [h], hxC⟩)
  have hzp : z ∉ p := by
    intro h
    exact hzU (Finset.mem_inter.mpr ⟨by simp [h], hzC⟩)
  have hzq : z ∉ q := by
    intro h
    exact hzU (Finset.mem_inter.mpr ⟨by simp [h], hzC⟩)
  have hy_ne_x : y ≠ x := by
    intro h
    subst x
    exact Finset.disjoint_left.mp hCB hxC hyB
  have hy_ne_z : y ≠ z := by
    intro h
    subst z
    exact Finset.disjoint_left.mp hCB hzC hyB
  rcases hpq.2.1 with hq0 | hqalt
  · subst q
    have hadj := hone l r x z y hsplit hyB
    rcases hadj with hxy | hzy
    · let q' := [y, x]
      have hq' : AltBCPath H cpath.toFinset B q' := by
        refine ⟨?_, .one y x hyB hxC⟩
        exact ⟨by simp [q'], by simp [q', hy_ne_x], by simpa [q'] using hxy.symm⟩
      have hnodup : (p ++ q').Nodup := by
        have hnew : (y :: x :: p).Nodup := by
          exact .cons (by simp [hyp, hy_ne_x]) (.cons hxp hpq.1.1.2.1)
        exact ((List.perm_middle (l₁ := p) (l₂ := [x]) (a := y)).trans
          ((List.perm_middle (l₁ := p) (l₂ := []) (a := x)).cons y)).nodup_iff.mpr
            (by simpa [q'] using hnew)
      have hPair' : Pair p q' := ⟨hpq.1, Or.inr hq', hnodup, hpq.2.2.2⟩
      have := hqmax p q' hPair' rfl
      simp [q'] at this
    · let q' := [y, z]
      have hq' : AltBCPath H cpath.toFinset B q' := by
        refine ⟨?_, .one y z hyB hzC⟩
        exact ⟨by simp [q'], by simp [q', hy_ne_z], by simpa [q'] using hzy.symm⟩
      have hnodup : (p ++ q').Nodup := by
        have hnew : (y :: z :: p).Nodup := by
          exact .cons (by simp [hyp, hy_ne_z]) (.cons hzp hpq.1.1.2.1)
        exact ((List.perm_middle (l₁ := p) (l₂ := [z]) (a := y)).trans
          ((List.perm_middle (l₁ := p) (l₂ := []) (a := z)).cons y)).nodup_iff.mpr
            (by simpa [q'] using hnew)
      have hPair' : Pair p q' := ⟨hpq.1, Or.inr hq', hnodup, hpq.2.2.2⟩
      have := hqmax p q' hPair' rfl
      simp [q'] at this
  · let y₁ := p.head hpq.1.1.1
    let y₂ := q.head hqalt.1.1
    have hy₁B : y₁ ∈ B := hpq.1.2.head_mem_B
    have hy₂B : y₂ ∈ B := hqalt.2.head_mem_B
    have hy_ne_y₁ : y ≠ y₁ := by
      intro h
      apply hyp
      rw [h]
      exact List.head_mem _
    have hy_ne_y₂ : y ≠ y₂ := by
      intro h
      apply hyq
      rw [h]
      exact List.head_mem _
    have hy₁_ne_y₂ : y₁ ≠ y₂ := by
      have hd := (List.nodup_append.mp hpq.2.2.1).2.2
      exact hd y₁ (List.head_mem _) y₂ (List.head_mem _)
    have hobs := hthree l r x z y y₁ y₂ hsplit hyB hy₁B hy₂B
      hy_ne_y₁ hy_ne_y₂ hy₁_ne_y₂
    have eliminate (w : V) (hwC : w ∈ cpath.toFinset)
        (hwp : w ∉ p) (hwq : w ∉ q)
        (hw : (H.Adj w y ∧ H.Adj w y₁) ∨
          (H.Adj w y ∧ H.Adj w y₂) ∨
          (H.Adj w y₁ ∧ H.Adj w y₂)) : False := by
      have hy_ne_w : y ≠ w := by
        intro h
        subst w
        exact Finset.disjoint_left.mp hCB hwC hyB
      rcases hw with hwy₁ | hwy₂ | hwy₁y₂
      · let p' := y :: w :: p
        have hp' : AltBCPath H cpath.toFinset B p' := by
          refine ⟨isPath_prepend_BC hpq.1.1 hyp hwp hwy₁.1.symm hwy₁.2,
            hpq.1.2.cons_pair hyB hwC⟩
        have hn : (p' ++ q).Nodup := by
          change (y :: w :: (p ++ q)).Nodup
          exact .cons (by simp [hyp, hyq, hy_ne_w])
            (.cons (by simp [hwp, hwq]) hpq.2.2.1)
        have hRp' : R ⊆ p'.toFinset := by
          intro a ha
          simp only [p', List.toFinset_cons, Finset.mem_insert]
          exact Or.inr (Or.inr (hpq.2.2.2 ha))
        have hPair' : Pair p' q := ⟨hp', Or.inr hqalt, hn, hRp'⟩
        have hle := hpmax p' q hPair'
        simp [p'] at hle
      · let q' := y :: w :: q
        have hq' : AltBCPath H cpath.toFinset B q' := by
          refine ⟨isPath_prepend_BC hqalt.1 hyq hwq hwy₂.1.symm hwy₂.2,
            hqalt.2.cons_pair hyB hwC⟩
        have hnew : (y :: w :: (p ++ q)).Nodup :=
          .cons (by simp [hyp, hyq, hy_ne_w])
            (.cons (by simp [hwp, hwq]) hpq.2.2.1)
        have hperm : List.Perm (p ++ q') (y :: w :: (p ++ q)) := by
          dsimp [q']
          exact (List.perm_middle (l₁ := p) (l₂ := w :: q) (a := y)).trans
            ((List.perm_middle (l₁ := p) (l₂ := q) (a := w)).cons y)
        have hn : (p ++ q').Nodup := hperm.nodup_iff.mpr hnew
        have hPair' : Pair p q' := ⟨hpq.1, Or.inr hq', hn, hpq.2.2.2⟩
        have hle := hqmax p q' hPair' rfl
        simp [q'] at hle
      · let p' := q.dropLast.reverse ++ w :: p
        have hp' : AltBCPath H cpath.toFinset B p' := by
          refine ⟨?_, hqalt.2.merge hpq.1.2 hwC⟩
          exact isPath_merge hpq.1.1 hqalt.1 hqalt.2.length_two_le
            hwp hwq hpq.2.2.1 hwy₁y₂.2.symm hwy₁y₂.1
        have hRp' : R ⊆ p'.toFinset := by
          intro a ha
          simp only [p', List.toFinset_append, List.toFinset_cons, Finset.mem_union,
            Finset.mem_insert]
          exact Or.inr (Or.inr (hpq.2.2.2 ha))
        have hPair' : Pair p' [] := by
          refine ⟨hp', Or.inl rfl, ?_, hRp'⟩
          simpa using hp'.1.2.1
        have hle := hpmax p' [] hPair'
        have hqlen : 2 ≤ q.length := hqalt.2.length_two_le
        simp [p', List.length_dropLast] at hle
        omega
    rcases hobs with hxobs | hzobs
    · exact eliminate x hxC hxp hxq hxobs
    · exact eliminate z hzC hzp hzq hzobs

/-- Join the reverse of the first alternating path to the two original
endpoints and then, when present, continue along the second alternating path. -/
theorem isPath_reverse_append_endpoints
    [DecidableEq V] {H : SimpleGraph V} {p q : List V} {a d : V}
    (hp : IsPath H p) (hq : q = [] ∨ IsPath H q)
    (hpq : (p ++ q).Nodup)
    (ha : a ∉ p ++ q) (hd : d ∉ p ++ q) (hadne : a ≠ d)
    (hpa : H.Adj (p.head hp.1) a) (had : H.Adj a d)
    (hdq : ∀ hq0 : q ≠ [], H.Adj d (q.head hq0)) :
    IsPath H (p.reverse ++ a :: d :: q) := by
  have htail : (a :: d :: q).IsChain H.Adj := by
    rcases hq with rfl | hq
    · simpa using had
    · exact .cons_cons had (hq.2.2.cons_of_ne_nil hq.1 (hdq hq.1))
  have hchain : (p.reverse ++ a :: d :: q).IsChain H.Adj := by
    apply (isPath_reverse hp).2.2.append htail
    intro x hx y hy
    simp only [List.getLast?_reverse] at hx
    rw [List.head?_eq_some_head hp.1] at hx
    simp only [Option.mem_some_iff] at hx
    simp only [List.head?_cons, Option.mem_some_iff] at hy
    subst x
    subst y
    exact hpa
  have hnew : (a :: d :: (p ++ q)).Nodup := by
    exact .cons (by simp [hadne, ha]) (.cons hd hpq)
  have hperm : List.Perm (p.reverse ++ a :: d :: q) (a :: d :: (p ++ q)) := by
    calc
      p.reverse ++ a :: d :: q ~ p ++ a :: d :: q :=
        (List.reverse_perm p).append_right _
      _ ~ a :: (p ++ d :: q) := List.perm_middle
      _ ~ a :: d :: (p ++ q) := (List.perm_middle.cons a)
  exact ⟨by simp [hp.1], hperm.nodup_iff.mpr hnew, hchain⟩

/-- Once the two disjoint balanced alternating paths cover `B`, they use
exactly `|B|` vertices from the other side. -/
theorem altBCPair_internal_card_eq
    [DecidableEq V] {H : SimpleGraph V} {C B : Finset V} {p q : List V}
    (hCB : Disjoint C B) (hp : AltBCPath H C B p)
    (hq : q = [] ∨ AltBCPath H C B q) (hpq : (p ++ q).Nodup)
    (hcover : ∀ y ∈ B, y ∈ p ∨ y ∈ q) :
    ((p ++ q).toFinset ∩ C).card = B.card := by
  have hside : ((p ++ q).toFinset ∩ C).card =
      ((p ++ q).toFinset ∩ B).card := by
    rw [card_inter_eq_filter_length C hpq, card_inter_eq_filter_length B hpq]
    simp only [List.filter_append, List.length_append]
    have hpcount := hp.2.filter_length_eq hCB
    rcases hq with rfl | hq
    · simpa using hpcount
    · have hqcount := hq.2.filter_length_eq hCB
      omega
  have heq : (p ++ q).toFinset ∩ B = B := by
    apply Finset.Subset.antisymm Finset.inter_subset_right
    intro y hy
    have hy' := hcover y hy
    exact Finset.mem_inter.mpr ⟨by simpa using hy', hy⟩
  rw [hside, heq]

private lemma compl_adj_one_of_consecutive [DecidableEq V]
    {G : SimpleGraph V} {p : List V}
    (hp : IsPath G p) (hmax : IsGloballyLongestMonoPath G p)
    {l r : List V} {x z y : V} (hsplit : p = l ++ x :: z :: r)
    (hy : y ∉ p) : Gᶜ.Adj x y ∨ Gᶜ.Adj z y := by
  have hxy : x ≠ y := fun h ↦ hy (hsplit ▸ by simp [h])
  have hzy : z ≠ y := fun h ↦ hy (hsplit ▸ by simp [h])
  by_cases hx : G.Adj x y
  · right
    rw [SimpleGraph.compl_adj]
    refine ⟨hzy, ?_⟩
    intro hz
    exact no_common_adj_consecutive_of_longest hp hmax hsplit hy ⟨hx, hz.symm⟩
  · left
    rw [SimpleGraph.compl_adj]
    exact ⟨hxy, hx⟩

/-- Strengthened strict rotation lemma.  Besides the numerical conclusion it
records both support containment and the consecutive endpoint edge; these are
needed for the equality case. -/
theorem rotation_strict_with_endpoints [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {p : List V}
    (hp : IsPath G p) (hmax : IsGloballyLongestMonoPath G p)
    (hncut : ¬ IsCutColoring G) (ht : 2 ≤ p.length)
    (B : Finset V) (hB : Disjoint B p.toFinset)
    (hb : B.card < (p.length + 1) / 2) :
    ∃ q : List V, IsStrictRotation G p q B := by
  classical
  obtain ⟨a, d, C, hpEq, ha, hd⟩ := exists_endpoint_decomposition hp ht
  have had : a ≠ d := by
    intro h
    have hN : (a :: C ++ [d]).Nodup := hpEq ▸ hp.2.1
    exact (List.nodup_cons.mp hN).1 (by simp [h])
  have haC : a ∉ C := by
    have hN : (a :: C ++ [d]).Nodup := hpEq ▸ hp.2.1
    intro h
    exact (List.nodup_cons.mp hN).1 (by simp [h])
  have hdC : d ∉ C := by
    have hN : (a :: C ++ [d]).Nodup := hpEq ▸ hp.2.1
    have htN := (List.nodup_cons.mp hN).2
    have hd := (List.nodup_append.mp htN).2.2
    intro h
    exact hd d h d (by simp) rfl
  have hCN : C.Nodup := by
    have hN : (a :: C ++ [d]).Nodup := hpEq ▸ hp.2.1
    exact (List.nodup_append.mp (List.nodup_cons.mp hN).2).1
  have hClen : C.length = p.length - 2 := by simp [hpEq]
  have hCB : Disjoint C.toFinset B := by
    rw [Finset.disjoint_left]
    intro x hxC hxB
    apply Finset.disjoint_left.mp hB hxB
    apply List.mem_toFinset.mpr
    have hx : x ∈ C := List.mem_toFinset.mp hxC
    simp [hpEq, hx]
  by_cases hB0 : B = ∅
  · subst B
    let q := [a, d]
    have hadj : Gᶜ.Adj a d := by
      simpa [ha, hd] using compl_adj_endpoints_of_not_cut hp hmax hncut ht
    have hq : IsPath Gᶜ q := by
      exact ⟨by simp [q], by simp [q, had], by simpa [q] using hadj⟩
    refine ⟨q, hq, by simp, ?_, ?_, ?_⟩
    · intro y hy
      refine Or.inl ?_
      simp [q] at hy
      rcases hy with rfl | rfl <;> simp [hpEq]
    · have hsub : ({a, d} : Finset V) ⊆ q.toFinset ∩ p.toFinset := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> simp [q, hpEq]
      have hc := Finset.card_le_card hsub
      simpa [q, had] using hc
    · refine ⟨hp, [], [], ?_⟩
      left
      simp [q, ha, hd]
  · have hBpos : 0 < B.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hB0)
    have ht3 : 3 ≤ p.length := by omega
    let Special : Prop := Odd p.length ∧ B.card + 1 = (p.length + 1) / 2
    obtain ⟨R, hRsub, hseed, hexclude⟩ :
        ∃ R : Finset V,
          R ⊆ C.toFinset ∧
          (∃ s, AltBCPath Gᶜ C.toFinset B s ∧ R ⊆ s.toFinset) ∧
          (∀ U : Finset V, R ⊆ U → Odd p.length →
            B.card + 1 = (p.length + 1) / 2 →
            U = oddIndexedVertices C → False) := by
      by_cases hs : Special
      · obtain ⟨e, heE, y, hyB, hey⟩ :=
          exists_compl_even_edge_of_odd_borderline hp hmax hncut hpEq B hB hs.1 hs.2
        refine ⟨{e}, ?_, ?_, ?_⟩
        · simpa using evenIndexedVertices_subset_toFinset C heE
        · refine ⟨[y, e], ⟨?_, .one y e hyB
              (evenIndexedVertices_subset_toFinset C heE)⟩, ?_⟩
          · exact ⟨by simp, by simp [hey.ne.symm], by simpa using hey.symm⟩
          · simp
        · intro U heU _ _ hU
          have heO : e ∈ oddIndexedVertices C := by
            rw [← hU]
            exact heU (by simp)
          exact Finset.disjoint_left.mp
            (evenIndexedVertices_disjoint_oddIndexedVertices C hCN) heE heO
      · have hgap0 := hasConsecutiveOutside_or_oddIndexedVertices
            p.length B.card C ∅ ht3 hBpos hClen hCN (by simp) (by simp) hb
        obtain hgap0 | hbad := hgap0
        · obtain ⟨l, r, x, z, hsplit, -, -⟩ := hgap0
          obtain ⟨y, hyB⟩ := Finset.card_pos.mp hBpos
          have hyP : y ∉ p := by
            intro hyP
            exact Finset.disjoint_left.mp hB hyB (List.mem_toFinset.mpr hyP)
          have hadj := compl_adj_one_of_consecutive hp hmax
            (show p = (a :: l) ++ x :: z :: (r ++ [d]) by simp [hpEq, hsplit]) hyP
          rcases hadj with hxy | hzy
          · refine ⟨∅, by simp, ⟨[y, x], ⟨?_, .one y x hyB (by simp [hsplit])⟩,
                by simp⟩, ?_⟩
            · exact ⟨by simp, by simp [hxy.ne.symm], by simpa using hxy.symm⟩
            · intro U _ hodd hcard _
              exact hs ⟨hodd, hcard⟩
          · refine ⟨∅, by simp, ⟨[y, z], ⟨?_, .one y z hyB (by simp [hsplit])⟩,
                by simp⟩, ?_⟩
            · exact ⟨by simp, by simp [hzy.ne.symm], by simpa using hzy.symm⟩
            · intro U _ hodd hcard _
              exact hs ⟨hodd, hcard⟩
        · exact (hs ⟨hbad.1, hbad.2.1⟩).elim
    have hgap : ∀ U : Finset V, U ⊆ C.toFinset → R ⊆ U →
        U.card ≤ B.card - 1 → HasConsecutiveOutside U C := by
      intro U hUC hRU hcardU
      rcases hasConsecutiveOutside_or_oddIndexedVertices p.length B.card C U
          ht3 hBpos hClen hCN hUC hcardU hb with hgap | hbad
      · exact hgap
      · exact (hexclude U hRU hbad.1 hbad.2.1 hbad.2.2).elim
    obtain ⟨p₁, p₂, hp₁, hp₂, hp₁p₂, hcover⟩ :=
      exists_two_altBCPath_cover Gᶜ C B R hCB hRsub hseed
        (fun U hUC hRU hcardU ↦ by
          obtain ⟨l, r, x, z, hs, hx, hz⟩ := hgap U hUC hRU hcardU
          exact ⟨l, r, x, z, hs, hx, hz⟩)
        (by
          intro l r x z y hs hyB
          have hyP : y ∉ p := by
            intro hyp
            exact Finset.disjoint_left.mp hB hyB (List.mem_toFinset.mpr hyp)
          exact compl_adj_one_of_consecutive hp hmax
            (show p = (a :: l) ++ x :: z :: (r ++ [d]) by simp [hpEq, hs]) hyP)
        (by
          intro l r x z y₀ y₁ y₂ hs hy₀ hy₁ hy₂ h₀₁ h₀₂ h₁₂
          have hout (y : V) (hy : y ∈ B) : y ∉ p := by
            intro hyp
            exact Finset.disjoint_left.mp hB hy (List.mem_toFinset.mpr hyp)
          exact rotation_triple_observation hp hmax
            (show p = (a :: l) ++ x :: z :: (r ++ [d]) by simp [hpEq, hs])
            (hout y₀ hy₀) (hout y₁ hy₁) (hout y₂ hy₂) h₀₁ h₀₂ h₁₂)
    have hp₂path : p₂ = [] ∨ IsPath Gᶜ p₂ := hp₂.imp_right And.left
    have hparts {x : V} (hx : x ∈ p₁ ++ p₂) : x ∈ C.toFinset ∨ x ∈ B := by
      rcases List.mem_append.mp hx with hx | hx
      · exact (hp₁.2.mem_union hx).symm
      · rcases hp₂ with rfl | hp₂
        · simp at hx
        · exact (hp₂.2.mem_union hx).symm
    have haFresh : a ∉ p₁ ++ p₂ := by
      intro hx
      rcases hparts hx with hxC | hxB
      · exact haC (List.mem_toFinset.mp hxC)
      · exact Finset.disjoint_left.mp hB hxB (by simp [hpEq])
    have hdFresh : d ∉ p₁ ++ p₂ := by
      intro hx
      rcases hparts hx with hxC | hxB
      · exact hdC (List.mem_toFinset.mp hxC)
      · exact Finset.disjoint_left.mp hB hxB (by simp [hpEq])
    have hp₁headB : p₁.head hp₁.1.1 ∈ B := hp₁.2.head_mem_B
    have hp₁headOut : p₁.head hp₁.1.1 ∉ p := by
      intro h
      exact Finset.disjoint_left.mp hB hp₁headB (List.mem_toFinset.mpr h)
    have hpa : Gᶜ.Adj (p₁.head hp₁.1.1) a := by
      simpa [ha] using
        (compl_adj_endpoints_of_longest hp hmax hp₁headOut).1.symm
    have hdq : ∀ hp₂0 : p₂ ≠ [], Gᶜ.Adj d (p₂.head hp₂0) := by
      intro hp₂0
      obtain hp₂alt := hp₂.resolve_left hp₂0
      have hheadB : p₂.head hp₂alt.1.1 ∈ B := hp₂alt.2.head_mem_B
      have hout : p₂.head hp₂alt.1.1 ∉ p := by
        intro h
        exact Finset.disjoint_left.mp hB hheadB (List.mem_toFinset.mpr h)
      simpa [hd] using (compl_adj_endpoints_of_longest hp hmax hout).2.symm
    have hadj : Gᶜ.Adj a d := by
      simpa [ha, hd] using compl_adj_endpoints_of_not_cut hp hmax hncut ht
    let q := p₁.reverse ++ a :: d :: p₂
    have hq : IsPath Gᶜ q := isPath_reverse_append_endpoints hp₁.1 hp₂path hp₁p₂
      haFresh hdFresh had hpa hadj hdq
    have hqcover : ∀ y ∈ B, y ∈ q := by
      intro y hy
      rcases hcover y hy with hy₁ | hy₂
      · simp [q, hy₁]
      · simp [q, hy₂]
    have hqsupport : ∀ y ∈ q, y ∈ p ∨ y ∈ B := by
      intro y hy
      simp only [q, List.mem_append, List.mem_cons] at hy
      rcases hy with hy | rfl | rfl | hy
      · have hy₁ : y ∈ p₁ := by simpa using hy
        rcases hp₁.2.mem_union hy₁ with hyB | hyC
        · exact Or.inr hyB
        · exact Or.inl (by
            have : y ∈ C := List.mem_toFinset.mp hyC
            simp [hpEq, this])
      · exact Or.inl (by simp [hpEq])
      · exact Or.inl (by simp [hpEq])
      · obtain hp₂alt := hp₂.resolve_left (fun h ↦ by simpa [h] using hy)
        rcases hp₂alt.2.mem_union hy with hyB | hyC
        · exact Or.inr hyB
        · exact Or.inl (by
            have : y ∈ C := List.mem_toFinset.mp hyC
            simp [hpEq, this])
    let U := (p₁ ++ p₂).toFinset ∩ C.toFinset
    have hUcard : U.card = B.card :=
      altBCPair_internal_card_eq hCB hp₁ hp₂ hp₁p₂ hcover
    have haU : a ∉ U := by
      intro haU'
      exact haC (List.mem_toFinset.mp (Finset.mem_inter.mp haU').2)
    have hdU : d ∉ U := by
      intro hdU'
      exact hdC (List.mem_toFinset.mp (Finset.mem_inter.mp hdU').2)
    have hTsub : insert a (insert d U) ⊆ q.toFinset ∩ p.toFinset := by
      intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | rfl | hx
      · simp [q, hpEq]
      · simp [q, hpEq]
      · have hxpair : x ∈ p₁ ++ p₂ := List.mem_toFinset.mp (Finset.mem_inter.mp hx).1
        have hxC : x ∈ C := List.mem_toFinset.mp (Finset.mem_inter.mp hx).2
        refine Finset.mem_inter.mpr ⟨?_, ?_⟩
        · rcases List.mem_append.mp hxpair with hx₁ | hx₂
          · simp [q, hx₁]
          · simp [q, hx₂]
        · exact List.mem_toFinset.mpr (by simp [hpEq, hxC])
    have hqcard : B.card + 2 ≤ (q.toFinset ∩ p.toFinset).card := by
      have hc := Finset.card_le_card hTsub
      have haDU : a ∉ insert d U := by simp [had, haU]
      rw [Finset.card_insert_of_notMem haDU,
        Finset.card_insert_of_notMem hdU, hUcard] at hc
      omega
    refine ⟨q, hq, hqcover, hqsupport, hqcard, hp, p₁.reverse, p₂, ?_⟩
    left
    dsimp [q]
    rw [ha, hd]

/-- Erdős--Gyárfás strict rotation lemma. -/
theorem rotation_strict [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {p : List V}
    (hp : IsPath G p) (hmax : IsGloballyLongestMonoPath G p)
    (hncut : ¬ IsCutColoring G) (ht : 2 ≤ p.length)
    (B : Finset V) (hB : Disjoint B p.toFinset)
    (hb : B.card < (p.length + 1) / 2) :
    ∃ q : List V, IsPath Gᶜ q ∧ (∀ y ∈ B, y ∈ q) ∧
      B.card + 2 ≤ (q.toFinset ∩ p.toFinset).card := by
  obtain ⟨q, hq, hcover, -, hcard, -⟩ :=
    rotation_strict_with_endpoints hp hmax hncut ht B hB hb
  exact ⟨q, hq, hcover, hcard⟩

/-- Erdős--Gyárfás rotation lemma in the even equality case. -/
theorem rotation_even [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {p : List V}
    (hp : IsPath G p) (hmax : IsGloballyLongestMonoPath G p)
    (hncut : ¬ IsCutColoring G) (ht : 2 ≤ p.length)
    (B : Finset V) (hB : Disjoint B p.toFinset)
    (heven : Even p.length) (hcard : B.card = p.length / 2) :
    ∃ q : List V, IsPath Gᶜ q ∧ (∀ y ∈ B, y ∈ q) ∧
      B.card + 1 ≤ (q.toFinset ∩ p.toFinset).card := by
  classical
  rcases heven with ⟨k, hk⟩
  have hBpos : 0 < B.card := by omega
  obtain ⟨y, hyB⟩ := Finset.card_pos.mp hBpos
  have hyP : y ∉ p := by
    intro hyp
    exact Finset.disjoint_left.mp hB hyB (List.mem_toFinset.mpr hyp)
  let B' := B.erase y
  have hB'dis : Disjoint B' p.toFinset := by
    rw [Finset.disjoint_left]
    intro x hxB' hxP
    exact Finset.disjoint_left.mp hB (Finset.mem_erase.mp hxB').2 hxP
  have hB'card : B'.card + 1 = B.card := by
    simp [B', hyB]
    omega
  have hB'small : B'.card < (p.length + 1) / 2 := by omega
  obtain ⟨q, hq, hqB', hqsupp, hinter, hcert⟩ :=
    rotation_strict_with_endpoints hp hmax hncut ht B' hB'dis hB'small
  rcases hcert with ⟨hp', l, r, hdecomp⟩
  have hynq : y ∉ q := by
    intro hyq
    rcases hqsupp y hyq with hyp | hyB'
    · exact hyP hyp
    · exact (Finset.mem_erase.mp hyB').1 rfl
  have hends := compl_adj_endpoints_of_longest hp hmax hyP
  rcases hdecomp with hdecomp | hdecomp
  · let q' := l ++ p.head hp.1 :: y :: p.getLast hp.1 :: r
    have hbase : IsPath Gᶜ (l ++ p.head hp.1 :: p.getLast hp.1 :: r) := by
      simpa [hdecomp] using hq
    have hybase : y ∉ l ++ p.head hp.1 :: p.getLast hp.1 :: r := by
      simpa [hdecomp] using hynq
    have hq' : IsPath Gᶜ q' := by
      exact isPath_insert_between hbase hybase hends.1 hends.2
    have hsub : q.toFinset ⊆ q'.toFinset := by
      intro z hz
      apply List.mem_toFinset.mpr
      have hzq := List.mem_toFinset.mp hz
      rw [hdecomp] at hzq
      simp only [q', List.mem_append, List.mem_cons] at hzq ⊢
      aesop
    refine ⟨q', hq', ?_, ?_⟩
    · intro z hzB
      by_cases hzy : z = y
      · subst z
        simp [q']
      · have hzB' : z ∈ B' := Finset.mem_erase.mpr ⟨hzy, hzB⟩
        exact List.mem_toFinset.mp (hsub (List.mem_toFinset.mpr (hqB' z hzB')))
    · have hi : q.toFinset ∩ p.toFinset ⊆ q'.toFinset ∩ p.toFinset := by
        intro z hz
        exact Finset.mem_inter.mpr ⟨hsub (Finset.mem_inter.mp hz).1,
          (Finset.mem_inter.mp hz).2⟩
      have hle := Finset.card_le_card hi
      omega
  · let q' := l ++ p.getLast hp.1 :: y :: p.head hp.1 :: r
    have hbase : IsPath Gᶜ (l ++ p.getLast hp.1 :: p.head hp.1 :: r) := by
      simpa [hdecomp] using hq
    have hybase : y ∉ l ++ p.getLast hp.1 :: p.head hp.1 :: r := by
      simpa [hdecomp] using hynq
    have hq' : IsPath Gᶜ q' := by
      exact isPath_insert_between hbase hybase hends.2.symm hends.1.symm
    have hsub : q.toFinset ⊆ q'.toFinset := by
      intro z hz
      apply List.mem_toFinset.mpr
      have hzq := List.mem_toFinset.mp hz
      rw [hdecomp] at hzq
      simp only [q', List.mem_append, List.mem_cons] at hzq ⊢
      aesop
    refine ⟨q', hq', ?_, ?_⟩
    · intro z hzB
      by_cases hzy : z = y
      · subst z
        simp [q']
      · have hzB' : z ∈ B' := Finset.mem_erase.mpr ⟨hzy, hzB⟩
        exact List.mem_toFinset.mp (hsub (List.mem_toFinset.mpr (hqB' z hzB')))
    · have hi : q.toFinset ∩ p.toFinset ⊆ q'.toFinset ∩ p.toFinset := by
        intro z hz
        exact Finset.mem_inter.mpr ⟨hsub (Finset.mem_inter.mp hz).1,
          (Finset.mem_inter.mp hz).2⟩
      have hle := Finset.card_le_card hi
      omega

end Erdos518
