/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTMader

/-!
# Mader's cycle theorem for minimally three-connected graphs

This file proves the `k = 3` instance of Mader's theorem used as
Theorem 4.1 by Aboulker--Havet--Trotignon: every cycle in an
edge-minimally three-connected finite graph contains a vertex of degree
three.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

namespace Mader41

private def strictLeft {H : SimpleGraph V} (s : AHTSeparation H) : Finset V :=
  s.left \ s.right

private def strictRight {H : SimpleGraph V} (s : AHTSeparation H) : Finset V :=
  s.right \ s.left

private lemma mem_left_iff_mem_strictLeft_or_separator
    {H : SimpleGraph V} (s : AHTSeparation H) {v : V} :
    v ∈ s.left ↔ v ∈ strictLeft s ∨ v ∈ s.separator := by
  simp [strictLeft, AHTSeparation.separator]
  tauto

private lemma mem_right_iff_mem_strictRight_or_separator
    {H : SimpleGraph V} (s : AHTSeparation H) {v : V} :
    v ∈ s.right ↔ v ∈ strictRight s ∨ v ∈ s.separator := by
  simp [strictRight, AHTSeparation.separator]
  tauto

private lemma mem_strictLeft_or_separator_or_strictRight
    {H : SimpleGraph V} [DecidableRel H.Adj]
    (s : AHTSeparation H) (v : V) :
    v ∈ strictLeft s ∨ v ∈ s.separator ∨ v ∈ strictRight s := by
  have hv := s.mem_left_or_mem_right v
  rcases hv with hv | hv
  · rw [mem_left_iff_mem_strictLeft_or_separator] at hv
    exact hv.elim Or.inl (fun h ↦ Or.inr (Or.inl h))
  · rw [mem_right_iff_mem_strictRight_or_separator] at hv
    exact hv.elim (fun h ↦ Or.inr (Or.inr h)) (fun h ↦ Or.inr (Or.inl h))

private structure CriticalCut (G : SimpleGraph V) (a x : V) where
  separation : AHTSeparation (eraseEdge G a x)
  proper : separation.Proper
  a_mem : a ∈ strictLeft separation
  x_mem : x ∈ strictRight separation
  order_lt_three : separation.order < 3

namespace CriticalCut

private abbrev left {a x : V} (C : CriticalCut G a x) : Finset V :=
  strictLeft C.separation

private abbrev middle {a x : V} (C : CriticalCut G a x) : Finset V :=
  C.separation.separator

private abbrev right {a x : V} (C : CriticalCut G a x) : Finset V :=
  strictRight C.separation

private theorem middle_card_lt_three {a x : V} (C : CriticalCut G a x) :
    C.middle.card < 3 := by
  exact C.order_lt_three

private theorem pairwise_disjoint {a x : V} (C : CriticalCut G a x) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin 3)) ![C.left, C.middle, C.right] := by
  intro i _ j _ hij
  fin_cases i <;> fin_cases j <;>
    simp_all [left, middle, right, strictLeft, strictRight,
      AHTSeparation.separator, Finset.disjoint_left]

private theorem cover {a x : V} (C : CriticalCut G a x) :
    C.left ∪ C.middle ∪ C.right = Finset.univ := by
  ext v
  simp only [Finset.mem_union, Finset.mem_univ, iff_true]
  rcases mem_strictLeft_or_separator_or_strictRight C.separation v with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

private theorem mem_trichotomy {a x : V} (C : CriticalCut G a x) (v : V) :
    v ∈ C.left ∨ v ∈ C.middle ∨ v ∈ C.right := by
  exact mem_strictLeft_or_separator_or_strictRight C.separation v

private theorem cross_eq {a x u v : V} (C : CriticalCut G a x)
    (hu : u ∈ C.left) (hv : v ∈ C.right) (huv : G.Adj u v) :
    u = a ∧ v = x := by
  have hnot : ¬(eraseEdge G a x).Adj u v := by
    exact C.separation.not_adj
      (Finset.mem_sdiff.mp hu).1 (Finset.mem_sdiff.mp hu).2
      (Finset.mem_sdiff.mp hv).1 (Finset.mem_sdiff.mp hv).2
  rw [eraseEdge_adj] at hnot
  have hp : (u = a ∧ v = x) ∨ (u = x ∧ v = a) := by
    tauto
  rcases hp with hp | hp
  · exact hp
  · exfalso
    exact (Finset.mem_sdiff.mp C.x_mem).2
      (hp.1 ▸ (Finset.mem_sdiff.mp hu).1)

private theorem walk_stays_left_after_delete_a
    {a x : V} (C : CriticalCut G a x)
    {z w : {v : V // v ∉ C.middle ∪ {a}}}
    (p : (G.induce {v : V | v ∉ C.middle ∪ {a}}).Walk z w)
    (hz : z.1 ∈ C.left) : w.1 ∈ C.left := by
  induction p with
  | nil => simpa only using hz
  | @cons z y w hzy p ih =>
      have hzyG : G.Adj z.1 y.1 := hzy
      have hyMiddle : y.1 ∉ C.middle := by
        intro hy
        exact y.property (Finset.mem_union_left _ hy)
      have hya : y.1 ≠ a := by
        intro hya
        exact y.property (Finset.mem_union_right _ (by simpa [hya]))
      have hyLeft : y.1 ∈ C.left := by
        rcases C.mem_trichotomy y.1 with hy | hy | hy
        · exact hy
        · exact (hyMiddle hy).elim
        · have hcross := C.cross_eq hz hy hzyG
          have hza : z.1 = a := hcross.1
          exact (z.property
            (Finset.mem_union_right _ (by simpa [hza]))).elim
      exact ih hyLeft

private theorem middle_card_eq_two
    {a x : V} (C : CriticalCut G a x)
    (hthree : IsThreeConnected G) (hdega : 4 ≤ G.degree a) :
    C.middle.card = 2 := by
  apply Nat.eq_of_lt_succ_of_not_lt C.middle_card_lt_three
  intro hsmall
  have htarget : (insert x C.middle).card < (G.neighborFinset a).card := by
    rw [G.card_neighborFinset_eq_degree]
    calc
      (insert x C.middle).card ≤ C.middle.card + 1 := Finset.card_insert_le _ _
      _ ≤ 2 := by omega
      _ < G.degree a := by omega
  obtain ⟨z, hza, hzout⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card htarget
  have haz : G.Adj a z := by simpa using hza
  have hzx : z ≠ x := by
    intro h
    exact hzout (by simp [h])
  have hzMiddle : z ∉ C.middle := by
    intro hz
    exact hzout (Finset.mem_insert_of_mem hz)
  have hzLeft : z ∈ C.left := by
    rcases C.mem_trichotomy z with hz | hz | hz
    · exact hz
    · exact (hzMiddle hz).elim
    · have hcross := C.cross_eq C.a_mem hz haz
      exact (hzx hcross.2).elim
  have hza_ne : z ≠ a := haz.ne'
  let Q : Finset V := C.middle ∪ {a}
  have hQcard : Q.card < 3 := by
    calc
      Q.card ≤ C.middle.card + ({a} : Finset V).card := by
        exact Finset.card_union_le _ _
      _ = C.middle.card + 1 := by simp
      _ < 3 := by omega
  have hzQ : z ∉ Q := by simp [Q, hzMiddle, hza_ne]
  have hxMiddle : x ∉ C.middle := by
    intro hx
    exact (Finset.mem_sdiff.mp C.x_mem).2 (Finset.mem_inter.mp hx).1
  have hxa : x ≠ a := by
    intro h
    exact (Finset.mem_sdiff.mp C.x_mem).2
      (h.symm ▸ (Finset.mem_sdiff.mp C.a_mem).1)
  have hxQ : x ∉ Q := by simp [Q, hxMiddle, hxa]
  have hreach :
      (G.induce {v : V | v ∉ Q}).Reachable ⟨z, hzQ⟩ ⟨x, hxQ⟩ :=
    hthree.induce_compl_preconnected Q hQcard _ _
  obtain ⟨p⟩ := hreach
  have hxLeft : x ∈ C.left := by
    simpa only [Q] using C.walk_stays_left_after_delete_a p hzLeft
  exact (Finset.mem_sdiff.mp C.x_mem).2 (Finset.mem_sdiff.mp hxLeft).1

end CriticalCut

private def swapSeparation {H : SimpleGraph V} (s : AHTSeparation H) :
    AHTSeparation H where
  left := s.right
  right := s.left
  cover := by simpa [Finset.union_comm] using s.cover
  not_adj := by
    intro u v huL huR hvR hvL huv
    exact s.not_adj hvR hvL huL huR huv.symm

private theorem exists_criticalCut
    (hmin : IsEdgeMinimallyThreeConnected G) {a x : V}
    (hax : G.Adj a x) : Nonempty (CriticalCut G a x) := by
  have hnot := hmin.eraseEdge_not_isThreeConnected hax
  have hnotall :
      ¬ ∀ s : AHTSeparation (eraseEdge G a x),
          s.Proper → 3 ≤ s.order := by
    intro hall
    exact hnot ⟨hmin.isThreeConnected.1, hall⟩
  push_neg at hnotall
  obtain ⟨s, hsProper, hsOrder⟩ := hnotall
  have hcross :
      (a ∈ strictLeft s ∧ x ∈ strictRight s) ∨
      (x ∈ strictLeft s ∧ a ∈ strictRight s) := by
    by_contra hn
    let hsepG : AHTSeparation G := {
      left := s.left
      right := s.right
      cover := s.cover
      not_adj := by
        intro u v huL huR hvR hvL huv
        apply s.not_adj huL huR hvR hvL
        rw [eraseEdge_adj]
        refine ⟨huv, ?_⟩
        intro hedge
        apply hn
        rcases hedge with hedge | hedge
        · apply Or.inl
          constructor
          · simpa [strictLeft, hedge.1] using
              (Finset.mem_sdiff.2 ⟨huL, huR⟩)
          · simpa [strictRight, hedge.2] using
              (Finset.mem_sdiff.2 ⟨hvR, hvL⟩)
        · apply Or.inr
          constructor
          · simpa [strictLeft, hedge.1] using
              (Finset.mem_sdiff.2 ⟨huL, huR⟩)
          · simpa [strictRight, hedge.2] using
              (Finset.mem_sdiff.2 ⟨hvR, hvL⟩)
      }
    have hlarge := hmin.isThreeConnected.2 hsepG hsProper
    exact (Nat.not_le_of_lt hsOrder) hlarge
  rcases hcross with hcross | hcross
  · exact ⟨{
      separation := s
      proper := hsProper
      a_mem := hcross.1
      x_mem := hcross.2
      order_lt_three := hsOrder }⟩
  · let t := swapSeparation s
    refine ⟨{
      separation := t
      proper := ?_
      a_mem := ?_
      x_mem := ?_
      order_lt_three := ?_ }⟩
    · exact ⟨hsProper.2, hsProper.1⟩
    · exact hcross.2
    · exact hcross.1
    · simpa [t, swapSeparation, AHTSeparation.order,
        AHTSeparation.separator, Finset.inter_comm] using hsOrder

private theorem no_closed_side_after_small_delete
    (hthree : IsThreeConnected G) (Q R : Finset V)
    (hQ : Q.card < 3) {z w : V}
    (hzQ : z ∉ Q) (hwQ : w ∉ Q) (hzR : z ∈ R) (hwR : w ∉ R)
    (hclosed : ∀ ⦃u v : V⦄, u ∈ R → u ∉ Q → v ∉ Q →
      G.Adj u v → v ∈ R) : False := by
  have hreach :
      (G.induce {v : V | v ∉ Q}).Reachable ⟨z, hzQ⟩ ⟨w, hwQ⟩ :=
    hthree.induce_compl_preconnected Q hQ _ _
  obtain ⟨p⟩ := hreach
  have hstay : ∀ {u v : {v : V // v ∉ Q}}
      (p : (G.induce {v : V | v ∉ Q}).Walk u v),
      u.1 ∈ R → v.1 ∈ R := by
    intro u v p hu
    induction p with
    | nil => simpa only using hu
    | @cons u y v huy p ih =>
        have hy : y.1 ∈ R := hclosed hu u.property y.property (by simpa using huy)
        exact ih hy
  exact hwR (hstay p hzR)

private theorem consecutive_cut_decrease
    {x a y : V} (hxa : G.Adj x a) (hay : G.Adj a y) (hxy : x ≠ y)
    (hthree : IsThreeConnected G) (hdegx : 4 ≤ G.degree x)
    (hdega : 4 ≤ G.degree a)
    (C : CriticalCut G x a) (D : CriticalCut G a y) :
    D.right.card < C.right.card := by
  have hScard : C.middle.card = 2 := C.middle_card_eq_two hthree hdegx
  have hTcard : D.middle.card = 2 := D.middle_card_eq_two hthree hdega
  have hClaimOne :
      (C.middle ∩ D.right).card ≤ (C.right ∩ D.middle).card := by
    by_contra hnot
    have hrev : (C.right ∩ D.middle).card < (C.middle ∩ D.right).card :=
      Nat.lt_of_not_ge hnot
    let U : Finset V := (C.middle \ D.right) ∪ (C.right ∩ D.middle)
    have hUcard : U.card < 2 := by
      have hle : U.card ≤ (C.middle \ D.right).card +
          (C.right ∩ D.middle).card := by
        exact Finset.card_union_le _ _
      have hsplit := Finset.card_sdiff_add_card_inter C.middle D.right
      rw [hScard] at hsplit
      omega
    let P : Finset V := insert x (insert y U)
    have hPcard : P.card < (G.neighborFinset a).card := by
      rw [G.card_neighborFinset_eq_degree]
      calc
        P.card ≤ (insert y U).card + 1 := by
          dsimp only [P]
          exact Finset.card_insert_le _ _
        _ ≤ (U.card + 1) + 1 := by
          gcongr
          exact Finset.card_insert_le _ _
        _ = U.card + 2 := by omega
        _ < 4 := by omega
        _ ≤ G.degree a := hdega
    obtain ⟨z, hza, hzP⟩ :=
      Finset.exists_mem_notMem_of_card_lt_card hPcard
    have haz : G.Adj a z := by simpa using hza
    have hzx : z ≠ x := by
      intro h
      exact hzP (by simp [P, h])
    have hzy : z ≠ y := by
      intro h
      exact hzP (by simp [P, h])
    have hzU : z ∉ U := by
      intro hz
      exact hzP (by simp [P, hz])
    have hzCright : z ∈ C.right := by
      rcases C.mem_trichotomy z with hz | hz | hz
      · have hcross := C.cross_eq hz C.x_mem haz.symm
        exact (hzx hcross.1).elim
      · have hzDright : z ∈ D.right := by
          by_contra hzD
          exact hzU (by
            apply Finset.mem_union_left
            exact Finset.mem_sdiff.2 ⟨hz, hzD⟩)
        have hcross := D.cross_eq D.a_mem hzDright haz
        exact (hzy hcross.2).elim
      · exact hz
    have hzDleft : z ∈ D.left := by
      rcases D.mem_trichotomy z with hz | hz | hz
      · exact hz
      · exact (hzU (by
          apply Finset.mem_union_right
          exact Finset.mem_inter.2 ⟨hzCright, hz⟩)).elim
      · have hcross := D.cross_eq D.a_mem hz haz
        exact (hzy hcross.2).elim
    let Q : Finset V := U ∪ {a}
    let R : Finset V := C.right ∩ D.left
    have hQcard : Q.card < 3 := by
      calc
        Q.card ≤ U.card + ({a} : Finset V).card := by
          exact Finset.card_union_le _ _
        _ = U.card + 1 := by simp
        _ < 3 := by omega
    have hza_ne : z ≠ a := haz.ne'
    have hzQ : z ∉ Q := by simp [Q, hzU, hza_ne]
    have hxU : x ∉ U := by
      intro hxU'
      rcases Finset.mem_union.mp hxU' with hxU' | hxU'
      · exact (Finset.mem_sdiff.mp C.a_mem).2
          (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxU').1).2
      · exact (Finset.mem_sdiff.mp C.a_mem).2
          (Finset.mem_sdiff.mp (Finset.mem_inter.mp hxU').1).1
    have hxa_ne : x ≠ a := hxa.ne
    have hxQ : x ∉ Q := by simp [Q, hxU, hxa_ne]
    have hzR : z ∈ R := Finset.mem_inter.2 ⟨hzCright, hzDleft⟩
    have hxR : x ∉ R := by
      intro hx
      exact (Finset.mem_sdiff.mp C.a_mem).2
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hx).1).1
    apply no_closed_side_after_small_delete hthree Q R hQcard hzQ hxQ hzR hxR
    intro u v huR huQ hvQ huv
    have huC : u ∈ C.right := (Finset.mem_inter.mp huR).1
    have huD : u ∈ D.left := (Finset.mem_inter.mp huR).2
    have huU : u ∉ U := fun hu ↦ huQ (Finset.mem_union_left _ hu)
    have hvU : v ∉ U := fun hv ↦ hvQ (Finset.mem_union_left _ hv)
    have hua : u ≠ a := by
      intro h
      exact huQ (Finset.mem_union_right _ (by simpa [h]))
    have hvC : v ∈ C.right := by
      rcases C.mem_trichotomy v with hv | hv | hv
      · have hcross := C.cross_eq hv huC huv.symm
        exact (hua hcross.2).elim
      · have hvDright : v ∈ D.right := by
          by_contra hvD
          exact hvU (Finset.mem_union_left _
            (Finset.mem_sdiff.2 ⟨hv, hvD⟩))
        have hcross := D.cross_eq huD hvDright huv
        exact (hua hcross.1).elim
      · exact hv
    have hvD : v ∈ D.left := by
      rcases D.mem_trichotomy v with hv | hv | hv
      · exact hv
      · exact (hvU (Finset.mem_union_right _
          (Finset.mem_inter.2 ⟨hvC, hv⟩))).elim
      · have hcross := D.cross_eq huD hv huv
        exact (hua hcross.1).elim
    exact Finset.mem_inter.2 ⟨hvC, hvD⟩
  have hClaimTwo : C.left ∩ D.right = ∅ := by
    by_contra hne
    obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hqC : q ∈ C.left := (Finset.mem_inter.mp hq).1
    have hqD : q ∈ D.right := (Finset.mem_inter.mp hq).2
    let W : Finset V := (C.middle ∩ D.right) ∪ (D.middle \ C.right)
    have hWcard : W.card < 3 := by
      have hle : W.card ≤ (C.middle ∩ D.right).card +
          (D.middle \ C.right).card := Finset.card_union_le _ _
      have hsplit := Finset.card_sdiff_add_card_inter D.middle C.right
      have hinter : (D.middle ∩ C.right).card =
          (C.right ∩ D.middle).card := by rw [Finset.inter_comm]
      rw [hTcard, hinter] at hsplit
      omega
    have hqCMiddle : q ∉ C.middle := by
      intro hm
      exact (Finset.mem_sdiff.mp hqC).2 (Finset.mem_inter.mp hm).2
    have hqDMiddle : q ∉ D.middle := by
      intro hm
      exact (Finset.mem_sdiff.mp hqD).2 (Finset.mem_inter.mp hm).1
    have hqW : q ∉ W := by simp [W, hqCMiddle, hqDMiddle]
    have haC : a ∈ C.right := C.x_mem
    have haD : a ∈ D.left := D.a_mem
    have haW : a ∉ W := by
      intro ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact (Finset.mem_sdiff.mp haD).2
          (Finset.mem_sdiff.mp (Finset.mem_inter.mp ha).2).1
      · exact (Finset.mem_sdiff.mp ha).2 haC
    let R : Finset V := C.left ∩ D.right
    have hqR : q ∈ R := hq
    have haR : a ∉ R := by
      intro ha
      exact (Finset.mem_sdiff.mp haC).2
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp ha).1).1
    apply no_closed_side_after_small_delete hthree W R hWcard hqW haW hqR haR
    intro u v huR huW hvW huv
    have huC : u ∈ C.left := (Finset.mem_inter.mp huR).1
    have huD : u ∈ D.right := (Finset.mem_inter.mp huR).2
    have hvC : v ∈ C.left := by
      rcases C.mem_trichotomy v with hv | hv | hv
      · exact hv
      · have hvDnot : v ∉ D.right := by
          intro hvD
          exact hvW (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hv, hvD⟩))
        rcases D.mem_trichotomy v with hvD | hvD | hvD
        · have hcrossD := D.cross_eq hvD huD huv.symm
          have hva : v = a := hcrossD.1
          have huy : u = y := hcrossD.2
          have hcrossC := C.cross_eq huC C.x_mem (hva ▸ huv)
          exact (hxy (hcrossC.1.symm.trans huy)).elim
        · have hvCright : v ∉ C.right := by
            intro hvCr
            exact (Finset.mem_sdiff.mp hvCr).2 (Finset.mem_inter.mp hv).1
          exact (hvW (Finset.mem_union_right _
            (Finset.mem_sdiff.2 ⟨hvD, hvCright⟩))).elim
        · exact (hvDnot hvD).elim
      · have hcrossC := C.cross_eq huC hv huv
        have hux : u = x := hcrossC.1
        have hva : v = a := hcrossC.2
        have hcrossD := D.cross_eq D.a_mem huD (hva ▸ huv.symm)
        exact (hxy (hux.symm.trans hcrossD.2)).elim
    have hvD : v ∈ D.right := by
      rcases D.mem_trichotomy v with hv | hv | hv
      · have hcrossD := D.cross_eq hv huD huv.symm
        have hva : v = a := hcrossD.1
        have huy : u = y := hcrossD.2
        have hcrossC := C.cross_eq huC C.x_mem (hva ▸ huv)
        exact (hxy (hcrossC.1.symm.trans huy)).elim
      · have hvCright : v ∈ C.right := by
          by_contra hvCr
          exact hvW (Finset.mem_union_right _
            (Finset.mem_sdiff.2 ⟨hv, hvCr⟩))
        have hcrossC := C.cross_eq huC hvCright huv
        have hux : u = x := hcrossC.1
        have hva : v = a := hcrossC.2
        have hcrossD := D.cross_eq D.a_mem huD (hva ▸ huv.symm)
        exact (hxy (hux.symm.trans hcrossD.2)).elim
      · exact hv
    exact Finset.mem_inter.2 ⟨hvC, hvD⟩
  have hYpartition :
      D.right = (C.middle ∩ D.right) ∪ (C.right ∩ D.right) := by
    ext v
    constructor
    · intro hv
      rcases C.mem_trichotomy v with hvC | hvC | hvC
      · have : v ∈ C.left ∩ D.right := Finset.mem_inter.2 ⟨hvC, hv⟩
        rw [hClaimTwo] at this
        simp at this
      · exact Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hvC, hv⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hvC, hv⟩)
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact (Finset.mem_inter.mp hv).2
      · exact (Finset.mem_inter.mp hv).2
  have hYdisj : Disjoint (C.middle ∩ D.right) (C.right ∩ D.right) := by
    apply Finset.disjoint_left.2
    intro v hvM hvR
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hvR).1).2
      (Finset.mem_inter.mp (Finset.mem_inter.mp hvM).1).1
  have hYcard : D.right.card = (C.middle ∩ D.right).card +
      (C.right ∩ D.right).card := by
    calc
      D.right.card =
          ((C.middle ∩ D.right) ∪ (C.right ∩ D.right)).card :=
        congrArg Finset.card hYpartition
      _ = _ := Finset.card_union_of_disjoint hYdisj
  have hApartition : C.right =
      ((C.right ∩ D.left) ∪ (C.right ∩ D.middle)) ∪
        (C.right ∩ D.right) := by
    ext v
    constructor
    · intro hv
      rcases D.mem_trichotomy v with hvD | hvD | hvD
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hv, hvD⟩))
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hv, hvD⟩))
      · exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hv, hvD⟩)
    · intro hv
      rcases Finset.mem_union.mp hv with hv | hv
      · rcases Finset.mem_union.mp hv with hv | hv
        · exact (Finset.mem_inter.mp hv).1
        · exact (Finset.mem_inter.mp hv).1
      · exact (Finset.mem_inter.mp hv).1
  have hABdisj : Disjoint (C.right ∩ D.left) (C.right ∩ D.middle) := by
    apply Finset.disjoint_left.2
    intro v hvL hvM
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hvL).2).2
      (Finset.mem_inter.mp (Finset.mem_inter.mp hvM).2).2
  have hABYdisj : Disjoint
      ((C.right ∩ D.left) ∪ (C.right ∩ D.middle))
      (C.right ∩ D.right) := by
    apply Finset.disjoint_left.2
    intro v hv hvY
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hv).2).2
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hvY).2).1
    · exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hvY).2).2
        (Finset.mem_inter.mp (Finset.mem_inter.mp hv).2).1
  have hAcard : C.right.card =
      (C.right ∩ D.left).card + (C.right ∩ D.middle).card +
        (C.right ∩ D.right).card := by
    calc
      C.right.card =
          (((C.right ∩ D.left) ∪ (C.right ∩ D.middle)) ∪
            (C.right ∩ D.right)).card := congrArg Finset.card hApartition
      _ = ((C.right ∩ D.left) ∪ (C.right ∩ D.middle)).card +
            (C.right ∩ D.right).card :=
        Finset.card_union_of_disjoint hABYdisj
      _ = _ := by rw [Finset.card_union_of_disjoint hABdisj]
  have hnonempty : (C.right ∩ D.left).Nonempty :=
    ⟨a, Finset.mem_inter.2 ⟨C.x_mem, D.a_mem⟩⟩
  have hpos : 1 ≤ (C.right ∩ D.left).card :=
    Finset.one_le_card.mpr hnonempty
  omega

private noncomputable def chosenCriticalCut
    (hmin : IsEdgeMinimallyThreeConnected G) {u v : V} (huv : G.Adj u v) :
    CriticalCut G u v :=
  Classical.choice (exists_criticalCut hmin huv)

private noncomputable def edgeRank
    (hmin : IsEdgeMinimallyThreeConnected G) (u v : V) : ℕ :=
  if huv : G.Adj u v then (chosenCriticalCut hmin huv).right.card else 0

private theorem edgeRank_decrease
    (hmin : IsEdgeMinimallyThreeConnected G)
    {x a y : V} (hxa : G.Adj x a) (hay : G.Adj a y) (hxy : x ≠ y)
    (hdegx : 4 ≤ G.degree x) (hdega : 4 ≤ G.degree a) :
    edgeRank hmin a y < edgeRank hmin x a := by
  simp only [edgeRank, dif_pos hxa, dif_pos hay]
  exact consecutive_cut_decrease hxa hay hxy hmin.isThreeConnected
    hdegx hdega (chosenCriticalCut hmin hxa) (chosenCriticalCut hmin hay)

end Mader41

/-- **Mader's Theorem 4.1, specialized to connectivity three.**
Every cycle in an edge-minimally three-connected finite graph contains a
vertex of ambient degree three. -/
theorem maderCycleProperty_of_isEdgeMinimallyThreeConnected
    (hmin : IsEdgeMinimallyThreeConnected G) : MaderCycleProperty G := by
  intro r p hp
  by_contra hex
  have hdeg (i : ℕ) : 4 ≤ G.degree (p.getVert i) := by
    have hminDeg := hmin.isThreeConnected.degree_ge (p.getVert i)
    have hne : G.degree (p.getVert i) ≠ 3 := by
      intro heq
      apply hex
      exact ⟨p.getVert i, p.getVert_mem_support i, heq⟩
    omega
  let rank : ℕ → ℕ := fun i ↦
    Mader41.edgeRank hmin (p.getVert i) (p.getVert (i + 1))
  have hstep (i : ℕ) (hi : i + 2 ≤ p.length) : rank (i + 1) < rank i := by
    have h₁ : G.Adj (p.getVert i) (p.getVert (i + 1)) :=
      p.adj_getVert_succ (by omega)
    have h₂ : G.Adj (p.getVert (i + 1)) (p.getVert (i + 2)) := by
      simpa only [Nat.add_assoc] using
        p.adj_getVert_succ (i := i + 1) (by omega)
    have hne : p.getVert i ≠ p.getVert (i + 2) := by
      have h := hp.getVert_sub_one_ne_getVert_add_one (i := i + 1) (by omega)
      simpa only [Nat.add_sub_cancel, Nat.add_assoc] using h
    exact Mader41.edgeRank_decrease hmin h₁ h₂ hne (hdeg i) (hdeg (i + 1))
  have hlen : 3 ≤ p.length := hp.three_le_length
  have hchain (k : ℕ) (hk : 1 ≤ k) (hkl : k < p.length) : rank k < rank 0 := by
    induction k with
    | zero => omega
    | succ k ih =>
        by_cases hk0 : k = 0
        · subst k
          exact hstep 0 (by omega)
        · exact lt_trans (hstep k (by omega)) (ih (by omega) (by omega))
  have hlastFirst : rank (p.length - 1) < rank 0 :=
    hchain (p.length - 1) (by omega) (by omega)
  have hclose : rank 0 < rank (p.length - 1) := by
    have hlast : G.Adj (p.getVert (p.length - 1)) (p.getVert p.length) := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ p.length)] using
        p.adj_getVert_succ (i := p.length - 1) (by omega)
    have hfirst : G.Adj (p.getVert p.length) (p.getVert 1) := by
      simpa only [Walk.getVert_length, Walk.getVert_zero] using
        p.adj_getVert_succ (i := 0) (by omega)
    have hne : p.getVert (p.length - 1) ≠ p.getVert 1 :=
      hp.snd_ne_penultimate.symm
    have h := Mader41.edgeRank_decrease hmin hlast hfirst hne
      (hdeg (p.length - 1)) (hdeg p.length)
    simpa only [rank, Nat.zero_add, Nat.sub_add_cancel (by omega : 1 ≤ p.length),
      Walk.getVert_length, Walk.getVert_zero] using h
  omega

end Erdos916
