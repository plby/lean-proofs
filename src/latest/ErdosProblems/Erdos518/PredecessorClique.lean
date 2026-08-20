/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Setup

/-!
# The predecessor clique of a longest path

This file isolates the local rotation observation used in Chen--Chen's Lemma 3.3.  A vertex
outside a globally longest blue path cannot be inserted by a two-chord rotation.  Consequently,
the predecessors of all its blue neighbours, together with the final vertex of the path, form a
red clique.  We also keep exact list and cardinality statements for this predecessor construction.
-/

open scoped SimpleGraph List

namespace Erdos518

universe u

variable {V : Type u}

/-- The consecutive `(predecessor, successor)` pairs of `P` whose successor is joined to `y`
in the complement colour. -/
def bluePredecessorPairs (G : SimpleGraph V) [DecidableRel Gᶜ.Adj]
    (P : List V) (y : V) : List (V × V) :=
  P.consecutivePairs.filter fun e ↦ decide (Gᶜ.Adj y e.2)

/-- The predecessors on `P` of the complement-colour neighbours of `y`.  The order is their
order along `P`. -/
def bluePredecessors (G : SimpleGraph V) [DecidableRel Gᶜ.Adj]
    (P : List V) (y : V) : List V :=
  (bluePredecessorPairs G P y).map Prod.fst

/-- Complement-colour neighbours of `y` which lie on `P`. -/
def blueNeighborsOnPath (G : SimpleGraph V) [DecidableEq V] [DecidableRel Gᶜ.Adj]
    (P : List V) (y : V) : Finset V :=
  P.toFinset.filter fun x ↦ Gᶜ.Adj y x

/-- The complement-colour degree of `y` into the vertex set of `P`. -/
def blueDegreeOnPath (G : SimpleGraph V) [DecidableEq V] [DecidableRel Gᶜ.Adj]
    (P : List V) (y : V) : ℕ :=
  (blueNeighborsOnPath G P y).card

/-- A convenient decomposition characterization of consecutive pairs. -/
lemma mem_consecutivePairs_iff {a b : V} {P : List V} :
    (a, b) ∈ P.consecutivePairs ↔ ∃ A R : List V, P = A ++ a :: b :: R := by
  induction P with
  | nil => simp
  | cons x tail ih =>
    cases tail with
    | nil =>
        simp only [List.consecutivePairs, List.tail_cons, List.tail_nil, List.zip_nil_right,
          List.not_mem_nil, false_iff, not_exists]
        intro A R h
        have hlen := congrArg List.length h
        simp at hlen
        omega
    | cons z P =>
      simp only [List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.mem_cons]
      constructor
      · rintro (h | h)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          exact ⟨[], P, by simp⟩
        · change (a, b) ∈ (z :: P).consecutivePairs at h
          obtain ⟨A, R, hP⟩ := ih.mp h
          exact ⟨x :: A, R, by simp [hP]⟩
      · rintro ⟨A, R, hA⟩
        cases A with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at hA
            exact Or.inl (Prod.ext hA.1.symm hA.2.1.symm)
        | cons w A =>
            simp only [List.cons_append, List.cons.injEq] at hA
            right
            change (a, b) ∈ (z :: P).consecutivePairs
            exact ih.mpr ⟨A, R, hA.2⟩

@[simp] lemma map_fst_consecutivePairs (P : List V) :
    P.consecutivePairs.map Prod.fst = P.dropLast := by
  induction P using List.twoStepInduction with
  | nil => simp [List.consecutivePairs]
  | singleton x => simp [List.consecutivePairs]
  | cons_cons x y P _ ih =>
      simp only [List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.map_cons,
        List.dropLast_cons_cons]
      simpa only [List.consecutivePairs, List.tail_cons] using congrArg (x :: ·) (ih y)

@[simp] lemma map_snd_consecutivePairs (P : List V) :
    P.consecutivePairs.map Prod.snd = P.tail := by
  exact List.map_snd_zip (by simp)

lemma bluePredecessors_sublist_dropLast
    (G : SimpleGraph V) [DecidableRel Gᶜ.Adj] (P : List V) (y : V) :
    bluePredecessors G P y <+ P.dropLast := by
  rw [← map_fst_consecutivePairs P]
  exact List.filter_sublist.map Prod.fst

lemma bluePredecessors_nodup
    (G : SimpleGraph V) [DecidableRel Gᶜ.Adj] {P : List V} (y : V)
    (hP : P.Nodup) : (bluePredecessors G P y).Nodup := by
  have hdrop : P.dropLast.Nodup :=
    List.Nodup.sublist P.dropLast_prefix.sublist hP
  exact List.Nodup.sublist (bluePredecessors_sublist_dropLast G P y) hdrop

lemma mem_bluePredecessors_iff
    (G : SimpleGraph V) [DecidableRel Gᶜ.Adj] {P : List V} {y a : V} :
    a ∈ bluePredecessors G P y ↔
      ∃ b : V, ∃ A R : List V, P = A ++ a :: b :: R ∧ Gᶜ.Adj y b := by
  simp only [bluePredecessors, List.mem_map, bluePredecessorPairs, List.mem_filter]
  constructor
  · rintro ⟨e, ⟨he, hblue⟩, hea⟩
    obtain ⟨a', b⟩ := e
    simp only [Prod.fst] at hea
    subst a'
    obtain ⟨A, R, hP⟩ := mem_consecutivePairs_iff.mp he
    exact ⟨b, A, R, hP, of_decide_eq_true hblue⟩
  · rintro ⟨b, A, R, hP, hblue⟩
    exact ⟨(a, b), ⟨mem_consecutivePairs_iff.mpr ⟨A, R, hP⟩,
      decide_eq_true hblue⟩, rfl⟩

/-- The explicit two-chord insertion used in the clique proof.  It reverses the block between
`a` and `c`, inserts `y`, and therefore contains every old vertex plus `y`. -/
lemma rotation_extension_isPath
    {H : SimpleGraph V} {A L R : List V} {a c d y : V}
    (hP : IsPath H (A ++ a :: L ++ c :: d :: R))
    (hy : y ∉ A ++ a :: L ++ c :: d :: R)
    (hac : H.Adj a c)
    (hay : H.Adj ((L ++ [c]).head (by simp)) y)
    (hyd : H.Adj y d) :
    IsPath H (A ++ a :: c :: L.reverse ++ y :: d :: R) := by
  have hperm : List.Perm
      (A ++ a :: c :: L.reverse ++ y :: d :: R)
      (y :: (A ++ a :: L ++ c :: d :: R)) := by
    have hrev : List.Perm L.reverse L := List.reverse_perm L
    have hmove : List.Perm (c :: L) (L ++ [c]) :=
      (List.perm_append_singleton c L).symm
    calc
      A ++ a :: c :: L.reverse ++ y :: d :: R ~
          A ++ a :: c :: L ++ y :: d :: R := by
            simpa only [List.append_assoc, List.cons_append] using
              ((hrev.append_right (y :: d :: R)).cons c |>.cons a |>.append_left A)
      _ ~ A ++ a :: L ++ c :: y :: d :: R := by
            simpa only [List.append_assoc, List.cons_append, List.singleton_append,
              List.nil_append] using
              ((hmove.append_right (y :: d :: R)).cons a |>.append_left A)
      _ ~ y :: (A ++ a :: L ++ c :: d :: R) := by
            simpa only [List.append_assoc, List.cons_append, List.singleton_append,
              List.nil_append] using
              (List.perm_middle (a := y)
                (l₁ := A ++ a :: L ++ [c]) (l₂ := d :: R))
  refine ⟨?_, (hperm.nodup_iff.mpr ?_), ?_⟩
  · simp
  · exact hP.2.1.cons hy
  · have hchain := hP.2.2
    cases L with
    | nil =>
        simpa [List.isChain_append] using
          show (A ++ a :: c :: y :: d :: R).IsChain H.Adj from by
            simp_all [List.isChain_append]
    | cons l L =>
        simp only [List.cons_append, List.head_cons] at hay
        have hmidInfix : (l :: L ++ [c]) <:+: (A ++ a :: l :: L ++ c :: d :: R) := by
          refine ⟨A ++ [a], d :: R, ?_⟩
          simp [List.append_assoc]
        have hmid : (l :: L ++ [c]).IsChain H.Adj := hP.2.2.infix hmidInfix
        have hmidRev : (l :: L ++ [c]).reverse.IsChain H.Adj := by
          rw [List.isChain_reverse]
          exact hmid.imp fun _ _ h ↦ h.symm
        rw [List.reverse_cons]
        simp only [List.append_assoc, List.cons_append]
        simp_all [List.isChain_append]

/-- The endpoint version of the rotation insertion.  A chord from `a` to the last vertex
reverses the nonempty suffix, after which `y` can be appended at its old first vertex. -/
lemma endpoint_rotation_extension_isPath
    {H : SimpleGraph V} {A R : List V} {a b y : V}
    (hP : IsPath H (A ++ a :: b :: R))
    (hy : y ∉ A ++ a :: b :: R)
    (halast : H.Adj a ((b :: R).getLast (by simp)))
    (hby : H.Adj b y) :
    IsPath H (A ++ a :: (b :: R).reverse ++ [y]) := by
  have hperm :
      A ++ a :: (b :: R).reverse ++ [y] ~ y :: (A ++ a :: b :: R) := by
    calc
      A ++ a :: (b :: R).reverse ++ [y] ~ A ++ a :: b :: R ++ [y] := by
        simpa only [List.append_assoc, List.cons_append] using
          ((List.reverse_perm (b :: R)).append_right [y] |>.cons a |>.append_left A)
      _ ~ y :: (A ++ a :: b :: R) := by
        simpa only [List.append_assoc, List.cons_append] using
          List.perm_append_singleton y (A ++ a :: b :: R)
  refine ⟨by simp, hperm.nodup_iff.mpr (hP.2.1.cons hy), ?_⟩
  have hsufInfix : (b :: R) <:+: (A ++ a :: b :: R) := by
    exact ⟨A ++ [a], [], by simp [List.append_assoc]⟩
  have hsuf : (b :: R).IsChain H.Adj := hP.2.2.infix hsufInfix
  have hsufRev : (b :: R).reverse.IsChain H.Adj := by
    rw [List.isChain_reverse]
    exact hsuf.imp fun _ _ h ↦ h.symm
  have hcore : (a :: (b :: R).reverse).IsChain H.Adj := by
    rw [List.isChain_cons]
    constructor
    · intro z hz
      have hz' : z = (b :: R).getLast (by simp) := by
        have hzmem : z ∈ (b :: R).getLast? := by
          simpa only [List.head?_reverse] using hz
        exact (List.getLast_of_mem_getLast? hzmem).symm
      rw [hz']
      exact halast
    · exact hsufRev
  have hpreInfix : (A ++ [a]) <+: (A ++ a :: b :: R) := by
    exact ⟨b :: R, by simp⟩
  have hpre : (A ++ [a]).IsChain H.Adj := hP.2.2.prefix hpreInfix
  simp_all [List.isChain_append]

/-- A vertex outside a globally longest complement-colour path cannot be adjacent in the
complement colour to its first vertex: that would simply extend the path. -/
lemma not_compl_adj_head_of_globally_longest
    {G : SimpleGraph V} {P : List V} (hP : IsPath Gᶜ P)
    (hlong : IsGloballyLongestMonoPath G P) {y : V} (hy : y ∉ P) :
    ¬ Gᶜ.Adj y (P.head hP.1) := by
  cases P with
  | nil => exact (hP.1 rfl).elim
  | cons x P =>
      intro hyx
      have hq : IsPath Gᶜ (y :: x :: P) := by
        refine ⟨by simp, ?_, ?_⟩
        · simpa using hP.2.1.cons hy
        · exact List.IsChain.cons_cons hyx hP.2.2
      have hlen := hlong.2 (y :: x :: P) (Or.inr hq)
      simp at hlen

/-- Two predecessors of complement-colour neighbours of `y`, in their path order, must be
adjacent in `G`; otherwise the explicit two-chord rotation inserts `y` into a longer blue path. -/
lemma adj_ordered_blue_predecessors_of_globally_longest
    {G : SimpleGraph V} {A L R : List V} {a c d y : V}
    (hP : IsPath Gᶜ (A ++ a :: L ++ c :: d :: R))
    (hlong : IsGloballyLongestMonoPath G (A ++ a :: L ++ c :: d :: R))
    (hy : y ∉ A ++ a :: L ++ c :: d :: R)
    (hay : Gᶜ.Adj y ((L ++ [c]).head (by simp)))
    (hyd : Gᶜ.Adj y d) :
    G.Adj a c := by
  have hacne : a ≠ c := by
    have hdis : List.Disjoint (A ++ [a]) (L ++ c :: d :: R) := by
      apply List.disjoint_of_nodup_append
      simpa only [List.append_assoc, List.singleton_append, List.cons_append,
        List.nil_append] using hP.2.1
    intro hac
    subst c
    have haLeft : a ∈ A ++ [a] := by simp
    have haRight : a ∈ L ++ a :: d :: R := by simp
    exact hdis haLeft haRight
  by_contra hac
  have hacBlue : Gᶜ.Adj a c := by
    simpa only [SimpleGraph.compl_adj] using ⟨hacne, hac⟩
  have hq := rotation_extension_isPath hP hy hacBlue hay.symm hyd
  have hlen := hlong.2 (A ++ a :: c :: L.reverse ++ y :: d :: R) (Or.inr hq)
  simp only [List.length_append, List.length_cons, List.length_reverse] at hlen
  omega

/-- The last vertex of the longest path is adjacent in `G` to each predecessor of a blue
neighbour of `y`.  A blue chord to that predecessor gives the endpoint rotation insertion. -/
lemma adj_last_blue_predecessor_of_globally_longest
    {G : SimpleGraph V} {A R : List V} {a b y : V}
    (hP : IsPath Gᶜ (A ++ a :: b :: R))
    (hlong : IsGloballyLongestMonoPath G (A ++ a :: b :: R))
    (hy : y ∉ A ++ a :: b :: R) (hyb : Gᶜ.Adj y b) :
    G.Adj ((b :: R).getLast (by simp)) a := by
  have halastne : a ≠ (b :: R).getLast (by simp) := by
    have hdis : List.Disjoint (A ++ [a]) (b :: R) := by
      apply List.disjoint_of_nodup_append
      simpa only [List.append_assoc, List.singleton_append, List.cons_append,
        List.nil_append] using hP.2.1
    intro ha
    have haLeft : a ∈ A ++ [a] := by simp
    have haRight : a ∈ b :: R := by
      rw [ha]
      exact List.getLast_mem (l := b :: R) (by simp)
    exact hdis haLeft haRight
  by_contra hred
  have hblue : Gᶜ.Adj a ((b :: R).getLast (by simp)) := by
    simpa only [SimpleGraph.compl_adj] using
      ⟨halastne, fun h ↦ hred h.symm⟩
  have hq := endpoint_rotation_extension_isPath hP hy hblue hyb.symm
  have hlen := hlong.2 (A ++ a :: (b :: R).reverse ++ [y]) (Or.inr hq)
  simp only [List.length_append, List.length_cons, List.length_reverse] at hlen
  omega

/-- Two distinct consecutive-pair occurrences in a list have a definite order.  In the first
alternative, `a` occurs before `c` and the head of the intervening nonempty-by-construction block
is exactly `b`; the second alternative is symmetric. -/
lemma order_two_consecutivePair_decompositions
    {P A B R S : List V} {a b c d : V}
    (hA : P = A ++ a :: b :: R) (hB : P = B ++ c :: d :: S) (hac : a ≠ c) :
    (∃ L : List V, P = A ++ a :: L ++ c :: d :: S ∧
      (L ++ [c]).head (by simp) = b) ∨
    (∃ L : List V, P = B ++ c :: L ++ a :: b :: R ∧
      (L ++ [a]).head (by simp) = d) := by
  have hAprefix : A ++ [a] <+: P := by
    exact ⟨b :: R, by simpa [List.append_assoc] using hA.symm⟩
  have hBprefix : B ++ [c] <+: P := by
    exact ⟨d :: S, by simpa [List.append_assoc] using hB.symm⟩
  have hApre : A <+: P := A.prefix_append (a :: b :: R) |>.trans (by simpa [hA])
  have hBpre : B <+: P := B.prefix_append (c :: d :: S) |>.trans (by simpa [hB])
  rcases lt_trichotomy A.length B.length with hlt | heq | hgt
  · left
    have hsmall : (A ++ [a]).length ≤ B.length := by simp; omega
    have hprefix : A ++ [a] <+: B :=
      List.prefix_of_prefix_length_le hAprefix hBpre hsmall
    obtain ⟨L, hBL⟩ := hprefix
    have hcombined : P = A ++ a :: L ++ c :: d :: S := by
      rw [hB, ← hBL]
      simp only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append]
    have htail : b :: R = L ++ c :: d :: S := by
      apply List.append_cancel_left (as := A ++ [a])
      simpa only [List.append_assoc, List.singleton_append, List.cons_append,
        List.nil_append] using
        hA.symm.trans hcombined
    refine ⟨L, hcombined, ?_⟩
    cases L <;> simp_all
  · have hprefixEq : A ++ [a] = B ++ [c] := by
      have hAB : A ++ [a] <+: B ++ [c] :=
        List.prefix_of_prefix_length_le hAprefix hBprefix (by simp [heq])
      exact hAB.eq_of_length (by simp [heq])
    have : a = c := by
      have hlast := congrArg List.getLast? hprefixEq
      simpa using hlast
    exact (hac this).elim
  · right
    have hsmall : (B ++ [c]).length ≤ A.length := by simp; omega
    have hprefix : B ++ [c] <+: A :=
      List.prefix_of_prefix_length_le hBprefix hApre hsmall
    obtain ⟨L, hAL⟩ := hprefix
    have hcombined : P = B ++ c :: L ++ a :: b :: R := by
      rw [hA, ← hAL]
      simp only [List.append_assoc, List.singleton_append, List.cons_append,
        List.nil_append]
    have htail : d :: S = L ++ a :: b :: R := by
      apply List.append_cancel_left (as := B ++ [c])
      simpa only [List.append_assoc, List.singleton_append, List.cons_append,
        List.nil_append] using
        hB.symm.trans hcombined
    refine ⟨L, hcombined, ?_⟩
    cases L <;> simp_all

/-- Distinct entries of the predecessor list are adjacent in `G`. -/
lemma adj_of_mem_bluePredecessors
    {G : SimpleGraph V} [DecidableRel Gᶜ.Adj] {P : List V} {y a c : V}
    (hP : IsPath Gᶜ P) (hlong : IsGloballyLongestMonoPath G P) (hy : y ∉ P)
    (ha : a ∈ bluePredecessors G P y) (hc : c ∈ bluePredecessors G P y)
    (hac : a ≠ c) :
    G.Adj a c := by
  obtain ⟨b, A, R, hA, hyb⟩ := (mem_bluePredecessors_iff G).mp ha
  obtain ⟨d, B, S, hB, hyd⟩ := (mem_bluePredecessors_iff G).mp hc
  rcases order_two_consecutivePair_decompositions hA hB hac with
    ⟨L, horder, hhead⟩ | ⟨L, horder, hhead⟩
  · have hP' := hP
    have hlong' := hlong
    have hy' := hy
    rw [horder] at hP' hlong' hy'
    apply adj_ordered_blue_predecessors_of_globally_longest hP' hlong' hy'
    · simpa only [hhead] using hyb
    · exact hyd
  · have hP' := hP
    have hlong' := hlong
    have hy' := hy
    rw [horder] at hP' hlong' hy'
    exact (adj_ordered_blue_predecessors_of_globally_longest hP' hlong' hy'
      (by simpa only [hhead] using hyd) hyb).symm

/-- The final vertex of `P` is adjacent in `G` to every entry of the predecessor list. -/
lemma adj_getLast_of_mem_bluePredecessors
    {G : SimpleGraph V} [DecidableRel Gᶜ.Adj] {P : List V} {y a : V}
    (hP : IsPath Gᶜ P) (hlong : IsGloballyLongestMonoPath G P) (hy : y ∉ P)
    (ha : a ∈ bluePredecessors G P y) :
    G.Adj (P.getLast hP.1) a := by
  obtain ⟨b, A, R, hA, hyb⟩ := (mem_bluePredecessors_iff G).mp ha
  have hP' := hP
  have hlong' := hlong
  have hy' := hy
  rw [hA] at hP' hlong' hy'
  have hadj := adj_last_blue_predecessor_of_globally_longest hP' hlong' hy' hyb
  have hlast : P.getLast hP.1 = (b :: R).getLast (by simp) := by
    have hopt := congrArg List.getLast? hA
    rw [List.getLast?_eq_some_getLast hP.1,
      List.getLast?_eq_some_getLast (l := A ++ a :: b :: R) (by simp)] at hopt
    have hallast : (A ++ a :: b :: R).getLast (by simp) =
        (b :: R).getLast (by simp) := by
      simpa only [List.append_assoc, List.singleton_append, List.cons_append,
        List.nil_append] using
        List.getLast_append_of_ne_nil (l := A ++ [a]) (l' := b :: R)
          (by simp) (by simp)
    exact Option.some.inj hopt |>.trans hallast
  rw [hlast]
  exact hadj

/-- The last vertex of `P` together with all predecessors of blue neighbours of `y`. -/
def predecessorClique (G : SimpleGraph V) [DecidableEq V] [DecidableRel Gᶜ.Adj]
    (P : List V) (hP : P ≠ []) (y : V) : Finset V :=
  insert (P.getLast hP) (bluePredecessors G P y).toFinset

/-- Every vertex of the predecessor clique lies on the original path. -/
theorem predecessorClique_subset_toFinset
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel Gᶜ.Adj]
    (P : List V) (hP : P ≠ []) (y : V) :
    predecessorClique G P hP y ⊆ P.toFinset := by
  intro x hx
  simp only [predecessorClique, Finset.mem_insert, List.mem_toFinset] at hx ⊢
  rcases hx with rfl | hx
  · exact List.getLast_mem (l := P) hP
  · exact P.dropLast_prefix.subset
      ((bluePredecessors_sublist_dropLast G P y).subset hx)

/-- **Chen's predecessor-clique rotation observation.**  If `P` is a globally longest
monochromatic path and is blue (a path of `Gᶜ`), then for every outside vertex `y`, its blue
predecessors on `P`, together with the last vertex of `P`, form a clique in `G`. -/
theorem predecessorClique_isClique
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel Gᶜ.Adj]
    {P : List V} (hP : IsPath Gᶜ P) (hlong : IsGloballyLongestMonoPath G P)
    {y : V} (hy : y ∉ P) :
    G.IsClique (predecessorClique G P hP.1 y : Set V) := by
  intro a ha c hc hac
  simp only [predecessorClique, Finset.mem_coe, Finset.mem_insert,
    List.mem_toFinset] at ha hc
  rcases ha with rfl | ha
  · rcases hc with hc | hc
    · exact (hac hc.symm).elim
    · exact adj_getLast_of_mem_bluePredecessors hP hlong hy hc
  · rcases hc with rfl | hc
    · exact (adj_getLast_of_mem_bluePredecessors hP hlong hy ha).symm
    · exact adj_of_mem_bluePredecessors hP hlong hy ha hc hac

/-- Projecting the filtered consecutive pairs to their successors gives exactly the filtered
tail of `P`. -/
lemma map_snd_bluePredecessorPairs
    (G : SimpleGraph V) [DecidableRel Gᶜ.Adj] (P : List V) (y : V) :
    (bluePredecessorPairs G P y).map Prod.snd =
      P.tail.filter fun x ↦ decide (Gᶜ.Adj y x) := by
  unfold bluePredecessorPairs
  calc
    (P.consecutivePairs.filter fun e ↦ decide (Gᶜ.Adj y e.2)).map Prod.snd =
        (P.consecutivePairs.map Prod.snd).filter fun x ↦ decide (Gᶜ.Adj y x) := by
      simpa only [Function.comp_def] using
        (List.filter_map (f := Prod.snd)
          (p := fun x : V ↦ decide (Gᶜ.Adj y x)) (l := P.consecutivePairs)).symm
    _ = _ := by rw [map_snd_consecutivePairs]

/-- The predecessor list has one entry for every blue neighbour in the tail of `P`. -/
lemma bluePredecessors_length_eq_filter_tail
    (G : SimpleGraph V) [DecidableRel Gᶜ.Adj] (P : List V) (y : V) :
    (bluePredecessors G P y).length =
      (P.tail.filter fun x ↦ decide (Gᶜ.Adj y x)).length := by
  have h := congrArg List.length (map_snd_bluePredecessorPairs G P y)
  simpa only [bluePredecessors, List.length_map] using h

/-- For an outside vertex of a globally longest path, the predecessor-list length equals its
blue degree into the whole path.  The only possible discrepancy is the first vertex, and a blue
edge there would extend `P`. -/
lemma bluePredecessors_length_eq_blueDegree
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel Gᶜ.Adj]
    {P : List V} (hP : IsPath Gᶜ P) (hlong : IsGloballyLongestMonoPath G P)
    {y : V} (hy : y ∉ P) :
    (bluePredecessors G P y).length = blueDegreeOnPath G P y := by
  have hhead := not_compl_adj_head_of_globally_longest hP hlong hy
  have hfin : blueNeighborsOnPath G P y =
      (P.filter fun x ↦ decide (Gᶜ.Adj y x)).toFinset := by
    ext x
    simp [blueNeighborsOnPath]
  rw [bluePredecessors_length_eq_filter_tail, blueDegreeOnPath, hfin,
    List.toFinset_card_of_nodup (hP.2.1.filter _)]
  cases P with
  | nil => exact (hP.1 rfl).elim
  | cons x P =>
      simp only [List.head_cons] at hhead
      have hfalse : decide (Gᶜ.Adj y x) = false := decide_eq_false hhead
      simpa only [List.tail_cons, List.filter_cons, hfalse, Bool.false_eq_true, ↓reduceIte]

/-- Injectivity of the predecessor construction, expressed as an exact finite-set cardinality. -/
lemma bluePredecessors_toFinset_card
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel Gᶜ.Adj]
    {P : List V} (y : V) (hP : P.Nodup) :
    (bluePredecessors G P y).toFinset.card = (bluePredecessors G P y).length := by
  exact List.toFinset_card_of_nodup (bluePredecessors_nodup G y hP)

/-- The last vertex of a duplicate-free nonempty path is not a predecessor; all predecessors
belong to `P.dropLast`. -/
lemma getLast_not_mem_bluePredecessors
    (G : SimpleGraph V) [DecidableRel Gᶜ.Adj]
    {P : List V} (y : V) (hPne : P ≠ []) (hP : P.Nodup) :
    P.getLast hPne ∉ bluePredecessors G P y := by
  intro hmem
  have hdrop : P.getLast hPne ∈ P.dropLast :=
    bluePredecessors_sublist_dropLast G P y |>.subset hmem
  have hn : (P.dropLast ++ [P.getLast hPne]).Nodup := by
    simpa only [List.dropLast_append_getLast hPne] using hP
  have hdis := List.disjoint_of_nodup_append hn
  exact hdis hdrop (by simp)

/-- Exact size of Chen's predecessor clique: blue degree into `P`, plus the disjoint last
vertex. -/
theorem predecessorClique_card_eq_blueDegree_add_one
    {G : SimpleGraph V} [DecidableEq V] [DecidableRel Gᶜ.Adj]
    {P : List V} (hP : IsPath Gᶜ P) (hlong : IsGloballyLongestMonoPath G P)
    {y : V} (hy : y ∉ P) :
    (predecessorClique G P hP.1 y).card = blueDegreeOnPath G P y + 1 := by
  have hlast : P.getLast hP.1 ∉ (bluePredecessors G P y).toFinset := by
    simpa only [List.mem_toFinset] using
      getLast_not_mem_bluePredecessors G y hP.1 hP.2.1
  rw [predecessorClique, Finset.card_insert_of_notMem hlast,
    bluePredecessors_toFinset_card G y hP.2.1,
    bluePredecessors_length_eq_blueDegree hP hlong hy]

end Erdos518
