/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CoreAHT

/-!
# The three-connected core of the AHT route

This file fixes the connectivity convention used in the Aboulker--Havet--
Trotignon route to Erdős Problem 916.  We use the standard separation-based
predicate: every proper separation has an intersection of cardinality at
least three, and the graph has more than three vertices.

The elementary consequences below are the exact hypotheses used at the start
of Section 6 of AHT: a three-connected graph has minimum degree three and
remains preconnected after deleting one or two vertices.  We also package the
stronger, source-faithful output (two vertex-disjoint degree-three false-twin
pairs) and prove that it implies the single pair needed by `CoreAHT`.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A finite vertex separation.  There are no edges between the two strict
sides, and the two sides cover all vertices. -/
structure AHTSeparation (G : SimpleGraph V) where
  left : Finset V
  right : Finset V
  cover : left ∪ right = Finset.univ
  not_adj : ∀ ⦃u v⦄, u ∈ left → u ∉ right →
    v ∈ right → v ∉ left → ¬G.Adj u v

namespace AHTSeparation

variable (s : AHTSeparation G)

/-- The vertex separator shared by the two sides. -/
def separator : Finset V := s.left ∩ s.right

/-- The order of a separation. -/
def order : ℕ := s.separator.card

/-- A separation is proper if both strict sides are nonempty. -/
def Proper : Prop :=
  (s.left \ s.right).Nonempty ∧ (s.right \ s.left).Nonempty

theorem mem_left_or_mem_right (v : V) : v ∈ s.left ∨ v ∈ s.right := by
  have h : v ∈ s.left ∪ s.right := by
    rw [s.cover]
    exact Finset.mem_univ v
  exact Finset.mem_union.mp h

/-- The separation isolating one vertex from all its non-neighbours. -/
def isolate (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    AHTSeparation G where
  left := insert v (G.neighborFinset v)
  right := Finset.univ.erase v
  cover := by
    ext x
    simp
    tauto
  not_adj := by
    intro u w huL huR hwR hwL
    have huv : u = v := by simpa using huR
    subst u
    rw [Finset.mem_insert] at hwL
    have hwn : w ∉ G.neighborFinset v := fun h => hwL (Or.inr h)
    simpa [G.mem_neighborFinset] using hwn

@[simp] theorem separator_isolate (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : (isolate G v).separator = G.neighborFinset v := by
  ext w
  by_cases hw : w = v
  · subst w
    simp [separator, isolate, G.notMem_neighborFinset_self]
  · simp [separator, isolate, hw]

@[simp] theorem order_isolate (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : (isolate G v).order = G.degree v := by
  simp [order]

theorem proper_isolate (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hcard : G.degree v + 1 < Fintype.card V) :
    (isolate G v).Proper := by
  constructor
  · exact ⟨v, by simp [isolate, G.notMem_neighborFinset_self]⟩
  · have hleft : (insert v (G.neighborFinset v)).card <
        (Finset.univ : Finset V).card := by
      simpa [G.notMem_neighborFinset_self] using hcard
    obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hleft
    exact ⟨w, by simpa [isolate] using hw⟩

/-- Add a deleted set to both sides of a separation of the induced graph on
its complement. -/
def liftDelete (S : Finset V)
    (t : AHTSeparation (G.induce {v : V | v ∉ S})) : AHTSeparation G where
  left := S ∪ t.left.image Subtype.val
  right := S ∪ t.right.image Subtype.val
  cover := by
    apply Finset.eq_univ_iff_forall.2
    intro v
    by_cases hv : v ∈ S
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
    · let w : {v : V // v ∉ S} := ⟨v, hv⟩
      rcases t.mem_left_or_mem_right w with hw | hw
      · exact Finset.mem_union_left _ <| Finset.mem_union_right _ <|
          Finset.mem_image.2 ⟨w, hw, rfl⟩
      · exact Finset.mem_union_right _ <| Finset.mem_union_right _ <|
          Finset.mem_image.2 ⟨w, hw, rfl⟩
  not_adj := by
    intro u v huL huR hvR hvL
    have huS : u ∉ S := fun hu => huR (Finset.mem_union_left _ hu)
    have hvS : v ∉ S := fun hv => hvL (Finset.mem_union_left _ hv)
    let u' : {v : V // v ∉ S} := ⟨u, huS⟩
    let v' : {v : V // v ∉ S} := ⟨v, hvS⟩
    have huLt : u' ∈ t.left := by
      rw [Finset.mem_union] at huL
      rcases huL with huL | huL
      · exact (huS huL).elim
      · obtain ⟨w, hwt, hw⟩ := Finset.mem_image.1 huL
        have hwu : w = u' := Subtype.ext hw
        simpa [hwu] using hwt
    have huRt : u' ∉ t.right := by
      intro h
      apply huR
      exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨u', h, rfl⟩)
    have hvRt : v' ∈ t.right := by
      rw [Finset.mem_union] at hvR
      rcases hvR with hvR | hvR
      · exact (hvS hvR).elim
      · obtain ⟨w, hwt, hw⟩ := Finset.mem_image.1 hvR
        have hwv : w = v' := Subtype.ext hw
        simpa [hwv] using hwt
    have hvLt : v' ∉ t.left := by
      intro h
      apply hvL
      exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨v', h, rfl⟩)
    exact fun huv => t.not_adj huLt huRt hvRt hvLt (by simpa [u', v'] using huv)

@[simp] theorem separator_liftDelete (S : Finset V)
    (t : AHTSeparation (G.induce {v : V | v ∉ S})) :
    (liftDelete S t).separator = S ∪ t.separator.image Subtype.val := by
  ext v
  by_cases hv : v ∈ S
  · simp [separator, liftDelete, hv]
  · simp only [separator, liftDelete, Finset.mem_inter, Finset.mem_union,
      Finset.mem_image, hv, false_or]
    constructor
    · rintro ⟨⟨u, huL, huv⟩, ⟨w, hwR, hwv⟩⟩
      have huw : u = w := Subtype.ext (huv.trans hwv.symm)
      subst w
      exact ⟨u, ⟨huL, hwR⟩, huv⟩
    · rintro ⟨u, hu, huv⟩
      exact ⟨⟨u, hu.1, huv⟩, ⟨u, hu.2, huv⟩⟩

theorem order_liftDelete (S : Finset V)
    (t : AHTSeparation (G.induce {v : V | v ∉ S})) :
    (liftDelete S t).order = S.card + t.order := by
  rw [order, separator_liftDelete, Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective]
    · rfl
    · exact Subtype.val_injective
  · apply Finset.disjoint_left.2
    intro v hvS hvI
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hvI
    exact w.property hvS

theorem proper_liftDelete (S : Finset V)
    (t : AHTSeparation (G.induce {v : V | v ∉ S})) (ht : t.Proper) :
    (liftDelete S t).Proper := by
  rcases ht with ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  rw [Finset.mem_sdiff] at hu hv
  rcases hu with ⟨huL, huR⟩
  rcases hv with ⟨hvR, hvL⟩
  constructor
  · refine ⟨u.1, Finset.mem_sdiff.2 ⟨?_, ?_⟩⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨u, huL, rfl⟩)
    · intro hu
      simp only [liftDelete, Finset.mem_union] at hu
      rcases hu with huS | hu
      · exact u.property huS
      · obtain ⟨w, hwt, hw⟩ := Finset.mem_image.1 hu
        have hwu : w = u := Subtype.ext hw
        exact huR (hwu ▸ hwt)
  · refine ⟨v.1, Finset.mem_sdiff.2 ⟨?_, ?_⟩⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨v, hvR, rfl⟩)
    · intro hv
      simp only [liftDelete, Finset.mem_union] at hv
      rcases hv with hvS | hv
      · exact v.property hvS
      · obtain ⟨w, hwt, hw⟩ := Finset.mem_image.1 hv
        have hwv : w = v := Subtype.ext hw
        exact hvL (hwv ▸ hwt)

/-- The separation into the vertices reachable from `u` and its complement. -/
noncomputable def reachable (G : SimpleGraph V) (u : V) : AHTSeparation G := by
  classical
  let L : Finset V := Finset.univ.filter (G.Reachable u)
  exact
    { left := L
      right := Lᶜ
      cover := Finset.union_compl L
      not_adj := by
        intro x y hxL _ hyR _ hxy
        have hux : G.Reachable u x := by simpa [L] using hxL
        have huy : ¬G.Reachable u y := by simpa [L] using hyR
        exact huy (hux.trans hxy.reachable) }

@[simp] theorem separator_reachable (G : SimpleGraph V) (u : V) :
    (reachable G u).separator = ∅ := by
  classical
  ext x
  simp [separator, reachable]

@[simp] theorem order_reachable (G : SimpleGraph V) (u : V) :
    (reachable G u).order = 0 := by
  simp [order]

theorem proper_reachable (G : SimpleGraph V) {u v : V}
    (huv : ¬G.Reachable u v) : (reachable G u).Proper := by
  classical
  constructor
  · refine ⟨u, Finset.mem_sdiff.2 ⟨?_, ?_⟩⟩ <;>
      simp [reachable, SimpleGraph.Reachable.rfl]
  · refine ⟨v, Finset.mem_sdiff.2 ⟨?_, ?_⟩⟩ <;>
      simp [reachable, huv]

end AHTSeparation

/-- Separation-based three-vertex-connectivity. -/
def IsThreeConnected (G : SimpleGraph V) : Prop :=
  3 < Fintype.card V ∧
    ∀ s : AHTSeparation G, s.Proper → 3 ≤ s.order

namespace IsThreeConnected

/-- A three-connected finite graph has at least four vertices. -/
theorem four_le_card (hG : IsThreeConnected G) :
    4 ≤ Fintype.card V := by
  exact Nat.succ_le_iff.mpr hG.1

/-- The standard minimum-degree consequence of three-connectivity. -/
theorem degree_ge (hG : IsThreeConnected G) (v : V) :
    3 ≤ G.degree v := by
  by_contra h
  have hdeg : G.degree v < 3 := Nat.lt_of_not_ge h
  have hproper : (AHTSeparation.isolate G v).Proper := by
    apply AHTSeparation.proper_isolate
    have hcard := hG.1
    omega
  have := hG.2 (AHTSeparation.isolate G v) hproper
  rw [AHTSeparation.order_isolate] at this
  exact (Nat.not_le_of_lt hdeg this).elim

/-- Deleting any set of fewer than three vertices leaves a preconnected
graph.  This is the form of vertex-connectivity used in the AHT path
arguments. -/
theorem induce_compl_preconnected (hG : IsThreeConnected G)
    (S : Finset V) (hS : S.card < 3) :
    (G.induce {v : V | v ∉ S}).Preconnected := by
  intro u v
  by_contra huv
  let t := AHTSeparation.reachable (G.induce {v : V | v ∉ S}) u
  have ht : t.Proper := AHTSeparation.proper_reachable _ huv
  have hsep := hG.2 (AHTSeparation.liftDelete S t)
    (AHTSeparation.proper_liftDelete S t ht)
  rw [AHTSeparation.order_liftDelete,
    AHTSeparation.order_reachable] at hsep
  omega

/-- In particular, deleting one vertex leaves a preconnected graph. -/
theorem delete_vertex_preconnected (hG : IsThreeConnected G) (v : V) :
    (G.induce {w : V | w ∉ ({v} : Finset V)}).Preconnected := by
  exact hG.induce_compl_preconnected ({v} : Finset V) (by simp)

/-- Deleting two distinct displayed vertices leaves a preconnected graph. -/
theorem delete_pair_preconnected (hG : IsThreeConnected G)
    {u v : V} (huv : u ≠ v) :
    (G.induce {w : V | w ∉ ({u, v} : Finset V)}).Preconnected := by
  have hcard : ({u, v} : Finset V).card < 3 := by simp [huv]
  exact hG.induce_compl_preconnected ({u, v} : Finset V) hcard

/-- The only three-connected graph on four vertices is complete, hence it
already contains the smallest wheel. -/
theorem hasWheelWitness_of_card_eq_four (hG : IsThreeConnected G)
    (hcard : Fintype.card V = 4) : HasWheelWitness G := by
  have hdeg (v : V) : G.degree v = 3 := by
    have hlo := hG.degree_ge v
    have hhi := G.degree_lt_card_verts v
    omega
  have huniv (v : V) : G.IsUniversal v := by
    rw [← G.degree_eq_card_sub_one v]
    rw [hcard]
    exact hdeg v
  have htop : G = ⊤ := G.eq_top_iff_forall_isUniversal.mpr huniv
  apply HasWheelWitness.mono (G := G) (H := ⊤)
  · rw [htop]
  · exact hasWheelWitness_top hG.four_le_card

/-- Consequently a wheel-free three-connected graph has at least five
vertices; this removes the `K₄` exceptional base case before the AHT
Watkins--Mesner analysis begins. -/
theorem five_le_card_of_noWheel (hG : IsThreeConnected G)
    (hno : ¬HasWheelWitness G) : 5 ≤ Fintype.card V := by
  have hfour := hG.four_le_card
  by_contra hfive
  have hcard : Fintype.card V = 4 := by omega
  exact hno (hG.hasWheelWitness_of_card_eq_four hcard)

end IsThreeConnected

/-! ## The cycle obstruction at a degree-three vertex -/

/-- An ambient cycle avoiding `v` and containing each of three displayed
vertices.  This is equivalent to a cycle through those vertices after
deleting `v`, but avoids subtype bookkeeping in the Watkins--Mesner layer. -/
def HasCycleAvoidingThrough (G : SimpleGraph V)
    (v a b c : V) : Prop :=
  ∃ r : V, ∃ p : G.Walk r r,
    p.IsCycle ∧ v ∉ p.support ∧
      a ∈ p.support ∧ b ∈ p.support ∧ c ∈ p.support

/-- In a wheel-free graph, no cycle avoiding a vertex can pass through three
distinct neighbours of that vertex.  This is the observation immediately
preceding the Watkins--Mesner theorem in AHT. -/
theorem not_hasCycleAvoidingThrough_of_noWheel
    (hno : ¬HasWheelWitness G) {v a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : G.Adj v a) (hb : G.Adj v b) (hc : G.Adj v c) :
    ¬HasCycleAvoidingThrough G v a b c := by
  rintro ⟨r, p, hp, hvp, hap, hbp, hcp⟩
  apply hno
  refine ⟨r, p, v, hp, hvp, ?_⟩
  have ha' : a ∈ G.neighborFinset v ∩ p.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨ha, hap⟩
  have hb' : b ∈ G.neighborFinset v ∩ p.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hb, hbp⟩
  have hc' : c ∈ G.neighborFinset v ∩ p.support.toFinset := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      List.mem_toFinset]
    exact ⟨hc, hcp⟩
  have hthree := Finset.two_lt_card_iff.mpr
    ⟨a, b, c, ha', hb', hc', hab, hac, hbc⟩
  omega

/-- A degree-three neighbourhood can be enumerated by three distinct
vertices; this is the normalized input expected by Watkins--Mesner. -/
theorem exists_three_neighbors_of_degree_eq_three {v : V}
    (hdeg : G.degree v = 3) :
    ∃ a b c : V,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        G.neighborFinset v = {a, b, c} := by
  have hcard : (G.neighborFinset v).card = 3 := by
    rw [G.card_neighborFinset_eq_degree, hdeg]
  exact Finset.card_eq_three.mp hcard

/-- Combining the preceding two lemmas gives the exact normalized obstruction
attached to every degree-three vertex of a wheel-free graph. -/
theorem degreeThree_cycle_obstruction (hno : ¬HasWheelWitness G)
    {v : V} (hdeg : G.degree v = 3) :
    ∃ a b c : V,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      G.neighborFinset v = {a, b, c} ∧
      ¬HasCycleAvoidingThrough G v a b c := by
  obtain ⟨a, b, c, hab, hac, hbc, hN⟩ :=
    exists_three_neighbors_of_degree_eq_three hdeg
  have ha : G.Adj v a := by
    rw [← SimpleGraph.mem_neighborFinset, hN]
    simp
  have hb : G.Adj v b := by
    rw [← SimpleGraph.mem_neighborFinset, hN]
    simp
  have hc : G.Adj v c := by
    rw [← SimpleGraph.mem_neighborFinset, hN]
    simp
  exact ⟨a, b, c, hab, hac, hbc, hN,
    not_hasCycleAvoidingThrough_of_noWheel hno hab hac hbc ha hb hc⟩

/-! ## The source-faithful two-pair output -/

/-- The stronger AHT Section 6 certificate: two vertex-disjoint pairs of
degree-three false twins. -/
structure TwoDisjointDegreeThreeFalseTwinPairs
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  u : V
  v : V
  x : V
  y : V
  twin_uv : AreFalseTwins G u v
  twin_xy : AreFalseTwins G x y
  degree_u : G.degree u = 3
  degree_x : G.degree x = 3
  disjoint : Disjoint ({u, v} : Finset V) ({x, y} : Finset V)

namespace TwoDisjointDegreeThreeFalseTwinPairs

variable (T : TwoDisjointDegreeThreeFalseTwinPairs G)

theorem degree_v : G.degree T.v = 3 := by
  exact T.twin_uv.degree_eq.symm.trans T.degree_u

theorem degree_y : G.degree T.y = 3 := by
  exact T.twin_xy.degree_eq.symm.trans T.degree_x

/-- The four displayed vertices in the two-pair certificate are distinct. -/
theorem pairwise_distinct :
    T.u ≠ T.v ∧ T.x ≠ T.y ∧ T.u ≠ T.x ∧ T.u ≠ T.y ∧
      T.v ≠ T.x ∧ T.v ≠ T.y := by
  have hdisj := Finset.disjoint_left.mp T.disjoint
  constructor
  · exact T.twin_uv.1
  constructor
  · exact T.twin_xy.1
  constructor
  · intro h
    exact hdisj (a := T.u) (by simp) (by simpa [h])
  constructor
  · intro h
    exact hdisj (a := T.u) (by simp) (by simpa [h])
  constructor
  · intro h
    exact hdisj (a := T.v) (by simp) (by simpa [h])
  · intro h
    exact hdisj (a := T.v) (by simp) (by simpa [h])

/-- Forgetting the second pair gives the exact single-pair conclusion needed
by the circuit argument. -/
theorem exists_degreeThree_falseTwins
    (T : TwoDisjointDegreeThreeFalseTwinPairs G) :
    ∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3 := by
  exact ⟨T.u, T.v, T.twin_uv, T.degree_u⟩

end TwoDisjointDegreeThreeFalseTwinPairs

/-- The conclusion used by the density/circuit layer. -/
def HasDegreeThreeFalseTwins
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ u v : V, AreFalseTwins G u v ∧ G.degree u = 3

/-- The stronger published two-pair conclusion implies the exact local
certificate used by `CircuitTwins`. -/
theorem hasDegreeThreeFalseTwins_of_twoDisjointPairs
    (T : TwoDisjointDegreeThreeFalseTwinPairs G) :
    HasDegreeThreeFalseTwins G := by
  exact T.exists_degreeThree_falseTwins

/-- Three-connectivity supplies the minimum-degree alternative in AHT
Theorem 1.2, so in this branch the desired global theorem reduces exactly to
the degree-three false-twin conclusion. -/
theorem no_vertex_degree_le_two_of_threeConnected
    (hG : IsThreeConnected G) :
    ¬∃ v : V, G.degree v ≤ 2 := by
  rintro ⟨v, hv⟩
  have := hG.degree_ge v
  omega

end Erdos916
