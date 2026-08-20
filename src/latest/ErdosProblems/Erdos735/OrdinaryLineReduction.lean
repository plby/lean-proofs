import ErdosProblems.Erdos735.Primal

/-!
# Ordinary-line counting reduction for Erdős 735

This scratch module is insertion-ready for `ErdosProblems/Erdos735.lean`: it imports
that file solely to reuse its concrete Euclidean-plane definitions.  The reduction is
the counting step in Ackerman--Buchin--Knauer--Pinchasi--Rote (2008), proof of their
Theorem 1: if every ordinary line passes through a fixed point `p`, then the ordinary
line graph on `P.erase p` is a matching and the ordinary line graph on `P` is a star.
Consequently

`2 * ordinaryLineCount (P.erase p) + ordinaryLineCount P ≤ (P.erase p).card`.

Combining this with the two explicit Kelly--Moser `3n/7` inequalities gives an
ordinary line avoiding `p`.  No Kelly--Moser lower bound is assumed globally or hidden
in this file; the endpoint theorem takes both numerical inequalities as hypotheses.
-/

namespace Erdos735

open scoped BigOperators

noncomputable section

def OrdinaryPair (S : Finset Point) (p q : Point) : Prop :=
  p ∈ S ∧ q ∈ S ∧ p ≠ q ∧
    ∀ r ∈ S, Collinear3 p q r → r = p ∨ r = q

def FinsetCollinear (S : Finset Point) : Prop :=
  S.card ≤ 1 ∨
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ∀ r ∈ S, Collinear3 a b r

lemma orientationDet_swap (p q r : Point) :
    orientationDet q p r = -orientationDet p q r := by
  simp [orientationDet]
  ring

lemma orientationDet_rotate (p q r : Point) :
    orientationDet q r p = orientationDet p q r := by
  exact orientationDet_cycle p q r

lemma collinear3_swap (p q r : Point) : Collinear3 q p r ↔ Collinear3 p q r := by
  unfold Collinear3
  rw [orientationDet_swap]
  constructor
  · exact neg_eq_zero.mp
  · exact neg_eq_zero.mpr

lemma collinear3_rotate (p q r : Point) : Collinear3 q r p ↔ Collinear3 p q r := by
  unfold Collinear3
  rw [orientationDet_rotate]

lemma collinear3_swap_right (p q r : Point) : Collinear3 p r q ↔ Collinear3 p q r := by
  unfold Collinear3
  have h : orientationDet p r q = -orientationDet p q r := by
    simp [orientationDet]
    ring
  rw [h]
  constructor
  · exact neg_eq_zero.mp
  · exact neg_eq_zero.mpr

lemma ordinaryPair_symm {S : Finset Point} {p q : Point} :
    OrdinaryPair S p q ↔ OrdinaryPair S q p := by
  constructor
  · rintro ⟨hp, hq, hpq, hline⟩
    refine ⟨hq, hp, hpq.symm, ?_⟩
    intro r hr hcol
    rcases hline r hr ((collinear3_swap p q r).mp hcol) with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro ⟨hq, hp, hqp, hline⟩
    refine ⟨hp, hq, hqp.symm, ?_⟩
    intro r hr hcol
    rcases hline r hr ((collinear3_swap q p r).mp hcol) with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- If `a,p,b` and `a,p,c` are collinear and `a ≠ p`, then `a,b,c` are collinear. -/
lemma collinear3_trans {a p b c : Point} (hap : a ≠ p)
    (hab : Collinear3 a p b) (hac : Collinear3 a p c) : Collinear3 a b c := by
  by_cases hab' : a = b
  · subst b
    simp [Collinear3, orientationDet]
  · have hbline : b ∈ line[ℝ, a, p] :=
      (collinear3_iff_mem_affineSpan_pair hap).mp hab
    have hcline : c ∈ line[ℝ, a, p] :=
      (collinear3_iff_mem_affineSpan_pair hap).mp hac
    have hlines : line[ℝ, a, b] = line[ℝ, a, p] :=
      affineSpan_pair_eq_of_mem_of_mem_of_ne
        (left_mem_affineSpan_pair ℝ a p) hbline hab'
    apply (collinear3_iff_mem_affineSpan_pair hab').mpr
    rwa [hlines]

@[simp] lemma collinear3_self_left (p q : Point) : Collinear3 p p q := by
  simp [Collinear3, orientationDet]

@[simp] lemma collinear3_self_right (p q : Point) : Collinear3 p q q := by
  simp only [Collinear3, orientationDet]
  ring

@[simp] lemma collinear3_right_eq_left (p q : Point) : Collinear3 p q p := by
  simp [Collinear3, orientationDet]

lemma finsetCollinear_of_card_le_two {S : Finset Point} (hcard : S.card ≤ 2) :
    FinsetCollinear S := by
  by_cases hsmall : S.card ≤ 1
  · exact Or.inl hsmall
  · have htwo : S.card = 2 := by omega
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp htwo
    right
    refine ⟨a, by simp, b, by simp, hab, ?_⟩
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl <;> simp

/-- Two distinct common points force two concrete affine lines to coincide. -/
lemma collinear3_unique_line {a b q r z : Point} (hab : a ≠ b) (hqr : q ≠ r)
    (habq : Collinear3 a b q) (habr : Collinear3 a b r)
    (hqrz : Collinear3 q r z) : Collinear3 a b z := by
  by_cases hqa : q = a
  · subst q
    have harb : Collinear3 a r b := (collinear3_swap_right a r b).mp habr
    exact collinear3_trans hqr harb hqrz
  · have haqr : Collinear3 a q r := collinear3_trans hab habq habr
    have hqra : Collinear3 q r a := (collinear3_rotate a q r).mpr haqr
    have hqaz : Collinear3 q a z := collinear3_trans hqr hqra hqrz
    have haqz : Collinear3 a q z := (collinear3_swap q a z).mpr hqaz
    have haqb : Collinear3 a q b := (collinear3_swap_right a q b).mp habq
    exact collinear3_trans (Ne.symm hqa) haqb haqz

lemma collinear3_of_on_line {a b p q r : Point} (hab : a ≠ b)
    (hp : Collinear3 a b p) (hq : Collinear3 a b q)
    (hr : Collinear3 a b r) : Collinear3 p q r := by
  by_cases hpa : p = a
  · subst p
    exact collinear3_trans hab hq hr
  · have hapq : Collinear3 a p q := collinear3_trans hab hp hq
    have hapr : Collinear3 a p r := collinear3_trans hab hp hr
    have hpaq : Collinear3 p a q := (collinear3_swap a p q).mpr hapq
    have hpar : Collinear3 p a r := (collinear3_swap a p r).mpr hapr
    exact collinear3_trans hpa hpaq hpar

/-- For a noncollinear configuration, the weak and fiber-exact near-pencil notions agree
in the direction needed by the avoiding-line reduction. -/
lemma isNearPencil_of_collinear_erase {S : Finset Point} {z : Point}
    (hz : z ∈ S) (hncol : ¬ FinsetCollinear S)
    (hQcol : FinsetCollinear (S.erase z)) : IsNearPencil S := by
  classical
  let Q := S.erase z
  have hQcard : 2 ≤ Q.card := by
    by_contra h
    have hQsmall : Q.card ≤ 1 := by omega
    apply hncol
    apply finsetCollinear_of_card_le_two
    have hcard := Finset.card_erase_add_one hz
    change Q.card + 1 = S.card at hcard
    omega
  rcases hQcol with hsmall | ⟨a, haQ, b, hbQ, hab, hline⟩
  · change Q.card ≤ 1 at hsmall
    omega
  have hznot : ¬ Collinear3 a b z := by
    intro habz
    apply hncol
    right
    refine ⟨a, Finset.mem_of_mem_erase haQ, b, Finset.mem_of_mem_erase hbQ, hab, ?_⟩
    intro r hrS
    by_cases hrz : r = z
    · simpa [hrz] using habz
    · exact hline r (Finset.mem_erase.mpr ⟨hrz, hrS⟩)
  refine ⟨z, hz, hQcard, ?_, ?_⟩
  · intro p hpQ q hqQ hpq
    ext r
    simp only [lineFiber, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hrS, hpqr⟩
      refine ⟨?_, hrS⟩
      intro hrz
      subst r
      have hpqz := hpqr
      have hpq_base : Collinear3 a b p := hline p hpQ
      have hqq_base : Collinear3 a b q := hline q hqQ
      exact hznot (collinear3_unique_line hab hpq hpq_base hqq_base
        hpqz)
    · rintro ⟨hrz, hrS⟩
      have hrQ : r ∈ Q := Finset.mem_erase.mpr ⟨hrz, hrS⟩
      exact ⟨hrS, collinear3_of_on_line hab (hline p hpQ) (hline q hqQ)
        (hline r hrQ)⟩
  · intro q hqQ
    ext r
    simp only [lineFiber, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hrS, hzqr⟩
      by_cases hrz : r = z
      · exact Or.inl hrz
      by_cases hrq : r = q
      · exact Or.inr hrq
      exfalso
      apply hznot
      exact collinear3_unique_line hab (Ne.symm hrq) (hline q hqQ)
        (hline r (Finset.mem_erase.mpr ⟨hrz, hrS⟩))
        ((collinear3_rotate z q r).mpr hzqr)
    · intro hr
      rcases hr with rfl | rfl
      · exact ⟨hz, by simp⟩
      · exact ⟨Finset.mem_of_mem_erase hqQ, by simp⟩

/-- The graph whose edges are ordinary pairs of `S`. -/
def ordinaryGraph (S : Finset Point) : SimpleGraph {x // x ∈ S} where
  Adj p q := OrdinaryPair S p.1 q.1
  symm := ⟨fun p q h ↦
    (ordinaryPair_symm (S := S) (p := p.1) (q := q.1)).mp h⟩
  loopless := ⟨fun _ h ↦ h.2.2.1 rfl⟩

lemma ordinaryGraph_adj {S : Finset Point} {p q : {x // x ∈ S}} :
    (ordinaryGraph S).Adj p q ↔ OrdinaryPair S p.1 q.1 := Iff.rfl

/-- If every ordinary line of `Q` contains an external point `p`, the ordinary-line
graph of `Q` is a matching (in the elementary degree-at-most-one sense). -/
lemma ordinaryGraph_degree_le_one {Q : Finset Point} {p : Point}
    (hp : p ∉ Q)
    (hthrough : ∀ a b, OrdinaryPair Q a b → Collinear3 a b p) :
    ∀ a : {x // x ∈ Q}, ((ordinaryGraph Q).neighborSet a).Subsingleton := by
  intro a
  intro b hab c hac
  have hab' : OrdinaryPair Q a.1 b.1 := hab
  have hac' : OrdinaryPair Q a.1 c.1 := hac
  have hpa : p ≠ a.1 := by
    intro h
    apply hp
    simpa [h] using a.2
  have hpab : Collinear3 a.1 p b.1 := by
    exact (collinear3_swap_right a.1 p b.1).mp (hthrough _ _ hab')
  have hpac : Collinear3 a.1 p c.1 := by
    exact (collinear3_swap_right a.1 p c.1).mp (hthrough _ _ hac')
  have habc : Collinear3 a.1 b.1 c.1 :=
    collinear3_trans hpa.symm hpab hpac
  rcases hab'.2.2.2 c.1 c.2 habc with hca | hcb
  · exact False.elim (hac'.2.2.1 hca.symm)
  · exact Subtype.ext hcb.symm

section Counting

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma SimpleGraph.edgeFinset_eq_incidenceFinset_of_star
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V)
    (hstar : ∀ a b, G.Adj a b → a = c ∨ b = c) :
    G.edgeFinset = G.incidenceFinset c := by
  apply Finset.Subset.antisymm
  · intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    rw [SimpleGraph.mem_incidenceFinset]
    induction e using Sym2.inductionOn with
    | _ a b =>
      change G.Adj a b at he
      rcases hstar a b he with rfl | rfl
      · exact G.mk'_mem_incidenceSet_left_iff.2 he
      · exact G.mk'_mem_incidenceSet_right_iff.2 he
  · exact G.incidenceFinset_subset c

lemma SimpleGraph.card_edgeFinset_eq_degree_of_star
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : V)
    (hstar : ∀ a b, G.Adj a b → a = c ∨ b = c) :
    G.edgeFinset.card = G.degree c := by
  rw [SimpleGraph.edgeFinset_eq_incidenceFinset_of_star G c hstar,
    SimpleGraph.card_incidenceFinset_eq_degree]

end Counting

noncomputable def ordinaryLineCount (S : Finset Point) : ℕ := by
  classical
  exact (ordinaryGraph S).edgeFinset.card

noncomputable def ordinarySupport (S : Finset Point) : Finset {x // x ∈ S} := by
  classical
  exact Finset.univ.filter fun v ↦ v ∈ (ordinaryGraph S).support

noncomputable def ordinaryPointSet (S : Finset Point) : Finset Point := by
  classical
  exact S.filter fun a ↦ ∃ b, OrdinaryPair S a b

noncomputable def ordinaryLeaves (S : Finset Point) (p : Point) : Finset Point := by
  classical
  exact (S.erase p).filter fun q ↦ OrdinaryPair S p q

lemma ordinarySupport_card_eq_ordinaryPointSet_card (S : Finset Point) :
    (ordinarySupport S).card = (ordinaryPointSet S).card := by
  classical
  apply Finset.card_bij (fun v _ ↦ v.1)
  · intro v hv
    rw [ordinaryPointSet, Finset.mem_filter]
    refine ⟨v.2, ?_⟩
    rw [ordinarySupport, Finset.mem_filter] at hv
    rcases hv.2 with ⟨w, hvw⟩
    exact ⟨w.1, hvw⟩
  · intro v hv w hw hvw
    exact Subtype.ext hvw
  · intro x hx
    rw [ordinaryPointSet, Finset.mem_filter] at hx
    rcases hx with ⟨hxS, y, hxy⟩
    let v : {x // x ∈ S} := ⟨x, hxS⟩
    let w : {x // x ∈ S} := ⟨y, hxy.2.1⟩
    refine ⟨v, ?_, rfl⟩
    rw [ordinarySupport, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, ⟨w, hxy⟩⟩

/-- In a matching graph, twice the number of edges is the number of nonisolated vertices. -/
lemma twice_ordinaryLineCount_eq_support_card {Q : Finset Point} {p : Point}
    (hp : p ∉ Q)
    (hthrough : ∀ a b, OrdinaryPair Q a b → Collinear3 a b p) :
    2 * ordinaryLineCount Q = (ordinaryPointSet Q).card := by
  classical
  let G := ordinaryGraph Q
  have hsub := ordinaryGraph_degree_le_one hp hthrough
  have hdeg : ∀ v : {x // x ∈ Q}, G.degree v = if v ∈ G.support then 1 else 0 := by
    intro v
    split_ifs with hv
    · have hvpos : 0 < G.degree v :=
        (SimpleGraph.degree_pos_iff_mem_support G v).2 hv
      have hvle : G.degree v ≤ 1 := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_le_one]
        intro a ha b hb
        exact hsub v (by simpa using ha) (by simpa using hb)
      omega
    · exact (SimpleGraph.degree_eq_zero_iff_notMem_support G v).2 hv
  have hhand := G.sum_degrees_eq_twice_card_edges
  have hsupport : (ordinarySupport Q).card = ∑ v : {x // x ∈ Q}, G.degree v := by
    rw [Finset.card_eq_sum_ones]
    simp only [ordinarySupport, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v hv
    rw [hdeg]
  rw [← ordinarySupport_card_eq_ordinaryPointSet_card, hsupport, hhand]
  simp [ordinaryLineCount, G]

lemma ordinaryLeaves_card_eq_ordinaryLineCount {S : Finset Point} {p : Point}
    (hp : p ∈ S)
    (hthrough : ∀ a b, OrdinaryPair S a b → Collinear3 a b p) :
    (ordinaryLeaves S p).card = ordinaryLineCount S := by
  classical
  let center : {x // x ∈ S} := ⟨p, hp⟩
  let G := ordinaryGraph S
  have hstar : ∀ a b, G.Adj a b → a = center ∨ b = center := by
    intro a b hab
    have hab' : OrdinaryPair S a.1 b.1 := hab
    rcases hab'.2.2.2 p hp (hthrough _ _ hab') with hpa | hpb
    · exact Or.inl (Subtype.ext hpa.symm)
    · exact Or.inr (Subtype.ext hpb.symm)
  have hedge : ordinaryLineCount S = G.degree center := by
    rw [ordinaryLineCount]
    exact SimpleGraph.card_edgeFinset_eq_degree_of_star G center hstar
  rw [hedge, ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun q hq ↦ (⟨q, (by
    rw [ordinaryLeaves, Finset.mem_filter] at hq
    exact (Finset.mem_erase.mp hq.1).2)⟩ : {x // x ∈ S}))
  · intro q hq
    rw [ordinaryLeaves, Finset.mem_filter] at hq
    rw [SimpleGraph.mem_neighborFinset]
    exact hq.2
  · intro q hq r hr hqr
    exact congrArg Subtype.val hqr
  · intro q hq
    rw [SimpleGraph.mem_neighborFinset] at hq
    have hq' : OrdinaryPair S p q.1 := hq
    have hqp : q.1 ≠ p := hq'.2.2.1.symm
    let r : {x // x ∈ ordinaryLeaves S p} := ⟨q.1, by
      rw [ordinaryLeaves, Finset.mem_filter, Finset.mem_erase]
      exact ⟨⟨hqp, q.2⟩, hq'⟩⟩
    exact ⟨r, r.2, Subtype.ext rfl⟩

lemma ordinaryPair_of_erase_of_not_collinear {S : Finset Point} {p a b : Point}
    (hab : OrdinaryPair (S.erase p) a b) (hcol : ¬ Collinear3 a b p) :
    OrdinaryPair S a b := by
  refine ⟨Finset.mem_of_mem_erase hab.1, Finset.mem_of_mem_erase hab.2.1,
    hab.2.2.1, ?_⟩
  intro r hrS hrcol
  by_cases hrp : r = p
  · exact False.elim (hcol (hrp ▸ hrcol))
  · exact hab.2.2.2 r (Finset.mem_erase.mpr ⟨hrp, hrS⟩) hrcol

/-- The numerical core of the avoiding-line argument: if all `S`-ordinary lines pass
through `p`, then the ordinary lines of `S.erase p` use disjoint pairs of the remaining
points, while the leaves of the ordinary star in `S` use none of those points. -/
lemma ordinary_count_erase_inequality {S : Finset Point} {p : Point} (hp : p ∈ S)
    (hthroughS : ∀ a b, OrdinaryPair S a b → Collinear3 a b p) :
    2 * ordinaryLineCount (S.erase p) + ordinaryLineCount S ≤ (S.erase p).card := by
  classical
  let Q := S.erase p
  have hpQ : p ∉ Q := Finset.notMem_erase p S
  have hthroughQ : ∀ a b, OrdinaryPair Q a b → Collinear3 a b p := by
    intro a b hab
    by_contra hcol
    exact hcol (hthroughS a b (ordinaryPair_of_erase_of_not_collinear hab hcol))
  have hsupportQ : ordinaryPointSet Q ⊆ Q := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hleavesQ : ordinaryLeaves S p ⊆ Q := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hdisj : Disjoint (ordinaryPointSet Q) (ordinaryLeaves S p) := by
    rw [Finset.disjoint_left]
    intro x hxOrd hxLeaf
    rcases (Finset.mem_filter.mp hxOrd).2 with ⟨y, hxy⟩
    have hleaf : OrdinaryPair S p x := (Finset.mem_filter.mp hxLeaf).2
    have hyQ : y ∈ Q := hxy.2.1
    have hpxy : Collinear3 p x y :=
      (collinear3_rotate p x y).mp (hthroughQ x y hxy)
    rcases hleaf.2.2.2 y (Finset.mem_of_mem_erase hyQ) hpxy with hyp | hyx
    · exact hpQ (hyp ▸ hyQ)
    · exact hxy.2.2.1 hyx.symm
  have hunion : ordinaryPointSet Q ∪ ordinaryLeaves S p ⊆ Q :=
    Finset.union_subset hsupportQ hleavesQ
  calc
    2 * ordinaryLineCount Q + ordinaryLineCount S =
        (ordinaryPointSet Q).card + (ordinaryLeaves S p).card := by
          rw [twice_ordinaryLineCount_eq_support_card hpQ hthroughQ,
            ordinaryLeaves_card_eq_ordinaryLineCount hp hthroughS]
    _ = (ordinaryPointSet Q ∪ ordinaryLeaves S p).card :=
      (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ Q.card := Finset.card_le_card hunion

/-- Kelly--Moser's `3n/7` estimates for `S` and `S.erase p` force an ordinary line
avoiding `p`. This theorem isolates the entirely finite counting reduction from the
geometric lower bound. -/
theorem exists_ordinaryPair_avoiding_of_kellyMoser_bounds
    {S : Finset Point} {p : Point} (hp : p ∈ S)
    (hKM_S : 3 * S.card ≤ 7 * ordinaryLineCount S)
    (hKM_erase : 3 * (S.erase p).card ≤ 7 * ordinaryLineCount (S.erase p)) :
    ∃ a b, OrdinaryPair S a b ∧ ¬ Collinear3 a b p := by
  by_contra h
  push Not at h
  have hcount := ordinary_count_erase_inequality hp h
  have hcard : S.card = (S.erase p).card + 1 :=
    (Finset.card_erase_add_one hp).symm
  rw [hcard] at hKM_S
  simp only [Nat.mul_add, Nat.mul_one] at hKM_S
  omega

end

end Erdos735
