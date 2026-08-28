import ErdosProblems.Erdos577.WeightedThirteenMissedScore
import ErdosProblems.Erdos577.WeightedThirteenCommonScore
import ErdosProblems.Erdos577.ThreeColumnCounts

/-! A nonuniversal three-contact low row forces the third-block weighted sum below thirteen. -/

namespace Erdos577.WeightedThirteen

open Finset ThirdModel

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem nonuniversal_weight_le_twelve {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hd : Disjoint p.support q.support) (h : WeightedPawBlock.Pattern13 p q)
    {a : Finset V} (ha : a ∈ c.blocks) (hab : a ≠ b) (v : Quadrilateral G) (hv : v.support = a)
    (hdis : Disjoint (p.support ∪ q.support) v.support)
    (hcl : G.IsNClique 4 v.support) (hrows : DenseRows p q v)
    {t : Finset V} (ht : t ∈ c.blocks) (htb : t ≠ b) (hta : t ≠ a)
    (w : Quadrilateral G) (hw : w.support = t)
    (hdt : Disjoint ((p.support ∪ q.support) ∪ v.support) w.support)
    (hdiag : G.Adj (q 0) (q 2)) (second : Bool)
    (hrow : ∀ j : Fin 4, G.Adj (q (lowIndex second)) (w j) ↔ j ≠ 3)
    (hwdiag : ¬G.Adj (w 1) (w 3)) : denseWeight p q v t ≤ 12 := by
  have hmiss := no_missed_contact hc hcard hdeg hn p hp hb q hq hd h ha hab v hv hdis hcl hrows
    ht htb hta w hw hdt hdiag second hrow hwdiag
  have hx : ¬G.Adj p.leaf (w 3) := fun he ↦ hmiss 0 he.symm
  have hv1 : ¬G.Adj (v 1) (w 3) := fun he ↦ hmiss 1 he.symm
  have hv2 : ¬G.Adj (v 2) (w 3) := fun he ↦ hmiss 2 he.symm
  have hother : ¬G.Adj (q (lowIndex (!second))) (w 3) := by
    have hh := hmiss 3
    cases second <;> exact fun he ↦ hh he.symm
  have hchosen : ¬G.Adj (q (lowIndex second)) (w 3) := fun he ↦ (hrow 3).mp he rfl
  have hout : q (lowIndex second) ∉ w.support := by
    intro hz
    exact disjoint_left.mp hdt
      (mem_union_left _ (mem_union_right _ ((q.mem_support _).mpr ⟨lowIndex second, rfl⟩))) hz
  have hrep := w.three_contact_replace (q (lowIndex second)) hout hrow 1 (Or.inl rfl)
  have hmid (newSecond : Bool) :
      ¬(G.Adj p.leaf (w 1) ∧ G.Adj (v (if newSecond then 2 else 1)) (w 1)) := by
    intro hh
    have hno : ¬CommonReplacement G p.leaf (v (if newSecond then 2 else 1))
        (q (lowIndex second)) t := by
      cases second <;> cases newSecond
      · exact no_dense_common hcard hn p hp hb q hq hd h ha v hv hdis hcl hrows ht htb hta 11
      · exact no_dense_common hcard hn p hp hb q hq hd h ha v hv hdis hcl hrows ht htb hta 12
      · exact no_dense_common hcard hn p hp hb q hq hd h ha v hv hdis hcl hrows ht htb hta 7
      · exact no_dense_common hcard hn p hp hb q hq hd h ha v hv hdis hcl hrows ht htb hta 8
    apply hno
    refine ⟨w 1, hw ▸ (w.mem_support _).mpr ⟨1, rfl⟩, hh.1, hh.2, ?_⟩
    simpa only [hw] using hrep
  have hhigh := no_high_common hc p hp hb q hq hd h ha hab v hv hdis hcl hrows
    ht htb hta w hw hdt hdiag second hrow hwdiag
  have hcommon (newSecond : Bool) (u : V) (hu : u ∈ w.support) :
      ¬(G.Adj p.leaf u ∧ G.Adj (v (if newSecond then 2 else 1)) u) := by
    obtain ⟨i, rfl⟩ := (w.mem_support u).mp hu
    cases newSecond <;> fin_cases i
    · exact fun he ↦ hhigh 0 ⟨he.1.symm, he.2.symm⟩
    · exact hmid false
    · exact fun he ↦ hhigh 2 ⟨he.1.symm, he.2.symm⟩
    · exact fun he ↦ hx he.1
    · exact fun he ↦ hhigh 1 ⟨he.1.symm, he.2.symm⟩
    · exact hmid true
    · exact fun he ↦ hhigh 3 ⟨he.1.symm, he.2.symm⟩
    · exact fun he ↦ hx he.1
  have hfirst := w.missed_disjoint_row_sum p.leaf (v 1) 3 hx hv1 (hcommon false)
  have hsecond := w.missed_disjoint_row_sum p.leaf (v 2) 3 hx hv2 (hcommon true)
  have hlow := w.degree_le_three_of_nonadjacent (q (lowIndex second)) 3 hchosen
  have hlow' := w.degree_le_three_of_nonadjacent (q (lowIndex (!second))) 3 hother
  rw [hw] at hfirst hsecond hlow hlow'
  unfold denseWeight
  cases second
  · change degreeIn G (q 1) t ≤ 3 at hlow
    change degreeIn G (q 3) t ≤ 3 at hlow'
    omega
  · change degreeIn G (q 3) t ≤ 3 at hlow
    change degreeIn G (q 1) t ≤ 3 at hlow'
    omega

end Erdos577.WeightedThirteen
