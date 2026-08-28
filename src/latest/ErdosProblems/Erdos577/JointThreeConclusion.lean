import ErdosProblems.Erdos577.JointThreeOtherRow

/-! The exact common-triple conclusion for the three-neighbor distinguished case. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem FinalRows.three_first_labels {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 3)
    (hw : degreeIn G w v.support = 3)
    (hyrow : ∀ i : Fin 4, G.Adj y (v i) ↔ (3 : ℕ).testBit i.val = true) :
    ∃ q : Quadrilateral G, q.support = v.support ∧
      (∀ i : Fin 4, i ≠ 0 → G.Adj z (q i) ∧ G.Adj w (q i)) ∧ G.Adj y (q 2) := by
  have hwrow := three_row_of_missing v w 3 hw (h.three_other_no_last hz hw hyrow)
  refine ⟨v.rotate 3, v.rotate_support 3, ?_, (hyrow 1).mpr (by decide)⟩
  intro i hi
  fin_cases i
  · exact False.elim (hi rfl)
  · exact ⟨h.three 0 (by decide), (hwrow 0).mpr (by decide)⟩
  · exact ⟨h.three 1 (by decide), (hwrow 1).mpr (by decide)⟩
  · exact ⟨h.three 2 (by decide), (hwrow 2).mpr (by decide)⟩

theorem FinalRows.three_conclusion {v : Quadrilateral G} {x y z w : V}
    (h : FinalRows v x y z w) (hz : degreeIn G z v.support = 3)
    (hw : degreeIn G w v.support ≤ 3) :
    degreeIn G x v.support + degreeIn G y v.support +
      degreeIn G z v.support + degreeIn G w v.support = 9 ∧
      ∃ q : Quadrilateral G, q.support = v.support ∧
        (∀ i : Fin 4, i ≠ 0 → G.Adj z (q i) ∧ G.Adj w (q i)) ∧ G.Adj y (q 2) := by
  obtain ⟨_, hy, hwexact, hsum⟩ := h.three_exact_degrees hz hw
  refine ⟨hsum, ?_⟩
  rcases h.three_leaf_rows hz y (Or.inr rfl) hy with hyrow | hyrow
  · exact h.three_first_labels hz hwexact hyrow
  · have hv : (v.rotate 2).reverse.support = v.support := by
      rw [Quadrilateral.reverse_support, Quadrilateral.rotate_support]
    obtain ⟨q, hq, hrows, hyq⟩ := h.reflect_highs.three_first_labels
      (by rwa [hv]) (by rwa [hv]) (reflect_six_row v y hyrow)
    exact ⟨q, hq.trans hv, hrows, hyq⟩

variable [Fintype V]

theorem Core.three_distinguished_conclusion {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (hnine : 9 ≤ contacts G (arms p q d) j) (hpos : 1 ≤ degreeIn G p.leaf j)
    (hfirst : degreeIn G (d 2) j ≤ 3) (hsecond : degreeIn G (d 3) j ≤ 3) :
    Conclusion p q d j := by
  obtain ⟨z, w, v, hpair, hle, hv, hthree, _⟩ :=
    h.exists_opposite_pair_labels hc hcard hdeg hn hj hjq hja hnine hpos
  have huppers : degreeIn G z v.support ≤ 3 ∧ degreeIn G w v.support ≤ 3 := by
    rw [hv]
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hfirst, hsecond⟩
    · exact ⟨hsecond, hfirst⟩
  have hrows := h.final_rows hc hcard hdeg hn hloss hj hjq hja hnine hpos v hv z w hpair hthree
  have hz : degreeIn G z v.support = 3 := by
    have hfive := hrows.toPairRows.distinguished_five
    rw [← hv] at hle
    omega
  obtain ⟨hsum, v', hv', hboth, hy⟩ := hrows.three_conclusion hz huppers.2
  rw [hv] at hsum
  refine ⟨?_, v', hv'.trans hv, ?_, hy⟩
  · rw [h.arms_contacts]
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hsum
    · omega
  · intro i hi
    have hh := hboth i hi
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hh
    · exact hh.symm

end Erdos577.JointFinal
