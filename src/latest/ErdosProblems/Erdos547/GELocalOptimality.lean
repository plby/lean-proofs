import ErdosProblems.Erdos547.GESupport
import ErdosProblems.Erdos547.FractionalTransfer

/-!
# Local optimality of a fractional GE matching

A deficient singleton cannot reach an over-saturated singleton by an
alternating two-edge path. The proof transfers a strictly positive amount
of weight and compares every term of the saturation sum.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
theorem edgeIncrement_zero_of_not_relation (R : V → V → Prop) {a b u v : V}
    (hab : R a b) (hba : R b a) (huv : ¬ R u v) (t : ℝ) : edgeIncrement a b t u v = 0 := by
  classical
  rw [edgeIncrement]
  apply if_neg
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact huv hab
  · exact huv hba

namespace GallaiEdmondsPartition

def IsMaxSaturation (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V)
    (μ : FractionalMatching G) : Prop := D.IsFractionalGE μ ∧
  ∀ ν : FractionalMatching G, D.IsFractionalGE ν → w.saturation ν.load c ≤ w.saturation μ.load c

theorem IsFractionalGE.transfer_singletons {D : GallaiEdmondsPartition G}
    {μ : FractionalMatching G} (h : D.IsFractionalGE μ) {x y z : V}
    (hxs : x ∈ D.singletonVertices) (hzs : z ∈ D.singletonVertices) (hy : y ∈ D.separator)
    (hxy : G.Adj x y) (hzy : G.Adj z y) (hxz : x ≠ z) (t : ℝ)
    (ht : 0 ≤ t) (he : t ≤ μ.weight z y) (hx : μ.load x + t ≤ 1) :
    D.IsFractionalGE (μ.transfer hxy hzy hxz t ht he hx) := by
  classical
  constructor
  · intro u hu
    have hux : u ≠ x := by
      intro heq
      subst u
      rcases Finset.mem_union.mp hu with hu | hu
      · exact D.singleton_not_separator hxs hu
      · exact D.singleton_not_nontrivial hxs hu
    have huz : u ≠ z := by
      intro heq
      subst u
      rcases Finset.mem_union.mp hu with hu | hu
      · exact D.singleton_not_separator hzs hu
      · exact D.singleton_not_nontrivial hzs hu
    rw [FractionalMatching.transfer_load, if_neg hux, if_neg huz, add_zero, sub_zero]
    exact h.1 u hu
  · intro u v hnot
    have hxyA : D.Allowed x y := Or.inr (Or.inr ⟨hy, hxs⟩)
    have hzyA : D.Allowed z y := Or.inr (Or.inr ⟨hy, hzs⟩)
    change μ.weight u v + edgeIncrement x y t u v - edgeIncrement z y t u v = 0
    rw [h.2 u v hnot,
      edgeIncrement_zero_of_not_relation D.Allowed hxyA (D.allowed_symm hxyA) hnot t,
      edgeIncrement_zero_of_not_relation D.Allowed hzyA (D.allowed_symm hzyA) hnot t]
    ring

theorem IsMaxSaturation.singleton_partner_le {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) {x y z : V}
    (hxs : x ∈ D.singletonVertices) (hzs : z ∈ D.singletonVertices)
    (hdef : μ.load x < w.weight c x) (hxy : G.Adj x y)
    (hpos : 0 < μ.weight y z) : μ.load z ≤ w.weight c z := by
  classical
  by_contra hnot
  have hexcess : w.weight c z < μ.load z := lt_of_not_ge hnot
  have hxz : x ≠ z := by
    intro heq
    rw [heq] at hdef
    linarith
  have hzy : G.Adj z y := by
    by_contra hn
    have hz : μ.weight y z = 0 := μ.supported y z (fun hyz ↦ hn hyz.symm)
    rw [hz] at hpos
    exact (lt_irrefl 0) hpos
  have hy := D.neighbour_of_singleton_mem_separator hxs hxy
  let t := min (μ.weight z y) (min (w.weight c x - μ.load x) (μ.load z - w.weight c z))
  have ht : 0 < t := lt_min (by simpa only [μ.symmetric z y] using hpos)
    (lt_min (sub_pos.mpr hdef) (sub_pos.mpr hexcess))
  have he : t ≤ μ.weight z y := min_le_left _ _
  have htx : t ≤ w.weight c x - μ.load x := (min_le_right _ _).trans (min_le_left _ _)
  have htz : t ≤ μ.load z - w.weight c z := (min_le_right _ _).trans (min_le_right _ _)
  have hx : μ.load x + t ≤ 1 := by linarith [w.at_most_one c x]
  let ν := μ.transfer hxy hzy hxz t ht.le he hx
  have hν : D.IsFractionalGE ν := h.1.transfer_singletons hxs hzs hy hxy hzy hxz t ht.le he hx
  have hxload : ν.load x = μ.load x + t := by
    simp [ν, FractionalMatching.transfer_load, hxz]
  have hzload : ν.load z = μ.load z - t := by
    simp [ν, FractionalMatching.transfer_load, hxz.symm]
  have heq_other (u : V) (hux : u ≠ x) (huz : u ≠ z) : ν.load u = μ.load u := by
    simp [ν, FractionalMatching.transfer_load, hux, huz]
  have hstrict : min (w.weight c x) (μ.load x) < min (w.weight c x) (ν.load x) := by
    rw [hxload, min_eq_right hdef.le, min_eq_right (by linarith)]
    linarith
  have hle (u : V) : min (w.weight c u) (μ.load u) ≤ min (w.weight c u) (ν.load u) := by
    by_cases hux : u = x
    · simpa only [hux] using hstrict.le
    · by_cases huz : u = z
      · subst u
        rw [hzload, min_eq_left hexcess.le, min_eq_left (by linarith)]
      · rw [heq_other u hux huz]
  have hsum : w.saturation μ.load c < w.saturation ν.load c :=
    Finset.sum_lt_sum (fun u _ ↦ hle u) ⟨x, Finset.mem_univ x, hstrict⟩
  exact (not_lt_of_ge (h.2 ν hν)) hsum

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsMaxSaturation.singleton_partner_le
