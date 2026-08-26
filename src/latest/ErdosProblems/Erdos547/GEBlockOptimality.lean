import ErdosProblems.Erdos547.GELocalOptimality
import ErdosProblems.Erdos547.GEBlockRepair

/-!
# A deficient singleton cannot reach a matched nontrivial block in two steps

After moving weight onto the deficient singleton, a convex replacement of
the internal block matching restores every load in that block. Only the
singleton's load increases, contradicting saturation maximality.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace GallaiEdmondsPartition

theorem IsMaxSaturation.partner_is_singleton {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) {x y z : V}
    (hxs : x ∈ D.singletonVertices) (hdef : μ.load x < w.weight c x)
    (hxy : G.Adj x y) (hpos : 0 < μ.weight y z) : z ∈ D.singletonVertices := by
  classical
  by_contra hzs
  have hy := D.neighbour_of_singleton_mem_separator hxs hxy
  have hallowed := h.1.allowed_of_pos hpos
  have hym : D.matching.Adj y z := (D.allowed_from_separator hy hallowed).resolve_right hzs
  have hzsep : z ∉ D.separator := by
    intro hz
    exact D.not_allowed_separator hy hz hallowed
  have hzbig : z ∈ D.nontrivialVertices :=
    ((D.vertex_classes z).resolve_left hzsep).resolve_left hzs
  obtain ⟨C, hC, hzC⟩ := Finset.mem_biUnion.mp hzbig
  obtain ⟨hC, hlarge⟩ := Finset.mem_filter.mp hC
  have hxC : x ∉ C := fun hx ↦ D.singleton_not_nontrivial hxs
    (D.nontrivial_of_mem_block hC hlarge hx)
  have hyC := D.matching_neighbour_outside_block hC hzC hym.symm
  have hxz : x ≠ z := fun hxz ↦ hxC (hxz ▸ hzC)
  have hzy : G.Adj z y := hym.symm.adj_sub
  have hl : 0 < μ.weight z y := by simpa only [μ.symmetric z y] using hpos
  let t := min (μ.weight z y) (w.weight c x - μ.load x)
  have ht : 0 < t := lt_min hl (sub_pos.mpr hdef)
  have he : t ≤ μ.weight z y := min_le_left _ _
  have htx : t ≤ w.weight c x - μ.load x := min_le_right _ _
  have hxcap : μ.load x + t ≤ 1 := by linarith [w.at_most_one c x]
  let T := μ.transfer hxy hzy hxz t ht.le he hxcap
  let I := μ.inside (C : Set V)
  obtain ⟨P, hP, hPloadout, hPweightout⟩ := D.exists_perfect_fractional_on_block hC hlarge
  have hgap (u : V) : P.load u - I.load u = if u = z then μ.weight z y else 0 :=
    h.1.block_load_gap hC hlarge hzC hym.symm P hP hPloadout u
  have hI : ∀ u v, I.weight u v ≤ T.weight u v := by
    intro u v
    by_cases hu : u ∈ C
    · by_cases hv : v ∈ C
      · have hexy : edgeIncrement x y t u v = 0 := by
          rw [edgeIncrement]
          apply if_neg
          rintro (⟨_, hvy⟩ | ⟨huy, _⟩)
          · exact hyC (hvy ▸ hv)
          · exact hyC (huy ▸ hu)
        have hezy : edgeIncrement z y t u v = 0 := by
          rw [edgeIncrement]
          apply if_neg
          rintro (⟨_, hvy⟩ | ⟨huy, _⟩)
          · exact hyC (hvy ▸ hv)
          · exact hyC (huy ▸ hu)
        change (μ.inside (C : Set V)).weight u v ≤
          μ.weight u v + edgeIncrement x y t u v - edgeIncrement z y t u v
        rw [μ.inside_weight_of_mem hu hv, hexy, hezy, add_zero, sub_zero]
      · have hz : I.weight u v = 0 := μ.inside_weight_of_notMem (Or.inr hv)
        rw [hz]
        exact T.nonnegative u v
    · have hz : I.weight u v = 0 := μ.inside_weight_of_notMem (Or.inl hu)
      rw [hz]
      exact T.nonnegative u v
  have hα : 0 ≤ t / μ.weight z y := div_nonneg ht.le hl.le
  have hαone : t / μ.weight z y ≤ 1 := (div_le_one hl).mpr he
  have hcancel : (t / μ.weight z y) * μ.weight z y = t := div_mul_cancel₀ _ hl.ne'
  have hTcap : T.load z + (t / μ.weight z y) * μ.weight z y ≤ 1 := by
    simp only [T, FractionalMatching.transfer_load, if_neg hxz.symm, ite_true,
      add_zero, hcancel]
    linarith [μ.load_le_one z]
  obtain ⟨ξ, hξload, hξweight⟩ := T.exists_single_load_repair I P hI z
    (μ.weight z y) (t / μ.weight z y) hα hαone hgap hTcap
  have hload (u : V) : ξ.load u = μ.load u + if u = x then t else 0 := by
    rw [hξload, hcancel]
    change (μ.transfer hxy hzy hxz t ht.le he hxcap).load u + _ = _
    rw [FractionalMatching.transfer_load]
    by_cases hux : u = x <;> by_cases huz : u = z <;> simp [hux, huz]
  have hξ : D.IsFractionalGE ξ := by
    constructor
    · intro u hu
      have hux : u ≠ x := by
        intro heq
        subst u
        rcases Finset.mem_union.mp hu with hu | hu
        · exact D.singleton_not_separator hxs hu
        · exact D.singleton_not_nontrivial hxs hu
      rw [hload, if_neg hux, add_zero]
      exact h.1.1 u hu
    · intro u v hnot
      have hμ : μ.weight u v = 0 := h.1.2 u v hnot
      have hIz : I.weight u v = 0 := le_antisymm
        (by have hi := μ.inside_weight_le (C : Set V) u v; simpa only [hμ] using hi)
        (I.nonnegative u v)
      have hPz : P.weight u v = 0 := by
        apply hPweightout
        by_cases hu : u ∈ C
        · right
          intro hv
          exact hnot (Or.inl (Or.inr ⟨C, hC, hlarge, hu, hv⟩))
        · exact Or.inl hu
      have hxyA : D.Allowed x y := Or.inr (Or.inr ⟨hy, hxs⟩)
      have hzyA : D.Allowed z y := Or.inl (Or.inl hym.symm)
      have hTz : T.weight u v = 0 := by
        change μ.weight u v + edgeIncrement x y t u v - edgeIncrement z y t u v = 0
        rw [hμ, edgeIncrement_zero_of_not_relation D.Allowed hxyA (D.allowed_symm hxyA) hnot t,
          edgeIncrement_zero_of_not_relation D.Allowed hzyA (D.allowed_symm hzyA) hnot t]
        ring
      rw [hξweight, hTz, hIz, hPz]
      ring
  have hstrict : min (w.weight c x) (μ.load x) < min (w.weight c x) (ξ.load x) := by
    rw [hload]
    simp only [ite_true]
    rw [min_eq_right hdef.le, min_eq_right (by linarith)]
    linarith
  have hle (u : V) : min (w.weight c u) (μ.load u) ≤ min (w.weight c u) (ξ.load u) := by
    rw [hload]
    apply min_le_min_left
    split_ifs <;> linarith
  have hsum : w.saturation μ.load c < w.saturation ξ.load c :=
    Finset.sum_lt_sum (fun u _ ↦ hle u) ⟨x, Finset.mem_univ x, hstrict⟩
  exact (not_lt_of_ge (h.2 ξ hξ)) hsum

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsMaxSaturation.partner_is_singleton
