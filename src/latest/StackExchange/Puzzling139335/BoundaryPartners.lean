import StackExchange.Puzzling139335.JordanRegion
import StackExchange.Puzzling139335.WeightedMass.Family

/-!
# Local partners on a finite tiling boundary

Away from triple contacts, a boundary point of a finite closed tiling has
exactly one partner piece.  The two frontiers agree in a neighborhood there.
The statements are formulated for a tiling of the whole plane, so they also
apply after adjoining the closed exterior of the square.
-/

open Set Metric

namespace Puzzling139335

variable {ι : Type*} [Finite ι]

/-- A boundary point in a finite closed cover belongs to another member. -/
theorem boundary_mem_another_of_closed_cover (P : ι → Set Plane)
    (hclosed : ∀ i, IsClosed (P i)) (hcover : (⋃ i, P i) = univ)
    {i : ι} {x : Plane} (hx : x ∈ frontier (P i)) :
    ∃ j, j ≠ i ∧ x ∈ P j := by
  exact exists_other_piece_at_frontier P hclosed hcover (by simp) hx

/-- Off triple contacts, all other pieces are absent from a neighborhood. -/
theorem pair_neighborhood_of_not_tripleContact (P : ι → Set Plane)
    (hclosed : ∀ i, IsClosed (P i)) {i j : ι} (hij : i ≠ j)
    {x : Plane} (hi : x ∈ P i) (hj : x ∈ P j) (hnot : x ∉ tripleContactSet P) :
    ∃ r > 0, ∀ k, k ≠ i → k ≠ j → Disjoint (ball x r) (P k) := by
  classical
  let U : Set Plane := ⋂ k, if k = i ∨ k = j then univ else (P k)ᶜ
  have hopen : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro k
    split_ifs
    · exact isOpen_univ
    · exact (hclosed k).isOpen_compl
  have hxU : x ∈ U := by
    apply mem_iInter.mpr
    intro k
    split_ifs with hk
    · trivial
    · intro hxk
      exact hnot ⟨i, j, k, hij, fun h => hk (Or.inl h.symm),
        fun h => hk (Or.inr h.symm), hi, hj, hxk⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hxU)
  refine ⟨r, hr, ?_⟩
  intro k hki hkj
  apply Set.disjoint_left.mpr
  intro y hy hyk
  have hynot : y ∉ P k := by
    simpa only [if_neg (not_or.mpr ⟨hki, hkj⟩), mem_compl_iff]
      using mem_iInter.mp (hball hy) k
  exact hynot hyk

/-- At a non-junction boundary point the two pieces fill a neighborhood and
their frontiers agree there.  In particular the partner label is locally constant. -/
theorem boundary_partner_neighborhood (P : ι → Set Plane)
    (hclosed : ∀ i, IsClosed (P i))
    (hregular : ∀ i, closure (interior (P i)) = P i)
    (hdis : Pairwise fun i j => Disjoint (interior (P i)) (interior (P j)))
    (hcover : (⋃ i, P i) = univ) {i : ι} {x : Plane}
    (hx : x ∈ frontier (P i)) (hnot : x ∉ tripleContactSet P) :
    ∃ j, j ≠ i ∧ ∃ r > 0,
      ball x r ⊆ P i ∪ P j ∧
      ball x r ∩ frontier (P i) = ball x r ∩ frontier (P j) ∧
      ∀ k, k ≠ i → k ≠ j → Disjoint (ball x r) (P k) := by
  classical
  obtain ⟨j, hji, hxj⟩ := boundary_mem_another_of_closed_cover P hclosed hcover hx
  have hxi : x ∈ P i := (hclosed i).closure_eq ▸ hx.1
  obtain ⟨r, hr, hothers⟩ :=
    pair_neighborhood_of_not_tripleContact P hclosed hji.symm hxi hxj hnot
  have hpair : ball x r ⊆ P i ∪ P j := by
    intro y hy
    have hycover : y ∈ ⋃ k, P k := by rw [hcover]; trivial
    obtain ⟨k, hk⟩ := mem_iUnion.mp hycover
    by_cases hki : k = i
    · exact Or.inl (hki ▸ hk)
    by_cases hkj : k = j
    · exact Or.inr (hkj ▸ hk)
    exact False.elim (Set.disjoint_left.mp (hothers k hki hkj) hy hk)
  have hIP {a b : ι} (hab : a ≠ b) : Disjoint (interior (P a)) (P b) := by
    exact disjoint_interior_piece_of_regular P hregular hdis hab
  have hfront (a b : ι) (hab : a ≠ b)
      (hother : ∀ k, k ≠ a → k ≠ b → Disjoint (ball x r) (P k))
      {y : Plane} (hyball : y ∈ ball x r) (hya : y ∈ frontier (P a)) :
      y ∈ frontier (P b) := by
    obtain ⟨k, hka, hyk⟩ := boundary_mem_another_of_closed_cover P hclosed hcover hya
    have hkb : k = b := by
      by_contra hkb
      exact Set.disjoint_left.mp (hother k hka hkb) hyball hyk
    have hyb : y ∈ P b := hkb ▸ hyk
    rw [(hclosed b).frontier_eq]
    refine ⟨hyb, ?_⟩
    intro hybint
    exact Set.disjoint_left.mp (hIP hab.symm) hybint ((hclosed a).closure_eq ▸ hya.1)
  refine ⟨j, hji, r, hr, hpair, ?_, hothers⟩
  apply Subset.antisymm
  · intro y hy
    exact ⟨hy.1, hfront i j hji.symm hothers hy.1 hy.2⟩
  · intro y hy
    exact ⟨hy.1, hfront j i hji (fun k hkj hki => hothers k hki hkj) hy.1 hy.2⟩

end Puzzling139335
