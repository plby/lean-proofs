import ErdosProblems.Erdos73.RegularSubwalls
import ErdosProblems.Erdos73.SubdivisionSupports

/-! Disjoint regular wall boxes yield odd-cycle packings or a bipartite induced subwall support. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset

theorem exists_bipartite_region_of_no_packing {V : Type*} [Fintype V] {G : SimpleGraph V}
    {p : ℕ} (R : Fin p → Finset V) (hdis : Pairwise (fun i j => Disjoint (R i) (R j)))
    (hno : ¬ HasOddCyclePacking p G) : ∃ i, (G.induce (R i : Set V)).IsBipartite := by
  by_contra hnone
  push Not at hnone
  exact hno (DisjointNonbipartiteRegions.hasOddCyclePacking ⟨R, fun _ _ h => hdis h, hnone⟩)

def columnBlockWallCopy (c r : ℕ) {C R p : ℕ} (hC : p * c ≤ C) (hr : r ≤ R) (i : Fin p) :
    (elementaryWall c r).Copy (elementaryWall C R) :=
  elementaryWallCopyOfOffsets 0 (i.val * c) (by omega) (by
    have hh := Nat.mul_le_mul_right c (show i.val + 1 ≤ p by omega)
    rw [Nat.add_mul, Nat.one_mul] at hh
    omega)

theorem columnBlockWallCopy_disjoint (c r : ℕ) {C R p : ℕ}
    (hC : p * c ≤ C) (hr : r ≤ R) :
    Pairwise (fun i j : Fin p => Disjoint
      (Finset.univ.image (columnBlockWallCopy c r hC hr i))
      (Finset.univ.image (columnBlockWallCopy c r hC hr j))) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hvi
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hvj
  have he := congrArg (fun w : ElementaryWallVertex C R => w.val.2.val) (hx.trans hy.symm)
  change 2 * (i.val * c) + x.val.2.val = 2 * (j.val * c) + y.val.2.val at he
  have hxlt := x.val.2.isLt
  have hylt := y.val.2.isLt
  have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
  rcases lt_or_gt_of_ne hne with hi | hj
  · have hh := Nat.mul_le_mul_right c (show i.val + 1 ≤ j.val by omega)
    rw [Nat.add_mul, Nat.one_mul] at hh
    omega
  · have hh := Nat.mul_le_mul_right c (show j.val + 1 ≤ i.val by omega)
    rw [Nat.add_mul, Nat.one_mul] at hh
    omega

theorem exists_bipartite_columnBlock_subdivision {V : Type*} [Fintype V] {G : SimpleGraph V}
    {c r C R p : ℕ} (S : GraphSubdivisionModel (elementaryWall C R) G)
    (hC : p * c ≤ C) (hr : r ≤ R) (hno : ¬ HasOddCyclePacking p G) :
    ∃ i : Fin p,
      (G.induce ((S.restrictCopy (columnBlockWallCopy c r hC hr i)).vertexSet : Set V)).IsBipartite := by
  apply exists_bipartite_region_of_no_packing
    (fun i => (S.restrictCopy (columnBlockWallCopy c r hC hr i)).vertexSet) ?_ hno
  intro i j hij
  exact S.restrictCopy_vertexSet_disjoint _ _ (columnBlockWallCopy_disjoint c r hC hr hij)

end
end Erdos73
