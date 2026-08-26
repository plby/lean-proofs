import ErdosProblems.Erdos73.NoncrossingLeftRegions
import ErdosProblems.Erdos73.BrickWallRotation

/-! Right-boundary port routing by the checked half-turn of an odd-height wall. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

theorem NoncrossingPortWord.reverse {N : ℕ} {U : Type*} {label : Fin N → U}
    (h : NoncrossingPortWord label) : NoncrossingPortWord (fun i => label i.rev) := by
  intro a b c d hab hbc hcd hac hbd
  have hh := h d.rev c.rev b.rev a.rev (Fin.rev_lt_rev.mpr hcd)
    (Fin.rev_lt_rev.mpr hbc) (Fin.rev_lt_rev.mpr hab) hbd.symm hac.symm
  exact hac.trans (hh.symm.trans hbd.symm)

theorem exists_disjoint_noncrossing_right_regions {N c r : ℕ} {U : Type*}
    (label : Fin N → U) (hsurj : Function.Surjective label) (hNC : NoncrossingPortWord label)
    (nails : Fin N → ElementaryWallVertex c r)
    (hmono : StrictMono (fun i => (nails i).val.1.val))
    (hright : ∀ i, 2 * (c - 1) ≤ (nails i).val.2.val) (hc : N + 2 ≤ c) (hr : Odd r) :
    ∃ R : U → Finset (ElementaryWallVertex c r),
      Pairwise (fun u v => Disjoint (R u) (R v)) ∧
      (∀ i, nails i ∈ R (label i)) ∧
      ∀ u, ((elementaryWall c r).induce (R u : Set (ElementaryWallVertex c r))).Connected := by
  let E := brickWallRotation c r hr
  let label' (i : Fin N) := label i.rev
  let nails' (i : Fin N) := E (nails i.rev)
  have hsurj' : Function.Surjective label' := by
    intro u
    obtain ⟨i, hi⟩ := hsurj u
    exact ⟨i.rev, by simpa only [label', Fin.rev_rev] using hi⟩
  have hmono' : StrictMono (fun i => (nails' i).val.1.val) := by
    intro i j hij
    have hh := hmono (Fin.rev_lt_rev.mpr hij)
    have hi := (nails i.rev).val.1.isLt
    have hj := (nails j.rev).val.1.isLt
    dsimp only at hh
    simp only [nails', E, brickWallRotation_val, Fin.val_rev]
    omega
  have hleft' (i : Fin N) : (nails' i).val.2.val ≤ 1 := by
    have hh := hright i.rev
    simp only [nails', E, brickWallRotation_val, Fin.val_rev]
    omega
  obtain ⟨R, hdis, hports, hconn⟩ :=
    exists_disjoint_noncrossing_left_regions label' hsurj' hNC.reverse nails' hmono' hleft' hc
  refine ⟨fun u => (R u).map E.toCopy.toEmbedding, ?_, ?_, ?_⟩
  · intro u v huv
    exact (Finset.disjoint_map E.toCopy.toEmbedding).mpr (hdis huv)
  · intro i
    have hi : nails' i.rev ∈ R (label i) := by
      simpa only [label', Fin.rev_rev] using hports i.rev
    refine mem_map.mpr ⟨nails' i.rev, hi, ?_⟩
    change E (E (nails i.rev.rev)) = nails i
    rw [Fin.rev_rev]
    exact brickWallRotation_involutive hr (nails i)
  · intro u
    exact connected_induce_map_copy E.toCopy (R u) (hconn u)

end
end Erdos73
