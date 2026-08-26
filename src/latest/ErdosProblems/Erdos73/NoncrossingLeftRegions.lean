import ErdosProblems.Erdos73.LeftCombRegions
import ErdosProblems.Erdos73.NoncrossingPortBlocks

/-! Realize every noncrossing partition of ordered left-boundary nails by disjoint connected regions. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset

variable {N c r : ℕ} {U : Type*}

def portWordRows (label : Fin N → U) (nails : Fin N → ElementaryWallVertex c r) (u : U) : Finset ℕ :=
  (portWordFiber label u).image (fun i => (nails i).val.1.val)

def portWordLeftComb (label : Fin N → U) (hsurj : Function.Surjective label)
    (nails : Fin N → ElementaryWallVertex c r) (u : U) : Finset (ElementaryWallVertex c r) :=
  brickLeftComb (portWordRows label nails u) (nails (portWordFirst label hsurj u)).val.1.val
    (nails (portWordLast label hsurj u)).val.1.val (portWordSpine label hsurj u)

theorem portWordRows_bounds (label : Fin N → U) (hsurj : Function.Surjective label)
    (nails : Fin N → ElementaryWallVertex c r) (hmono : StrictMono (fun i => (nails i).val.1.val))
    (u : U) : ∀ i ∈ portWordRows label nails u,
      (nails (portWordFirst label hsurj u)).val.1.val ≤ i ∧
        i ≤ (nails (portWordLast label hsurj u)).val.1.val := by
  intro row hrow
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hrow
  have hh := portWord_bounds label hsurj ((mem_portWordFiber _ _ _).mp hi)
  exact ⟨hmono.monotone hh.1, hmono.monotone hh.2⟩

theorem portWordRows_avoids_nested {label : Fin N → U} (hsurj : Function.Surjective label)
    (hNC : NoncrossingPortWord label) (nails : Fin N → ElementaryWallVertex c r)
    (hmono : StrictMono (fun i => (nails i).val.1.val)) {u v : U} (huv : u ≠ v)
    (hlo : portWordFirst label hsurj u < portWordFirst label hsurj v) :
    ∀ i ∈ portWordRows label nails u,
      ¬ ((nails (portWordFirst label hsurj v)).val.1.val ≤ i ∧
        i ≤ (nails (portWordLast label hsurj v)).val.1.val) := by
  intro row hrow hbound
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hrow
  exact hNC.outer_block_avoids_inner huv hlo
    (portWordFirst_label label hsurj u) (portWordFirst_label label hsurj v)
    (portWordLast_label label hsurj v) ((mem_portWordFiber _ _ _).mp hi)
    ⟨hmono.le_iff_le.mp hbound.1, hmono.le_iff_le.mp hbound.2⟩

theorem portWordLeftComb_disjoint {label : Fin N → U} (hsurj : Function.Surjective label)
    (hNC : NoncrossingPortWord label) (nails : Fin N → ElementaryWallVertex c r)
    (hmono : StrictMono (fun i => (nails i).val.1.val)) :
    Pairwise (fun u v => Disjoint (portWordLeftComb label hsurj nails u)
      (portWordLeftComb label hsurj nails v)) := by
  intro u v huv
  have hh := hNC.interval_cases huv (portWordFirst_le_last label hsurj u)
    (portWordFirst_le_last label hsurj v) (portWordFirst_label label hsurj u)
    (portWordLast_label label hsurj u) (portWordFirst_label label hsurj v)
    (portWordLast_label label hsurj v)
  rcases hh with hh | hh | ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
  · exact brickLeftComb_disjoint_series (portWordRows_bounds label hsurj nails hmono u)
      (portWordRows_bounds label hsurj nails hmono v) (hmono hh)
  · exact (brickLeftComb_disjoint_series (portWordRows_bounds label hsurj nails hmono v)
      (portWordRows_bounds label hsurj nails hmono u) (hmono hh)).symm
  · exact brickLeftComb_disjoint_nested (portWordRows_bounds label hsurj nails hmono v)
      (portWordSpine_lt_of_nested label hsurj hlo hhi)
      (portWordRows_avoids_nested hsurj hNC nails hmono huv hlo)
  · exact (brickLeftComb_disjoint_nested (portWordRows_bounds label hsurj nails hmono u)
      (portWordSpine_lt_of_nested label hsurj hlo hhi)
      (portWordRows_avoids_nested hsurj hNC nails hmono (Ne.symm huv) hlo)).symm

theorem exists_connected_portWordLeft_region (label : Fin N → U)
    (hsurj : Function.Surjective label) (nails : Fin N → ElementaryWallVertex c r)
    (hmono : StrictMono (fun i => (nails i).val.1.val))
    (hleft : ∀ i, (nails i).val.2.val ≤ 1) (hc : N + 2 ≤ c) (u : U) :
    ∃ T : Finset (ElementaryWallVertex c r),
      (∀ i, label i = u → nails i ∈ T) ∧ T ⊆ portWordLeftComb label hsurj nails u ∧
      ((elementaryWall c r).induce (T : Set (ElementaryWallVertex c r))).Connected := by
  let lo := portWordFirst label hsurj u
  let hi := portWordLast label hsurj u
  let j := portWordSpine label hsurj u
  have hj : 0 < j := portWordSpine_pos label hsurj u
  have hjc : j + 1 < c := by have hh := portWordSpine_le label hsurj u; omega
  have hroot : (nails lo).val.1.val ∈ portWordRows label nails u :=
    mem_image.mpr ⟨lo, (mem_portWordFiber _ _ _).mpr (portWordFirst_label label hsurj u), rfl⟩
  have hrootcol : (nails lo).val.2.val ≤ 2 * j + 1 := by have hh := hleft lo; omega
  have hrows (i : portWordFiber label u) : (nails i.val).val.1.val ∈ portWordRows label nails u :=
    mem_image.mpr ⟨i.val, i.property, rfl⟩
  have horder (i : portWordFiber label u) : (nails lo).val.1.val ≤ (nails i.val).val.1.val :=
    hmono.monotone (portWord_bounds label hsurj ((mem_portWordFiber _ _ _).mp i.property)).1
  have hbound (i : portWordFiber label u) : (nails i.val).val.1.val ≤ (nails hi).val.1.val :=
    hmono.monotone (portWord_bounds label hsurj ((mem_portWordFiber _ _ _).mp i.property)).2
  have hcols (i : portWordFiber label u) : (nails i.val).val.2.val ≤ 2 * j + 1 := by
    have hh := hleft i.val
    omega
  obtain ⟨T, _, hports, hsub, hconn⟩ := exists_connected_leftComb_region (nails lo)
    (fun i : portWordFiber label u => nails i.val) (portWordRows label nails u)
    (nails hi).val.1.val j hj hjc hroot hrootcol hrows horder hbound hcols
  exact ⟨T, fun i hi => hports ⟨i, (mem_portWordFiber _ _ _).mpr hi⟩, hsub, hconn⟩

theorem exists_disjoint_noncrossing_left_regions (label : Fin N → U)
    (hsurj : Function.Surjective label) (hNC : NoncrossingPortWord label)
    (nails : Fin N → ElementaryWallVertex c r)
    (hmono : StrictMono (fun i => (nails i).val.1.val))
    (hleft : ∀ i, (nails i).val.2.val ≤ 1) (hc : N + 2 ≤ c) :
    ∃ R : U → Finset (ElementaryWallVertex c r),
      Pairwise (fun u v => Disjoint (R u) (R v)) ∧
      (∀ i, nails i ∈ R (label i)) ∧
      ∀ u, ((elementaryWall c r).induce (R u : Set (ElementaryWallVertex c r))).Connected := by
  choose R hports hsub hconn using exists_connected_portWordLeft_region label hsurj nails hmono hleft hc
  refine ⟨R, ?_, fun i => hports (label i) i rfl, hconn⟩
  intro u v huv
  exact (portWordLeftComb_disjoint hsurj hNC nails hmono huv).mono (hsub u) (hsub v)

end
end Erdos73
