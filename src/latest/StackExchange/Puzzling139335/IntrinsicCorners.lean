import StackExchange.Puzzling139335.Basic
import StackExchange.Puzzling139335.CornerIncidence
import StackExchange.Puzzling139335.CornerSupport

/-!
# Intrinsic square-corner types

Choose one actual congruence from piece zero to each piece. Pulling the
occupied square corners back along those congruences gives a finite set of
points of the prototype. The supporting-corner theorem bounds this set by
four, without any assumption about the number of corners of the boundary.
-/

open Set

namespace Puzzling139335

namespace SquareDissection

noncomputable section

/-- A chosen Euclidean placement of the prototype into each piece. -/
def placement (d : SquareDissection) (i : Fin 4) : Plane ≃ᵃⁱ[ℝ] Plane :=
  Classical.choose (d.congruent 0 i)

theorem placement_image (d : SquareDissection) (i : Fin 4) :
    d.placement i '' d.piece 0 = d.piece i :=
  Classical.choose_spec (d.congruent 0 i)

/-- The prototype point used at a specified physical square corner. -/
def intrinsicCorner (d : SquareDissection) (i j : Fin 4) : Plane :=
  (d.placement i).symm (corner j)

@[simp] theorem placement_intrinsicCorner (d : SquareDissection) (i j : Fin 4) :
    d.placement i (d.intrinsicCorner i j) = corner j :=
  (d.placement i).apply_symm_apply _

theorem intrinsicCorner_mem_iff (d : SquareDissection) (i j : Fin 4) :
    d.intrinsicCorner i j ∈ d.piece 0 ↔ corner j ∈ d.piece i := by
  rw [← d.placement_image i]
  constructor
  · intro h
    exact ⟨d.intrinsicCorner i j, h, d.placement_intrinsicCorner i j⟩
  · rintro ⟨p, hp, heq⟩
    have hpeq : p = d.intrinsicCorner i j := by
      apply (d.placement i).injective
      simpa using heq
    exact hpeq ▸ hp

theorem intrinsicCorner_injective (d : SquareDissection) (i : Fin 4) :
    Function.Injective (d.intrinsicCorner i) :=
  (d.placement i).symm.injective.comp corner_injective

open scoped Classical in
/-- The actual square-corner incidences, before identifying prototype points. -/
def cornerOccurrences (d : SquareDissection) : Finset (Fin 4 × Fin 4) :=
  Finset.univ.filter fun q => corner q.2 ∈ d.piece q.1

@[simp] theorem mem_cornerOccurrences (d : SquareDissection) (q : Fin 4 × Fin 4) :
    q ∈ d.cornerOccurrences ↔ corner q.2 ∈ d.piece q.1 := by
  classical
  simp [cornerOccurrences]

open scoped Classical in
/-- All intrinsic points that occur at square corners in the four placements. -/
def usedCornerTypes (d : SquareDissection) : Finset Plane :=
  d.cornerOccurrences.image fun q => d.intrinsicCorner q.1 q.2

theorem mem_usedCornerTypes (d : SquareDissection) {v : Plane} :
    v ∈ d.usedCornerTypes ↔
      ∃ i j : Fin 4, corner j ∈ d.piece i ∧ d.intrinsicCorner i j = v := by
  classical
  simp only [usedCornerTypes, Finset.mem_image, mem_cornerOccurrences]
  constructor
  · rintro ⟨⟨i, j⟩, hi, hv⟩
    exact ⟨i, j, hi, hv⟩
  · rintro ⟨i, j, hi, hv⟩
    exact ⟨(i, j), hi, hv⟩

theorem usedCornerTypes_nonempty (d : SquareDissection) :
    d.usedCornerTypes.Nonempty := by
  obtain ⟨i, hi⟩ := d.exists_piece_mem (corner_mem_unitSquare 0)
  exact ⟨d.intrinsicCorner i 0, d.mem_usedCornerTypes.mpr ⟨i, 0, hi, rfl⟩⟩

theorem usedCornerTypes_subset (d : SquareDissection) :
    (d.usedCornerTypes : Set Plane) ⊆ d.piece 0 := by
  intro v hv
  obtain ⟨i, j, hj, rfl⟩ := d.mem_usedCornerTypes.mp hv
  exact (d.intrinsicCorner_mem_iff i j).mpr hj

theorem isSupportCorner_of_mem_usedCornerTypes (d : SquareDissection)
    {v : Plane} (hv : v ∈ d.usedCornerTypes) : IsSupportCorner (d.piece 0) v := by
  obtain ⟨i, j, hj, rfl⟩ := d.mem_usedCornerTypes.mp hv
  apply isSupportCorner_preimage (d.placement i)
  · rw [d.placement_image]
    exact d.piece_subset i
  · rwa [d.placement_image]

/-- There are at most four intrinsic corner types in an arbitrary Jordan
dissection. No protected-center or polygonality assumption is needed. -/
theorem usedCornerTypes_card_le_four (d : SquareDissection) :
    d.usedCornerTypes.card ≤ 4 :=
  CornerSupport.card_le_four d.usedCornerTypes
    (fun _ hv => d.isSupportCorner_of_mem_usedCornerTypes hv)

/-- The actual congruence between two chosen placements. -/
def relativePlacement (d : SquareDissection) (i k : Fin 4) :
    Plane ≃ᵃⁱ[ℝ] Plane :=
  (d.placement i).symm.trans (d.placement k)

theorem relativePlacement_image (d : SquareDissection) (i k : Fin 4) :
    d.relativePlacement i k '' d.piece i = d.piece k := by
  rw [← d.placement_image i, ← d.placement_image k, Set.image_image]
  congr 1
  funext p
  simp [relativePlacement]

theorem relativePlacement_corner (d : SquareDissection) {i j k l : Fin 4}
    (h : d.intrinsicCorner i j = d.intrinsicCorner k l) :
    d.relativePlacement i k (corner j) = corner l := by
  change d.placement k (d.intrinsicCorner i j) = corner l
  rw [h, d.placement_intrinsicCorner]

end

end SquareDissection

end Puzzling139335
