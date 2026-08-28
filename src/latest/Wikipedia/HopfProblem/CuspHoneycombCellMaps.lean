import Wikipedia.HopfProblem.CuspHoneycombCellCoordinates
import Wikipedia.HopfProblem.CuspHoneycombPositiveCells
import Wikipedia.HopfProblem.CuspHoneycombCellIncidence
import Wikipedia.HopfProblem.CuspHoneycombCellCompatibility

/-!
# The compatible maps on all actual honeycomb cells

The central cell map is propagated by integral translations in the plane
and by the genuine positive-twist action on the central fibre. Its exact
opposite-edge equation proves agreement on every intersection. The maps
preserve membership in all other cells, so their point identifications
are exactly those of the original planar cells.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycomb

open ToricSpace ToricFan ToricComponent CuspPositiveRetraction
open CuspHoneycombHexagon CuspHoneycombTiling CuspHoneycombPositive

local notation "Lattice" => CuspHoneycombTiling.Lattice
local notation "Plane" => CuspHoneycombTiling.Plane

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ)

/-- The actual central cell homeomorphism propagated to every lattice cell. -/
def cellHomeomorph (v : Lattice) : cell v ≃ₜ positiveCell v :=
  (cellTranslationHomeomorph v).symm.trans
    ((compatibleCellHomeomorph C₀).trans (positiveE0CellHomeomorph C₀ v))

@[simp] theorem cellHomeomorph_coe (v : Lattice) (x : cell v) :
    ((cellHomeomorph C₀ v x).1.1 : Space) =
      twistedTranslate (CuspPositive.positiveTwist C₀) (-cuspVector v)
        ((compatibleCellHomeomorph C₀ ((cellTranslationHomeomorph v).symm x)).1 : Space) := rfl

/-- Membership in every other actual component is exactly planar cell
membership, including vertices belonging to three cells. -/
theorem cellHomeomorph_mem_positiveCell_iff (v w : Lattice) (x : cell v) :
    (cellHomeomorph C₀ v x : PositiveCentralFibre) ∈ positiveCell w ↔
      (x : Plane) ∈ cell w := by
  change ((cellHomeomorph C₀ v x).1.1 : Space) ∈ rayDivisor w ↔ _
  rw [cellHomeomorph_coe, twistedTranslate_mem_rayDivisor, cuspVector_neg,
    cuspVector_cuspVector, neg_neg, compatibleCellHomeomorph_mem_rayDivisor_iff]
  change (x : Plane) - latticePoint v ∈ cell (w - v) ↔ _
  rw [sub_latticePoint_mem_cell_iff]
  have he : v + (w - v) = w := by abel
  rw [he]

/-- The two cell definitions agree on every literal overlap. -/
theorem cellHomeomorph_compatible (v w : Lattice) (x : cell v) (y : cell w)
    (hxy : (x : Plane) = (y : Plane)) :
    (cellHomeomorph C₀ v x : PositiveCentralFibre) =
      (cellHomeomorph C₀ w y : PositiveCentralFibre) := by
  have hxw : (x : Plane) ∈ cell w := by rw [hxy]; exact y.2
  have hnonempty : (cell v ∩ cell w).Nonempty := ⟨x, x.2, hxw⟩
  rcases (cell_inter_cell_nonempty_iff_adjacent v w).mp hnonempty with rfl | hadj
  · have he : x = y := Subtype.ext hxy
    rw [he]
  obtain ⟨k, hk⟩ := (areAdjacent_iff_hexagonRay v w).mp hadj
  have hw : w = v + hexagonRay k :=
    (sub_eq_iff_eq_add.mp hk).trans (add_comm _ _)
  let a : baseCell := (cellTranslationHomeomorph v).symm x
  let b : baseCell := (cellTranslationHomeomorph w).symm y
  have ha : (a : Plane) ∈ cell (hexagonRay k) := by
    change (x : Plane) - latticePoint v ∈ cell (hexagonRay k)
    apply (sub_latticePoint_mem_cell_iff v (hexagonRay k) x).mpr
    simpa only [← hw] using hxw
  have hb : b = ⟨(a : Plane) - latticePoint (hexagonRay k), ha⟩ := by
    apply Subtype.ext
    change (y : Plane) - latticePoint w =
      ((x : Plane) - latticePoint v) - latticePoint (hexagonRay k)
    rw [← hxy, hw, latticePoint_add]
    abel
  apply Subtype.ext
  apply Subtype.ext
  rw [cellHomeomorph_coe, cellHomeomorph_coe]
  change twistedTranslate (CuspPositive.positiveTwist C₀) (-cuspVector v)
      ((compatibleCellHomeomorph C₀ a).1 : Space) =
    twistedTranslate (CuspPositive.positiveTwist C₀) (-cuspVector w)
      ((compatibleCellHomeomorph C₀ b).1 : Space)
  rw [hb, compatibleCellHomeomorph_opposite C₀ k a ha, twistedTranslate_add]
  have hu : -cuspVector w + cuspVector (hexagonRay k) = -cuspVector v := by
    rw [hw, cuspVector_add]
    abel
  rw [hu]

/-- No additional point-identifications occur in the actual central fibre. -/
theorem cellHomeomorph_eq_iff (v w : Lattice) (x : cell v) (y : cell w) :
    (cellHomeomorph C₀ v x : PositiveCentralFibre) =
      (cellHomeomorph C₀ w y : PositiveCentralFibre) ↔ (x : Plane) = (y : Plane) := by
  constructor
  · intro h
    have hxw : (x : Plane) ∈ cell w :=
      (cellHomeomorph_mem_positiveCell_iff C₀ v w x).mp (by
        rw [h]
        exact (cellHomeomorph C₀ w y).2)
    have hcomp := cellHomeomorph_compatible C₀ v w x ⟨x, hxw⟩ rfl
    have he : cellHomeomorph C₀ w ⟨x, hxw⟩ = cellHomeomorph C₀ w y :=
      Subtype.ext (hcomp.symm.trans h)
    exact congrArg Subtype.val ((cellHomeomorph C₀ w).injective he)
  · exact cellHomeomorph_compatible C₀ v w x y

end Wikipedia.HopfProblem.CuspHoneycomb
