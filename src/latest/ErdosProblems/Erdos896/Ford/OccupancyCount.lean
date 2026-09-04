/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.Occupancy

/-!
# Counting good finite occupancies

The cycle lemma in `Occupancy` says that every placement of `v` labelled
balls into `v` boxes can be made good by a cyclic relabelling of the boxes.
Here we turn that statement into the corresponding finite cardinality bound:
at least a `1 / v` fraction of all placements are good.
-/

namespace Erdos896.Ford.Occupancy

/-- Rotating a good placement back by the opposite cut gives a surjection
from good placements together with a cut onto all placements. -/
theorem surjective_rotatePlacement_good (v : ℕ) (hv : 0 < v) :
    Function.Surjective
      (fun p : {f : Fin v → Fin v // Good f} × Fin v ↦
        rotatePlacement (-p.2) p.1) := by
  let : NeZero v := ⟨Nat.ne_of_gt hv⟩
  intro f
  obtain ⟨r, hr⟩ := exists_rotatePlacement_good hv f
  refine ⟨⟨⟨rotatePlacement r f, hr⟩, r⟩, ?_⟩
  funext i
  simp [rotatePlacement, sub_eq_add_neg, add_assoc]

/-- There are at least `v ^ v / v` good placements of `v` labelled balls
into `v` boxes, stated without division in `ℕ`. -/
theorem pow_le_mul_card_good (v : ℕ) (hv : 0 < v) :
    v ^ v ≤ v * (Finset.univ.filter (@Good v)).card := by
  have hcard := Fintype.card_le_of_surjective
    (fun p : {f : Fin v → Fin v // Good f} × Fin v ↦
      rotatePlacement (-p.2) p.1)
    (surjective_rotatePlacement_good v hv)
  simpa [Fintype.card_prod, Fintype.card_subtype, Nat.mul_comm] using hcard

end Erdos896.Ford.Occupancy
