import Wikipedia.NoExoticSixSphere.PartialFrameOverlap
import Wikipedia.NoExoticSixSphere.PartialFrameOneColumn
import Wikipedia.NoExoticSixSphere.SphereCylinderCoordinates
import Wikipedia.NoExoticSixSphere.SphereCompactificationChart

/-!
# Cylinder coordinates on the actual antipodal chart overlap

For the coordinate pole, the two-chart base intersection is exactly the
previously constructed smooth sphere cylinder. Consequently the actual
two-column total-space overlap is homeomorphic to `(ℝ × Sⁿ) × Sⁿ`.
The result is a homeomorphism of the original subspace topologies, not an
assigned homotopy type or an assumed homology calculation.
-/

noncomputable section

namespace NoExoticSixSphere.SphereCylinder

open Set

theorem join_head_tail (n : ℕ) (y : EuclideanSpace ℝ (Fin (n + 2))) :
    join n (y 0, tail n y) = y :=
  (join n).apply_symm_apply y

theorem join_zero (n : ℕ) (s : ℝ) :
    join n (s, 0) = s • (spherePole (n + 1)).val := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [spherePole]
  · simp [spherePole]

theorem tail_pole (n : ℕ) : tail n (spherePole (n + 1)).val = 0 := by
  have h := congrArg (tail n) (join_zero n 1)
  simpa only [tail_join, one_smul] using h.symm

theorem tail_eq_zero_iff (n : ℕ) (y : Sphere (n + 1)) :
    tail n y.val = 0 ↔ y = spherePole (n + 1) ∨ y = antipode (spherePole (n + 1)) := by
  constructor
  · intro h
    have hn := norm_join_sq n (y.val 0) (tail n y.val)
    rw [join_head_tail, ClosedHemisphere.unit_norm, h, norm_zero] at hn
    have hs : (y.val 0) ^ 2 = 1 := by nlinarith
    have hy : y.val = y.val 0 • (spherePole (n + 1)).val := by
      calc
        y.val = join n (y.val 0, tail n y.val) := (join_head_tail n y.val).symm
        _ = join n (y.val 0, 0) := by rw [h]
        _ = y.val 0 • (spherePole (n + 1)).val := join_zero n _
    rcases sq_eq_one_iff.mp hs with hp | hm
    · left
      apply Subtype.ext
      simpa only [hp, one_smul] using hy
    · right
      apply Subtype.ext
      change y.val = -(spherePole (n + 1)).val
      simpa only [hm, neg_one_smul] using hy
  · rintro (rfl | rfl)
    · exact tail_pole n
    · change tail n (-(spherePole (n + 1)).val) = 0
      rw [map_neg, tail_pole, neg_zero]

theorem band_eq_base_intersection (n : ℕ) :
    band n = Stiefel.ColumnBundle.baseSet (spherePole (n + 1)) ∩
      Stiefel.ColumnBundle.baseSet (antipode (spherePole (n + 1))) := by
  ext y
  have hi : antipode (antipode (spherePole (n + 1))) = spherePole (n + 1) :=
    Subtype.ext (neg_neg _)
  change ¬(tail n y.val = 0) ↔ y ≠ antipode (spherePole (n + 1)) ∧
    y ≠ antipode (antipode (spherePole (n + 1)))
  rw [tail_eq_zero_iff n y, not_or, hi, and_comm]

def bandHomeomorph (n : ℕ) : band n ≃ₜ ℝ × Sphere n :=
  (chart n).toOpenPartialHomeomorph.symm.toHomeomorphSourceTarget.trans
    (Homeomorph.Set.univ (ℝ × Sphere n))

theorem bandHomeomorph_symm_val (n : ℕ) (p : ℝ × Sphere n) :
    ((bandHomeomorph n).symm p).val = point n p := rfl

end NoExoticSixSphere.SphereCylinder

namespace NoExoticSixSphere.Stiefel.ColumnBundle

open GLOrthonormalization Set

def antipodalBaseHomeomorph (n : ℕ) :
    ↥(baseSet (spherePole (n + 1)) ∩ baseSet (antipode (spherePole (n + 1)))) ≃ₜ
      ℝ × Sphere n :=
  (Homeomorph.setCongr (SphereCylinder.band_eq_base_intersection n).symm).trans
    (SphereCylinder.bandHomeomorph n)

theorem antipodalBaseHomeomorph_symm_val (n : ℕ) (p : ℝ × Sphere n) :
    ((antipodalBaseHomeomorph n).symm p).val = SphereCylinder.point n p := rfl

def overlapCylinderHomeomorph {r : ℕ} (n : ℕ) (v : UnitSphere (Vector (r + 1))) :
    Overlap v (spherePole (n + 1)) (antipode (spherePole (n + 1))) ≃ₜ
      (ℝ × Sphere n) × Space (n + 1) r :=
  (overlapHomeomorph v (spherePole (n + 1)) (antipode (spherePole (n + 1)))).trans
    ((antipodalBaseHomeomorph n).prodCongr (Homeomorph.refl _))

theorem overlapCylinderHomeomorph_symm_val {r : ℕ} (n : ℕ)
    (v : UnitSphere (Vector (r + 1))) (p : (ℝ × Sphere n) × Space (n + 1) r) :
    ((overlapCylinderHomeomorph n v).symm p).val =
      fromCoordinates v (spherePole (n + 1)) (SphereCylinder.point n p.1, p.2) := rfl

def twoColumnOverlapHomeomorph (n : ℕ) (v : UnitSphere (Vector 2))
    (w : UnitSphere (Vector 1)) :
    Overlap v (spherePole (n + 1)) (antipode (spherePole (n + 1))) ≃ₜ
      (ℝ × Sphere n) × Sphere n :=
  (overlapCylinderHomeomorph n v).trans
    ((Homeomorph.refl (ℝ × Sphere n)).prodCongr (OneColumn.homeomorph w))

end NoExoticSixSphere.Stiefel.ColumnBundle
