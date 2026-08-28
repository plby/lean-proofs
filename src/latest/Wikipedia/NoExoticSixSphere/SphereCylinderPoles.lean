import Wikipedia.NoExoticSixSphere.SphereCylinderCoordinates

/-!
# The actual two missing points of the sphere-cylinder chart

The complement of the genuine cylinder chart is exactly its two coordinate
poles. Its point map is an open embedding, and its image is the original
sphere with precisely those two points removed.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereCylinder

def endPole (n : ℕ) (b : Bool) : Sphere (n + 1) :=
  ⟨join n ((if b then 1 else -1), 0), by
    have hn := norm_join_sq n (if b then 1 else -1) 0
    have hs : (if b then (1 : ℝ) else -1) ^ 2 = 1 := by cases b <;> norm_num
    simp only [hs, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at hn
    have hnorm : ‖join n ((if b then 1 else -1), 0)‖ = 1 := by
      nlinarith [norm_nonneg (join n ((if b then 1 else -1), 0))]
    simpa only [mem_sphere, dist_zero_right] using hnorm⟩

theorem endPole_head (n : ℕ) (b : Bool) : (endPole n b).val 0 = if b then 1 else -1 := rfl

theorem tail_endPole (n : ℕ) (b : Bool) : tail n (endPole n b).val = 0 :=
  tail_join n _ _

theorem endPole_not_mem_band (n : ℕ) (b : Bool) : endPole n b ∉ band n := by
  change ¬ tail n (endPole n b).val ≠ 0
  rw [tail_endPole]
  exact not_not.mpr rfl

theorem endPoles_ne (n : ℕ) : endPole n false ≠ endPole n true := by
  intro he
  have h := congrArg (fun y : Sphere (n + 1) ↦ y.val 0) he
  norm_num [endPole_head] at h

theorem not_mem_band_iff (n : ℕ) (y : Sphere (n + 1)) :
    y ∉ band n ↔ y = endPole n false ∨ y = endPole n true := by
  constructor
  · intro hy
    have ht : tail n y.val = 0 := not_ne_iff.mp hy
    have he : y.val = join n (y.val 0, 0) := by
      ext i
      refine Fin.cases rfl (fun j ↦ ?_) i
      exact congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ z j) ht
    have hs := norm_join_sq n (y.val 0) 0
    rw [← he, ClosedHemisphere.unit_norm, norm_zero] at hs
    have hm : (y.val 0 - 1) * (y.val 0 + 1) = 0 := by nlinarith [hs]
    rcases mul_eq_zero.mp hm with h | h
    · right
      apply Subtype.ext
      rw [he, sub_eq_zero.mp h]
      rfl
    · left
      have hh : y.val 0 = -1 := by linarith
      apply Subtype.ext
      rw [he, hh]
      rfl
  · rintro (rfl | rfl)
    · exact endPole_not_mem_band n false
    · exact endPole_not_mem_band n true

theorem band_compl_eq (n : ℕ) :
    (band n)ᶜ = {endPole n false, endPole n true} := by
  ext y
  exact not_mem_band_iff n y

theorem injective_point (n : ℕ) : Injective (point n) :=
  LeftInverse.injective (inverse_point n)

theorem isOpenEmbedding_point (n : ℕ) : IsOpenEmbedding (point n) :=
  (chart n).toOpenPartialHomeomorph.isOpenEmbedding rfl

end NoExoticSixSphere.SphereCylinder
