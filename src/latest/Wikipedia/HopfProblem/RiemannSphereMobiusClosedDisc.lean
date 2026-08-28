import Wikipedia.HopfProblem.RiemannSphereMobiusDisc

/-!
# The closed disc with a boundary pole removed

The verified sphere cross-ratio restricts to a homeomorphism between the
closed unit disc minus its pole and a closed half-plane. All topologies
here are the inherited subspace topologies of `ℂ`: the construction uses
the existing sphere homeomorphism and the ordinary finite affine chart.
-/

noncomputable section

open Set Topology OnePoint
open scoped ContDiff

namespace Wikipedia.HopfProblem.RiemannSphere

open MobiusCircle

/-- The closed unit disc with the prescribed finite pole removed. -/
def closedDiscWithoutPole (c : ℂ) : Set ℂ := {z | ‖z‖ ≤ 1 ∧ z ≠ c}

theorem closedDiscWithoutPole_eq (c : ℂ) :
    closedDiscWithoutPole c = Metric.closedBall 0 1 \ {c} := by
  ext z
  simp [closedDiscWithoutPole, dist_zero_right]

/-- The closed half-plane selected by a nonzero real orientation constant. -/
def closedOrientedHalfPlane (k : ℝ) : Set ℂ := {w | 0 ≤ k * w.im}

/-- Passing to the finite affine chart preserves the actual subspace topology. -/
def finiteImageHomeomorph (s : Set ℂ) : s ≃ₜ finiteImage s :=
  (OnePoint.isOpenEmbedding_coe (X := ℂ)).isEmbedding.homeomorphImage s

@[simp] theorem finiteImageHomeomorph_apply_coe (s : Set ℂ) (z : s) :
    (finiteImageHomeomorph s z : RiemannSphere) = ((z : ℂ) : RiemannSphere) := rfl

@[simp] theorem finiteImageHomeomorph_symm_apply_coe (s : Set ℂ) (p : finiteImage s) :
    (((finiteImageHomeomorph s).symm p : ℂ) : RiemannSphere) = (p : RiemannSphere) := by
  exact congrArg Subtype.val ((finiteImageHomeomorph s).apply_symm_apply p)

variable {a b c : ℂ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
variable (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : ‖c‖ = 1)

include hab hac hbc ha hb hc in
theorem orientation_mul_crossRatio_im_nonneg_iff {z : ℂ} (hzc : z ≠ c) :
    0 ≤ orientation a b c * (crossRatio a b c z).im ↔ ‖z‖ ≤ 1 := by
  have h := not_congr
    (orientation_mul_crossRatio_im_neg_iff ha hb hc hab.symm hbc hac hzc)
  simpa only [not_lt] using h

include ha hb hc in
theorem threePointBiholomorph_mem_closedHalfPlane_iff (p : RiemannSphere) :
    threePointBiholomorph a b c hab hac hbc p ∈
        finiteImage (closedOrientedHalfPlane (orientation a b c)) ↔
      p ∈ finiteImage (closedDiscWithoutPole c) := by
  induction p using OnePoint.rec with
  | infty =>
    rw [threePointBiholomorph_infty]
    simp only [coe_mem_finiteImage_iff, infty_not_mem_finiteImage, iff_false,
      closedOrientedHalfPlane, mem_ofPred_eq]
    exact not_le_of_gt (orientation_mul_coefficient_im_neg ha hb hc hab.symm hbc hac)
  | coe z =>
    by_cases hzc : z = c
    · subst z
      simp [closedDiscWithoutPole]
    · rw [threePointBiholomorph_coe a b c hab hac hbc z hzc]
      simp only [coe_mem_finiteImage_iff, closedOrientedHalfPlane, closedDiscWithoutPole,
        mem_ofPred_eq, and_iff_left hzc]
      exact orientation_mul_crossRatio_im_nonneg_iff hab hac hbc ha hb hc hzc

/-- The restricted sphere homeomorphism, still with the inherited sphere topologies. -/
def closedDiscHalfPlaneSphereHomeomorph :
    finiteImage (closedDiscWithoutPole c) ≃ₜ
      finiteImage (closedOrientedHalfPlane (orientation a b c)) :=
  (threePointBiholomorph a b c hab hac hbc).toHomeomorph.subtype
    (fun p => (threePointBiholomorph_mem_closedHalfPlane_iff hab hac hbc ha hb hc p).symm)

/-- The closed unit disc minus a boundary pole is homeomorphic to the closed
oriented half-plane in its ordinary complex subspace topology. -/
def closedDiscHalfPlaneHomeomorph :
    closedDiscWithoutPole c ≃ₜ closedOrientedHalfPlane (orientation a b c) :=
  ((finiteImageHomeomorph (closedDiscWithoutPole c)).trans
    (closedDiscHalfPlaneSphereHomeomorph hab hac hbc ha hb hc)).trans
      (finiteImageHomeomorph (closedOrientedHalfPlane (orientation a b c))).symm

theorem closedDiscHalfPlaneHomeomorph_sphere (z : closedDiscWithoutPole c) :
    (((closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc z :
      closedOrientedHalfPlane (orientation a b c)) : ℂ) : RiemannSphere) =
        threePointBiholomorph a b c hab hac hbc ((z : ℂ) : RiemannSphere) := by
  exact finiteImageHomeomorph_symm_apply_coe
    (closedOrientedHalfPlane (orientation a b c))
    (closedDiscHalfPlaneSphereHomeomorph hab hac hbc ha hb hc
      (finiteImageHomeomorph (closedDiscWithoutPole c) z))

/-- The homeomorphism has the literal finite cross-ratio formula. -/
@[simp] theorem closedDiscHalfPlaneHomeomorph_apply (z : closedDiscWithoutPole c) :
    (closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc z : ℂ) = crossRatio a b c z := by
  apply OnePoint.coe_injective
  rw [closedDiscHalfPlaneHomeomorph_sphere,
    threePointBiholomorph_coe a b c hab hac hbc z z.property.2]
  rfl

@[simp] theorem closedDiscHalfPlaneHomeomorph_first :
    (closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc ⟨a, ha.le, hac⟩ : ℂ) = 0 := by
  rw [closedDiscHalfPlaneHomeomorph_apply]
  exact crossRatio_at_zero a b c

@[simp] theorem closedDiscHalfPlaneHomeomorph_second :
    (closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc ⟨b, hb.le, hbc⟩ : ℂ) = 1 := by
  rw [closedDiscHalfPlaneHomeomorph_apply]
  exact crossRatio_at_one hab.symm hbc

/-- Precisely the remaining unit-circle points go to the real boundary. -/
theorem closedDiscHalfPlaneHomeomorph_im_eq_zero_iff (z : closedDiscWithoutPole c) :
    (closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc z : ℂ).im = 0 ↔ ‖(z : ℂ)‖ = 1 := by
  rw [closedDiscHalfPlaneHomeomorph_apply]
  exact crossRatio_im_eq_zero_iff ha hb hc hab.symm hbc hac z.property.2

/-- Precisely the open-disc points go to the strict half-plane. -/
theorem closedDiscHalfPlaneHomeomorph_strict_iff (z : closedDiscWithoutPole c) :
    0 < orientation a b c * (closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc z : ℂ).im ↔
      ‖(z : ℂ)‖ < 1 := by
  rw [closedDiscHalfPlaneHomeomorph_apply]
  exact orientation_mul_crossRatio_im_pos_iff ha hb hc hab.symm hbc hac z.property.2

include hab hac hbc ha hb hc in
/-- The coordinate formula is bijective between the two closed sets. -/
theorem crossRatio_bijOn_closedDiscWithoutPole :
    BijOn (crossRatio a b c) (closedDiscWithoutPole c)
      (closedOrientedHalfPlane (orientation a b c)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rw [← closedDiscHalfPlaneHomeomorph_apply hab hac hbc ha hb hc ⟨z, hz⟩]
    exact (closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc ⟨z, hz⟩).property
  · intro z hz w hw he
    have he' : closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc ⟨z, hz⟩ =
        closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc ⟨w, hw⟩ := by
      apply Subtype.ext
      simpa only [closedDiscHalfPlaneHomeomorph_apply] using he
    exact congrArg Subtype.val ((closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc).injective he')
  · intro w hw
    obtain ⟨z, hz⟩ := (closedDiscHalfPlaneHomeomorph hab hac hbc ha hb hc).surjective ⟨w, hw⟩
    refine ⟨z, z.property, ?_⟩
    rw [← closedDiscHalfPlaneHomeomorph_apply hab hac hbc ha hb hc z]
    exact congrArg Subtype.val hz

theorem closedHalfPlane_eq_upper_or_lower {k : ℝ} (hk : k ≠ 0) :
    closedOrientedHalfPlane k = {z : ℂ | 0 ≤ z.im} ∨
      closedOrientedHalfPlane k = {z : ℂ | z.im ≤ 0} := by
  rcases lt_or_gt_of_ne hk with hk | hk
  · right
    ext z
    change 0 ≤ k * z.im ↔ z.im ≤ 0
    constructor
    · intro hz
      by_contra hn
      have hz' := lt_of_not_ge hn
      exact not_le_of_gt (mul_neg_of_neg_of_pos hk hz') hz
    · exact fun hz => mul_nonneg_of_nonpos_of_nonpos hk.le hz
  · left
    ext z
    exact mul_nonneg_iff_of_pos_left hk

end Wikipedia.HopfProblem.RiemannSphere
