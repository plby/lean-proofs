import StackExchange.Puzzling139335.N4Midline.Contacts.Angles

/-!
# The used supporting corner is the bottom midpoint

For an inward frame in the second quadrant, a supporting cone based in
the left half-square can contain the bottom midpoint only when its vertex
is that midpoint. If an actual neighborhood of the cone lies in the
piece, the second inward ray cannot point below the square. This forces
the first ray's angle to equal `π / 2`.
-/

open Set Metric

namespace Puzzling139335.N4Midline

noncomputable section

open ThreeCorners

/-- The midpoint of the square's bottom edge. -/
def bottomMidpoint : Plane := !₂[(1 / 2 : ℝ), 0]

@[simp] theorem bottomMidpoint_zero : bottomMidpoint 0 = (1 / 2 : ℝ) := rfl
@[simp] theorem bottomMidpoint_one : bottomMidpoint 1 = (0 : ℝ) := rfl

/-- Cone containment of the bottom midpoint already forces the cone
vertex to be the midpoint throughout the allowed angular interval. -/
theorem eq_bottomMidpoint_of_mem_supportCone {B : Plane} (hB : B ∈ leftHalfSquare)
    {θ : ℝ} (hθ : θ ∈ Ico (Real.pi / 2) Real.pi)
    (hM : bottomMidpoint ∈ supportCone B θ) : B = bottomMidpoint := by
  have hs : 0 < Real.sin θ := sin_pos_of_left_frame_angle hθ
  have hc : Real.cos θ ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 (by linarith [Real.pi_pos, hθ.2])
  have hdx : 0 ≤ (1 / 2 : ℝ) - B 0 := sub_nonneg.mpr hB.1.2
  have hby : 0 ≤ B 1 := hB.2.1
  have hprod : Real.cos θ * ((1 / 2 : ℝ) - B 0) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hc hdx
  have hfirst := hM.1
  have hsecond := hM.2
  simp [Schoenflies.Plane.inner_eq, ray, perpRay, bottomMidpoint] at hfirst hsecond
  have hBy : B 1 = 0 := by nlinarith
  have hBx : B 0 = (1 / 2 : ℝ) := by
    rw [hBy] at hsecond
    nlinarith
  ext i
  fin_cases i
  · exact hBx
  · exact hBy

/-- A cone germ in the upper closed half-plane cannot have a second
inward ray with negative vertical component at a bottom-line vertex. -/
theorem cos_nonneg_of_bottom_cone_germ {P : Set Plane}
    (hP : ∀ p ∈ P, 0 ≤ p 1) {B : Plane} (hB : B 1 = 0) {θ : ℝ}
    (hgerm : ∃ ε : ℝ, 0 < ε ∧ ball B ε ∩ supportCone B θ ⊆ P) :
    0 ≤ Real.cos θ := by
  obtain ⟨ε, hε, hnear⟩ := hgerm
  have ht : 0 < ε / 2 := half_pos hε
  have htε : ε / 2 < ε := half_lt_self hε
  have hball : B + (ε / 2) • perpRay θ ∈ ball B ε := by
    apply mem_ball.mpr
    calc
      dist (B + (ε / 2) • perpRay θ) B = ‖(ε / 2) • perpRay θ‖ := by
        rw [dist_eq_norm]
        congr 1
        abel
      _ = ε / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, norm_perpRay, mul_one]
      _ < ε := htε
  have hcone : B + (ε / 2) • perpRay θ ∈ supportCone B θ :=
    (mem_supportCone_iff _ _ _).mpr ⟨0, ε / 2, le_rfl, ht.le, by simp⟩
  have hnonneg := hP _ (hnear ⟨hball, hcone⟩)
  have hproduct : 0 ≤ (ε / 2) * Real.cos θ := by
    simpa [hB, perpRay] using hnonneg
  exact nonneg_of_mul_nonneg_right hproduct ht

/-- The actual cone germ and bottom-midpoint membership force the
supporting vertex and angle used by the endpoint placement argument. -/
theorem endpoint_of_bottomMidpoint_mem {P : Set Plane} (hP : P ⊆ leftHalfSquare)
    {B : Plane} (hB : B ∈ P) {θ : ℝ}
    (hθ : θ ∈ Ico (Real.pi / 2) Real.pi) (hcone : P ⊆ supportCone B θ)
    (hM : bottomMidpoint ∈ P)
    (hgerm : ∃ ε : ℝ, 0 < ε ∧ ball B ε ∩ supportCone B θ ⊆ P) :
    θ = Real.pi / 2 ∧ B = bottomMidpoint := by
  have hBM := eq_bottomMidpoint_of_mem_supportCone (hP hB) hθ (hcone hM)
  have hcos : 0 ≤ Real.cos θ := cos_nonneg_of_bottom_cone_germ
    (fun p hp => (hP hp).2.1) (by rw [hBM]; rfl) hgerm
  refine ⟨le_antisymm ?_ hθ.1, hBM⟩
  by_contra hgt
  have hstrict : Real.pi / 2 < θ := lt_of_not_ge hgt
  exact (not_lt_of_ge hcos) (cos_neg_of_strict_left_frame_angle ⟨hstrict, hθ.2⟩)

end

end Puzzling139335.N4Midline
