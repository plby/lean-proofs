import Util.IncidenceGeometry.PlanarRot90CoefficientUniqueness
import Util.IncidenceGeometry.PlanarRot90Decomposition
import Util.IncidenceGeometry.PlanarRot90LinearCombination
import Util.IncidenceGeometry.PlanarRot90ScalarSameSideConesDisjoint

open Classical
noncomputable section

lemma PlanarRot90SameSideConesDisjoint {u d : EuclideanSpace ℝ (Fin 2)}
    (hu : u ≠ 0) (_hd : d ≠ 0)
    (hnot : ¬ ∃ A : ℝ, 0 < A ∧ d = A • u) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ a c b r : ℝ, 0 < a → 0 < c → 0 < b * r →
        |b| < κ * a → |r| < κ * c →
          a • u + b • PlanarRot90 u ≠ c • d + r • PlanarRot90 d := by
  let A : ℝ := inner ℝ d u / (‖u‖ ^ 2)
  let B : ℝ := inner ℝ d (PlanarRot90 u) / (‖u‖ ^ 2)
  have hd_decomp : d = A • u + B • PlanarRot90 u := by
    simpa [A, B] using PlanarRot90Decomposition u d hu
  have hscalar_not : ¬ (0 < A ∧ B = 0) := by
    intro hAB
    exact hnot ⟨A, hAB.1, by simp [hd_decomp, hAB.2]⟩
  obtain ⟨κ, hκpos, hκ⟩ := PlanarRot90ScalarSameSideConesDisjoint A B hscalar_not
  refine ⟨κ, hκpos, ?_⟩
  intro a c b r ha hc hbr hb hr hEq
  have hrot_decomp : PlanarRot90 d = (-B) • u + A • PlanarRot90 u := by
    rw [hd_decomp]
    exact PlanarRot90LinearCombination u A B
  let x : EuclideanSpace ℝ (Fin 2) := a • u + b • PlanarRot90 u
  have hleft_coeff := PlanarRot90CoefficientUniqueness (d := u) (v := x) hu (by rfl)
  have hright_rep :
      x = (c * A - r * B) • u + (c * B + r * A) • PlanarRot90 u := by
    dsimp [x]
    rw [hEq, hd_decomp, PlanarRot90LinearCombination u A B]
    apply PiLp.ext
    intro k
    simp
    ring
  have hright_coeff :=
    PlanarRot90CoefficientUniqueness (d := u) (v := x) hu hright_rep
  have ha_eq : a = c * A - r * B := by
    linarith [hleft_coeff.1, hright_coeff.1]
  have hb_eq : b = c * B + r * A := by
    linarith [hleft_coeff.2, hright_coeff.2]
  exact hκ a c b r ha hc hbr hb hr ⟨ha_eq, hb_eq⟩
