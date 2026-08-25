import StackExchange.Puzzling139335.GlideCrossing.SourceBounds
import StackExchange.Puzzling139335.GlideCrossing.FirstBound
import StackExchange.Puzzling139335.GlideCrossing.SecondBound

/-!+# Scalar crossing theorem for the reversed-straddle glide configuration

The inputs are the two source-face height bounds, the unit-strip bounds on
the source side arms, and the endpoint bounds on the source-face centers.
The theorem proves both strict lower determinant inequalities.  The separate
topological interface argument supplies the two strict upper inequalities.
-/

noncomputable section

namespace Puzzling139335.GlideCrossing

/-- Determinant of the left copy's first base endpoint relative to the
right copy's directed unit base, after the common vertical reflection. -/
def firstDeterminant (α β y₁ x₂ y₂ : ℝ) : ℝ :=
  Real.sin α - y₁ - Real.sin (α - β) * x₂ - Real.cos (α - β) * y₂

/-- The corresponding determinant expression for the other unit base. -/
def secondDeterminant (α β x₁ y₁ y₂ : ℝ) : ℝ :=
  Real.sin β - Real.sin (α - β) * x₁ - Real.cos (α - β) * y₁ - y₂

/-- Complete analytic lower bounds from the scalar source geometry. -/
theorem sourceBounds_lower (α β a b x₁ y₁ x₂ y₂ : ℝ)
    (hβ : 0 < β) (hβα : β < α) (hα : α < Real.pi / 2) (hb : b < 1 / 2)
    (hheight₁ : 2 * Real.cos α * (1 / 2 - b) ≤ 1 / 2 - a)
    (hheight₂ : 2 * Real.cos β * (1 / 2 - a) ≤ 1 / 2 - b)
    (haCap : a ≤ min (1 / 2) (Real.cos β / (1 + Real.sin β)))
    (hbCap : b ≤ min (Real.sin β / (1 + Real.cos β))
      (Real.cos α / (1 + Real.sin α)))
    (hx₁ : x₁ ≤ 1 - Real.sin α * (1 / 2 - b))
    (hy₁ : y₁ ≤ 1 / 2 - Real.cos α * (1 / 2 - b))
    (hx₂ : x₂ ≤ 1)
    (hy₂ : y₂ ≤ 1 / 2 - Real.cos β * (1 / 2 - a)) :
    -Real.sin (α - β) < firstDeterminant α β y₁ x₂ y₂ ∧
      -Real.sin (α - β) < secondDeterminant α β x₁ y₁ y₂ := by
  obtain ⟨hαlo, hprod⟩ := sourceFace_angle_bounds α β a b
    hβ hβα.le hα hb hheight₁ hheight₂
  obtain ⟨hD, hK⟩ := strictAngleDifference α β hβ hβα hα
  have hπ := Real.pi_pos
  have hC : 0 ≤ Real.cos α :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith, hα⟩).le
  have hc : 0 ≤ Real.cos β :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩).le
  have hs : 0 ≤ Real.sin β :=
    Real.sin_nonneg_of_nonneg_of_le_pi hβ.le (by linarith)
  have hp : 0 ≤ 1 / 2 - a := by
    have ha := le_trans haCap (min_le_left _ _)
    linarith
  have hx₂' : x₂ ≤ 1 + Real.sin β * (1 / 2 - a) := by
    linarith only [hx₂, mul_nonneg hs hp]
  have hbC : b ≤ Real.cos α / (1 + Real.sin α) :=
    le_trans hbCap (min_le_right _ _)
  have hFpos := firstLowerBound_pos α β hαlo hβ hβα.le hα
  have hFarms := firstArm_lower (Real.cos α) (Real.sin α)
    (Real.cos β) (Real.sin β) (Real.cos (α - β)) a b hC haCap hbC
  have hFgeom := firstDet_lower (Real.cos α) (Real.sin α)
    (Real.cos β) (Real.sin β) (Real.sin (α - β)) (Real.cos (α - β))
    (1 / 2 - a) (1 / 2 - b) x₂ y₁ y₂ hD.le hK.le
    (firstCoefficient_trig α β) hy₁ hx₂' hy₂
  have hFlower : 0 < firstDeterminant α β y₁ x₂ y₂ + Real.sin (α - β) :=
    lt_of_lt_of_le hFpos (le_trans hFarms hFgeom)
  have hGpos := secondLowerBound_pos α β hαlo hβ hβα.le hα hprod
  have hGarms := secondArm_lower (Real.cos α) (Real.sin α)
    (Real.cos β) (Real.sin β) (Real.cos (α - β)) a b hC hc hheight₁ hbCap
  have hGgeom := secondDet_lower (Real.cos α) (Real.sin α)
    (Real.cos β) (Real.sin β) (Real.sin (α - β)) (Real.cos (α - β))
    (1 / 2 - a) (1 / 2 - b) x₁ y₁ y₂ hD.le hK.le
    (secondCoefficient_trig α β) hx₁ hy₁ hy₂
  have hGlower : 0 < secondDeterminant α β x₁ y₁ y₂ + Real.sin (α - β) :=
    lt_of_lt_of_le hGpos (le_trans hGarms hGgeom)
  constructor <;> linarith only [hFlower, hGlower]

/-- The two strict sign changes imply the determinant formulation of a
proper crossing; the upper signs are supplied by the interface lemma. -/
theorem crossingSigns_of_lower (α β y₁ x₂ y₂ x₁ : ℝ)
    (hF : -Real.sin (α - β) < firstDeterminant α β y₁ x₂ y₂)
    (hG : -Real.sin (α - β) < secondDeterminant α β x₁ y₁ y₂)
    (hFneg : firstDeterminant α β y₁ x₂ y₂ < 0)
    (hGneg : secondDeterminant α β x₁ y₁ y₂ < 0) :
    firstDeterminant α β y₁ x₂ y₂ ∈ Set.Ioo (-Real.sin (α - β)) 0 ∧
      secondDeterminant α β x₁ y₁ y₂ ∈ Set.Ioo (-Real.sin (α - β)) 0 :=
  ⟨⟨hF, hFneg⟩, ⟨hG, hGneg⟩⟩

end Puzzling139335.GlideCrossing
