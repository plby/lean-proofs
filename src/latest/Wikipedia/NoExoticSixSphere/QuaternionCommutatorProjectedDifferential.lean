import Wikipedia.NoExoticSixSphere.QuaternionCommutatorRotationDifferential
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The actual projected commutator derivative in quaternionic tangent directions

For infinitesimal quaternion inputs v,w with zero real part, the actual
first-column expression has derivative (-v,4a+w) at the midpoint.
The tangent hypotheses here are discharged by the sphere charts later.
-/

noncomputable section

open scoped ContDiff commutatorElement

namespace NoExoticSixSphere.QuaternionCommutatorProjectedDifferential

open Wikipedia.HopfProblem.UnitQuaternionSphere
open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
open QuaternionCommutatorRotation QuaternionCommutatorColumns
open QuaternionCommutatorColumnDifferential QuaternionCommutatorRotationDifferential

local notation "ℍ" => Quaternion ℝ

local instance : StarModule ℝ ℍ where
  star_smul r q := by simp [Quaternion.star_smul]

def column (θ : ℝ) (q r : ℍ) : ℍ × ℍ :=
  (top (diagonalZero (Real.cos θ) (Real.sin θ) r)
    (offDiagonal (Real.cos θ) (Real.sin θ) r) q,
   bottom (diagonalZero (Real.cos θ) (Real.sin θ) r)
    (offDiagonal (Real.cos θ) (Real.sin θ) r)
    (diagonalOne (Real.cos θ) (Real.sin θ) r) q)

theorem column_actual (θ : ℝ) (q r : UnitQuaternions) :
    ((projection ⁅fiberInclusion q, conjugatedFiber θ r⁆).val.fst,
      (projection ⁅fiberInclusion q, conjugatedFiber θ r⁆).val.snd) = column θ q.val r.val := by
  apply Prod.ext
  · change (⁅fiberInclusion q, conjugatedFiber θ r⁆).val 0 0 = _
    rw [commutator_top, conjugatedFiber_matrix]
    rfl
  · change (⁅fiberInclusion q, conjugatedFiber θ r⁆).val 1 0 = _
    rw [commutator_bottom, conjugatedFiber_matrix]
    rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {θ : E → ℝ} {q r : E → ℍ}
  {θ' : E →L[ℝ] ℝ} {q' r' : E →L[ℝ] ℍ} {x : E}

theorem hasFDerivAt_column (hθ : HasFDerivAt θ θ' x)
    (hq : HasFDerivAt q q' x) (hr : HasFDerivAt r r' x)
    (hθ₀ : θ x = Real.pi / 4) (hq₀ : q x = -1) (hr₀ : r x = -1)
    (hq' : ∀ v, star (q' v) = -q' v) (hr' : ∀ v, star (r' v) = -r' v) :
    HasFDerivAt (fun y ↦ column (θ y) (q y) (r y))
      ((-q').prod (((4 : ℝ) • θ').smulRight (1 : ℍ) + r')) x := by
  have ha := hasFDerivAt_diagonalZero hθ hr hθ₀ hr₀
  have hb := hasFDerivAt_offDiagonal hθ hr hθ₀ hr₀
  have hd := hasFDerivAt_diagonalOne hθ hr hθ₀ hr₀
  have ha₀ : diagonalZero (Real.cos (θ x)) (Real.sin (θ x)) (r x) = 0 := by
    rw [hθ₀, hr₀]
    exact midpoint_entries.1
  have hb₀ : offDiagonal (Real.cos (θ x)) (Real.sin (θ x)) (r x) = 1 := by
    rw [hθ₀, hr₀]
    exact midpoint_entries.2.1
  have hd₀ : diagonalOne (Real.cos (θ x)) (Real.sin (θ x)) (r x) = 0 := by
    rw [hθ₀, hr₀]
    exact midpoint_entries.2.2
  have ht := hasFDerivAt_top ha hb hq ha₀ hb₀ hq₀
  have hbottom := hasFDerivAt_bottom ha hb hd hq ha₀ hb₀ hd₀ hq₀
  convert! ht.prodMk hbottom using 1 <;> try rfl
  ext v : 1
  apply Prod.ext
  · simp [conjugation, Quaternion.star_smul, hq', hr']
  · simp [conjugation, Quaternion.star_smul, hq', hr']
    module

theorem contDiff_column {n : ℕ∞ω} (hθ : ContDiff ℝ n θ)
    (hq : ContDiff ℝ n q) (hr : ContDiff ℝ n r) :
    ContDiff ℝ n (fun y ↦ column (θ y) (q y) (r y)) := by
  have ha : ContDiff ℝ n
      (fun y ↦ diagonalZero (Real.cos (θ y)) (Real.sin (θ y)) (r y)) := by
    simp only [diagonalZero_smul]
    exact ((hθ.cos.pow 2).smul contDiff_const).add ((hθ.sin.pow 2).smul hr)
  have hb : ContDiff ℝ n
      (fun y ↦ offDiagonal (Real.cos (θ y)) (Real.sin (θ y)) (r y)) := by
    simp only [offDiagonal_smul]
    exact (hθ.cos.mul hθ.sin).smul (contDiff_const.sub hr)
  have hd : ContDiff ℝ n
      (fun y ↦ diagonalOne (Real.cos (θ y)) (Real.sin (θ y)) (r y)) := by
    simp only [diagonalOne_smul]
    exact ((hθ.sin.pow 2).smul contDiff_const).add ((hθ.cos.pow 2).smul hr)
  have hsa := conjugation.contDiff.comp ha
  have hsb := conjugation.contDiff.comp hb
  have hsq := conjugation.contDiff.comp hq
  exact ((ha.mul hsa).add ((hb.mul hsq).mul hsb)).prodMk
    (hq.mul ((hb.mul hsa).add ((hd.mul hsq).mul hsb)))

end NoExoticSixSphere.QuaternionCommutatorProjectedDifferential
