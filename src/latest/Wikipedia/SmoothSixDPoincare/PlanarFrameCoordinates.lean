import Wikipedia.SmoothSixDPoincare.PlaneAffinePerturbation
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.LinearAlgebra.Determinant

/-!
# Explicit coordinates on the two determinant components of planar frames

The first column is nonzero. The second has a unique parallel coefficient
and a signed transverse coefficient relative to the quarter-turn of the
first. The latter coefficient has the determinant's sign. These coordinates
will construct paths inside the actual open determinant component.
-/

noncomputable section

open Function
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.PlanarFrame

open PlaneImmersion (Plane linearMap)

def area (u v : Plane) : ℝ := u.1 * v.2 - u.2 * v.1

def squareLength (u : Plane) : ℝ := u.1 ^ 2 + u.2 ^ 2

def quarterTurn (u : Plane) : Plane := (-u.2, u.1)

def parallelCoeff (u v : Plane) : ℝ := (u.1 * v.1 + u.2 * v.2) / squareLength u

def transverseCoeff (u v : Plane) : ℝ := area u v / squareLength u

def determinant (L : Plane →L[ℝ] Plane) : ℝ := area (L (1, 0)) (L (0, 1))

theorem squareLength_pos {u : Plane} (hu : u ≠ 0) : 0 < squareLength u := by
  have hsq₁ := sq_nonneg u.1
  have hsq₂ := sq_nonneg u.2
  by_contra h
  have hz : u.1 ^ 2 + u.2 ^ 2 ≤ 0 := le_of_not_gt h
  have hu₁ : u.1 = 0 := by nlinarith
  have hu₂ : u.2 = 0 := by nlinarith
  exact hu (Prod.ext hu₁ hu₂)

theorem decompose_second_column {u : Plane} (hu : u ≠ 0) (v : Plane) :
    parallelCoeff u v • u + transverseCoeff u v • quarterTurn u = v := by
  have hnorm := (squareLength_pos hu).ne'
  ext <;> dsimp [parallelCoeff, transverseCoeff, area, quarterTurn]
  · field_simp
    simp only [squareLength]
    ring
  · field_simp
    simp only [squareLength]
    ring

theorem area_transverse (u : Plane) (a b : ℝ) :
    area u (a • u + b • quarterTurn u) = b * squareLength u := by
  dsimp [area, quarterTurn, squareLength]
  ring

theorem linearMap_first (u v : Plane) : linearMap (u, v) (1, 0) = u := by
  simp [PlaneImmersion.linearMap_apply]

theorem linearMap_second (u v : Plane) : linearMap (u, v) (0, 1) = v := by
  simp [PlaneImmersion.linearMap_apply]

theorem linearMap_columns (L : Plane →L[ℝ] Plane) :
    linearMap (L (1, 0), L (0, 1)) = L := by
  apply ContinuousLinearMap.ext
  intro p
  have hp : p = p.1 • ((1 : ℝ), 0) + p.2 • (0, 1) := by ext <;> simp
  rw [PlaneImmersion.linearMap_apply, ← map_smul, ← map_smul, ← map_add, ← hp]

theorem determinant_linearMap (u v : Plane) : determinant (linearMap (u, v)) = area u v := by
  rw [determinant, linearMap_first, linearMap_second]

/-- The explicit signed area is the genuine basis-independent linear determinant. -/
theorem determinant_eq_det (L : Plane →L[ℝ] Plane) : determinant L = L.toLinearMap.det := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ), Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Module.Basis.coe_finTwoProd_repr,
    determinant, area, mul_comm]

theorem bijective_of_determinant_ne_zero (L : Plane →L[ℝ] Plane) (hL : determinant L ≠ 0) :
    Bijective L := by
  have hdet : L.toLinearMap.det ≠ 0 := by rwa [determinant_eq_det] at hL
  have hker : L.toLinearMap.ker = ⊥ := by
    by_contra h
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  have hi : Injective L := LinearMap.ker_eq_bot.mp hker
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi⟩

theorem continuous_determinant : Continuous determinant := by
  have h₁ : Continuous (fun L : Plane →L[ℝ] Plane => L (1, 0)) :=
    continuous_id.clm_apply continuous_const
  have h₂ : Continuous (fun L : Plane →L[ℝ] Plane => L (0, 1)) :=
    continuous_id.clm_apply continuous_const
  exact (h₁.fst.mul h₂.snd).sub (h₁.snd.mul h₂.fst)

theorem continuous_quarterTurn : Continuous quarterTurn :=
  continuous_snd.neg.prodMk continuous_fst

theorem continuous_linearMap :
    Continuous (linearMap : (Plane × Plane) → (Plane →L[ℝ] Plane)) := by
  exact ((ContinuousLinearMap.smulRightL ℝ Plane Plane
    (ContinuousLinearMap.fst ℝ ℝ ℝ)).continuous.comp continuous_fst).add
      ((ContinuousLinearMap.smulRightL ℝ Plane Plane
        (ContinuousLinearMap.snd ℝ ℝ ℝ)).continuous.comp continuous_snd)

end Wikipedia.SmoothSixDPoincare.PlanarFrame
