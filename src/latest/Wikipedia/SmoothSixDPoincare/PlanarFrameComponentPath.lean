import Wikipedia.SmoothSixDPoincare.PlanarFrameCoordinates
import Wikipedia.SmoothSixDPoincare.NonzeroVectorCurveGerms
import Mathlib.Analysis.Convex.PathConnected

/-!
# Construct an actual path inside a planar determinant component

Join the nonzero first columns in the punctured plane. Interpolate the
parallel and signed transverse coefficients of the second column. The
transverse coefficient retains its chosen sign throughout the interval,
so this is a path of actual invertible linear maps.
-/

noncomputable section

open Set Function ContinuousMap Topology
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.PlanarFrame

open PlaneImmersion (Plane linearMap)

/-- The actual open determinant component selected by a nonzero sign multiplier. -/
def determinantComponent (σ : ℝ) : TopologicalSpace.Opens (Plane →L[ℝ] Plane) :=
  ⟨{L | 0 < σ * determinant L},
    isOpen_lt continuous_const (continuous_const.mul continuous_determinant)⟩

theorem first_column_ne_zero {σ : ℝ} (L : determinantComponent σ) :
    (L : Plane →L[ℝ] Plane) (1, 0) ≠ 0 := by
  intro hz
  have h := L.property
  change 0 < σ * area ((L : Plane →L[ℝ] Plane) (1, 0)) ((L : Plane →L[ℝ] Plane) (0, 1)) at h
  rw [hz] at h
  simp [area] at h

theorem signed_transverseCoeff_pos {σ : ℝ} (L : determinantComponent σ) :
    0 < σ * transverseCoeff ((L : Plane →L[ℝ] Plane) (1, 0)) ((L : Plane →L[ℝ] Plane) (0, 1)) := by
  rw [transverseCoeff, ← mul_div_assoc]
  exact div_pos L.property (squareLength_pos (first_column_ne_zero L))

/-- An explicit invertible path connects any two points in the same determinant component. -/
theorem nonempty_path_determinantComponent {σ : ℝ} (a b : determinantComponent σ) :
    Nonempty (Path a b) := by
  have hrank : 1 < Module.rank ℝ Plane := by
    rw [← Module.finrank_eq_rank]
    norm_num [Plane, Module.finrank_prod, Module.finrank_self]
  let : PathConnectedSpace (DiskFraming.puncturedModel Plane) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_compl_singleton_of_one_lt_rank hrank (0 : Plane))
  let a₁ : DiskFraming.puncturedModel Plane :=
    ⟨(a : Plane →L[ℝ] Plane) (1, 0), first_column_ne_zero a⟩
  let b₁ : DiskFraming.puncturedModel Plane :=
    ⟨(b : Plane →L[ℝ] Plane) (1, 0), first_column_ne_zero b⟩
  let γ := PathConnectedSpace.somePath a₁ b₁
  let v : unitInterval → Plane := fun t => (γ t : Plane)
  have hv : Continuous v := continuous_subtype_val.comp γ.continuous
  have hvne (t : unitInterval) : v t ≠ 0 := (γ t).property
  let α₀ := parallelCoeff ((a : Plane →L[ℝ] Plane) (1, 0)) ((a : Plane →L[ℝ] Plane) (0, 1))
  let α₁ := parallelCoeff ((b : Plane →L[ℝ] Plane) (1, 0)) ((b : Plane →L[ℝ] Plane) (0, 1))
  let β₀ := transverseCoeff ((a : Plane →L[ℝ] Plane) (1, 0)) ((a : Plane →L[ℝ] Plane) (0, 1))
  let β₁ := transverseCoeff ((b : Plane →L[ℝ] Plane) (1, 0)) ((b : Plane →L[ℝ] Plane) (0, 1))
  let α (t : unitInterval) : ℝ := (1 - (t : ℝ)) * α₀ + (t : ℝ) * α₁
  let β (t : unitInterval) : ℝ := (1 - (t : ℝ)) * β₀ + (t : ℝ) * β₁
  have hα : Continuous α :=
    ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)
  have hβ : Continuous β :=
    ((continuous_const.sub continuous_subtype_val).mul continuous_const).add
      (continuous_subtype_val.mul continuous_const)
  have hβpos (t : unitInterval) : 0 < σ * β t := by
    have hpos : 0 < (1 - (t : ℝ)) * (σ * β₀) + (t : ℝ) * (σ * β₁) :=
      (convex_Ioi (0 : ℝ)) (signed_transverseCoeff_pos a) (signed_transverseCoeff_pos b)
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)
    have heq : σ * β t = (1 - (t : ℝ)) * (σ * β₀) + (t : ℝ) * (σ * β₁) := by
      dsimp only [β]
      ring
    rwa [heq]
  let F (t : unitInterval) : Plane →L[ℝ] Plane :=
    linearMap (v t, α t • v t + β t • quarterTurn (v t))
  have hF : Continuous F := continuous_linearMap.comp
    (hv.prodMk ((hα.smul hv).add (hβ.smul (continuous_quarterTurn.comp hv))))
  have hcomponent (t : unitInterval) : F t ∈ determinantComponent σ := by
    change 0 < σ * determinant (linearMap (v t, α t • v t + β t • quarterTurn (v t)))
    rw [determinant_linearMap, area_transverse, ← mul_assoc]
    exact mul_pos (hβpos t) (squareLength_pos (hvne t))
  have hv0 : v 0 = (a : Plane →L[ℝ] Plane) (1, 0) := congrArg Subtype.val γ.source
  have hv1 : v 1 = (b : Plane →L[ℝ] Plane) (1, 0) := congrArg Subtype.val γ.target
  have hF0 : F 0 = (a : Plane →L[ℝ] Plane) := by
    change linearMap (v 0, α 0 • v 0 + β 0 • quarterTurn (v 0)) = _
    have hα0 : α 0 = α₀ := by simp [α]
    have hβ0 : β 0 = β₀ := by simp [β]
    rw [hv0, hα0, hβ0, decompose_second_column (first_column_ne_zero a)]
    exact linearMap_columns a
  have hF1 : F 1 = (b : Plane →L[ℝ] Plane) := by
    change linearMap (v 1, α 1 • v 1 + β 1 • quarterTurn (v 1)) = _
    have hα1 : α 1 = α₁ := by simp [α]
    have hβ1 : β 1 = β₁ := by simp [β]
    rw [hv1, hα1, hβ1, decompose_second_column (first_column_ne_zero b)]
    exact linearMap_columns b
  exact ⟨{
    toFun := fun t => ⟨F t, hcomponent t⟩
    continuous_toFun := hF.subtype_mk hcomponent
    source' := Subtype.ext hF0
    target' := Subtype.ext hF1 }⟩

end Wikipedia.SmoothSixDPoincare.PlanarFrame
