import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Actual coordinates adapted to a finite-rank operator

Complement the actual kernel and range. The restriction from the kernel
complement to the range is an equivalence. After the specified dimension
identifications, the original operator becomes the identity on its leading
coordinates and zero on the remaining coordinates.
-/

noncomputable section

open Function Module

namespace NoExoticSixSphere.OperatorRank

variable {V W E N F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_coordinates (L : V →L[ℝ] W)
    (hr : finrank ℝ L.range = finrank ℝ E)
    (hv : finrank ℝ V = finrank ℝ E + finrank ℝ N)
    (hw : finrank ℝ W = finrank ℝ E + finrank ℝ F) :
    ∃ u : V ≃L[ℝ] E × N, ∃ v : W ≃L[ℝ] E × F,
      ∀ x y, v (L (u.symm (x, y))) = (x, 0) := by
  obtain ⟨C, hC⟩ := L.ker.exists_isCompl
  obtain ⟨D, hD⟩ := L.range.exists_isCompl
  let e : C ≃L[ℝ] L.range :=
    (L.toLinearMap.kerComplementEquivRange hC.symm).toContinuousLinearEquiv
  have hCr : finrank ℝ C = finrank ℝ E := e.toLinearEquiv.finrank_eq.trans hr
  have hKr : finrank ℝ L.ker = finrank ℝ N := by
    have h := L.toLinearMap.finrank_range_add_finrank_ker
    omega
  have hDr : finrank ℝ D = finrank ℝ F := by
    have h := Submodule.finrank_add_eq_of_isCompl hD
    omega
  let a : C ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq hCr
  let b : L.ker ≃L[ℝ] N := ContinuousLinearEquiv.ofFinrankEq hKr
  let c : L.range ≃L[ℝ] E := e.symm.trans a
  let d : D ≃L[ℝ] F := ContinuousLinearEquiv.ofFinrankEq hDr
  let s : (C × L.ker) ≃L[ℝ] V :=
    (C.prodEquivOfIsCompl L.ker hC.symm).toContinuousLinearEquiv
  let t : (L.range × D) ≃L[ℝ] W :=
    (L.range.prodEquivOfIsCompl D hD).toContinuousLinearEquiv
  let u : V ≃L[ℝ] E × N := s.symm.trans (a.prodCongr b)
  let v : W ≃L[ℝ] E × F := t.symm.trans (c.prodCongr d)
  have ht (z : L.range) : t.symm (z : W) = (z, 0) :=
    Submodule.prodEquivOfIsCompl_symm_apply_left L.range D hD z
  have he (z : C) : (e z : W) = L z := rfl
  refine ⟨u, v, ?_⟩
  intro x y
  have hk : L (b.symm y : V) = 0 := (b.symm y).property
  have hinput : L (u.symm (x, y)) = (e (a.symm x) : W) := by
    change L ((a.symm x : V) + (b.symm y : V)) = _
    rw [map_add, hk, add_zero, he]
  change (c.prodCongr d) (t.symm (L (u.symm (x, y)))) = (x, 0)
  rw [hinput, ht]
  simp [c]

end NoExoticSixSphere.OperatorRank
