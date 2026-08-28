import Wikipedia.HopfProblem.DegreeCollapsePassageRetimingDerivative

/-!
# Extract the shared source and normal frames from one transverse passage

An actual bijective three-dimensional normal derivative factors through
the common source and target linear maps. Equal dimensions force those
maps themselves to be equivalences, retaining their literal coefficients.
-/

noncomputable section

open Function

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "D₂" => EuclideanSpace ℝ (Fin 2)
local notation "P₃" => EuclideanSpace ℝ (Fin 3)

variable {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]

theorem exists_shared_passage_frames
    (P : P₃ →L[ℝ] (ℝ × D₂)) (B : (ℝ × D₂) →L[ℝ] N)
    (Q : (ℝ × D₂) ≃L[ℝ] (ℝ × D₂))
    (hdim : Module.finrank ℝ N = 3)
    (hbij : Bijective (B.comp (Q.toContinuousLinearMap.comp P))) :
    ∃ (P' : P₃ ≃L[ℝ] (ℝ × D₂)) (B' : (ℝ × D₂) ≃L[ℝ] N),
      P'.toContinuousLinearMap = P ∧ B'.toContinuousLinearMap = B := by
  have hPi : Injective P := by
    intro x y hxy
    apply hbij.injective
    change B (Q (P x)) = B (Q (P y))
    rw [hxy]
  have hBs : Surjective B := by
    intro y
    obtain ⟨x, hx⟩ := hbij.surjective y
    exact ⟨Q (P x), hx⟩
  have hdimP : Module.finrank ℝ P₃ = Module.finrank ℝ (ℝ × D₂) := by
    simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin]
  have hdimB : Module.finrank ℝ (ℝ × D₂) = Module.finrank ℝ N := by
    simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin, hdim]
  have hPb : Bijective P :=
    ⟨hPi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimP).mp hPi⟩
  have hBb : Bijective B :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimB).mpr hBs, hBs⟩
  exact ⟨(LinearEquiv.ofBijective P.toLinearMap hPb).toContinuousLinearEquiv,
    (LinearEquiv.ofBijective B.toLinearMap hBb).toContinuousLinearEquiv, rfl, rfl⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
