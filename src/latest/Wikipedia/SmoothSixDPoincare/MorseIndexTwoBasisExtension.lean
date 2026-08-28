import Wikipedia.SmoothSixDPoincare.MorseIndexTwoHomology
import Mathlib.Data.Fin.VecNotation

/-!
# Extend a native homology basis by the actual index-two collapse coordinate

The previous basis is retained on the zero-new-coordinate subspace. The
new coordinate is measured by the original collapse, not by an abstract
rank choice. This preserves the maps needed for the middle-handle matrices.
-/

noncomputable section

namespace Wikipedia.SmoothSixDPoincare

namespace HomologyTransport

def integerCoordinateSplit (n : ℕ) :
    (Fin (n + 1) → ℤ) ≃+ ((Fin n → ℤ) × ℤ) where
  toFun v := (fun i => v i.succ, v 0)
  invFun v := Fin.cons v.2 v.1
  left_inv v := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv v := rfl
  map_add' _ _ := rfl

end HomologyTransport

namespace ManifoldMorse.MorseSurgeryData

open Set Metric ContinuousMap
open Wikipedia.HopfProblem.SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

theorem exists_indexTwoBasis_extension (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    [Subsingleton (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 1)]
    (n : ℕ)
    (e : (Fin n → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} 2) :
    ∃ H : (Fin (n + 1) → ℤ) ≃ₗ[ℤ] SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} 2,
      (∀ v, H (Fin.cons 0 v) = d.lowerRealizationHomologyMap 2 (e v)) ∧
        ∀ v, d.indexTwoCollapseCoordinate hf hindex (H v) = v 0 := by
  obtain ⟨H, hH, hcoord⟩ := d.exists_indexTwoHomology_split hf hindex
  let G := (HomologyTransport.integerCoordinateSplit n).trans
    ((e.toAddEquiv.prodCongr (AddEquiv.refl ℤ)).trans H.toAddEquiv)
  refine ⟨G.toIntLinearEquiv, ?_, ?_⟩
  · intro v
    exact hH (e v)
  · intro v
    exact hcoord (e (fun i => v i.succ), v 0)

end ManifoldMorse.MorseSurgeryData

end Wikipedia.SmoothSixDPoincare
