import ErdosProblems.Erdos1148.ModularBowenPairs
import ErdosProblems.Erdos1148.ForwardBowenTube

/-! # Forward Bowen pairs as centered Bowen pairs after a half-time translation -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

def modularForwardBowenPairs (η S : ℝ) : Set (ModularOrbitSpace × ModularOrbitSpace) :=
  (Prod.map (modularRightTranslate (diagonalFlow (S / 2)))
    (modularRightTranslate (diagonalFlow (S / 2)))) ⁻¹'
      modularBowenPairs η (η * Real.exp (-(S / 2)))

lemma measurableSet_modularForwardBowenPairs (η S : ℝ) :
    MeasurableSet (modularForwardBowenPairs η S) :=
  (measurableSet_modularBowenPairs _ _).preimage
    ((continuous_modularRightTranslate _).measurable.prodMap
      (continuous_modularRightTranslate _).measurable)

theorem mem_modularForwardBowenPairs_of_lifts {η S : ℝ} (hS : 0 ≤ S) (g h : SL(2, ℝ))
    (hclose : ∀ t ∈ Set.Icc 0 S, EntryCloseOne η
      ((g * diagonalFlow t)⁻¹ * (h * diagonalFlow t))) :
    (modularMk g, modularMk h) ∈ modularForwardBowenPairs η S := by
  refine ⟨g * diagonalFlow (S / 2), h * diagonalFlow (S / 2), rfl, ?_⟩
  apply (entryBowenTube_iff_flow_closeness (by linarith : 0 ≤ S / 2) _).mpr
  intro t ht
  have hs : S / 2 + t ∈ Set.Icc 0 S := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have htime := hclose (S / 2 + t) hs
  have heq :
      diagonalFlow (-t) * ((g * diagonalFlow (S / 2))⁻¹ * (h * diagonalFlow (S / 2))) *
          diagonalFlow t =
        (g * diagonalFlow (S / 2 + t))⁻¹ * (h * diagonalFlow (S / 2 + t)) := by
    rw [diagonalFlow_add, diagonalFlow_neg]
    group
  rw [heq]
  exact htime

theorem modularForwardBowenPairs_mass (μ : Measure ModularOrbitSpace) [SFinite μ]
    (hinv : ∀ t : ℝ, Measure.map (modularRightTranslate (diagonalFlow t)) μ = μ) (η S : ℝ) :
    (μ.prod μ) (modularForwardBowenPairs η S) =
      (μ.prod μ) (modularBowenPairs η (η * Real.exp (-(S / 2)))) := by
  rw [modularForwardBowenPairs, ← Measure.map_apply
    ((continuous_modularRightTranslate _).measurable.prodMap
      (continuous_modularRightTranslate _).measurable) (measurableSet_modularBowenPairs _ _),
    ← Measure.map_prod_map μ μ (continuous_modularRightTranslate _).measurable
      (continuous_modularRightTranslate _).measurable, hinv]

end Erdos1148.DukeArithmetic
