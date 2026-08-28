import Wikipedia.SmoothSixDPoincare.MorseCellHomologyMaps
import Wikipedia.SmoothSixDPoincare.LinearExactTransport

/-!
# The exact singular homology sequence of the original Morse sublevels

All maps are the actual maps constructed from the same Morse surgery.
Transport of the core-cell calculation retains the attaching-sphere map
and the whole-attachment realization of the original lower sublevel.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
theorem morse_exact_at_lower (hf : Continuous f) (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (d.coreBoundaryHomologyMap k) =
      LinearMap.ker (d.lowerRealizationHomologyMap k) := by
  refine HomologyTransport.exact_of_equivalences (LinearEquiv.refl ℤ _)
    (d.cellOldHomologyEquiv hf k).symm (d.cellTotalHomologyEquiv hf k)
    ((d.coreCellPresentation hf).attachingHomologyMap k)
    ((d.coreCellPresentation hf).oldHomologyMap k)
    (d.coreBoundaryHomologyMap k) (d.lowerRealizationHomologyMap k) ?_ ?_
    ((d.coreCellPresentation hf).cell_exact_at_old k hk)
  · intro a
    change d.coreBoundaryHomologyMap k a =
      (d.cellOldHomologyEquiv hf k).symm ((d.coreCellPresentation hf).attachingHomologyMap k a)
    rw [d.cellAttachingHomology_compare, LinearEquiv.symm_apply_apply]
  · intro a
    have h := d.cellOldHomology_compare hf k ((d.cellOldHomologyEquiv hf k).symm a)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm

open Classical in
theorem morse_exact_at_upper (hf : Continuous f) (k : ℕ) :
    LinearMap.range (d.lowerRealizationHomologyMap (k + 1)) =
      LinearMap.ker (d.morseConnectingMap hf k) := by
  refine HomologyTransport.exact_of_equivalences (d.cellOldHomologyEquiv hf (k + 1)).symm
    (d.cellTotalHomologyEquiv hf (k + 1)) (LinearEquiv.refl ℤ _)
    ((d.coreCellPresentation hf).oldHomologyMap (k + 1))
    ((d.coreCellPresentation hf).cellConnectingMap k)
    (d.lowerRealizationHomologyMap (k + 1)) (d.morseConnectingMap hf k) ?_ ?_
    ((d.coreCellPresentation hf).cell_exact_at_ambient k)
  · intro a
    have h := d.cellOldHomology_compare hf (k + 1) ((d.cellOldHomologyEquiv hf (k + 1)).symm a)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  · exact d.morseConnecting_compare hf k

open Classical in
theorem morse_exact_at_attachingSphere (hf : Continuous f) (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (d.morseConnectingMap hf k) = LinearMap.ker (d.coreBoundaryHomologyMap k) := by
  refine HomologyTransport.exact_of_equivalences (d.cellTotalHomologyEquiv hf (k + 1))
    (LinearEquiv.refl ℤ _) (d.cellOldHomologyEquiv hf k).symm
    ((d.coreCellPresentation hf).cellConnectingMap k)
    ((d.coreCellPresentation hf).attachingHomologyMap k)
    (d.morseConnectingMap hf k) (d.coreBoundaryHomologyMap k) ?_ ?_
    ((d.coreCellPresentation hf).cell_exact_at_sphere k hk)
  · exact d.morseConnecting_compare hf k
  · intro a
    change d.coreBoundaryHomologyMap k a =
      (d.cellOldHomologyEquiv hf k).symm ((d.coreCellPresentation hf).attachingHomologyMap k a)
    rw [d.cellAttachingHomology_compare, LinearEquiv.symm_apply_apply]

open Classical in
/-- Vanishing above a surgery and on its attaching sphere forces vanishing below it. -/
theorem lowerHomology_subsingleton_of_upper_and_sphere (hf : Continuous f) (k : ℕ) (hk : k ≠ 0)
    [Subsingleton (SingularHomology {y : M // f y ≤ f p + d.radius ^ 2} k)]
    [Subsingleton (SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) k)] :
    Subsingleton (SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} k) := by
  have hall : ∀ a : SingularHomology {y : M // f y ≤ f p - d.radius ^ 2} k, a = 0 := by
    intro a
    have ha : a ∈ LinearMap.ker (d.lowerRealizationHomologyMap k) := Subsingleton.elim _ _
    rw [← d.morse_exact_at_lower hf k hk] at ha
    obtain ⟨s, hs⟩ := ha
    have hs0 : s = 0 := Subsingleton.elim _ _
    rw [hs0, map_zero] at hs
    exact hs.symm
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
