import ErdosProblems.Erdos486.BiasedFiniteBlock
import ErdosProblems.Erdos486.BiasedRecovery
import ErdosProblems.Erdos486.BiasedSummability

/- Ported to Lean/Mathlib 4.33.0; see README.md for source and modifications. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The concrete block interface for Erdős problem 486

We choose one of the finite colourings supplied at every sufficiently large
scale, enlarge the first scale until the summable error tail is below `1/100`,
and package the resulting arithmetic blocks into `DyadicBlockInterface`.
-/

open Filter Set
open scoped BigOperators

namespace Erdos486

noncomputable section

/-- A deterministic colouring chosen from the finite averaging theorem at
large scales.  Values below the arithmetic cutoff are irrelevant to the
geometry, so we use the constant colouring there. -/
def chosenBiasedColoring (j : ℕ) : BiasedColoring j :=
  if hj : 400 ≤ j then
    Classical.choose (exists_biasedColoring_footprint_le hj)
  else
    fun _ ↦ 0

theorem chosenBiasedColoring_footprint_le_eta_of_large {j : ℕ}
    (hj : 400 ≤ j) :
    biasedFootprint j (chosenBiasedColoring j) ≤ biasedEta j := by
  rw [chosenBiasedColoring, dif_pos hj]
  exact Classical.choose_spec (exists_biasedColoring_footprint_le hj)

/-- The chosen footprint is bounded by `biasedEta` at every index.  Below
`400`, the radius is zero, so `biasedEta = 3`, while every footprint is at
most one. -/
theorem chosenBiasedColoring_footprint_le_eta (j : ℕ) :
    biasedFootprint j (chosenBiasedColoring j) ≤ biasedEta j := by
  by_cases hj : 400 ≤ j
  · exact chosenBiasedColoring_footprint_le_eta_of_large hj
  · have hjlt : j < 400 := Nat.lt_of_not_ge hj
    have hsqrt : Nat.sqrt j < 20 := by
      rw [Nat.sqrt_lt]
      omega
    have hradius : biasedRadius j = 0 := by
      simp [biasedRadius, Nat.div_eq_of_lt hsqrt]
    calc
      biasedFootprint j (chosenBiasedColoring j) ≤ 1 :=
        biasedFootprint_le_one j (chosenBiasedColoring j)
      _ ≤ biasedEta j := by simp [biasedEta, hradius]

/-- A cutoff whose entire finite tail has total error at most `1/100`. -/
def biasedTailCutoff : ℕ :=
  Classical.choose exists_biasedEta_tail_finset_le

theorem biasedTailCutoff_spec (s : Finset ℕ)
    (hs : ∀ j ∈ s, biasedTailCutoff ≤ j) :
    (∑ j ∈ s, biasedEta j) ≤ (1 : ℝ) / 100 :=
  Classical.choose_spec exists_biasedEta_tail_finset_le s hs

/-- The final first scale combines the arithmetic and analytic cutoffs. -/
def erdos486FirstScale : ℕ :=
  max 400 biasedTailCutoff

theorem four_hundred_le_erdos486FirstScale : 400 ≤ erdos486FirstScale :=
  Nat.le_max_left _ _

theorem biasedTailCutoff_le_erdos486FirstScale :
    biasedTailCutoff ≤ erdos486FirstScale :=
  Nat.le_max_right _ _

/-- The concrete coloured block geometry used in the counterexample. -/
def erdos486Geometry : DyadicBlockGeometry :=
  biasedColoredGeometryAbove erdos486FirstScale
    four_hundred_le_erdos486FirstScale chosenBiasedColoring

/-- The biased construction supplies every field of the abstract block
interface. -/
def erdos486BlockInterface : DyadicBlockInterface where
  geometry := erdos486Geometry
  footprint := biasedEta
  footprint_nonneg := biasedEta_nonneg
  summable_footprint := summable_biasedEta
  tail_budget := by
    intro J hJ
    apply biasedTailCutoff_spec J
    intro j hj
    exact biasedTailCutoff_le_erdos486FirstScale.trans (hJ j hj)
  finite_recovery := by
    intro J
    obtain ⟨d, hd, hlower⟩ := biasedColored_finite_recovery
      erdos486FirstScale four_hundred_le_erdos486FirstScale
      chosenBiasedColoring J
    refine ⟨d, ?_, ?_⟩
    · simpa [erdos486Geometry] using hd
    · have hsum :
          (∑ j ∈ J, biasedFootprint j (chosenBiasedColoring j)) ≤
            ∑ j ∈ J, biasedEta j := by
        exact Finset.sum_le_sum fun j _hj ↦
          chosenBiasedColoring_footprint_le_eta j
      exact (sub_le_sub_left hsum 1).trans hlower

end

end Erdos486
