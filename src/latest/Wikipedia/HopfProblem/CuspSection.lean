import Wikipedia.HopfProblem.CuspStrata

/-!
# The section through the smooth part of the cusp fibre

The explicit toric point `(t,1,1)` gives a section over the whole cusp
disc, not just its puncture.  Its quotient is a holomorphic closed
embedding and meets the central fibre at a one-branch point.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.CuspQuotient

open ToricCharts ToricFan ToricSpace

local notation "I₃" => modelWithCornersSelf ℂ (CoordinateSpace 3)
local notation "I₁" => modelWithCornersSelf ℂ ℂ

def sectionCoordinates (t : ℂ) : CoordinateSpace 3 := ![t, 1, 1]

@[simp] theorem time_sectionCoordinates (t : ℂ) : Triangle.time (sectionCoordinates t) = t := by
  simp [Triangle.time, sectionCoordinates]

theorem sectionCoordinates_holomorphic : ContDiff ℂ ω sectionCoordinates := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_id
  · exact contDiff_const
  · exact contDiff_const

/-- A lift of the section to the actual open toric tube. -/
def sectionLift (ε : ℝ) (t : disc ε) : Tube (disc ε) :=
  ⟨inclusion referenceTriangle (sectionCoordinates t), by
    change time (inclusion referenceTriangle (sectionCoordinates t)) ∈ disc ε
    simpa only [time_inclusion, time_sectionCoordinates] using t.2⟩

theorem sectionLift_continuous (ε : ℝ) : Continuous (sectionLift ε) :=
  (((inclusion_openEmbedding referenceTriangle).continuous.comp
    sectionCoordinates_holomorphic.continuous).comp continuous_subtype_val).subtype_mk _

theorem sectionLift_holomorphic (ε : ℝ) : ContMDiff I₁ I₃ ω (sectionLift ε) := by
  intro t
  have he : ContMDiffAt I₁ I₃ ω (fun r => (sectionLift ε r : Space)) t ↔
      ContMDiffAt I₁ I₃ ω (sectionLift ε) t :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (((inclusion_holomorphic referenceTriangle).comp
    sectionCoordinates_holomorphic.contMDiff).comp contMDiff_subtype_val t)

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)

/-- The extended zero section in the cusp quotient. -/
def zeroSection : disc ε → QuotientSpace C ε := quotientMap C ε ∘ sectionLift ε

@[simp] theorem projection_zeroSection (t : disc ε) : projection C ε (zeroSection C ε t) = t := by
  change time (inclusion referenceTriangle (sectionCoordinates t)) = t
  simp

@[simp] theorem baseMap_zeroSection (t : disc ε) : baseMap C ε (zeroSection C ε t) = t :=
  Subtype.ext (projection_zeroSection C ε t)

theorem baseMap_leftInverse_zeroSection : Function.LeftInverse (baseMap C ε) (zeroSection C ε) :=
  baseMap_zeroSection C ε

theorem zeroSection_continuous : Continuous (zeroSection C ε) :=
  (quotientMap_continuous C ε).comp (sectionLift_continuous ε)

theorem zeroSection_injective : Function.Injective (zeroSection C ε) :=
  (baseMap_leftInverse_zeroSection C ε).injective

theorem zeroSection_isEmbedding : IsEmbedding (zeroSection C ε) :=
  (baseMap_leftInverse_zeroSection C ε).isEmbedding
    (baseMap_continuous C ε) (zeroSection_continuous C ε)

theorem zeroSection_holomorphic (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    ContMDiff I₁ I₃ ω (zeroSection C ε) := by
  let := chartedSpace C ε hε hε1 hC hR
  exact (quotientMap_holomorphic C ε hε hε1 hC hR).comp (sectionLift_holomorphic ε)

/-- The disc is closed in the quotient because it is a continuous section
of the base projection and the quotient is Hausdorff. -/
theorem zeroSection_isClosedEmbedding (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) : IsClosedEmbedding (zeroSection C ε) := by
  let := quotient_t2Space C ε hε hε1 hC hR
  exact (baseMap_leftInverse_zeroSection C ε).isClosedEmbedding
    (baseMap_continuous C ε) (zeroSection_continuous C ε)

/-- The section has just one vanishing boundary coordinate at zero and
none away from zero. -/
theorem branchCount_zeroSection (t : disc ε) :
    branchCount C ε (zeroSection C ε t) = if (t : ℂ) = 0 then 1 else 0 := by
  classical
  change ToricSpace.branchCount (inclusion referenceTriangle (sectionCoordinates t)) = _
  rw [ToricSpace.branchCount_inclusion, ← vanishingIndices_card]
  by_cases ht : (t : ℂ) = 0
  · have hJ : vanishingIndices (sectionCoordinates t) = {0} := by
      ext i
      fin_cases i <;> simp [sectionCoordinates, ht]
    rw [hJ]
    simp [ht]
  · have hJ : vanishingIndices (sectionCoordinates t) = ∅ := by
      ext i
      fin_cases i <;> simp [sectionCoordinates, ht]
    rw [hJ]
    simp [ht]

/-- The central fibre meets the section in exactly its value at zero. -/
theorem zeroSection_central_intersection (hε : 0 < ε) :
    range (zeroSection C ε) ∩ projection C ε ⁻¹' {0} =
      {zeroSection C ε ⟨0, by simpa [disc] using hε⟩} := by
  ext x
  constructor
  · rintro ⟨⟨t, rfl⟩, ht⟩
    have ht0 : (t : ℂ) = 0 := by simpa using ht
    exact congrArg (zeroSection C ε) (Subtype.ext ht0)
  · rintro rfl
    exact ⟨mem_range_self _, by simp⟩

end Wikipedia.HopfProblem.CuspQuotient
