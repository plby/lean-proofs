import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowupH1Cousin
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowupH1Sections
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Cech

/-!
# Solving genuine holomorphic sheaf cocycles on the affine blowup

Actual sheaf sections supply the analytic transition functions of the
proved arbitrary-cover Cousin theorem. Its solutions are bundled back
into sections on exactly the original open cover.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupH1

open AffineBlowup ToricCharts HolomorphicFunctionSheaf.SphereH1

variable {ι : Type} {U : ι → Opens Space}

def cocycleSection (c : CechOneCocycle blowupSheaf U) (i j : ι) :
    HolomorphicFunctionSheaf.Section 𝓘(ℂ, CoordinateSpace 2) Space (U i ⊓ U j) :=
  c.value i j

theorem cocycleSection_condition (c : CechOneCocycle blowupSheaf U)
    (i j k : ι) (x : Space) (hi : x ∈ U i) (hj : x ∈ U j) (hk : x ∈ U k) :
    cocycleSection c i j ⟨x, hi, hj⟩ + cocycleSection c j k ⟨x, hj, hk⟩ =
      cocycleSection c i k ⟨x, hi, hk⟩ := by
  exact congrArg
    (fun s : HolomorphicFunctionSheaf.Section 𝓘(ℂ, CoordinateSpace 2) Space
      ((U i ⊓ U j) ⊓ U k) => s ⟨x, ⟨hi, hj⟩, hk⟩) (c.condition i j k)

def cocycleCoefficient (c : CechOneCocycle blowupSheaf U) (i j : ι) : Space → ℂ :=
  sectionExtension (U i ⊓ U j) (cocycleSection c i j)

theorem cocycleCoefficient_holomorphic (c : CechOneCocycle blowupSheaf U) (i j : ι) :
    ContMDiffOn 𝓘(ℂ, CoordinateSpace 2) 𝓘(ℂ) ω (cocycleCoefficient c i j)
      ((U i : Set Space) ∩ U j) :=
  sectionExtension_holomorphic (U i ⊓ U j) (cocycleSection c i j)

theorem cocycleCoefficient_condition (c : CechOneCocycle blowupSheaf U)
    (i j k : ι) (x : Space) (hi : x ∈ U i) (hj : x ∈ U j) (hk : x ∈ U k) :
    cocycleCoefficient c i j x + cocycleCoefficient c j k x =
      cocycleCoefficient c i k x := by
  simp only [cocycleCoefficient,
    sectionExtension_apply (U i ⊓ U j) (cocycleSection c i j) x ⟨hi, hj⟩,
    sectionExtension_apply (U j ⊓ U k) (cocycleSection c j k) x ⟨hj, hk⟩,
    sectionExtension_apply (U i ⊓ U k) (cocycleSection c i k) x ⟨hi, hk⟩]
  exact cocycleSection_condition c i j k x hi hj hk

/-- Every genuine holomorphic one-cocycle on every actual open cover of
the incidence blowup is a coboundary of actual holomorphic sections. -/
theorem blowup_cechOneVanishing : CechOneVanishing blowupSheaf := by
  intro ι U hcover c
  obtain ⟨s, hs, hsub⟩ := exists_holomorphic_cocycle_cochain
    (fun i => (U i).isOpen) hcover
    (cocycleCoefficient_holomorphic c) (cocycleCoefficient_condition c)
  refine ⟨fun i => sectionOfHolomorphic (U i) (s i) (hs i), ?_⟩
  intro i j
  apply ContMDiffMap.ext
  rintro ⟨x, hi, hj⟩
  change s i x - s j x = cocycleSection c i j ⟨x, hi, hj⟩
  exact (hsub i j x hi hj).trans
    (sectionExtension_apply (U i ⊓ U j) (cocycleSection c i j) x ⟨hi, hj⟩)

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupH1
