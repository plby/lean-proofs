import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyFibreInclusion
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyMayerVietoris

/-!
# Actual fibre homology in the regular-family Mayer--Vietoris sequence

The genuine homotopies of the inverse cover markings to the original fibre
inclusion identify both cover maps on singular homology. In these markings
the right Mayer--Vietoris map is the fibre inclusion applied to the sum.
Consequently its image is exactly the actual fibre image, and exactness
describes both this image and the kernel of the fibre homology map.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology

variable (D : Data ℂ TriangleRegularPoint) (b : SlitBaseLift)

/-- The upper inverse marking followed by inclusion induces the actual fibre homology map. -/
theorem upperFamilyInclusion_homology_symm (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    singularHomologyMap (upperFamilyInclusion D) n ((upperHomologyEquiv D b n).symm a) =
      singularHomologyMap (familyFibreInclusion D b) n a := by
  change singularHomologyMap (upperFamilyInclusion D) n
      (singularHomologyMap (upperHomotopyEquiv D b).invFun n a) = _
  exact LinearMap.congr_fun
    ((singularHomologyMap_comp (upperHomotopyEquiv D b).invFun
      (upperFamilyInclusion D) n).symm.trans
        (homotopy_homologyMap (upperFamilyFibreHomotopy D b) n)) a

/-- The lower inverse marking induces the same original fibre homology map. -/
theorem lowerFamilyInclusion_homology_symm (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    singularHomologyMap (lowerFamilyInclusion D) n ((lowerHomologyEquiv D b n).symm a) =
      singularHomologyMap (familyFibreInclusion D b) n a := by
  change singularHomologyMap (lowerFamilyInclusion D) n
      (singularHomologyMap (lowerHomotopyEquiv D b).invFun n a) = _
  exact LinearMap.congr_fun
    ((singularHomologyMap_comp (lowerHomotopyEquiv D b).invFun
      (lowerFamilyInclusion D) n).symm.trans
        (homotopy_homologyMap (lowerFamilyFibreHomotopy D b) n)) a

/-- The inverse pair marking consists of the two inverse homology markings. -/
@[simp] theorem pairHomologyEquiv_symm_apply (n : ℕ)
    (a : SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) :
    (pairHomologyEquiv D b n).symm a =
      ((upperHomologyEquiv D b n).symm a.1, (lowerHomologyEquiv D b n).symm a.2) := rfl

/-- In actual torus markings the right Mayer--Vietoris map is the fibre map of the sum. -/
theorem familyRightHomologyMap_pair_symm (n : ℕ)
    (a : SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) :
    familyRightHomologyMap D n ((pairHomologyEquiv D b n).symm a) =
      singularHomologyMap (familyFibreInclusion D b) n (a.1 + a.2) := by
  refine (rightHomologyMap_apply (upperFamily D : Set D.Space) (lowerFamily D) n
    ((pairHomologyEquiv D b n).symm a)).trans ?_
  change singularHomologyMap (upperFamilyInclusion D) n
        ((upperHomologyEquiv D b n).symm a.1) +
      singularHomologyMap (lowerFamilyInclusion D) n
        ((lowerHomologyEquiv D b n).symm a.2) = _
  rw [upperFamilyInclusion_homology_symm, lowerFamilyInclusion_homology_symm, map_add]

/-- The same formula evaluated on an arbitrary pair of actual cover classes. -/
theorem familyRightHomologyMap_pair (n : ℕ)
    (a : SingularHomology (upperFamily D) n × SingularHomology (lowerFamily D) n) :
    familyRightHomologyMap D n a =
      singularHomologyMap (familyFibreInclusion D b) n
        ((pairHomologyEquiv D b n a).1 + (pairHomologyEquiv D b n a).2) := by
  simpa only [LinearEquiv.symm_apply_apply] using
    familyRightHomologyMap_pair_symm D b n (pairHomologyEquiv D b n a)

/-- The actual right Mayer--Vietoris image is exactly the actual fibre image. -/
theorem familyRightHomologyMap_range_eq_fibre (n : ℕ) :
    LinearMap.range (familyRightHomologyMap D n) =
      LinearMap.range (singularHomologyMap (familyFibreInclusion D b) n) := by
  apply le_antisymm
  · rintro y ⟨a, rfl⟩
    refine ⟨(pairHomologyEquiv D b n a).1 + (pairHomologyEquiv D b n a).2, ?_⟩
    exact (familyRightHomologyMap_pair D b n a).symm
  · rintro y ⟨a, rfl⟩
    refine ⟨(pairHomologyEquiv D b n).symm (a, 0), ?_⟩
    simpa only [add_zero] using familyRightHomologyMap_pair_symm D b n (a, 0)

/-- The connecting homomorphism vanishes precisely on the actual fibre image. -/
theorem familyConnectingHomomorphism_ker_eq_fibre (n : ℕ) :
    LinearMap.ker (familyConnectingHomomorphism D n) =
      LinearMap.range (singularHomologyMap (familyFibreInclusion D b) (n + 1)) :=
  (LinearMap.exact_iff.mp (family_exact_at_ambient D n)).trans
    (familyRightHomologyMap_range_eq_fibre D b (n + 1))

/-- A fibre class dies in the actual family exactly when its marked upper
representative lies in the image of the actual intersection map. -/
theorem familyFibreInclusion_homology_zero_iff (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    singularHomologyMap (familyFibreInclusion D b) n a = 0 ↔
      (pairHomologyEquiv D b n).symm (a, 0) ∈ LinearMap.range (familyLeftHomologyMap D n) := by
  rw [← (LinearMap.exact_iff.mp (family_exact_at_pair D n))]
  change singularHomologyMap (familyFibreInclusion D b) n a = 0 ↔
    familyRightHomologyMap D n ((pairHomologyEquiv D b n).symm (a, 0)) = 0
  rw [familyRightHomologyMap_pair_symm, add_zero]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
