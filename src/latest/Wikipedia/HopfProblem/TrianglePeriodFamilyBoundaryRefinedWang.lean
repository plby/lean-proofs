import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryRefinedWangHomology
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologySourceSequence

/-!
# Actual refined Wang-to-regular-family comparison

A continuous boundary map that carries the genuinely smaller mapping-torus
arcs into the two actual family slits induces an actual connecting-map
comparison. Identity-refinement naturality identifies the source connecting
class with the original signed Wang pair. Both comparison columns are the
literal geometric maps at one quarter and three quarters, retaining all
fibre dependence and the original source-kernel orientation change.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.RefinedWang

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology Homology

variable {X : Type} [TopologicalSpace X]
  (D : Data ℂ TriangleRegularPoint) (φ : X ≃ₜ X)
  (F : C(MappingTorus.Torus φ, D.Space))
  (hU : Set.MapsTo F (U φ) (upperFamily D))
  (hV : Set.MapsTo F (V φ) (lowerFamily D))

/-- The literal boundary map restricted to the genuine refined intersection. -/
def intersectionMap :
    C((U φ ∩ V φ : Set (MappingTorus.Torus φ)), familyIntersection D) :=
  intersectionRestriction F (U φ) (V φ) (upperFamily D) (lowerFamily D) hU hV

@[simp] theorem intersectionMap_apply
    (x : (U φ ∩ V φ : Set (MappingTorus.Torus φ))) :
    (intersectionMap D φ F hU hV x).val = F x.val := rfl

/-- Naturality of the actual connecting maps for the smaller source cover. -/
theorem markedConnecting_naturality (b : SlitBaseLift) (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    familyMarkedConnecting D b n (singularHomologyMap F (n + 1) a) =
      Homology.intersectionHomologyEquiv D b n
        (singularHomologyMap (intersectionMap D φ F hU hV) n
          (mayerVietorisConnecting φ n a)) := by
  have h := connectingHomomorphism_naturality_apply F (U φ) (V φ)
    (upperFamily D) (lowerFamily D) hU hV (U_open φ) (V_open φ) (cover φ)
    (upperFamily D).isOpen (lowerFamily D).isOpen (upperFamily_union_lowerFamily D) n a
  exact (congrArg (Homology.intersectionHomologyEquiv D b n) h).symm

/-- The actual intersection map in its two source and three target component coordinates. -/
def intersectionComparison (b : SlitBaseLift) (n : ℕ) :
    (SingularHomology X n × SingularHomology X n) →ₗ[ℤ]
      (SingularHomology RealTorus₄ n ×
        (SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n)) :=
  (Homology.intersectionHomologyEquiv D b n).toLinearMap.comp
    ((singularHomologyMap (intersectionMap D φ F hU hV) n).comp
      (intersectionHomologyEquiv φ n).symm.toLinearMap)

@[simp] theorem intersectionComparison_apply (b : SlitBaseLift) (n : ℕ)
    (a : SingularHomology X n × SingularHomology X n) :
    intersectionComparison D φ F hU hV b n a =
      Homology.intersectionHomologyEquiv D b n
        (singularHomologyMap (intersectionMap D φ F hU hV) n
          ((intersectionHomologyEquiv φ n).symm a)) := rfl

/-- The original Wang boundary controls the actual regular-family connecting map. -/
theorem markedConnecting_wangBoundary (b : SlitBaseLift) (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    familyMarkedConnecting D b n (singularHomologyMap F (n + 1) a) =
      intersectionComparison D φ F hU hV b n
        (-MappingTorusHomology.wangBoundary φ n a, MappingTorusHomology.wangBoundary φ n a) := by
  refine (markedConnecting_naturality D φ F hU hV b n a).trans ?_
  exact congrArg
    (fun z => Homology.intersectionHomologyEquiv D b n
      (singularHomologyMap (intersectionMap D φ F hU hV) n z))
    (mappingTorusConnecting_eq_marked_boundary φ n a)

/-- The source-kernel projection retains the original proved orientation change. -/
theorem sourceKernelProjection_wangBoundary (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    (sourceKernelProjection D n (singularHomologyMap F (n + 1) a) :
      SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) =
      normalizedSourceDomainEquiv n
        (intersectionComparison D φ F hU hV normalizedSlitBaseLift n
          (-MappingTorusHomology.wangBoundary φ n a,
            MappingTorusHomology.wangBoundary φ n a)).2 := by
  exact congrArg
    (fun z : SingularHomology RealTorus₄ n ×
      (SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) =>
        normalizedSourceDomainEquiv n z.2)
    (markedConnecting_wangBoundary D φ F hU hV normalizedSlitBaseLift n a)

/-- The signed boundary pair is the difference of the two genuine component columns. -/
theorem intersectionComparison_antidiagonal (b : SlitBaseLift) (n : ℕ)
    (a : SingularHomology X n) :
    intersectionComparison D φ F hU hV b n (-a, a) =
      -intersectionComparison D φ F hU hV b n (a, 0) +
        intersectionComparison D φ F hU hV b n (0, a) := by
  have h : (-a, a) = -(a, (0 : SingularHomology X n)) + (0, a) := by
    ext <;> simp
  rw [h, map_add, map_neg]

/-- The actual boundary map at the refined lower component's quarter-time fibre. -/
def lowerColumnMap : C(X, familyIntersection D) :=
  (intersectionMap D φ F hU hV).comp (lowerComponentFibre φ)

/-- The actual boundary map at the refined upper component's three-quarter-time fibre. -/
def upperColumnMap : C(X, familyIntersection D) :=
  (intersectionMap D φ F hU hV).comp (upperComponentFibre φ)

@[simp] theorem lowerColumnMap_coe (x : X) :
    (lowerColumnMap D φ F hU hV x).val = F (MappingTorus.mk φ (1 / 4, x)) := by
  change F (lowerComponentFibre φ x).val = _
  rw [lowerComponentFibre_coe]

@[simp] theorem upperColumnMap_coe (x : X) :
    (upperColumnMap D φ F hU hV x).val = F (MappingTorus.mk φ (3 / 4, x)) := by
  change F (upperComponentFibre φ x).val = _
  rw [upperComponentFibre_coe]

/-- The first comparison column is induced by the actual quarter-time map. -/
theorem intersectionComparison_lowerColumn (b : SlitBaseLift) (n : ℕ)
    (a : SingularHomology X n) :
    intersectionComparison D φ F hU hV b n (a, 0) =
      Homology.intersectionHomologyEquiv D b n
        (singularHomologyMap (lowerColumnMap D φ F hU hV) n a) := by
  rw [intersectionComparison_apply, intersectionHomologyEquiv_symm_lower]
  exact congrArg (Homology.intersectionHomologyEquiv D b n)
    (LinearMap.congr_fun
      (singularHomologyMap_comp (lowerComponentFibre φ) (intersectionMap D φ F hU hV) n) a).symm

/-- The second comparison column is induced by the actual three-quarter-time map. -/
theorem intersectionComparison_upperColumn (b : SlitBaseLift) (n : ℕ)
    (a : SingularHomology X n) :
    intersectionComparison D φ F hU hV b n (0, a) =
      Homology.intersectionHomologyEquiv D b n
        (singularHomologyMap (upperColumnMap D φ F hU hV) n a) := by
  rw [intersectionComparison_apply, intersectionHomologyEquiv_symm_upper]
  exact congrArg (Homology.intersectionHomologyEquiv D b n)
    (LinearMap.congr_fun
      (singularHomologyMap_comp (upperComponentFibre φ) (intersectionMap D φ F hU hV) n) a).symm

/-- Every actual connecting class is the signed difference of the actual quarter-time columns. -/
theorem markedConnecting_quarterColumns (b : SlitBaseLift) (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    familyMarkedConnecting D b n (singularHomologyMap F (n + 1) a) =
      -Homology.intersectionHomologyEquiv D b n
        (singularHomologyMap (lowerColumnMap D φ F hU hV) n
          (MappingTorusHomology.wangBoundary φ n a)) +
      Homology.intersectionHomologyEquiv D b n
        (singularHomologyMap (upperColumnMap D φ F hU hV) n
          (MappingTorusHomology.wangBoundary φ n a)) := by
  rw [markedConnecting_wangBoundary D φ F hU hV b n a,
    intersectionComparison_antidiagonal, intersectionComparison_lowerColumn,
    intersectionComparison_upperColumn]

/-- The literal source-kernel projection in terms of those two genuine geometric columns. -/
theorem sourceKernelProjection_quarterColumns (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    (sourceKernelProjection D n (singularHomologyMap F (n + 1) a) :
      SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) =
      normalizedSourceDomainEquiv n
        (-Homology.intersectionHomologyEquiv D normalizedSlitBaseLift n
          (singularHomologyMap (lowerColumnMap D φ F hU hV) n
            (MappingTorusHomology.wangBoundary φ n a)) +
        Homology.intersectionHomologyEquiv D normalizedSlitBaseLift n
          (singularHomologyMap (upperColumnMap D φ F hU hV) n
            (MappingTorusHomology.wangBoundary φ n a))).2 := by
  exact congrArg
    (fun z : SingularHomology RealTorus₄ n ×
      (SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) =>
        normalizedSourceDomainEquiv n z.2)
    (markedConnecting_quarterColumns D φ F hU hV normalizedSlitBaseLift n a)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.RefinedWang
