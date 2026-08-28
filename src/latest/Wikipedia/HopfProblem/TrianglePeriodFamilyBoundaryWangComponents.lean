import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryWang

/-!
# Actual component columns of the Wang-to-family comparison

The two source component generators are inserted at the literal times
`1/4` and `3/4`. The actual two-component homology marking sends these
insertions to its two coordinate summands. Consequently each comparison
column is induced by the original geometric boundary map at one of those
times, with all its fibre dependence retained.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology Homology
open MappingTorus.HomologyCover

variable {X : Type} [TopologicalSpace X] (φ : X ≃ₜ X)

/-- The lower actual arc-overlap basepoint, at real time one quarter. -/
def lowerComponentTime : Set.Ioo (0 : ℝ) (1 / 2) := ⟨1 / 4, by constructor <;> norm_num⟩

/-- The upper actual arc-overlap basepoint, at real time three quarters. -/
def upperComponentTime : Set.Ioo (1 / 2 : ℝ) 1 := ⟨3 / 4, by constructor <;> norm_num⟩

/-- Insert the actual fibre into the lower component of the actual mapping-torus intersection. -/
def lowerComponentFibre : C(X, (U φ ∩ V φ : Set (MappingTorus.Torus φ))) where
  toFun x := (intersectionHomeomorph φ).symm (Sum.inl (lowerComponentTime, x))
  continuous_toFun := (intersectionHomeomorph φ).symm.continuous.comp
    (continuous_inl.comp (continuous_const.prodMk continuous_id))

/-- Insert the actual fibre into the upper component at real time three quarters. -/
def upperComponentFibre : C(X, (U φ ∩ V φ : Set (MappingTorus.Torus φ))) where
  toFun x := (intersectionHomeomorph φ).symm (Sum.inr (upperComponentTime, x))
  continuous_toFun := (intersectionHomeomorph φ).symm.continuous.comp
    (continuous_inr.comp (continuous_const.prodMk continuous_id))

@[simp] theorem lowerComponentFibre_coe (x : X) :
    (lowerComponentFibre φ x).val = MappingTorus.mk φ (1 / 4, x) :=
  intersectionHomeomorph_symm_inl_coe φ (lowerComponentTime, x)

@[simp] theorem upperComponentFibre_coe (x : X) :
    (upperComponentFibre φ x).val = MappingTorus.mk φ (3 / 4, x) :=
  intersectionHomeomorph_symm_inr_coe φ (upperComponentTime, x)

/-- The actual intersection retraction sends the lower insertion to the first coproduct summand. -/
theorem lowerComponentFibre_retraction :
    (intersectionHomotopyEquiv φ).toFun.comp (lowerComponentFibre φ) = sumInlMap X X := by
  apply ContinuousMap.ext
  intro x
  exact intersectionHomotopyEquiv_inl φ (lowerComponentTime, x)

/-- The upper insertion is the second genuine coproduct summand under the retraction. -/
theorem upperComponentFibre_retraction :
    (intersectionHomotopyEquiv φ).toFun.comp (upperComponentFibre φ) = sumInrMap X X := by
  apply ContinuousMap.ext
  intro x
  exact intersectionHomotopyEquiv_inr φ (upperComponentTime, x)

/-- The actual lower insertion gives exactly the first homology coordinate. -/
@[simp] theorem lowerComponentFibre_homology (n : ℕ) (a : SingularHomology X n) :
    MappingTorusHomology.intersectionHomologyEquiv φ n
      (singularHomologyMap (lowerComponentFibre φ) n a) = (a, 0) := by
  rw [MappingTorusHomology.intersectionHomologyEquiv_apply,
    ← LinearMap.comp_apply, ← singularHomologyMap_comp,
    lowerComponentFibre_retraction, sumHomologyEquiv_inl]

/-- The actual upper insertion gives exactly the second homology coordinate. -/
@[simp] theorem upperComponentFibre_homology (n : ℕ) (a : SingularHomology X n) :
    MappingTorusHomology.intersectionHomologyEquiv φ n
      (singularHomologyMap (upperComponentFibre φ) n a) = (0, a) := by
  rw [MappingTorusHomology.intersectionHomologyEquiv_apply,
    ← LinearMap.comp_apply, ← singularHomologyMap_comp,
    upperComponentFibre_retraction, sumHomologyEquiv_inr]

@[simp] theorem intersectionHomologyEquiv_symm_lower (n : ℕ) (a : SingularHomology X n) :
    (MappingTorusHomology.intersectionHomologyEquiv φ n).symm (a, 0) =
      singularHomologyMap (lowerComponentFibre φ) n a := by
  apply (MappingTorusHomology.intersectionHomologyEquiv φ n).injective
  rw [LinearEquiv.apply_symm_apply, lowerComponentFibre_homology]

@[simp] theorem intersectionHomologyEquiv_symm_upper (n : ℕ) (a : SingularHomology X n) :
    (MappingTorusHomology.intersectionHomologyEquiv φ n).symm (0, a) =
      singularHomologyMap (upperComponentFibre φ) n a := by
  apply (MappingTorusHomology.intersectionHomologyEquiv φ n).injective
  rw [LinearEquiv.apply_symm_apply, upperComponentFibre_homology]

variable (D : Data ℂ TriangleRegularPoint)
  (F : C(MappingTorus.Torus φ, D.Space))
  (hU : Set.MapsTo F (U φ) (upperFamily D))
  (hV : Set.MapsTo F (V φ) (lowerFamily D))

/-- The original boundary map at the actual lower-component fibre, as an intersection map. -/
def lowerColumnMap : C(X, familyIntersection D) :=
  (intersectionMap D φ F hU hV).comp (lowerComponentFibre φ)

/-- The original boundary map at the actual upper-component fibre. -/
def upperColumnMap : C(X, familyIntersection D) :=
  (intersectionMap D φ F hU hV).comp (upperComponentFibre φ)

@[simp] theorem lowerColumnMap_coe (x : X) :
    (lowerColumnMap φ D F hU hV x).val = F (MappingTorus.mk φ (1 / 4, x)) := by
  change F (lowerComponentFibre φ x).val = _
  rw [lowerComponentFibre_coe]

@[simp] theorem upperColumnMap_coe (x : X) :
    (upperColumnMap φ D F hU hV x).val = F (MappingTorus.mk φ (3 / 4, x)) := by
  change F (upperComponentFibre φ x).val = _
  rw [upperComponentFibre_coe]

/-- The first comparison column is the actual geometric lower fibre map. -/
theorem intersectionComparison_lowerColumn (b : SlitBaseLift) (n : ℕ)
    (a : SingularHomology X n) :
    intersectionComparison D φ F hU hV b n (a, 0) =
      Homology.intersectionHomologyEquiv D b n
        (singularHomologyMap (lowerColumnMap φ D F hU hV) n a) := by
  rw [intersectionComparison_apply, intersectionHomologyEquiv_symm_lower]
  exact congrArg (Homology.intersectionHomologyEquiv D b n)
    (LinearMap.congr_fun
      (singularHomologyMap_comp (lowerComponentFibre φ) (intersectionMap D φ F hU hV) n) a).symm

/-- The second comparison column is the actual geometric upper fibre map. -/
theorem intersectionComparison_upperColumn (b : SlitBaseLift) (n : ℕ)
    (a : SingularHomology X n) :
    intersectionComparison D φ F hU hV b n (0, a) =
      Homology.intersectionHomologyEquiv D b n
        (singularHomologyMap (upperColumnMap φ D F hU hV) n a) := by
  rw [intersectionComparison_apply, intersectionHomologyEquiv_symm_upper]
  exact congrArg (Homology.intersectionHomologyEquiv D b n)
    (LinearMap.congr_fun
      (singularHomologyMap_comp (upperComponentFibre φ) (intersectionMap D φ F hU hV) n) a).symm

/-- On an actual Wang boundary, the regular connecting coordinate is the difference
of the two genuine quarter-time fibre maps. -/
theorem markedConnecting_quarterColumns (b : SlitBaseLift) (n : ℕ)
    (a : SingularHomology (MappingTorus.Torus φ) (n + 1)) :
    familyMarkedConnecting D b n (singularHomologyMap F (n + 1) a) =
      -Homology.intersectionHomologyEquiv D b n
        (singularHomologyMap (lowerColumnMap φ D F hU hV) n
          (MappingTorusHomology.wangBoundary φ n a)) +
      Homology.intersectionHomologyEquiv D b n
        (singularHomologyMap (upperColumnMap φ D F hU hV) n
          (MappingTorusHomology.wangBoundary φ n a)) := by
  rw [markedConnecting_wangBoundary D φ F hU hV b n a,
    intersectionComparison_antidiagonal, intersectionComparison_lowerColumn,
    intersectionComparison_upperColumn]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
