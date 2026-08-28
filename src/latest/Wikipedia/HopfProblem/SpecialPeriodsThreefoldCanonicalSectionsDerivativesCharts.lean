import Wikipedia.HopfProblem.EllipticEquivariantFamilies
import Wikipedia.HopfProblem.EllipticBundleCharacters
import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalBundle

/-!
# The ambient elliptic generator in actual family charts

The logarithmic generator acts on the varying-period torus family by an
affine lift.  Its actual derivative, including derivatives of the moving
periods and the translation, has top determinant equal to the base
rotation times the determinant of its two-dimensional fibre matrix.
The calculation descends through the actual lattice quotient charts.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data.Canonical

open SpecialPeriods TrianglePeriodFamily.Canonical

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ Model

variable {j : Kind} (D : Equivariant.Data j)

local instance coveringChartedSpace : ChartedSpace Model (Disc × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (Disc × ComplexPlane₂))

local instance coveringManifold : IsManifold I₃ ω (Disc × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := I₁) (I' := I₂) Disc ComplexPlane₂

/-- All native disc charts have the same complex coordinate. -/
theorem disc_chart_apply (a s : Disc) : chartAt ℂ a s = (s : ℂ) := rfl

/-- The actual base rotation in a native source chart. -/
def rotationCoordinate (j : Kind) (a : Disc) (z : ℂ) : ℂ :=
  (familyRotation j ((chartAt ℂ a).symm z) : ℂ)

/-- The fibre matrix of the actual affine lift in that chart. -/
def matrixCoordinate (a : Disc) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  linearMatrix j (D.periods.point ((chartAt ℂ a).symm z))

/-- A transported real-period displacement in the rotated fibre. -/
def displacementCoordinate (a : Disc) (v : RealCoordinates) (z : ℂ) : ComplexPlane₂ :=
  D.periods.periodEquiv (familyRotation j ((chartAt ℂ a).symm z)) v

theorem rotationCoordinate_eventually_mul (j : Kind) (a : Disc) {z : ℂ}
    (hz : z ∈ (chartAt ℂ a).target) :
    rotationCoordinate j a =ᶠ[𝓝 z] (fun w => normalPhase j * w) := by
  filter_upwards [(chartAt ℂ a).open_target.mem_nhds hz] with w hw
  rw [rotationCoordinate, familyRotation_val,
    base_chart_inverse_coordinate (fun s : Disc => (s : ℂ)) disc_chart_apply a hw]

theorem rotationCoordinate_hasDerivAt (j : Kind) (a : Disc) {z : ℂ}
    (hz : z ∈ (chartAt ℂ a).target) :
    HasDerivAt (rotationCoordinate j a) (normalPhase j) z := by
  have h : HasDerivAt (fun w : ℂ => normalPhase j * w) (normalPhase j) z := by
    simpa using (hasDerivAt_id z).const_mul (normalPhase j)
  exact h.congr_of_eventuallyEq (rotationCoordinate_eventually_mul j a hz)

/-- Entrywise holomorphicity follows from the actual holomorphic linear
lift, evaluated on the two standard basis vectors. -/
theorem matrix_entry_holomorphic (i k : Fin 2) :
    ContMDiff I₁ I₁ ω (fun s : Disc => linearMatrix j (D.periods.point s) i k) := by
  have hp : ContMDiff I₁ I₃ ω
      (fun s : Disc => (s, (Pi.single k (1 : ℂ) : ComplexPlane₂))) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_id.prodMk contMDiff_const
  have h := (contMDiff_pi_space.mp (D.linearLift_holomorphic.comp hp)) i
  simpa only [Function.comp_apply, Matrix.mulVec_single_one, Matrix.col_apply] using h

theorem matrixCoordinate_contDiffAt (a : Disc) {z : ℂ}
    (hz : z ∈ (chartAt ℂ a).target) (i k : Fin 2) :
    ContDiffAt ℂ ω (fun w => matrixCoordinate D a w i k) z := by
  have hi : ContMDiffAt I₁ I₁ ω (chartAt ℂ a).symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a) hz
  exact ((matrix_entry_holomorphic D i k).contMDiffAt.comp z hi).contDiffAt

theorem displacementCoordinate_contDiffAt (a : Disc) (v : RealCoordinates) {z : ℂ}
    (hz : z ∈ (chartAt ℂ a).target) :
    ContDiffAt ℂ ω (displacementCoordinate D a v) z := by
  have hi : ContMDiffAt I₁ I₁ ω (chartAt ℂ a).symm z :=
    contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a) hz
  have hp := (D.periods.holomorphic_periodEquiv_const v).comp
    (familyRotation j).contMDiff_toFun
  exact (hp.contMDiffAt.comp z hi).contDiffAt

/-- Exact expression of the actual affine lift, before taking any derivative. -/
theorem complexLift_chart_expression (v : Lattice) (a b : Disc × ComplexPlane₂) :
    chartAt Model b ∘ D.complexLift v ∘ (chartAt Model a).symm =
      skewMap (rotationCoordinate j a.1) (matrixCoordinate D a.1)
        (displacementCoordinate D a.1 ((1 / (j.order : ℝ)) • realCast v)) := by
  funext w
  rfl

/-- The actual three-dimensional Jacobian of the lifted generator. -/
theorem complexLift_chart_det_fderiv (v : Lattice) (a b : Disc × ComplexPlane₂)
    {u : Model} (hu : u ∈ (chartAt Model a).target) :
    LinearMap.det (fderiv ℂ
      (chartAt Model b ∘ D.complexLift v ∘ (chartAt Model a).symm) u).toLinearMap =
      normalPhase j * (matrixCoordinate D a.1 u.1).det := by
  rw [complexLift_chart_expression]
  exact det_fderiv_skewMap u.2 (rotationCoordinate_hasDerivAt j a.1 hu.1)
    (fun i k => ((matrixCoordinate_contDiffAt D a.1 hu.1 i k).differentiableAt
      (by simp)).hasDerivAt)
    ((displacementCoordinate_contDiffAt D a.1 _ hu.1).differentiableAt
      (by simp)).hasDerivAt

theorem complexLift_chart_volume (v : Lattice) (a b : Disc × ComplexPlane₂)
    {u : Model} (hu : u ∈ (chartAt Model a).target) :
    volume.compContinuousLinearMap
      (fderiv ℂ (chartAt Model b ∘ D.complexLift v ∘ (chartAt Model a).symm) u) =
        (normalPhase j * (matrixCoordinate D a.1 u.1).det) • volume := by
  rw [volume_pullback, complexLift_chart_det_fderiv D v a b hu]

/-- The generator in the original varying-period lattice-quotient charts. -/
def permutationCoordinate (v : Lattice) (a b : D.TotalSpace) : Model → Model :=
  familyChart D.periods b ∘ D.permutation v ∘ (familyChart D.periods a).symm

/-- Locally the genuine quotient generator is its affine lift followed
by a single target-lattice shear. -/
theorem permutationCoordinate_eventually_skew (v : Lattice) (a b : D.TotalSpace)
    {u : Model} (hu : u ∈ (familyChart D.periods a).target)
    (hb : D.permutation v ((familyChart D.periods a).symm u) ∈
      (familyChart D.periods b).source) :
    ∃ w : Multiplicative standardLattice,
      permutationCoordinate D v a b =ᶠ[𝓝 u]
        skewMap (rotationCoordinate j (familyRepresentative D.periods a).1)
          (matrixCoordinate D (familyRepresentative D.periods a).1)
          (displacementCoordinate D (familyRepresentative D.periods a).1
            (((1 / (j.order : ℝ)) • realCast v) + w.toAdd)) := by
  let := D.periods.coveringAction
  let a' := familyRepresentative D.periods a
  let b' := familyRepresentative D.periods b
  let x := (chartAt Model a').symm u
  let y := D.complexLift v x
  have hy : D.periods.quotientMap y ∈ (familyChart D.periods b).source := by
    rw [familyChart_symm_apply, ← D.complexLift_quotientMap] at hb
    exact hb
  obtain ⟨w, _, hw⟩ := CoveringQuotient.localInverse_eventually_deck
    D.periods.quotientCoveringMap
    (fun w => (D.periods.coveringAction_holomorphic w).continuous) b' y hy.1
  have ht : Tendsto (D.complexLift v ∘ (chartAt Model a').symm) (𝓝 u) (𝓝 y) :=
    (D.complexLift_holomorphic v).continuous.continuousAt.comp
      ((chartAt Model a').symm.continuousAt (familyChart_target_subset D.periods a hu))
  refine ⟨w, ?_⟩
  filter_upwards [hw.comp_tendsto ht] with z hz
  change familyChart D.periods b (D.permutation v ((familyChart D.periods a).symm z)) = _
  rw [familyChart_symm_apply, ← D.complexLift_quotientMap]
  change (chartAt Model b')
    ((CoveringQuotient.localInverse D.periods.quotientCoveringMap b')
      (D.periods.quotientMap (D.complexLift v ((chartAt Model a').symm z)))) = _
  rw [show (CoveringQuotient.localInverse D.periods.quotientCoveringMap b')
      (D.periods.quotientMap (D.complexLift v ((chartAt Model a').symm z))) =
        w • D.complexLift v ((chartAt Model a').symm z) from hz]
  change ((familyRotation j ((chartAt ℂ a'.1).symm z.1) : ℂ),
    (linearMatrix j (D.periods.point ((chartAt ℂ a'.1).symm z.1)) *ᵥ z.2 +
      D.periods.periodEquiv (familyRotation j ((chartAt ℂ a'.1).symm z.1))
        ((1 / (j.order : ℝ)) • realCast v)) +
      D.periods.periodEquiv (familyRotation j ((chartAt ℂ a'.1).symm z.1)) w.toAdd) = _
  simp only [a', skewMap, rotationCoordinate, matrixCoordinate, displacementCoordinate,
    map_add, add_assoc]

/-- The multiplier is the determinant of the actual derivative on the
torus family, not merely of a formal affine model. -/
theorem permutationCoordinate_det_fderiv (v : Lattice) (a b : D.TotalSpace)
    {u : Model} (hu : u ∈ (familyChart D.periods a).target)
    (hb : D.permutation v ((familyChart D.periods a).symm u) ∈
      (familyChart D.periods b).source) :
    LinearMap.det (fderiv ℂ (permutationCoordinate D v a b) u).toLinearMap =
      normalPhase j * (matrixCoordinate D (familyRepresentative D.periods a).1 u.1).det := by
  obtain ⟨w, hw⟩ := permutationCoordinate_eventually_skew D v a b hu hb
  rw [hw.fderiv_eq]
  have hz : u.1 ∈ (chartAt ℂ (familyRepresentative D.periods a).1).target :=
    (familyChart_target_subset D.periods a hu).1
  exact det_fderiv_skewMap u.2 (rotationCoordinate_hasDerivAt j _ hz)
    (fun i k => ((matrixCoordinate_contDiffAt D _ hz i k).differentiableAt
      (by simp)).hasDerivAt)
    ((displacementCoordinate_contDiffAt D _ _ hz).differentiableAt (by simp)).hasDerivAt

theorem permutationCoordinate_volume (v : Lattice) (a b : D.TotalSpace)
    {u : Model} (hu : u ∈ (familyChart D.periods a).target)
    (hb : D.permutation v ((familyChart D.periods a).symm u) ∈
      (familyChart D.periods b).source) :
    volume.compContinuousLinearMap (fderiv ℂ (permutationCoordinate D v a b) u) =
      (normalPhase j * (matrixCoordinate D (familyRepresentative D.periods a).1 u.1).det) •
        volume := by
  rw [volume_pullback, permutationCoordinate_det_fderiv D v a b hu hb]

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data.Canonical
