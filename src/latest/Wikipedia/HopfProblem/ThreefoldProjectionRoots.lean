import Wikipedia.HopfProblem.ThreefoldReducedEllipticDivisor
import Wikipedia.HopfProblem.ThreefoldProjectionLocalUnit
import Wikipedia.HopfProblem.ThreefoldProjectionHomogeneousCoordinates
import Wikipedia.HopfProblem.HolomorphicPicardContinuousChartScalars
import Wikipedia.HopfProblem.ContinuousRootFromLocalFactors
import Wikipedia.HopfProblem.ThreefoldFundamentalGroup

/-!
# Global cubic and quartic roots of the actual projection coordinates

The reduced divisor sections have local roots as their coefficients.
The original elliptic chart and finite sphere chart differ by a nonzero
analytic factor. Continuous trivializations supply the remaining nonzero
factors. These extend across the divisor and acquire global roots by
simple connectivity of the original threefold.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.ProjectionHomotopy

open Elliptic EllipticGeometry
open CanonicalGlobal.BaseTwist
open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames
open ProjectionLocalUnit

namespace Roots

abbrev coordinate : Kind → Space → ℂ
  | .three => zeroCoordinate
  | .four => oneCoordinate

theorem coordinate_continuous (j : Kind) : Continuous (coordinate j) := by
  cases j
  · exact zeroCoordinate_continuous
  · exact oneCoordinate_continuous

theorem coordinate_eq_zero_iff (j : Kind) (x : Space) :
    coordinate j x = 0 ↔ projectionSphere x = sphereValue j := by
  cases j
  · exact (zeroCoordinate_eq_zero_iff x).trans (by rw [sphereValue_three])
  · exact (oneCoordinate_eq_zero_iff x).trans (by rw [sphereValue_four])

def finiteLocus : TopologicalSpace.Opens Space :=
  ⟨projectionSphere ⁻¹' (finiteChart : Set RiemannSphere),
    finiteChart.isOpen.preimage projectionSphere_continuous⟩

def finiteValue (x : Space) : ℂ := finiteCoordinate (projectionSphere x)

theorem finiteValue_continuousOn : ContinuousOn finiteValue finiteLocus :=
  finiteCoordinate_holomorphicOn.continuousOn.comp projectionSphere_continuous.continuousOn
    (fun _ hx => hx)

theorem finiteValue_coe {x : Space} (hx : x ∈ finiteLocus) :
    (finiteValue x : RiemannSphere) = projectionSphere x := by
  have hn : projectionSphere x ≠ (∞ : RiemannSphere) := (mem_finiteChart _).mp hx
  generalize hp : projectionSphere x = p at hn ⊢
  unfold finiteValue
  rw [hp]
  induction p using OnePoint.rec with
  | infty => exact (hn rfl).elim
  | coe z => rfl

def finiteScale (x : Space) : ℂ := zeroCoordinate x - oneCoordinate x

theorem finiteScale_continuous : Continuous finiteScale :=
  zeroCoordinate_continuous.sub oneCoordinate_continuous

theorem finiteScale_eq {x : Space} (hx : x ∈ finiteLocus) :
    finiteScale x = coordinateScale x := by
  have hf := (finiteValue_coe hx).symm
  rw [finiteScale, zeroCoordinate_of_finite x (finiteValue x) hf,
    oneCoordinate_of_finite x (finiteValue x) hf]
  ring

theorem finiteScale_ne_zero {x : Space} (hx : x ∈ finiteLocus) : finiteScale x ≠ 0 := by
  rw [finiteScale_eq hx]
  exact coordinateScale_ne_zero x

theorem coordinate_finite (j : Kind) {x : Space} (hx : x ∈ finiteLocus) :
    coordinate j x = (finiteValue x - center j) * finiteScale x := by
  rw [finiteScale_eq hx]
  cases j
  · simpa only [coordinate, ProjectionLocalUnit.center, sub_zero] using
      zeroCoordinate_of_finite x (finiteValue x) (finiteValue_coe hx).symm
  · exact oneCoordinate_of_finite x (finiteValue x) (finiteValue_coe hx).symm

def rootScale (j : Kind) (i : ReducedEllipticDivisor.Index j) (x : Space) : ℂ :=
  HolomorphicPicard.ContinuousTrivialization.chartScalar
    (ReducedEllipticDivisor.transitions j) (ReducedEllipticDivisor.trivialization j) i x

theorem rootScale_continuousOn (j : Kind) (i : ReducedEllipticDivisor.Index j) :
    ContinuousOn (rootScale j i) (ReducedEllipticDivisor.baseSet j i) :=
  HolomorphicPicard.ContinuousTrivialization.chartScalar_continuousOn _ _ i

theorem rootScale_ne_zero (j : Kind) (i : ReducedEllipticDivisor.Index j) (x : Space) :
    rootScale j i x ≠ 0 :=
  HolomorphicPicard.ContinuousTrivialization.chartScalar_ne_zero _ _ i x

theorem definingFunction_chart (j : Kind) (i : ReducedEllipticDivisor.Index j)
    {x : Space} (hx : x ∈ ReducedEllipticDivisor.baseSet j i) :
    ReducedEllipticDivisor.definingFunction j x =
      ReducedEllipticDivisor.localEquation j i x * rootScale j i x :=
  HolomorphicPicard.ContinuousTrivialization.sectionFromLocal_eq_mul_chartScalar
    _ _ _ (ReducedEllipticDivisor.localEquation_compatible j) i hx

theorem local_factor_at_zero (j : Kind) (x : Space)
    (hx : ReducedEllipticDivisor.definingFunction j x = 0) :
    ∃ (U : Set Space) (u : Space → ℂ), IsOpen U ∧ x ∈ U ∧ ContinuousOn u U ∧
      ∀ y ∈ U, u y ≠ 0 ∧ coordinate j y =
        ReducedEllipticDivisor.definingFunction j y ^ j.order * u y := by
  have hp := (ReducedEllipticDivisor.definingFunction_eq_zero_iff j x).mp hx
  have hpatch := FibreClassification.elliptic_fibre_mem_liftedPatch j x hp
  let i := (ReducedEllipticDivisor.fillingData j).indexAt
    (ReducedEllipticDivisor.fillingPoint j x)
  have hi : x ∈ ReducedEllipticDivisor.chartSet j i :=
    ReducedEllipticDivisor.mem_chartSet_at j hpatch
  have hfin : x ∈ finiteLocus := by
    change projectionSphere x ∈ finiteChart
    rw [hp, sphereValue_eq_coe]
    exact coe_mem_finiteChart _
  have hval : finiteValue x = center j :=
    OnePoint.coe_injective ((finiteValue_coe hfin).trans (hp.trans (sphereValue_eq_coe j)))
  obtain ⟨V, u, hVo, hcV, hu, huf⟩ := exists_unit_near_center j
  let W : Set Space := ReducedEllipticDivisor.chartSet j i ∩ finiteLocus
  let U : Set Space := W ∩ finiteValue ⁻¹' V
  have hWo : IsOpen W := (ReducedEllipticDivisor.isOpen_chartSet j i).inter finiteLocus.isOpen
  have hUo : IsOpen U :=
    (finiteValue_continuousOn.mono inter_subset_right).isOpen_inter_preimage hWo hVo
  have hUc : ContinuousOn (fun y => u (finiteValue y)) U :=
    hu.comp (finiteValue_continuousOn.mono (fun _ hy => hy.1.2)) (fun _ hy => hy.2)
  have hSc : ContinuousOn (rootScale j (some i)) U :=
    (rootScale_continuousOn j (some i)).mono (fun _ hy => hy.1.1)
  refine ⟨U, (fun y => finiteScale y / (u (finiteValue y) * rootScale j (some i) y ^ j.order)),
    hUo, ⟨⟨hi, hfin⟩, by change finiteValue x ∈ V; rw [hval]; exact hcV⟩,
    finiteScale_continuous.continuousOn.div (hUc.mul (hSc.pow j.order))
      (fun y hy => mul_ne_zero (huf _ hy.2).1 (pow_ne_zero _ (rootScale_ne_zero j _ y))), ?_⟩
  intro y hy
  have hu0 := (huf (finiteValue y) hy.2).1
  have hs0 := rootScale_ne_zero j (some i) y
  refine ⟨div_ne_zero (finiteScale_ne_zero hy.1.2) (mul_ne_zero hu0 (pow_ne_zero _ hs0)), ?_⟩
  rw [coordinate_finite j hy.1.2, definingFunction_chart j (some i) hy.1.1]
  change (finiteValue y - center j) * finiteScale y =
    (ReducedEllipticDivisor.coefficient j i y * rootScale j (some i) y) ^ j.order * _
  have hpow := ReducedEllipticDivisor.coefficient_pow j i hy.1.1
  have he : ReducedEllipticDivisor.coefficient j i y ^ j.order =
      (finiteValue y - center j) * u (finiteValue y) := by
    rw [hpow, ← finiteValue_coe hy.1.2]
    exact (huf (finiteValue y) hy.2).2
  rw [mul_pow, he]
  field_simp [hu0, hs0]

theorem local_factor (j : Kind) (x : Space) :
    ∃ (U : Set Space) (u : Space → ℂ), IsOpen U ∧ x ∈ U ∧ ContinuousOn u U ∧
      ∀ y ∈ U, u y ≠ 0 ∧ coordinate j y =
        ReducedEllipticDivisor.definingFunction j y ^ j.order * u y := by
  by_cases hx : ReducedEllipticDivisor.definingFunction j x = 0
  · exact local_factor_at_zero j x hx
  · let g := ReducedEllipticDivisor.definingFunction j
    let U : Set Space := {y | g y ≠ 0}
    have hg := ReducedEllipticDivisor.definingFunction_continuous j
    refine ⟨U, (fun y => coordinate j y / g y ^ j.order),
      isOpen_ne_fun hg continuous_const, hx,
      (coordinate_continuous j).continuousOn.div (hg.pow j.order).continuousOn
        (fun y hy => pow_ne_zero _ hy), ?_⟩
    intro y hy
    have hf : coordinate j y ≠ 0 :=
      (coordinate_eq_zero_iff j y).not.mpr
        ((ReducedEllipticDivisor.definingFunction_eq_zero_iff j y).not.mp hy)
    refine ⟨div_ne_zero hf (pow_ne_zero _ hy), ?_⟩
    field_simp [pow_ne_zero j.order hy]
    rfl

/-- Both roots are obtained from the native divisor geometry and the
proved simple connectivity of X; they are not hypotheses. -/
theorem exists_root (j : Kind) : ∃ a : C(Space, ℂ), ∀ x, a x ^ j.order = coordinate j x := by
  let := space_simplyConnected
  let := space_locallyPathConnected
  exact ContinuousRootFromLocalFactors.exists_continuous_root j.order_pos.ne'
    (ReducedEllipticDivisor.definingFunction_continuous j)
    (ReducedEllipticDivisor.definingFunction_nonzero_dense j) (local_factor j)

def root (j : Kind) : C(Space, ℂ) := (exists_root j).choose

theorem root_pow (j : Kind) (x : Space) : root j x ^ j.order = coordinate j x :=
  (exists_root j).choose_spec x

theorem cubic_root (x : Space) : root .three x ^ 3 = zeroCoordinate x := root_pow .three x

theorem quartic_root (x : Space) : root .four x ^ 4 = oneCoordinate x := root_pow .four x

theorem roots_no_common_zero (x : Space) : root .three x ≠ 0 ∨ root .four x ≠ 0 := by
  rcases coordinates_no_common_zero x with h | h
  · exact Or.inl (fun he => h (by rw [← cubic_root, he]; norm_num))
  · exact Or.inr (fun he => h (by rw [← quartic_root, he]; norm_num))

end Roots

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.ProjectionHomotopy
