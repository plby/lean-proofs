import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescentAlgebra
import Wikipedia.HopfProblem.PeriodTorusAppellHumbertData

/-!
# A genuine holomorphic factor from a cover frame

Local coefficient ratios are holomorphic in each fixed native bundle chart.
Their chart independence therefore makes the extracted scalar factor globally
holomorphic. Its positive translation action preserves the actual native
total-space map determined by the frame.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescent

open PeriodTorusLineBundleClassificationNative PeriodTorusAppellHumbert

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

variable {p : PeriodDomain} {V : p.Torus → Type*}
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V IC]

theorem frameFactorScalar_contDiffAt (s : CoverSection p V) (hne : ∀ z, s z ≠ 0)
    (l : p.lattice) (z : ComplexPlane₂) :
    ContDiffAt ℂ ω (frameFactorScalar s l) z := by
  have hi := FiberBundle.mem_baseSet_trivializationAt ℂ V (p.lattice.mkQ z)
  have hi' : p.lattice.mkQ (z + l) ∈
      (nativeTriv V (p.lattice.mkQ z)).baseSet := by
    rwa [quotient_add_lattice]
  have hn : ContDiffAt ℂ ω (coefficient s (p.lattice.mkQ z)) z :=
    (coefficient_contMDiffAt s (p.lattice.mkQ z) z hi).contDiffAt
  have hd₀ : ContDiffAt ℂ ω (coefficient s (p.lattice.mkQ z)) (z + l) :=
    (coefficient_contMDiffAt s (p.lattice.mkQ z) (z + l) hi').contDiffAt
  have hd : ContDiffAt ℂ ω
      (fun w => coefficient s (p.lattice.mkQ z) (w + l)) z :=
    hd₀.comp (f := fun w : ComplexPlane₂ => w + l) z
      (contDiffAt_id.add contDiffAt_const)
  have hratio := hn.div hd (coefficient_ne_zero s hne (p.lattice.mkQ z) (z + l) hi')
  apply hratio.congr_of_eventuallyEq
  have hU : ∀ᶠ w in 𝓝 z,
      p.lattice.mkQ w ∈ (nativeTriv V (p.lattice.mkQ z)).baseSet :=
    p.lattice.continuous_mkQ.continuousAt
      ((nativeTriv V (p.lattice.mkQ z)).open_baseSet.mem_nhds hi)
  filter_upwards [hU] with w hw
  exact frameFactorScalar_eq_coefficient_div s l w (p.lattice.mkQ z) hw

theorem frameFactorScalar_holomorphic (s : CoverSection p V) (hne : ∀ z, s z ≠ 0)
    (l : p.lattice) : ContDiff ℂ ω (frameFactorScalar s l) :=
  contDiff_iff_contDiffAt.mpr (frameFactorScalar_contDiffAt s hne l)

/-- The genuine factor of automorphy of the supplied nonvanishing holomorphic
frame of the actual native universal-cover pullback. -/
def frameFactor (s : CoverSection p V) (hne : ∀ z, s z ≠ 0) : FactorOfAutomorphy p where
  factor l z := Units.mk0 (frameFactorScalar s l z) (frameFactorScalar_ne_zero s hne l z)
  factor_zero z := Units.ext (frameFactorScalar_zero s hne z)
  factor_add l m z := Units.ext (frameFactorScalar_add s hne l m z)
  holomorphic_factor := frameFactorScalar_holomorphic s hne

@[simp] theorem frameFactor_coe (s : CoverSection p V) (hne : ∀ z, s z ≠ 0)
    (l : p.lattice) (z : ComplexPlane₂) :
    ((frameFactor s hne).factor l z : ℂ) = frameFactorScalar s l z := rfl

/-- The positive factor action preserves the actual native total-space map.
The equality is proved in a common native trivialization, including the base
point equality, so no dependent-fibre identification is postulated. -/
theorem frameFactor_equivariance (s : CoverSection p V) (hne : ∀ z, s z ≠ 0)
    (l : p.lattice) (z : ComplexPlane₂) (c : ℂ) :
    coverScalarMap s (z + l, ((frameFactor s hne).factor l z : ℂ) * c) =
      coverScalarMap s (z, c) := by
  have hi := FiberBundle.mem_baseSet_trivializationAt ℂ V (p.lattice.mkQ z)
  have hi' : p.lattice.mkQ (z + l) ∈
      (nativeTriv V (p.lattice.mkQ z)).baseSet := by
    rwa [quotient_add_lattice]
  apply (nativeTriv V (p.lattice.mkQ z)).toOpenPartialHomeomorph.injOn
  · exact (nativeTriv V (p.lattice.mkQ z)).mem_source.mpr hi'
  · exact (nativeTriv V (p.lattice.mkQ z)).mem_source.mpr hi
  · change nativeTriv V (p.lattice.mkQ z)
        (coverScalarMap s (z + l, ((frameFactor s hne).factor l z : ℂ) * c)) =
      nativeTriv V (p.lattice.mkQ z) (coverScalarMap s (z, c))
    rw [coverScalarMap_localTriv s (p.lattice.mkQ z) _ hi',
      coverScalarMap_localTriv s (p.lattice.mkQ z) _ hi]
    apply Prod.ext
    · exact quotient_add_lattice z l
    · change (frameFactorScalar s l z * c) *
          coefficient s (p.lattice.mkQ z) (z + l) =
        c * coefficient s (p.lattice.mkQ z) z
      calc
        _ = c * (frameFactorScalar s l z *
            coefficient s (p.lattice.mkQ z) (z + l)) := by ring
        _ = _ := by rw [frameFactorScalar_mul_coefficient s hne l z (p.lattice.mkQ z) hi]

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescent
