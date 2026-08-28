import Wikipedia.HopfProblem.CuspCentralHomologyPhaseOrbitNullhomotopy

/-!
# The actual inner-region inclusion is nullhomotopic

The inner region has unique compact-phase and interior-hexagon coordinates.
Moving that planar coordinate along a straight segment to the fixed literal
triangle barycenter gives a homotopy in the original central fibre. At the
endpoint all phases coincide, by the actual toric stabilizer computation.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction CuspHoneycomb CuspHoneycombTiling

local notation "Plane" => CuspHoneycombTiling.Plane

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The original subspace inclusion, with no change of topology. -/
def innerRegionInclusion : C(innerRegion C ε hε, QuotientCentralFibre C ε) :=
  ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem innerRegionInclusion_apply (q : innerRegion C ε hε) :
    innerRegionInclusion C ε hε q = (q : QuotientCentralFibre C ε) := rfl

variable (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- The chosen inverse to the inner-region phase equivalence is the
literal phase orbit over the centre, after the actual inclusion. -/
theorem innerRegionInclusion_comp_phaseSection :
    (innerRegionInclusion C ε hε).comp
        (innerRegionHomotopyEquiv C ε hε hε1 hC hR).symm.toFun =
      centralPhaseOrbit C ε hε := by
  apply ContinuousMap.ext
  intro φ
  change (innerRegionHomeomorph C ε hε hε1 hC hR
    (φ, Radial.interiorCellZero) : QuotientCentralFibre C ε) = _
  rw [innerRegionHomeomorph_honeycomb, Radial.interiorCellZero_coe]
  rfl

/-- The displayed straight homotopy contracts the actual inclusion into
the original central fibre, not the inner region itself. -/
def innerRegionInclusionHomotopy :
    (innerRegionInclusion C ε hε).Homotopy
      (ContinuousMap.const (innerRegion C ε hε)
        (honeycombCollapseMap C ε hε (1, (phaseOrbitVertex : Plane)))) where
  toFun p :=
    let x := (innerRegionHomeomorph C ε hε hε1 hC hR).symm p.2
    honeycombCollapseMap C ε hε
      (x.1, (1 - (p.1 : ℝ)) • (x.2 : Plane) + (p.1 : ℝ) • (phaseOrbitVertex : Plane))
  continuous_toFun := by
    have hx := (innerRegionHomeomorph C ε hε hε1 hC hR).symm.continuous.comp
      (continuous_snd : Continuous (Prod.snd : unitInterval × innerRegion C ε hε → _))
    have hs : Continuous (fun p : unitInterval × innerRegion C ε hε => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact (honeycombCollapseMap_continuous C ε hε).comp
      ((continuous_fst.comp hx).prodMk
        (((continuous_const.sub hs).smul
          (continuous_subtype_val.comp (continuous_snd.comp hx))).add
            (hs.smul continuous_const)))
  map_zero_left q := by
    change honeycombCollapseMap C ε hε
      (((innerRegionHomeomorph C ε hε hε1 hC hR).symm q).1,
        (1 - (0 : ℝ)) • (((innerRegionHomeomorph C ε hε hε1 hC hR).symm q).2 : Plane) +
          (0 : ℝ) • (phaseOrbitVertex : Plane)) = (q : QuotientCentralFibre C ε)
    rw [sub_zero, one_smul, zero_smul, add_zero]
    simpa only [Homeomorph.apply_symm_apply] using
      (innerRegionHomeomorph_honeycomb C ε hε hε1 hC hR
        ((innerRegionHomeomorph C ε hε hε1 hC hR).symm q)).symm
  map_one_left q := by
    change honeycombCollapseMap C ε hε
      (((innerRegionHomeomorph C ε hε hε1 hC hR).symm q).1,
        (1 - (1 : ℝ)) • (((innerRegionHomeomorph C ε hε hε1 hC hR).symm q).2 : Plane) +
          (1 : ℝ) • (phaseOrbitVertex : Plane)) = _
    rw [sub_self, zero_smul, one_smul, zero_add]
    exact honeycombCollapseMap_phaseOrbitVertex C ε hε _

@[simp] theorem innerRegionInclusionHomotopy_apply
    (s : unitInterval) (q : innerRegion C ε hε) :
    innerRegionInclusionHomotopy C ε hε hε1 hC hR (s, q) =
      honeycombCollapseMap C ε hε
        (((innerRegionHomeomorph C ε hε hε1 hC hR).symm q).1,
          (1 - (s : ℝ)) • (((innerRegionHomeomorph C ε hε hε1 hC hR).symm q).2 : Plane) +
            (s : ℝ) • (phaseOrbitVertex : Plane)) := rfl

include hε1 hC hR in
/-- The inclusion of the genuine inner open set into the central fibre is nullhomotopic. -/
theorem innerRegionInclusion_nullhomotopic :
    (innerRegionInclusion C ε hε).Nullhomotopic :=
  ⟨honeycombCollapseMap C ε hε (1, (phaseOrbitVertex : Plane)),
    ⟨innerRegionInclusionHomotopy C ε hε hε1 hC hR⟩⟩

end Wikipedia.HopfProblem.CuspCentralHomology
