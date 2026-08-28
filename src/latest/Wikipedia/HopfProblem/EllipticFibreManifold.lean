import Wikipedia.HopfProblem.EllipticCentralImmersion
import Wikipedia.HopfProblem.EllipticNonzeroFibres
import Wikipedia.HopfProblem.EllipticFibreManifoldCore

/-!
# The complex structures induced on the actual elliptic filling fibres

Each fibre has its literal subspace topology.  Its analytic charts are the
restrictions of ambient immersion normal forms.  The central quotient
surface supplies these normal forms at zero; a period torus supplies them
away from zero.  The atlas away from zero is indexed by the actual base
value, rather than by an arbitrary choice of its root.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic

open SpecialPeriods

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ FamilyModel

abbrev FillingFibre (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) (b : Disc) :=
  fillingProjection j v hv ⁻¹' {b}

theorem centralFibreHomeomorph_isImmersionOfComplement (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω
      (Subtype.val ∘ centralFibreHomeomorph j v hv) :=
  centralFibreInclusion_isImmersionOfComplement j v hv

/-- Ambient-normal-form coordinates on the literal central fibre. -/
@[instance_reducible] def centralFibreChartedSpace (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    ChartedSpace ComplexPlane₂ (FillingFibre j v hv Elliptic.discZero) :=
  EmbeddedFibre.chartedSpace (centralFibreHomeomorph j v hv)
    (centralFibreHomeomorph_isImmersionOfComplement j v hv)

theorem centralFibre_isManifold (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := centralFibreChartedSpace j v hv
    IsManifold I₂ ω (FillingFibre j v hv Elliptic.discZero) :=
  EmbeddedFibre.isManifold (centralFibreHomeomorph j v hv)
    (centralFibreHomeomorph_isImmersionOfComplement j v hv)

theorem centralFibre_inclusion_isImmersionOfComplement (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    letI := centralFibreChartedSpace j v hv
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω
      (Subtype.val : FillingFibre j v hv Elliptic.discZero → Filling j v hv) :=
  EmbeddedFibre.inclusion_isImmersionOfComplement (centralFibreHomeomorph j v hv)
    (centralFibreHomeomorph_isImmersionOfComplement j v hv)

/-- A chosen root is used only to select immersion normal forms, not to
change the fibre's underlying set or its subspace topology. -/
def fillingFibreRoot (j : Kind) (b : Disc) : Disc :=
  (discPower_surjective j.order j.order_pos b).choose

@[simp] theorem discPower_fillingFibreRoot (j : Kind) (b : Disc) :
    discPower j.order j.order_pos (fillingFibreRoot j b) = b :=
  (discPower_surjective j.order j.order_pos b).choose_spec

theorem fillingFibreRoot_ne_zero (j : Kind) (b : Disc) (hb : (b : ℂ) ≠ 0) :
    (fillingFibreRoot j b : ℂ) ≠ 0 := by
  intro hz
  apply hb
  rw [← discPower_fillingFibreRoot j b, discPower_coe, hz, zero_pow j.order_pos.ne']

theorem torusFibreMap_isImmersionOfComplement (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (z : Disc) :
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω (torusFibreMap j v hv z) :=
  fillingFibreInclusion_isImmersionOfComplement j v hv z

/-- The chosen root torus is identified with the literal fibre over `b`. -/
def nonzeroFibreHomeomorph (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (b : Disc) (hb : (b : ℂ) ≠ 0) :
    ((familyPeriods j).point (fillingFibreRoot j b)).Torus ≃ₜ FillingFibre j v hv b :=
  (torusFibreHomeomorph j v hv (fillingFibreRoot j b) (fillingFibreRoot_ne_zero j b hb)).trans
    (Homeomorph.setCongr (by rw [discPower_fillingFibreRoot]))

@[simp] theorem nonzeroFibreHomeomorph_coe (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (b : Disc) (hb : (b : ℂ) ≠ 0)
    (x : ((familyPeriods j).point (fillingFibreRoot j b)).Torus) :
    (nonzeroFibreHomeomorph j v hv b hb x : Filling j v hv) =
      torusFibreMap j v hv (fillingFibreRoot j b) x := rfl

theorem nonzeroFibreHomeomorph_isImmersionOfComplement (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (b : Disc) (hb : (b : ℂ) ≠ 0) :
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω
      (Subtype.val ∘ nonzeroFibreHomeomorph j v hv b hb) :=
  torusFibreMap_isImmersionOfComplement j v hv (fillingFibreRoot j b)

/-- Ambient-normal-form coordinates on the literal nonzero fibre over `b`. -/
@[instance_reducible] def nonzeroFibreChartedSpace (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (b : Disc) (hb : (b : ℂ) ≠ 0) :
    ChartedSpace ComplexPlane₂ (FillingFibre j v hv b) :=
  EmbeddedFibre.chartedSpace (nonzeroFibreHomeomorph j v hv b hb)
    (nonzeroFibreHomeomorph_isImmersionOfComplement j v hv b hb)

theorem nonzeroFibre_isManifold (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    (b : Disc) (hb : (b : ℂ) ≠ 0) :
    letI := nonzeroFibreChartedSpace j v hv b hb
    IsManifold I₂ ω (FillingFibre j v hv b) :=
  EmbeddedFibre.isManifold (nonzeroFibreHomeomorph j v hv b hb)
    (nonzeroFibreHomeomorph_isImmersionOfComplement j v hv b hb)

theorem nonzeroFibre_inclusion_isImmersionOfComplement (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (b : Disc) (hb : (b : ℂ) ≠ 0) :
    letI := nonzeroFibreChartedSpace j v hv b hb
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω
      (Subtype.val : FillingFibre j v hv b → Filling j v hv) :=
  EmbeddedFibre.inclusion_isImmersionOfComplement (nonzeroFibreHomeomorph j v hv b hb)
    (nonzeroFibreHomeomorph_isImmersionOfComplement j v hv b hb)

/-- One selected ambient-induced atlas for every actual filling fibre. -/
@[instance_reducible] def fillingFibreChartedSpace (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (b : Disc) : ChartedSpace ComplexPlane₂ (FillingFibre j v hv b) := by
  classical
  by_cases hb : b = Elliptic.discZero
  · subst b
    exact centralFibreChartedSpace j v hv
  · exact nonzeroFibreChartedSpace j v hv b (fun he => hb (Subtype.ext he))

@[simp] theorem fillingFibreChartedSpace_zero (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    fillingFibreChartedSpace j v hv Elliptic.discZero = centralFibreChartedSpace j v hv := by
  simp [fillingFibreChartedSpace]

theorem fillingFibreChartedSpace_nonzero (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (b : Disc) (hb : (b : ℂ) ≠ 0) :
    fillingFibreChartedSpace j v hv b = nonzeroFibreChartedSpace j v hv b hb := by
  have hne : b ≠ Elliptic.discZero := fun h => hb (congrArg Subtype.val h)
  simp [fillingFibreChartedSpace, hne]

theorem fillingFibre_isManifold (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) (b : Disc) :
    letI := fillingFibreChartedSpace j v hv b
    IsManifold I₂ ω (FillingFibre j v hv b) := by
  by_cases hb : (b : ℂ) = 0
  · have he : b = Elliptic.discZero := Subtype.ext hb
    subst b
    rw [fillingFibreChartedSpace_zero]
    exact centralFibre_isManifold j v hv
  · rw [fillingFibreChartedSpace_nonzero j v hv b hb]
    exact nonzeroFibre_isManifold j v hv b hb

theorem fillingFibre_inclusion_isImmersionOfComplement (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (b : Disc) :
    letI := fillingFibreChartedSpace j v hv b
    Manifold.IsImmersionOfComplement ℂ I₂ I₃ ω
      (Subtype.val : FillingFibre j v hv b → Filling j v hv) := by
  by_cases hb : (b : ℂ) = 0
  · have he : b = Elliptic.discZero := Subtype.ext hb
    subst b
    rw [fillingFibreChartedSpace_zero]
    exact centralFibre_inclusion_isImmersionOfComplement j v hv
  · rw [fillingFibreChartedSpace_nonzero j v hv b hb]
    exact nonzeroFibre_inclusion_isImmersionOfComplement j v hv b hb

theorem fillingFibre_inclusion_holomorphic (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (b : Disc) :
    letI := fillingFibreChartedSpace j v hv b
    ContMDiff I₂ I₃ ω (Subtype.val : FillingFibre j v hv b → Filling j v hv) := by
  let := fillingFibreChartedSpace j v hv b
  exact (fillingFibre_inclusion_isImmersionOfComplement j v hv b).contMDiff

/-- Every chosen fibre chart is literally a restricted ambient chart on
the zero-transverse-coordinate slice.  The source equality uses the actual
subspace topology; the two formulas identify both chart directions. -/
theorem fillingFibre_charts_are_ambient_slices (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (b : Disc) (x : FillingFibre j v hv b) :
    letI := fillingFibreChartedSpace j v hv b
    ∃ c : OpenPartialHomeomorph (Filling j v hv) FamilyModel,
      ∃ L : (ComplexPlane₂ × ℂ) ≃L[ℂ] FamilyModel,
        c ∈ IsManifold.maximalAtlas I₃ ω (Filling j v hv) ∧
        (chartAt ComplexPlane₂ x).source = Subtype.val ⁻¹' c.source ∧
        (∀ y ∈ (chartAt ComplexPlane₂ x).source,
          c (y : Filling j v hv) = L (chartAt ComplexPlane₂ x y, 0)) ∧
        (∀ z ∈ (chartAt ComplexPlane₂ x).target,
          ((chartAt ComplexPlane₂ x).symm z : Filling j v hv) = c.symm (L (z, 0))) := by
  by_cases hb : (b : ℂ) = 0
  · have he : b = Elliptic.discZero := Subtype.ext hb
    subst b
    rw [fillingFibreChartedSpace_zero]
    let e := centralFibreHomeomorph j v hv
    let hι := centralFibreHomeomorph_isImmersionOfComplement j v hv
    obtain ⟨c, hc, hs, hf, hi⟩ := EmbeddedFibre.exists_ambient_restriction e hι x
    exact ⟨c, EmbeddedFibre.coordinateEquiv e hι x, hc, hs, hf, hi⟩
  · rw [fillingFibreChartedSpace_nonzero j v hv b hb]
    let e := nonzeroFibreHomeomorph j v hv b hb
    let hι := nonzeroFibreHomeomorph_isImmersionOfComplement j v hv b hb
    obtain ⟨c, hc, hs, hf, hi⟩ := EmbeddedFibre.exists_ambient_restriction e hι x
    exact ⟨c, EmbeddedFibre.coordinateEquiv e hι x, hc, hs, hf, hi⟩

end Wikipedia.HopfProblem.Elliptic
