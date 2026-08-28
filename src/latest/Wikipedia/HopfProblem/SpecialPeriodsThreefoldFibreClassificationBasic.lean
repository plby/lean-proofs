import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRegularFibres
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspCritical
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspDifferentialSubmersion

/-!
# The actual differential critical locus of the global sphere projection

Criticality is defined by failure of surjectivity of the differential of
the constructed global map.  The regular normal forms exclude every
unmarked value.  On the literal infinity fibre, the proved native cusp
criterion identifies criticality with the actual multiple-branch locus.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FibreClassification

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace Threefold.space_t2Space

/-- The critical points of the actual global sphere map, defined by
the usual failure of differential surjectivity. -/
def criticalLocus : Set Threefold.Space :=
  {y | ¬Surjective (mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y)}

/-- The actual critical values, rather than a prescribed marked set. -/
def criticalValues : Set RiemannSphere := Threefold.projectionSphere '' criticalLocus

@[simp] theorem mem_criticalLocus (y : Threefold.Space) :
    y ∈ criticalLocus ↔
      ¬Surjective (mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y) := Iff.rfl

@[simp] theorem mem_criticalValues (b : RiemannSphere) :
    b ∈ criticalValues ↔
      ∃ y ∈ criticalLocus, Threefold.projectionSphere y = b := Iff.rfl

theorem not_surjective_of_mfderiv_eq_zero (y : Threefold.Space)
    (hy : mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y = 0) :
    ¬Surjective (mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y) := by
  intro hsurj
  obtain ⟨v, hv⟩ := hsurj (1 : ℂ)
  rw [hy] at hv
  change (0 : ℂ) = 1 at hv
  exact zero_ne_one hv

theorem critical_of_mfderiv_eq_zero (y : Threefold.Space)
    (hy : mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y = 0) : y ∈ criticalLocus :=
  not_surjective_of_mfderiv_eq_zero y hy

/-- The actual submersion normal form gives surjectivity of the actual
global differential at every regular point. -/
theorem regular_mfderiv_surjective (y : Threefold.Space)
    (h_inf : Threefold.projectionSphere y ≠ (∞ : RiemannSphere))
    (h₀ : Threefold.projectionSphere y ≠ ((0 : ℂ) : RiemannSphere))
    (h₁ : Threefold.projectionSphere y ≠ ((1 : ℂ) : RiemannSphere)) :
    Surjective (mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y) :=
  SubmersionDifferential.mfderiv_surjective
    (Threefold.projectionSphere_submersionAt_of_ne y h_inf h₀ h₁)

theorem regular_not_critical (y : Threefold.Space)
    (h_inf : Threefold.projectionSphere y ≠ (∞ : RiemannSphere))
    (h₀ : Threefold.projectionSphere y ≠ ((0 : ℂ) : RiemannSphere))
    (h₁ : Threefold.projectionSphere y ≠ ((1 : ℂ) : RiemannSphere)) :
    y ∉ criticalLocus :=
  fun hy => hy (regular_mfderiv_surjective y h_inf h₀ h₁)

/-- No unmarked sphere point is a critical value.  This is derived from
the global differential rather than put into the definition. -/
theorem critical_projection_marked (y : Threefold.Space) (hy : y ∈ criticalLocus) :
    Threefold.projectionSphere y = (∞ : RiemannSphere) ∨
      Threefold.projectionSphere y = ((0 : ℂ) : RiemannSphere) ∨
      Threefold.projectionSphere y = ((1 : ℂ) : RiemannSphere) := by
  by_contra h
  simp only [not_or] at h
  exact hy (regular_mfderiv_surjective y h.1 h.2.1 h.2.2)

theorem criticalValues_subset_marked :
    criticalValues ⊆ {(∞ : RiemannSphere), ((0 : ℂ) : RiemannSphere),
      ((1 : ℂ) : RiemannSphere)} := by
  rintro b ⟨y, hy, rfl⟩
  exact critical_projection_marked y hy

/-- On the literal infinity fibre, vanishing of the actual sphere
differential is equivalent to differential criticality. -/
theorem cusp_mfderiv_eq_zero_iff_critical (y : Threefold.Space)
    (hy : Threefold.projectionSphere y = (∞ : RiemannSphere)) :
    mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y = 0 ↔ y ∈ criticalLocus := by
  obtain ⟨x, _, rfl⟩ :=
    CuspGeometry.exists_cusp_representative_of_projectionSphere_eq_infty y hy
  exact CuspGeometry.projectionSphere_critical_iff_not_surjective x

/-- The entire critical subset of the infinity fibre is precisely the
three actual double curves, including their two triple intersections. -/
theorem cusp_critical_iff_mem_doubleStratum (y : Threefold.Space)
    (hy : Threefold.projectionSphere y = (∞ : RiemannSphere)) :
    y ∈ criticalLocus ↔ y ∈ CuspGeometry.doubleStratum :=
  (cusp_mfderiv_eq_zero_iff_critical y hy).symm.trans
    (CuspGeometry.fibre_critical_iff_mem_doubleStratum ⟨y, hy⟩)

theorem doubleStratum_subset_criticalLocus : CuspGeometry.doubleStratum ⊆ criticalLocus := by
  intro y hy
  exact (cusp_critical_iff_mem_doubleStratum y
    (CuspGeometry.doubleStratum_subset_sphereCuspFibre hy)).mpr hy

theorem doubleCurve_subset_criticalLocus (i : Fin 3) :
    CuspGeometry.doubleCurve i ⊆ criticalLocus := by
  intro y hy
  apply doubleStratum_subset_criticalLocus
  rw [CuspGeometry.doubleStratum_eq_union]
  exact mem_iUnion.mpr ⟨i, hy⟩

theorem criticalLocus_inter_cuspFibre :
    criticalLocus ∩ CuspGeometry.sphereCuspFibre = CuspGeometry.doubleStratum := by
  ext y
  constructor
  · rintro ⟨hy, hcentral⟩
    exact (cusp_critical_iff_mem_doubleStratum y hcentral).mp hy
  · intro hy
    exact ⟨doubleStratum_subset_criticalLocus hy,
      CuspGeometry.doubleStratum_subset_sphereCuspFibre hy⟩

/-- Infinity is attained by a genuine critical point of the global
map: one of the actual three-branch cusp points. -/
theorem infty_mem_criticalValues : (∞ : RiemannSphere) ∈ criticalValues :=
  ⟨CuspGeometry.lowerTriplePoint,
    doubleCurve_subset_criticalLocus 0 (CuspGeometry.lowerTriplePoint_mem_doubleCurve 0),
    CuspGeometry.lowerTriplePoint_mem_sphereCuspFibre⟩

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FibreClassification
