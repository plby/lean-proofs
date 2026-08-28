import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFibreClassificationBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldFibreClassificationElliptic

/-!
# Exact critical points and values of the constructed sphere projection

The critical locus is defined by its actual manifold differential.  It
consists of the entire two finite multiple fibres and the three actual
double curves of the infinity fibre.  The critical values are exactly
infinity, zero, and one; each value is attained by a proved critical point.
-/

noncomputable section

open Function Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.FibreClassification

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

attribute [local instance] Threefold.chartedSpace Threefold.space_t2Space

theorem zeroFibre_subset_criticalLocus :
    Threefold.projectionSphere ⁻¹' {((0 : ℂ) : RiemannSphere)} ⊆ criticalLocus :=
  fun y hy => critical_of_mfderiv_eq_zero y (zero_mfderiv_eq_zero y hy)

theorem oneFibre_subset_criticalLocus :
    Threefold.projectionSphere ⁻¹' {((1 : ℂ) : RiemannSphere)} ⊆ criticalLocus :=
  fun y hy => critical_of_mfderiv_eq_zero y (one_mfderiv_eq_zero y hy)

/-- The exact differential critical locus of the actual global map:
both finite multiple fibres and only the double-curve locus at infinity. -/
theorem criticalLocus_eq_fibres_union_doubleStratum :
    criticalLocus =
      (Threefold.projectionSphere ⁻¹' {((0 : ℂ) : RiemannSphere)}) ∪
      (Threefold.projectionSphere ⁻¹' {((1 : ℂ) : RiemannSphere)}) ∪
      CuspGeometry.doubleStratum := by
  ext y
  constructor
  · intro hy
    rcases critical_projection_marked y hy with h_inf | h₀ | h₁
    · exact Or.inr ((cusp_critical_iff_mem_doubleStratum y h_inf).mp hy)
    · exact Or.inl (Or.inl h₀)
    · exact Or.inl (Or.inr h₁)
  · rintro ((h₀ | h₁) | hc)
    · exact zeroFibre_subset_criticalLocus h₀
    · exact oneFibre_subset_criticalLocus h₁
    · exact doubleStratum_subset_criticalLocus hc

/-- The cusp contribution is the union of the three actual double
curves, rather than the whole infinity fibre. -/
theorem criticalLocus_eq_fibres_union_doubleCurves :
    criticalLocus =
      (Threefold.projectionSphere ⁻¹' {((0 : ℂ) : RiemannSphere)}) ∪
      (Threefold.projectionSphere ⁻¹' {((1 : ℂ) : RiemannSphere)}) ∪
      (⋃ i : Fin 3, CuspGeometry.doubleCurve i) := by
  rw [criticalLocus_eq_fibres_union_doubleStratum, CuspGeometry.doubleStratum_eq_union]

/-- In this one-dimensional target, the proved local forms show
directly that failure of surjectivity is equivalent to a zero differential. -/
theorem mfderiv_eq_zero_iff_critical (y : Threefold.Space) :
    mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y = 0 ↔ y ∈ criticalLocus := by
  constructor
  · exact critical_of_mfderiv_eq_zero y
  · intro hy
    rcases critical_projection_marked y hy with h_inf | h₀ | h₁
    · exact (cusp_mfderiv_eq_zero_iff_critical y h_inf).mpr hy
    · exact zero_mfderiv_eq_zero y h₀
    · exact one_mfderiv_eq_zero y h₁

theorem mfderiv_eq_zero_iff (y : Threefold.Space) :
    mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y = 0 ↔
      Threefold.projectionSphere y = ((0 : ℂ) : RiemannSphere) ∨
      Threefold.projectionSphere y = ((1 : ℂ) : RiemannSphere) ∨
      y ∈ CuspGeometry.doubleStratum := by
  rw [mfderiv_eq_zero_iff_critical, criticalLocus_eq_fibres_union_doubleStratum]
  exact or_assoc

theorem mfderiv_surjective_iff (y : Threefold.Space) :
    Surjective (mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y) ↔
      Threefold.projectionSphere y ≠ ((0 : ℂ) : RiemannSphere) ∧
      Threefold.projectionSphere y ≠ ((1 : ℂ) : RiemannSphere) ∧
      y ∉ CuspGeometry.doubleStratum := by
  classical
  have he : ¬Surjective (mfderiv IF 𝓘(ℂ) Threefold.projectionSphere y) ↔
      Threefold.projectionSphere y = ((0 : ℂ) : RiemannSphere) ∨
      Threefold.projectionSphere y = ((1 : ℂ) : RiemannSphere) ∨
      y ∈ CuspGeometry.doubleStratum :=
    (mfderiv_eq_zero_iff_critical y).symm.trans (mfderiv_eq_zero_iff y)
  simpa only [not_not, not_or] using not_congr he

theorem criticalLocus_compact : IsCompact criticalLocus := by
  rw [criticalLocus_eq_fibres_union_doubleStratum]
  exact ((Threefold.projectionSphere_fibre_compact _).union
    (Threefold.projectionSphere_fibre_compact _)).union CuspGeometry.doubleStratum_compact

theorem criticalLocus_isClosed : IsClosed criticalLocus := criticalLocus_compact.isClosed

/-- A genuine point of the entire order-three fibre attains zero as
a critical value of the constructed global map. -/
theorem zero_mem_criticalValues : ((0 : ℂ) : RiemannSphere) ∈ criticalValues := by
  obtain ⟨y, hy⟩ := Threefold.projectionSphere_surjective ((0 : ℂ) : RiemannSphere)
  exact ⟨y, zeroFibre_subset_criticalLocus hy, hy⟩

/-- The actual order-four fibre similarly supplies a critical point
above one. -/
theorem one_mem_criticalValues : ((1 : ℂ) : RiemannSphere) ∈ criticalValues := by
  obtain ⟨y, hy⟩ := Threefold.projectionSphere_surjective ((1 : ℂ) : RiemannSphere)
  exact ⟨y, oneFibre_subset_criticalLocus hy, hy⟩

/-- Exact critical values of the actual unconditional compact threefold. -/
theorem criticalValues_eq :
    criticalValues = {(∞ : RiemannSphere), ((0 : ℂ) : RiemannSphere),
      ((1 : ℂ) : RiemannSphere)} := by
  apply Subset.antisymm criticalValues_subset_marked
  intro b hb
  rcases hb with rfl | rfl | rfl
  · exact infty_mem_criticalValues
  · exact zero_mem_criticalValues
  · exact one_mem_criticalValues

theorem criticalValues_card : criticalValues.ncard = 3 := by
  rw [criticalValues_eq]
  have h₀₁ : ((0 : ℂ) : RiemannSphere) ≠ ((1 : ℂ) : RiemannSphere) :=
    fun h => (zero_ne_one : (0 : ℂ) ≠ 1) (OnePoint.coe_injective h)
  simp [Set.ncard_insert_of_notMem, h₀₁]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.FibreClassification
