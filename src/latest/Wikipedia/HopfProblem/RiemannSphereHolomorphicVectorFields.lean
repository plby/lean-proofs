import Wikipedia.HopfProblem.HolomorphicVectorFields
import Wikipedia.HopfProblem.RiemannSphereHolomorphicVectorFieldsCharts
import Wikipedia.HopfProblem.RiemannSphereHolomorphicVectorFieldsChartsSmooth
import Wikipedia.HopfProblem.RiemannSphereHolomorphicVectorFieldsScalar

/-!
# Three zeros force a holomorphic sphere tangent field to vanish

The coefficients are extracted from the actual native tangent section.
Their transition is the actual derivative of complex inversion. The
scalar removable-division and Liouville argument proves vanishing,
without assuming a polynomial classification of sphere vector fields.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.RiemannSphere.HolomorphicVectorFields

/-- A coefficient of the genuine tangent field in one of the two affine charts. -/
def coefficient (v : Wikipedia.HopfProblem.HolomorphicVectorFields.Field ℂ RiemannSphere)
    (b : Bool) (z : ℂ) : ℂ :=
  coordinate b (standardCharts.affineMap b z) (v (standardCharts.affineMap b z))

theorem coefficient_holomorphic
    (v : Wikipedia.HopfProblem.HolomorphicVectorFields.Field ℂ RiemannSphere) (b : Bool) :
    ContDiff ℂ ω (coefficient v b) := by
  apply ContMDiff.contDiff
  intro z
  have hp : standardCharts.affineMap b z ∈ (chartAt ℂ (chartCenter b)).source :=
    (parametrization b z).property
  have hv : ContMDiff 𝓘(ℂ) 𝓘(ℂ).tangent ω
      (fun z => (⟨standardCharts.affineMap b z, v (standardCharts.affineMap b z)⟩ :
        TangentBundle 𝓘(ℂ) RiemannSphere)) :=
    v.contMDiff.comp (standardCharts.affineMap_holomorphic b)
  have ht := tangent_coordinate_contMDiffAt (chartCenter b)
    (p := ⟨standardCharts.affineMap b z, v (standardCharts.affineMap b z)⟩) hp
  have hh := ht.comp z (hv z)
  exact hh

/-- The minus sign and the square come from the native derivative of inversion. -/
theorem coefficient_transition
    (v : Wikipedia.HopfProblem.HolomorphicVectorFields.Field ℂ RiemannSphere)
    {w : ℂ} (hw : w ≠ 0) :
    coefficient v true w = -(w ^ 2) * coefficient v false w⁻¹ := by
  change coordinate true (infinityParametrization w) (v (infinityParametrization w)) =
    -(w ^ 2) * coordinate false ((w⁻¹ : ℂ) : RiemannSphere) (v ((w⁻¹ : ℂ) : RiemannSphere))
  rw [infinityParametrization_of_ne hw]
  exact coordinate_transition hw _

theorem coefficient_eq_zero_of_value_eq_zero
    (v : Wikipedia.HopfProblem.HolomorphicVectorFields.Field ℂ RiemannSphere)
    (b : Bool) (z : ℂ) (hz : v (standardCharts.affineMap b z) = 0) :
    coefficient v b z = 0 := by
  unfold coefficient
  rw [hz]
  have hm : standardCharts.affineMap b z ∈ chartOpen b := (parametrization b z).property
  exact (coordinate_eq_continuousLinearMapAt b hm 0).trans (map_zero _)

/-- A genuine holomorphic tangent field on the standard sphere that
vanishes at zero, one, and infinity is the zero native section. -/
theorem eq_zero_of_three_zeros
    (v : Wikipedia.HopfProblem.HolomorphicVectorFields.Field ℂ RiemannSphere)
    (h₀ : v ((0 : ℂ) : RiemannSphere) = 0)
    (h₁ : v ((1 : ℂ) : RiemannSphere) = 0)
    (h_inf : v (∞ : RiemannSphere) = 0) : v = 0 := by
  have hfinite := (coefficient_holomorphic v false).differentiable (by simp)
  have hinfinity := (coefficient_holomorphic v true).differentiable (by simp)
  have hc₀ := coefficient_eq_zero_of_value_eq_zero v false 0 h₀
  have hc₁ := coefficient_eq_zero_of_value_eq_zero v false 1 h₁
  have hci : coefficient v true 0 = 0 := by
    apply coefficient_eq_zero_of_value_eq_zero
    change v (infinityParametrization 0) = 0
    rw [infinityParametrization_zero]
    exact h_inf
  obtain ⟨hA, hB⟩ := scalar_field_eq_zero hfinite hinfinity
    (fun _ hw => coefficient_transition v hw) hc₀ hc₁ hci
  apply ContMDiffSection.ext
  intro y
  obtain ⟨b, hy⟩ : ∃ b : Bool, y ∈ chartOpen b := by
    rcases mem_chartOpen_cover y with hy | hy
    · exact ⟨false, hy⟩
    · exact ⟨true, hy⟩
  obtain ⟨z, hz⟩ := parametrization_surjective b ⟨y, hy⟩
  have hz' : standardCharts.affineMap b z = y := congrArg Subtype.val hz
  have hc : coefficient v b z = 0 := by
    cases b
    · exact congrFun hA z
    · exact congrFun hB z
  apply coordinate_injective b hy
  calc
    coordinate b y (v y) = 0 :=
      (congrArg (fun p : RiemannSphere => coordinate b p (v p)) hz').symm.trans hc
    _ = coordinate b y 0 := by
      rw [coordinate_eq_continuousLinearMapAt b hy, map_zero]

end Wikipedia.HopfProblem.RiemannSphere.HolomorphicVectorFields
