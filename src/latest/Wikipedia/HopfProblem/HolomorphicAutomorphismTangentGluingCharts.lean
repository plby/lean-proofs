import Wikipedia.HopfProblem.HolomorphicVectorFields
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Native tangent vectors from preferred chart coordinates

All coordinates in this file come from `chartAt E a` on the original
analytic manifold and from the corresponding original tangent-bundle
trivialization. Inverse trivialization is proved to be the genuine
differential of the inverse chart. The transition law is the Fréchet
derivative of the actual chart transition.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismTangentGluing

variable {E M : Type*} [NormedAddCommGroup E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The part of a preferred chart lying over a coordinate domain. -/
def chartDomain (a : M) (V : Set E) : Set M :=
  (chartAt E a).source ∩ (chartAt E a) ⁻¹' V

theorem chartDomain_isOpen (a : M) {V : Set E} (hV : IsOpen V) :
    IsOpen (chartDomain a V) := (chartAt E a).isOpen_inter_preimage hV

variable [NormedSpace ℂ E] [IsManifold 𝓘(ℂ, E) ω M]

/-- The actual tangent-trivialization coordinate at a preferred chart. -/
def chartCoordinate (a x : M) (v : TangentSpace 𝓘(ℂ, E) x) : E :=
  (trivializationAt E (TangentSpace 𝓘(ℂ, E)) a ⟨x, v⟩).2

/-- Convert a coordinate vector to the original native tangent space.
Outside the chart source the total linear inverse has its usual zero value. -/
def chartVector (a x : M) (w : E) : TangentSpace 𝓘(ℂ, E) x :=
  (trivializationAt E (TangentSpace 𝓘(ℂ, E)) a).symmL ℂ x w

theorem chartCoordinate_eq_continuousLinearMapAt (a : M) {x : M}
    (hx : x ∈ (chartAt E a).source) (v : TangentSpace 𝓘(ℂ, E) x) :
    chartCoordinate a x v =
      (trivializationAt E (TangentSpace 𝓘(ℂ, E)) a).continuousLinearMapAt ℂ x v :=
  ((trivializationAt E (TangentSpace 𝓘(ℂ, E)) a).continuousLinearMapAt_apply_of_mem
    ℂ hx v).symm

theorem chartCoordinate_chartVector (a : M) {x : M}
    (hx : x ∈ (chartAt E a).source) (w : E) :
    chartCoordinate a x (chartVector a x w) = w := by
  rw [chartCoordinate_eq_continuousLinearMapAt a hx]
  exact (trivializationAt E (TangentSpace 𝓘(ℂ, E)) a).continuousLinearMapAt_symmL hx w

theorem chartVector_chartCoordinate (a : M) {x : M}
    (hx : x ∈ (chartAt E a).source) (v : TangentSpace 𝓘(ℂ, E) x) :
    chartVector a x (chartCoordinate a x v) = v := by
  rw [chartCoordinate_eq_continuousLinearMapAt a hx]
  exact (trivializationAt E (TangentSpace 𝓘(ℂ, E)) a).symmL_continuousLinearMapAt hx v

theorem chartCoordinate_injective (a : M) {x : M}
    (hx : x ∈ (chartAt E a).source) : Function.Injective (chartCoordinate (E := E) a x) :=
  Function.LeftInverse.injective (chartVector_chartCoordinate (E := E) a hx)

theorem chartVector_injective (a : M) {x : M}
    (hx : x ∈ (chartAt E a).source) : Function.Injective (chartVector (E := E) a x) :=
  Function.LeftInverse.injective (chartCoordinate_chartVector (E := E) a hx)

@[simp] theorem chartVector_zero (a x : M) : chartVector a x (0 : E) = 0 :=
  map_zero _

theorem chartVector_eq_zero_iff (a : M) {x : M}
    (hx : x ∈ (chartAt E a).source) (w : E) :
    chartVector a x w = 0 ↔ w = 0 := by
  rw [← chartVector_zero a x, (chartVector_injective a hx).eq_iff]

/-- Preferred tangent coordinates are exactly the actual chart differential. -/
theorem chartCoordinate_eq_mfderiv (a : M) {x : M}
    (hx : x ∈ (chartAt E a).source) (v : TangentSpace 𝓘(ℂ, E) x) :
    chartCoordinate a x v = mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (chartAt E a) x v := by
  rw [chartCoordinate_eq_continuousLinearMapAt a hx,
    TangentBundle.continuousLinearMapAt_trivializationAt hx]
  rfl

/-- Inverse tangent coordinates are the differential pushforward by the
actual inverse chart, not a separately chosen identification. -/
theorem chartVector_eq_mfderiv_symm (a : M) {x : M}
    (hx : x ∈ (chartAt E a).source) (w : E) :
    chartVector a x w =
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (chartAt E a).symm ((chartAt E a) x) w := by
  unfold chartVector
  rw [TangentBundle.symmL_trivializationAt hx]
  simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ]
  rfl

theorem chartCoordinate_eq_tangentCoordChange (a x : M)
    (v : TangentSpace 𝓘(ℂ, E) x) :
    chartCoordinate a x v = tangentCoordChange 𝓘(ℂ, E) x a x v := rfl

@[simp] theorem chartCoordinate_zero (a x : M) :
    chartCoordinate a x (0 : TangentSpace 𝓘(ℂ, E) x) = 0 := by
  rw [chartCoordinate_eq_tangentCoordChange]
  exact map_zero _

/-- The native tangent cocycle is the derivative of the ordinary coordinate
change on the model vector space. -/
theorem tangentCoordChange_eq_fderiv (a b x : M) :
    tangentCoordChange 𝓘(ℂ, E) a b x =
      fderiv ℂ ((chartAt E b) ∘ (chartAt E a).symm) ((chartAt E a) x) := by
  rw [tangentCoordChange_def]
  simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ]
  rfl

theorem chartCoordinate_transition (a b : M) {x : M}
    (ha : x ∈ (chartAt E a).source) (hb : x ∈ (chartAt E b).source)
    (v : TangentSpace 𝓘(ℂ, E) x) :
    chartCoordinate b x v =
      fderiv ℂ ((chartAt E b) ∘ (chartAt E a).symm) ((chartAt E a) x)
        (chartCoordinate a x v) := by
  have hcomp := tangentCoordChange_comp (I := 𝓘(ℂ, E))
    (w := x) (x := a) (y := b) (z := x) (v := v)
    ⟨⟨mem_extChartAt_source x, by rwa [extChartAt_source]⟩,
      by rwa [extChartAt_source]⟩
  rw [chartCoordinate_eq_tangentCoordChange, chartCoordinate_eq_tangentCoordChange,
    ← hcomp, tangentCoordChange_eq_fderiv]

/-- An actual local native section produced by coordinate functions. -/
def chartSection (a : M) (h : E → E) (x : M) : TangentSpace 𝓘(ℂ, E) x :=
  chartVector a x (h ((chartAt E a) x))

theorem chartSection_coordinate (a : M) (h : E → E) {x : M}
    (hx : x ∈ (chartAt E a).source) :
    chartCoordinate a x (chartSection a h x) = h ((chartAt E a) x) :=
  chartCoordinate_chartVector a hx _

/-- Analytic coordinate functions define an analytic map to the original
tangent bundle on the corresponding chart domain. -/
theorem chartSection_holomorphicOn (a : M) {V : Set E} (hV : IsOpen V)
    {h : E → E} (hh : ContDiffOn ℂ ω h V) :
    ContMDiffOn 𝓘(ℂ, E) (𝓘(ℂ, E).prod 𝓘(ℂ, E)) ω
      (fun x => (⟨x, chartSection a h x⟩ : TangentBundle 𝓘(ℂ, E) M)) (chartDomain a V) := by
  let e := trivializationAt E (TangentSpace 𝓘(ℂ, E)) a
  apply (e.contMDiffOn_section_iff (chartDomain_isOpen a hV) (fun x hx => hx.1)).mpr
  have hc : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, E) ω (chartAt E a) (chartDomain a V) :=
    contMDiffOn_chart.mono inter_subset_left
  have hh' := hh.contMDiffOn.comp hc (fun x hx => hx.2)
  exact hh'.congr fun x hx => chartSection_coordinate a h hx.1

/-- Genuine differential transition compatibility makes the native local
sections equal on the overlap. -/
theorem chartSection_eq_of_transition (a b : M) {h k : E → E} {x : M}
    (ha : x ∈ (chartAt E a).source) (hb : x ∈ (chartAt E b).source)
    (hcompat : fderiv ℂ ((chartAt E b) ∘ (chartAt E a).symm) ((chartAt E a) x)
      (h ((chartAt E a) x)) = k ((chartAt E b) x)) :
    chartSection a h x = chartSection b k x := by
  apply chartCoordinate_injective b hb
  rw [chartCoordinate_transition a b ha hb, chartSection_coordinate a h ha,
    chartSection_coordinate b k hb]
  exact hcompat

end Wikipedia.HopfProblem.HolomorphicAutomorphismTangentGluing
