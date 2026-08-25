import StackExchange.Puzzling139335.Basic
import StackExchange.Puzzling139335.JordanRegion

/-!
# Connected interiors cannot cross a fixed level

For a reflection, the fixed level is its mirror line. The argument uses
connectedness and regular closedness of a Jordan region, without area or
any assumptions on its boundary length.
-/

open Set

namespace Puzzling139335.ReflectionSeparation

theorem interior_avoids_fixed_level {P Q : Set Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q)
    (hdis : Disjoint (interior P) (interior Q))
    (f : Plane → ℝ) (c : ℝ) (hfix : ∀ x, f x = c → e x = x) :
    ∀ x ∈ interior P, f x ≠ c := by
  intro x hx hlevel
  exact (not_mem_interior_of_fixed_congruence e he hdis (hfix x hlevel)).1 hx

/-- The connected interior lies strictly on one side of a continuous level
whose points are fixed by a congruence to a disjoint-interior region. -/
theorem interior_lt_or_gt_of_fixed_level {P Q : Set Plane}
    (hP : IsJordanRegion P) (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q)
    (hdis : Disjoint (interior P) (interior Q))
    (f : Plane → ℝ) (hf : Continuous f) (c : ℝ)
    (hfix : ∀ x, f x = c → e x = x) :
    (∀ x ∈ interior P, f x < c) ∨ (∀ x ∈ interior P, c < f x) := by
  have h := hP.isConnected_interior.isPreconnected.mapsTo_Ioi_or_Iio hf.continuousOn
    (interior_avoids_fixed_level e he hdis f c hfix)
  exact h.symm

/-- Closing the connected interior places the entire Jordan region in one
of the two closed sides of the fixed level. -/
theorem subset_le_or_ge_of_fixed_level {P Q : Set Plane}
    (hP : IsJordanRegion P) (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q)
    (hdis : Disjoint (interior P) (interior Q))
    (f : Plane → ℝ) (hf : Continuous f) (c : ℝ)
    (hfix : ∀ x, f x = c → e x = x) :
    P ⊆ {x | f x ≤ c} ∨ P ⊆ {x | c ≤ f x} := by
  obtain hlt | hgt := interior_lt_or_gt_of_fixed_level hP e he hdis f hf c hfix
  · left
    have hsub : interior P ⊆ {x | f x ≤ c} := fun x hx => (hlt x hx).le
    have hcl := closure_minimal hsub (isClosed_le hf continuous_const)
    rwa [hP.closure_interior] at hcl
  · right
    have hsub : interior P ⊆ {x | c ≤ f x} := fun x hx => (hgt x hx).le
    have hcl := closure_minimal hsub (isClosed_le continuous_const hf)
    rwa [hP.closure_interior] at hcl

/-- A single point strictly below the mirror selects the lower closed side. -/
theorem subset_le_of_fixed_level_of_mem_lt {P Q : Set Plane}
    (hP : IsJordanRegion P) (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q)
    (hdis : Disjoint (interior P) (interior Q))
    (f : Plane → ℝ) (hf : Continuous f) (c : ℝ)
    (hfix : ∀ x, f x = c → e x = x) {x : Plane}
    (hx : x ∈ P) (hlt : f x < c) : P ⊆ {y | f y ≤ c} := by
  obtain hle | hge := subset_le_or_ge_of_fixed_level hP e he hdis f hf c hfix
  · exact hle
  · exact False.elim (not_le_of_gt hlt (hge hx))

/-- A single point strictly above the mirror selects the upper closed side. -/
theorem subset_ge_of_fixed_level_of_mem_gt {P Q : Set Plane}
    (hP : IsJordanRegion P) (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' P = Q)
    (hdis : Disjoint (interior P) (interior Q))
    (f : Plane → ℝ) (hf : Continuous f) (c : ℝ)
    (hfix : ∀ x, f x = c → e x = x) {x : Plane}
    (hx : x ∈ P) (hgt : c < f x) : P ⊆ {y | c ≤ f y} := by
  obtain hle | hge := subset_le_or_ge_of_fixed_level hP e he hdis f hf c hfix
  · exact False.elim (not_le_of_gt hgt (hle hx))
  · exact hge

end Puzzling139335.ReflectionSeparation
