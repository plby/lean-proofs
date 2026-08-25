import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.GlobalSupport.MiddleNormals
import StackExchange.Puzzling139335.N4MiddleInvolutions.Reflection.GlobalSupport.SourceNormal

/-!
# A global supporting base is impossible for the middle reflection pair

The actual image of the outer piece's unit base gives a unit supporting
normal of the convex hull of the middle union. Its real coordinate is
nonzero by the nonaxis placement theorem. The two reflection symmetries
force that same coordinate to vanish by the finite-normal obstruction.
-/

open Set ComplexConjugate

namespace Puzzling139335.N4MiddleInvolutions.Reflection

open PlaneIsometries

/-- An actual placement of the bottom outer piece into the first middle
piece cannot put the entire middle union above its base when an ordinary
reflection carries that middle piece onto the other one. -/
theorem false_of_global_base_support {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 2 = d.piece 3)
    (c : ℂ) (u : Circle)
    (hform : ∀ p, complexEquiv (e p) =
      c + (u : ℂ) * conj ((complexEquiv p - c) / (u : ℂ)))
    (f : Plane ≃ᵃⁱ[ℝ] Plane) (hf : f '' d.piece 0 = d.piece 2)
    (hsupport : ∀ z ∈ d.piece 2 ∪ d.piece 3, 0 ≤ (f.symm z) 1) : False := by
  obtain ⟨z, hz, hzne⟩ :=
    exists_oblique_unit_normal_of_global_base_support h hc f hf hsupport
  exact hzne (middleHull_unit_support_normal_re_eq_zero h hc e he c u hform hz)

end Puzzling139335.N4MiddleInvolutions.Reflection
