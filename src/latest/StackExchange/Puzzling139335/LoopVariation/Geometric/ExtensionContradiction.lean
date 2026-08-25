import StackExchange.Puzzling139335.LoopVariation.Geometric.ArcCuts
import StackExchange.Puzzling139335.LoopVariation.Geometric.CutPairs

/-!
# The nonrectifiable common-cut contradiction

When congruent Jordan boundaries share one interface, neither remaining arc can
contain an isometric copy of the other with genuine arcs left over on both
sides. The positive truncated variation of a leftover contradicts the common
interface cancellation estimate at sufficiently small resolution.
-/

open Set

namespace Puzzling139335.LoopVariation

noncomputable section

/-- The analytic contradiction used in the antipodal-endpoint argument. Every
variation property here has already been proved for its concrete supremum. -/
theorem common_cut_excludes_three_arc_extension
    {C₁ C₂ Γ M N K D : Set Schoenflies.Plane}
    {p q r s u v w z : Schoenflies.Plane}
    (hcut₁ : Schoenflies.IsCutPair C₁ p q Γ M)
    (hcut₂ : Schoenflies.IsCutPair C₂ r s Γ N)
    {e g : Schoenflies.Plane → Schoenflies.Plane}
    (he : Isometry e) (hcongr : e '' C₁ = C₂) (hg : Isometry g)
    (hK : Schoenflies.IsArcBetween K u v)
    (hM : Schoenflies.IsArcBetween (g '' M) v w)
    (hD : Schoenflies.IsArcBetween D w z)
    (hmeetKM : ∀ x ∈ K, x ∈ g '' M → x = v)
    (hmeetD : ∀ x ∈ K ∪ g '' M, x ∈ D → x = w)
    (hunion : (K ∪ g '' M) ∪ D = N) : False := by
  obtain ⟨η, hη, hbound⟩ := arcVariation_exists_positive_lower_bound hK.isArc
  have hε : 0 < η / 4 := by positivity
  have hsmall : η / 4 ≤ η := by linarith
  have hKpos := hbound (η / 4) hε hsmall
  have hDnonneg := arcVariation_nonneg hD.isArc hε
  have hext := (arcVariation_three_arc_bounds hK hM hD hmeetKM hmeetD hε).1
  rw [hunion, arcVariation_image_isometry (η / 4) hcut₁.snd.isArc hg] at hext
  have hcancel := abs_arcVariation_sub_le_of_common_arc_isometry hcut₁ hcut₂
    he hcongr hε
  have hcancel' := (abs_le.mp hcancel).1
  linarith

end

end Puzzling139335.LoopVariation
