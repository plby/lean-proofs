import StackExchange.Puzzling139335.CentralRotation.CircleArcs
import StackExchange.Puzzling139335.CentralRotation.ArcEndpoints
import StackExchange.Puzzling139335.CentralRotation.LocalInvariantArc
import StackExchange.Puzzling139335.CentralRotation.RotationAlgebra.Direct

/-!
# Local rigidity of reversed overlapping Jordan subarcs

A direct isometry mapping two overlapping Jordan subarcs and fixing an
internal point preserves a smaller compact simple arc.  Its endpoints are
permuted.  Fixing them would force the isometry to be the identity; swapping
them forces a half-turn.  A decreasing circle lift supplies the internal
fixed point and excludes identity.
-/

open Set Schoenflies

namespace Puzzling139335.CentralRotation

/-- A nonidentity direct isometry with an internal fixed point in two
matching subarcs of one Jordan curve is the half-turn about that point. -/
theorem eq_halfTurn_of_internal_fixedPoint {C I J : Set Plane} {p q r s z : Plane}
    (hC : IsJordanCurve C) (hI : IsArcBetween I p q) (hJ : IsArcBetween J r s)
    (hIC : I ⊆ C) (hJC : J ⊆ C)
    (k : Plane ≃ᵃⁱ[ℝ] Plane) (a : Circle) (b : ℂ)
    (hform : ∀ x, PlaneIsometries.complexEquiv (k x) =
      (a : ℂ) * PlaneIsometries.complexEquiv x + b)
    (hne : k ≠ AffineIsometryEquiv.refl ℝ Plane)
    (hmap : k '' I = J) (hzI : z ∈ I \ {p, q}) (hzJ : z ∈ J \ {r, s})
    (hfix : k z = z) : k = AffineIsometryEquiv.pointReflection ℝ z := by
  obtain ⟨E, u, v, hE, -, -, hEmap⟩ :=
    exists_invariant_subarc hC hI hJ hIC hJC k hmap hzI hzJ hfix
  rcases hE.endpoints_fixed_or_swapped k.toHomeomorph hEmap with hfixed | hswap
  · exact False.elim (hne (RotationAlgebra.direct_eq_refl_of_two_fixed
      k a b hform hE.ne hfixed.1 hfixed.2))
  · exact RotationAlgebra.direct_eq_pointReflection_of_fixed_of_swap
      k a b hform hfix hE.ne hswap.1 hswap.2

/-- Concrete orientation-reversing arc lemma.  The reversal is a decreasing
real lift in an injective circle parametrization, and overlap is overlap of
the actual open arc sets.  Both the fixed point and the half-turn conclusion
are proved, with no rectifiability or polygonality premise. -/
theorem halfTurn_of_decreasing_lift_overlap
    {f : AddCircle (1 : ℝ) → Plane} (hfc : Continuous f) (hfi : Function.Injective f)
    {a b : ℝ} (hab : a < b) (hshort : b < a + 1)
    (k : Plane ≃ᵃⁱ[ℝ] Plane) (u : Circle) (v : ℂ)
    (hform : ∀ x, PlaneIsometries.complexEquiv (k x) =
      (u : ℂ) * PlaneIsometries.complexEquiv x + v)
    (hsub : k '' (circleParam f '' Icc a b) ⊆ range f)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc a b))
    (hanti : StrictAntiOn φ (Icc a b))
    (hagrees : ∀ t ∈ Icc a b, k (circleParam f t) = circleParam f (φ t))
    (hoverlap : (k '' (circleParam f '' Ioo a b) ∩
      (circleParam f '' Ioo a b)).Nonempty) :
    ∃ z ∈ (circleParam f '' Ioo a b) ∩ k '' (circleParam f '' Ioo a b),
      k = AffineIsometryEquiv.pointReflection ℝ z := by
  have hC := isJordanCurve_range_circle hfc hfi
  have hI := isArcBetween_circleParam hfc hfi hab hshort
  have hIC : circleParam f '' Icc a b ⊆ range f := by
    rintro _ ⟨t, _, rfl⟩
    exact mem_range_self (t : AddCircle (1 : ℝ))
  have hne : k ≠ AffineIsometryEquiv.refl ℝ Plane := by
    intro hk
    apply decreasing_lift_not_identity hab hφ hanti
    intro t ht
    apply hfi
    change circleParam f (φ t) = circleParam f t
    rw [← hagrees t ht, hk]
    rfl
  obtain ⟨t, ht, hfix⟩ := exists_fixedPoint_of_decreasing_lift hfi hφ hanti hagrees hoverlap
  let z := circleParam f t
  have hzopen : z ∈ circleParam f '' Ioo a b := ⟨t, ht, rfl⟩
  have hzI : z ∈ circleParam f '' Icc a b \ {circleParam f a, circleParam f b} := by
    rw [← circleParam_image_Ioo hfi hab hshort]
    exact hzopen
  have hzJ : z ∈ k '' (circleParam f '' Icc a b) \
      {k (circleParam f a), k (circleParam f b)} := by
    rw [← image_pair, ← image_sdiff k.injective]
    exact ⟨z, hzI, hfix⟩
  refine ⟨z, ⟨hzopen, ⟨z, hzopen, hfix⟩⟩, ?_⟩
  exact eq_halfTurn_of_internal_fixedPoint hC hI (hI.image_homeomorph k.toHomeomorph)
    hIC hsub k u v hform hne rfl hzI hzJ hfix

/-- Consequently a direct isometry which is not a half-turn cannot give
an overlapping reversed pair of proper open Jordan subarcs. -/
theorem disjoint_of_decreasing_lift_of_not_halfTurn
    {f : AddCircle (1 : ℝ) → Plane} (hfc : Continuous f) (hfi : Function.Injective f)
    {a b : ℝ} (hab : a < b) (hshort : b < a + 1)
    (k : Plane ≃ᵃⁱ[ℝ] Plane) (u : Circle) (v : ℂ)
    (hform : ∀ x, PlaneIsometries.complexEquiv (k x) =
      (u : ℂ) * PlaneIsometries.complexEquiv x + v)
    (hsub : k '' (circleParam f '' Icc a b) ⊆ range f)
    {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Icc a b))
    (hanti : StrictAntiOn φ (Icc a b))
    (hagrees : ∀ t ∈ Icc a b, k (circleParam f t) = circleParam f (φ t))
    (hnot : ∀ z, k ≠ AffineIsometryEquiv.pointReflection ℝ z) :
    Disjoint (circleParam f '' Ioo a b) (k '' (circleParam f '' Ioo a b)) := by
  apply disjoint_left.2
  intro x hx hkx
  obtain ⟨z, _, hz⟩ := halfTurn_of_decreasing_lift_overlap hfc hfi hab hshort
    k u v hform hsub hφ hanti hagrees ⟨x, hkx, hx⟩
  exact hnot z hz

end Puzzling139335.CentralRotation
