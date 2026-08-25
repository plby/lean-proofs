import StackExchange.Puzzling139335.N4OuterPair.Midline
import StackExchange.Puzzling139335.N4OuterPair.Remainder
import StackExchange.Puzzling139335.JordanInvolution

/-!
# Centers and invariant middle unions

A nonempty compact plane set has at most one center of central symmetry.
Every affine symmetry of such a set fixes that center. These facts also
dispose of the exceptional case in which the outer pair is a half-turn
pair and the middle congruence is an involution.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions

def middleUnion (d : SquareDissection) : Set Plane := d.piece 2 ∪ d.piece 3

theorem middleUnion_isCompact (d : SquareDissection) : IsCompact (middleUnion d) :=
  (d.jordan 2).isCompact.union (d.jordan 3).isCompact

theorem middleUnion_nonempty (d : SquareDissection) : (middleUnion d).Nonempty := by
  obtain ⟨p, hp⟩ := (d.jordan 2).interior_nonempty
  exact ⟨p, Or.inl (interior_subset hp)⟩

theorem middleUnion_subset_square (d : SquareDissection) : middleUnion d ⊆ unitSquare :=
  union_subset (d.piece_subset 2) (d.piece_subset 3)

theorem pointReflection_coord (c p : Plane) (i : Fin 2) :
    AffineIsometryEquiv.pointReflection ℝ c p i = 2 * c i - p i := by
  rw [AffineIsometryEquiv.pointReflection_apply]
  change c i - p i + c i = 2 * c i - p i
  ring

theorem map_pointReflection (e : Plane ≃ᵃⁱ[ℝ] Plane) (c p : Plane) :
    e (AffineIsometryEquiv.pointReflection ℝ c p) =
      AffineIsometryEquiv.pointReflection ℝ (e c) (e p) := by
  simp only [AffineIsometryEquiv.pointReflection_apply]
  change e.toAffineIsometry ((c -ᵥ p) +ᵥ c) =
    (e.toAffineIsometry c -ᵥ e.toAffineIsometry p) +ᵥ e.toAffineIsometry c
  rw [AffineIsometry.map_vadd, AffineIsometry.map_vsub]

/-- Compactness and nonemptiness make a central-symmetry center unique.
No convexity, Jordan property, or interior hypothesis is required. -/
theorem eq_of_pointReflection_maps {K : Set Plane} {c d : Plane}
    (hK : IsCompact K) (hne : K.Nonempty)
    (hc : MapsTo (AffineIsometryEquiv.pointReflection ℝ c) K K)
    (hd : MapsTo (AffineIsometryEquiv.pointReflection ℝ d) K K) : c = d := by
  ext i
  obtain ⟨p, hp, hmax⟩ := hK.exists_isMaxOn hne
    ((EuclideanSpace.proj i).continuous.continuousOn)
  have hcd := isMaxOn_iff.mp hmax _ (hc (hd hp))
  have hdc := isMaxOn_iff.mp hmax _ (hd (hc hp))
  change AffineIsometryEquiv.pointReflection ℝ c
    (AffineIsometryEquiv.pointReflection ℝ d p) i ≤ p i at hcd
  change AffineIsometryEquiv.pointReflection ℝ d
    (AffineIsometryEquiv.pointReflection ℝ c p) i ≤ p i at hdc
  simp only [pointReflection_coord] at hcd hdc
  linarith

/-- Every affine symmetry of a compact centrally symmetric set fixes its
center. This is a statement about the actual set, not its individual pieces. -/
theorem center_fixed_of_invariant_central_set {K : Set Plane} {c : Plane}
    (hK : IsCompact K) (hne : K.Nonempty)
    (hc : AffineIsometryEquiv.pointReflection ℝ c '' K = K)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' K = K) : e c = c := by
  have hcmap : MapsTo (AffineIsometryEquiv.pointReflection ℝ c) K K :=
    fun p hp => hc ▸ mem_image_of_mem _ hp
  have hemap : MapsTo e K K := fun p hp => he ▸ mem_image_of_mem _ hp
  have hnew : MapsTo (AffineIsometryEquiv.pointReflection ℝ (e c)) K K := by
    intro p hp
    have hpin : p ∈ e '' K := he.symm ▸ hp
    obtain ⟨q, hq, rfl⟩ := hpin
    rw [← map_pointReflection]
    exact hemap (hcmap hq)
  exact eq_of_pointReflection_maps hK hne hnew hcmap

theorem image_back_of_involution {P Q : Set Plane} (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hinv : Function.Involutive e) (he : e '' P = Q) : e '' Q = P := by
  rw [← he, image_image]
  change ((e : Plane → Plane) ∘ e) '' P = P
  rw [hinv.comp_self, image_id]

theorem image_union_of_involution {P Q : Set Plane} (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hinv : Function.Involutive e) (he : e '' P = Q) : e '' (P ∪ Q) = P ∪ Q := by
  rw [image_union, he, image_back_of_involution e hinv he, union_comm]

theorem middleUnion_image_of_involution {d : SquareDissection}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hinv : Function.Involutive e)
    (he : e '' d.piece 2 = d.piece 3) : e '' middleUnion d = middleUnion d :=
  image_union_of_involution e hinv he

theorem middleUnion_central_of_outer_halfTurn {d : SquareDissection}
    (houter : AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece 0 = d.piece 1) :
    AffineIsometryEquiv.pointReflection ℝ squareCenter '' middleUnion d = middleUnion d := by
  let e := (AffineIsometryEquiv.pointReflection ℝ squareCenter).toHomeomorph
  have hout : e '' (d.piece 0 ∪ d.piece 1) = d.piece 0 ∪ d.piece 1 :=
    image_union_of_involution (AffineIsometryEquiv.pointReflection ℝ squareCenter)
      (AffineIsometryEquiv.pointReflection_involutive (𝕜 := ℝ) squareCenter) houter
  change e '' (d.piece 2 ∪ d.piece 3) = d.piece 2 ∪ d.piece 3
  rw [N4OuterPair.middle_union_eq_closure d, e.image_closure,
    image_sdiff e.injective,
    show e '' unitSquare = unitSquare from HalfTurnRemainder.pointReflection_image_unitSquare,
    hout]

/-- Any congruence between the two middle pieces must move the square
center in a protected-center configuration. -/
theorem center_not_fixed_of_middle_pair {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 2 = d.piece 3) :
    e squareCenter ≠ squareCenter := by
  intro hfix
  have hnot := d.center_not_mem_fixed_pair (by decide : (2 : Fin 4) ≠ 3) e he hfix
  exact (h.center_in_middle hc).elim hnot.1 hnot.2

/-- The exceptional outer half-turn case is already impossible for any
involutive congruence between the middle pieces. -/
theorem false_of_outer_halfTurn_and_middle_involution {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter)
    (houter : AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece 0 = d.piece 1)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hinv : Function.Involutive e)
    (he : e '' d.piece 2 = d.piece 3) : False := by
  apply center_not_fixed_of_middle_pair h hc e he
  exact center_fixed_of_invariant_central_set (middleUnion_isCompact d)
    (middleUnion_nonempty d) (middleUnion_central_of_outer_halfTurn houter) e
    (middleUnion_image_of_involution e hinv he)

end Puzzling139335.N4MiddleInvolutions
