import StackExchange.Puzzling139335.CentralNonRotation.SquareTranslationAxis.BoundedTranslation
import StackExchange.Puzzling139335.CentralNonRotation.SquareTranslationAxis.Displacement

/-!
# Central symmetry of a two-piece union determines the translation axis

For an affine isometry `g` whose square is translation by `v`, the displacement
image of `P ∪ g '' P` is invariant under reflection in `v / 2`. If that union is
centrally symmetric about `c`, its displacement image is also invariant under
reflection in `g c - c`. Compactness and nonemptiness force those centers to agree.
No disjointness, Jordan boundary, or nonzero-translation assumption is needed.
-/

namespace Puzzling139335.CentralNonRotation

open Set

/-- Central symmetry of a compact two-piece union determines the translation
vector of the square of its congruence. -/
theorem square_translation_eq_twice_displacement
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (c v : Plane)
    (hg2 : ∀ x, g (g x) = x + v)
    {P : Set Plane} (hP : IsCompact P) (hPne : P.Nonempty)
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' (P ∪ g '' P) = P ∪ g '' P) :
    v = (g c - c) + (g c - c) := by
  let K : Set Plane := affineDisplacement g '' (P ∪ g '' P)
  have hK : IsCompact K :=
    (hP.union (hP.image g.continuous)).image (continuous_affineDisplacement g)
  have hKne : K.Nonempty := by
    obtain ⟨p, hp⟩ := hPne
    exact ⟨affineDisplacement g p, p, Or.inl hp, rfl⟩
  have hgK : ∀ z ∈ K, v - z ∈ K := by
    rintro z ⟨x, hx, rfl⟩
    rcases hx with hx | ⟨y, hy, rfl⟩
    · exact ⟨g x, Or.inr ⟨x, hx, rfl⟩,
        affineDisplacement_apply_of_square_translation g v hg2 x⟩
    · refine ⟨y, Or.inl hy, ?_⟩
      rw [affineDisplacement_apply_of_square_translation g v hg2 y]
      abel
  have hcK : ∀ z ∈ K,
      (affineDisplacement g c + affineDisplacement g c) - z ∈ K := by
    rintro z ⟨x, hx, rfl⟩
    refine ⟨AffineIsometryEquiv.pointReflection ℝ c x, ?_,
      affineDisplacement_pointReflection g c x⟩
    exact hsym ▸
      (show AffineIsometryEquiv.pointReflection ℝ c x ∈
        AffineIsometryEquiv.pointReflection ℝ c '' (P ∪ g '' P) from ⟨x, hx, rfl⟩)
  have htranslation : ∀ z ∈ K,
      z + (v - (affineDisplacement g c + affineDisplacement g c)) ∈ K := by
    intro z hz
    convert hgK _ (hcK _ hz) using 1 <;> abel
  have hzero := translation_eq_zero_of_isCompact K hK hKne
    (v - (affineDisplacement g c + affineDisplacement g c)) htranslation
  exact sub_eq_zero.mp hzero

/-- Scalar-multiplication form of the displacement identity. -/
theorem square_translation_eq_two_smul_displacement
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (c v : Plane)
    (hg2 : ∀ x, g (g x) = x + v)
    {P : Set Plane} (hP : IsCompact P) (hPne : P.Nonempty)
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' (P ∪ g '' P) = P ∪ g '' P) :
    v = (2 : ℝ) • (g c - c) := by
  simpa only [two_smul] using
    square_translation_eq_twice_displacement g c v hg2 hP hPne hsym

/-- The half-turn about the union's center conjugates the congruence to its
inverse whenever the square of that congruence is a translation. -/
theorem pointReflection_conjugate_eq_symm_of_square_translation
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (c v : Plane)
    (hg2 : ∀ x, g (g x) = x + v)
    {P : Set Plane} (hP : IsCompact P) (hPne : P.Nonempty)
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' (P ∪ g '' P) = P ∪ g '' P)
    (x : Plane) :
    AffineIsometryEquiv.pointReflection ℝ c
      (g (AffineIsometryEquiv.pointReflection ℝ c x)) = g.symm x :=
  pointReflection_conjugate_eq_symm_of_twice_displacement g c v hg2
    (square_translation_eq_twice_displacement g c v hg2 hP hPne hsym) x

/-- In the involutive case, the union's central symmetry forces the congruence
to fix the center. -/
theorem fixed_center_of_involutive_of_centrally_symmetric_union
    (g : Plane ≃ᵃⁱ[ℝ] Plane) (c : Plane)
    (hg2 : ∀ x, g (g x) = x)
    {P : Set Plane} (hP : IsCompact P) (hPne : P.Nonempty)
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' (P ∪ g '' P) = P ∪ g '' P) :
    g c = c := by
  have hshift := square_translation_eq_two_smul_displacement g c 0
    (by simpa only [add_zero] using hg2) hP hPne hsym
  have hdisplacement : g c - c = 0 :=
    (smul_eq_zero.mp hshift.symm).resolve_left (by norm_num)
  exact sub_eq_zero.mp hdisplacement

end Puzzling139335.CentralNonRotation
