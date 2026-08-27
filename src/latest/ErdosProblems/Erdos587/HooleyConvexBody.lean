import ErdosProblems.Erdos587.HooleyLatticeRounding

/-! # A full-dimensional body with a small rounding cell has full lattice span -/

namespace Erdos587.GeneralizedAP

theorem delta_span_integerPointCasts_eq_top {d : ℕ} {B : Set (Fin d → ℝ)}
    (hcompact : IsCompact B) (hzero : (0 : Fin d → ℝ) ∈ B) (hconv : Convex ℝ B)
    (hneg : ∀ x ∈ B, -x ∈ B) (hfull : ∀ x, ∃ c : ℝ, 0 < c ∧ c • x ∈ B)
    (hround : ∀ x : Fin d → ℝ, ∃ v : Fin d → ℤ,
      x - intCastVec v ∈ bodyDilate (1 / 4 : ℝ) B) :
    Submodule.span ℝ (integerPointCasts B) = ⊤ := by
  by_contra hspan
  obtain ⟨ℓ, hℓ, hker⟩ := (Submodule.span ℝ (integerPointCasts B)).exists_le_ker_of_lt_top
    (lt_top_iff_ne_top.mpr hspan)
  have hbound (v : Fin d → ℤ) (hv : intCastVec v ∈ B) : |ℓ (intCastVec v)| ≤ 0 := by
    have hz : ℓ (intCastVec v) = 0 := hker (Submodule.subset_span ⟨v, hv, rfl⟩)
    simp only [hz, abs_zero, le_refl]
  have hreal := delta_real_width_le_twice_lattice_width hcompact hzero hconv hneg hround ℓ 0 hbound
  apply hℓ
  apply LinearMap.ext
  intro x
  change ℓ x = 0
  obtain ⟨c, hc, hcx⟩ := hfull x
  have habs : |ℓ (c • x)| ≤ 0 := by simpa only [mul_zero] using hreal _ hcx
  have hz : ℓ (c • x) = 0 := abs_eq_zero.mp (le_antisymm habs (abs_nonneg _))
  rw [map_smul, smul_eq_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left hc.ne'

def deltaConvexProgression {d : ℕ} (base : ℤ) (eval : (Fin d → ℤ) →+ ℤ)
    (B : Set (Fin d → ℝ)) (hcompact : IsCompact B) (hzero : (0 : Fin d → ℝ) ∈ B)
    (hconv : Convex ℝ B) (hneg : ∀ x ∈ B, -x ∈ B)
    (hfull : ∀ x, ∃ c : ℝ, 0 < c ∧ c • x ∈ B)
    (hround : ∀ x : Fin d → ℝ, ∃ v : Fin d → ℤ,
      x - intCastVec v ∈ bodyDilate (1 / 4 : ℝ) B) : ConvexProgression where
  rank := d
  base := base
  body := B
  body_zero := hzero
  body_convex := hconv
  body_neg := hneg
  body_closed := hcompact.isClosed
  body_bounded := hcompact.isBounded
  body_full := hfull
  body_lattice_full := delta_span_integerPointCasts_eq_top hcompact hzero hconv hneg hfull hround
  eval := eval

theorem delta_rounding_of_projected_cube {d n : ℕ}
    (q : (Fin d → ℤ) →ₗ[ℤ] (Fin n → ℤ)) (hq : Function.Surjective q)
    {B : Set (Fin n → ℝ)}
    (hcube : ∀ e : Fin d → ℝ, (∀ i, |e i| ≤ (1 / 2 : ℝ)) →
      intLinearMapRealExtension q e ∈ bodyDilate (1 / 4 : ℝ) B) :
    ∀ x : Fin n → ℝ, ∃ v : Fin n → ℤ,
      x - intCastVec v ∈ bodyDilate (1 / 4 : ℝ) B := by
  intro x
  obtain ⟨v, e, he, heq⟩ := delta_projected_cube_rounding q hq x
  refine ⟨v, ?_⟩
  rw [heq]
  exact hcube e he

end Erdos587.GeneralizedAP
