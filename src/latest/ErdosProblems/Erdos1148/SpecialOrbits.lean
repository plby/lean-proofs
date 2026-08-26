import ErdosProblems.Erdos1148.PairFrames

/-!
# Special-orthogonal orbits of pairs

The group used for the local embedding count is different from the integral
special-linear action on binary forms. This file keeps the two orbit types
distinct and proves transitivity in the unit-discriminant case.
-/

namespace Erdos1148.DukeArithmetic

def specialDiscrGroup (R : Type*) [CommRing R] : Subgroup ((R × R × R) ≃ₗ[R] (R × R × R)) where
  carrier := {g | (∀ t, discr (g t) = discr t) ∧ LinearMap.det g.toLinearMap = 1}
  one_mem' := ⟨fun _ => rfl, LinearMap.det_id⟩
  mul_mem' := by
    intro g h hg hh
    constructor
    · intro t
      exact (hg.1 (h t)).trans (hh.1 t)
    · change LinearMap.det (g.toLinearMap.comp h.toLinearMap) = 1
      rw [LinearMap.det_comp, hg.2, hh.2, one_mul]
  inv_mem' := by
    intro g hg
    constructor
    · intro t
      have h := hg.1 (g.symm t)
      rw [LinearEquiv.apply_symm_apply] at h
      exact h.symm
    · have h := LinearEquiv.det_mul_det_symm g
      rw [hg.2, one_mul] at h
      exact h

lemma pairing_linearEquiv {R : Type*} [CommRing R]
    (g : (R × R × R) ≃ₗ[R] (R × R × R)) (hg : ∀ t, discr (g t) = discr t)
    (t u : R × R × R) : pairing (g t) (g u) = pairing t u := by
  have h := hg (t - u)
  rw [map_sub, discr_sub, discr_sub, hg, hg] at h
  linear_combination -h

def specialPairAction {R : Type*} [CommRing R] {d ℓ : R}
    (g : specialDiscrGroup R) (p : FormPair R d ℓ) : FormPair R d ℓ :=
  ⟨(g.1 p.1.1, g.1 p.1.2), by
    simpa only [g.2.1, pairing_linearEquiv g.1 g.2.1] using p.2⟩

instance specialPairMulAction {R : Type*} [CommRing R] {d ℓ : R} :
    MulAction (specialDiscrGroup R) (FormPair R d ℓ) where
  smul := specialPairAction
  one_smul p := by apply Subtype.ext; rfl
  mul_smul g h p := by apply Subtype.ext; rfl

abbrev SpecialPairOrbits (R : Type*) [CommRing R] (d ℓ : R) :=
  Quotient (MulAction.orbitRel (specialDiscrGroup R) (FormPair R d ℓ))

/-- There is at most one local orbit when the binary discriminant is a unit. -/
theorem specialPairOrbits_subsingleton_of_unit {R : Type*} [CommRing R]
    [NoZeroDivisors R] [CharZero R] {d ℓ : R} (hunit : IsUnit (ℓ ^ 2 - 4 * d ^ 2)) :
    Subsingleton (SpecialPairOrbits R d ℓ) := by
  refine ⟨fun x y => ?_⟩
  induction x, y using Quotient.inductionOn₂ with | h p q =>
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    obtain ⟨g, hdet, hfirst, hsecond⟩ :=
      exists_specialIsometry_of_unit_pair_discriminant q p hunit
    refine ⟨⟨g.toLinearEquiv, ⟨fun t => g.map_app t, hdet⟩⟩, ?_⟩
    apply Subtype.ext
    exact Prod.ext hfirst hsecond

theorem card_specialPairOrbits_eq_one_of_unit {R : Type*} [CommRing R]
    [NoZeroDivisors R] [CharZero R] {d ℓ : R} [Nonempty (FormPair R d ℓ)]
    (hunit : IsUnit (ℓ ^ 2 - 4 * d ^ 2)) : Nat.card (SpecialPairOrbits R d ℓ) = 1 := by
  let := specialPairOrbits_subsingleton_of_unit hunit
  let : Nonempty (SpecialPairOrbits R d ℓ) :=
    ⟨Quotient.mk _ (Classical.choice (inferInstance : Nonempty (FormPair R d ℓ)))⟩
  exact Nat.card_unique

lemma padic_isUnit_pair_discriminant (p : ℕ) [Fact p.Prime] (d ℓ : ℤ)
    (hgood : ¬ (p : ℤ) ∣ ℓ ^ 2 - 4 * d ^ 2) :
    IsUnit ((ℓ : PadicInt p) ^ 2 - 4 * (d : PadicInt p) ^ 2) := by
  have hunitZ : IsUnit ((ℓ ^ 2 - 4 * d ^ 2 : ℤ) : PadicInt p) := by
    rw [PadicInt.isUnit_iff]
    apply le_antisymm (PadicInt.norm_le_one _)
    apply not_lt.mp
    rwa [PadicInt.norm_int_lt_one_iff_dvd]
  simpa only [Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using hunitZ

/-- At every prime not dividing the binary discriminant the local factor is exactly one. -/
theorem padic_card_specialPairOrbits_eq_one (p : ℕ) [Fact p.Prime] (d ℓ : ℤ)
    (hgood : ¬ (p : ℤ) ∣ ℓ ^ 2 - 4 * d ^ 2)
    (pair : FormPair (PadicInt p) d ℓ) :
    Nat.card (SpecialPairOrbits (PadicInt p) d ℓ) = 1 := by
  let : Nonempty (FormPair (PadicInt p) d ℓ) := ⟨pair⟩
  exact card_specialPairOrbits_eq_one_of_unit (padic_isUnit_pair_discriminant p d ℓ hgood)

end Erdos1148.DukeArithmetic
