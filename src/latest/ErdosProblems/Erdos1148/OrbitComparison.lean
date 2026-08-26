import ErdosProblems.Erdos1148.IntegralProjectiveAction
import ErdosProblems.Erdos1148.LocalProduct
import ErdosProblems.Erdos1148.FormActionBaseChange

/-!
# Comparing integral special-linear and special-orthogonal orbits

An integral special isometry is a binary change of variables, possibly
followed by one fixed involution. Consequently each special-orthogonal orbit
contains at most two special-linear orbits.
-/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def signFlip {R : Type*} [CommRing R] (t : R × R × R) : R × R × R :=
  (-t.1, t.2.1, -t.2.2)

lemma discr_signFlip {R : Type*} [CommRing R] (t : R × R × R) :
    discr (signFlip t) = discr t := by
  simp [signFlip, discr]

lemma pairing_signFlip {R : Type*} [CommRing R] (t u : R × R × R) :
    pairing (signFlip t) (signFlip u) = pairing t u := by
  simp [signFlip, pairing]

def reflectionMatrix {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![-1, 0; 0, 1]

lemma det_reflectionMatrix {R : Type*} [CommRing R] :
    (reflectionMatrix (R := R)).det = -1 := by
  simp [reflectionMatrix, Matrix.det_fin_two]

lemma transform_reflection_signFlip {R : Type*} [CommRing R] (t : R × R × R) :
    transform reflectionMatrix (signFlip t) = -t := by
  ext <;> simp [transform, reflectionMatrix, signFlip]

lemma transform_neg {R : Type*} [CommRing R]
    (A : Matrix (Fin 2) (Fin 2) R) (t : R × R × R) :
    transform A (-t) = -transform A t := (transformLinear A).map_neg t

theorem exists_signed_integral_transform (g : specialDiscrGroup ℤ) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℤ,
      (A.det = 1 ∧ ∀ t, g.1 t = transform A t) ∨
      (A.det = -1 ∧ ∀ t, g.1 t = -transform A t) := by
  obtain ⟨A, hA, hg⟩ := exists_integral_normalizedTransformIsometry g
  have hact (t : ℤ × ℤ × ℤ) := congrArg (fun k : specialDiscrGroup ℚ =>
    k.1 (mapCoeffs (Int.castRingHom ℚ) t)) hg
  simp only [normalizedTransformIsometry_apply, specialDiscrBaseChange_apply,
    ← mapCoeffs_transform] at hact
  have hdet : (A.map (Int.castRingHom ℚ)).det = (A.det : ℚ) := by
    exact ((Int.castRingHom ℚ).map_det A).symm
  refine ⟨A, ?_⟩
  rcases Int.isUnit_eq_one_or hA with hpos | hneg
  · left
    refine ⟨hpos, fun t => ?_⟩
    apply mapCoeffs_injective (Int.castRingHom ℚ) Int.cast_injective
    have h := hact t
    simpa only [hdet, hpos, Int.cast_one, inv_one, one_smul] using h.symm
  · right
    refine ⟨hneg, fun t => ?_⟩
    apply mapCoeffs_injective (Int.castRingHom ℚ) Int.cast_injective
    have h := hact t
    rw [hdet, hneg] at h
    simpa [mapCoeffs] using h.symm

/-- The sole extra coset is represented by `(a,b,c) ↦ (-a,b,-c)`. -/
theorem specialDiscrGroup_two_actions (g : specialDiscrGroup ℤ) :
    ∃ h : SL(2, ℤ),
      (∀ t, g.1 t = formAction h t) ∨ (∀ t, g.1 t = formAction h (signFlip t)) := by
  obtain ⟨A, ⟨hdet, hact⟩ | ⟨hdet, hact⟩⟩ := exists_signed_integral_transform g
  · let h : SL(2, ℤ) := ⟨A, hdet⟩
    refine ⟨h⁻¹, Or.inl ?_⟩
    intro t
    simpa only [formAction, inv_inv] using hact t
  · have hdet' : (reflectionMatrix * A).det = 1 := by
      rw [Matrix.det_mul, det_reflectionMatrix, hdet]
      norm_num
    let h : SL(2, ℤ) := ⟨reflectionMatrix * A, hdet'⟩
    refine ⟨h⁻¹, Or.inr ?_⟩
    intro t
    simp only [formAction, inv_inv]
    change g.1 t = transform (reflectionMatrix * A) (signFlip t)
    rw [transform_mul, transform_reflection_signFlip, transform_neg, hact]

def signFlipPair {R : Type*} [CommRing R] {d ℓ : R} (p : FormPair R d ℓ) : FormPair R d ℓ :=
  ⟨(signFlip p.1.1, signFlip p.1.2), by
    simpa only [discr_signFlip, pairing_signFlip] using p.2⟩

lemma specialPairAction_two_actions {d ℓ : ℤ}
    (g : specialDiscrGroup ℤ) (p : FormPair ℤ d ℓ) :
    ∃ h : SL(2, ℤ), g • p = h • p ∨ g • p = h • signFlipPair p := by
  obtain ⟨h, hact | hact⟩ := specialDiscrGroup_two_actions g
  · refine ⟨h, Or.inl ?_⟩
    apply Subtype.ext
    exact Prod.ext (hact p.1.1) (hact p.1.2)
  · refine ⟨h, Or.inr ?_⟩
    apply Subtype.ext
    exact Prod.ext (hact p.1.1) (hact p.1.2)

noncomputable def twoOrbitRepresentatives {d ℓ : ℤ}
    (x : SpecialPairOrbits ℤ d ℓ × Bool) : IntegralPairOrbits d ℓ :=
  Quotient.mk _ (if x.2 then signFlipPair x.1.out else x.1.out)

lemma twoOrbitRepresentatives_surjective {d ℓ : ℤ} :
    Function.Surjective (twoOrbitRepresentatives (d := d) (ℓ := ℓ)) := by
  intro y
  induction y using Quotient.inductionOn with | h p =>
    let x : SpecialPairOrbits ℤ d ℓ := Quotient.mk _ p
    have hrel : MulAction.orbitRel (specialDiscrGroup ℤ) (FormPair ℤ d ℓ) p x.out :=
      Quotient.exact (Quotient.out_eq x).symm
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
    obtain ⟨h, hact | hact⟩ := specialPairAction_two_actions g x.out
    · refine ⟨(x, false), ?_⟩
      change Quotient.mk _ x.out = Quotient.mk _ p
      apply Eq.symm
      apply Quotient.sound
      apply MulAction.orbitRel_apply.mpr
      exact MulAction.mem_orbit_iff.mpr ⟨h, hact.symm.trans hg⟩
    · refine ⟨(x, true), ?_⟩
      change Quotient.mk _ (signFlipPair x.out) = Quotient.mk _ p
      apply Eq.symm
      apply Quotient.sound
      apply MulAction.orbitRel_apply.mpr
      exact MulAction.mem_orbit_iff.mpr ⟨h, hact.symm.trans hg⟩

theorem card_integralPairOrbits_le_twice {d ℓ : ℤ} [Finite (SpecialPairOrbits ℤ d ℓ)] :
    Nat.card (IntegralPairOrbits d ℓ) ≤ 2 * Nat.card (SpecialPairOrbits ℤ d ℓ) := by
  have h := Nat.card_le_card_of_surjective _
    (twoOrbitRepresentatives_surjective (d := d) (ℓ := ℓ))
  simpa only [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
    mul_comm] using h

theorem finite_integralPairOrbits {d ℓ : ℤ} (base : FormPair ℤ d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) : Finite (IntegralPairOrbits d ℓ) := by
  let := finite_integer_specialPairOrbits base hnd
  exact Finite.of_surjective _ (twoOrbitRepresentatives_surjective (d := d) (ℓ := ℓ))

/-- The source's local-product bound, now for the original special-linear pair action. -/
theorem card_integralPairOrbits_le_local_product {d ℓ : ℤ} (base : FormPair ℤ d ℓ)
    (hnd : ℓ ^ 2 ≠ 4 * d ^ 2) :
    Nat.card (IntegralPairOrbits d ℓ) ≤
      2 * ∏ r : BadPairPrime d ℓ, Nat.card (BadLocalPairOrbit d ℓ r) := by
  let := finite_integer_specialPairOrbits base hnd
  exact card_integralPairOrbits_le_twice.trans
    (Nat.mul_le_mul_left 2 (card_integer_specialPairOrbits_le_local_product base hnd))

end Erdos1148.DukeArithmetic
