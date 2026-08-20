import ErdosProblems.Erdos957.Scale
import ErdosProblems.Erdos957.TransferCert

/-!
# The certificate-to-product bridge for Erdős problem 957

This module packages the part of Dumitrescu's argument after the geometric
transfer certificate has been constructed.  It combines the exact certificate
edge bound, the `2520` exceptional-hull-vertex count, Hopf--Pannwitz, and the
final quadratic optimization.
-/

namespace Erdos957

noncomputable section

/-- A geometric transfer certificate, together with the two endpoint-cardinality
facts, implies the sharp product estimate with the explicit linear error
`1260 * |A|`. -/
theorem product_bound_of_transfer {A : Finset Point} {d₁ dₖ : ℝ}
    (H Q B D : Finset {x // x ∈ A})
    (C : TransferCert (distanceGraph A d₁) H Q B)
    (hDH : D.card ≤ H.card) (hDQ : D.card ≤ Q.card + 2520)
    (hmax : multiplicity A dₖ ≤ D.card) :
    (multiplicity A d₁ : ℝ) * multiplicity A dₖ ≤
      (9 / 8 : ℝ) * (A.card : ℝ) ^ 2 + 1260 * (A.card : ℝ) := by
  have hedge := C.edge_bound_of_transfer
  have hDH' : (D.card : ℤ) ≤ H.card := by
    exact_mod_cast hDH
  have hDQ' : (D.card : ℤ) ≤ (Q.card : ℤ) + 2520 := by
    exact_mod_cast hDQ
  have hcharge :
      (4 * multiplicity A d₁ : ℤ) ≤
        12 * (A.card : ℤ) - 8 * (D.card : ℤ) + 5040 := by
    change (4 * (distanceGraph A d₁).edgeFinset.card : ℤ) ≤ _
    have hcard : Fintype.card {x // x ∈ A} = A.card := Fintype.card_coe A
    rw [hcard] at hedge
    nlinarith
  have hDcard : D.card ≤ A.card := by
    calc
      D.card ≤ H.card := hDH
      _ ≤ Fintype.card {x // x ∈ A} := Finset.card_le_univ H
      _ = A.card := Fintype.card_coe A
  exact product_bound_real A.card D.card (multiplicity A d₁)
    (multiplicity A dₖ) hcharge hmax hDcard

/-- The form used by the geometric argument: normalize the least distance to
one, construct a certificate there, and transport the resulting product bound
back to the original configuration. -/
theorem product_bound_of_normalized_transfer {A : Finset Point} {d₁ dₖ : ℝ}
    (hmin : IsMinimumDistance A d₁)
    (H Q B D : Finset {x // x ∈ normalizedSet A d₁ hmin.pos})
    (C : TransferCert
      (distanceGraph (normalizedSet A d₁ hmin.pos) 1) H Q B)
    (hDH : D.card ≤ H.card) (hDQ : D.card ≤ Q.card + 2520)
    (hmax : multiplicity (normalizedSet A d₁ hmin.pos) (dₖ / d₁) ≤ D.card) :
    (multiplicity A d₁ : ℝ) * multiplicity A dₖ ≤
      (9 / 8 : ℝ) * (A.card : ℝ) ^ 2 + 1260 * (A.card : ℝ) := by
  have hprod := product_bound_of_transfer H Q B D C hDH hDQ hmax
  have hminMult :
      multiplicity (normalizedSet A d₁ hmin.pos) 1 = multiplicity A d₁ := by
    simpa [hmin.pos.ne'] using multiplicity_normalizedSet A d₁ hmin.pos d₁
  have hmaxMult :
      multiplicity (normalizedSet A d₁ hmin.pos) (dₖ / d₁) =
        multiplicity A dₖ :=
    multiplicity_normalizedSet A d₁ hmin.pos dₖ
  have hcard : (normalizedSet A d₁ hmin.pos).card = A.card :=
    normalizedSet_card A d₁ hmin.pos
  simpa [hminMult, hmaxMult, hcard] using hprod

end

end Erdos957
