/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.DyadicBadRoots

/-!
# Incidence bound for a block of bad roots

This is the final purely finite double count in the few-bad-moduli argument.
If every selected root has many endpoint-bad auxiliary partners, then the
number of selected roots is controlled by the bad auxiliary conductors and
the bad product conductors.
-/

namespace Erdos48

noncomputable section

/-- A fixed reciprocal-mass gap gives a natural-number lower bound for the
number of endpoint-bad partners.  The division by `D` deliberately rounds
down, which is the form needed by the incidence count. -/
theorem div_le_card_endpointBadAuxiliaryPartners
    {x q R0 D : ℕ} {R : Finset ℕ} {S G : ℝ}
    (hR0 : 0 < R0) (hD : 0 < D)
    (hlower : ∀ r ∈ R, R0 ≤ r)
    (htotal : S ≤ ∑ r ∈ R, (r : ℝ)⁻¹)
    (hgood : (∑ r ∈ endpointGoodAuxiliaryPartners x q R,
      (r : ℝ)⁻¹) < G)
    (hgap : ((D : ℝ)⁻¹) ≤ S - G) :
    R0 / D ≤ (endpointBadAuxiliaryPartners x q R).card := by
  have hbad := mul_sub_lt_card_endpointBadAuxiliaryPartners
    hR0 hlower htotal hgood
  have hcastDiv : ((R0 / D : ℕ) : ℝ) ≤ (R0 : ℝ) / (D : ℝ) :=
    Nat.cast_div_le
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  have hmiddle : (R0 : ℝ) / (D : ℝ) ≤
      (R0 : ℝ) * (S - G) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hgap (by positivity)
  have hstrict : ((R0 / D : ℕ) : ℝ) <
      ((endpointBadAuxiliaryPartners x q R).card : ℝ) :=
    (hcastDiv.trans hmiddle).trans_lt hbad
  exact_mod_cast hstrict.le

/-- Root--auxiliary incidence double count, already separated into the two
endpoint-mass errors that are estimated by Vaughan's mean theorem. -/
theorem badRoots_card_mul_le_auxiliary_add_product
    {x A : ℕ} {E Q R : Finset ℕ}
    (hE : E ⊆ Q)
    (hlower : ∀ q ∈ E,
      A ≤ (endpointBadAuxiliaryPartners x q R).card) :
    E.card * A ≤
      Q.card * (R.filter fun r ↦
        (x : ℝ) / 10 < primitiveEndpointMass x r).card +
      ((Q.product R).filter fun qr ↦
        (x : ℝ) / 10 <
          primitiveEndpointMass x (qr.1 * qr.2)).card := by
  let P : ℕ → ℕ → Prop := fun q r ↦
    (x : ℝ) / 10 < primitiveEndpointMass x r ∨
      (x : ℝ) / 10 < primitiveEndpointMass x (q * r)
  have hpartners : ∀ q ∈ E, A ≤ (R.filter fun r ↦ P q r).card := by
    intro q hq
    simpa only [P, endpointBadAuxiliaryPartners] using hlower q hq
  have hincidence := card_mul_le_card_badPairs_of_partner_lower
    (P := P) hE hpartners
  exact hincidence.trans (card_endpointBadPairs_le x Q R)

end

end Erdos48
