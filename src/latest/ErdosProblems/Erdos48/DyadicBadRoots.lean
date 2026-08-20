/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.AuxiliaryCounting
import ErdosProblems.Erdos48.ProductPairEndpointMass

/-!
# The finite dyadic bad-root reduction

This file contains the combinatorial heart of FLP Lemma 2.6.  For a fixed
root prime `q`, retain the auxiliary primes whose own endpoint mass and whose
product-conductor endpoint mass are both small.  The auxiliary-prime
incidence theorem bounds the reciprocal mass of that retained set whenever
the shifted-smooth `q`-fiber is too small.  Consequently a bad root must
either have large endpoint mass itself or have many bad auxiliary partners.
-/

namespace Erdos48

open scoped BigOperators

noncomputable section

/-- Auxiliary primes for which both endpoint masses used by the progression
argument are small. -/
def endpointGoodAuxiliaryPartners
    (x q : ℕ) (R : Finset ℕ) : Finset ℕ :=
  R.filter fun r ↦
    primitiveEndpointMass x r ≤ (x : ℝ) / 10 ∧
      primitiveEndpointMass x (q * r) ≤ (x : ℝ) / 10

@[simp] theorem mem_endpointGoodAuxiliaryPartners
    {x q r : ℕ} {R : Finset ℕ} :
    r ∈ endpointGoodAuxiliaryPartners x q R ↔
      r ∈ R ∧ primitiveEndpointMass x r ≤ (x : ℝ) / 10 ∧
        primitiveEndpointMass x (q * r) ≤ (x : ℝ) / 10 := by
  simp [endpointGoodAuxiliaryPartners]

/-- If the shifted-smooth fiber at `q` is smaller than `L`, the reciprocal
mass of the endpoint-good auxiliary partners is correspondingly small. -/
theorem mul_sum_inv_endpointGoodAuxiliaryPartners_lt
    {x u q B D R0 : ℕ} {R : Finset ℕ} {W L : ℝ}
    (hx : 2 ≤ x) (hW : 0 < W) (hD : 0 < D)
    (hq : q.Prime)
    (hprime : ∀ r ∈ R, r.Prime)
    (hqu : q ≤ u)
    (hqUpper : q ≤ R0)
    (hru : ∀ r ∈ R, r ≤ u)
    (hlower : ∀ r ∈ R, R0 < r)
    (hpow : x + 1 < (R0 + 1) ^ (D + 1))
    (hqGood : primitiveEndpointMass x q ≤ (x : ℝ) / 10)
    (hcofactor : ∀ r ∈ R,
      ∀ p ∈ primesInProgression x (q * r) (q * r - 1),
        ∀ s : ℕ, s.Prime → u < s → s ∣ p + 1 →
          (p + 1) / (q * r * s) ≤ B)
    (hnumeric : ∀ r ∈ R,
      ((representedLargeFactorPrimes x u q r B).card : ℝ) +
          W * (r : ℝ)⁻¹ ≤
        (Chebyshev.theta (x : ℝ) / ((q * r).totient : ℝ) -
          (Real.log (((q * r) * x : ℕ) : ℝ) ^ 2 +
            ((q * r).totient : ℝ)⁻¹ * (4 * ((x : ℝ) / 10)) +
              (Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ)))) /
            Real.log (x : ℝ))
    (hbad : ((((smoothShiftedPrimes x u).filter
      fun p ↦ q ∣ p + 1).card : ℕ) : ℝ) < L) :
    W * ∑ r ∈ endpointGoodAuxiliaryPartners x q R, (r : ℝ)⁻¹ <
      (D : ℝ) * L := by
  let G := endpointGoodAuxiliaryPartners x q R
  have hGsub : G ⊆ R := Finset.filter_subset _ _
  have hbound :=
    mul_sum_inv_le_mul_card_smoothShiftedFiber_of_endpoint_good
      (R := G) hx hW.le hq
      (fun r hr ↦ hprime r (hGsub hr)) hqu hqUpper
      (fun r hr ↦ hru r (hGsub hr))
      (fun r hr ↦ hlower r (hGsub hr)) hpow hqGood
      (fun r hr ↦
        (mem_endpointGoodAuxiliaryPartners.mp hr).2.1)
      (fun r hr ↦
        (mem_endpointGoodAuxiliaryPartners.mp hr).2.2)
      (fun r hr ↦ hcofactor r (hGsub hr))
      (fun r hr ↦ hnumeric r (hGsub hr))
  exact hbound.trans_lt (mul_lt_mul_of_pos_left hbad (by exact_mod_cast hD))

/-- Complementary endpoint-bad partners. -/
def endpointBadAuxiliaryPartners
    (x q : ℕ) (R : Finset ℕ) : Finset ℕ :=
  R.filter fun r ↦
    (x : ℝ) / 10 < primitiveEndpointMass x r ∨
      (x : ℝ) / 10 < primitiveEndpointMass x (q * r)

@[simp] theorem mem_endpointBadAuxiliaryPartners
    {x q r : ℕ} {R : Finset ℕ} :
    r ∈ endpointBadAuxiliaryPartners x q R ↔
      r ∈ R ∧ ((x : ℝ) / 10 < primitiveEndpointMass x r ∨
        (x : ℝ) / 10 < primitiveEndpointMass x (q * r)) := by
  simp [endpointBadAuxiliaryPartners]

theorem endpointGoodAuxiliaryPartners_union_bad
    (x q : ℕ) (R : Finset ℕ) :
    endpointGoodAuxiliaryPartners x q R ∪
      endpointBadAuxiliaryPartners x q R = R := by
  classical
  ext r
  constructor
  · intro hr
    rw [Finset.mem_union] at hr
    rcases hr with hr | hr
    · exact (mem_endpointGoodAuxiliaryPartners.mp hr).1
    · exact (mem_endpointBadAuxiliaryPartners.mp hr).1
  · intro hr
    by_cases hfirst :
        primitiveEndpointMass x r ≤ (x : ℝ) / 10
    · by_cases hsecond :
          primitiveEndpointMass x (q * r) ≤ (x : ℝ) / 10
      · exact Finset.mem_union_left _
          (mem_endpointGoodAuxiliaryPartners.mpr
            ⟨hr, hfirst, hsecond⟩)
      · exact Finset.mem_union_right _
          (mem_endpointBadAuxiliaryPartners.mpr
            ⟨hr, Or.inr (lt_of_not_ge hsecond)⟩)
    · exact Finset.mem_union_right _
        (mem_endpointBadAuxiliaryPartners.mpr
          ⟨hr, Or.inl (lt_of_not_ge hfirst)⟩)

theorem disjoint_endpointGoodAuxiliaryPartners_bad
    (x q : ℕ) (R : Finset ℕ) :
    Disjoint (endpointGoodAuxiliaryPartners x q R)
      (endpointBadAuxiliaryPartners x q R) := by
  classical
  rw [Finset.disjoint_left]
  intro r hrGood hrBad
  have hg := mem_endpointGoodAuxiliaryPartners.mp hrGood
  have hb := mem_endpointBadAuxiliaryPartners.mp hrBad
  rcases hb.2 with hb | hb <;> linarith

/-- Reciprocal mass splits exactly between good and bad partners. -/
theorem sum_inv_endpointGood_add_bad
    (x q : ℕ) (R : Finset ℕ) :
    (∑ r ∈ endpointGoodAuxiliaryPartners x q R, (r : ℝ)⁻¹) +
        (∑ r ∈ endpointBadAuxiliaryPartners x q R, (r : ℝ)⁻¹) =
      ∑ r ∈ R, (r : ℝ)⁻¹ := by
  rw [← Finset.sum_union
    (disjoint_endpointGoodAuxiliaryPartners_bad x q R),
    endpointGoodAuxiliaryPartners_union_bad]

/-- A lower endpoint for the auxiliary interval converts reciprocal mass
loss into a cardinality lower bound. -/
theorem mul_sub_lt_card_endpointBadAuxiliaryPartners
    {x q R0 : ℕ} {R : Finset ℕ} {S G : ℝ}
    (hR0 : 0 < R0)
    (hlower : ∀ r ∈ R, R0 ≤ r)
    (htotal : S ≤ ∑ r ∈ R, (r : ℝ)⁻¹)
    (hgood : (∑ r ∈ endpointGoodAuxiliaryPartners x q R,
      (r : ℝ)⁻¹) < G) :
    (R0 : ℝ) * (S - G) <
      ((endpointBadAuxiliaryPartners x q R).card : ℝ) := by
  have hinv : (∑ r ∈ endpointBadAuxiliaryPartners x q R,
      (r : ℝ)⁻¹) ≤
      ((endpointBadAuxiliaryPartners x q R).card : ℝ) /
        (R0 : ℝ) := by
    calc
      (∑ r ∈ endpointBadAuxiliaryPartners x q R, (r : ℝ)⁻¹) ≤
          ∑ _r ∈ endpointBadAuxiliaryPartners x q R,
            ((R0 : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro r hr
        apply inv_anti₀
        · exact_mod_cast hR0
        · exact_mod_cast hlower r
            (mem_endpointBadAuxiliaryPartners.mp hr).1
      _ = ((endpointBadAuxiliaryPartners x q R).card : ℝ) /
          (R0 : ℝ) := by
        simp [div_eq_mul_inv]
  have hsplit := sum_inv_endpointGood_add_bad x q R
  have hmass : S - G <
      ∑ r ∈ endpointBadAuxiliaryPartners x q R, (r : ℝ)⁻¹ := by
    linarith
  have hdiv : S - G <
      ((endpointBadAuxiliaryPartners x q R).card : ℝ) /
        (R0 : ℝ) := hmass.trans_le hinv
  have hmul := (lt_div_iff₀ (by exact_mod_cast hR0 : (0 : ℝ) < R0)).mp hdiv
  simpa only [mul_comm] using hmul

/-- Pure finite incidence double count: if every selected root has at least
`A` bad auxiliary partners, their number times `A` is bounded by the total
number of bad ordered pairs. -/
theorem card_mul_le_card_badPairs_of_partner_lower
    {Q R E : Finset ℕ} {A : ℕ} {P : ℕ → ℕ → Prop}
    [DecidableRel P]
    (hE : E ⊆ Q)
    (hlower : ∀ q ∈ E, A ≤ (R.filter fun r ↦ P q r).card) :
    E.card * A ≤
      ((Q.product R).filter fun qr ↦ P qr.1 qr.2).card := by
  calc
    E.card * A = ∑ _q ∈ E, A := by simp
    _ ≤ ∑ q ∈ E, (R.filter fun r ↦ P q r).card := by
      exact Finset.sum_le_sum hlower
    _ ≤ ∑ q ∈ Q, (R.filter fun r ↦ P q r).card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hE
      intro q hqQ hqE
      omega
    _ = ((Q.product R).filter fun qr ↦ P qr.1 qr.2).card := by
      classical
      calc
        (∑ q ∈ Q, (R.filter fun r ↦ P q r).card) =
            ∑ q ∈ Q, ∑ r ∈ R, if P q r then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        _ = ∑ qr ∈ Q.product R,
            if P qr.1 qr.2 then 1 else 0 := by
          exact (Finset.sum_product' Q R
            (fun q r ↦ if P q r then 1 else 0)).symm
        _ = ((Q.product R).filter fun qr ↦ P qr.1 qr.2).card := by
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Every bad-partner pair is caused either by a bad auxiliary conductor or
by a bad product conductor.  This separates the two Vaughan estimates. -/
theorem card_endpointBadPairs_le
    (x : ℕ) (Q R : Finset ℕ) :
    ((Q.product R).filter fun qr ↦
      (x : ℝ) / 10 < primitiveEndpointMass x qr.2 ∨
        (x : ℝ) / 10 <
          primitiveEndpointMass x (qr.1 * qr.2)).card ≤
      Q.card * (R.filter fun r ↦
        (x : ℝ) / 10 < primitiveEndpointMass x r).card +
      ((Q.product R).filter fun qr ↦
        (x : ℝ) / 10 <
          primitiveEndpointMass x (qr.1 * qr.2)).card := by
  classical
  let A := (Q.product R).filter fun qr ↦
    (x : ℝ) / 10 < primitiveEndpointMass x qr.2
  let B := (Q.product R).filter fun qr ↦
    (x : ℝ) / 10 < primitiveEndpointMass x (qr.1 * qr.2)
  have hsub : ((Q.product R).filter fun qr ↦
      (x : ℝ) / 10 < primitiveEndpointMass x qr.2 ∨
        (x : ℝ) / 10 < primitiveEndpointMass x (qr.1 * qr.2)) ⊆
      A ∪ B := by
    intro qr hqr
    have hd := Finset.mem_filter.mp hqr
    rcases hd.2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd.1, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hd.1, h⟩)
  calc
    ((Q.product R).filter fun qr ↦
        (x : ℝ) / 10 < primitiveEndpointMass x qr.2 ∨
          (x : ℝ) / 10 <
            primitiveEndpointMass x (qr.1 * qr.2)).card ≤
        (A ∪ B).card := Finset.card_le_card hsub
    _ ≤ A.card + B.card := Finset.card_union_le A B
    _ = Q.card * (R.filter fun r ↦
          (x : ℝ) / 10 < primitiveEndpointMass x r).card +
        ((Q.product R).filter fun qr ↦
          (x : ℝ) / 10 <
            primitiveEndpointMass x (qr.1 * qr.2)).card := by
      dsimp [A, B]
      have hfilter := Finset.filter_product_right
        (s := Q) (t := R)
        (fun r ↦ (x : ℝ) / 10 < primitiveEndpointMass x r)
      rw [hfilter, Finset.card_product]

end

end Erdos48
