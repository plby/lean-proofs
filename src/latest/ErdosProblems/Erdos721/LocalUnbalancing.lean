/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos721.PositiveDefiniteLifting
import APAP.Physics.Unbalancing

/-!
# Local unbalancing on a cyclic Bohr set

This file proves the quantitative local form of the unbalancing step used in
Bloom--Sisask, Proposition 18.  The positive-definite input is expressed by a
difference-convolution square root, as in `APAP.Physics.Unbalancing`; the
three error terms introduced by replacing the carrier measure are controlled
pointwise by fine Bohr regularity on the support of the weight.
-/

namespace Erdos721

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ComplexConjugate ComplexOrder ENNReal Indicator mu NNReal Pointwise

namespace CyclicLocalUnbalancing

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- A pointwise bound on the support of a probability weight bounds every
nonzero finite weighted `L^p` norm. -/
lemma wLpNorm_le_of_bound_on_support
    (nu : G → ℝ≥0) (f : G → ℝ) (p : ℕ) (hp : p ≠ 0)
    {e : ℝ} (he : 0 ≤ e) (hnu : ∑ x, nu x = 1)
    (hf : ∀ x, x ∈ Function.support nu → |f x| ≤ e) :
    ‖f‖_[p, nu] ≤ e := by
  rw [wLpNorm_eq_sum_norm (by exact_mod_cast hp) (by simp)]
  have hsum :
      ∑ x, (nu x : ℝ) * |f x| ^ (p : ℝ) ≤
        ∑ x, (nu x : ℝ) * e ^ (p : ℝ) := by
    apply Finset.sum_le_sum
    intro x _
    by_cases hx : nu x = 0
    · simp [hx]
    · gcongr
      exact hf x hx
  calc
    (∑ x, (nu x : ℝ) * |f x| ^ (p : ℝ)) ^ ((p : ℝ)⁻¹) ≤
        (∑ x, (nu x : ℝ) * e ^ (p : ℝ)) ^ ((p : ℝ)⁻¹) := by
      gcongr
    _ = e := by
      rw [← Finset.sum_mul, show ∑ x, (nu x : ℝ) = 1 by exact_mod_cast hnu,
        one_mul, ← Real.rpow_mul he]
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
      rw [mul_inv_cancel₀ hpR, Real.rpow_one]

variable {N : ℕ} [NeZero N]

/-- Every cyclic Bohr carrier is invariant under negation. -/
lemma neg_carrier (B : CyclicBohr.Set N) : -B.carrier = B.carrier := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_neg] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact B.neg_mem_iff y |>.2 hy
  · intro x hx
    rw [Finset.mem_neg]
    refine ⟨-x, B.neg_mem_iff x |>.2 hx, by simp⟩

/-- On a symmetric Bohr carrier, convolution and difference convolution
against its uniform measure agree. -/
lemma mu_dddconv_bohr_eq_ddconv (A : Finset (ZMod N))
    (B : CyclicBohr.Set N) :
    μ_[ℝ] A ○ᵈ μ_[ℝ] B.carrier =
      μ_[ℝ] A ∗ᵈ μ_[ℝ] B.carrier := by
  rw [← ddconv_conjneg, conjneg_mu, neg_carrier]

/-- The reversed mixed correlation at `x` is the forward one at `-x`. -/
lemma bohr_mu_dddconv_apply_eq (A : Finset (ZMod N))
    (B : CyclicBohr.Set N) (x : ZMod N) :
    (μ_[ℝ] B.carrier ○ᵈ μ_[ℝ] A) x =
      (μ_[ℝ] A ∗ᵈ μ_[ℝ] B.carrier) (-x) := by
  rw [← mu_dddconv_bohr_eq_ddconv A B]
  exact (dddconv_apply_neg (μ_[ℝ] A) (μ_[ℝ] B.carrier) x).symm

/-- Exact local four-term identity used after unbalancing. -/
lemma relativeBalance_dddconv_add_error
    (A : Finset (ZMod N)) (B : CyclicBohr.Set N) :
    (B.carrier.card : ℝ) •
          (CyclicRelativeLifting.relativeBalance A B.carrier ○ᵈ
            CyclicRelativeLifting.relativeBalance A B.carrier) + 1 +
        ((B.carrier.card : ℝ) •
            ((μ_[ℝ] A ○ᵈ μ_[ℝ] B.carrier) +
              (μ_[ℝ] B.carrier ○ᵈ μ_[ℝ] A) -
              (μ_[ℝ] B.carrier ○ᵈ μ_[ℝ] B.carrier)) - 1) =
      (B.carrier.card : ℝ) • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) := by
  simp only [CyclicRelativeLifting.relativeBalance, sub_dddconv, dddconv_sub]
  ext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply,
    smul_eq_mul]
  ring

/-- Three functions that are pointwise close to one have the required
three-term inclusion--exclusion combination close to one. -/
lemma abs_add_sub_sub_one_le_three_mul
    {a b c e : ℝ} (he : 0 ≤ e)
    (ha : |a - 1| ≤ e) (hb : |b - 1| ≤ e) (hc : |c - 1| ≤ e) :
    |a + b - c - 1| ≤ 3 * e := by
  have hid : a + b - c - 1 = (a - 1) + (b - 1) - (c - 1) := by ring
  rw [hid]
  calc
    |(a - 1) + (b - 1) - (c - 1)| ≤
        |(a - 1) + (b - 1)| + |c - 1| := abs_sub _ _
    _ ≤ (|a - 1| + |b - 1|) + |c - 1| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ (e + e) + e := by gcongr
    _ = 3 * e := by ring

/-- Local unbalancing on a fine regular Bohr dilate.  A large norm of the
locally balanced self-correlation yields a large norm of the unbalanced
self-correlation, with explicit exponent and error bounds. -/
theorem bohr_unbalancing
    (B : CyclicBohr.Set N) (A : Finset (ZMod N)) (m p : ℕ)
    {t delta alpha epsilon : ℝ}
    (hm : 0 < m) (hp : p ≠ 0) (halpha : 0 < alpha)
    (hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (hdelta : 0 ≤ delta) (hinner : 0 ≤ t - delta)
    (hregular :
      (10 * m) * (B.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (B.dilate (t - delta)).carrier.card)
    (hA : A.Nonempty) (hAB : A ⊆ (B.dilate t).carrier)
    (hAdense : alpha * (B.dilate t).carrier.card ≤ A.card)
    (nu : ZMod N → ℝ≥0) (root : ZMod N → ℂ)
    (hroot : root ○ᵈ root = fun x ↦ (nu x : ℂ))
    (hnu : ∑ x, nu x = 1)
    (hnusupport : Function.support nu ⊆
      ((B.dilate delta).carrier : Set (ZMod N)))
    (herror : 3 * (1 / ((5 * m : ℕ) * alpha)) ≤ epsilon / 4)
    (hlarge : epsilon ≤
      ‖(B.dilate t).carrier.card •
        (CyclicRelativeLifting.relativeBalance A (B.dilate t).carrier ○ᵈ
          CyclicRelativeLifting.relativeBalance A (B.dilate t).carrier)‖_[p, nu]) :
    ∃ p' : ℕ,
      p' ≤ 2 ^ 10 * epsilon⁻¹ ^ 2 * p ∧
      1 + epsilon / 4 ≤
        (B.dilate t).carrier.card •
          ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[p', nu] := by
  let C := B.dilate t
  let f : ZMod N → ℝ :=
    C.carrier.card •
      (CyclicRelativeLifting.relativeBalance A C.carrier ○ᵈ
        CyclicRelativeLifting.relativeBalance A C.carrier)
  let g : ZMod N → ℂ :=
    Real.sqrt C.carrier.card •
      (((↑) : ℝ → ℂ) ∘ CyclicRelativeLifting.relativeBalance A C.carrier)
  obtain ⟨p', hp'upper, hunbalance⟩ :=
      unbalancing' p hp epsilon hepsilon0 hepsilon1 nu f g root (by
        ext x : 1
        simp [g, f, smul_dddconv, dddconv_smul, ← mul_assoc, ← sq,
          ← Complex.ofReal_pow]) (by
            change root ○ᵈ root = fun x ↦ ((nu x : ℝ) : ℂ)
            exact hroot) hnu (by simpa [C, f] using hlarge)
  have hp'0 : p' ≠ 0 := by
    intro hp'zero
    subst p'
    simp at hunbalance
    linarith
  let err : ZMod N → ℝ :=
    (C.carrier.card : ℝ) •
        ((μ_[ℝ] A ○ᵈ μ_[ℝ] C.carrier) +
          (μ_[ℝ] C.carrier ○ᵈ μ_[ℝ] A) -
          (μ_[ℝ] C.carrier ○ᵈ μ_[ℝ] C.carrier)) - 1
  let e : ℝ := 1 / ((5 * m : ℕ) * alpha)
  have hCneg : -C.carrier = C.carrier := neg_carrier C
  have hstable (x : ZMod N) (hx : x ∈ B.dilate delta) :
      (5 * m) * CyclicBohr.translationDiscrepancy C.carrier x ≤
        C.carrier.card := by
    exact CyclicBohr.five_mul_m_translationDiscrepancy_le_card B m hm hdelta
      hinner hregular hx
  have halphaOne : alpha ≤ 1 := by
    have hcard := Finset.card_le_card hAB
    have hCcard : (0 : ℝ) < C.carrier.card := by
      exact_mod_cast C.card_pos
    have hAdenseR : alpha * (C.carrier.card : ℝ) ≤ A.card := by
      simpa [C] using hAdense
    have hcardR : (A.card : ℝ) ≤ C.carrier.card := by exact_mod_cast hcard
    nlinarith
  have hCdense : alpha * C.carrier.card ≤ C.carrier.card := by
    exact_mod_cast (mul_le_of_le_one_left (by positivity : (0 : ℝ) ≤ C.carrier.card)
      halphaOne)
  have herrPoint (x : ZMod N) (hx : x ∈ Function.support nu) :
      |err x| ≤ 3 * e := by
    have hxsmall : x ∈ B.dilate delta := hnusupport hx
    have hnegsmall : -x ∈ B.dilate delta :=
      (B.dilate delta).neg_mem_iff x |>.2 hxsmall
    have hforward :
        |(C.carrier.card : ℝ) *
            (μ_[ℝ] A ○ᵈ μ_[ℝ] C.carrier) x - 1| ≤ e := by
      rw [mu_dddconv_bohr_eq_ddconv]
      exact CyclicRelativeLifting.abs_card_mul_mu_ddconv_mu_sub_one_le_of_dense
        A C m hm halpha hA hAB (by simpa [C] using hAdense) (hstable x hxsmall)
    have hreverse :
        |(C.carrier.card : ℝ) *
            (μ_[ℝ] C.carrier ○ᵈ μ_[ℝ] A) x - 1| ≤ e := by
      rw [bohr_mu_dddconv_apply_eq]
      exact CyclicRelativeLifting.abs_card_mul_mu_ddconv_mu_sub_one_le_of_dense
        A C m hm halpha hA hAB (by simpa [C] using hAdense)
          (hstable (-x) hnegsmall)
    have hbase :
        |(C.carrier.card : ℝ) *
            (μ_[ℝ] C.carrier ○ᵈ μ_[ℝ] C.carrier) x - 1| ≤ e := by
      rw [mu_dddconv_bohr_eq_ddconv]
      exact CyclicRelativeLifting.abs_card_mul_mu_ddconv_mu_sub_one_le_of_dense
        C.carrier C m hm halpha C.carrier_nonempty (by rfl) hCdense
          (hstable x hxsmall)
    simpa only [err, e, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      Pi.one_apply, smul_eq_mul, mul_add, mul_sub] using
      abs_add_sub_sub_one_le_three_mul (by positivity) hforward hreverse hbase
  have herrNorm : ‖err‖_[p', nu] ≤ 3 * e :=
    wLpNorm_le_of_bound_on_support nu err p' hp'0 (by positivity) hnu herrPoint
  have hidentity :
      f + 1 + err = C.carrier.card • (μ_[ℝ] A ○ᵈ μ_[ℝ] A) := by
    simpa only [C, f, err, Nat.cast_smul_eq_nsmul] using
      relativeBalance_dddconv_add_error A C
  have htriangle :
      ‖f + 1‖_[p', nu] ≤
        C.carrier.card • ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[p', nu] +
          ‖err‖_[p', nu] := by
    calc
      ‖f + 1‖_[p', nu] ≤ ‖f + 1 + err‖_[p', nu] + ‖err‖_[p', nu] :=
        wLpNorm_le_add_wLpNorm_add (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp'0)
          nu (f + 1) err
      _ = _ := by rw [hidentity, wLpNorm_nsmul]
  refine ⟨p', hp'upper, ?_⟩
  have hchain :
      1 + epsilon / 2 ≤
        C.carrier.card • ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[p', nu] + 3 * e :=
    hunbalance.trans (htriangle.trans <| add_le_add_right herrNorm _)
  simpa only [C] using (show
    1 + epsilon / 4 ≤
      C.carrier.card • ‖μ_[ℝ] A ○ᵈ μ_[ℝ] A‖_[p', nu] by
        linarith)

end CyclicLocalUnbalancing
end Erdos721
