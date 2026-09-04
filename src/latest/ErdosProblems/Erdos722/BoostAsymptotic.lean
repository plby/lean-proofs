/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos722.Asymptotics
import ErdosProblems.Erdos722.BinomialBounds
import ErdosProblems.Erdos722.Boost
import Mathlib

/-!
# Asymptotic estimates for the regularity boost

This file discharges the natural-number ambient-extension estimate uniformly
over every omitted host whose maximum lower-face degree satisfies a fixed
power-cleared sparse bound.
-/

namespace Erdos722.BoostAsymptotic

open Finset Filter
open scoped Topology Real
open Erdos722.Asymptotics
open Erdos722.BinomialBounds
open Erdos722.Boost
open Erdos722.Counting

noncomputable section

/-- Half of the complete-host number of decoder ambients. -/
def boostAmbientLower (n q r : ℕ) : ℕ :=
  ambientScale n q r / 2

private def spoiledAmbientConstant (q r : ℕ) : ℝ :=
  q * 2 ^ (q + r)

private def ambientDominationConstant (q r : ℕ) : ℝ :=
  2 * spoiledAmbientConstant q r * (2 ^ q * q.factorial)

lemma sparseDegree_cast_le
    {d n D : ℕ} (hd : 0 < d)
    (hD : D ^ d ≤ n ^ (d - 1)) :
    (D : ℝ) ≤ (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d) := by
  have hthreshold := le_rationalPowerThreshold_of_pow_le
    (d - 1) d n D hd hD
  exact (Nat.cast_le.mpr hthreshold).trans
    (rationalPowerThreshold_cast_le (d - 1) d n)

lemma sparse_ambient_exponent_lt
    {q d : ℕ} (hq : 0 < q) (hd : 1 < d) :
    ((q - 1 : ℕ) : ℝ) + ((d - 1 : ℕ) : ℝ) / d < q := by
  have hdR : (0 : ℝ) < d := by positivity
  have hdsub : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  have hqsub : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub hq]
    norm_num
  rw [hqsub, hdsub]
  have hone : (0 : ℝ) < 1 / d := by positivity
  field_simp
  nlinarith

theorem eventually_sparse_ambient_domination
    (q r d : ℕ) (hq : 0 < q) (hd : 1 < d) :
    ∀ᶠ n : ℕ in atTop,
      ambientDominationConstant q r *
          (n : ℝ) ^ (((q - 1 : ℕ) : ℝ) +
            ((d - 1 : ℕ) : ℝ) / d) ≤
        (n : ℝ) ^ (q : ℝ) := by
  exact eventually_const_mul_rpow_le_rpow
    (sparse_ambient_exponent_lt hq hd)
    (by unfold ambientDominationConstant spoiledAmbientConstant; positivity)

/-- Uniformly over every power-bounded omitted graph, half of all complete
decoder ambients remain available through every host edge. -/
theorem eventually_decoderAmbients_half_lower
    (hr : 0 < r) (hrq : r < q) {d : ℕ} (hd : 1 < d) :
    ∀ᶠ n : ℕ in atTop, ∀ (D : ℕ)
      (G : Finset (Finset (Fin n))),
      D ^ d ≤ n ^ (d - 1) →
      G ⊆ Typicality.uniformEdges n r →
      LowerDegreeLE n r D (complementEdges n r G) →
      ∀ e ∈ G,
        boostAmbientLower n q r ≤ (decoderAmbients n q r G e).card := by
  have hdom := eventually_sparse_ambient_domination q r d (hr.trans hrq) hd
  filter_upwards [hdom, eventually_ge_atTop (2 * (r + q))] with n hdom hn
  intro D G hD hGsub hdegree e he
  have hecard : e.card = r := Typicality.mem_uniformEdges.mp (hGsub he)
  have heNot : e ∉ complementEdges n r G := by
    intro hec
    exact (Finset.mem_sdiff.mp hec).2 he
  have hspoiled := Counting.card_spoiledExtensions_le hr
    (by omega : r < q + r) Boost.complementEdges_uniform hdegree hecard heNot
  have hspoiled' :
      (Counting.spoiledExtensions n (q + r)
        (complementEdges n r G) e).card ≤
          q * n ^ (q - 1) * (2 ^ (q + r) * D) := by
    simpa [Nat.add_sub_cancel] using hspoiled
  have hDreal := sparseDegree_cast_le (by omega : 0 < d) hD
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hspReal :
      ((Counting.spoiledExtensions n (q + r)
        (complementEdges n r G) e).card : ℝ) ≤
        spoiledAmbientConstant q r *
          (n : ℝ) ^ (((q - 1 : ℕ) : ℝ) +
            ((d - 1 : ℕ) : ℝ) / d) := by
    calc
      ((Counting.spoiledExtensions n (q + r)
          (complementEdges n r G) e).card : ℝ) ≤
          (q * n ^ (q - 1) * (2 ^ (q + r) * D) : ℕ) := by
            exact_mod_cast hspoiled'
      _ = spoiledAmbientConstant q r * (n : ℝ) ^ (q - 1) * D := by
        unfold spoiledAmbientConstant
        push_cast
        ring
      _ ≤ spoiledAmbientConstant q r * (n : ℝ) ^ (q - 1) *
          (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d) := by
        gcongr
        unfold spoiledAmbientConstant
        positivity
      _ = spoiledAmbientConstant q r *
          (n : ℝ) ^ (((q - 1 : ℕ) : ℝ) +
            ((d - 1 : ℕ) : ℝ) / d) := by
        rw [← Real.rpow_natCast, Real.rpow_add hnpos]
        ring
  have hambientLower := half_pow_div_factorial_le_choose_sub n r q hn
  have hspHalfReal :
      (2 : ℝ) *
          (Counting.spoiledExtensions n (q + r)
            (complementEdges n r G) e).card ≤
        (ambientScale n q r : ℝ) := by
    calc
      (2 : ℝ) *
          (Counting.spoiledExtensions n (q + r)
            (complementEdges n r G) e).card ≤
          2 * (spoiledAmbientConstant q r *
            (n : ℝ) ^ (((q - 1 : ℕ) : ℝ) +
              ((d - 1 : ℕ) : ℝ) / d)) := by gcongr
      _ ≤ (n : ℝ) ^ q / (2 ^ q * q.factorial) := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) <
          2 ^ q * q.factorial)).2
        calc
          2 * (spoiledAmbientConstant q r *
              (n : ℝ) ^ (((q - 1 : ℕ) : ℝ) +
                ((d - 1 : ℕ) : ℝ) / d)) *
                (2 ^ q * q.factorial) =
              ambientDominationConstant q r *
                (n : ℝ) ^ (((q - 1 : ℕ) : ℝ) +
                  ((d - 1 : ℕ) : ℝ) / d) := by
            unfold ambientDominationConstant
            ring
          _ ≤ (n : ℝ) ^ (q : ℕ) := by
            simpa only [Real.rpow_natCast] using hdom
      _ = ((n : ℝ) / 2) ^ q / q.factorial := by
        rw [div_pow]
        ring
      _ ≤ (Nat.choose (n - r) q : ℝ) := hambientLower
      _ = (ambientScale n q r : ℝ) := rfl
  have hspHalf :
      2 * (Counting.spoiledExtensions n (q + r)
        (complementEdges n r G) e).card ≤ ambientScale n q r := by
    exact_mod_cast hspHalfReal
  rw [card_decoderAmbients_eq_sub_spoiled hecard]
  unfold boostAmbientLower
  omega

private def boostQuantCoreConstant (q r : ℕ) : ℝ :=
  ((q - r) * 2 ^ q : ℕ) * decoderBound q r * (2 ^ (q + r) : ℕ)

private def boostQuantDominationConstant (q r : ℕ) : ℝ :=
  boostQuantCoreConstant q r * (3 * 2 ^ q * q.factorial : ℕ)

lemma boost_quant_exponent_lt
    (hrq : r < q) {d : ℕ} (hd : 1 < d) :
    ((q - 1 : ℕ) : ℝ) + ((d - 1 : ℕ) : ℝ) / d < q :=
  sparse_ambient_exponent_lt (by omega) hd

theorem eventually_boost_quant_domination
    (hrq : r < q) {d : ℕ} (hd : 1 < d) :
    ∀ᶠ n : ℕ in atTop,
      boostQuantDominationConstant q r *
          (n : ℝ) ^ (((q - 1 : ℕ) : ℝ) +
            ((d - 1 : ℕ) : ℝ) / d) ≤
        (n : ℝ) ^ (q : ℝ) := by
  exact eventually_const_mul_rpow_le_rpow
    (boost_quant_exponent_lt hrq hd)
    (by
      unfold boostQuantDominationConstant boostQuantCoreConstant decoderBound
      positivity)

/-- The pointwise correction term in the local-decoder boost is eventually
small enough to remain inside the Bernoulli interval `[0,1]`, uniformly over
all complements satisfying the power-cleared sparse-degree bound. -/
theorem eventually_boost_quantitative_bound
    (hrq : r < q) {d : ℕ} (hd : 1 < d) :
    ∀ᶠ n : ℕ in atTop, ∀ D : ℕ,
      D ^ d ≤ n ^ (d - 1) →
      (extensionScale n q r : ℝ) *
        (sparseDefectBound n q r D * decoderBound q r *
          sparseMassBound n q r (boostAmbientLower n q r)) ≤ 1 / 2 := by
  have hdom := eventually_boost_quant_domination hrq hd
  filter_upwards [hdom, eventually_ge_atTop (2 * (r + q)),
    eventually_ge_atTop (r + q + 1)] with n hdom hn hnlarge
  intro D hD
  let E := extensionScale n q r
  let A := boostAmbientLower n q r
  have hqpos : 0 < q := by omega
  have hnposNat : 0 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
  have hEpos : 0 < E := by
    dsimp [E, extensionScale]
    exact Nat.choose_pos (by omega)
  have hApos : 0 < A := by
    dsimp [A, boostAmbientLower, ambientScale]
    have hchoose : q + 1 ≤ Nat.choose (n - r) q := by
      calc
        q + 1 = Nat.choose (q + 1) q := by simp
        _ ≤ Nat.choose (n - r) q := Nat.choose_le_choose q (by omega)
    omega
  have hAcast : (ambientScale n q r : ℝ) / 3 ≤ (A : ℝ) := by
    have hA_nat : ambientScale n q r ≤ 3 * A := by
      dsimp [A, boostAmbientLower]
      have htwo : 2 ≤ ambientScale n q r := by
        dsimp [ambientScale]
        have hchoose : q + 1 ≤ Nat.choose (n - r) q := by
          calc
            q + 1 = Nat.choose (q + 1) q := by simp
            _ ≤ Nat.choose (n - r) q := Nat.choose_le_choose q (by omega)
        omega
      omega
    have hreal : (ambientScale n q r : ℝ) ≤ 3 * (A : ℝ) := by
      exact_mod_cast hA_nat
    linarith
  have hambientLower := half_pow_div_factorial_le_choose_sub n r q hn
  have hpowerA : (n : ℝ) ^ q /
      (3 * 2 ^ q * q.factorial : ℕ) ≤ (A : ℝ) := by
    calc
      (n : ℝ) ^ q / (3 * 2 ^ q * q.factorial : ℕ) =
          (((n : ℝ) / 2) ^ q / q.factorial) / 3 := by
        push_cast
        rw [div_pow]
        ring
      _ ≤ (ambientScale n q r : ℝ) / 3 := by
        gcongr
        simpa [ambientScale] using hambientLower
      _ ≤ (A : ℝ) := hAcast
  have hDreal := sparseDegree_cast_le (by omega : 0 < d) hD
  have hcore : boostQuantCoreConstant q r * (D : ℝ) *
      (n : ℝ) ^ (q - 1) ≤
        boostQuantCoreConstant q r *
          (n : ℝ) ^ (((q - 1 : ℕ) : ℝ) +
            ((d - 1 : ℕ) : ℝ) / d) := by
    calc
      boostQuantCoreConstant q r * (D : ℝ) * (n : ℝ) ^ (q - 1) ≤
          boostQuantCoreConstant q r *
            (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d) *
              (n : ℝ) ^ (q - 1) := by
        gcongr
        unfold boostQuantCoreConstant decoderBound
        positivity
      _ = boostQuantCoreConstant q r *
          (n : ℝ) ^ (((q - 1 : ℕ) : ℝ) +
            ((d - 1 : ℕ) : ℝ) / d) := by
        rw [← Real.rpow_natCast, Real.rpow_add hnpos]
        ring
  have hcoreA : boostQuantCoreConstant q r * (D : ℝ) *
      (n : ℝ) ^ (q - 1) ≤ (A : ℝ) := by
    apply hcore.trans
    apply hpowerA.trans'
    apply (le_div_iff₀ (by positivity : (0 : ℝ) <
      (3 * 2 ^ q * q.factorial : ℕ))).2
    calc
      boostQuantCoreConstant q r *
          (n : ℝ) ^ (((q - 1 : ℕ) : ℝ) +
            ((d - 1 : ℕ) : ℝ) / d) *
            (3 * 2 ^ q * q.factorial : ℕ) =
          boostQuantDominationConstant q r *
            (n : ℝ) ^ (((q - 1 : ℕ) : ℝ) +
              ((d - 1 : ℕ) : ℝ) / d) := by
        unfold boostQuantDominationConstant
        ring
      _ ≤ (n : ℝ) ^ (q : ℕ) := by
        simpa only [Real.rpow_natCast] using hdom
  have hnum :
      (((q - r) * n ^ (q - r - 1) * (2 ^ q * D) : ℕ) : ℝ) *
          decoderBound q r *
          ((n ^ r * 2 ^ (q + r) : ℕ) : ℝ) ≤
        (A : ℝ) := by
    have hpow : (n : ℝ) ^ (q - r - 1) * (n : ℝ) ^ r =
        (n : ℝ) ^ (q - 1) := by
      rw [← pow_add, show q - r - 1 + r = q - 1 by omega]
    calc
      (((q - r) * n ^ (q - r - 1) * (2 ^ q * D) : ℕ) : ℝ) *
          decoderBound q r *
          ((n ^ r * 2 ^ (q + r) : ℕ) : ℝ) =
        boostQuantCoreConstant q r * (D : ℝ) *
          (n : ℝ) ^ (q - 1) := by
            unfold boostQuantCoreConstant
            push_cast
            rw [← hpow]
            ring
      _ ≤ (A : ℝ) := hcoreA
  have hEne : (E : ℝ) ≠ 0 := by exact_mod_cast hEpos.ne'
  have hAne : (A : ℝ) ≠ 0 := by exact_mod_cast hApos.ne'
  change (E : ℝ) *
    (((((q - r) * n ^ (q - r - 1) * (2 ^ q * D) : ℕ) : ℝ) /
        (2 * E : ℕ)) * decoderBound q r *
      (((n ^ r * 2 ^ (q + r) : ℕ) : ℝ) / A)) ≤ 1 / 2
  have heq : (E : ℝ) *
      (((((q - r) * n ^ (q - r - 1) * (2 ^ q * D) : ℕ) : ℝ) /
          (2 * E : ℕ)) * decoderBound q r *
        (((n ^ r * 2 ^ (q + r) : ℕ) : ℝ) / A)) =
      ((((q - r) * n ^ (q - r - 1) * (2 ^ q * D) : ℕ) : ℝ) *
          decoderBound q r *
          ((n ^ r * 2 ^ (q + r) : ℕ) : ℝ)) / (2 * A) := by
    push_cast
    field_simp
  rw [heq]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * A)).2
  nlinarith

/-- The absolute rounding error used in the boost: `n^(q-r-4/9)`, with
the fractional exponent power-cleared by denominator nine.  This slightly
stronger rounding scale leaves room for the reciprocal nibble barriers. -/
def boostErrorNumerator (q r : ℕ) : ℕ := 9 * (q - r) - 4

def boostError (n q r : ℕ) : ℕ :=
  rationalPowerThreshold (boostErrorNumerator q r) 9 n

def boostTailNumerator (q r : ℕ) : ℕ := 9 * (q - r) - 8

def boostErrorExponent (q r : ℕ) : ℝ :=
  (boostErrorNumerator q r : ℝ) / 9

def boostTailExponent (q r : ℕ) : ℝ :=
  (boostTailNumerator q r : ℝ) / 9

lemma boost_exponent_identities (hrq : r < q) :
    0 < boostErrorNumerator q r ∧
    0 < boostTailNumerator q r ∧
    2 * boostErrorExponent q r =
      (q - r : ℕ) + boostTailExponent q r := by
  have hs : 1 ≤ q - r := by omega
  constructor
  · unfold boostErrorNumerator
    omega
  constructor
  · unfold boostTailNumerator
    omega
  · unfold boostErrorExponent boostTailExponent boostErrorNumerator
      boostTailNumerator
    rw [Nat.cast_sub (by omega : 4 ≤ 9 * (q - r)),
      Nat.cast_sub (by omega : 8 ≤ 9 * (q - r))]
    push_cast
    ring

lemma incidentClique_nonempty_of_decoderAmbient
    (hrq : r ≤ q) {G : Finset (Finset (Fin n))}
    {e : Finset (Fin n)} (hecard : e.card = r)
    (hZ : (decoderAmbients n q r G e).Nonempty) :
    Nonempty (IncidentClique n q r G e) := by
  classical
  obtain ⟨Z, hZ⟩ := hZ
  have hZdata := mem_decoderAmbients.mp hZ
  obtain ⟨Q, heQ, hQZ, hQcard⟩ :=
    Finset.exists_subsuperset_card_eq hZdata.2.1
      (by simpa [hecard] using hrq) (by omega : q ≤ Z.card)
  have hQclique : Q ∈ cliqueFamily n q r G := by
    apply mem_cliqueFamily.mpr
    refine ⟨hQcard, ?_⟩
    intro f hf
    exact hZdata.2.2 (Finset.mem_powersetCard.mpr
      ⟨(Finset.mem_powersetCard.mp hf).1.trans hQZ,
        (Finset.mem_powersetCard.mp hf).2⟩)
  exact ⟨⟨Q, hQclique, heQ⟩⟩

theorem eventually_boost_error_lower (hrq : r < q) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ boostErrorExponent q r / 2 ≤ boostError n q r := by
  simpa [boostError, boostErrorExponent] using
    eventually_half_rpow_le_rationalPowerThreshold
      (boost_exponent_identities hrq).1 (by norm_num : 0 < (9 : ℕ))

/-- The Hoeffding union bound for independently rounding the corrected
weights tends to zero, uniformly over the host and its power-bounded sparse
complement. -/
theorem eventually_boost_tail_bound
    (hr : 0 < r) (hrq : r < q) {d : ℕ} (hd : 1 < d) :
    ∀ᶠ n : ℕ in atTop, ∀ (D : ℕ)
      (G : Finset (Finset (Fin n))),
      D ^ d ≤ n ^ (d - 1) →
      G ⊆ Typicality.uniformEdges n r →
      LowerDegreeLE n r D (complementEdges n r G) →
      (∑ e ∈ G, 2 * Real.exp
        (-(boostError n q r : ℝ) ^ 2 /
          (2 * (∑ _Q : IncidentClique n q r G e,
            (Probability.hoeffdingUnitVariance : ℝ))))) < 1 := by
  let γ := boostTailExponent q r
  have hγ : 0 < γ := by
    dsimp [γ, boostTailExponent]
    exact div_pos (by exact_mod_cast (boost_exponent_identities hrq).2.1)
      (by norm_num)
  have hdecay := Reserve.tendsto_pow_mul_exp_neg_rpow_atTop r hγ
    (by norm_num : (0 : ℝ) < 1 / 8)
  have hconst : Tendsto
      (fun x : ℝ ↦ 2 * (x ^ r * Real.exp (-(1 / 8 : ℝ) * x ^ γ)))
      atTop (nhds 0) := by
    have htwo : Tendsto (fun _ : ℝ ↦ (2 : ℝ)) atTop (nhds 2) :=
      tendsto_const_nhds
    simpa only [mul_zero] using htwo.mul hdecay
  have hnat := hconst.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop,
      2 * ((n : ℝ) ^ r *
        Real.exp (-(1 / 8 : ℝ) * (n : ℝ) ^ γ)) < 1 :=
    (tendsto_order.1 hnat).2 _ (by norm_num)
  have herr := eventually_boost_error_lower hrq
  have hambient := eventually_decoderAmbients_half_lower hr hrq hd
  filter_upwards [hsmall, herr, hambient,
    eventually_ge_atTop (r + q + 1)] with n hsmall herr hambient hn
  intro D G hD hGsub hdegree
  have hnposNat : 0 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
  have hEpos : 0 < extensionScale n q r := by
    exact Nat.choose_pos (by simp [extensionScale]; omega)
  have hApos : 0 < boostAmbientLower n q r := by
    dsimp [boostAmbientLower, ambientScale]
    have hchoose : q + 1 ≤ Nat.choose (n - r) q := by
      calc
        q + 1 = Nat.choose (q + 1) q := by simp
        _ ≤ Nat.choose (n - r) q := Nat.choose_le_choose q (by omega)
    omega
  have htailExp :
      2 * boostErrorExponent q r = (q - r : ℕ) + γ := by
    simpa [γ] using (boost_exponent_identities hrq).2.2
  have herrorSq : (n : ℝ) ^ (2 * boostErrorExponent q r) / 4 ≤
      (boostError n q r : ℝ) ^ 2 := by
    have herr0 : 0 ≤ (n : ℝ) ^ boostErrorExponent q r / 2 := by positivity
    have hsquare := pow_le_pow_left₀ herr0 herr 2
    have hpow : (n : ℝ) ^ (2 * boostErrorExponent q r) =
        ((n : ℝ) ^ boostErrorExponent q r) ^ 2 := by
      calc
        (n : ℝ) ^ (2 * boostErrorExponent q r) =
            (n : ℝ) ^ (boostErrorExponent q r * 2) := by
              apply congrArg (fun z : ℝ ↦ (n : ℝ) ^ z)
              ring
        _ = ((n : ℝ) ^ boostErrorExponent q r) ^ (2 : ℝ) :=
          Real.rpow_mul (Nat.cast_nonneg n) _ _
        _ = ((n : ℝ) ^ boostErrorExponent q r) ^ (2 : ℕ) :=
          Real.rpow_natCast _ 2
    calc
      (n : ℝ) ^ (2 * boostErrorExponent q r) / 4 =
          ((n : ℝ) ^ boostErrorExponent q r / 2) ^ 2 := by
        rw [hpow, div_pow]
        norm_num
      _ ≤ (boostError n q r : ℝ) ^ 2 := hsquare
  have hEupper : (extensionScale n q r : ℝ) ≤
      (n : ℝ) ^ (q - r) := by
    exact_mod_cast (Nat.choose_le_pow (n - r) (q - r) |>.trans
      (Nat.pow_le_pow_left (Nat.sub_le n r) (q - r)))
  calc
    (∑ e ∈ G, 2 * Real.exp
        (-(boostError n q r : ℝ) ^ 2 /
          (2 * (∑ _Q : IncidentClique n q r G e,
            (Probability.hoeffdingUnitVariance : ℝ))))) ≤
      ∑ _e ∈ G, 2 * Real.exp
        (-(1 / 8 : ℝ) * (n : ℝ) ^ γ) := by
      apply Finset.sum_le_sum
      intro e he
      have hecard : e.card = r :=
        Typicality.mem_uniformEdges.mp (hGsub he)
      have hdecCard := hambient D G hD hGsub hdegree e he
      have hdecNonempty : (decoderAmbients n q r G e).Nonempty :=
        Finset.card_pos.mp (hApos.trans_le hdecCard)
      have hinc : Nonempty (IncidentClique n q r G e) :=
        incidentClique_nonempty_of_decoderAmbient hrq.le hecard hdecNonempty
      let S : ℝ := ∑ _Q : IncidentClique n q r G e,
        (Probability.hoeffdingUnitVariance : ℝ)
      have hSpos : 0 < S := by
        dsimp [S, Probability.hoeffdingUnitVariance]
        have hcardpos : 0 < Fintype.card (IncidentClique n q r G e) :=
          Fintype.card_pos
        simp only [one_div, inv_pow, sum_const, card_univ, nsmul_eq_mul, inv_pos, Nat.ofNat_pos, pow_succ_pos,
    mul_pos_iff_of_pos_right, Nat.cast_pos, gt_iff_lt]
        positivity
      have hSupper : S ≤ (extensionScale n q r : ℝ) := by
        calc
          S ≤ Fintype.card (IncidentClique n q r G e) := by
            dsimp [S, Probability.hoeffdingUnitVariance]
            simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
              Finset.sum_const, nsmul_eq_mul]
            norm_num
            have hcard0 : (0 : ℝ) ≤
                Fintype.card (IncidentClique n q r G e) := by positivity
            linarith
          _ ≤ (extensionScale n q r : ℝ) := by
            exact_mod_cast fintypeCard_incidentClique_le hrq.le hecard
      have hratio : (n : ℝ) ^ γ / 8 ≤
          (boostError n q r : ℝ) ^ 2 / (2 * S) := by
        have hpowid : (n : ℝ) ^ (2 * boostErrorExponent q r) =
            (n : ℝ) ^ (q - r) * (n : ℝ) ^ γ := by
          rw [htailExp, Real.rpow_add hnpos, Real.rpow_natCast]
        calc
          (n : ℝ) ^ γ / 8 =
              ((n : ℝ) ^ (2 * boostErrorExponent q r) / 4) /
                (2 * (n : ℝ) ^ (q - r)) := by
            rw [hpowid]
            field_simp
            ring
          _ ≤ ((n : ℝ) ^ (2 * boostErrorExponent q r) / 4) /
                (2 * S) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left (hSupper.trans hEupper)
              (by norm_num)
          _ ≤ (boostError n q r : ℝ) ^ 2 / (2 * S) := by
            exact div_le_div_of_nonneg_right herrorSq (by positivity)
      gcongr
      convert neg_le_neg hratio using 1 <;> ring
    _ = (G.card : ℝ) *
        (2 * Real.exp (-(1 / 8 : ℝ) * (n : ℝ) ^ γ)) := by simp
    _ ≤ (n : ℝ) ^ r *
        (2 * Real.exp (-(1 / 8 : ℝ) * (n : ℝ) ^ γ)) := by
      gcongr
      calc
        (G.card : ℝ) ≤ Nat.choose n r := by
          exact_mod_cast (by
            simpa [Typicality.uniformEdges] using Finset.card_le_card hGsub)
        _ ≤ (n : ℝ) ^ r := by exact_mod_cast Nat.choose_le_pow n r
    _ = 2 * ((n : ℝ) ^ r *
        Real.exp (-(1 / 8 : ℝ) * (n : ℝ) ^ γ)) := by ring
    _ < 1 := hsmall

/-- Fully asymptotic regularity boost under a power-cleared sparse-complement
degree hypothesis. -/
theorem eventually_exists_boost_of_power_bounded_complement
    (hr : 0 < r) (hrq : r < q) {d : ℕ} (hd : 1 < d) :
    ∀ᶠ n : ℕ in atTop, ∀ (D : ℕ)
      (G : Finset (Finset (Fin n))),
      D ^ d ≤ n ^ (d - 1) →
      G ⊆ Typicality.uniformEdges n r →
      LowerDegreeLE n r D (complementEdges n r G) →
      ∃ H : Finset (Finset (Fin n)), H ⊆ cliqueFamily n q r G ∧
        ∀ e ∈ G,
          |((H.filter fun Q ↦ e ⊆ Q).card : ℝ) -
              (extensionScale n q r : ℝ) / 2| < boostError n q r := by
  have hambient := eventually_decoderAmbients_half_lower hr hrq hd
  have hquant := eventually_boost_quantitative_bound hrq hd
  have htail := eventually_boost_tail_bound hr hrq hd
  filter_upwards [hambient, hquant, htail,
    eventually_ge_atTop (r + q + 1)] with n hambient hquant htail hn
  intro D G hD hGsub hdegree
  have hscale : 0 < extensionScale n q r := by
    exact Nat.choose_pos (by simp [extensionScale]; omega)
  have hApos : 0 < boostAmbientLower n q r := by
    dsimp [boostAmbientLower, ambientScale]
    have hchoose : q + 1 ≤ Nat.choose (n - r) q := by
      calc
        q + 1 = Nat.choose (q + 1) q := by simp
        _ ≤ Nat.choose (n - r) q := Nat.choose_le_choose q (by omega)
    omega
  exact exists_boost_of_sparse_finite hr hrq hGsub hdegree hscale hApos
    (hambient D G hD hGsub hdegree) (hquant D hD)
    (boostError n q r : ℝ) (by positivity)
    (htail D G hD hGsub hdegree)

end

end Erdos722.BoostAsymptotic
