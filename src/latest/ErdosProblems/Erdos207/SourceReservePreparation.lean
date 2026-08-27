/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceReserveGoodProbability
import ErdosProblems.Erdos207.IterationReserveRegularization
import ErdosProblems.Erdos207.ReserveRegularizationPowerScalars
import ErdosProblems.Erdos207.PolynomialExponentialDecay
import ErdosProblems.Erdos207.IntermediateLinkSourceGeometry

/-! # One reserve sample supplies the regularizer and both cover stages -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def reserveRegularizationFailureBound (n : ℕ) (p eta r : ℝ≥0) : ℝ≥0 :=
  12 * (n + 1 : ℝ≥0) ^ 4 * (Real.exp (-(r : ℝ) * ((p : ℝ) ^ 4 * (eta : ℝ) ^ 6 * n) / 8)).toNNReal

def SourceReservePreparationGood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : TripleSystemOn V) (current U : Finset V)
    (p eta r : ℝ≥0) (epsilon theta : ℝ) (supply : ℕ) (bits : Sym2 V → Bool) : Prop :=
  SourceReserveGood G A current U p eta r epsilon supply bits ∧
    HasReserveRegularizedTriangles G U current A p eta theta bits

theorem IsIterationTypical.sourceReservePreparation_failure_probability_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {stage : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V} {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (htri : ConsistsOfTriangles G A) (hp : 0 < p) (hp1 : p ≤ 1) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V)) (hh : 4 ≤ h)
    (r : ℝ≥0) (hr : r ≤ 1) (hrsmall : r ≤ 1 / 24576)
    (epsilon theta : ℝ) (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hxi : (xi : ℝ) ≤ epsilon / 4) (hxiSmall : xi ≤ 1 / 1536)
    (hendpoint : 1 ≤ (epsilon / 4) * ((p : ℝ) ^ 2 * eta * (W.U i.succ).card))
    (supply : ℕ) (hsupply : (supply : ℝ) ≤ (r : ℝ) ^ 2 * (p : ℝ) ^ 2 * eta * (W.U i.succ).card / 8)
    (hdensity : 6144 ≤ p ^ 4 * eta ^ 6 * (W.U i.castSucc).card)
    (hinner : ((W.U i.succ).card : ℝ≥0) ≤ p ^ 4 * eta ^ 6 * (W.U i.castSucc).card / 1536)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hsampling : 2 * ((W.U i.castSucc).card : ℝ) ^ 2 *
      Real.exp (-theta ^ 2 * ((p : ℝ) ^ 2 * eta * (W.U i.castSucc).card) / 16) < 1) :
    (reserveEdgeLaw G (W.U i.succ) r hr).probability (fun bits ↦
      ¬ SourceReservePreparationGood G A (W.U i.castSucc) (W.U i.succ) p eta r epsilon theta supply bits) ≤
      sourceReserveFailureBound (Fintype.card V) (W.U i.succ).card p eta r epsilon +
        reserveRegularizationFailureBound (W.U i.castSucc).card p eta r := by
  have hcover := htyp.sourceReserveGood_failure_probability_le htri hp1 heta1 i hstage hGsupp (by omega)
    r hr epsilon hepsilon hepsilon1 hxi hendpoint supply hsupply
  have hregular := htyp.reserve_probability_no_regularized_triangles i hstage hh (W.U i.succ) r hr
    hGsupp (fun T hT ↦ htri.triple_edges_subset hT) hp hp1 heta heta1 hxiSmall hrsmall hdensity hinner
    theta htheta htheta1 hsampling
  have hregNN : (reserveEdgeLaw G (W.U i.succ) r hr).probability
      (fun bits ↦ ¬ HasReserveRegularizedTriangles G (W.U i.succ) (W.U i.castSucc) A p eta theta bits) ≤
        reserveRegularizationFailureBound (W.U i.castSucc).card p eta r := by
    apply NNReal.coe_le_coe.mp
    simpa only [reserveRegularizationFailureBound, NNReal.coe_mul, NNReal.coe_pow,
      NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_ofNat, NNReal.coe_one,
      Real.coe_toNNReal _ (Real.exp_pos _).le] using hregular
  have hb := (reserveEdgeLaw G (W.U i.succ) r hr).probability_or_le
    (fun bits ↦ ¬ SourceReserveGood G A (W.U i.castSucc) (W.U i.succ) p eta r epsilon supply bits)
    (fun bits ↦ ¬ HasReserveRegularizedTriangles G (W.U i.succ) (W.U i.castSucc) A p eta theta bits)
  simpa only [SourceReservePreparationGood, not_and_or] using hb.trans (add_le_add hcover hregNN)

theorem eventually_reserveRegularizationFailureBound_le_power
    (reserveExp b L R decay : ℕ) (eta0 error0 : ℝ≥0)
    (heta0 : 0 < eta0) (herror0 : 0 < error0) (hL : 4 * b + reserveExp + 1 ≤ L) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ (n : ℕ) (p eta r : ℝ≥0), n ≤ t ^ R → t ^ L ≤ n →
      1 / (t : ℝ≥0) ^ b ≤ p → 1 / (t : ℝ≥0) ^ reserveExp ≤ r → eta0 ≤ eta →
      reserveRegularizationFailureBound n p eta r ≤ error0 / (t : ℝ≥0) ^ decay := by
  let c : ℝ := (eta0 : ℝ) ^ 6 / 8
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨T, hT1, hT⟩ := eventually_polynomial_exp_neg_mul_lt 192 c error0 (4 * R + decay)
    hc (by exact_mod_cast herror0)
  refine ⟨T, hT1, ?_⟩
  intro t ht n p eta r hn hu hp hr heta
  have ht1 : 1 ≤ t := hT1.trans ht
  have htNN : (1 : ℝ≥0) ≤ t := by exact_mod_cast ht1
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hscale := inversePower_reserve_exponent_scale t p eta eta0 n b reserveExp L htNN hL
    (by exact_mod_cast hu) hp heta
  have hscaleR : (eta0 : ℝ) ^ 6 * t ≤ (r : ℝ) * ((p : ℝ) ^ 4 * (eta : ℝ) ^ 6 * n) := by
    exact_mod_cast hscale.trans (mul_le_mul_of_nonneg_right hr
      (show 0 ≤ p ^ 4 * eta ^ 6 * n from zero_le))
  have hexp : Real.exp (-(r : ℝ) * ((p : ℝ) ^ 4 * (eta : ℝ) ^ 6 * n) / 8) ≤ Real.exp (-c * t) := by
    apply Real.exp_le_exp.mpr
    dsimp only [c]
    linarith only [hscaleR]
  have hnR : (n : ℝ) ≤ (t : ℝ) ^ R := by exact_mod_cast hn
  have hone : (1 : ℝ) ≤ (t : ℝ) ^ R := one_le_pow₀ (by exact_mod_cast ht1)
  have hplus : (n + 1 : ℝ) ≤ 2 * (t : ℝ) ^ R := by linarith
  have hcoef : 12 * (n + 1 : ℝ) ^ 4 ≤ 192 * (t : ℝ) ^ (4 * R) := by
    calc
      _ ≤ 12 * (2 * (t : ℝ) ^ R) ^ 4 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hplus _) (by norm_num)
      _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_comm R 4]; ring
  apply NNReal.coe_le_coe.mp
  simp only [reserveRegularizationFailureBound, NNReal.coe_mul, NNReal.coe_pow,
    NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_ofNat, NNReal.coe_one, NNReal.coe_div,
    Real.coe_toNNReal _ (Real.exp_pos _).le]
  apply (mul_le_mul hcoef hexp (Real.exp_pos _).le (by positivity)).trans
  apply (le_div_iff₀ (pow_pos ht0 decay)).mpr
  have hb := (hT t ht).le
  rw [pow_add] at hb
  nlinarith only [hb]

end

end Erdos207
