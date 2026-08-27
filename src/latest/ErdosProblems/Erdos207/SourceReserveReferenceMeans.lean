/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveLinkReferenceTests
import ErdosProblems.Erdos207.IterationLinkRealWindows

/-! # Source typicality supplies the actual reserve reference means -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem real_scaled_reference_mean_window
    (base actual r xi epsilon : ℝ) (hbase : 0 ≤ base) (hr : 0 ≤ r) (hxi : xi ≤ epsilon/2)
    (hactual : (1-xi)*base ≤ actual ∧ actual ≤ (1+xi)*base) :
    (1-epsilon/2)*(r*base) ≤ r*actual ∧ r*actual ≤ (1+epsilon/2)*(r*base) := by
  have hcoeff := mul_le_mul_of_nonneg_right hxi hbase
  have hlo : (1-epsilon/2)*base ≤ actual := by nlinarith only [hcoeff, hactual.1]
  have hhi : actual ≤ (1+epsilon/2)*base := by nlinarith only [hcoeff, hactual.2]
  constructor
  · have hb := mul_le_mul_of_nonneg_left hlo hr
    nlinarith only [hb]
  · have hb := mul_le_mul_of_nonneg_left hhi hr
    nlinarith only [hb]

theorem real_scaled_reference_mean_window_of_endpoint_loss
    (base actual r xi epsilon : ℝ) (hbase : 0 ≤ base) (hr : 0 ≤ r) (hepsilon : 0 ≤ epsilon)
    (hxi : xi ≤ epsilon/4) (hendpoint : 1 ≤ (epsilon/4)*base)
    (hactual : (1-xi)*base-1 ≤ actual ∧ actual ≤ (1+xi)*base) :
    (1-epsilon/2)*(r*base) ≤ r*actual ∧ r*actual ≤ (1+epsilon/2)*(r*base) := by
  have hcoeff := mul_le_mul_of_nonneg_right hxi hbase
  have hxi' : xi ≤ epsilon/2 := by linarith only [hxi, hepsilon]
  have hcoeff' := mul_le_mul_of_nonneg_right hxi' hbase
  have hlo : (1-epsilon/2)*base ≤ actual := by nlinarith only [hcoeff, hendpoint, hactual.1]
  have hhi : actual ≤ (1+epsilon/2)*base := by nlinarith only [hcoeff', hactual.2]
  constructor
  · have hb := mul_le_mul_of_nonneg_left hlo hr
    nlinarith only [hb]
  · have hb := mul_le_mul_of_nonneg_left hhi hr
    nlinarith only [hb]

theorem IsIterationTypical.reserveLinkReference_means
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell+1)} {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ} (htyp : IsIterationTypical W k G A p eta xi h)
    (hxi1 : xi ≤ 1) (i : Fin ell) (hki : k.val ≤ i.val) (hh : 3 ≤ h)
    (r : ℝ≥0) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (hxi : (xi : ℝ) ≤ epsilon/4)
    (hendpoint : 1 ≤ (epsilon/4)*((p : ℝ)^2*eta*(W.U i.succ).card)) :
    ∀ j : ReserveLinkTest V, reserveLinkTestRelevant G (W.U i.castSucc) (W.U i.succ) j →
      (reserveLinkTestLower j = true →
        (1-epsilon/2)*reserveLinkTestTarget ((r : ℝ)*p*(W.U i.succ).card) ((p : ℝ)*eta) j ≤
          (r : ℝ)*(reserveLinkTestEdges G A (W.U i.succ) j).card) ∧
        (r : ℝ)*(reserveLinkTestEdges G A (W.U i.succ) j).card ≤
          (1+epsilon/2)*reserveLinkTestTarget ((r : ℝ)*p*(W.U i.succ).card) ((p : ℝ)*eta) j := by
  have hsub : W.U i.succ ⊆ W.U i.castSucc := W.antitone _ _ (by change i.val ≤ i.val+1; omega)
  have hxiHalf : (xi : ℝ) ≤ epsilon/2 := by linarith only [hxi, hepsilon]
  intro j hj
  rcases j with c | (⟨c,x⟩ | ⟨c,x,y⟩)
  · have hw := htyp.neighbor_real_window hxi1 i hki c hj.1
    have hb := real_scaled_reference_mean_window ((p : ℝ)*(W.U i.succ).card)
      ((neighborsIn G (W.U i.succ) c).card : ℝ) r xi epsilon (by positivity) (by positivity) hxiHalf hw
    have hcard : ((neighborsIn G (W.U i.succ) c).image (fun x ↦ s(c,x))).card =
        (neighborsIn G (W.U i.succ) c).card :=
      card_image_of_injective _ (fun _ _ h ↦ Sym2.congr_right.mp h)
    constructor
    · intro _
      simpa only [reserveLinkTestEdges, reserveLinkTestTarget, hcard, mul_assoc] using hb.1
    · simpa only [reserveLinkTestEdges, reserveLinkTestTarget, hcard, mul_assoc] using hb.2
  · have hw := htyp.ambientLinkDegree_real_window hxi1 i hki hj.2.2.2 hj.1
      (hsub hj.2.2.1) hj.2.1 (by omega)
    have hb := real_scaled_reference_mean_window_of_endpoint_loss
      ((p : ℝ)^2*eta*(W.U i.succ).card)
      ((ambientLinkNeighborsIn c A (W.U i.succ) x).card : ℝ) r xi epsilon
      (by positivity) (by positivity) hepsilon hxi hendpoint hw
    have htarget : (p : ℝ)*eta*((r : ℝ)*p*(W.U i.succ).card) =
        (r : ℝ)*((p : ℝ)^2*eta*(W.U i.succ).card) := by ring
    constructor
    · intro _
      simpa only [reserveLinkTestEdges, reserveLinkTestTarget,
        ambientLinkSpokeEdges_card c A (W.U i.succ) x hj.2.1, htarget] using hb.1
    · simpa only [reserveLinkTestEdges, reserveLinkTestTarget,
        ambientLinkSpokeEdges_card c A (W.U i.succ) x hj.2.1, htarget] using hb.2
  · have hw := htyp.ambientLinkCodegree_real_upper hxi1 i hki hj.2.2.2.1 hj.2.2.2.2.2.1
      hj.2.2.2.2.2.2 hj.1 (hsub hj.2.2.1) (hsub hj.2.2.2.2.1) hh
    have hcoeff := mul_le_mul_of_nonneg_right hxiHalf
      (show 0 ≤ (p : ℝ)^3*eta^2*(W.U i.succ).card by positivity)
    have hupper : ((ambientLinkCommonNeighborsIn c A (W.U i.succ) x y).card : ℝ) ≤
        (1+epsilon/2)*((p : ℝ)^3*eta^2*(W.U i.succ).card) := by nlinarith only [hw, hcoeff]
    have hb := mul_le_mul_of_nonneg_left hupper (show 0 ≤ (r : ℝ) by positivity)
    have htarget : (1+epsilon/2)*(((p : ℝ)*eta)^2*((r : ℝ)*p*(W.U i.succ).card)) =
        (r : ℝ)*((1+epsilon/2)*((p : ℝ)^3*eta^2*(W.U i.succ).card)) := by ring
    constructor
    · intro hf
      cases hf
    · simpa only [reserveLinkTestEdges, reserveLinkTestTarget,
        ambientLinkCommonSpokeEdges_card c A (W.U i.succ) x y hj.2.1, htarget] using hb

theorem IsIterationTypical.reserveLinkReference_failure_probability_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell+1)} {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ} (htyp : IsIterationTypical W k G A p eta xi h)
    (htri : ConsistsOfTriangles G A) (hp : p ≤ 1) (heta : eta ≤ 1)
    (hxi1 : xi ≤ 1) (i : Fin ell) (hki : k.val ≤ i.val) (hh : 3 ≤ h)
    (r : ℝ≥0) (hr : r ≤ 1) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hxi : (xi : ℝ) ≤ epsilon/4)
    (hendpoint : 1 ≤ (epsilon/4)*((p : ℝ)^2*eta*(W.U i.succ).card)) :
    ((reserveEdgeLaw G (W.U i.succ) r hr).probability (fun bits ↦
      ¬ ReserveLinkReferenceGood G A (W.U i.castSucc) (W.U i.succ) (reserveEdges G (W.U i.succ) bits)
        ((r : ℝ)*p*(W.U i.succ).card) ((p : ℝ)*eta) epsilon) : ℝ) ≤
      2*((Fintype.card V : ℝ)+(Fintype.card V : ℝ)^2+(Fintype.card V : ℝ)^3)*
        Real.exp (-epsilon^2*((r : ℝ)*(p : ℝ)^3*eta^2*(W.U i.succ).card)/32) := by
  have hpR : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  have hetaR : (eta : ℝ) ≤ 1 := by exact_mod_cast heta
  have hrho : (p : ℝ)*eta ≤ 1 := by
    calc
      _ ≤ (p : ℝ)*1 := mul_le_mul_of_nonneg_left hetaR (by positivity)
      _ ≤ 1 := by simpa only [mul_one] using hpR
  have hb := reserveEdgeLaw_probability_not_reserveLinkReferenceGood G A (W.U i.castSucc) (W.U i.succ)
    htri r hr ((r : ℝ)*p*(W.U i.succ).card) ((p : ℝ)*eta) epsilon
    (by positivity) (by positivity) hrho hepsilon hepsilon1
    (htyp.reserveLinkReference_means hxi1 i hki hh r epsilon hepsilon hxi hendpoint)
  have htarget : ((p : ℝ)*eta)^2*((r : ℝ)*p*(W.U i.succ).card) =
      (r : ℝ)*(p : ℝ)^3*eta^2*(W.U i.succ).card := by ring
  simpa only [htarget] using hb

end

end Erdos207
