/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceInternalReserveSupply
import ErdosProblems.Erdos207.SourceReserveReferenceMeans
import ErdosProblems.Erdos207.FiniteFailureCombination
import ErdosProblems.Erdos207.FiniteJointBind

/-! # The common reserve event, with the prior bad mass retained -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

def SourceReserveGood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A : TripleSystemOn V) (current U : Finset V)
    (p eta r : ℝ≥0) (epsilon : ℝ) (supply : ℕ) (bits : Sym2 V → Bool) : Prop :=
  InternalReserveSupplyGood G A U supply bits ∧
    ReserveLinkReferenceGood G A current U (reserveEdges G U bits)
      ((r : ℝ) * p * U.card) ((p : ℝ) * eta) epsilon

def sourceReserveFailureBound (N u : ℕ) (p eta r : ℝ≥0) (epsilon : ℝ) : ℝ≥0 :=
  (N : ℝ≥0) ^ 2 * (Real.exp (-(r : ℝ) ^ 2 * (p : ℝ) ^ 2 * eta * u / 8)).toNNReal +
    2 * ((N : ℝ≥0) + (N : ℝ≥0) ^ 2 + (N : ℝ≥0) ^ 3) *
      (Real.exp (-epsilon ^ 2 * ((r : ℝ) * (p : ℝ) ^ 3 * eta ^ 2 * u) / 32)).toNNReal

theorem IsIterationTypical.sourceReserveGood_failure_probability_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {stage : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V} {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (htri : ConsistsOfTriangles G A) (hp : p ≤ 1) (heta : eta ≤ 1)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V)) (hh : 3 ≤ h)
    (r : ℝ≥0) (hr : r ≤ 1) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (hxi : (xi : ℝ) ≤ epsilon / 4)
    (hendpoint : 1 ≤ (epsilon / 4) * ((p : ℝ) ^ 2 * eta * (W.U i.succ).card))
    (supply : ℕ) (hsupply : (supply : ℝ) ≤ (r : ℝ) ^ 2 * (p : ℝ) ^ 2 * eta * (W.U i.succ).card / 8) :
    (reserveEdgeLaw G (W.U i.succ) r hr).probability (fun bits ↦
      ¬ SourceReserveGood G A (W.U i.castSucc) (W.U i.succ) p eta r epsilon supply bits) ≤
        sourceReserveFailureBound (Fintype.card V) (W.U i.succ).card p eta r epsilon := by
  have hxiHalf : (xi : ℝ) ≤ 1 / 2 := by linarith only [hxi, hepsilon1]
  have hxi1 : xi ≤ 1 := by exact_mod_cast (show (xi : ℝ) ≤ 1 by linarith only [hxiHalf])
  have hi := htyp.internalReserveSupply_failure_probability_le htri hxiHalf i hstage
    hGsupp (by omega) r hr supply hsupply
  have hl := htyp.reserveLinkReference_failure_probability_le htri hp heta hxi1 i hstage hh
    r hr epsilon hepsilon hepsilon1 hxi hendpoint
  have hb := finiteLaw_failure_and_le (reserveEdgeLaw G (W.U i.succ) r hr) _ _ _ _ hi hl
  apply NNReal.coe_le_coe.mp
  simpa only [SourceReserveGood, sourceReserveFailureBound, NNReal.coe_add, NNReal.coe_mul,
    NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_ofNat,
    Real.coe_toNNReal _ (Real.exp_pos _).le] using hb

theorem FiniteLaw.jointBind_not_good_pair_le
    {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ω] [DecidableEq Ξ]
    (L : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) (Prior : Ω → Prop) (Good : Ω → Ξ → Prop)
    (priorError error : ℝ≥0) (hprior : L.probability (fun omega ↦ ¬ Prior omega) ≤ priorError)
    (hconditional : ∀ omega, 0 < L.mass omega → Prior omega →
      (K omega).probability (fun sample ↦ ¬ Good omega sample) ≤ error) :
    (L.jointBind K).probability (fun z ↦ ¬ (Prior z.1 ∧ Good z.1 z.2)) ≤ priorError + error := by
  let joint := L.jointBind K
  calc
    _ ≤ joint.probability (fun z ↦ ¬ Prior z.1 ∨ (Prior z.1 ∧ ¬ Good z.1 z.2)) := by
      apply joint.probability_mono
      intro z hz
      by_cases hp : Prior z.1
      · exact Or.inr ⟨hp, fun hg ↦ hz ⟨hp, hg⟩⟩
      · exact Or.inl hp
    _ ≤ joint.probability (fun z ↦ ¬ Prior z.1) +
        joint.probability (fun z ↦ Prior z.1 ∧ ¬ Good z.1 z.2) := joint.probability_or_le _ _
    _ ≤ priorError + error * L.probability Prior := by
      apply add_le_add
      · change (L.jointBind K).probability (fun z ↦ ¬ Prior z.1) ≤ priorError
        rw [L.probability_jointBind_fst K (fun omega ↦ ¬ Prior omega)]
        exact hprior
      · exact L.jointBind_probability_and_le_on_support K Prior
          (fun omega sample ↦ ¬ Good omega sample) error hconditional
    _ ≤ priorError + error := add_le_add le_rfl
      (mul_le_of_le_one_right zero_le (L.probability_le_one Prior))

theorem FiniteLaw.jointReserve_sourceGood_failure_le
    {Ω V : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (i : Fin ell)
    (G : Ω → SimpleGraph V) (A : Ω → TripleSystemOn V)
    (p eta xi r : ℝ≥0) (h : ℕ) (epsilon : ℝ) (supply : ℕ)
    (Prior : Ω → Prop) (priorError : ℝ≥0)
    (htyp : ∀ omega, 0 < L.mass omega → Prior omega →
      IsIterationTypical W i.castSucc (G omega) (A omega) p eta xi h)
    (htri : ∀ omega, 0 < L.mass omega → Prior omega → ConsistsOfTriangles (G omega) (A omega))
    (hGsupp : ∀ omega, 0 < L.mass omega → Prior omega →
      GraphSupportedOn (G omega) (W.U i.castSucc : Set V))
    (hp : p ≤ 1) (heta : eta ≤ 1) (hh : 3 ≤ h) (hr : r ≤ 1)
    (hepsilon : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) (hxi : (xi : ℝ) ≤ epsilon / 4)
    (hendpoint : 1 ≤ (epsilon / 4) * ((p : ℝ) ^ 2 * eta * (W.U i.succ).card))
    (hsupply : (supply : ℝ) ≤ (r : ℝ) ^ 2 * (p : ℝ) ^ 2 * eta * (W.U i.succ).card / 8)
    (hprior : L.probability (fun omega ↦ ¬ Prior omega) ≤ priorError) :
    (L.jointBind (fun omega ↦ reserveEdgeLaw (G omega) (W.U i.succ) r hr)).probability
      (fun z ↦ ¬ (Prior z.1 ∧
        SourceReserveGood (G z.1) (A z.1) (W.U i.castSucc) (W.U i.succ) p eta r epsilon supply z.2)) ≤
          priorError + sourceReserveFailureBound (Fintype.card V) (W.U i.succ).card p eta r epsilon := by
  apply L.jointBind_not_good_pair_le (Ξ := Sym2 V → Bool)
    (fun omega ↦ reserveEdgeLaw (G omega) (W.U i.succ) r hr) Prior
    (fun omega bits ↦ SourceReserveGood (G omega) (A omega) (W.U i.castSucc) (W.U i.succ)
      p eta r epsilon supply bits) priorError
    (sourceReserveFailureBound (Fintype.card V) (W.U i.succ).card p eta r epsilon) hprior
  intro omega hmass hg
  exact (htyp omega hmass hg).sourceReserveGood_failure_probability_le
    (htri omega hmass hg) hp heta i le_rfl (hGsupp omega hmass hg) hh
    r hr epsilon hepsilon hepsilon1 hxi hendpoint supply hsupply

end

end Erdos207
