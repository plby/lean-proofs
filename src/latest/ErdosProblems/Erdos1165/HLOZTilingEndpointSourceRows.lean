/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZMeshCandidatePolynomialNumerics
import ErdosProblems.Erdos1165.HLOZPrefixedProp49CandidateWindowRatio
import ErdosProblems.Erdos1165.HLOZSourceEndpointTransportTable

/-!
# Finite normalized endpoint-source rows for each tiling

Column tilings have the four orientation/endpoint-class rows.  A checker
opposite row must additionally remember the physical first direction deleted
by one-step recentering, so checker tilings have two canonical-orientation
rows and four fixed-direction opposite rows.  Six is therefore a uniform
row-count bound across all tilings.
-/

open scoped ENNReal

namespace Erdos1165.HLOZTilingEndpointSourceRows

open HLOZMeshCandidatePolynomialNumerics
open HLOZPathEvents
open HLOZPrefixedProp49CandidateWindowRatio
open HLOZSourceEndpointTransportTable
open LazyDecomposition ScreeningInstantiation

noncomputable section

abbrev DominoTiling := Tilings.Tiling

local instance orientationFintype : Fintype Orientation where
  elems := { .even, .shifted }
  complete := by intro o; cases o <;> simp

local instance endpointClassFintype : Fintype DominantEndpointClass where
  elems := { .canonical, .opposite }
  complete := by intro cls; cases cls <;> simp

/-- Physical normalized rows.  The right checker summand stores the deleted
first direction; column rows need only orientation and endpoint class. -/
abbrev TilingEndpointSourceRow (t : DominoTiling) : Type :=
  match t with
  | .checker _ => Orientation ⊕ Direction
  | .evenColumns | .oddColumns => Orientation × DominantEndpointClass

noncomputable instance (t : DominoTiling) :
    Fintype (TilingEndpointSourceRow t) := by
  cases t <;> infer_instance

noncomputable instance (t : DominoTiling) :
    Countable (TilingEndpointSourceRow t) := by infer_instance

def orientation (t : DominoTiling) :
    TilingEndpointSourceRow t → Orientation := by
  cases t with
  | checker _ =>
      intro row
      exact row.elim id (fun _ ↦ .shifted)
  | evenColumns | oddColumns => exact Prod.fst

def endpointClass (t : DominoTiling) :
    TilingEndpointSourceRow t → DominantEndpointClass := by
  cases t with
  | checker _ =>
      intro row
      exact row.elim (fun _ ↦ .canonical) (fun _ ↦ .opposite)
  | evenColumns | oddColumns => exact Prod.snd

/-- Only checker-opposite rows carry a physical first direction. -/
def physicalFirstDirection (t : DominoTiling) :
    TilingEndpointSourceRow t → Option Direction := by
  cases t with
  | checker _ =>
      intro row
      exact row.elim (fun _ ↦ none) some
  | evenColumns | oddColumns => exact fun _ ↦ none

theorem card_le_six (t : DominoTiling) :
    Fintype.card (TilingEndpointSourceRow t) ≤ 6 := by
  have ho : Fintype.card Orientation = 2 := by decide
  have hc : Fintype.card DominantEndpointClass = 2 := by decide
  cases t <;> simp [TilingEndpointSourceRow, ho, hc]

/-- The sum of identical row ratios is controlled by the common six-row
polynomial envelope. -/
theorem sum_candidateRatio_le_six (t : DominoTiling) (m : ℕ)
    (a : GapScale) :
    ∑ _row : TilingEndpointSourceRow t,
        prop49CandidateRatioEnvelope prop49WindowRatioConstant m a ≤
      prop49CandidateRatioEnvelope (6 * prop49WindowRatioConstant) m a := by
  simp only [Finset.sum_const, Finset.card_univ]
  rw [prop49CandidateRatioEnvelope, prop49CandidateRatioEnvelope]
  rw [← ENNReal.ofReal_nsmul]
  have hcardReal : (Fintype.card (TilingEndpointSourceRow t) : ℝ) ≤ 6 := by
    exact_mod_cast card_le_six t
  have hnonneg : 0 ≤ prop49WindowRatioConstant *
      (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne) :=
    mul_nonneg prop49WindowRatioConstant_pos.le
      (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  apply ENNReal.ofReal_le_ofReal
  simp only [nsmul_eq_mul]
  calc
    (Fintype.card (TilingEndpointSourceRow t) : ℝ) *
          (prop49WindowRatioConstant *
            (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne)) ≤
        6 * (prop49WindowRatioConstant *
          (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne)) :=
      mul_le_mul_of_nonneg_right hcardReal hnonneg
    _ = 6 * prop49WindowRatioConstant *
        (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne) := by ring

end

end Erdos1165.HLOZTilingEndpointSourceRows
