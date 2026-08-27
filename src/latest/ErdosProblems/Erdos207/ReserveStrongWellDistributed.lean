/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.StrongWellDistributedAdjoin
import ErdosProblems.Erdos207.ReserveEdgeSampling
import ErdosProblems.Erdos207.FiniteConditioning

/-!
# Strong well-distributedness with prescribed reserve edges

The final link matching is not bounded sharply enough by its sparsification
density alone.  Every selected matching triangle also requires two crossing
edges retained by the earlier reserve sample.  This file records the exact
strengthening of strong well-distributedness that retains those independent
reserve-edge factors, proves it for a freshly sampled reserve, and gives the
powerset adjoin theorem for a later family whose members force prescribed
reserve edges.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Strong-distribution event together with inclusion of fixed reserve
edges. -/
def ReserveStrongDistributionEvent
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    (initial later : Omega → TripleSystemOn V)
    (reserve : Omega → Finset (Sym2 V))
    (Ifix Dfix : TripleSystemOn V)
    (Efix Rfix : Finset (Sym2 V)) (omega : Omega) : Prop :=
  StrongDistributionEvent initial later Ifix Dfix Efix omega ∧
    Rfix ⊆ reserve omega

/-- Strong well-distributedness retaining the product probability of every
prescribed reserve edge. -/
def IsReserveStronglyWellDistributed
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : ℕ} (L : FiniteLaw Omega) (W : Vortex V ell)
    (k : Fin (ell + 1))
    (initial later : Omega → TripleSystemOn V)
    (reserve : Omega → Finset (Sym2 V))
    (p reserveDensity C b : ℝ≥0) : Prop :=
  ∀ (Ifix Dfix : TripleSystemOn V) (Efix Rfix : Finset (Sym2 V)),
    Disjoint Ifix Dfix →
    L.probability (ReserveStrongDistributionEvent initial later reserve
      Ifix Dfix Efix Rfix) ≤
      C ^ (Ifix.card + Dfix.card + Efix.card + Rfix.card) *
        (p ^ Efix.card * reserveDensity ^ Rfix.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
            laterTriangleScale W k p Dfix + b)

/-- With additive error one, reserve-aware strong distribution is automatic.
This coarse endpoint is useful at a terminal stage, where the law is no
longer propagated to another vortex level. -/
theorem reserveStronglyWellDistributed_one
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : ℕ} (L : FiniteLaw Omega) (W : Vortex V ell)
    (k : Fin (ell + 1))
    (initial later : Omega → TripleSystemOn V)
    (reserve : Omega → Finset (Sym2 V)) (p reserveDensity : ℝ≥0) :
    IsReserveStronglyWellDistributed L W k initial later reserve
      p reserveDensity 1 1 := by
  intro Ifix Dfix Efix Rfix _hdisjoint
  calc
    L.probability (ReserveStrongDistributionEvent initial later reserve
        Ifix Dfix Efix Rfix) ≤ 1 := L.probability_le_one _
    _ ≤ 1 ^ (Ifix.card + Dfix.card + Efix.card + Rfix.card) *
        (p ^ Efix.card * reserveDensity ^ Rfix.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
            laterTriangleScale W k p Dfix + 1) := by simp

/-- Enlarging the multiplicative constant preserves reserve-aware strong
well-distributedness. -/
theorem IsReserveStronglyWellDistributed.mono_factor
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : ℕ} {L : FiniteLaw Omega} {W : Vortex V ell}
    {k : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {p reserveDensity C C' b : ℝ≥0}
    (h : IsReserveStronglyWellDistributed L W k initial later reserve
      p reserveDensity C b)
    (hCC' : C ≤ C') :
    IsReserveStronglyWellDistributed L W k initial later reserve
      p reserveDensity C' b := by
  intro Ifix Dfix Efix Rfix hdisj
  exact (h Ifix Dfix Efix Rfix hdisj).trans (by gcongr)

/-- Enlarging the additive error preserves reserve-aware strong
well-distributedness. -/
theorem IsReserveStronglyWellDistributed.mono_additiveError
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : ℕ} {L : FiniteLaw Omega} {W : Vortex V ell}
    {k : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {p reserveDensity C b b' : ℝ≥0}
    (h : IsReserveStronglyWellDistributed L W k initial later reserve
      p reserveDensity C b)
    (hbb' : b ≤ b') :
    IsReserveStronglyWellDistributed L W k initial later reserve
      p reserveDensity C b' := by
  intro Ifix Dfix Efix Rfix hdisj
  exact (h Ifix Dfix Efix Rfix hdisj).trans (by gcongr)

/-- Forgetting the reserve prescription recovers ordinary strong
well-distributedness. -/
theorem IsReserveStronglyWellDistributed.toStrong
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : ℕ} {L : FiniteLaw Omega} {W : Vortex V ell}
    {k : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {p reserveDensity C b : ℝ≥0}
    (h : IsReserveStronglyWellDistributed L W k initial later reserve
      p reserveDensity C b) :
    IsStronglyWellDistributed L W k initial later p C b := by
  intro Ifix Dfix Efix hdisj
  have hraw := h Ifix Dfix Efix ∅ hdisj
  have hevent : ReserveStrongDistributionEvent initial later reserve
      Ifix Dfix Efix ∅ =
      StrongDistributionEvent initial later Ifix Dfix Efix := by
    funext omega
    simp [ReserveStrongDistributionEvent]
  rw [hevent] at hraw
  simpa using hraw

/-- Conditioning on a positive event preserves the reserve-aware estimate,
with the same reciprocal loss in the multiplicative constant as for ordinary
strong well-distributedness. -/
theorem IsReserveStronglyWellDistributed.conditionOn
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V]
    {ell : ℕ} {L : FiniteLaw Omega} {W : Vortex V ell}
    {k : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {p reserveDensity C b : ℝ≥0}
    (h : IsReserveStronglyWellDistributed L W k initial later reserve
      p reserveDensity C b)
    (P : Omega → Prop) (hP : 0 < L.probability P) :
    IsReserveStronglyWellDistributed (L.conditionOn P hP) W k
      initial later reserve p reserveDensity (C / L.probability P) b := by
  intro Ifix Dfix Efix Rfix hdisj
  let m := Ifix.card + Dfix.card + Efix.card + Rfix.card
  let X := p ^ Efix.card * reserveDensity ^ Rfix.card *
    (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
    laterTriangleScale W k p Dfix + b
  by_cases hm : m = 0
  · have hI : Ifix = ∅ := card_eq_zero.mp (by dsimp only [m] at hm; omega)
    have hD : Dfix = ∅ := card_eq_zero.mp (by dsimp only [m] at hm; omega)
    have hE : Efix = ∅ := card_eq_zero.mp (by dsimp only [m] at hm; omega)
    have hR : Rfix = ∅ := card_eq_zero.mp (by dsimp only [m] at hm; omega)
    subst Ifix
    subst Dfix
    subst Efix
    subst Rfix
    exact ((L.conditionOn P hP).probability_le_one
      (ReserveStrongDistributionEvent initial later reserve ∅ ∅ ∅ ∅)).trans
        (by simp [ReserveStrongDistributionEvent, StrongDistributionEvent])
  · have hzle : L.probability P ≤ 1 := L.probability_le_one P
    have hzpow : (L.probability P) ^ m ≤ L.probability P :=
      pow_le_of_le_one zero_le hzle hm
    have hscale : C ^ m / L.probability P ≤
        (C / L.probability P) ^ m := by
      rw [div_pow]
      gcongr
    have horiginal := h Ifix Dfix Efix Rfix hdisj
    calc
      (L.conditionOn P hP).probability
          (ReserveStrongDistributionEvent initial later reserve
            Ifix Dfix Efix Rfix) ≤
        L.probability
            (ReserveStrongDistributionEvent initial later reserve
              Ifix Dfix Efix Rfix) / L.probability P :=
        L.conditionOn_probability_le P
          (ReserveStrongDistributionEvent initial later reserve
            Ifix Dfix Efix Rfix) hP
      _ ≤ (C ^ m * X) / L.probability P := by
        gcongr
      _ = (C ^ m / L.probability P) * X := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ (C / L.probability P) ^ m * X := by
        gcongr
      _ = (C / L.probability P) ^
            (Ifix.card + Dfix.card + Efix.card + Rfix.card) *
          (p ^ Efix.card * reserveDensity ^ Rfix.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
            laterTriangleScale W k p Dfix + b) := by
        rfl

/-- Independently adjoining the reserve-edge sample upgrades ordinary strong
well-distributedness to its reserve-aware form. -/
theorem IsStronglyWellDistributed.jointBind_reserveEdges
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {G : Omega → SimpleGraph V} {U : Finset V}
    {p C b r : ℝ≥0}
    (hstrong : IsStronglyWellDistributed L W k initial later p C b)
    (hC : 1 ≤ C) (hr : r ≤ 1) :
    IsReserveStronglyWellDistributed
      (L.jointBind fun omega ↦ reserveEdgeLaw (G omega) U r hr)
      W k (fun z ↦ initial z.1) (fun z ↦ later z.1)
      (fun z ↦ reserveEdges (G z.1) U z.2) p r C b := by
  intro Ifix Dfix Efix Rfix hdisj
  let K : Omega → FiniteLaw (Sym2 V → Bool) :=
    fun omega ↦ reserveEdgeLaw (G omega) U r hr
  let Old : Omega → Prop :=
    StrongDistributionEvent initial later Ifix Dfix Efix
  let Reserve : Omega → (Sym2 V → Bool) → Prop :=
    fun omega bits ↦ Rfix ⊆ reserveEdges (G omega) U bits
  have hconditional : ∀ omega, Old omega →
      (K omega).probability (Reserve omega) ≤ r ^ Rfix.card := by
    intro omega _hold
    by_cases hcross : Rfix ⊆ crossingEdges (G omega) U
    · exact le_of_eq (reserveEdgeLaw_probability_subset_reserveEdges
        (G omega) U r hr Rfix hcross)
    · have himpossible : ∀ bits, ¬ Reserve omega bits := by
        intro bits hR
        exact hcross (hR.trans
          (reserveEdges_subset_crossingEdges (G omega) U bits))
      have hzero : (K omega).probability (Reserve omega) = 0 := by
        apply le_antisymm
        · calc
            (K omega).probability (Reserve omega) ≤
                (K omega).probability (fun _ ↦ False) := by
              apply FiniteLaw.probability_mono
              intro bits hbits
              exact himpossible bits hbits
            _ = 0 := FiniteLaw.probability_false _
        · exact zero_le
      rw [hzero]
      exact zero_le
  have hjoint :
      (L.jointBind K).probability (fun z ↦ Old z.1 ∧ Reserve z.1 z.2) ≤
        r ^ Rfix.card * L.probability Old :=
    L.jointBind_probability_and_le K Old Reserve (r ^ Rfix.card)
      hconditional
  have hold := hstrong Ifix Dfix Efix hdisj
  have hpowC : C ^ (Ifix.card + Dfix.card + Efix.card) ≤
      C ^ (Ifix.card + Dfix.card + Efix.card + Rfix.card) := by
    exact pow_le_pow_right₀ hC (by omega)
  have hrpow : r ^ Rfix.card ≤ 1 := pow_le_one₀ (by positivity) hr
  calc
    (L.jointBind fun omega ↦ reserveEdgeLaw (G omega) U r hr).probability
        (ReserveStrongDistributionEvent
          (fun z ↦ initial z.1) (fun z ↦ later z.1)
          (fun z ↦ reserveEdges (G z.1) U z.2)
          Ifix Dfix Efix Rfix) =
        (L.jointBind K).probability
          (fun z ↦ Old z.1 ∧ Reserve z.1 z.2) := by rfl
    _ ≤ r ^ Rfix.card * L.probability Old := hjoint
    _ ≤ r ^ Rfix.card *
        (C ^ (Ifix.card + Dfix.card + Efix.card) *
          (p ^ Efix.card *
              (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
              laterTriangleScale W k p Dfix + b)) := by gcongr
    _ ≤ C ^ (Ifix.card + Dfix.card + Efix.card + Rfix.card) *
        (p ^ Efix.card * r ^ Rfix.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
            laterTriangleScale W k p Dfix + b) := by
      calc
        r ^ Rfix.card *
            (C ^ (Ifix.card + Dfix.card + Efix.card) *
              (p ^ Efix.card *
                  (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                  laterTriangleScale W k p Dfix + b)) =
            C ^ (Ifix.card + Dfix.card + Efix.card) *
              (p ^ Efix.card * r ^ Rfix.card *
                  (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                  laterTriangleScale W k p Dfix + r ^ Rfix.card * b) := by
          ring
        _ ≤ C ^ (Ifix.card + Dfix.card + Efix.card) *
              (p ^ Efix.card * r ^ Rfix.card *
                  (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                  laterTriangleScale W k p Dfix + b) := by
          gcongr
          exact mul_le_of_le_one_left (by positivity) hrpow
        _ ≤ C ^
              (Ifix.card + Dfix.card + Efix.card + Rfix.card) *
              (p ^ Efix.card * r ^ Rfix.card *
                  (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                  laterTriangleScale W k p Dfix + b) := by
          gcongr

/-- Exact powerset estimate when every selected new family forces a
prescribed set of reserve edges in the old outcome. -/
theorem IsReserveStronglyWellDistributed.jointBind_adjoin_le
    {Omega Xi V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype Xi] [DecidableEq Xi] [Fintype V] [DecidableEq V]
    {ell : ℕ} {L : FiniteLaw Omega} {K : Omega → FiniteLaw Xi}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {p reserveDensity C b : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed L W k initial later reserve
      p reserveDensity C b)
    (added : Omega → Xi → TripleSystemOn V)
    (addedBound : TripleSystemOn V → ℝ≥0)
    (required : TripleSystemOn V → Finset (Sym2 V))
    (hadded : ∀ omega Q,
      (K omega).probability (fun xi ↦ Q ⊆ added omega xi) ≤
        addedBound Q)
    (hrequired : ∀ omega xi Q, 0 < (K omega).mass xi →
      Q ⊆ added omega xi → required Q ⊆ reserve omega)
    (Ifix Dfix : TripleSystemOn V) (Efix : Finset (Sym2 V))
    (hdisj : Disjoint Ifix Dfix) :
    (L.jointBind K).probability
        (StrongDistributionEvent (jointInitial initial)
          (jointLater later added) Ifix Dfix Efix) ≤
      ∑ S ∈ Dfix.powerset,
        addedBound (Dfix \ S) *
          (C ^ (Ifix.card + S.card + Efix.card +
              (required (Dfix \ S)).card) *
            (p ^ Efix.card *
                reserveDensity ^ (required (Dfix \ S)).card *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                laterTriangleScale W k p S + b)) := by
  classical
  let Event : TripleSystemOn V → (Omega × Xi) → Prop :=
    fun S z ↦
      ReserveStrongDistributionEvent initial later reserve Ifix S Efix
        (required (Dfix \ S)) z.1 ∧
      Dfix \ S ⊆ added z.1 z.2
  have hsupport : (L.jointBind K).SupportedOn
      (fun z ↦ 0 < (K z.1).mass z.2) := by
    have hL : L.SupportedOn (fun _omega ↦ True) := fun _omega _hmass ↦ trivial
    have hK : ∀ omega, True → (K omega).SupportedOn
        (fun xi ↦ 0 < (K omega).mass xi) := by
      intro omega _ xi hxi
      exact hxi
    have hjoint := hL.jointBind hK
    intro z hz
    exact (hjoint z hz).2
  calc
    (L.jointBind K).probability
        (StrongDistributionEvent (jointInitial initial)
          (jointLater later added) Ifix Dfix Efix) ≤
        (L.jointBind K).probability
          (fun z ↦ ∃ S ∈ Dfix.powerset, Event S z) := by
      apply FiniteLaw.probability_mono_of_supported _ hsupport
      intro z hzsupport hz
      obtain ⟨S, hSpow, hOld, hNew⟩ :=
        strongDistributionEvent_jointLater_partition initial later added
          Ifix Dfix Efix z hz
      refine ⟨S, hSpow, ?_, hNew⟩
      exact ⟨hOld, hrequired z.1 z.2 (Dfix \ S) hzsupport hNew⟩
    _ ≤ ∑ S ∈ Dfix.powerset,
        (L.jointBind K).probability (Event S) :=
      (L.jointBind K).probability_exists_le Dfix.powerset Event
    _ ≤ ∑ S ∈ Dfix.powerset,
        addedBound (Dfix \ S) *
          (C ^ (Ifix.card + S.card + Efix.card +
              (required (Dfix \ S)).card) *
            (p ^ Efix.card *
                reserveDensity ^ (required (Dfix \ S)).card *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                laterTriangleScale W k p S + b)) := by
      apply sum_le_sum
      intro S hS
      apply (L.jointBind_probability_and_le K
        (ReserveStrongDistributionEvent initial later reserve Ifix S Efix
          (required (Dfix \ S)))
        (fun omega xi ↦ Dfix \ S ⊆ added omega xi)
        (addedBound (Dfix \ S)) (fun omega _hOld ↦
          hadded omega (Dfix \ S))).trans
      gcongr
      exact hstrong Ifix S Efix (required (Dfix \ S))
        (Disjoint.mono_right (mem_powerset.mp hS) hdisj)

/-- Factor-absorption form of the reserve-aware adjoin theorem. -/
theorem IsReserveStronglyWellDistributed.jointBind_adjoin
    {Omega Xi V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype Xi] [DecidableEq Xi] [Fintype V] [DecidableEq V]
    {ell : ℕ} {L : FiniteLaw Omega} {K : Omega → FiniteLaw Xi}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {p reserveDensity C b p' C' b' : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed L W k initial later reserve
      p reserveDensity C b)
    (added : Omega → Xi → TripleSystemOn V)
    (addedBound : TripleSystemOn V → ℝ≥0)
    (required : TripleSystemOn V → Finset (Sym2 V))
    (hadded : ∀ omega Q,
      (K omega).probability (fun xi ↦ Q ⊆ added omega xi) ≤
        addedBound Q)
    (hrequired : ∀ omega xi Q, 0 < (K omega).mass xi →
      Q ⊆ added omega xi → required Q ⊆ reserve omega)
    (hpartition : ∀ (Ifix Dfix : TripleSystemOn V)
      (Efix : Finset (Sym2 V)), Disjoint Ifix Dfix →
      ∀ S ∈ Dfix.powerset,
        addedBound (Dfix \ S) *
          (C ^ (Ifix.card + S.card + Efix.card +
              (required (Dfix \ S)).card) *
            (p ^ Efix.card *
                reserveDensity ^ (required (Dfix \ S)).card *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                laterTriangleScale W k p S + b)) ≤
          C' ^ (Ifix.card + Dfix.card + Efix.card) *
            (p' ^ Efix.card *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                laterTriangleScale W next p' Dfix + b')) :
    IsStronglyWellDistributed (L.jointBind K) W next
      (jointInitial initial) (jointLater later added) p' (2 * C') b' := by
  intro Ifix Dfix Efix hdisj
  have hraw := hstrong.jointBind_adjoin_le added addedBound required
    hadded hrequired Ifix Dfix Efix hdisj
  let m := Ifix.card + Dfix.card + Efix.card
  let X := p' ^ Efix.card *
    (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
      laterTriangleScale W next p' Dfix + b'
  calc
    (L.jointBind K).probability
        (StrongDistributionEvent (jointInitial initial)
          (jointLater later added) Ifix Dfix Efix) ≤
        ∑ S ∈ Dfix.powerset,
          addedBound (Dfix \ S) *
            (C ^ (Ifix.card + S.card + Efix.card +
                (required (Dfix \ S)).card) *
              (p ^ Efix.card *
                  reserveDensity ^ (required (Dfix \ S)).card *
                  (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                  laterTriangleScale W k p S + b)) := hraw
    _ ≤ ∑ _S ∈ Dfix.powerset, C' ^ m * X := by
      apply sum_le_sum
      intro S hS
      simpa only [m, X] using hpartition Ifix Dfix Efix hdisj S hS
    _ = (2 : ℝ≥0) ^ Dfix.card * (C' ^ m * X) := by simp
    _ ≤ (2 : ℝ≥0) ^ m * (C' ^ m * X) := by
      gcongr
      · norm_num
      · dsimp only [m]
        omega
    _ = (2 * C') ^ (Ifix.card + Dfix.card + Efix.card) *
        (p' ^ Efix.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
            laterTriangleScale W next p' Dfix + b') := by
      rw [mul_pow]
      dsimp only [m, X]
      ring

end

end Erdos207
