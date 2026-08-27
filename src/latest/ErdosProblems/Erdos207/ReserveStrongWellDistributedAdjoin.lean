/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveStrongWellDistributed

/-!
# Reserve-preserving adjoin updates

An internal-cover kernel has a joint-inclusion estimate conditional on every
already sampled reserve outcome.  Adjoining it therefore preserves arbitrary
future reserve-edge prescriptions without charging those edges a second
time.  This is distinct from the final link kernel, whose selected triangles
themselves force specified reserve spokes.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsReserveStronglyWellDistributed.jointBind_adjoin_preserve_le
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
    (hadded : ∀ omega Q,
      (K omega).probability (fun xi ↦ Q ⊆ added omega xi) ≤ addedBound Q)
    (Ifix Dfix : TripleSystemOn V) (Efix Rfix : Finset (Sym2 V))
    (hdisj : Disjoint Ifix Dfix) :
    (L.jointBind K).probability
        (ReserveStrongDistributionEvent (jointInitial initial)
          (jointLater later added) (fun z ↦ reserve z.1)
          Ifix Dfix Efix Rfix) ≤
      ∑ S ∈ Dfix.powerset,
        addedBound (Dfix \ S) *
          (C ^ (Ifix.card + S.card + Efix.card + Rfix.card) *
            (p ^ Efix.card * reserveDensity ^ Rfix.card *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                laterTriangleScale W k p S + b)) := by
  classical
  let Event : TripleSystemOn V → (Omega × Xi) → Prop := fun S z ↦
    ReserveStrongDistributionEvent initial later reserve
      Ifix S Efix Rfix z.1 ∧ Dfix \ S ⊆ added z.1 z.2
  calc
    (L.jointBind K).probability
        (ReserveStrongDistributionEvent (jointInitial initial)
          (jointLater later added) (fun z ↦ reserve z.1)
          Ifix Dfix Efix Rfix) ≤
        (L.jointBind K).probability
          (fun z ↦ ∃ S ∈ Dfix.powerset, Event S z) := by
      apply FiniteLaw.probability_mono
      intro z hz
      obtain ⟨S, hSpow, hOld, hNew⟩ :=
        strongDistributionEvent_jointLater_partition initial later added
          Ifix Dfix Efix z hz.1
      exact ⟨S, hSpow, ⟨hOld, hz.2⟩, hNew⟩
    _ ≤ ∑ S ∈ Dfix.powerset, (L.jointBind K).probability (Event S) :=
      (L.jointBind K).probability_exists_le Dfix.powerset Event
    _ ≤ ∑ S ∈ Dfix.powerset,
        addedBound (Dfix \ S) *
          (C ^ (Ifix.card + S.card + Efix.card + Rfix.card) *
            (p ^ Efix.card * reserveDensity ^ Rfix.card *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                laterTriangleScale W k p S + b)) := by
      apply sum_le_sum
      intro S hS
      apply (L.jointBind_probability_and_le K
        (ReserveStrongDistributionEvent initial later reserve
          Ifix S Efix Rfix)
        (fun omega xi ↦ Dfix \ S ⊆ added omega xi)
        (addedBound (Dfix \ S))
        (fun omega _hOld ↦ hadded omega (Dfix \ S))).trans
      gcongr
      exact hstrong Ifix S Efix Rfix
        (Disjoint.mono_right (mem_powerset.mp hS) hdisj)

/-- Factor-absorption form retaining the sampled reserve in the output. -/
theorem IsReserveStronglyWellDistributed.jointBind_adjoin_preserve
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
    (hadded : ∀ omega Q,
      (K omega).probability (fun xi ↦ Q ⊆ added omega xi) ≤ addedBound Q)
    (hpartition : ∀ (Ifix Dfix : TripleSystemOn V)
      (Efix Rfix : Finset (Sym2 V)), Disjoint Ifix Dfix →
      ∀ S ∈ Dfix.powerset,
        addedBound (Dfix \ S) *
          (C ^ (Ifix.card + S.card + Efix.card + Rfix.card) *
            (p ^ Efix.card * reserveDensity ^ Rfix.card *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                laterTriangleScale W k p S + b)) ≤
          C' ^ (Ifix.card + Dfix.card + Efix.card + Rfix.card) *
            (p' ^ Efix.card * reserveDensity ^ Rfix.card *
                (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                laterTriangleScale W next p' Dfix + b')) :
    IsReserveStronglyWellDistributed (L.jointBind K) W next
      (jointInitial initial) (jointLater later added) (fun z ↦ reserve z.1)
      p' reserveDensity (2 * C') b' := by
  intro Ifix Dfix Efix Rfix hdisj
  have hraw := hstrong.jointBind_adjoin_preserve_le added addedBound hadded
    Ifix Dfix Efix Rfix hdisj
  let m := Ifix.card + Dfix.card + Efix.card + Rfix.card
  let X := p' ^ Efix.card * reserveDensity ^ Rfix.card *
    (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
      laterTriangleScale W next p' Dfix + b'
  calc
    (L.jointBind K).probability
        (ReserveStrongDistributionEvent (jointInitial initial)
          (jointLater later added) (fun z ↦ reserve z.1)
          Ifix Dfix Efix Rfix) ≤
        ∑ S ∈ Dfix.powerset,
          addedBound (Dfix \ S) *
            (C ^ (Ifix.card + S.card + Efix.card + Rfix.card) *
              (p ^ Efix.card * reserveDensity ^ Rfix.card *
                  (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
                  laterTriangleScale W k p S + b)) := hraw
    _ ≤ ∑ _S ∈ Dfix.powerset, C' ^ m * X := by
      apply sum_le_sum
      intro S hS
      simpa only [m, X] using hpartition Ifix Dfix Efix Rfix hdisj S hS
    _ = (2 : ℝ≥0) ^ Dfix.card * (C' ^ m * X) := by simp
    _ ≤ (2 : ℝ≥0) ^ m * (C' ^ m * X) := by
      gcongr
      · norm_num
      · dsimp only [m]
        omega
    _ = (2 * C') ^
          (Ifix.card + Dfix.card + Efix.card + Rfix.card) *
        (p' ^ Efix.card * reserveDensity ^ Rfix.card *
          (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
          laterTriangleScale W next p' Dfix + b') := by
      rw [mul_pow]
      dsimp only [m, X]
      ring

end

end Erdos207
