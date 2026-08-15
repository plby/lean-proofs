/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.FiniteWeylInequality
import ErdosProblems.Erdos387.IteratedReciprocalCompletion

/-!
# Closing finite Weyl differencing with interval completion

This file iterates the one-step positive-shift inequality.  At the chosen
bottom depth it inserts the completed short rational-phase estimate proved in
`IteratedReciprocalCompletion`.
-/

namespace Erdos387

open scoped BigOperators

namespace IteratedWeylBound

/-- Recursive real envelope for `r` remaining Weyl differences. -/
noncomputable def envelope (P : ℕ) : ℕ → ℝ → ℝ
  | 0, B => B
  | r + 1, B => Real.sqrt ((P : ℝ) + 2 * P * envelope P r B)

theorem envelope_nonneg {P r : ℕ} {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ envelope P r B := by
  induction r with
  | zero => simpa [envelope] using hB
  | succ r ih => exact Real.sqrt_nonneg _

/-- Bottom estimate at total differencing depth `J`. -/
noncomputable def bottomBound (p J : ℕ) : ℝ :=
  (Real.log p + 1) * IteratedReciprocalCompletion.completeBound p J

theorem bottomBound_nonneg {p J : ℕ} (hp : 1 < p) :
    0 ≤ bottomBound p J := by
  apply mul_nonneg
  · have : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hp.le)
    positivity
  · exact IteratedReciprocalCompletion.completeBound_nonneg p J

/-- An iterated reciprocal sum of any length at most `P` is bounded by the
recursive Weyl envelope, provided `r` more differences reach total depth
`J`. -/
theorem norm_sum_iteratedInversePhase_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (hp : 1 < p) {c a : ZMod p} (hc : c ≠ 0)
    {P Q J r : ℕ} (hQ : Q ≤ P) (hP : P < p)
    (hs : List ℕ) (hlen : hs.length + r = J)
    (hshift : ∀ h ∈ hs, h + 1 < p)
    (hpow : IteratedReciprocalCompletion.poleEnvelope J < p) :
    ‖∑ x ∈ Finset.range Q,
        ZMod.stdAddChar
          (InverseWeyl.iteratedInversePhase p c a hs x)‖ ≤
      envelope P r (bottomBound p J) := by
  induction r generalizing hs Q with
  | zero =>
      have hlength : hs.length = J := by omega
      have hpowHs : IteratedReciprocalCompletion.poleEnvelope hs.length < p := by
        simpa [hlength] using hpow
      have hsum :
          (∑ x ∈ Finset.range Q,
              ZMod.stdAddChar
                (InverseWeyl.iteratedInversePhase p c a hs x)) =
            ∑ x ∈ Finset.range Q,
              ZMod.stdAddChar
                (IteratedReciprocalCompletion.phase p c a hs
                  (x : ZMod p)) := by
        apply Finset.sum_congr rfl
        intro x _hx
        rw [IteratedReciprocalCompletion.phase,
          InverseRational.zmodIteratedInversePhase_natCast]
      rw [hsum,
        ReciprocalIntervalCompletion.sum_range_eq_shortPhase_neg_one]
      simpa only [envelope, bottomBound, hlength] using
        (IteratedReciprocalCompletion.norm_shortPhase_le
          (a := a) hp hc hs hshift hpowHs (-1) Q (hQ.trans hP.le))
  | succ r ih =>
      have hcore := FiniteWeyl.norm_sum_iteratedInversePhase_sq_le
        p c a hs Q
      let E := envelope P r (bottomBound p J)
      have hE : 0 ≤ E := envelope_nonneg (bottomBound_nonneg hp)
      have hterm (h : ℕ) (hh : h ∈ Finset.range Q) :
          ‖∑ y ∈ Finset.range (Q - h - 1),
              ZMod.stdAddChar
                (InverseWeyl.iteratedInversePhase p c a (h :: hs) y)‖ ≤
            E := by
        apply ih (Q := Q - h - 1) (hs := h :: hs)
        · exact (Nat.sub_le Q (h + 1)).trans hQ
        · simp only [List.length_cons]
          omega
        · have hhQ : h < Q := Finset.mem_range.mp hh
          simp only [List.mem_cons]
          intro t ht
          rcases ht with rfl | ht
          · omega
          · exact hshift t ht
      have hsumBound :
          (∑ h ∈ Finset.range Q,
            ‖∑ y ∈ Finset.range (Q - h - 1),
              ZMod.stdAddChar
                (InverseWeyl.iteratedInversePhase p c a (h :: hs) y)‖) ≤
            (Q : ℝ) * E := by
        calc
          (∑ h ∈ Finset.range Q,
            ‖∑ y ∈ Finset.range (Q - h - 1),
              ZMod.stdAddChar
                (InverseWeyl.iteratedInversePhase p c a (h :: hs) y)‖) ≤
              ∑ _h ∈ Finset.range Q, E := by
            exact Finset.sum_le_sum fun h hh => hterm h hh
          _ = (Q : ℝ) * E := by simp
      have hsq :
          ‖∑ x ∈ Finset.range Q,
              ZMod.stdAddChar
                (InverseWeyl.iteratedInversePhase p c a hs x)‖ ^ 2 ≤
            (P : ℝ) + 2 * P * E := by
        calc
          ‖∑ x ∈ Finset.range Q,
              ZMod.stdAddChar
                (InverseWeyl.iteratedInversePhase p c a hs x)‖ ^ 2 ≤
              (Q : ℝ) + 2 *
                ∑ h ∈ Finset.range Q,
                  ‖∑ y ∈ Finset.range (Q - h - 1),
                    ZMod.stdAddChar
                      (InverseWeyl.iteratedInversePhase p c a (h :: hs) y)‖ :=
            hcore
          _ ≤ (Q : ℝ) + 2 * ((Q : ℝ) * E) := by gcongr
          _ ≤ (P : ℝ) + 2 * P * E := by
            have hQR : (Q : ℝ) ≤ P := by exact_mod_cast hQ
            nlinarith
      have hrad : 0 ≤ (P : ℝ) + 2 * P * E := by positivity
      have hsqrt : (envelope P (r + 1) (bottomBound p J)) ^ 2 =
          (P : ℝ) + 2 * P * E := by
        rw [envelope, Real.sq_sqrt hrad]
      have henv : 0 ≤ envelope P (r + 1) (bottomBound p J) :=
        envelope_nonneg (bottomBound_nonneg hp)
      nlinarith [norm_nonneg
        (∑ x ∈ Finset.range Q,
          ZMod.stdAddChar
            (InverseWeyl.iteratedInversePhase p c a hs x))]

/-- Source-facing specialization starting before any differences. -/
theorem norm_sum_inversePhase_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (hp : 1 < p) {c a : ZMod p} (hc : c ≠ 0)
    {P J : ℕ} (hP : P < p)
    (hpow : IteratedReciprocalCompletion.poleEnvelope J < p) :
    ‖∑ x ∈ Finset.range P,
        InverseWeyl.inversePhaseSequence p c a x‖ ≤
      envelope P J (bottomBound p J) := by
  simpa only [InverseWeyl.inversePhaseSequence,
    InverseWeyl.iteratedInversePhase] using
    (norm_sum_iteratedInversePhase_le hp hc le_rfl hP []
      (by simp) (by simp) hpow)

end IteratedWeylBound

end Erdos387
