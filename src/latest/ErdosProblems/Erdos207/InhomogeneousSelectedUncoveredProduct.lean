/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InhomogeneousSelectedUncovered
import ErdosProblems.Erdos207.InhomogeneousWeightedJointInclusion
import ErdosProblems.Erdos207.SupportRestrictedSelectedUncovered

/-!
# Sharp inhomogeneous selected/uncovered products

For a long random-greedy phase neither the insertion hazard nor the survival
hazard may be frozen at its worst value.  The survival probability is the
product of the per-step contractions.  After that common product is factored
out, a prescribed insertion at time `i` costs the adjusted hazard `rho i`,
where `delta i <= theta i ^ |B| * rho i`.

The theorem below is the abstract retrospective estimate needed for initial
sparsification.  It is the time-inhomogeneous analogue of
`selectedUncoveredEnvelope_le_product`, and unlike the older uniform bound it
retains every factor of the survival product.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Product of the survival contractions in the first `t` transitions. -/
def cumulativeSurvival (theta : ℕ -> ℝ≥0) (t : ℕ) : ℝ≥0 :=
  ∏ i ∈ range t, theta i

@[simp]
lemma cumulativeSurvival_zero (theta : ℕ -> ℝ≥0) :
    cumulativeSurvival theta 0 = 1 := by
  simp [cumulativeSurvival]

lemma cumulativeSurvival_succ (theta : ℕ -> ℝ≥0) (t : ℕ) :
    cumulativeSurvival theta (t + 1) =
      cumulativeSurvival theta t * theta t := by
  simp [cumulativeSurvival, prod_range_succ]

/-- Exact mixed product estimate for time-dependent kernels.  The adjusted
point hazard may depend on the prescribed surviving set through the sole
hypothesis `hadjust`; in applications it is the raw insertion hazard divided
by the survival contraction charged at that transition. -/
theorem evolveKernels_probability_selectedUncovered_le_product
    {Omega W Z : Type*} [Fintype Omega] [DecidableEq Omega]
    [DecidableEq W] [DecidableEq Z]
    (K : ℕ -> Omega -> FiniteLaw Omega)
    (R : Omega -> Finset W) (U : Omega -> Finset Z)
    (delta theta rho : ℕ -> ℝ≥0)
    (hsingle : ∀ i, IsMonotoneSingleInsertionKernel (K i) R)
    (hantitone : ∀ i, IsAntitoneSetKernel (K i) U)
    (hsurvive : ∀ i omega B, B ⊆ U omega ->
      (K i omega).probability (fun omega' => B ⊆ U omega') <=
        theta i ^ B.card)
    (hpoint : ∀ i omega x, x ∉ R omega -> ∀ B, B ⊆ U omega ->
      (K i omega).probability (fun omega' =>
        x ∈ R omega' ∧ B ⊆ U omega') <= delta i)
    (omega0 : Omega) (Q : Finset W) (B : Finset Z)
    (hdisjoint : Disjoint Q (R omega0)) (hB0 : B ⊆ U omega0)
    (hadjust : ∀ i, delta i <= theta i ^ B.card * rho i)
    (t : ℕ) :
    (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega0)).probability
        (SelectedUncoveredEvent R U Q B) <=
      cumulativeSurvival theta t ^ B.card *
        setWeight (cumulativePointHazard (fun i _ => rho i) t) Q := by
  classical
  induction t generalizing Q with
  | zero =>
      simp only [FiniteLaw.evolveKernels_zero, FiniteLaw.probability_pure,
        cumulativeSurvival_zero, one_pow, one_mul, cumulativePointHazard,
        range_zero, sum_empty]
      by_cases hQ : Q = ∅
      · subst Q
        simp [SelectedUncoveredEvent, hB0, setWeight]
      · have hnot : ¬ Q ⊆ R omega0 := by
          intro hsub
          obtain ⟨x, hxQ⟩ := nonempty_iff_ne_empty.mpr hQ
          exact disjoint_left.mp hdisjoint hxQ (hsub hxQ)
        have hcard : Q.card ≠ 0 :=
          card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hQ)
        simp [SelectedUncoveredEvent, hnot, setWeight, hcard]
  | succ t ih =>
      rw [FiniteLaw.evolveKernels_succ]
      have hrec := bind_probability_selectedUncovered_le
        (K t) R U (delta t) (theta t) (hsingle t) (hantitone t)
          (hsurvive t) (hpoint t)
          (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega0)) Q B
      let s : ℝ≥0 := cumulativeSurvival theta t ^ B.card
      let pi : W -> ℝ≥0 :=
        cumulativePointHazard (fun i _ => rho i) t
      have hQbound :
          (FiniteLaw.evolveKernels K t
            (FiniteLaw.pure omega0)).probability
              (SelectedUncoveredEvent R U Q B) <= s * setWeight pi Q := by
        simpa only [s, pi] using ih Q hdisjoint
      have herase : ∀ x ∈ Q,
          (FiniteLaw.evolveKernels K t
            (FiniteLaw.pure omega0)).probability
              (SelectedUncoveredEvent R U (Q.erase x) B) <=
            s * setWeight pi (Q.erase x) := by
        intro x hx
        have hd : Disjoint (Q.erase x) (R omega0) :=
          hdisjoint.mono_left (erase_subset x Q)
        simpa only [s, pi] using ih (Q.erase x) hd
      have hfirst :
          theta t ^ B.card *
              (FiniteLaw.evolveKernels K t
                (FiniteLaw.pure omega0)).probability
                  (SelectedUncoveredEvent R U Q B) <=
            (s * theta t ^ B.card) * setWeight pi Q := by
        calc
          theta t ^ B.card *
                (FiniteLaw.evolveKernels K t
                  (FiniteLaw.pure omega0)).probability
                    (SelectedUncoveredEvent R U Q B) <=
              theta t ^ B.card * (s * setWeight pi Q) := by gcongr
          _ = (s * theta t ^ B.card) * setWeight pi Q := by ring
      have hsum :
          delta t * ∑ x ∈ Q,
              (FiniteLaw.evolveKernels K t
                (FiniteLaw.pure omega0)).probability
                  (SelectedUncoveredEvent R U (Q.erase x) B) <=
            (s * theta t ^ B.card) *
              ∑ x ∈ Q, rho t * setWeight pi (Q.erase x) := by
        calc
          delta t * ∑ x ∈ Q,
                (FiniteLaw.evolveKernels K t
                  (FiniteLaw.pure omega0)).probability
                    (SelectedUncoveredEvent R U (Q.erase x) B) <=
              delta t * ∑ x ∈ Q,
                (s * setWeight pi (Q.erase x)) := by
            gcongr with x hx
            exact herase x hx
          _ <= (theta t ^ B.card * rho t) *
                ∑ x ∈ Q, (s * setWeight pi (Q.erase x)) := by
            gcongr
            exact hadjust t
          _ = (s * theta t ^ B.card) *
              ∑ x ∈ Q, rho t * setWeight pi (Q.erase x) := by
            rw [mul_sum, mul_sum]
            apply sum_congr rfl
            intro x hx
            ring
      calc
        (FiniteLaw.bind
            (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega0))
            (K t)).probability (SelectedUncoveredEvent R U Q B) <=
          theta t ^ B.card *
              (FiniteLaw.evolveKernels K t
                (FiniteLaw.pure omega0)).probability
                  (SelectedUncoveredEvent R U Q B) +
            delta t * ∑ x ∈ Q,
              (FiniteLaw.evolveKernels K t
                (FiniteLaw.pure omega0)).probability
                  (SelectedUncoveredEvent R U (Q.erase x) B) := hrec
        _ <= (s * theta t ^ B.card) * setWeight pi Q +
            (s * theta t ^ B.card) *
              ∑ x ∈ Q, rho t * setWeight pi (Q.erase x) :=
          add_le_add hfirst hsum
        _ = (s * theta t ^ B.card) *
            (setWeight pi Q +
              ∑ x ∈ Q, rho t * setWeight pi (Q.erase x)) := by ring
        _ <= (s * theta t ^ B.card) *
            setWeight (fun x => pi x + rho t) Q := by
          gcongr
          exact setWeight_add_singletons_le pi (fun _ => rho t) Q
        _ = cumulativeSurvival theta (t + 1) ^ B.card *
            setWeight
              (cumulativePointHazard (fun i _ => rho i) (t + 1)) Q := by
          have hs' : s * theta t ^ B.card =
              cumulativeSurvival theta (t + 1) ^ B.card := by
            simp only [s, cumulativeSurvival_succ, mul_pow]
          have hpi : (fun x => pi x + rho t) =
              cumulativePointHazard (fun i _ => rho i) (t + 1) := by
            funext x
            simp only [pi, cumulativePointHazard, sum_range_succ]
          rw [hs', hpi]

/-- Support-restricted version of the sharp inhomogeneous product estimate.
This is the form used by a stopped clocked process: the local estimates only
need to hold on states that can actually be reached at the corresponding
time. -/
theorem evolveKernels_probability_selectedUncovered_le_product_of_supported
    {Omega W Z : Type*} [Fintype Omega] [DecidableEq Omega]
    [DecidableEq W] [DecidableEq Z]
    (K : ℕ -> Omega -> FiniteLaw Omega)
    (R : Omega -> Finset W) (U : Omega -> Finset Z)
    (delta theta rho : ℕ -> ℝ≥0)
    (P : ℕ -> Omega -> Prop) (N : ℕ)
    (hsupport : ∀ i, i < N -> ∀ omega, P i omega ->
      (K i omega).SupportedOn (P (i + 1)))
    (hsingle : ∀ i, i < N -> ∀ omega, P i omega ->
      (K i omega).SupportedOn fun omega' =>
        R omega ⊆ R omega' ∧ (R omega' \ R omega).card <= 1)
    (hantitone : ∀ i, i < N -> ∀ omega, P i omega ->
      (K i omega).SupportedOn fun omega' => U omega' ⊆ U omega)
    (hsurvive : ∀ i, i < N -> ∀ omega, P i omega ->
      ∀ B, B ⊆ U omega ->
      (K i omega).probability (fun omega' => B ⊆ U omega') <=
        theta i ^ B.card)
    (hpoint : ∀ i, i < N -> ∀ omega, P i omega ->
      ∀ x, x ∉ R omega -> ∀ B, B ⊆ U omega ->
      (K i omega).probability (fun omega' =>
        x ∈ R omega' ∧ B ⊆ U omega') <= delta i)
    (omega0 : Omega) (hP0 : P 0 omega0)
    (Q : Finset W) (B : Finset Z)
    (hdisjoint : Disjoint Q (R omega0)) (hB0 : B ⊆ U omega0)
    (hadjust : ∀ i, delta i <= theta i ^ B.card * rho i)
    (t : ℕ) (htN : t <= N) :
    (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega0)).probability
        (SelectedUncoveredEvent R U Q B) <=
      cumulativeSurvival theta t ^ B.card *
        setWeight (cumulativePointHazard (fun i _ => rho i) t) Q := by
  classical
  have hP (n : ℕ) (hnN : n <= N) :
      (FiniteLaw.evolveKernels K n (FiniteLaw.pure omega0)).SupportedOn
        (P n) := by
    induction n with
    | zero => exact FiniteLaw.supportedOn_pure _ hP0
    | succ n ih =>
        exact (ih (by omega)).bind (K n) fun omega homega =>
          hsupport n (by omega) omega homega
  induction t generalizing Q with
  | zero =>
      simp only [FiniteLaw.evolveKernels_zero, FiniteLaw.probability_pure,
        cumulativeSurvival_zero, one_pow, one_mul, cumulativePointHazard,
        range_zero, sum_empty]
      by_cases hQ : Q = ∅
      · subst Q
        simp [SelectedUncoveredEvent, hB0, setWeight]
      · have hnot : ¬ Q ⊆ R omega0 := by
          intro hsub
          obtain ⟨x, hxQ⟩ := nonempty_iff_ne_empty.mpr hQ
          exact disjoint_left.mp hdisjoint hxQ (hsub hxQ)
        simp [SelectedUncoveredEvent, hnot, setWeight]
  | succ t ih =>
      rw [FiniteLaw.evolveKernels_succ]
      have ht : t < N := by omega
      have hrec := bind_probability_selectedUncovered_le_of_supported
        (K t) R U (delta t) (theta t) (P t)
          (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega0))
          (hP t (by omega))
          (hsingle t ht) (hantitone t ht)
          (hsurvive t ht) (hpoint t ht) Q B
      let s : ℝ≥0 := cumulativeSurvival theta t ^ B.card
      let pi : W -> ℝ≥0 :=
        cumulativePointHazard (fun i _ => rho i) t
      have hQbound :
          (FiniteLaw.evolveKernels K t
            (FiniteLaw.pure omega0)).probability
              (SelectedUncoveredEvent R U Q B) <= s * setWeight pi Q := by
        simpa only [s, pi] using ih Q hdisjoint (by omega)
      have herase : ∀ x ∈ Q,
          (FiniteLaw.evolveKernels K t
            (FiniteLaw.pure omega0)).probability
              (SelectedUncoveredEvent R U (Q.erase x) B) <=
            s * setWeight pi (Q.erase x) := by
        intro x hx
        have hd : Disjoint (Q.erase x) (R omega0) :=
          hdisjoint.mono_left (erase_subset x Q)
        simpa only [s, pi] using ih (Q.erase x) hd (by omega)
      have hfirst :
          theta t ^ B.card *
              (FiniteLaw.evolveKernels K t
                (FiniteLaw.pure omega0)).probability
                  (SelectedUncoveredEvent R U Q B) <=
            (s * theta t ^ B.card) * setWeight pi Q := by
        calc
          theta t ^ B.card *
                (FiniteLaw.evolveKernels K t
                  (FiniteLaw.pure omega0)).probability
                    (SelectedUncoveredEvent R U Q B) <=
              theta t ^ B.card * (s * setWeight pi Q) := by gcongr
          _ = (s * theta t ^ B.card) * setWeight pi Q := by ring
      have hsum :
          delta t * ∑ x ∈ Q,
              (FiniteLaw.evolveKernels K t
                (FiniteLaw.pure omega0)).probability
                  (SelectedUncoveredEvent R U (Q.erase x) B) <=
            (s * theta t ^ B.card) *
              ∑ x ∈ Q, rho t * setWeight pi (Q.erase x) := by
        calc
          delta t * ∑ x ∈ Q,
                (FiniteLaw.evolveKernels K t
                  (FiniteLaw.pure omega0)).probability
                    (SelectedUncoveredEvent R U (Q.erase x) B) <=
              delta t * ∑ x ∈ Q,
                (s * setWeight pi (Q.erase x)) := by
            gcongr with x hx
            exact herase x hx
          _ <= (theta t ^ B.card * rho t) *
                ∑ x ∈ Q, (s * setWeight pi (Q.erase x)) := by
            gcongr
            exact hadjust t
          _ = (s * theta t ^ B.card) *
              ∑ x ∈ Q, rho t * setWeight pi (Q.erase x) := by
            rw [mul_sum, mul_sum]
            apply sum_congr rfl
            intro x hx
            ring
      calc
        (FiniteLaw.bind
            (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega0))
            (K t)).probability (SelectedUncoveredEvent R U Q B) <=
          theta t ^ B.card *
              (FiniteLaw.evolveKernels K t
                (FiniteLaw.pure omega0)).probability
                  (SelectedUncoveredEvent R U Q B) +
            delta t * ∑ x ∈ Q,
              (FiniteLaw.evolveKernels K t
                (FiniteLaw.pure omega0)).probability
                  (SelectedUncoveredEvent R U (Q.erase x) B) := hrec
        _ <= (s * theta t ^ B.card) * setWeight pi Q +
            (s * theta t ^ B.card) *
              ∑ x ∈ Q, rho t * setWeight pi (Q.erase x) :=
          add_le_add hfirst hsum
        _ = (s * theta t ^ B.card) *
            (setWeight pi Q +
              ∑ x ∈ Q, rho t * setWeight pi (Q.erase x)) := by ring
        _ <= (s * theta t ^ B.card) *
            setWeight (fun x => pi x + rho t) Q := by
          gcongr
          exact setWeight_add_singletons_le pi (fun _ => rho t) Q
        _ = cumulativeSurvival theta (t + 1) ^ B.card *
            setWeight
              (cumulativePointHazard (fun i _ => rho i) (t + 1)) Q := by
          have hs' : s * theta t ^ B.card =
              cumulativeSurvival theta (t + 1) ^ B.card := by
            simp only [s, cumulativeSurvival_succ, mul_pow]
          have hpi : (fun x => pi x + rho t) =
              cumulativePointHazard (fun i _ => rho i) (t + 1) := by
            funext x
            simp only [pi, cumulativePointHazard, sum_range_succ]
          rw [hs', hpi]

end

end Erdos207
