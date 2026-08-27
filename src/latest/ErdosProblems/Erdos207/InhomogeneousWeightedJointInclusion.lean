/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.WeightedKernelJointInclusion
import ErdosProblems.Erdos207.FiniteKernelConcentration

/-!
# Point-weighted joint inclusion for inhomogeneous kernels

The scalar inhomogeneous estimate loses the vortex level of every triangle.
Here each time step has its own point hazard `delta i x`; the final weight of
`x` is the sum of its hazards over time.  This is the form needed to compose
the fixed-level phases of a vortex sweep.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- The product with pointwise enlarged factors contains both the old
product and every term in which exactly one factor is replaced. -/
lemma setWeight_add_singletons_le
    {W : Type*} [DecidableEq W] (pi rho : W → ℝ≥0) :
    ∀ U : Finset W,
      setWeight pi U +
          ∑ x ∈ U, rho x * setWeight pi (U.erase x) ≤
        setWeight (fun x ↦ pi x + rho x) U := by
  intro U
  induction U using Finset.induction_on with
  | empty => simp [setWeight]
  | @insert x U hx ih =>
      have herase_x : (insert x U).erase x = U := by simp [hx]
      have herase_y (y : W) (hy : y ∈ U) :
          (insert x U).erase y = insert x (U.erase y) := by
        ext z
        simp only [mem_erase, mem_insert]
        constructor
        · intro hz
          rcases hz.2 with rfl | hzU
          · exact Or.inl rfl
          · exact Or.inr ⟨hz.1, hzU⟩
        · intro hz
          refine ⟨?_, ?_⟩
          · rcases hz with rfl | hz
            · exact fun hxy ↦ hx (hxy ▸ hy)
            · exact hz.1
          · rcases hz with rfl | hz
            · exact Or.inl rfl
            · exact Or.inr hz.2
      simp only [setWeight, prod_insert hx, sum_insert hx, herase_x]
      have hrewrite :
          ∑ y ∈ U, rho y *
              (pi x * ∏ z ∈ U.erase y, pi z) =
            pi x * ∑ y ∈ U, rho y * ∏ z ∈ U.erase y, pi z := by
        rw [mul_sum]
        apply sum_congr rfl
        intro y hy
        ring
      have hsum_erase :
          ∑ y ∈ U, rho y * ∏ z ∈ (insert x U).erase y, pi z =
            ∑ y ∈ U, rho y *
              (pi x * ∏ z ∈ U.erase y, pi z) := by
        apply sum_congr rfl
        intro y hy
        rw [herase_y y hy, prod_insert]
        exact fun hxerase ↦ hx (erase_subset y U hxerase)
      rw [hsum_erase]
      rw [hrewrite]
      calc
        pi x * ∏ z ∈ U, pi z +
              (rho x * ∏ z ∈ U, pi z +
                pi x * ∑ y ∈ U,
                  rho y * ∏ z ∈ U.erase y, pi z) =
            (pi x + rho x) * ∏ z ∈ U, pi z +
              pi x * ∑ y ∈ U,
                rho y * ∏ z ∈ U.erase y, pi z := by ring
        _ ≤ (pi x + rho x) *
              (∏ z ∈ U, pi z +
                ∑ y ∈ U, rho y * ∏ z ∈ U.erase y, pi z) := by
          rw [mul_add]
          exact add_le_add_right
            (mul_le_mul_left (le_add_of_nonneg_right bot_le)
              (∑ y ∈ U, rho y * ∏ z ∈ U.erase y, pi z)) _
        _ ≤ (pi x + rho x) *
              ∏ z ∈ U, (pi z + rho z) :=
          mul_le_mul_right ih (pi x + rho x)
        _ = (pi x + rho x) *
              ∏ z ∈ U, (fun z ↦ pi z + rho z) z := rfl

/-- Cumulative point hazard through the first `t` kernels. -/
def cumulativePointHazard
    {W : Type*} (delta : ℕ → W → ℝ≥0) (t : ℕ) (x : W) : ℝ≥0 :=
  ∑ i ∈ range t, delta i x

/-- A time-inhomogeneous monotone single-insertion process retains the
product of the individual cumulative point hazards. -/
theorem evolveKernels_probability_subset_le_pointWeights
    {Omega W : Type*} [Fintype Omega] [DecidableEq Omega] [DecidableEq W]
    (K : ℕ → Omega → FiniteLaw Omega) (R : Omega → Finset W)
    (delta : ℕ → W → ℝ≥0)
    (hsingle : ∀ i, IsMonotoneSingleInsertionKernel (K i) R)
    (hpoint : ∀ i omega x, x ∉ R omega →
      (K i omega).probability (fun omega' ↦ x ∈ R omega') ≤ delta i x)
    (omega0 : Omega) (U : Finset W) (hdisjoint : Disjoint U (R omega0))
    (t : ℕ) :
    (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega0)).probability
        (fun omega ↦ U ⊆ R omega) ≤
      (U.card.factorial : ℝ≥0) *
        setWeight (cumulativePointHazard delta t) U := by
  classical
  induction t generalizing U with
  | zero =>
      simp only [FiniteLaw.evolveKernels_zero, FiniteLaw.probability_pure,
        cumulativePointHazard, range_zero, sum_empty]
      by_cases hU : U = ∅
      · subst U
        simp [setWeight]
      · have hnot : ¬ U ⊆ R omega0 := by
          intro hsub
          obtain ⟨x, hxU⟩ := nonempty_iff_ne_empty.mpr hU
          exact disjoint_left.mp hdisjoint hxU (hsub hxU)
        simp [hnot]
  | succ t ih =>
      by_cases hU : U = ∅
      · subst U
        simp [FiniteLaw.probability_true, setWeight]
      · have hcardpos : 0 < U.card := card_pos.mpr
          (nonempty_iff_ne_empty.mpr hU)
        obtain ⟨s, hcard⟩ : ∃ s, U.card = s + 1 :=
          Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcardpos)
        rw [FiniteLaw.evolveKernels_succ]
        have hrec := bind_probability_subset_le_pointWeight
          (K t) R (delta t) (hsingle t) (hpoint t)
          (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega0)) U
        have hUbound := ih U hdisjoint
        have herase (x : W) (hx : x ∈ U) :
            (FiniteLaw.evolveKernels K t
              (FiniteLaw.pure omega0)).probability
                (fun omega ↦ U.erase x ⊆ R omega) ≤
              (s.factorial : ℝ≥0) *
                setWeight (cumulativePointHazard delta t) (U.erase x) := by
          have hd : Disjoint (U.erase x) (R omega0) :=
            hdisjoint.mono_left (erase_subset x U)
          have h := ih (U.erase x) hd
          simpa [card_erase_of_mem hx, hcard] using h
        let pi : W → ℝ≥0 := cumulativePointHazard delta t
        let rho : W → ℝ≥0 := delta t
        have hsum :
            ∑ x ∈ U, rho x *
                (FiniteLaw.evolveKernels K t
                  (FiniteLaw.pure omega0)).probability
                    (fun omega ↦ U.erase x ⊆ R omega) ≤
              (s.factorial : ℝ≥0) *
                ∑ x ∈ U, rho x * setWeight pi (U.erase x) := by
          calc
            ∑ x ∈ U, rho x *
                (FiniteLaw.evolveKernels K t
                  (FiniteLaw.pure omega0)).probability
                    (fun omega ↦ U.erase x ⊆ R omega) ≤
                ∑ x ∈ U, rho x *
                  ((s.factorial : ℝ≥0) *
                    setWeight pi (U.erase x)) := by
              apply sum_le_sum
              intro x hx
              simpa only [rho, pi, mul_comm] using
                mul_le_mul_left (herase x hx) (rho x)
            _ = (s.factorial : ℝ≥0) *
                ∑ x ∈ U, rho x * setWeight pi (U.erase x) := by
              rw [mul_sum]
              apply sum_congr rfl
              intro x hx
              ring
        have hone : (1 : ℝ≥0) ≤ s + 1 := by
          exact_mod_cast Nat.succ_pos s
        have hinside :
            (s + 1 : ℝ≥0) * setWeight pi U +
                ∑ x ∈ U, rho x * setWeight pi (U.erase x) ≤
              (s + 1 : ℝ≥0) *
                setWeight (fun x ↦ pi x + rho x) U := by
          calc
            (s + 1 : ℝ≥0) * setWeight pi U +
                  ∑ x ∈ U, rho x * setWeight pi (U.erase x) ≤
                (s + 1 : ℝ≥0) * setWeight pi U +
                  (s + 1 : ℝ≥0) *
                    ∑ x ∈ U, rho x * setWeight pi (U.erase x) := by
              gcongr
              exact (show
                ∑ x ∈ U, rho x * setWeight pi (U.erase x) ≤
                  (s + 1 : ℝ≥0) *
                    ∑ x ∈ U, rho x * setWeight pi (U.erase x) by
                calc
                  ∑ x ∈ U, rho x * setWeight pi (U.erase x) =
                      1 * ∑ x ∈ U,
                        rho x * setWeight pi (U.erase x) := by simp
                  _ ≤ (s + 1 : ℝ≥0) *
                      ∑ x ∈ U, rho x * setWeight pi (U.erase x) := by
                    gcongr)
            _ = (s + 1 : ℝ≥0) *
                (setWeight pi U +
                  ∑ x ∈ U, rho x * setWeight pi (U.erase x)) := by ring
            _ ≤ (s + 1 : ℝ≥0) *
                setWeight (fun x ↦ pi x + rho x) U := by
              gcongr
              exact setWeight_add_singletons_le pi rho U
        calc
          (FiniteLaw.bind
              (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega0))
              (K t)).probability (fun omega ↦ U ⊆ R omega) ≤
            (FiniteLaw.evolveKernels K t
              (FiniteLaw.pure omega0)).probability
                (fun omega ↦ U ⊆ R omega) +
              ∑ x ∈ U, rho x *
                (FiniteLaw.evolveKernels K t
                  (FiniteLaw.pure omega0)).probability
                    (fun omega ↦ U.erase x ⊆ R omega) := by
            simpa only [rho] using hrec
          _ ≤ (U.card.factorial : ℝ≥0) * setWeight pi U +
              (s.factorial : ℝ≥0) *
                ∑ x ∈ U, rho x * setWeight pi (U.erase x) :=
            add_le_add (by simpa only [pi] using hUbound) hsum
          _ = (s.factorial : ℝ≥0) *
              ((s + 1 : ℝ≥0) * setWeight pi U +
                ∑ x ∈ U, rho x * setWeight pi (U.erase x)) := by
            simp only [hcard, Nat.factorial_succ, Nat.cast_mul,
              Nat.cast_add, Nat.cast_one]
            ring
          _ ≤ (s.factorial : ℝ≥0) *
              ((s + 1 : ℝ≥0) *
                setWeight (fun x ↦ pi x + rho x) U) := by gcongr
          _ = (U.card.factorial : ℝ≥0) *
              setWeight (cumulativePointHazard delta (t + 1)) U := by
            have hpi : (fun x ↦ pi x + rho x) =
                cumulativePointHazard delta (t + 1) := by
              funext x
              simp only [pi, rho, cumulativePointHazard, sum_range_succ]
            rw [hpi]
            simp only [hcard, Nat.factorial_succ, Nat.cast_mul,
              Nat.cast_add, Nat.cast_one]
            ring

end

end Erdos207
