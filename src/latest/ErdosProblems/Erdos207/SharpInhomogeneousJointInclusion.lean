/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InhomogeneousWeightedJointInclusion

/-!
# Sharp inhomogeneous joint inclusion

The one-step subset recurrence already has the elementary symmetric form
needed for a product bound.  Iterating `setWeight_add_singletons_le`
therefore gives the product of cumulative point hazards with no factorial
loss.  This sharper form is important for a scheduled cover kernel whose
schedule can be much longer than its pointwise candidate threshold.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- A time-inhomogeneous monotone single-insertion process is bounded by the
product of its cumulative point hazards. -/
theorem evolveKernels_probability_subset_le_pointWeights_sharp
    {Omega W : Type*} [Fintype Omega] [DecidableEq Omega] [DecidableEq W]
    (K : Nat -> Omega -> FiniteLaw Omega) (R : Omega -> Finset W)
    (delta : Nat -> W -> NNReal)
    (hsingle : ∀ i, IsMonotoneSingleInsertionKernel (K i) R)
    (hpoint : ∀ i omega x, x ∉ R omega ->
      (K i omega).probability (fun omega' => x ∈ R omega') <= delta i x)
    (omega0 : Omega) (U : Finset W) (hdisjoint : Disjoint U (R omega0))
    (t : Nat) :
    (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega0)).probability
        (fun omega => U ⊆ R omega) <=
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
        have hcard : U.card ≠ 0 := card_ne_zero.mpr
          (nonempty_iff_ne_empty.mpr hU)
        simp [hnot, setWeight, hcard]
  | succ t ih =>
      rw [FiniteLaw.evolveKernels_succ]
      have hrec := bind_probability_subset_le_pointWeight
        (K t) R (delta t) (hsingle t) (hpoint t)
        (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega0)) U
      let pi : W -> NNReal := cumulativePointHazard delta t
      let rho : W -> NNReal := delta t
      have hUbound :
          (FiniteLaw.evolveKernels K t
            (FiniteLaw.pure omega0)).probability
              (fun omega => U ⊆ R omega) <= setWeight pi U := by
        simpa only [pi] using ih U hdisjoint
      have herase : ∀ x ∈ U,
          (FiniteLaw.evolveKernels K t
            (FiniteLaw.pure omega0)).probability
              (fun omega => U.erase x ⊆ R omega) <=
            setWeight pi (U.erase x) := by
        intro x hx
        have hd : Disjoint (U.erase x) (R omega0) :=
          hdisjoint.mono_left (erase_subset x U)
        simpa only [pi] using ih (U.erase x) hd
      calc
        (FiniteLaw.bind
            (FiniteLaw.evolveKernels K t (FiniteLaw.pure omega0))
            (K t)).probability (fun omega => U ⊆ R omega) <=
          (FiniteLaw.evolveKernels K t
            (FiniteLaw.pure omega0)).probability
              (fun omega => U ⊆ R omega) +
            ∑ x ∈ U, rho x *
              (FiniteLaw.evolveKernels K t
                (FiniteLaw.pure omega0)).probability
                  (fun omega => U.erase x ⊆ R omega) := by
            simpa only [rho] using hrec
        _ <= setWeight pi U +
            ∑ x ∈ U, rho x * setWeight pi (U.erase x) := by
          apply add_le_add hUbound
          apply sum_le_sum
          intro x hx
          simpa only [mul_comm] using mul_le_mul_left (herase x hx) (rho x)
        _ <= setWeight (fun x => pi x + rho x) U :=
          setWeight_add_singletons_le pi rho U
        _ = setWeight (cumulativePointHazard delta (t + 1)) U := by
          congr 1
          funext x
          simp only [pi, rho, cumulativePointHazard, sum_range_succ]

end

end Erdos207
