/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos721.LocalStructuralIteration
import APAP.Prereqs.Convolution.ThreeAP

/-!
# The diagonal three-progression count at the local endpoint

For a three-progression-free set in a finite abelian group of odd order,
the only pairs contributing to its self-convolution on twice the set are
the diagonal pairs.  APAP proves the resulting exact inner-product identity.
This file records the fixed correlation gap used at the terminal stage of
the cyclic Bloom--Sisask iteration.
-/

namespace Erdos721

open Finset Fintype RCLike
open scoped Pointwise mu

namespace CyclicLocalAPCounting

/-- The exact diagonal count for a progression-free set. -/
theorem diagonal_correlation
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hodd : Odd (Fintype.card G)) (A : Finset G)
    (hAfree : ThreeAPFree (A : Set G)) :
    ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] A, μ_[ℝ] (A.image (2 • ·))⟫_[ℝ] =
      ((A.card : ℝ) ^ 2)⁻¹ := by
  simpa using hAfree.wInner_one_mu_ddconv_mu_mu_two_smul_mu hodd

/-- If the diagonal contribution is at most one half after local scaling,
then the correlation differs from the random value `1` by at least one
half.  This is precisely the `hmain` hypothesis of the local lifting step
with `epsilon = 1 / 2`. -/
theorem half_le_abs_scaled_correlation_sub_one
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hodd : Odd (Fintype.card G)) (B A : Finset G)
    (hAfree : ThreeAPFree (A : Set G))
    (hdiag : (B.card : ℝ) * ((A.card : ℝ) ^ 2)⁻¹ ≤ 1 / 2) :
    1 / 2 ≤
      |(B.card : ℝ) *
          ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] A, μ_[ℝ] (A.image (2 • ·))⟫_[ℝ] - 1| := by
  rw [diagonal_correlation hodd A hAfree]
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- A convenient cardinal form of the diagonal-smallness hypothesis. -/
theorem half_le_abs_scaled_correlation_sub_one_of_card
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (hodd : Odd (Fintype.card G)) (B A : Finset G)
    (hA : A.Nonempty) (hAfree : ThreeAPFree (A : Set G))
    (hcard : 2 * B.card ≤ A.card ^ 2) :
    1 / 2 ≤
      |(B.card : ℝ) *
          ⟪μ_[ℝ] A ∗ᵈ μ_[ℝ] A, μ_[ℝ] (A.image (2 • ·))⟫_[ℝ] - 1| := by
  apply half_le_abs_scaled_correlation_sub_one hodd B A hAfree
  have hAcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  rw [← div_eq_mul_inv, div_le_iff₀ (by positivity : (0 : ℝ) < (A.card : ℝ) ^ 2)]
  have hcardR : (2 : ℝ) * B.card ≤ (A.card : ℝ) ^ 2 := by
    exact_mod_cast hcard
  nlinarith

end CyclicLocalAPCounting
end Erdos721
