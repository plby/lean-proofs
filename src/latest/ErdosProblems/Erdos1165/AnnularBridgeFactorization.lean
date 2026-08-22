/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.AnnularBoundaryExcursionKernel

/-!
# Full-skeleton factorization for intermediate annular bridges

This is the canonical insertion wrapper for the actual Appendix-A.6 mark.
The complementary code may retain the whole stopped history, including all
information after every erased bridge.  Each erased bridge is coded by its
literal first-outer-hit word together with the exact number of completed
middle-to-inner excursions and its outer endpoint.

Consequently the fair-walk mass factors exactly as the arbitrary retained
skeleton weight times the product of the literal joint count/endpoint
kernels.  No adaptedness, conditional-independence, or measure identity is
assumed as a premise.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularBridgeFactorization

noncomputable section

open MarkedBridgeFactorization AnnularBoundaryExcursionKernel

/-- Canonical full-skeleton factorization for the genuine intermediate
annular offspring mark.  The sole compatibility hypothesis is that the
insertion datum uses the underlying word of the canonical stopped-word code.
The probability identity follows from prefix-free insertion and countable
additivity. -/
theorem fairSteps_event_eq_weight_mul_canonical_excursionKernel
    {m : ℕ} {Complement : Type*} [Countable Complement]
    (outer middle inner : Fin m → Set Point)
    (start endpoint : Fin m → Point)
    (offspring : Fin m → ℕ)
    (atom : ComplementarySkeletonAtom m Complement
      (fun j ↦ BoundaryExcursionExitWordCode
        (outer j) (middle j) (inner j) (start j)
        (offspring j) (endpoint j)))
    (hword : ∀ j b, atom.bridgeWord j b = b.1) :
    fairSteps atom.event = atom.weight *
      ∏ j, boundaryExcursionExitKernel
        (outer j) (middle j) (inner j) (start j)
        (offspring j) (endpoint j) := by
  rw [fairSteps_event_eq_weight_mul_prod_kernel atom]
  apply congrArg (atom.weight * ·)
  apply Finset.prod_congr rfl
  intro j _hj
  change (∑' b, stoppedWordMass (atom.bridgeWord j b)) =
    boundaryExcursionExitKernel
      (outer j) (middle j) (inner j) (start j)
      (offspring j) (endpoint j)
  rw [boundaryExcursionExitKernel_eq_tsum_stoppedWordMass]
  apply tsum_congr
  intro b
  rw [hword j b]

end

end Erdos1165.AnnularBridgeFactorization
