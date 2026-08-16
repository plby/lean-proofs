/-
Copyright 2026 The Lean-Proofs Authors.

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
import Mathlib

/-!
# Erdős Problem 1064

The density-one inequality `φ (n - φ n) + f n < φ n` holds for every
natural-valued `o(n)` error term `f`.
-/

open Nat Filter Topology Set Real
open scoped BigOperators

namespace Set

@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

namespace Erdos1064

noncomputable section

def reciprocalPrimeMass (n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors, (p : ℝ)⁻¹

def largeReciprocalPrimeMass (B n : ℕ) : ℝ :=
  ∑ p ∈ n.primeFactors.filter (B < ·), (p : ℝ)⁻¹

theorem erdos_1064.variants.general_function (f : ℕ → ℕ)
    (hf : (fun n ↦ (f n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ))) :
    {n : ℕ | φ (n - φ n) + f n < φ n}.HasDensity 1 := by
  sorry
