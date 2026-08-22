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

import ErdosProblems.Erdos1165.AsymmetricPairSeparationGeometry

/-!
# Successful profiles with one erased scale interval

The asymmetric pair splice retains the left profile before a three-scale
separation buffer and after the padded right-hand cut.  The coordinates in
between are deliberately unrestricted.  This file defines that exact
pathwise predicate and records its elementary source and congruence lemmas.
-/

namespace Erdos1165.BufferedSuccessfulProfile

open ThickPoint

noncomputable section

/-- A profile coordinate is retained if it lies before `low` or after
`high`.  Both endpoints are retained. -/
def RetainedCoordinate (low high k : ℕ) : Prop := k ≤ low ∨ high ≤ k

instance retainedCoordinateDecidable (low high k : ℕ) :
    Decidable (RetainedCoordinate low high k) := by
  unfold RetainedCoordinate
  infer_instance

/-- The HLOZ successful-profile conditions outside one erased interval.
The initial coordinate is imposed exactly when it belongs to the retained
low block.  The terminal window is retained explicitly. -/
def IsBufferedSuccessfulProfile
    (n low high : ℕ) (delta : ℝ) (N : Fin (n + 2) → ℕ) : Prop :=
  (1 ≤ low → N ⟨1, by omega⟩ = 1) ∧
  (∀ k : Fin (n + 2), 2 ≤ k.1 → k.1 ≤ n →
    RetainedCoordinate low high k.1 →
      |(N k : ℝ) - 2 * (k.1 : ℝ) ^ 2| ≤
        (k.1 : ℝ) ^ (1 + delta)) ∧
  terminalLower n delta ≤ (N ⟨n + 1, by omega⟩ : ℝ) ∧
  N ⟨n + 1, by omega⟩ ≤ n ^ 3

/-- Ordinary success implies success after erasing any scale interval. -/
theorem of_successfulProfile
    {n low high : ℕ} {delta : ℝ} {N : Fin (n + 2) → ℕ}
    (hN : SuccessfulProfile n delta N) :
    IsBufferedSuccessfulProfile n low high delta N := by
  refine ⟨fun _ ↦ hN.1, ?_, hN.2.2⟩
  intro k hk2 hkn _hk
  exact hN.2.1 k hk2 hkn

/-- Equality on every retained coordinate transports buffered success. -/
theorem congr_retained
    {n low high : ℕ} {delta : ℝ}
    {left right : Fin (n + 2) → ℕ}
    (hhigh : high ≤ n + 1)
    (hleft : IsBufferedSuccessfulProfile n low high delta left)
    (heq : ∀ k : Fin (n + 2), RetainedCoordinate low high k.1 →
      right k = left k) :
    IsBufferedSuccessfulProfile n low high delta right := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hlow
    rw [heq ⟨1, by omega⟩ (Or.inl hlow)]
    exact hleft.1 hlow
  · intro k hk2 hkn hk
    rw [heq k hk]
    exact hleft.2.1 k hk2 hkn hk
  · have hterminal : RetainedCoordinate low high (n + 1) := by
      exact Or.inr hhigh
    rw [heq ⟨n + 1, by omega⟩ hterminal]
    exact hleft.2.2.1
  · have hterminal : RetainedCoordinate low high (n + 1) := by
      exact Or.inr hhigh
    rw [heq ⟨n + 1, by omega⟩ hterminal]
    exact hleft.2.2.2

/-- Pathwise buffered success at one centre and one stopping horizon. -/
def BufferedSuccessfulPoint
    (s : WalkPath) (n low high horizon : ℕ) (delta : ℝ)
    (x : Point) : Prop :=
  x ∈ candidateBox n ∧
    IsBufferedSuccessfulProfile n low high delta
      (excursionProfile s n horizon x)

/-- Ordinary successful points are buffered successful points. -/
theorem of_successfulPoint
    {s : WalkPath} {n low high horizon : ℕ} {delta : ℝ} {x : Point}
    (h : SuccessfulPoint s n horizon delta x) :
    BufferedSuccessfulPoint s n low high horizon delta x :=
  ⟨h.1, of_successfulProfile h.2⟩

/-- A retained-coordinate profile identity transports buffered point
success while keeping the common candidate-box condition. -/
theorem point_congr_retained
    {left right : WalkPath} {n low high leftHorizon rightHorizon : ℕ}
    {delta : ℝ} {x : Point}
    (hhigh : high ≤ n + 1)
    (hleft : BufferedSuccessfulPoint left n low high leftHorizon delta x)
    (heq : ∀ k : Fin (n + 2), RetainedCoordinate low high k.1 →
      excursionProfile right n rightHorizon x k =
        excursionProfile left n leftHorizon x k) :
    BufferedSuccessfulPoint right n low high rightHorizon delta x :=
  ⟨hleft.1, congr_retained hhigh hleft.2 heq⟩

end

end Erdos1165.BufferedSuccessfulProfile
