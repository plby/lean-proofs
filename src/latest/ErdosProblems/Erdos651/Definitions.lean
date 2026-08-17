/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-! Exact geometric and asymptotic definitions for Erdős Problem 651. -/

namespace Erdos651

open Filter Set
open scoped Topology

noncomputable section

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

def InGeneralPosition (d : ℕ) (X : Finset (Point d)) : Prop :=
  ∀ S : Finset (Point d), S ⊆ X → S.card = d + 1 →
    AffineIndependent ℝ (fun p : ↥S ↦ (p : Point d))

def InConvexPosition {d : ℕ} (X : Finset (Point d)) : Prop :=
  ∀ x ∈ X, x ∉ convexHull ℝ (↑(X.erase x) : Set (Point d))

def ContainsConvexSubset (d n : ℕ) (X : Finset (Point d)) : Prop :=
  ∃ Y : Finset (Point d), Y ⊆ X ∧ Y.card = n ∧ InConvexPosition Y

def ForcesConvexSubset (d n N : ℕ) : Prop :=
  ∀ X : Finset (Point d), N ≤ X.card → InGeneralPosition d X →
    ContainsConvexSubset d n X

def HasErdosSzekeresNumber (d n : ℕ) : Prop :=
  Set.Nonempty {N : ℕ | ForcesConvexSubset d n N}

noncomputable def erdosSzekeresNumber (d n : ℕ) : ℕ :=
  sInf {N : ℕ | ForcesConvexSubset d n N}

lemma ForcesConvexSubset.mono {d n N M : ℕ} (hNM : N ≤ M)
    (hN : ForcesConvexSubset d n N) : ForcesConvexSubset d n M := by
  intro X hMX hgp
  exact hN X (hNM.trans hMX) hgp

lemma erdosSzekeresNumber_forces {d n : ℕ}
    (h : HasErdosSzekeresNumber d n) :
    ForcesConvexSubset d n (erdosSzekeresNumber d n) := by
  exact Nat.sInf_mem h

lemma erdosSzekeresNumber_le {d n N : ℕ}
    (hN : ForcesConvexSubset d n N) :
    erdosSzekeresNumber d n ≤ N := by
  exact Nat.sInf_le hN

def HasSubexponentialUpperBound (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n : ℕ in Filter.atTop,
      (f n : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ))

def HasExponentialLowerBound (f : ℕ → ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ n : ℕ in Filter.atTop, (1 + c) ^ n < (f n : ℝ)

def Erdos651Claim : Prop :=
  HasExponentialLowerBound (erdosSzekeresNumber 3)

def PohoataZakharovConclusion : Prop :=
  HasSubexponentialUpperBound (erdosSzekeresNumber 3)

end

end Erdos651
