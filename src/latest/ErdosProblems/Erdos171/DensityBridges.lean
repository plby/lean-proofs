/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.SubspaceDensity
import ErdosProblems.Erdos171.Tiling
import ErdosProblems.Erdos171.Iteration

/-!
# Compatibility bridges for the Erdős 171 density APIs

`SubspaceDensity` and `Tiling` introduced the same two finite constructions
under names adapted to their respective uses.  This file keeps both public
APIs stable and records their extensional equality.  It also records the exact
ambient-denominator change when a finset of words is included from `Fin k` into
`Fin (k + 1)`.
-/

open Combinatorics

namespace Erdos171

section SubspaceAPIs

variable {eta alpha iota : Type*}

/-- The density API's pullback and the tiling API's pullback are the same
finset of parameter words. -/
@[simp] theorem pullbackFinset_eq_subspacePullback
    [Fintype (eta → alpha)]
    (U : Subspace eta alpha iota) (D : Finset (iota → alpha)) :
    pullbackFinset U D = subspacePullback U D := by
  classical
  ext x
  simp

/-- The density API's finite subspace image is the tiling API's tile. -/
@[simp] theorem subspaceImageFinset_eq_subspacePoints
    [Fintype (eta → alpha)] [DecidableEq (iota → alpha)]
    (U : Subspace eta alpha iota) :
    subspaceImageFinset U = subspacePoints U := by
  classical
  ext x
  simp

/-- Pullback density may equivalently be expressed using the tiling pullback. -/
theorem subspaceDensityFinset_eq_density_subspacePullback
    [Fintype (eta → alpha)]
    (U : Subspace eta alpha iota) (D : Finset (iota → alpha)) :
    subspaceDensityFinset U D = density (subspacePullback U D) := by
  rw [subspaceDensityFinset, pullbackFinset_eq_subspacePullback]

/-- Relative density inside the density API's image is the same expression
with the tiling API's tile. -/
theorem subspaceDensityFinset_eq_relative_subspacePoints
    [Fintype (eta → alpha)] [DecidableEq (iota → alpha)]
    (U : Subspace eta alpha iota) (D : Finset (iota → alpha)) :
    subspaceDensityFinset U D = relativeDensityFinset D (subspacePoints U) := by
  rw [subspaceDensityFinset_eq_relative,
    subspaceImageFinset_eq_subspacePoints]
  congr

/-- The iteration module's specialized pullback is the canonical density
pullback. -/
@[simp] theorem iterationPullback_eq_pullbackFinset {d t n : ℕ}
    (U : Subspace (Fin d) (Fin t) (Fin n)) (A : Finset (Word t n)) :
    iterationPullback U A = pullbackFinset U A := by
  classical
  ext x
  simp

/-- Direct compatibility between the iteration and tiling pullback names. -/
theorem iterationPullback_eq_subspacePullback {d t n : ℕ}
    (U : Subspace (Fin d) (Fin t) (Fin n)) (A : Finset (Word t n)) :
    iterationPullback U A = subspacePullback U A := by
  rw [iterationPullback_eq_pullbackFinset,
    pullbackFinset_eq_subspacePullback]

end SubspaceAPIs

section AlphabetInclusion

variable {eta : Type*} {k : ℕ}

/-- The older finite-word name and the generic sum-coordinate name for the
alphabet inclusion agree.  The orientation makes mixed files normalize to
`liftWord`. -/
@[simp] theorem restrictWord_eq_liftWord {m : ℕ} (x : Word k m) :
    restrictWord x = liftWord x :=
  rfl

/-- Exact density after including a finset into the alphabet with one new
letter.  Its cardinality is unchanged, but the uniform ambient denominator is
the cardinality of the enlarged word cube. -/
theorem density_liftFinset_exact
    [Fintype (eta → Fin (k + 1))] [DecidableEq (eta → Fin (k + 1))]
    (A : Finset (eta → Fin k)) :
    density (liftFinset A) =
      (A.card : ℝ) / Fintype.card (eta → Fin (k + 1)) := by
  rw [density_eq_card_div_card, card_liftFinset]

/-- Natural-number specialization of `density_liftFinset_exact`: the new
ambient cube has exactly `(k+1)^m` words. -/
theorem density_liftFinset_fin_exact {m : ℕ} (A : Finset (Word k m)) :
    density (liftFinset A) = (A.card : ℝ) / (k + 1) ^ m := by
  rw [density_liftFinset_exact]
  simp [Word]

/-- The numerator in the preceding formula is unchanged. -/
theorem card_liftFinset_exact
    [DecidableEq (eta → Fin (k + 1))] (A : Finset (eta → Fin k)) :
    (liftFinset A).card = A.card :=
  card_liftFinset A

end AlphabetInclusion

end Erdos171
