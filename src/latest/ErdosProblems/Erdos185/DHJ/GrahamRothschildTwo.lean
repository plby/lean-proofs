/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos171.GrahamRothschild

/-!
# Graham--Rothschild for binary combinatorial lines

This is the binary specialization of the finite line-color
Graham--Rothschild theorem.  It is the Ramsey input used in the
density-increment proof of ternary density Hales--Jewett.
-/

namespace Erdos185.DHJ

open Combinatorics

/-- For every target dimension, some binary cube contains a subspace on
which every internal combinatorial line has the same Boolean color. -/
theorem binary_line_homogeneous (m : ℕ) :
    ∃ N : ℕ, ∀ c : Line (Fin 2) (Fin N) → Bool,
      ∃ U : Subspace (Fin m) (Fin 2) (Fin N), ∃ b : Bool,
        ∀ l : Line (Fin 2) (Fin m), c (U.lineMap l) = b :=
  Erdos171.GrahamRothschild.exists_mono_lines_fin (Fin 2) m

end Erdos185.DHJ
