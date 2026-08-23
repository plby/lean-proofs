/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Util.Density

/-!
# Lower-density interface for Erdős Problem 822

Problem 822 uses the repository's canonical density definitions.  In
particular, the corrected target is Set.lowerDensity, the liminf of the
finite partial densities.  Keeping this small re-export avoids duplicating
the same declarations and permits reuse of neighboring checked sieve files
which already import Util.Density.
-/
