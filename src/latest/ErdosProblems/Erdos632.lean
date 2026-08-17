/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos632.Uniformization

/-!
# Erdős Problem 632

A graph is `(a,b)`-choosable when every assignment of an `a`-element finite
list to each vertex admits a choice of `b` colours at every vertex, with
disjoint choices at adjacent vertices.  Erdős, Rubin, and Taylor asked whether
`(a,b)`-choosability always implies `(a*m,b*m)`-choosability for every positive
integer `m`.

Dvořák, Hu, and Sereni disproved this by constructing a finite graph which is
`4`-choosable but not `(8,2)`-choosable.  The imported development formalizes
their exact 37-vertex nonuniform gadget, its positive and negative lemmas, and
the final uniformization by a root `K₄`.

References:

* P. Erdős, A. L. Rubin, H. Taylor, *Choosability in graphs*, Congressus
  Numerantium XXVI (1980), 125–157.
* Z. Dvořák, X. Hu, J.-S. Sereni, *A 4-choosable graph that is not
  (8:2)-choosable*, Advances in Combinatorics 2019:5,
  doi:10.19086/aic.10811, arXiv:1806.03880v2.
-/

namespace Erdos632

/-- The universal scaling assertion asked in Erdős Problem 632, for finite
simple graphs and positive list parameters. -/
def Erdos632Conjecture : Prop :=
  ∀ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (a b m : ℕ),
    1 ≤ b → b ≤ a → 1 ≤ m →
      IsABChoosable.{0, 0} G a b →
        IsABChoosable.{0, 0} G (a * m) (b * m)

/-- The explicit Dvořák--Hu--Sereni graph is the required counterexample. -/
theorem erdos_632_counterexample :
    IsABChoosable.{0, 0} finalGraph 4 1 ∧
      ¬ IsABChoosable.{0, 0} finalGraph 8 2 :=
  finalGraph_counterexample

/-- Erdős Problem 632 has a negative answer. -/
theorem erdos_632 : ¬ Erdos632Conjecture := by
  intro h
  have hscaled : IsABChoosable.{0, 0} finalGraph (4 * 2) (1 * 2) :=
    h FinalVertex inferInstance finalGraph 4 1 2 (by decide) (by decide)
      (by decide) erdos_632_counterexample.1
  exact erdos_632_counterexample.2 (by simpa using hscaled)

#print axioms Erdos632.erdos_632

end Erdos632
