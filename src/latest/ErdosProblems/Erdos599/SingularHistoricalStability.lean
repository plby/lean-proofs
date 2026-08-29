/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularJointFullRow
import ErdosProblems.Erdos599.SingularHistoricalClosure

/-!
# The exact same-column obstruction in historical singular rows

`SingularHistoricalClosure` removes the cross-column `+1` mismatch by
closing sources under every finite row history.  Its remaining premise says
that all rows accumulated in one column form a warp.  Since every historical
row already has the *full ambient source* as its initial set, that premise is
equivalent to literal equality of every row in the column.

Thus historical closure does not permit a sequence of mutually compatible
fresh rows: it requires one row, selected at stage zero, to serve unchanged
at every later request stage.  This is the sharp obstruction to replacing
forward extension by a plain union of independently selected histories.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularHistoricalStability

open SingularJointFullRow SingularHistoricalClosure SingularMatrix

universe u

variable {V : Type u}
variable {G : DWeb V} {fixed : Set G.DPath}
variable {A₀ : Set V} {kappa : Cardinal.{u}}
variable {huncountable : Cardinal.aleph0 < kappa}
variable {hsingular : kappa.IsSingular} {hcard : #A₀ = kappa}

/-- A warp union of two historical full-source rows identifies the rows. -/
theorem paths_eq_of_columnPaths_isWarp
    (R : HistoricalRows G fixed A₀ kappa
      huncountable hsingular hcard)
    (i : Index kappa)
    (hcolumn : G.IsWarp (columnPaths R.paths i))
    (m n : ℕ) :
    R.paths i m = R.paths i n := by
  apply eq_of_union_isWarp_of_initialSet_eq_source G
    (R.initialSet i m) (R.initialSet i n)
  intro p hp q hq hpq
  rcases hp with hpm | hpn <;> rcases hq with hqm | hqn
  · exact hcolumn (Set.mem_iUnion.2 ⟨m, hpm⟩)
      (Set.mem_iUnion.2 ⟨m, hqm⟩) hpq
  · exact hcolumn (Set.mem_iUnion.2 ⟨m, hpm⟩)
      (Set.mem_iUnion.2 ⟨n, hqn⟩) hpq
  · exact hcolumn (Set.mem_iUnion.2 ⟨n, hpn⟩)
      (Set.mem_iUnion.2 ⟨m, hqm⟩) hpq
  · exact hcolumn (Set.mem_iUnion.2 ⟨n, hpn⟩)
      (Set.mem_iUnion.2 ⟨n, hqn⟩) hpq

/-- The same-column union-warp premise is exactly literal constancy of the
row sequence. -/
theorem columnPaths_isWarp_iff_constant
    (R : HistoricalRows G fixed A₀ kappa
      huncountable hsingular hcard)
    (i : Index kappa) :
    G.IsWarp (columnPaths R.paths i) ↔
      ∀ n, R.paths i n = R.paths i 0 := by
  constructor
  · intro hcolumn n
    exact paths_eq_of_columnPaths_isWarp R i hcolumn n 0
  · intro hconstant
    have hcolumnEq : columnPaths R.paths i = R.paths i 0 := by
      apply Set.Subset.antisymm
      · intro p hp
        obtain ⟨n, hpn⟩ := Set.mem_iUnion.1 hp
        rw [hconstant n] at hpn
        exact hpn
      · intro p hp
        exact Set.mem_iUnion.2 ⟨0, hp⟩
    rw [hcolumnEq]
    exact R.isWarp i 0

/-- Under the union-warp premise, the entire historical column is already
its stage-zero row. -/
theorem columnPaths_eq_zero_of_warp
    (R : HistoricalRows G fixed A₀ kappa
      huncountable hsingular hcard)
    (i : Index kappa)
    (hcolumn : G.IsWarp (columnPaths R.paths i)) :
    columnPaths R.paths i = R.paths i 0 := by
  apply Set.Subset.antisymm
  · intro p hp
    obtain ⟨n, hpn⟩ := Set.mem_iUnion.1 hp
    rw [paths_eq_of_columnPaths_isWarp R i hcolumn n 0] at hpn
    exact hpn
  · intro p hp
    exact Set.mem_iUnion.2 ⟨0, hp⟩

/-- Hence the historical limit does not synthesize a new compatible row:
the literal stage-zero row must already link every source ever added to its
column. -/
theorem zeroRow_links_limit
    (R : HistoricalRows G fixed A₀ kappa
      huncountable hsingular hcard)
    (hNorm : G.IsNormalized) (i : Index kappa)
    (hcolumn : G.IsWarp (columnPaths R.paths i)) :
    LinksToTarget G (R.paths i 0)
      (limitSources R.sources i) := by
  rw [← columnPaths_eq_zero_of_warp R i hcolumn]
  exact R.columnPaths_links hNorm i

/-- Consequently the historical adapter's geometric premise can be stated
without unions: every column must have selected the same full-source row at
all finite stages. -/
theorem all_columnPaths_isWarp_iff_constant
    (R : HistoricalRows G fixed A₀ kappa
      huncountable hsingular hcard) :
    (∀ i, G.IsWarp (columnPaths R.paths i)) ↔
      ∀ i n, R.paths i n = R.paths i 0 := by
  constructor
  · intro h i
    exact (columnPaths_isWarp_iff_constant R i).1 (h i)
  · intro h i
    exact (columnPaths_isWarp_iff_constant R i).2 (h i)

#print axioms paths_eq_of_columnPaths_isWarp
#print axioms columnPaths_isWarp_iff_constant
#print axioms zeroRow_links_limit
#print axioms all_columnPaths_isWarp_iff_constant

end SingularHistoricalStability
end CardinalInduction
end Erdos599
