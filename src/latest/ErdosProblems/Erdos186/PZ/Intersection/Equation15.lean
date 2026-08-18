/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.StructureTheorem

/-!
# The finite subset-sum content of Pham--Zakharov equation (15)

The geometric argument preceding equation (15) has two logically distinct
outputs.  Rounding a zonotope point gives a subset sum of a `core`, with an
integer error in a prescribed translate of a dilated GAP.  The structure
theorem says that every point of that translated GAP is a subset sum of a
small `reserved` set.  Provided the two pieces are disjoint, the two subset
sum witnesses can be united without multiplicities.

This file records exactly that finite last step.  In particular,
`RoundingErrorsAbsorbedBy` does **not** assert that its target is contained in
any subset-sum set: it only locates the residual error after choosing a core
subset.  Theorems `equation15` and `equation15_of_cfpWitness` derive the
subset-sum inclusion from that residual-error assertion and the independent
GAP-coverage assertion.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

/-- `RoundingErrorsAbsorbedBy target core errors` is the finite output of the
zonotope-rounding and error-absorption estimates: every target lattice point
can be rounded to a subset sum of `core`, and the remaining integer error
belongs to `errors`.

This is deliberately weaker than a subset-sum inclusion.  No subset of the
reserved set, and no representation of the error as a subset sum, occurs in
the definition. -/
def RoundingErrorsAbsorbedBy {d : ℕ}
    (target core errors : Finset (LatticePoint d)) : Prop :=
  ∀ z ∈ target, ∃ T ⊆ core, z - ∑ x ∈ T, x ∈ errors

/-- The residual-error formulation can equivalently be written as an
additive decomposition of the target point. -/
theorem roundingErrorsAbsorbedBy_iff {d : ℕ}
    {target core errors : Finset (LatticePoint d)} :
    RoundingErrorsAbsorbedBy target core errors ↔
      ∀ z ∈ target, ∃ T ⊆ core, ∃ e ∈ errors,
        e + ∑ x ∈ T, x = z := by
  constructor
  · intro h z hz
    obtain ⟨T, hT, he⟩ := h z hz
    exact ⟨T, hT, z - ∑ x ∈ T, x, he, sub_add_cancel z _⟩
  · intro h z hz
    obtain ⟨T, hT, e, he, hsum⟩ := h z hz
    refine ⟨T, hT, ?_⟩
    have : e = z - ∑ x ∈ T, x := by
      rw [eq_sub_iff_add_eq]
      exact hsum
    simpa [← this] using he

/-- **Pham--Zakharov equation (15), finite GAP form.**

Suppose zonotope rounding leaves, after a core subset sum, an error in a
translate of a dilated GAP.  Suppose independently that the translated GAP
is covered by subset sums of a reserved set.  If the reserved and core sets
are disjoint, every target point is a subset sum of their union.

The disjointness hypothesis is essential: `GAP.subsetSums` uses finsets, so
an element present in both witnesses cannot in general be used twice. -/
theorem equation15 {d r k : ℕ}
    {target reserved core : Finset (LatticePoint d)}
    {P : GAP d r} {translatePoint : LatticePoint d}
    (hdisjoint : Disjoint reserved core)
    (hround : RoundingErrorsAbsorbedBy target core
      (CFP.translate translatePoint (P.dilate k).carrier))
    (hcovered :
      CFP.translate translatePoint (P.dilate k).carrier ⊆
        GAP.subsetSums reserved) :
    target ⊆ GAP.subsetSums (reserved ∪ core) := by
  intro z hz
  obtain ⟨T, hTcore, herror⟩ := hround z hz
  obtain ⟨R, hRreserved, hRsum⟩ :=
    GAP.mem_subsetSums_iff.mp (hcovered herror)
  have hRT : Disjoint R T := hdisjoint.mono hRreserved hTcore
  apply GAP.mem_subsetSums_iff.mpr
  refine ⟨R ∪ T, ?_, ?_⟩
  · exact Finset.union_subset
      (hRreserved.trans Finset.subset_union_left)
      (hTcore.trans Finset.subset_union_right)
  · rw [Finset.sum_union hRT, hRsum]
    exact sub_add_cancel z _

/-- Version of equation (15) whose GAP coverage is supplied directly by a
`CFP.CFPWitness`.  The `roundingCore` is the portion retained for zonotope
rounding after removing the witness's reserved elements; it need not be the
CFP witness's `core` field. -/
theorem equation15_of_cfpWitness {d s D k loss : ℕ}
    {A : Finset (LatticePoint d)}
    (W : CFP.CFPWitness A s D k loss)
    {target roundingCore : Finset (LatticePoint d)}
    (hdisjoint : Disjoint W.reserved roundingCore)
    (hround : RoundingErrorsAbsorbedBy target roundingCore
      (CFP.translate W.translatePoint
        (W.progression.dilate k).carrier)) :
    target ⊆ GAP.subsetSums (W.reserved ∪ roundingCore) := by
  exact equation15 hdisjoint hround W.covered

/-- Equation (15) in the ambient-set form used in the intersection
argument.  When both the reserved and rounding-core pieces lie in `A`, the
union inclusion above and monotonicity of subset sums place every target
point in `GAP.subsetSums A`. -/
theorem equation15_subsetSums_of_parts {d r k : ℕ}
    {A target reserved core : Finset (LatticePoint d)}
    {P : GAP d r} {translatePoint : LatticePoint d}
    (hreserved : reserved ⊆ A) (hcore : core ⊆ A)
    (hdisjoint : Disjoint reserved core)
    (hround : RoundingErrorsAbsorbedBy target core
      (CFP.translate translatePoint (P.dilate k).carrier))
    (hcovered :
      CFP.translate translatePoint (P.dilate k).carrier ⊆
        GAP.subsetSums reserved) :
    target ⊆ GAP.subsetSums A := by
  exact (equation15 hdisjoint hround hcovered).trans
    (CFP.subsetSums_mono (Finset.union_subset hreserved hcore))

/-- Ambient-set specialization backed by a `CFP.CFPWitness`.  Only the
rounding core's inclusion in the original set remains to be supplied,
because the witness already proves that its reserved set is contained in
`A`. -/
theorem equation15_subsetSums_of_cfpWitness {d s D k loss : ℕ}
    {A : Finset (LatticePoint d)}
    (W : CFP.CFPWitness A s D k loss)
    {target roundingCore : Finset (LatticePoint d)}
    (hcore : roundingCore ⊆ A)
    (hdisjoint : Disjoint W.reserved roundingCore)
    (hround : RoundingErrorsAbsorbedBy target roundingCore
      (CFP.translate W.translatePoint
        (W.progression.dilate k).carrier)) :
    target ⊆ GAP.subsetSums A := by
  exact (equation15_of_cfpWitness W hdisjoint hround).trans
    (CFP.subsetSums_mono
      (Finset.union_subset W.reserved_subset hcore))

end

end Erdos186.PZ.Intersection
