/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 330, positive upper density formulation.
Informal authors: GPT-5.5 Pro, David Turturean.
Formal authors: Codex, GPT-5.5 Pro, Allen Graham Hart.
Source: https://www.erdosproblems.com/forum/thread/330#post-6271
https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/6160036caab0dcee80395ba3beb7b6ef2731604e/formalizations/erdos330
Original Lean/Mathlib version: 4.27.0.
-/
import ErdosProblems.Erdos330.ConcreteCRTGadget
import ErdosProblems.Erdos330.LocalReservoir

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Stage coverage wrappers for Erdős Problem 330

This file packages the local reservoir, middle-block, and canonical-tail
coverage lemmas in the forms used by the eventual one-stage construction.
-/

namespace Erdos330

open scoped Pointwise

theorem twoFoldFinset_subset_union_left {A B : Finset ℕ} :
    twoFoldFinset A ⊆ twoFoldFinset (A ∪ B) :=
  twoFoldFinset_mono Finset.subset_union_left

theorem twoFoldFinset_subset_union_right {A B : Finset ℕ} :
    twoFoldFinset B ⊆ twoFoldFinset (A ∪ B) :=
  twoFoldFinset_mono Finset.subset_union_right

theorem active_add_block_mem_twoFold_union {S B : Finset ℕ} {a p : ℕ}
    (haS : a ∈ S) (hpB : p ∈ B) :
    a + p ∈ twoFoldFinset (S ∪ B) := by
  exact ⟨a, Finset.mem_union.mpr (Or.inl haS), p, Finset.mem_union.mpr (Or.inr hpB), rfl⟩

theorem gadget_T_middle_cover_in_union (st : StageState) {a N L n : ℕ}
    [NeZero st.M] (G : CRTGadget st.P st.m st.M a st.D)
    (hML : st.M ≤ L) (hnlo : 2 * N + st.M ≤ n)
    (hnhi : n ≤ 2 * N + 2 * L - st.M)
    (hnot_private : (n : ZMod st.M) ∉
      ((fun x : ZMod st.M => (a : ZMod st.M) + x) '' (G.Pstar : Set (ZMod st.M)))) :
    n ∈ twoFoldFinset (st.S ∪ residueBlockFinset st.M G.T N (N + L)) := by
  exact twoFoldFinset_subset_union_right
    (gadget_T_middle_residueBlock_cover st G hML hnlo hnhi hnot_private)

theorem canonicalD_middle_cover_in_union (st : StageState) (hD : st.HasCanonicalD)
    {a N L n : ℕ} (ha : a ∈ st.P)
    (hML : st.M ≤ L) (hnlo : 2 * N + st.M ≤ n)
    (hnhi : n ≤ 2 * N + 2 * L - st.M) :
    n ∈ twoFoldFinset (st.S ∪ residueBlockFinset st.M st.D N (N + L)) := by
  exact twoFoldFinset_subset_union_right
    (canonicalD_middle_residueBlock_cover st hD ha hML hnlo hnhi)

end Erdos330
