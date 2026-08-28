import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeCutBinary
import Mathlib.Algebra.BigOperators.Fin

/-!
# Finite coordinate cuts of actual native generalized loops

The recursive concatenation consists of the literal consecutive coordinate
slices. Repeated binary subdivision gives an actual relative homotopy from
the first-to-last slice to that concatenation. Endpoints zero and one then
recover the original cube, and native concatenation gives the finite sum.
-/

noncomputable section

open scoped Topology unitInterval BigOperators

namespace Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision

variable {N : Type*} [DecidableEq N]
variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The actual native concatenation of all consecutive coordinate slices. -/
def sliceConcat (p : GenLoop N X x) (i : N) :
    (k : ℕ) → (a : Fin (k + 1) → C(NativeCube N, I)) →
      (∀ j, CutBased p i (a j)) → GenLoop N X x
  | 0, _, _ => GenLoop.const
  | k + 1, a, ha => GenLoop.transAt i
      (sliceLoop p i (a 0) (a (0 : Fin (k + 1)).succ) (ha 0) (ha (0 : Fin (k + 1)).succ))
      (sliceConcat p i k (fun j => a j.succ) (fun j => ha j.succ))

/-- Every finite sequence of independent based cuts gives an actual relative homotopy. -/
theorem slice_homotopic_concat (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, I))
    (ha : ∀ j, CutBased p i (a j)) (hInd : ∀ j, CutIndependent i (a j)) :
    GenLoop.Homotopic (sliceLoop p i (a 0) (a (Fin.last k)) (ha 0) (ha (Fin.last k)))
      (sliceConcat p i k a ha) := by
  induction k with
  | zero =>
      change GenLoop.Homotopic (sliceLoop p i (a 0) (a 0) (ha 0) (ha 0)) GenLoop.const
      rw [sliceLoop_self]
  | succ k ih =>
      have ht := ih (fun j => a j.succ) (fun j => ha j.succ) (fun j => hInd j.succ)
      have hs := slice_homotopic_trans p i (a 0) (a (0 : Fin (k + 1)).succ)
        (a (Fin.last (k + 1))) (ha 0) (ha (0 : Fin (k + 1)).succ) (ha (Fin.last (k + 1)))
        (hInd 0) (hInd (0 : Fin (k + 1)).succ) (hInd (Fin.last (k + 1)))
      apply hs.trans
      apply slice_transAt_homotopic
      · exact GenLoop.Homotopic.refl _
      · exact ht

theorem sliceConcat_class [Nontrivial N] (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, I)) (ha : ∀ j, CutBased p i (a j)) :
    nativeClass (sliceConcat p i k a ha) =
      ∑ j : Fin k, nativeClass (sliceLoop p i (a j.castSucc) (a j.succ)
        (ha j.castSucc) (ha j.succ)) := by
  induction k with
  | zero => simp [sliceConcat]
  | succ k ih =>
      rw [sliceConcat, nativeClass_transAt, ih, Fin.sum_univ_succ]
      rfl

/-- Finite graph cuts with the actual endpoints zero and one recover the original cube. -/
theorem finiteCuts_homotopic (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, I))
    (ha : ∀ j, CutBased p i (a j)) (hInd : ∀ j, CutIndependent i (a j))
    (hzero : ∀ u, a 0 u = 0) (hone : ∀ u, a (Fin.last k) u = 1) :
    GenLoop.Homotopic p (sliceConcat p i k a ha) := by
  have h := slice_homotopic_concat p i k a ha hInd
  rwa [sliceLoop_full p i (a 0) (a (Fin.last k)) (ha 0) (ha (Fin.last k)) hzero hone] at h

/-- The native class is the sum of its actual consecutive coordinate slices. -/
theorem finiteCuts_class [Nontrivial N] (p : GenLoop N X x) (i : N) (k : ℕ)
    (a : Fin (k + 1) → C(NativeCube N, I))
    (ha : ∀ j, CutBased p i (a j)) (hInd : ∀ j, CutIndependent i (a j))
    (hzero : ∀ u, a 0 u = 0) (hone : ∀ u, a (Fin.last k) u = 1) :
    nativeClass p = ∑ j : Fin k, nativeClass (sliceLoop p i (a j.castSucc) (a j.succ)
      (ha j.castSucc) (ha j.succ)) :=
  (nativeClass_homotopic (finiteCuts_homotopic p i k a ha hInd hzero hone)).trans
    (sliceConcat_class p i k a ha)

end Wikipedia.HopfProblem.HigherHurewicz.NativeSubdivision
