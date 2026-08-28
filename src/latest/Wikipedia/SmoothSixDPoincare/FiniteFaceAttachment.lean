import Wikipedia.SmoothSixDPoincare.FaceAttachment
import Mathlib.Topology.Category.TopCat.Basic

/-!
# Finite attachment sequences with all original whole-piece maps retained

A sequence records the actual face maps and quotient homeomorphisms at each
stage. Changing its initial space changes only the first face map; the tail
and final space stay literally the same. The induced maps of every whole
attached piece into the final space are preserved pointwise.
-/

noncomputable section

open Set ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.FaceAttachment

/-- A finite sequence of genuine face attachments, with a terminal coordinate map. -/
inductive Chain : TopCat.{0} → TopCat.{0} → ℕ → Type 1
  | nil {X Z : TopCat.{0}} (r : X ≃ₜ Z) : Chain X Z 0
  | cons {X Y Z : TopCat.{0}} {n : ℕ} (K : TopCat.{0}) (B : Set K)
      (b : C(B, X)) (r : Space b ≃ₜ Y) (tail : Chain Y Z n) : Chain X Z (n + 1)

namespace Chain

variable {X Y Z : TopCat.{0}} {n : ℕ}

/-- Change only the initial space, keeping every later stage and attaching map. -/
def rebase (c : Chain X Z n) (e : X ≃ₜ Y) : Chain Y Z n :=
  match c with
  | .nil r => .nil (e.symm.trans r)
  | .cons K B b r tail =>
      .cons K B (e.toHomotopyEquiv.toFun.comp b) (changedRealization b e r) tail

/-- The complete map of the old space into the final stage. -/
def sourceMap : {X Z : TopCat.{0}} → {n : ℕ} → Chain X Z n → C(X, Z)
  | _, _, _, .nil r => r.toHomotopyEquiv.toFun
  | _, _, _, .cons _ _ b r tail =>
      tail.sourceMap.comp (r.toHomotopyEquiv.toFun.comp (oldMap b))

/-- The disjoint union of all whole attached pieces, with their original coordinates. -/
def pieces : {X Z : TopCat.{0}} → {n : ℕ} → Chain X Z n → TopCat.{0}
  | _, _, _, .nil _ => TopCat.of PEmpty
  | _, _, _, .cons K _ _ _ tail => TopCat.of (K ⊕ tail.pieces)

/-- All original whole-piece parametrizations into the final stage. -/
def piecesMap : {X Z : TopCat.{0}} → {n : ℕ} → (c : Chain X Z n) → C(c.pieces, Z)
  | _, _, _, .nil _ => ⟨PEmpty.elim, by fun_prop⟩
  | _, _, _, .cons _ _ b r tail =>
      ⟨Sum.elim (tail.sourceMap ∘ r ∘ handleMap b) tail.piecesMap,
        continuous_sum_dom.mpr
          ⟨tail.sourceMap.continuous.comp (r.continuous.comp (handleMap b).continuous),
            tail.piecesMap.continuous⟩⟩

/-- Rebasing retains the same whole-piece coordinates, not merely their homeomorphism types. -/
def rebasePieces (c : Chain X Z n) (e : X ≃ₜ Y) : c.pieces ≃ₜ (c.rebase e).pieces := by
  cases c <;> exact Homeomorph.refl _

theorem rebase_sourceMap (c : Chain X Z n) (e : X ≃ₜ Y) (y : Y) :
    (c.rebase e).sourceMap y = c.sourceMap (e.symm y) := by
  cases c with
  | nil r => rfl
  | cons K B b r tail =>
      exact congrArg tail.sourceMap (changedRealization_old b e r y)

theorem rebase_piecesMap (c : Chain X Z n) (e : X ≃ₜ Y) (z : c.pieces) :
    (c.rebase e).piecesMap (c.rebasePieces e z) = c.piecesMap z := by
  cases c with
  | nil r => exact PEmpty.elim z
  | cons K B b r tail =>
      cases z with
      | inl k => exact congrArg tail.sourceMap (changedRealization_handle b e r k)
      | inr z => rfl

end Chain

end Wikipedia.SmoothSixDPoincare.FaceAttachment
