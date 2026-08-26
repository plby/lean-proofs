import Mathlib
import ErdosProblems.Erdos336.ThickAbsorption
import ErdosProblems.Erdos336.PiecewiseBohrTransfer

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Abstract piecewise-patch transference master lemma
-/

namespace Erdos336

open PiecewiseBohrTransfer

private lemma rep_iff_zRep {D : Set ℤ} {k : ℕ} {n : ℤ} :
    Rep D k n ↔ ZRepExactly D k n := Iff.rfl

/-- Once the deep density/compact input has supplied a piecewise patch in
`2hD` and a finite exact-`M` family of shifts covering its factor, the removed
set has eventual exact order at most `M+3h`. -/
theorem eventuallyExactlyZ_of_piecewise_patch
    {K : Type*} {φ : ℤ → K} {U : Set K} {T P D : Set ℤ}
    {S : Finset ℤ} {c : ℤ} {h M : ℕ}
    (hzero : 0 ∈ D)
    (hparent : EventuallyWithOneExtra D c h)
    (hT : ThickZ T)
    (hpatch : ∀ n : ℤ, φ n ∈ U → n ∈ T → n ∈ P)
    (hcover : ∀ n : ℤ, ∃ s ∈ S, φ (n - s) ∈ U)
    (hPrep : ∀ p ∈ P, ZRepExactly D (2 * h) p)
    (hSrep : ∀ s ∈ S, ZRepExactly D M s) :
    EventuallyExactlyZ D (M + 3 * h) := by
  have hthickRep : RepThick D (2 * h + M) := by
    apply repThick_of_patch_cover hT hpatch hcover
    · intro p hp
      exact (rep_iff_zRep).mpr (hPrep p hp)
    · intro s hs
      exact (rep_iff_zRep).mpr (hSrep s hs)
  have hthick : ExactPowerThick D (2 * h + M) := by
    intro F
    obtain ⟨a, ha⟩ := hthickRep F
    exact ⟨a, fun x hx => (rep_iff_zRep).mp (ha x hx)⟩
  have hout := eventuallyExactlyZ_of_thick_of_oneExtra hzero hthick hparent
  convert hout using 1 <;> omega

end Erdos336
