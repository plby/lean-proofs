/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.NegateWitness
import ErdosProblems.Erdos186.PZ.Intersection.ProgressionContainment

/-!
# Negation invariance of the source control box

The selector is run on `A₂ - a`, while the second intersection side uses
`a - A₂`.  Negating the selected witness therefore also negates its
containing translate.  The source control box is centred at zero, so the
same box controls the negated progression.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

@[simp] theorem neg_mem_controlIntegerBox_iff
    {ambient d : ℕ} (P : GAP ambient d) (m : ℕ)
    (x : LatticePoint d) :
    -x ∈ (controlIntegerBox P m).carrier ↔
      x ∈ (controlIntegerBox P m).carrier := by
  simp only [CFP.IntegerBox.mem_carrier_iff, controlIntegerBox, Pi.neg_apply]
  constructor
  · intro h i
    have hi := h i
    constructor <;> omega
  · intro h i
    have hi := h i
    constructor <;> omega

@[simp] theorem image_neg_controlIntegerBox
    {ambient d : ℕ} (P : GAP ambient d) (m : ℕ) :
    (controlIntegerBox P m).carrier.image (fun x ↦ -x) =
      (controlIntegerBox P m).carrier := by
  classical
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (neg_mem_controlIntegerBox_iff P m y).2 hy
  · intro hx
    exact ⟨-x, (neg_mem_controlIntegerBox_iff P m x).2 hx, by simp⟩

/-- A progression controlled by a translate of the source box remains
controlled after negating both the progression and the translation. -/
theorem negatedGAP_carrier_subset_translate_controlIntegerBox
    {ambient d r : ℕ} (S : GAP ambient d) (m : ℕ)
    (P : GAP d r) (t : LatticePoint d)
    (hcontain : P.carrier ⊆
      CFP.translate t (controlIntegerBox S m).carrier) :
    (negatedGAP P).carrier ⊆
      CFP.translate (-t) (controlIntegerBox S m).carrier := by
  rw [negatedGAP.carrier]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, hyb⟩ := CFP.mem_translate_iff.mp (hcontain hy)
  apply CFP.mem_translate_iff.mpr
  refine ⟨-b, (neg_mem_controlIntegerBox_iff S m b).2 hb, ?_⟩
  rw [← hyb]
  abel

end

end Erdos186.PZ.Intersection
