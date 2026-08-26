/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Integer-valued codes for prime-power classes and their refinement maps.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.ResidueImage

namespace Erdos477.Counting

def residueCode (p r : ℕ) (z : Fin 3 → ℤ) : Fin 3 → ℤ :=
  fun k => z k % (p : ℤ) ^ r

lemma residueCode_zero (p : ℕ) (z : Fin 3 → ℤ) : residueCode p 0 z = 0 := by
  ext k
  simp [residueCode]

lemma residueCode_refines (p r : ℕ) (z : Fin 3 → ℤ) :
    residueCode p r (residueCode p (r + 1) z) = residueCode p r z := by
  ext k
  exact Int.emod_emod_of_dvd _ (pow_dvd_pow _ (Nat.le_succ r))

lemma residueCode_eq_iff (p r : ℕ) (z w : Fin 3 → ℤ) :
    residueCode p r z = residueCode p r w ↔
      (fun k => (z k : ZMod (p ^ r))) = (fun k => (w k : ZMod (p ^ r))) := by
  constructor <;> intro h <;> ext k
  · apply (ZMod.intCast_eq_intCast_iff' _ _ _).mpr
    simpa only [residueCode, Nat.cast_pow] using congrFun h k
  · have hk := (ZMod.intCast_eq_intCast_iff' _ _ _).mp (congrFun h k)
    simpa only [residueCode, Nat.cast_pow] using hk

lemma card_residueCode_image_le (p r : ℕ) (hp : p ≠ 0) (S : Finset (Fin 3 → ℤ)) :
    (S.image (residueCode p r)).card ≤ (sexticResidueImage p r S).card := by
  classical
  let : NeZero (p ^ r) := ⟨pow_ne_zero r hp⟩
  have hrepr (z : Fin 3 → ℤ) :
      residueCode p r z = fun k => ((z k : ZMod (p ^ r)).val : ℤ) := by
    ext k
    simp only [residueCode, ZMod.val_intCast, Nat.cast_pow]
  have himage : S.image (residueCode p r) =
      (sexticResidueImage p r S).image
        (fun (a : Fin 3 → ZMod (p ^ r)) k => ((a k).val : ℤ)) := by
    simp only [sexticResidueImage, Finset.image_image]
    apply Finset.image_congr
    intro z _
    exact hrepr z
  rw [himage]
  exact Finset.card_image_le

#print axioms card_residueCode_image_le
-- 'Erdos477.Counting.card_residueCode_image_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
