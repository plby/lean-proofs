import ErdosProblems.Erdos577.JointCoreCandidates

/-! Small finite relabelings for the maximal core; all 128 row cases are kernel checked. -/

namespace Erdos577.JointCore.Refinement

open Finset
open scoped BigOperators

def rows (tag : Fin 8) (b : Fin 16) : Fin 4 → ℕ :=
  ![0, centerRow tag, b.val, thirdRow tag]

def count (tag : Fin 8) (b : Fin 16) (i : Fin 4) : ℕ :=
  ∑ j : Fin 4, ((rows tag b i).testBit j.val).toNat

def packed (tag : Fin 8) (b : Fin 16) : ℕ :=
  16 * centerRow tag + 256 * b.val + 4096 * thirdRow tag

def Allowed (tag : Fin 8) (b : Fin 16) : Prop :=
  ∀ j : Fin 4, ((secondLower tag).testBit j.val = true → b.val.testBit j.val = true) ∧
    (b.val.testBit j.val = true → (secondUpper tag).testBit j.val = true)

instance (tag : Fin 8) (b : Fin 16) : Decidable (Allowed tag b) :=
  inferInstanceAs (Decidable (∀ _ : Fin 4, _ ∧ _))

private def swap01 : Fin 4 ↪ Fin 4 := ⟨![1, 0, 2, 3], by decide +kernel⟩
private def swap12 : Fin 4 ↪ Fin 4 := ⟨![0, 2, 1, 3], by decide +kernel⟩
private def swap13 : Fin 4 ↪ Fin 4 := ⟨![0, 3, 2, 1], by decide +kernel⟩

def candidate (tag : Fin 8) (b : Fin 16) : Fin 8 × (Fin 4 ↪ Fin 4) :=
  if tag = 4 ∧ b ≠ 13 then (5, swap01)
  else if tag = 5 ∧ b = 13 then (5, swap12)
  else if tag = 1 ∧ b = 5 then (1, swap12)
  else if tag = 1 ∧ b = 9 then (1, swap13)
  else (tag, Function.Embedding.refl _)

def Accepted (tag : Fin 8) (b : Fin 16) : Prop :=
  let tag' := (candidate tag b).1
  let e := (candidate tag b).2
  FirstPaw.CycleOrder (diagonal tag) e ∧ Pattern tag' (diagonal tag) (packed tag b) e ∧
    tag' ≠ 2 ∧ tag' ≠ 3 ∧
    (tag' = 4 → (rows tag b 2).testBit (e 2).val = true ∧
      ∀ j : Fin 4, (rows tag b 2).testBit (e j).val = (rows tag b 1).testBit (e j).val) ∧
    (tag' = 5 → (rows tag b 2).testBit (e 1).val = true ∧
      ∃ j : Fin 4, (rows tag b 2).testBit (e j).val ≠ (rows tag b 1).testBit (e j).val) ∧
    (tag' = 1 → count tag b 2 = 2 →
      ∀ j : Fin 4, (rows tag b 2).testBit (e j).val = true ↔ j = 0 ∨ j = 1)

instance (tag : Fin 8) (b : Fin 16) : Decidable (Accepted tag b) :=
  inferInstanceAs (Decidable (_ ∧ _))

lemma packed_bit (tag : Fin 8) (b : Fin 16) (i j : Fin 4) :
    (packed tag b).testBit (4 * i.val + j.val) = (rows tag b i).testBit j.val := by
  have hf : ∀ tag : Fin 8, ∀ b : Fin 16, ∀ i j : Fin 4,
      (packed tag b).testBit (4 * i.val + j.val) = (rows tag b i).testBit j.val := by
    decide +kernel
  exact hf tag b i j

theorem finite_refinement (tag : Fin 8) (b : Fin 16) (h : Allowed tag b)
    (hseven : count tag b 1 + count tag b 3 = 7 →
      10 ≤ count tag b 1 + count tag b 2 + count tag b 3) : Accepted tag b := by
  have hf : ∀ tag : Fin 8, ∀ b : Fin 16, Allowed tag b →
      (count tag b 1 + count tag b 3 = 7 →
        10 ≤ count tag b 1 + count tag b 2 + count tag b 3) → Accepted tag b := by
    decide +kernel
  exact hf tag b h hseven

end Erdos577.JointCore.Refinement
