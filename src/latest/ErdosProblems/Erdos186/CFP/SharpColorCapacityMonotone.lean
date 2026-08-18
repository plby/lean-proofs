/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.SharpColorCapacityNumerics

/-!
# Monotone sharp-colouring capacity

The blocked reserve construction uses a population cap smaller than the
canonical sharp-colouring cap.  The additive capacity estimate is monotone
in this cap, so the same source cutoff applies without changing the event
term.
-/

namespace Erdos186.CFP.RandomPartition

noncomputable section

set_option autoImplicit false

/-- The sharp additive-capacity cutoff also controls every smaller
population cap. -/
theorem exists_cutoff_sharpColorCapacity_of_le
    (q C0 E H : ℕ) (eta : ℝ)
    (hq : 0 < q) (hC0 : 0 < C0) (heta : 0 < eta) :
    ∃ cutoff : ℕ, 2 ≤ cutoff ∧
      ∀ {m n s cap : ℕ}, cutoff ≤ m →
        Nat.log 2 n + 1 ≤ H * (Nat.log 2 m + 1) →
        Real.rpow (m : ℝ) eta ≤ (s : ℝ) →
        cap ≤ colorCap s q C0 →
        (2 * q + 1) *
            ((cap + 1) +
              (Nat.log 2 ((n ^ E + 1) * (q + 1)) + 1)) ≤
          s / C0 + 1 := by
  obtain ⟨cutoff, hcutoff, hcapacity⟩ :=
    exists_cutoff_sharpColorCapacity q C0 E H eta hq hC0 heta
  refine ⟨cutoff, hcutoff, ?_⟩
  intro m n s cap hm hlog hscale hcap
  apply (Nat.mul_le_mul_left (2 * q + 1) ?_).trans
    (hcapacity hm hlog hscale)
  exact Nat.add_le_add_right (Nat.add_le_add_right hcap 1)
    (Nat.log 2 ((n ^ E + 1) * (q + 1)) + 1)

end

end Erdos186.CFP.RandomPartition

#print axioms
  Erdos186.CFP.RandomPartition.exists_cutoff_sharpColorCapacity_of_le
