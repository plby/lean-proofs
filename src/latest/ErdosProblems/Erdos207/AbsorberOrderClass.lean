/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AbsorberNontrivialFamily
import ErdosProblems.Erdos207.TerminalConfigurationCount

/-! # Actual forbidden order classes lie in the induced families -/

namespace Erdos207

open Finset

noncomputable section

theorem forbiddenFamilyOfOrder_subset_absorberInduced
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {q j : ℕ} {B : TripleSystemOn V}
    (hF : F ⊆ absorberErdosForbiddenConfigurationsOn q B) (hj : 4 ≤ j) :
    forbiddenFamilyOfOrder F j ⊆ absorberInducedConfigurationsOn q j B := by
  intro E hE
  have hd := mem_forbiddenFamilyOfOrder.mp hE
  have hc : 2 ≤ E.card := by omega
  obtain ⟨i, hi4, _, hi⟩ := mem_absorberNontrivialInducedFamily.mp
    (mem_absorberNontrivialInducedFamily_of_card_ge_two (hF hd.1) hc)
  have hsize := (mem_absorberInducedConfigurationsOn_iff.mp hi).1
  have heq : i = j := by omega
  exact heq ▸ hi

end

end Erdos207
