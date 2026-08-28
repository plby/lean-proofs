import ErdosProblems.Erdos577.TripleCoreWitnessData

/-! Every one of the forty-eight literal table entries supplies the full U, V or C hypothesis. -/

namespace Erdos577.TripleCorePatterns

open Finset UniversalTriple

theorem u_case (tag : Fin 12) (j : Fin 4) (hk : kind tag j = 0) :
    UCase (paw tag) block (marked j) (first tag j) (second tag j) := by
  have hu := u_data tag j hk
  refine {
    triangle := by simpa [triple, center, hk, paw, Paw.center] using triangle_clique tag j
    subset := by
      rw [paw_core]
      simpa [triple, center, hk, paw, Paw.center] using hu.1
    bridge := hu.2
    complement_quad := by
      rw [paw_core]
      simpa [target, triple, center, hk, paw, Paw.center] using quad_on tag j 0
    complement_score := by
      rw [paw_core]
      simpa [target, triple, center, hk, paw, Paw.center] using complement_score tag j
    final_quad := by
      rw [paw_core]
      simpa [target, center, hk, paw, Paw.center] using quad_on tag j 1
    left_quad := by
      rw [paw_core]
      simpa [target, center, hk, paw, Paw.center] using quad_on tag j 2
    right_quad := by
      rw [paw_core]
      simpa [target, center, hk, paw, Paw.center] using quad_on tag j 3 }

theorem v_case (tag : Fin 12) (j : Fin 4) (hk : kind tag j = 1) :
    VCase (paw tag) block (marked j) (first tag j) (second tag j) := by
  have hv := v_data tag j hk
  refine {
    triangle := by simpa [triple, center, hk, paw, Paw.center] using triangle_clique tag j
    subset := by
      rw [paw_core]
      simpa [triple, center, hk, paw, Paw.center] using hv.1
    bridge := hv.2
    complement_quad := by
      rw [paw_core]
      simpa [target, triple, center, hk, paw, Paw.center] using quad_on tag j 0
    complement_score := by
      rw [paw_core]
      simpa [target, triple, center, hk, paw, Paw.center] using complement_score tag j
    final_quad := by
      rw [paw_core]
      simpa [target, center, hk, paw, Paw.center] using quad_on tag j 1
    left_quad := by
      rw [paw_core]
      simpa [target, center, hk, paw, Paw.center] using quad_on tag j 2
    right_quad := by
      rw [paw_core]
      simpa [target, center, hk, paw, Paw.center] using quad_on tag j 3 }

theorem c_case (tag : Fin 12) (j : Fin 4) (hk : kind tag j = 2) :
    CCase (paw tag) block (marked j) (first tag j) (second tag j) := by
  have hc := c_data tag j hk
  refine {
    first_mem := hc.1
    second_mem := hc.2.1
    marked_mem := hc.2.2.1
    triangle := by simpa [triple, center, hk, paw, Paw.center] using triangle_clique tag j
    complement_quad := by
      rw [paw_core]
      simpa [target, triple, center, hk, paw, Paw.center] using quad_on tag j 0
    complement_score := by
      rw [paw_core]
      simpa [target, triple, center, hk, paw, Paw.center] using complement_score tag j
    core_budget := by
      rw [paw_core]
      simpa [triple, center, hk, paw, Paw.center] using hc.2.2.2 }

theorem witness (tag : Fin 12) (j : Fin 4) :
    UCase (paw tag) block (marked j) (first tag j) (second tag j) ∨
      VCase (paw tag) block (marked j) (first tag j) (second tag j) ∨
      CCase (paw tag) block (marked j) (first tag j) (second tag j) := by
  have hcases : kind tag j = 0 ∨ kind tag j = 1 ∨ kind tag j = 2 := by omega
  rcases hcases with h | h | h
  · exact Or.inl (u_case tag j h)
  · exact Or.inr (Or.inl (v_case tag j h))
  · exact Or.inr (Or.inr (c_case tag j h))

end Erdos577.TripleCorePatterns
