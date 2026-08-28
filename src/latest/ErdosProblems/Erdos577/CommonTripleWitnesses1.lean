import ErdosProblems.Erdos577.CommonTripleMasks1

/-! Explicit common-neighbor replacements and matching gains for Wang 3.3. -/

namespace Erdos577.CommonTriple.D1

open Finset

private theorem witness_0 : Positive 1 14464 := by
  left
  refine ⟨7, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_1 : Positive 1 21024 := by
  left
  refine ⟨5, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_2 : Positive 1 22656 := by
  left
  refine ⟨7, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_3 : Positive 1 26752 := by
  left
  refine ⟨7, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_4 : Positive 1 37408 := by
  left
  refine ⟨5, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_5 : Positive 1 41232 := by
  left
  refine ⟨4, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_6 : Positive 1 42048 := by
  left
  refine ⟨6, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_7 : Positive 1 49696 := by
  left
  refine ⟨5, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

theorem masks_sound {m : ℕ} (h : m ∈ masks) : Positive 1 m := by
  simp only [masks, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_0
  · exact witness_1
  · exact witness_2
  · exact witness_3
  · exact witness_4
  · exact witness_5
  · exact witness_6
  · exact witness_7

theorem finite_classification (m : Fin 65536) (hh : Hypotheses m.val) :
    Positive 1 m.val ∨ Conclusion m.val := by
  rcases Bool.or_eq_true_iff.mp (coverage m hh) with hp | hc
  · obtain ⟨w, hw, hsub⟩ := List.any_eq_true.mp hp
    exact Or.inl ((masks_sound hw).mono (beq_iff_eq.mp hsub))
  · exact Or.inr (of_decide_eq_true hc)

end Erdos577.CommonTriple.D1
