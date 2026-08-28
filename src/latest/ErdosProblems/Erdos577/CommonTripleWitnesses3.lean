import ErdosProblems.Erdos577.CommonTripleMasks3

/-! Explicit common-neighbor replacements and matching gains for Wang 3.3. -/

namespace Erdos577.CommonTriple.D3

open Finset

private theorem witness_0 : Positive 3 13376 := by
  left
  refine ⟨6, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_1 : Positive 3 14464 := by
  left
  refine ⟨7, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_2 : Positive 3 21024 := by
  left
  refine ⟨5, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_3 : Positive 3 22656 := by
  left
  refine ⟨7, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_4 : Positive 3 24848 := by
  left
  refine ⟨4, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_5 : Positive 3 26752 := by
  left
  refine ⟨7, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_6 : Positive 3 37408 := by
  left
  refine ⟨5, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_7 : Positive 3 37952 := by
  left
  refine ⟨6, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_8 : Positive 3 41232 := by
  left
  refine ⟨4, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_9 : Positive 3 42048 := by
  left
  refine ⟨6, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_10 : Positive 3 49424 := by
  left
  refine ⟨4, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_11 : Positive 3 49696 := by
  left
  refine ⟨5, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

theorem masks_sound {m : ℕ} (h : m ∈ masks) : Positive 3 m := by
  simp only [masks, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_0
  · exact witness_1
  · exact witness_2
  · exact witness_3
  · exact witness_4
  · exact witness_5
  · exact witness_6
  · exact witness_7
  · exact witness_8
  · exact witness_9
  · exact witness_10
  · exact witness_11

theorem finite_classification (m : Fin 65536) (hh : Hypotheses m.val) :
    Positive 3 m.val ∨ Conclusion m.val := by
  rcases Bool.or_eq_true_iff.mp (coverage m hh) with hp | hc
  · obtain ⟨w, hw, hsub⟩ := List.any_eq_true.mp hp
    exact Or.inl ((masks_sound hw).mono (beq_iff_eq.mp hsub))
  · exact Or.inr (of_decide_eq_true hc)

end Erdos577.CommonTriple.D3
