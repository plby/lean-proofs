import StackExchange.Puzzling139335.JordanSubarc

/-!
# Initial subarcs and branch selection

An arc has a nondegenerate initial subarc avoiding any other prescribed point.
If such a subarc lies on a Jordan curve cut at its first endpoint and the avoided
point, connectedness puts the entire subarc on one side of that cut.
-/

open Set

namespace Schoenflies

/-- A short initial subarc avoids any point other than its first endpoint. -/
theorem IsArcBetween.exists_subarc_avoiding_point {A : Set Plane} {v a b : Plane}
    (hA : IsArcBetween A v a) (hvb : v ≠ b) :
    ∃ U u, IsArcBetween U v u ∧ U ⊆ A ∧ b ∉ U := by
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hA
  have hshort : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ b ∉ f '' Icc 0 δ := by
    by_cases hbA : b ∈ A
    · obtain ⟨β, hβ, hfβ⟩ : b ∈ f '' unitInterval := hfim.symm ▸ hbA
      have hβpos : 0 < β := by
        by_contra hβpos
        have hβ0 : β = 0 := le_antisymm (le_of_not_gt hβpos) hβ.1
        apply hvb
        calc
          v = f 0 := hf0.symm
          _ = f β := by rw [hβ0]
          _ = b := hfβ
      refine ⟨β / 2, by linarith, by linarith [hβ.2], ?_⟩
      rintro ⟨s, hs, hfs⟩
      have hsI : s ∈ unitInterval := ⟨hs.1, by linarith [hs.2, hβ.2]⟩
      have hsβ : s = β := hfi hsI hβ (hfs.trans hfβ.symm)
      linarith [hs.2]
    · refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
      intro hb
      apply hbA
      rw [← hfim]
      exact image_mono (Icc_subset_Icc le_rfl (by norm_num : (1 / 2 : ℝ) ≤ 1)) hb
  obtain ⟨δ, hδpos, hδ1, hδb⟩ := hshort
  refine ⟨f '' Icc 0 δ, f δ, ?_, ?_, hδb⟩
  · have h := isArcBetween_subarc_of_injOn_I hfc hfi zero_mem_I
      ⟨hδpos.le, hδ1⟩ hδpos.ne
    simpa only [uIcc_of_le hδpos.le, hf0] using h
  · rw [← hfim]
    exact image_mono (Icc_subset_Icc le_rfl hδ1)

/-- An arc beginning at one cut point and avoiding the other is wholly
contained in one of the two cut-pair arcs. -/
theorem IsCutPair.endpoint_subarc_subset_or {C D E U : Set Plane} {v b u : Plane}
    (hcut : IsCutPair C v b D E) (hU : IsArcBetween U v u) (hUC : U ⊆ C)
    (hbU : b ∉ U) : U ⊆ D ∨ U ⊆ E := by
  have hsub : U \ {v, u} ⊆ D ∪ E := by
    intro x hx
    rw [hcut.union_eq]
    exact hUC hx.1
  have hdis : Disjoint ((U \ {v, u}) ∩ D) ((U \ {v, u}) ∩ E) := by
    apply Set.disjoint_left.mpr
    intro x hxD hxE
    have hxpair : x ∈ ({v, b} : Set Plane) :=
      hcut.inter_eq ▸ (show x ∈ D ∩ E from ⟨hxD.2, hxE.2⟩)
    rcases mem_insert_iff.mp hxpair with hxv | hxb
    · exact hxD.1.2 (Or.inl hxv)
    · have hxb' := mem_singleton_iff.mp hxb
      exact hbU (hxb' ▸ hxD.1.1)
  have hchoice : U \ {v, u} ⊆ D ∨ U \ {v, u} ⊆ E := by
    by_cases hD : U \ {v, u} ⊆ D
    · exact Or.inl hD
    obtain ⟨x, hx, hxD⟩ := Set.not_subset.mp hD
    have hxE := (hsub hx).resolve_left hxD
    refine Or.inr ?_
    intro z hz
    by_contra hzE
    have hzD := (hsub hz).resolve_right hzE
    obtain ⟨w, hw, hwD, hwE⟩ := isPreconnected_closed_iff.mp hU.isPreconnected_diff
      D E hcut.fst.isArc.isClosed hcut.snd.isArc.isClosed hsub ⟨z, hz, hzD⟩ ⟨x, hx, hxE⟩
    exact Set.disjoint_left.mp hdis ⟨hw, hwD⟩ ⟨hw, hwE⟩
  have extend_subset {K : Set Plane} (hK : IsClosed K) (hUK : U \ {v, u} ⊆ K) : U ⊆ K := by
    intro x hx
    apply closure_minimal hUK hK
    by_cases hxends : x ∈ ({v, u} : Set Plane)
    · rcases mem_insert_iff.mp hxends with rfl | hxu
      · exact hU.left_mem_closure_diff
      · obtain rfl := mem_singleton_iff.mp hxu
        exact hU.right_mem_closure_diff
    · exact subset_closure ⟨hx, hxends⟩
  exact hchoice.imp (extend_subset hcut.fst.isArc.isClosed)
    (extend_subset hcut.snd.isArc.isClosed)

end Schoenflies
