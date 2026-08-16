import ErdosProblems.Erdos965.FiniteColoring
import ErdosProblems.Erdos965.HamelTransfer

open Function Set

namespace Erdos965

noncomputable section

/-! The finite-support form of Komjáth's anti-Ramsey coloring. -/

theorem supportColor_finset_pair_antiramsey :
    finset_pair_antiramsey supportColor := by
  classical
  intro T hT
  obtain ⟨n, hI⟩ :=
    uncountable_fiber_of_countable_range (fun s : Finset HamelIndex ↦ s.card) hT
  let I : Set (Finset HamelIndex) := {s ∈ T | s.card = n}
  let ι := I
  let F : ι → Finset HamelIndex := fun s ↦ s.1
  have hcard : ∀ s : ι, (F s).card = n := fun s ↦ s.2.2
  have hι : ¬ (Set.univ : Set ι).Countable := by
    intro hu
    apply hI
    rw [← Set.countable_coe_iff]
    exact Set.countable_univ_iff.mp hu
  obtain ⟨W, hWuniv⟩ :=
    exists_uniformPrefixWitness F hcard hι
  obtain ⟨D, ND⟩ :=
    FiniteColoring.exists_coordinateNormalization_of_uniformPrefixWitness F hcard W
  let p : Fin n → ι → HamelIndex := fun j s ↦ finsetCoord F hcard s j
  let M : Finset (Fin n) := Finset.univ.filter fun j ↦ InjOn (p j) D
  have hM_inj : ∀ j ∈ M, InjOn (p j) D := by
    intro j hj
    simpa [M] using (Finset.mem_filter.mp hj).2
  have hconst : ∀ j ∉ M, ∃ c, ∀ s ∈ D, p j s = c := by
    intro j hj
    have hjnot : ¬ InjOn (p j) D := by
      intro hinj
      apply hj
      simp [M, hinj]
    rcases ND.normalized j with hconst | hinj
    · exact hconst
    · exact (hjnot hinj.1).elim
  have hMne : M.Nonempty := by
    by_contra hMempty
    have hMempty' : M = ∅ := Finset.not_nonempty_iff_eq_empty.mp hMempty
    have hDne : D.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      exact ND.uncountable (h ▸ Set.countable_empty)
    obtain ⟨s₀, hs₀⟩ := hDne
    apply ND.uncountable
    refine (Set.countable_singleton s₀).mono ?_
    intro s hs
    have hFs : F s = F s₀ :=
      finset_eq_of_all_coords_eq F hcard fun j ↦ by
        obtain ⟨c, hc⟩ := hconst j (by simp [hMempty'])
        exact (hc s hs).trans (hc s₀ hs₀).symm
    have : s = s₀ := Subtype.ext hFs
    exact Set.mem_singleton_iff.mpr this
  obtain ⟨S⟩ := exists_finiteSplitWitness p D M ND.uncountable hM_inj
  have hleftD : S.left ⊆ D := S.left_subset
  have hrightD : S.right ⊆ D := S.right_subset
  have hleftW : S.left ⊆ W.carrier :=
    S.left_subset.trans ND.subset
  have hrightW : S.right ⊆ W.carrier :=
    S.right_subset.trans ND.subset
  have hleftne : S.left.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact S.left_uncountable (h ▸ Set.countable_empty)
  have hrightne : S.right.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact S.right_uncountable (h ▸ Set.countable_empty)
  let aBase : ι := hleftne.choose
  have haBase : aBase ∈ S.left := hleftne.choose_spec
  let bBase : ι := hrightne.choose
  have hbBase : bBase ∈ S.right := hrightne.choose_spec
  have hlevel_ge : ∀ j ∈ M, W.L ≤ S.level j := by
    intro j hj
    have hpneq : p j aBase ≠ p j bBase := by
      rcases (S.split j hj).2 with hord | hord
      · exact (hord aBase haBase bBase hbBase).ne
      · exact (hord aBase haBase bBase hbBase).ne.symm
    have hprefix :
        PiNat.res (binaryCode (p j aBase)) W.L =
          PiNat.res (binaryCode (p j bBase)) W.L := by
      exact (W.prefix_eq aBase (hleftW haBase) j).trans
        (W.prefix_eq bBase (hrightW hbBase) j).symm
    have hle : W.L ≤ firstDiff (p j aBase) (p j bBase) := by
      apply (PiNat.mem_cylinder_iff_le_firstDiff (binaryCode_ne hpneq) W.L).1
      exact PiNat.res_eq_res.mp hprefix
    rw [(S.split j hj).1 aBase haBase bBase hbBase] at hle
    exact hle
  let levels : Finset ℕ := M.image S.level
  have hlevels : levels.Nonempty := hMne.image _
  let m : ℕ := levels.max' hlevels
  have hmlevels : m ∈ levels := Finset.max'_mem levels hlevels
  obtain ⟨j₀, hj₀M, hj₀m⟩ := Finset.mem_image.mp hmlevels
  let C : Finset (Fin n) := M.filter fun j ↦ S.level j = m
  have hC : C.Nonempty := by
    refine ⟨j₀, ?_⟩
    exact Finset.mem_filter.mpr ⟨hj₀M, hj₀m⟩
  let jstar : Fin n := C.min' hC
  have hjstarC : jstar ∈ C := Finset.min'_mem C hC
  have hjstarM : jstar ∈ M := (Finset.mem_filter.mp hjstarC).1
  have hjstarm : S.level jstar = m := (Finset.mem_filter.mp hjstarC).2
  have hlevel_le : ∀ j ∈ M, S.level j ≤ S.level jstar := by
    intro j hj
    rw [hjstarm]
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
  have hjstarleast :
      ∀ j ∈ M, S.level j = S.level jstar → jstar ≤ j := by
    intro j hjM hjlevel
    apply Finset.min'_le
    exact Finset.mem_filter.mpr ⟨hjM, hjlevel.trans hjstarm⟩
  have hcrit : ∀ {a b : ι}, a ∈ S.left → b ∈ S.right →
      criticalPair (F a ∪ F b) =
        (min (p jstar a) (p jstar b), max (p jstar a) (p jstar b)) := by
    intro a b ha hb
    exact criticalPair_crossUnion F hcard W ND.subset hconst S hjstarM
      hlevel_le hlevel_ge hjstarleast ha hb
  have hjstarLower :
      ∀ x ∈ D, {y ∈ D | WellOrderingRel (p jstar y) (p jstar x)}.Countable := by
    rcases ND.normalized jstar with hc | hi
    · have hinj := hM_inj jstar hjstarM
      obtain ⟨c, hc⟩ := hc
      obtain ⟨x₀, hx₀⟩ := hleftne
      exfalso
      apply ND.uncountable
      refine (Set.countable_singleton x₀).mono ?_
      intro x hx
      have hpx : p jstar x = p jstar x₀ :=
        (hc x hx).trans (hc x₀ (hleftD hx₀)).symm
      exact Set.mem_singleton_iff.mpr (hinj hx (hleftD hx₀) hpx)
    · exact hi.2
  have hjstarInj : InjOn (p jstar) D := hM_inj jstar hjstarM
  obtain ⟨a₀, ha₀⟩ := hleftne
  obtain ⟨b₀, hb₀, hb₀not⟩ :=
    exists_mem_not_mem_of_uncountable_of_countable S.right_uncountable
      (hjstarLower a₀ (hleftD ha₀))
  have hp₀ne : p jstar a₀ ≠ p jstar b₀ := by
    rcases (S.split jstar hjstarM).2 with hord | hord
    · exact (hord a₀ ha₀ b₀ hb₀).ne
    · exact (hord a₀ ha₀ b₀ hb₀).ne.symm
  have hW₀ : WellOrderingRel (p jstar a₀) (p jstar b₀) := by
    rcases trichotomous_of WellOrderingRel (p jstar a₀) (p jstar b₀) with h | h | h
    · exact h
    · exact (hp₀ne h).elim
    · exact (hb₀not ⟨hrightD hb₀, h⟩).elim
  obtain ⟨b₁, hb₁⟩ := hrightne
  obtain ⟨a₁, ha₁, ha₁not⟩ :=
    exists_mem_not_mem_of_uncountable_of_countable S.left_uncountable
      (hjstarLower b₁ (hrightD hb₁))
  have hp₁ne : p jstar a₁ ≠ p jstar b₁ := by
    rcases (S.split jstar hjstarM).2 with hord | hord
    · exact (hord a₁ ha₁ b₁ hb₁).ne
    · exact (hord a₁ ha₁ b₁ hb₁).ne.symm
  have hW₁ : WellOrderingRel (p jstar b₁) (p jstar a₁) := by
    rcases trichotomous_of WellOrderingRel (p jstar b₁) (p jstar a₁) with h | h | h
    · exact h
    · exact (hp₁ne h.symm).elim
    · exact (ha₁not ⟨hleftD ha₁, h⟩).elim
  have hcard_union : ∀ {a b : ι}, a ∈ S.left → b ∈ S.right →
      2 ≤ (F a ∪ F b).card := by
    intro a b ha hb
    rcases (S.split jstar hjstarM).2 with hord | hord
    · have h : 1 < (F a ∪ F b).card := Finset.one_lt_card.mpr
        ⟨p jstar a, Finset.mem_union_left _ (finsetCoord_mem F hcard a jstar),
          p jstar b, Finset.mem_union_right _ (finsetCoord_mem F hcard b jstar),
          (hord a ha b hb).ne⟩
      omega
    · have h : 1 < (F a ∪ F b).card := Finset.one_lt_card.mpr
        ⟨p jstar b, Finset.mem_union_right _ (finsetCoord_mem F hcard b jstar),
          p jstar a, Finset.mem_union_left _ (finsetCoord_mem F hcard a jstar),
          (hord a ha b hb).ne⟩
      omega
  have ha₀T : F a₀ ∈ T := a₀.2.1
  have hb₀T : F b₀ ∈ T := b₀.2.1
  have ha₁T : F a₁ ∈ T := a₁.2.1
  have hb₁T : F b₁ ∈ T := b₁.2.1
  refine ⟨F a₀, ha₀T, F b₀, hb₀T, F a₁, ha₁T, F b₁, hb₁T, ?_, ?_, ?_⟩
  · intro hab
    exact hp₀ne (congrArg (fun s ↦ finsetCoord (fun t : ι ↦ t.1) hcard s jstar)
      (Subtype.ext hab))
  · intro hab
    exact hp₁ne (congrArg (fun s ↦ finsetCoord (fun t : ι ↦ t.1) hcard s jstar)
      (Subtype.ext hab))
  · rcases (S.split jstar hjstarM).2 with hord | hord
    · have hord₀ := hord a₀ ha₀ b₀ hb₀
      have hord₁ := hord a₁ ha₁ b₁ hb₁
      have hc₀ : supportColor (F a₀ ∪ F b₀) = 0 :=
        supportColor_eq_zero_of_criticalPair (hcard_union ha₀ hb₀)
          (by simpa [min_eq_left hord₀.le, max_eq_right hord₀.le] using hcrit ha₀ hb₀) hW₀
      have hc₁ : supportColor (F a₁ ∪ F b₁) = 1 :=
        supportColor_eq_one_of_criticalPair (hcard_union ha₁ hb₁)
          (by simpa [min_eq_left hord₁.le, max_eq_right hord₁.le] using hcrit ha₁ hb₁)
          (fun h ↦
            (show WellFounded WellOrderingRel from IsWellFounded.wf).asymmetric
              _ _ h hW₁)
      simp [hc₀, hc₁]
    · have hord₀ := hord a₀ ha₀ b₀ hb₀
      have hord₁ := hord a₁ ha₁ b₁ hb₁
      have hc₀ : supportColor (F a₀ ∪ F b₀) = 1 :=
        supportColor_eq_one_of_criticalPair (hcard_union ha₀ hb₀)
          (by simpa [min_eq_right hord₀.le, max_eq_left hord₀.le] using hcrit ha₀ hb₀)
          (fun h ↦
            (show WellFounded WellOrderingRel from IsWellFounded.wf).asymmetric
              _ _ h hW₀)
      have hc₁ : supportColor (F a₁ ∪ F b₁) = 0 :=
        supportColor_eq_zero_of_criticalPair (hcard_union ha₁ hb₁)
          (by simpa [min_eq_right hord₁.le, max_eq_left hord₁.le] using hcrit ha₁ hb₁) hW₁
      simp [hc₀, hc₁]

end

end Erdos965
