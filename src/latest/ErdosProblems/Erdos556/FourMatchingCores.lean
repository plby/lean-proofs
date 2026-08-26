import ErdosProblems.Erdos556.ProfileRefinement
import ErdosProblems.Erdos556.CleanProfileSystem

/-! Assembling refinements at the four even vertices of the cube. -/

namespace Erdos556

open SimpleGraph Finset

structure FourMatchingCores {V : Type*} [DecidableEq V]
    (c : ThreeColouring V) (L d : ℕ) where
  profiles : Fin 4 → CubeProfile
  cores : Fin 4 → Finset V
  dimension : ∀ l, profileDimension (profiles l) = 1
  profile_disjoint : ∀ l m, l ≠ m → Disjoint (profileVertices (profiles l)) (profileVertices (profiles m))
  core_disjoint : ∀ l m, l ≠ m → Disjoint (cores l) (cores m)
  large : ∀ l, L ≤ (cores l).card
  dense : ∀ l m i, uniqueProfileSeparator (profiles l) (profiles m) i →
    BipartiteDefect (c.graph i) (cores l) (cores m) d

theorem four_matching_cores_of_refinements {V : Type*} [DecidableEq V]
    {c : ThreeColouring V} {n L : ℕ} {η : ℝ} (h : CleanProfileSystem c n η)
    (href : ∀ p, 0 < h.weight p →
      Nonempty (ProfileRefinement c p (h.sets p) L h.defect)) :
    Nonempty (FourMatchingCores c L h.defect) := by
  classical
  have hex (l : Fin 4) : ∃ p : CubeProfile, 0 < h.weight p ∧ evenCubeVertex l ∈ profileVertices p := by
    have hh : evenCubeVertex l ∈ (positiveCubeProfiles h.weight).biUnion profileVertices := by
      rw [h.tiling.cover h.admissible]
      exact mem_univ _
    obtain ⟨p, hp, hmem⟩ := mem_biUnion.mp hh
    exact ⟨p, (mem_filter.mp hp).2, hmem⟩
  choose p hp hmem using hex
  let P : Fin 4 → {q : CubeProfile // 0 < h.weight q} := fun l => ⟨p l, hp l⟩
  let R (q : {q : CubeProfile // 0 < h.weight q}) :
      ProfileRefinement c q.val (h.sets q.val) L h.defect := Classical.choice (href q.val q.property)
  have hmemP (l : Fin 4) : evenCubeVertex l ∈ profileVertices (P l).val := hmem l
  have hneq (l m : Fin 4) (hne : P l ≠ P m) : (P l).val ≠ (P m).val :=
    fun he => hne (Subtype.ext he)
  refine ⟨{
    profiles := fun l => matchingProfile l (R (P l)).direction
    cores := fun l => (R (P l)).cores l
    dimension := fun l => matchingProfile_dimension l _
    profile_disjoint := ?_
    core_disjoint := ?_
    large := fun l => (R (P l)).large l (hmemP l)
    dense := ?_ }⟩
  · intro l m hlm
    by_cases he : P l = P m
    · have hm : evenCubeVertex m ∈ profileVertices (P l).val := by rw [he]; exact hmemP m
      rw [← he]
      exact (R (P l)).profile_disjoint l m hlm (hmemP l) hm
    · exact (h.tiling.disjoint _ _ (hneq l m he) (P l).property (P m).property).mono
        ((R (P l)).subprofile l (hmemP l)) ((R (P m)).subprofile m (hmemP m))
  · intro l m hlm
    by_cases he : P l = P m
    · have hm : evenCubeVertex m ∈ profileVertices (P l).val := by rw [he]; exact hmemP m
      rw [← he]
      exact (R (P l)).core_disjoint l m hlm (hmemP l) hm
    · exact (h.disjoint _ _ (hneq l m he)).mono
        ((R (P l)).subset l (hmemP l)) ((R (P m)).subset m (hmemP m))
  · intro l m i hsep
    by_cases he : P l = P m
    · have hm : evenCubeVertex m ∈ profileVertices (P l).val := by rw [he]; exact hmemP m
      rw [← he] at hsep ⊢
      exact (R (P l)).dense l m (hmemP l) hm i hsep
    · have hparent := unique_separator_of_disjoint_parent (P l).val (P m).val _ _ i
        (h.tiling.disjoint _ _ (hneq l m he) (P l).property (P m).property)
        ((R (P l)).subprofile l (hmemP l)) ((R (P m)).subprofile m (hmemP m)) hsep
      exact (h.dense _ _ i hparent).mono
        ((R (P l)).subset l (hmemP l)) ((R (P m)).subset m (hmemP m))

#print axioms four_matching_cores_of_refinements

end Erdos556
