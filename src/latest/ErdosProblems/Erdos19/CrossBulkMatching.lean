import ErdosProblems.Erdos19.CrossMatchings
import ErdosProblems.Erdos19.InducedMatchingMerge
import ErdosProblems.Erdos19.ParityCorrections

/-! # Coverage accounting after merging exceptional and bulk matchings -/

namespace Erdos19

open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V I : Type*} (X : Set V) (active : X → Finset I)

def bulkForbidden (partner : ActiveRequest active → V) (C : I → Set V) (i : I) : Set ↥(Xᶜ) :=
  {v | v.1 ∈ C i ∨ v.1 ∈ partnerVertices X active partner i}

theorem crossMatching_touches_outliers (G : _root_.SimpleGraph V)
    (partner : ActiveRequest active → V)
    (hadj : ∀ e, G.Adj (requestSource X active e) (partner e)) (i : I) (x y : V)
    (hxy : (crossMatching X active G partner hadj i).Adj x y) : x ∈ X ∨ y ∈ X := by
  obtain ⟨e, _, h | h⟩ := (crossMatching_adj X active G partner hadj i x y).mp hxy
  · exact Or.inl (h.1 ▸ e.1.1.2)
  · exact Or.inr (h.1 ▸ e.1.1.2)

theorem exists_merged_cross_bulk_matchings [Fintype V] [Fintype I]
    (G : _root_.SimpleGraph V) (partner : ActiveRequest active → V)
    (hadj : ∀ e, G.Adj (requestSource X active e) (partner e))
    (hout : ∀ e, partner e ∉ X)
    (hproper : ∀ e f, e ≠ f → (e.1.1 = f.1.1 ∨ e.1.2 = f.1.2) → partner e ≠ partner f)
    (C : I → Set V) (hactive : ∀ u i, i ∈ active u → u.1 ∉ C i)
    (hpartner : ∀ e, partner e ∉ C e.1.2)
    (U : Set V) (f : I → ↥(Xᶜ)) (hf : Function.Injective f) (hfU : ∀ i, (f i).1 ∈ U)
    (B : I → (G.induce Xᶜ).Subgraph)
    (hB : ∀ i, (B i).IsMatching ∧
      (B i).verts = auxiliaryTarget (bulkForbidden X active partner C i) (f i))
    (hBd : Pairwise (fun i j ↦ Disjoint (B i).spanningCoe (B j).spanningCoe)) :
    ∃ M : I → G.Subgraph,
      (∀ i, (M i).IsMatching ∧ (M i).verts ⊆ (C i)ᶜ) ∧
      Pairwise (fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe) ∧
      (∀ u : X, (∑ i : I, if u.1 ∈ (M i).verts then 1 else 0) = (active u).card) ∧
      (∀ v, v ∉ X → (∑ i : I, if v ∈ (M i).verts then 0 else 1) ≤
        (∑ i : I, if v ∈ C i then 1 else 0) + if v ∈ U then 1 else 0) := by
  classical
  let P := crossMatching X active G partner hadj
  let M : I → G.Subgraph := fun i ↦ P i ⊔ inducedMatchingLift G X (B i)
  have hP (i : I) : (P i).IsMatching :=
    crossMatching_isMatching X active G partner hadj hout
      (fun e f hef hi ↦ hproper e f hef (Or.inr hi)) i
  have hPd := crossMatching_pairwise_disjoint X active G partner hadj hout hproper
  have havoidP (i : I) : (P i).verts ⊆ (C i)ᶜ :=
    crossMatching_avoids X active G partner hadj C hactive hpartner i
  have havoidB (i : I) (v : ↥(Xᶜ)) (hv : v ∈ (B i).verts) :
      v.1 ∉ C i ∧ v.1 ∉ partnerVertices X active partner i := by
    rw [(hB i).2] at hv
    have h := auxiliaryTarget_subset _ _ hv
    exact ⟨fun hc ↦ h (Or.inl hc), fun hp ↦ h (Or.inr hp)⟩
  obtain ⟨hM, hMd⟩ := merge_induced_matching_families G X P B hP (fun i ↦ (hB i).1)
    hPd hBd (crossMatching_touches_outliers X active G partner hadj) (by
      intro i v hv hp
      exact (havoidB i v hv).2
        ((crossMatching_mem_of_not_outlier X active G partner hadj i v.2).mp hp))
  refine ⟨M, ?_, hMd, ?_, ?_⟩
  · intro i
    refine ⟨hM i, ?_⟩
    intro v hv
    rcases hv with hp | hb
    · exact havoidP i hp
    · obtain ⟨hn, hb⟩ := (inducedMatchingLift_mem G X (B i) v).mp hb
      exact (havoidB i ⟨v, hn⟩ hb).1
  · intro u
    have hmem (i : I) : u.1 ∈ (M i).verts ↔ i ∈ active u :=
      (merge_induced_mem_of_outlier G X (P i) (B i) u.2).trans
        (crossMatching_mem_of_outlier X active G partner hadj hout i u)
    simp [hmem]
  · intro v hv
    have hcover (i : I) (hc : v ∉ C i) (hf' : v ≠ (f i).1) : v ∈ (M i).verts := by
      apply (merge_induced_mem_of_not_outlier G X (P i) (B i) hv).mpr
      by_cases hp : v ∈ partnerVertices X active partner i
      · exact Or.inl ((crossMatching_mem_of_not_outlier X active G partner hadj i hv).mpr hp)
      · right
        rw [(hB i).2]
        apply subset_auxiliaryTarget
        refine ⟨?_, ?_⟩
        · exact fun h ↦ h.elim hc hp
        · intro heq
          exact hf' (congrArg Subtype.val heq)
    have hper (i : I) : (if v ∈ (M i).verts then 0 else 1) ≤
        (if v ∈ C i then 1 else 0) + (if (f i).1 = v then 1 else 0) := by
      by_cases hc : v ∈ C i
      · simp only [hc, ↓reduceIte]; split_ifs <;> omega
      · by_cases heq : (f i).1 = v
        · simp only [heq, hc, ↓reduceIte]; split_ifs <;> omega
        · have hm := hcover i hc (Ne.symm heq)
          simp only [hm, ↓reduceIte, Nat.zero_le]
    have hfval : Function.Injective (fun i ↦ (f i).1) := Subtype.val_injective.comp hf
    have hfiber : (∑ i : I, if (f i).1 = v then 1 else 0) ≤ if v ∈ U then 1 else 0 := by
      by_cases hu : v ∈ U
      · rw [if_pos hu]
        simp only [Finset.sum_boole]
        apply Finset.card_le_one.mpr
        intro i hi j hj
        exact hfval ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
      · have hne : ∀ i, (f i).1 ≠ v := fun i heq ↦ hu (heq ▸ hfU i)
        simp only [hne, hu, ↓reduceIte, Finset.sum_const_zero, le_refl]
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset I)) ↦ hper i)
    rw [Finset.sum_add_distrib] at hs
    exact hs.trans (Nat.add_le_add_left hfiber _)

#print axioms exists_merged_cross_bulk_matchings

end Erdos19
