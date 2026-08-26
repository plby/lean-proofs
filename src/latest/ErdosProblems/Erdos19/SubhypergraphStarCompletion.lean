import ErdosProblems.Erdos19.StarCoverCompletion

/-! # Completing a colored subhypergraph across pair stars -/

namespace Erdos19.SetHypergraph

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

theorem reserved_usedColorsOn_card_le (H : SetHypergraph V) (hlinear : H.IsLinear)
    (S : Finset H) {C : Type*} [DecidableEq C] (c : H → C) (reserved : Finset C)
    (r : ℕ) (hr : 2 ≤ r)
    (hmin : ∀ e ∈ S, c e ∈ reserved → r ≤ e.1.ncard) (v : V) :
    (reserved ∩ H.usedColorsOn S c v).card ≤ (Fintype.card V - 1) / (r - 1) := by
  classical
  let I := S.filter fun e ↦ c e ∈ reserved ∧ v ∈ e.1
  have hsub : reserved ∩ H.usedColorsOn S c v ⊆ I.image c := by
    intro a ha
    obtain ⟨haR, haUsed⟩ := mem_inter.mp ha
    obtain ⟨e, he, hv, hea⟩ := (H.mem_usedColorsOn S c v a).mp haUsed
    refine mem_image.mpr ⟨e, mem_filter.mpr ⟨he, ?_, hv⟩, hea⟩
    simpa only [hea] using haR
  have hI : I.card ≤ (Fintype.card V - 1) / (r - 1) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < r - 1)).mpr
    have h := H.incidentSubfamily_ncard_mul_sub_one_le hlinear (I : Set H) v r
      (fun e he ↦ (mem_filter.mp he).2.2)
      (fun e he ↦ hmin e (mem_filter.mp he).1 (mem_filter.mp he).2.1)
    simpa only [Set.ncard_coe_finset] using h
  exact (card_le_card hsub).trans (card_image_le.trans hI)

theorem exists_coloring_completing_pair_stars (H J : SetHypergraph V)
    (hlinear : H.IsLinear) (hmin : ∀ e : H, 2 ≤ e.1.ncard)
    (n : ℕ) (hn : 0 < n) (hvertices : Fintype.card V = n)
    (color : J.EdgeColoring (Fin n)) (U : Finset V)
    (hmissing : ∀ e ∈ H, e ∉ J → e.ncard = 2 ∧ ∃ v ∈ U, v ∈ e)
    (reserved : Finset (Fin n)) (A r : ℕ) (hr : 2 ≤ r)
    (hcover : ∀ a, (J.coveredVertices {e | color e = a}).ncard ≤ A)
    (hreserveRank : ∀ e : J, color e ∈ reserved → r ≤ e.1.ncard)
    (hslack : A + 2 * ((n - 1) / (r - 1)) + 4 * U.card ≤ reserved.card) :
    ∃ c : H.EdgeColoring (Fin n), ∀ e : H, ∀ he : e.1 ∈ J, c e = color ⟨e.1, he⟩ := by
  classical
  let S : Finset H := univ.filter fun e ↦ e.1 ∈ J
  let T := univ \ S
  let c₀ : H → Fin n := fun e ↦ if he : e.1 ∈ J then color ⟨e.1, he⟩ else ⟨0, hn⟩
  have hpartial (e : H) (he : e ∈ S) :
      c₀ e = color ⟨e.1, (mem_filter.mp he).2⟩ := by
    simp only [c₀, dif_pos (mem_filter.mp he).2]
  have hproper : H.IsProperOn S c₀ := by
    intro e he f hf hef hinter
    rw [hpartial e he, hpartial f hf]
    apply color.valid _ hinter
    intro h
    exact hef (Subtype.ext (congrArg (fun z : J ↦ z.1) h))
  have hpartialCover : ∀ a, (H.coveredVertices {e | e ∈ S ∧ c₀ e = a}).ncard ≤ A := by
    intro a
    apply le_trans (Set.ncard_le_ncard (t := J.coveredVertices {e | color e = a}) ?_)
      (hcover a)
    intro v hv
    simp only [coveredVertices, Set.mem_iUnion, Set.mem_ofPred_eq] at hv ⊢
    obtain ⟨e, ⟨he, hecolor⟩, hve⟩ := hv
    exact ⟨⟨e.1, (mem_filter.mp he).2⟩, (hpartial e he).symm.trans hecolor, hve⟩
  have hreserved : ∀ v, (reserved ∩ H.usedColorsOn S c₀ v).card ≤
      (n - 1) / (r - 1) := by
    intro v
    conv_rhs => rw [← hvertices]
    apply H.reserved_usedColorsOn_card_le hlinear S c₀ reserved r hr
    intro e he hcolor
    apply hreserveRank ⟨e.1, (mem_filter.mp he).2⟩
    simpa only [hpartial e he] using hcolor
  have hTmissing : ∀ e ∈ T, e.1.ncard = 2 ∧ ∃ v ∈ U, v ∈ e.1 := by
    intro e he
    apply hmissing e.1 e.2
    intro hJ
    exact (mem_sdiff.mp he).2 (mem_filter.mpr ⟨mem_univ _, hJ⟩)
  obtain ⟨c, hagree⟩ := H.exists_coloring_of_star_cover hlinear hmin n hvertices reserved U S T
    (disjoint_left.mpr (fun _ he ht ↦ (mem_sdiff.mp ht).2 he))
    (union_sdiff_of_subset (subset_univ _))
    (fun e he ↦ (hTmissing e he).1) (fun e he ↦ (hTmissing e he).2)
    c₀ hproper A ((n - 1) / (r - 1)) hpartialCover
    (fun _ _ v _ ↦ hreserved v) hslack
  refine ⟨c, ?_⟩
  intro e he
  have heS : e ∈ S := mem_filter.mpr ⟨mem_univ _, he⟩
  exact (hagree e heS).trans (hpartial e heS)

#print axioms reserved_usedColorsOn_card_le
#print axioms exists_coloring_completing_pair_stars

end Erdos19.SetHypergraph
