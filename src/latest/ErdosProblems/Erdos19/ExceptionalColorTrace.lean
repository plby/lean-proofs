import ErdosProblems.Erdos19.Core

/-! # At most one color can occupy most of a buffer

Classes that are not singletons have small coverage. Two distinct singleton
edges meet in at most one vertex, so they cannot both occupy more than half
of the buffer with a margin of one vertex.
-/

namespace Erdos19.SetHypergraph

variable {V C : Type*} [Fintype V]

theorem coveredVertices_eq_of_singleton_family (H : SetHypergraph V)
    (S : Set H) (hS : S.ncard ≤ 1) (e : H) (he : e ∈ S) :
    H.coveredVertices S = e.1 := by
  ext v
  constructor
  · intro hv
    obtain ⟨f, hf⟩ := Set.mem_iUnion.mp hv
    obtain ⟨hfS, hvf⟩ := Set.mem_iUnion.mp hf
    exact ((Set.ncard_le_one_iff_subsingleton.mp hS) hfS he) ▸ hvf
  · intro hv
    exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨he, hv⟩⟩

theorem exists_singleton_class_of_large_trace (H : SetHypergraph V)
    (c : H → C) (A : ℕ) (hbounded : H.IsCoverBoundedColoring c A)
    (Y : Set V) (hA : 2 * A ≤ Y.ncard + 1) (a : C)
    (ha : Y.ncard + 1 < 2 * (Y ∩ H.coveredVertices {e | c e = a}).ncard) :
    ∃ e : H, c e = a ∧ H.coveredVertices {f | c f = a} = e.1 := by
  have hsmall : ({e : H | c e = a} : Set H).ncard ≤ 1 := by
    rcases hbounded a with hs | hc
    · exact hs
    · have htrace := (Set.ncard_le_ncard
        (show Y ∩ H.coveredVertices {e | c e = a} ⊆ H.coveredVertices {e | c e = a}
          from Set.inter_subset_right)).trans hc
      omega
  have hpos : 0 < (Y ∩ H.coveredVertices {e | c e = a}).ncard := by omega
  obtain ⟨v, _, hv⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp hv
  obtain ⟨hea, _⟩ := Set.mem_iUnion.mp he
  exact ⟨e, hea, H.coveredVertices_eq_of_singleton_family _ hsmall e hea⟩

theorem linear_edge_trace_sum_le (H : SetHypergraph V) (hlinear : H.IsLinear)
    (Y : Set V) (e f : H) (hef : e ≠ f) :
    (Y ∩ e.1).ncard + (Y ∩ f.1).ncard ≤ Y.ncard + 1 := by
  have hsub : (Y ∩ e.1) ∪ (Y ∩ f.1) ⊆ Y := Set.union_subset
    Set.inter_subset_left Set.inter_subset_left
  have hinter : ((Y ∩ e.1) ∩ (Y ∩ f.1)).Subsingleton := by
    intro v hv w hw
    exact hlinear e.2 f.2 (fun h ↦ hef (Subtype.ext h))
      ⟨hv.1.2, hv.2.2⟩ ⟨hw.1.2, hw.2.2⟩
  have hcard := Set.ncard_union_add_ncard_inter (Y ∩ e.1) (Y ∩ f.1)
  have hunion := Set.ncard_le_ncard hsub
  have hi := Set.ncard_le_one_iff_subsingleton.mpr hinter
  omega

theorem large_trace_colors_subsingleton (H : SetHypergraph V) (hlinear : H.IsLinear)
    (c : H → C) (A : ℕ) (hbounded : H.IsCoverBoundedColoring c A)
    (Y : Set V) (hA : 2 * A ≤ Y.ncard + 1) :
    ({a : C | Y.ncard + 1 <
      2 * (Y ∩ H.coveredVertices {e | c e = a}).ncard} : Set C).Subsingleton := by
  intro a ha b hb
  obtain ⟨e, hea, heCover⟩ := H.exists_singleton_class_of_large_trace c A hbounded Y hA a ha
  obtain ⟨f, hfb, hfCover⟩ := H.exists_singleton_class_of_large_trace c A hbounded Y hA b hb
  by_contra hab
  have hef : e ≠ f := fun h ↦ hab (hea.symm.trans ((congrArg c h).trans hfb))
  have hsum := H.linear_edge_trace_sum_le hlinear Y e f hef
  change Y.ncard + 1 < 2 * (Y ∩ H.coveredVertices {e | c e = a}).ncard at ha
  change Y.ncard + 1 < 2 * (Y ∩ H.coveredVertices {e | c e = b}).ncard at hb
  rw [heCover] at ha
  rw [hfCover] at hb
  omega

#print axioms large_trace_colors_subsingleton

end Erdos19.SetHypergraph
