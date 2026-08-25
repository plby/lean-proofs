import StackExchange.Puzzling139335.JordanArcGerms.Initial
import StackExchange.Puzzling139335.JordanArcGerms.Nested

/-!
# The two local branches of a Jordan curve

Two cuts of the same Jordan curve through a common point determine the same two
local boundary germs, up to exchanging their names.  An arbitrary incident arc
agrees locally with one of these branches.  Distinct incident arcs meeting only
at endpoints cannot have the same germ.
-/

open Set Puzzling139335

namespace Schoenflies

/-- Any incident arc on a Jordan curve has the germ of one of the branches
of a prescribed cut pair through its endpoint. -/
theorem IsCutPair.endpoint_arc_germ_eq_or {C A D E : Set Plane} {v a b : Plane}
    (hcut : IsCutPair C v b D E) (hA : IsArcBetween A v a) (hAC : A ⊆ C) :
    SameBoundaryGerm A D v ∨ SameBoundaryGerm A E v := by
  have hvb : v ≠ b := by
    obtain ⟨f, _, hi, _, h0, h1⟩ := hcut.fst
    intro heq
    exact zero_ne_one (hi zero_mem_I one_mem_I (h0.trans (heq.trans h1.symm)))
  obtain ⟨U, u, hU, hUA, hbU⟩ := hA.exists_subarc_avoiding_point hvb
  have hAU := nested_arcs_sameBoundaryGerm hA hU hUA
  rcases hcut.endpoint_subarc_subset_or hU (hUA.trans hAC) hbU with hUD | hUE
  · exact Or.inl (hAU.trans (nested_arcs_sameBoundaryGerm hcut.fst hU hUD).symm)
  · exact Or.inr (hAU.trans (nested_arcs_sameBoundaryGerm hcut.snd hU hUE).symm)

/-- Once the first branches of two cuts through a common point have the same
germ, their remaining branches also have the same germ. -/
theorem IsCutPair.sameBoundaryGerm_snd_of_fst {C A B D E : Set Plane} {v a b : Plane}
    (h : IsCutPair C v a A B) (h' : IsCutPair C v b D E)
    (hAD : SameBoundaryGerm A D v) : SameBoundaryGerm B E v := by
  have hva : v ≠ a := by
    obtain ⟨f, _, hi, _, h0, h1⟩ := h.fst
    intro heq
    exact zero_ne_one (hi zero_mem_I one_mem_I (h0.trans (heq.trans h1.symm)))
  have hvb : v ≠ b := by
    obtain ⟨f, _, hi, _, h0, h1⟩ := h'.fst
    intro heq
    exact zero_ne_one (hi zero_mem_I one_mem_I (h0.trans (heq.trans h1.symm)))
  have hvavoid : v ∉ ({a, b} : Set Plane) := by
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨hva, hvb⟩
  obtain ⟨r, hr, hAD⟩ := hAD
  obtain ⟨s, hs, havoid⟩ :=
    Metric.isOpen_iff.mp ((Set.finite_singleton b).insert a).isClosed.isOpen_compl v hvavoid
  refine ⟨min r s, lt_min hr hs, ?_⟩
  ext x
  by_cases hxball : x ∈ Metric.ball v (min r s)
  · simp only [mem_inter_iff, hxball, true_and]
    by_cases hxv : x = v
    · subst x
      exact iff_of_true h.snd.left_mem h'.snd.left_mem
    have hxballr := Metric.ball_subset_ball (min_le_left r s) hxball
    have hxballs := Metric.ball_subset_ball (min_le_right r s) hxball
    have hxAD : x ∈ A ↔ x ∈ D := by
      constructor
      · intro hxA
        exact ((Set.ext_iff.mp hAD x).mp ⟨hxballr, hxA⟩).2
      · intro hxD
        exact ((Set.ext_iff.mp hAD x).mpr ⟨hxballr, hxD⟩).2
    have hnotAB : ¬ (x ∈ A ∧ x ∈ B) := by
      intro hx
      have hxpair : x ∈ ({v, a} : Set Plane) := h.inter_eq ▸ hx
      rcases mem_insert_iff.mp hxpair with hxv' | hxa
      · exact hxv hxv'
      · exact (havoid hxballs) (Or.inl (mem_singleton_iff.mp hxa))
    have hnotDE : ¬ (x ∈ D ∧ x ∈ E) := by
      intro hx
      have hxpair : x ∈ ({v, b} : Set Plane) := h'.inter_eq ▸ hx
      rcases mem_insert_iff.mp hxpair with hxv' | hxb
      · exact hxv hxv'
      · exact (havoid hxballs) (Or.inr hxb)
    have hcover : (x ∈ A ∨ x ∈ B) ↔ (x ∈ D ∨ x ∈ E) := by
      change x ∈ A ∪ B ↔ x ∈ D ∪ E
      rw [h.union_eq, h'.union_eq]
    tauto
  · simp only [mem_inter_iff, hxball, false_and]

/-- The two branches at a point of a Jordan curve are independent of the
chosen second cut point, up to exchanging the branches. -/
theorem IsCutPair.sameBoundaryGerm_pair {C A B D E : Set Plane} {v a b : Plane}
    (h : IsCutPair C v a A B) (h' : IsCutPair C v b D E) :
    (SameBoundaryGerm A D v ∧ SameBoundaryGerm B E v) ∨
      (SameBoundaryGerm A E v ∧ SameBoundaryGerm B D v) := by
  rcases h'.endpoint_arc_germ_eq_or h.fst h.fst_subset with hAD | hAE
  · exact Or.inl ⟨hAD, h.sameBoundaryGerm_snd_of_fst h' hAD⟩
  · exact Or.inr ⟨hAE, h.sameBoundaryGerm_snd_of_fst h'.symm hAE⟩

/-- A set meeting an arc only at its endpoints cannot agree locally with the
arc at its first endpoint. -/
theorem IsArcBetween.not_sameBoundaryGerm_of_inter_subset_endpoints
    {A B : Set Plane} {v a : Plane} (hA : IsArcBetween A v a)
    (hinter : A ∩ B ⊆ ({v, a} : Set Plane)) : ¬ SameBoundaryGerm A B v := by
  rintro ⟨r, hr, hAB⟩
  obtain ⟨x, hxball, hxA⟩ := mem_closure_iff.mp hA.left_mem_closure_diff
    (Metric.ball v r) Metric.isOpen_ball (Metric.mem_ball_self hr)
  have hxB := ((Set.ext_iff.mp hAB x).mp ⟨hxball, hxA.1⟩).2
  exact hxA.2 (hinter ⟨hxA.1, hxB⟩)

/-- The two members of a cut pair represent distinct local branches. -/
theorem IsCutPair.not_sameBoundaryGerm {C A B : Set Plane} {v a : Plane}
    (h : IsCutPair C v a A B) : ¬ SameBoundaryGerm A B v :=
  h.fst.not_sameBoundaryGerm_of_inter_subset_endpoints h.inter_eq.subset

end Schoenflies
