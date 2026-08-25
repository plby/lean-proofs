import Wikipedia.SchoenfliesTheorem.TwoArcs
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Enclosing a proper closed subset of a Jordan curve in an arc

A missing point has a parameter neighborhood disjoint from the closed subset.
The rest of the loop is an arc.  If the missing point is the loop's start, the
neighborhood is removed at both ends of the parameter interval.
-/

open Set unitInterval

namespace Schoenflies

/-- Every proper closed subset of a Jordan curve is contained in an arc on
that curve.  No connectedness or nonemptiness of the subset is needed. -/
theorem IsJordanCurve.exists_arc_enclosing_closed_subset {C E : Set Plane}
    (hC : IsJordanCurve C) (hE : IsClosed E) (hsub : E ⊆ C) (hproper : E ≠ C) :
    ∃ A p q, IsArcBetween A p q ∧ E ⊆ A ∧ A ⊆ C := by
  have hmissing : ∃ x ∈ C, x ∉ E := by
    by_contra h
    apply hproper
    apply Subset.antisymm hsub
    intro x hx
    by_contra hxE
    exact h ⟨x, hx, hxE⟩
  obtain ⟨x, hxC, hxE⟩ := hmissing
  obtain ⟨f, hf, himage⟩ := hC
  obtain ⟨c, hc, hc1, hcx⟩ := hf.parameter_before_finish (himage.symm ▸ hxC)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hE.isOpen_compl x hxE
  obtain ⟨δ, hδ, hsmall⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_I.uniformContinuousOn_of_continuous hf.continuousOn) r hr
  have exclude (t u : ℝ) (ht : t ∈ I) (hu : u ∈ I) (hux : f u = x)
      (htu : dist t u < δ) : f t ∉ E := by
    apply hball
    change dist (f t) x < r
    rw [← hux]
    exact hsmall t ht u hu htu
  by_cases hc0 : c = 0
  · subst c
    let d : ℝ := min (δ / 2) (1 / 4)
    have hd : 0 < d := lt_min (half_pos hδ) (by norm_num)
    have hdδ : d < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hdq : d ≤ 1 / 4 := min_le_right _ _
    have ha : d ∈ I := ⟨hd.le, by linarith⟩
    have hb : 1 - d ∈ I := ⟨by linarith, by linarith⟩
    have hab : d < 1 - d := by linarith
    refine ⟨f '' Icc d (1 - d), f d, f (1 - d),
      hf.middle_IsArcBetween ha hb (by linarith) hab, ?_, ?_⟩
    · intro y hyE
      obtain ⟨t, ht, rfl⟩ := himage.symm ▸ hsub hyE
      refine ⟨t, ⟨?_, ?_⟩, rfl⟩
      · by_contra htd
        have htd' : t < d := lt_of_not_ge htd
        have htδ : dist t 0 < δ := by
          rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
          exact htd'.trans hdδ
        exact exclude t 0 ht zero_mem_I hcx htδ hyE
      · by_contra htd
        have htd' : 1 - d < t := lt_of_not_ge htd
        have htδ : dist t 1 < δ := by
          rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2)]
          linarith
        exact exclude t 1 ht one_mem_I (hf.closes.symm.trans hcx) htδ hyE
    · intro y hy
      rw [← himage]
      exact image_mono (IsLoop.middle_subset_I ha hb) hy
  · have hcpos : 0 < c := lt_of_le_of_ne hc.1 (Ne.symm hc0)
    have hclt : c < 1 := lt_of_le_of_ne hc.2 hc1
    let d : ℝ := min (δ / 2) (min (c / 2) ((1 - c) / 2))
    have hd : 0 < d :=
      lt_min (half_pos hδ) (lt_min (half_pos hcpos) (by linarith))
    have hdδ : d < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hdc : d ≤ c / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hd1c : d ≤ (1 - c) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    have ha : c - d ∈ I := ⟨by linarith, by linarith⟩
    have hb : c + d ∈ I := ⟨by linarith, by linarith⟩
    have ha1 : c - d ≠ 1 := by linarith
    have hb1 : c + d ≠ 1 := by linarith
    have hab : c - d < c + d := by linarith
    refine ⟨f '' Icc 0 (c - d) ∪ f '' Icc (c + d) 1, f (c + d), f (c - d),
      hf.outside_IsArcBetween ha hb ha1 hb1 hab, ?_, ?_⟩
    · intro y hyE
      obtain ⟨t, ht, rfl⟩ := himage.symm ▸ hsub hyE
      by_cases hta : t ≤ c - d
      · exact Or.inl ⟨t, ⟨ht.1, hta⟩, rfl⟩
      · have hbt : c + d ≤ t := by
          by_contra htb
          have hta' : c - d < t := lt_of_not_ge hta
          have htb' : t < c + d := lt_of_not_ge htb
          have htδ : dist t c < δ := by
            rw [Real.dist_eq, abs_lt]
            constructor <;> linarith
          exact exclude t c ht hc hcx htδ hyE
        exact Or.inr ⟨t, ⟨hbt, ht.2⟩, rfl⟩
    · intro y hy
      rw [← himage]
      exact hy.elim (fun hz => image_mono (f := f) (IsLoop.front_subset_I ha) hz)
        (fun hz => image_mono (f := f) (IsLoop.back_subset_I hb) hz)

/-- Compact version of the enclosure theorem, convenient for compact connected
subsets of a Jordan curve. -/
theorem IsJordanCurve.exists_arc_enclosing_compact_subset {C E : Set Plane}
    (hC : IsJordanCurve C) (hE : IsCompact E) (hsub : E ⊆ C) (hproper : E ≠ C) :
    ∃ A p q, IsArcBetween A p q ∧ E ⊆ A ∧ A ⊆ C :=
  hC.exists_arc_enclosing_closed_subset hE.isClosed hsub hproper

end Schoenflies
