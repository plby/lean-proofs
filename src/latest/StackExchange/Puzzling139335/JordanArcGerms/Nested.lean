import Wikipedia.SchoenfliesTheorem.MatchedArc
import StackExchange.Puzzling139335.BoundaryGerm

/-!
# Endpoint neighborhoods of nested arcs

A subarc with the same initial endpoint as an ambient arc contains all of the
ambient arc sufficiently near that endpoint.  The compact remaining tail of
an injective parametrization can be excluded by a small ball.
-/

open Set unitInterval Schoenflies

namespace Puzzling139335

/-- Nested arcs with a common initial endpoint agree in a neighborhood of it. -/
theorem nested_arcs_agree_near_endpoint {A B : Set Plane} {v a b : Plane}
    (hA : IsArcBetween A v a) (hB : IsArcBetween B v b) (hBA : B ⊆ A) :
    ∃ r > 0, Metric.ball v r ∩ A = Metric.ball v r ∩ B := by
  have hvb : v ≠ b := by
    obtain ⟨g, _, hgi, _, hg0, hg1⟩ := hB
    intro hvb
    exact zero_ne_one (hgi zero_mem_I one_mem_I (hg0.trans (hvb.trans hg1.symm)))
  obtain ⟨f, hfc, hfi, hfim, hf0, hf1⟩ := hA
  obtain ⟨β, hβ, hfβ⟩ : b ∈ f '' I := hfim.symm ▸ hBA hB.right_mem
  have hβne : β ≠ 0 := by
    intro hzero
    apply hvb
    exact hf0.symm.trans ((congrArg f hzero.symm).trans hfβ)
  have hβpos : 0 < β := lt_of_le_of_ne hβ.1 hβne.symm
  have hUarc : IsArcBetween (f '' Icc 0 β) v b := by
    simpa only [uIcc_of_le hβ.1, hf0, hfβ] using
      isArcBetween_subarc_of_injOn_I hfc hfi zero_mem_I hβ hβne.symm
  have hUsub : f '' Icc 0 β ⊆ A := by
    rw [← hfim]
    exact image_mono (Icc_subset_Icc le_rfl hβ.2)
  have hBU : B = f '' Icc 0 β :=
    hB.eq_of_subset_arc hUarc ⟨f, hfc, hfi, hfim, hf0, hf1⟩ hBA hUsub
  have htailclosed : IsClosed (f '' Icc β 1) :=
    (isCompact_Icc.image_of_continuousOn
      (hfc.mono (Icc_subset_Icc hβ.1 le_rfl))).isClosed
  have hvnot : v ∉ f '' Icc β 1 := by
    rintro ⟨s, hs, hsv⟩
    have hsI : s ∈ I := ⟨hβ.1.trans hs.1, hs.2⟩
    have hs0 : s = 0 := hfi hsI zero_mem_I (hsv.trans hf0.symm)
    exact (not_le_of_gt hβpos) (hs0 ▸ hs.1)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp htailclosed.isOpen_compl v hvnot
  refine ⟨r, hr, Set.Subset.antisymm ?_ ?_⟩
  · rintro y ⟨hyball, hyA⟩
    refine ⟨hyball, ?_⟩
    rw [hBU]
    obtain ⟨s, hs, rfl⟩ : y ∈ f '' I := hfim.symm ▸ hyA
    by_cases hsβ : s ≤ β
    · exact ⟨s, ⟨hs.1, hsβ⟩, rfl⟩
    · exact False.elim (hball hyball ⟨s, ⟨(lt_of_not_ge hsβ).le, hs.2⟩, rfl⟩)
  · exact fun _ hy => ⟨hy.1, hBA hy.2⟩

/-- The endpoint germ of an arc is unchanged on passing to a subarc with
the same initial endpoint. -/
theorem nested_arcs_sameBoundaryGerm {A B : Set Plane} {v a b : Plane}
    (hA : IsArcBetween A v a) (hB : IsArcBetween B v b) (hBA : B ⊆ A) :
    SameBoundaryGerm A B v :=
  nested_arcs_agree_near_endpoint hA hB hBA

end Puzzling139335
