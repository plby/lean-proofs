import ErdosProblems.Erdos1148.ClosedOrbitImageMeasure

/-! # Fundamental rectangles for two closed-orbit parameters -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

lemma existsUnique_period_translate {T : ℝ} (hT : 0 < T) (x a : ℝ) :
    ∃! n : AddSubgroup.zmultiples T, n +ᵥ x ∈ Set.Ioc a (a + T) := by
  obtain ⟨n, hn, huniq⟩ := existsUnique_add_zsmul_mem_Ioc hT x a
  refine ⟨⟨n • T, AddSubgroup.zsmul_mem_zmultiples T n⟩, ?_, ?_⟩
  · change n • T + x ∈ Set.Ioc a (a + T)
    simpa only [add_comm] using hn
  · rintro ⟨m, hm⟩ hmem
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
    have hkuniq : k = n := by
      apply huniq
      change m + x ∈ Set.Ioc a (a + T) at hmem
      simpa only [hk, add_comm] using hmem
    apply Subtype.ext
    change m = n • T
    rw [← hk, hkuniq]

lemma isAddFundamentalDomain_period_rectangle {T U : ℝ} (hT : 0 < T) (hU : 0 < U) :
    IsAddFundamentalDomain ((AddSubgroup.zmultiples T).prod (AddSubgroup.zmultiples U))
      (Set.Ioc 0 T ×ˢ Set.Ioc 0 U) (volume : Measure (ℝ × ℝ)) := by
  apply IsAddFundamentalDomain.mk' (measurableSet_Ioc.prod measurableSet_Ioc).nullMeasurableSet
  rintro ⟨x, y⟩
  obtain ⟨m, hm, hmuniq⟩ := existsUnique_period_translate hT x 0
  obtain ⟨n, hn, hnuniq⟩ := existsUnique_period_translate hU y 0
  refine ⟨⟨((m : ℝ), (n : ℝ)), m.property, n.property⟩, ?_, ?_⟩
  · exact ⟨by simpa [AddSubgroup.vadd_def] using hm,
      by simpa [AddSubgroup.vadd_def] using hn⟩
  · rintro ⟨⟨r, s⟩, hrs⟩ hmem
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val (hmuniq ⟨r, hrs.1⟩ (by simpa [AddSubgroup.vadd_def] using hmem.1))
    · exact congrArg Subtype.val (hnuniq ⟨s, hrs.2⟩ (by simpa [AddSubgroup.vadd_def] using hmem.2))

end Erdos1148.DukeArithmetic
