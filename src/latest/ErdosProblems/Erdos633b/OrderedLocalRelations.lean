import ErdosProblems.Erdos633b.LocalDeficitPatterns

/-! An explicit finite set of 26 linear angle relations. Every table entry
is accompanied by a kernel-checked membership proof and real equality. -/

namespace Erdos633b

def orderedRelationTriples : Finset (ℤ × ℤ × ℤ) :=
  {(0, 3, 1),
    (0, 4, 1),
    (0, 5, 1),
    (0, 5, 2),
    (0, 7, 2),
    (0, 9, 2),
    (0, 11, 2),
    (1, -6, -1),
    (1, -5, -1),
    (1, -4, -1),
    (1, -3, -1),
    (1, 5, 2),
    (1, 6, 2),
    (1, 7, 2),
    (1, 8, 2),
    (1, 9, 2),
    (1, 10, 2),
    (2, -1, 0),
    (2, 2, 1),
    (2, 3, 1),
    (3, 1, 1),
    (3, 2, 1),
    (3, 3, 1),
    (3, 4, 2),
    (4, 3, 2),
    (5, 5, 3)}

def OrderedLocalRelation (α β : ℝ) : Prop :=
  ∃ t ∈ orderedRelationTriples, (t.1 : ℝ) * α + (t.2.1 : ℝ) * β = (t.2.2 : ℝ) * Real.pi

theorem orderedRelationTriples_card : orderedRelationTriples.card = 26 := by decide

theorem one_zero_relation_of_pattern (α β γ : ℝ) (hs : α + β + γ = Real.pi)
    (q r : ℕ) (hp : OneZeroPattern q r)
    (he : (q : ℝ) * β + (r : ℝ) * γ = Real.pi) :
    OrderedLocalRelation α β := by
  rcases hp with ⟨rfl, hlo, hhi⟩ |
    ⟨rfl, rfl⟩
  · interval_cases q
    · refine ⟨(0, 3, 1), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(0, 4, 1), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(0, 5, 1), by decide, ?_⟩
      norm_num at he ⊢; linarith
  · refine ⟨(2, 2, 1), by decide, ?_⟩
    norm_num at he ⊢; linarith

theorem two_zero_relation_of_pattern (α β γ : ℝ) (hs : α + β + γ = Real.pi)
    (q r : ℕ) (hp : TwoZeroPattern q r)
    (he : (q : ℝ) * β + (r : ℝ) * γ = 2 * Real.pi) :
    OrderedLocalRelation α β := by
  rcases hp with ⟨rfl, hlo, hhi⟩ |
    ⟨rfl, hlo, hhi⟩ |
    ⟨rfl, rfl⟩ |
    ⟨rfl, hhi⟩ |
    ⟨rfl, hhi⟩ |
    ⟨rfl, rfl⟩
  · interval_cases q
    · refine ⟨(0, 5, 2), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(0, 3, 1), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(0, 7, 2), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(0, 4, 1), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(0, 9, 2), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(0, 5, 1), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(0, 11, 2), by decide, ?_⟩
      norm_num at he ⊢; linarith
  · interval_cases q
    · refine ⟨(1, -3, -1), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(1, -4, -1), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(1, -5, -1), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(1, -6, -1), by decide, ?_⟩
      norm_num at he ⊢; linarith
  · refine ⟨(2, -1, 0), by decide, ?_⟩
    norm_num at he ⊢; linarith
  · interval_cases q
    · refine ⟨(3, 3, 1), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(3, 2, 1), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(3, 1, 1), by decide, ?_⟩
      norm_num at he ⊢; linarith
  · interval_cases q
    · refine ⟨(2, 2, 1), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(4, 3, 2), by decide, ?_⟩
      norm_num at he ⊢; linarith
  · refine ⟨(5, 5, 3), by decide, ?_⟩
    norm_num at he ⊢; linarith

theorem two_one_relation_of_pattern (α β γ : ℝ) (hs : α + β + γ = Real.pi)
    (q r : ℕ) (hp : TwoOnePattern q r)
    (he : α + (q : ℝ) * β + (r : ℝ) * γ = 2 * Real.pi) :
    OrderedLocalRelation α β := by
  rcases hp with ⟨rfl, hlo, hhi⟩ |
    ⟨rfl, hlo, hhi⟩ |
    ⟨rfl, hhi⟩ |
    ⟨rfl, rfl⟩
  · interval_cases q
    · refine ⟨(1, 5, 2), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(1, 6, 2), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(1, 7, 2), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(1, 8, 2), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(1, 9, 2), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(1, 10, 2), by decide, ?_⟩
      norm_num at he ⊢; linarith
  · interval_cases q
    · refine ⟨(0, 3, 1), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(0, 4, 1), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(0, 5, 1), by decide, ?_⟩
      norm_num at he ⊢; linarith
  · interval_cases q
    · refine ⟨(2, 3, 1), by decide, ?_⟩
      norm_num at he ⊢; linarith
    · refine ⟨(2, 2, 1), by decide, ?_⟩
      norm_num at he ⊢; linarith
  · refine ⟨(3, 4, 2), by decide, ?_⟩
    norm_num at he ⊢; linarith

theorem ordered_relation_of_local_deficit (α β γ : ℝ) (hα : 0 < α)
    (h01 : α < β) (h12 : β < γ) (hs : α + β + γ = Real.pi)
    (hγ : γ ≤ 2 * Real.pi / 3) (p q r k : ℕ) (hpk : p < k) (hr : r ≤ 5)
    (hkpos : 1 ≤ k) (hkbound : k ≤ 2)
    (he : (p : ℝ) * α + (q : ℝ) * β + (r : ℝ) * γ = (k : ℝ) * Real.pi) :
    OrderedLocalRelation α β := by
  have hkv : k = 1 ∨ k = 2 := by omega
  rcases hkv with rfl | rfl
  · have hp0 : p = 0 := by omega
    rw [hp0] at he
    norm_num at he
    exact one_zero_relation_of_pattern α β γ hs q r
      (one_zero_pattern α β γ hα h01 h12 hs hγ q r hr he) he
  · have hpv : p = 0 ∨ p = 1 := by omega
    rcases hpv with rfl | rfl <;> norm_num at he
    · exact two_zero_relation_of_pattern α β γ hs q r
        (two_zero_pattern α β γ hα h01 h12 hs hγ q r hr he) he
    · exact two_one_relation_of_pattern α β γ hs q r
        (two_one_pattern α β γ hα h01 h12 hs hγ q r hr he) he

end Erdos633b
