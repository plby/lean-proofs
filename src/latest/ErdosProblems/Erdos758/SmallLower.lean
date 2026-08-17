/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos758

namespace Erdos758

open SimpleGraph

namespace SmallLower

/-! Explicit witnesses for the lower bounds in the small-values table. -/

def singletonGraph : SimpleGraph (Fin 1) := ⊥

theorem singletonGraph_not_zero : ¬ CochromaticColorable singletonGraph 0 := by
  rintro ⟨c, _⟩
  exact Fin.elim0 (c 0)

def oneEdgeThree : SimpleGraph (Fin 3) :=
  SimpleGraph.fromRel fun u v ↦
    (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0)

instance oneEdgeThreeAdjDecidable : DecidableRel oneEdgeThree.Adj := fun u v ↦ by
  rw [oneEdgeThree, SimpleGraph.fromRel_adj]
  infer_instance

theorem oneEdgeThree_not_one : ¬ CochromaticColorable oneEdgeThree 1 := by
  decide

def cycleFive : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun u v ↦
    u.val + 1 = v.val ∨ v.val + 1 = u.val ∨
    (u.val = 0 ∧ v.val = 4) ∨ (u.val = 4 ∧ v.val = 0)

instance cycleFiveAdjDecidable : DecidableRel cycleFive.Adj := fun u v ↦ by
  rw [cycleFive, SimpleGraph.fromRel_adj]
  infer_instance

theorem cycleFive_not_two : ¬ CochromaticColorable cycleFive 2 := by
  decide

/-- The vertex labels of the nine-vertex induced Paley witness. -/
def witnessNineVertex : Fin 9 → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | 5 => 5
  | 6 => 8
  | 7 => 10
  | 8 => 14

def witnessNine : SimpleGraph (Fin 9) :=
  SimpleGraph.fromRel fun u v ↦
    (witnessNineVertex u + 17 - witnessNineVertex v) % 17 ∈ quadraticResidues17

instance witnessNineAdjDecidable : DecidableRel witnessNine.Adj := fun u v ↦ by
  rw [witnessNine, SimpleGraph.fromRel_adj]
  infer_instance

private def colorNine (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Fin 3) : Fin 9 → Fin 3
  | 0 => a0
  | 1 => a1
  | 2 => a2
  | 3 => a3
  | 4 => a4
  | 5 => a5
  | 6 => a6
  | 7 => a7
  | 8 => a8

private theorem no_witnessNine_assignment_00 :
    ∀ a3 a4 a5 a6 a7 a8 : Fin 3,
      ¬ IsCochromaticColoring witnessNine (colorNine 0 0 0 a3 a4 a5 a6 a7 a8) := by decide
private theorem no_witnessNine_assignment_01 :
    ∀ a3 a4 a5 a6 a7 a8 : Fin 3,
      ¬ IsCochromaticColoring witnessNine (colorNine 0 0 1 a3 a4 a5 a6 a7 a8) := by decide
private theorem no_witnessNine_assignment_02 :
    ∀ a3 a4 a5 a6 a7 a8 : Fin 3,
      ¬ IsCochromaticColoring witnessNine (colorNine 0 0 2 a3 a4 a5 a6 a7 a8) := by decide
private theorem no_witnessNine_assignment_10 :
    ∀ a3 a4 a5 a6 a7 a8 : Fin 3,
      ¬ IsCochromaticColoring witnessNine (colorNine 0 1 0 a3 a4 a5 a6 a7 a8) := by decide
private theorem no_witnessNine_assignment_11 :
    ∀ a3 a4 a5 a6 a7 a8 : Fin 3,
      ¬ IsCochromaticColoring witnessNine (colorNine 0 1 1 a3 a4 a5 a6 a7 a8) := by decide
private theorem no_witnessNine_assignment_12 :
    ∀ a3 a4 a5 a6 a7 a8 : Fin 3,
      ¬ IsCochromaticColoring witnessNine (colorNine 0 1 2 a3 a4 a5 a6 a7 a8) := by decide
private theorem no_witnessNine_assignment_20 :
    ∀ a3 a4 a5 a6 a7 a8 : Fin 3,
      ¬ IsCochromaticColoring witnessNine (colorNine 0 2 0 a3 a4 a5 a6 a7 a8) := by decide
private theorem no_witnessNine_assignment_21 :
    ∀ a3 a4 a5 a6 a7 a8 : Fin 3,
      ¬ IsCochromaticColoring witnessNine (colorNine 0 2 1 a3 a4 a5 a6 a7 a8) := by decide
private theorem no_witnessNine_assignment_22 :
    ∀ a3 a4 a5 a6 a7 a8 : Fin 3,
      ¬ IsCochromaticColoring witnessNine (colorNine 0 2 2 a3 a4 a5 a6 a7 a8) := by decide

private theorem no_witnessNine_assignment_zero :
    ∀ a1 a2 a3 a4 a5 a6 a7 a8 : Fin 3,
      ¬ IsCochromaticColoring witnessNine (colorNine 0 a1 a2 a3 a4 a5 a6 a7 a8) := by
  intro a1 a2
  fin_cases a1 <;> fin_cases a2
  · exact no_witnessNine_assignment_00
  · exact no_witnessNine_assignment_01
  · exact no_witnessNine_assignment_02
  · exact no_witnessNine_assignment_10
  · exact no_witnessNine_assignment_11
  · exact no_witnessNine_assignment_12
  · exact no_witnessNine_assignment_20
  · exact no_witnessNine_assignment_21
  · exact no_witnessNine_assignment_22

private theorem relabel {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {c : V → Fin k} (hc : IsCochromaticColoring G c) (e : Equiv.Perm (Fin k)) :
    IsCochromaticColoring G (e ∘ c) := by
  intro i
  rcases hc (e.symm i) with h | h
  · left
    intro u v hu hv huv
    apply h u v
    · apply e.injective
      simpa using hu
    · apply e.injective
      simpa using hv
    · exact huv
  · right
    intro u v hu hv huv
    apply h u v
    · apply e.injective
      simpa using hu
    · apply e.injective
      simpa using hv
    · exact huv

theorem witnessNine_not_three : ¬ CochromaticColorable witnessNine 3 := by
  rintro ⟨c, hc⟩
  let e : Equiv.Perm (Fin 3) := Equiv.swap (c 0) 0
  let c' : Fin 9 → Fin 3 := e ∘ c
  have hc' : IsCochromaticColoring witnessNine c' := relabel hc e
  have hzero : c' 0 = 0 := by simp [c', e]
  apply no_witnessNine_assignment_zero (c' 1) (c' 2) (c' 3) (c' 4)
    (c' 5) (c' 6) (c' 7) (c' 8)
  rw [show colorNine 0 (c' 1) (c' 2) (c' 3) (c' 4) (c' 5) (c' 6) (c' 7) (c' 8) = c' by
    funext x
    fin_cases x
    · exact hzero.symm
    all_goals rfl]
  exact hc'

def paleyPrefix13 : SimpleGraph (Fin 13) :=
  SimpleGraph.fromRel fun u v ↦ (u.val + 17 - v.val) % 17 ∈ quadraticResidues17

def paleyPrefix16 : SimpleGraph (Fin 16) :=
  SimpleGraph.fromRel fun u v ↦ (u.val + 17 - v.val) % 17 ∈ quadraticResidues17

instance paleyPrefix13AdjDecidable : DecidableRel paleyPrefix13.Adj := fun u v ↦ by
  rw [paleyPrefix13, SimpleGraph.fromRel_adj]
  infer_instance

instance paleyPrefix16AdjDecidable : DecidableRel paleyPrefix16.Adj := fun u v ↦ by
  rw [paleyPrefix16, SimpleGraph.fromRel_adj]
  infer_instance

private theorem paleyPrefix13_no_homogeneous_four_points :
    ∀ a b c d : Fin 13,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ¬ HomogeneousFour paleyPrefix13 a b c d := by
  decide

private theorem paleyPrefix16_no_homogeneous_four_at_0 :
    ∀ b c d : Fin 16, (0 : Fin 16) ≠ b → (0 : Fin 16) ≠ c → (0 : Fin 16) ≠ d →
      b ≠ c → b ≠ d → c ≠ d → ¬ HomogeneousFour paleyPrefix16 0 b c d := by decide
private theorem paleyPrefix16_no_homogeneous_four_at_1 :
    ∀ b c d : Fin 16, (1 : Fin 16) ≠ b → (1 : Fin 16) ≠ c → (1 : Fin 16) ≠ d →
      b ≠ c → b ≠ d → c ≠ d → ¬ HomogeneousFour paleyPrefix16 1 b c d := by decide
private theorem paleyPrefix16_no_homogeneous_four_at_2 :
    ∀ b c d : Fin 16, (2 : Fin 16) ≠ b → (2 : Fin 16) ≠ c → (2 : Fin 16) ≠ d →
      b ≠ c → b ≠ d → c ≠ d → ¬ HomogeneousFour paleyPrefix16 2 b c d := by decide
private theorem paleyPrefix16_no_homogeneous_four_at_3 :
    ∀ b c d : Fin 16, (3 : Fin 16) ≠ b → (3 : Fin 16) ≠ c → (3 : Fin 16) ≠ d →
      b ≠ c → b ≠ d → c ≠ d → ¬ HomogeneousFour paleyPrefix16 3 b c d := by decide
private theorem paleyPrefix16_no_homogeneous_four_at_4 :
    ∀ b c d : Fin 16, (4 : Fin 16) ≠ b → (4 : Fin 16) ≠ c → (4 : Fin 16) ≠ d →
      b ≠ c → b ≠ d → c ≠ d → ¬ HomogeneousFour paleyPrefix16 4 b c d := by decide
private theorem paleyPrefix16_no_homogeneous_four_at_5 :
    ∀ b c d : Fin 16, (5 : Fin 16) ≠ b → (5 : Fin 16) ≠ c → (5 : Fin 16) ≠ d →
      b ≠ c → b ≠ d → c ≠ d → ¬ HomogeneousFour paleyPrefix16 5 b c d := by decide
private theorem paleyPrefix16_no_homogeneous_four_at_6 :
    ∀ b c d : Fin 16, (6 : Fin 16) ≠ b → (6 : Fin 16) ≠ c → (6 : Fin 16) ≠ d →
      b ≠ c → b ≠ d → c ≠ d → ¬ HomogeneousFour paleyPrefix16 6 b c d := by decide
private theorem paleyPrefix16_no_homogeneous_four_at_7 :
    ∀ b c d : Fin 16, (7 : Fin 16) ≠ b → (7 : Fin 16) ≠ c → (7 : Fin 16) ≠ d →
      b ≠ c → b ≠ d → c ≠ d → ¬ HomogeneousFour paleyPrefix16 7 b c d := by decide
private theorem paleyPrefix16_no_homogeneous_four_at_8 :
    ∀ b c d : Fin 16, (8 : Fin 16) ≠ b → (8 : Fin 16) ≠ c → (8 : Fin 16) ≠ d →
      b ≠ c → b ≠ d → c ≠ d → ¬ HomogeneousFour paleyPrefix16 8 b c d := by decide
private theorem paleyPrefix16_no_homogeneous_four_at_9 :
    ∀ b c d : Fin 16, (9 : Fin 16) ≠ b → (9 : Fin 16) ≠ c → (9 : Fin 16) ≠ d →
      b ≠ c → b ≠ d → c ≠ d → ¬ HomogeneousFour paleyPrefix16 9 b c d := by decide
private theorem paleyPrefix16_no_homogeneous_four_at_10 :
    ∀ b c d : Fin 16, (10 : Fin 16) ≠ b → (10 : Fin 16) ≠ c → (10 : Fin 16) ≠ d →
      b ≠ c → b ≠ d → c ≠ d → ¬ HomogeneousFour paleyPrefix16 10 b c d := by decide
private theorem paleyPrefix16_no_homogeneous_four_at_11 :
    ∀ b c d : Fin 16, (11 : Fin 16) ≠ b → (11 : Fin 16) ≠ c → (11 : Fin 16) ≠ d →
      b ≠ c → b ≠ d → c ≠ d → ¬ HomogeneousFour paleyPrefix16 11 b c d := by decide
private theorem paleyPrefix16_no_homogeneous_four_at_12 :
    ∀ b c d : Fin 16, (12 : Fin 16) ≠ b → (12 : Fin 16) ≠ c → (12 : Fin 16) ≠ d →
      b ≠ c → b ≠ d → c ≠ d → ¬ HomogeneousFour paleyPrefix16 12 b c d := by decide
private theorem paleyPrefix16_no_homogeneous_four_at_13 :
    ∀ b c d : Fin 16, (13 : Fin 16) ≠ b → (13 : Fin 16) ≠ c → (13 : Fin 16) ≠ d →
      b ≠ c → b ≠ d → c ≠ d → ¬ HomogeneousFour paleyPrefix16 13 b c d := by decide
private theorem paleyPrefix16_no_homogeneous_four_at_14 :
    ∀ b c d : Fin 16, (14 : Fin 16) ≠ b → (14 : Fin 16) ≠ c → (14 : Fin 16) ≠ d →
      b ≠ c → b ≠ d → c ≠ d → ¬ HomogeneousFour paleyPrefix16 14 b c d := by decide
private theorem paleyPrefix16_no_homogeneous_four_at_15 :
    ∀ b c d : Fin 16, (15 : Fin 16) ≠ b → (15 : Fin 16) ≠ c → (15 : Fin 16) ≠ d →
      b ≠ c → b ≠ d → c ≠ d → ¬ HomogeneousFour paleyPrefix16 15 b c d := by decide

private theorem paleyPrefix16_no_homogeneous_four_points :
    ∀ a b c d : Fin 16,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ¬ HomogeneousFour paleyPrefix16 a b c d := by
  intro a
  fin_cases a
  · exact paleyPrefix16_no_homogeneous_four_at_0
  · exact paleyPrefix16_no_homogeneous_four_at_1
  · exact paleyPrefix16_no_homogeneous_four_at_2
  · exact paleyPrefix16_no_homogeneous_four_at_3
  · exact paleyPrefix16_no_homogeneous_four_at_4
  · exact paleyPrefix16_no_homogeneous_four_at_5
  · exact paleyPrefix16_no_homogeneous_four_at_6
  · exact paleyPrefix16_no_homogeneous_four_at_7
  · exact paleyPrefix16_no_homogeneous_four_at_8
  · exact paleyPrefix16_no_homogeneous_four_at_9
  · exact paleyPrefix16_no_homogeneous_four_at_10
  · exact paleyPrefix16_no_homogeneous_four_at_11
  · exact paleyPrefix16_no_homogeneous_four_at_12
  · exact paleyPrefix16_no_homogeneous_four_at_13
  · exact paleyPrefix16_no_homogeneous_four_at_14
  · exact paleyPrefix16_no_homogeneous_four_at_15

private theorem no_homogeneous_four_finset_of_points {n : ℕ} (G : SimpleGraph (Fin n))
    (hpoints : ∀ a b c d : Fin n,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ¬ HomogeneousFour G a b c d) :
    ∀ S : Finset (Fin n), S.card = 4 → ¬ IsHomogeneousFinset G S := by
  intro S hcard hhom
  have hlarge : 3 < S.card := by omega
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ :=
    Finset.three_lt_card_iff.mp hlarge
  apply hpoints a b c d hab hac had hbc hbd hcd
  rcases hhom with h | h
  · left
    exact ⟨h a ha b hb hab, h a ha c hc hac, h a ha d hd had,
      h b hb c hc hbc, h b hb d hd hbd, h c hc d hd hcd⟩
  · right
    exact ⟨h a ha b hb hab, h a ha c hc hac, h a ha d hd had,
      h b hb c hc hbc, h b hb d hd hbd, h c hc d hd hcd⟩

private theorem not_colorable_of_no_homogeneous_four {n k : ℕ}
    (G : SimpleGraph (Fin n))
    (hno : ∀ S : Finset (Fin n), S.card = 4 → ¬ IsHomogeneousFinset G S)
    (hsize : Fintype.card (Fin k) * 3 < Fintype.card (Fin n)) :
    ¬ CochromaticColorable G k := by
  rintro ⟨c, hc⟩
  obtain ⟨i, hi⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card (f := c) hsize
  let S : Finset (Fin n) := Finset.univ.filter fun v ↦ c v = i
  have hi' : 3 < S.card := by simpa [S] using hi
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (by omega : 4 ≤ S.card)
  apply hno T hTcard
  rcases hc i with hclique | hindependent
  · left
    intro u hu v hv huv
    exact hclique u v (by simpa [S] using hTS hu) (by simpa [S] using hTS hv) huv
  · right
    intro u hu v hv huv
    exact hindependent u v (by simpa [S] using hTS hu) (by simpa [S] using hTS hv) huv

theorem paleyPrefix13_not_four : ¬ CochromaticColorable paleyPrefix13 4 :=
  not_colorable_of_no_homogeneous_four paleyPrefix13
    (no_homogeneous_four_finset_of_points paleyPrefix13
      paleyPrefix13_no_homogeneous_four_points) (by decide)

theorem paleyPrefix16_not_five : ¬ CochromaticColorable paleyPrefix16 5 :=
  not_colorable_of_no_homogeneous_four paleyPrefix16
    (no_homogeneous_four_finset_of_points paleyPrefix16
      paleyPrefix16_no_homogeneous_four_points) (by decide)

theorem lt_z_of_not_colorable {n k : ℕ} (G : SimpleGraph (Fin n))
    (hG : ¬ CochromaticColorable G k) : k < z n := by
  by_contra h
  apply hG
  exact (z_spec n G).mono (Nat.le_of_not_gt h)

private theorem colorable_comap {V W : Type*} (H : SimpleGraph W) (f : V → W)
    (hf : Function.Injective f) {k : ℕ}
    (h : CochromaticColorable H k) : CochromaticColorable (H.comap f) k := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c ∘ f, ?_⟩
  intro i
  rcases hc i with hi | hi
  · left
    intro u v hu hv huv
    exact hi (f u) (f v) hu hv (hf.ne huv)
  · right
    intro u v hu hv huv
    exact hi (f u) (f v) hu hv (hf.ne huv)

theorem z_mono {m n : ℕ} (hmn : m ≤ n) : z m ≤ z n := by
  apply z_le
  intro G
  let e : Fin m ↪ Fin n := Fin.castLEEmb hmn
  have hlarge := z_spec n (G.map e)
  simpa only [SimpleGraph.comap_map_eq] using
    colorable_comap (G.map e) e e.injective hlarge

end SmallLower

/-- The lower half of the complete small-values table for `z`. -/
theorem small_values_lower_bounds :
    1 ≤ z 1 ∧ 1 ≤ z 2 ∧
    2 ≤ z 3 ∧ 2 ≤ z 4 ∧
    3 ≤ z 5 ∧ 3 ≤ z 6 ∧ 3 ≤ z 7 ∧ 3 ≤ z 8 ∧
    4 ≤ z 9 ∧ 4 ≤ z 10 ∧ 4 ≤ z 11 ∧ 4 ≤ z 12 ∧
    5 ≤ z 13 ∧ 5 ≤ z 14 ∧ 5 ≤ z 15 ∧
    6 ≤ z 16 ∧ 6 ≤ z 17 ∧ 6 ≤ z 18 ∧ 6 ≤ z 19 := by
  have h1 : 1 ≤ z 1 := by
    have h := SmallLower.lt_z_of_not_colorable SmallLower.singletonGraph
      SmallLower.singletonGraph_not_zero
    omega
  have h3 : 2 ≤ z 3 := by
    have h := SmallLower.lt_z_of_not_colorable SmallLower.oneEdgeThree
      SmallLower.oneEdgeThree_not_one
    omega
  have h5 : 3 ≤ z 5 := by
    have h := SmallLower.lt_z_of_not_colorable SmallLower.cycleFive
      SmallLower.cycleFive_not_two
    omega
  have h9 : 4 ≤ z 9 := by
    have h := SmallLower.lt_z_of_not_colorable SmallLower.witnessNine
      SmallLower.witnessNine_not_three
    omega
  have h13 : 5 ≤ z 13 := by
    have h := SmallLower.lt_z_of_not_colorable SmallLower.paleyPrefix13
      SmallLower.paleyPrefix13_not_four
    omega
  have h16 : 6 ≤ z 16 := by
    have h := SmallLower.lt_z_of_not_colorable SmallLower.paleyPrefix16
      SmallLower.paleyPrefix16_not_five
    omega
  have h2 := h1.trans (SmallLower.z_mono (by omega : 1 ≤ 2))
  have h4 := h3.trans (SmallLower.z_mono (by omega : 3 ≤ 4))
  have h6 := h5.trans (SmallLower.z_mono (by omega : 5 ≤ 6))
  have h7 := h5.trans (SmallLower.z_mono (by omega : 5 ≤ 7))
  have h8 := h5.trans (SmallLower.z_mono (by omega : 5 ≤ 8))
  have h10 := h9.trans (SmallLower.z_mono (by omega : 9 ≤ 10))
  have h11 := h9.trans (SmallLower.z_mono (by omega : 9 ≤ 11))
  have h12 := h9.trans (SmallLower.z_mono (by omega : 9 ≤ 12))
  have h14 := h13.trans (SmallLower.z_mono (by omega : 13 ≤ 14))
  have h15 := h13.trans (SmallLower.z_mono (by omega : 13 ≤ 15))
  have h17 := h16.trans (SmallLower.z_mono (by omega : 16 ≤ 17))
  have h18 := h16.trans (SmallLower.z_mono (by omega : 16 ≤ 18))
  have h19 := h16.trans (SmallLower.z_mono (by omega : 16 ≤ 19))
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, h16, h17, h18, h19⟩

#print axioms small_values_lower_bounds

end Erdos758
