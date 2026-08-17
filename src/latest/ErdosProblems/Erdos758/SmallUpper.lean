import ErdosProblems.Erdos758
import Util.Ramsey

namespace Erdos758

open SimpleGraph

/-- A uniform cochromatic upper bound for labelled `n`-vertex graphs. -/
def UniformBound (n k : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), CochromaticColorable G k

/-- Pull a cochromatic colouring back along an injective vertex map. -/
theorem cochromaticColorable_comap_of_injective
    {V W : Type*} (H : SimpleGraph W) (f : V → W)
    (hf : Function.Injective f) {k : ℕ}
    (h : CochromaticColorable H k) :
    CochromaticColorable (H.comap f) k := by
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

/-- Transfer a labelled uniform bound to any finite vertex type of the same cardinality. -/
theorem colorable_of_card_eq {V : Type*} [Fintype V] {m k : ℕ}
    (hcard : Fintype.card V = m) (h : UniformBound m k)
    (G : SimpleGraph V) : CochromaticColorable G k := by
  let e : Fin m ≃ V := (Fintype.equivFinOfCardEq hcard).symm
  exact (cochromaticColorable_comap_equiv G e k).mp (h (G.comap e))

/-- Uniform upper bounds pull back from `n` vertices to every smaller number of vertices. -/
theorem uniformBound_mono_vertices {m n k : ℕ} (hmn : m ≤ n)
    (h : UniformBound n k) : UniformBound m k := by
  intro G
  let e : Fin m ↪ Fin n := Fin.castLEEmb hmn
  have hpull := cochromaticColorable_comap_of_injective
    (G.map e) e e.injective (h (G.map e))
  rw [SimpleGraph.comap_map_eq] at hpull
  exact hpull

/-- A diagonal Ramsey property produces a homogeneous finset of the requested size. -/
theorem exists_homogeneous_finset_of_ramsey {r n : ℕ}
    (hR : Ramsey.RamseyProperty r r n) (G : SimpleGraph (Fin n)) :
    ∃ S : Finset (Fin n), S.card = r ∧ IsHomogeneousFinset G S := by
  classical
  by_contra hnone
  apply hR G
  constructor
  · intro S hS
    apply hnone
    refine ⟨S, hS.card_eq, Or.inl ?_⟩
    intro u hu v hv huv
    exact hS.isClique hu hv huv
  · intro S hS
    apply hnone
    refine ⟨S, hS.card_eq, Or.inr ?_⟩
    intro u hu v hv huv
    exact hS.isIndepSet hu hv huv

/-- Remove one Ramsey-guaranteed homogeneous block and colour the remaining vertices. -/
theorem uniformBound_of_ramsey {n r k : ℕ}
    (hR : Ramsey.RamseyProperty r r n)
    (hsmall : UniformBound (n - r) k) : UniformBound n (k + 1) := by
  intro G
  obtain ⟨S, hScard, hS⟩ := exists_homogeneous_finset_of_ramsey hR G
  apply cochromaticColorable_add_homogeneous_block G S k
  · apply colorable_of_card_eq (m := n - r)
    · change Fintype.card {v : Fin n // ¬v ∈ S} = n - r
      rw [Fintype.card_subtype_compl]
      simpa only [Fintype.card_fin, Fintype.card_coe, hScard]
    · exact hsmall
  · exact hS

/-- Complementing all graphs exchanges the two parameters of a Ramsey property. -/
theorem ramseyProperty_symm {k l n : ℕ}
    (h : Ramsey.RamseyProperty k l n) : Ramsey.RamseyProperty l k n := by
  intro G hbad
  apply h Gᶜ
  constructor
  · simpa [SimpleGraph.cliqueFree_compl] using hbad.2
  · simpa [SimpleGraph.indepSetFree_compl] using hbad.1

/-- The upper-bound half of `R(3,3)=6`. -/
theorem ramseyProperty_three_three_six : Ramsey.RamseyProperty 3 3 6 := by
  intro G hbad
  classical
  let v : Fin 6 := 0
  have hcfCompl : Gᶜ.CliqueFree 3 := by
    simpa [SimpleGraph.cliqueFree_compl] using hbad.2
  have hifCompl : Gᶜ.IndepSetFree 3 := by
    simpa [SimpleGraph.indepSetFree_compl] using hbad.1
  have hdeg : (G.neighborFinset v).card ≤ 2 := by
    by_contra hdeg
    have hdeg3 : 3 ≤ (G.neighborFinset v).card :=
      Nat.succ_le_of_lt (lt_of_not_ge hdeg)
    obtain ⟨s, hs_sub, hs_card⟩ :=
      Finset.exists_subset_card_eq (s := G.neighborFinset v) hdeg3
    have hs_indep : G.IsNIndepSet 3 s := by
      refine ⟨?_, hs_card⟩
      rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hab
      have hInd := G.isIndepSet_neighborSet_of_triangleFree hbad.1 v
      have ha' : a ∈ G.neighborSet v := by
        have : a ∈ G.neighborFinset v := hs_sub ha
        simpa [SimpleGraph.mem_neighborFinset] using this
      have hb' : b ∈ G.neighborSet v := by
        have : b ∈ G.neighborFinset v := hs_sub hb
        simpa [SimpleGraph.mem_neighborFinset] using this
      exact hInd ha' hb' hab
    exact hbad.2 s hs_indep
  have hdegCompl : (Gᶜ.neighborFinset v).card ≤ 2 := by
    by_contra hdeg
    have hdeg3 : 3 ≤ (Gᶜ.neighborFinset v).card :=
      Nat.succ_le_of_lt (lt_of_not_ge hdeg)
    obtain ⟨s, hs_sub, hs_card⟩ :=
      Finset.exists_subset_card_eq (s := Gᶜ.neighborFinset v) hdeg3
    have hs_indep : Gᶜ.IsNIndepSet 3 s := by
      refine ⟨?_, hs_card⟩
      rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hab
      have hInd := Gᶜ.isIndepSet_neighborSet_of_triangleFree hcfCompl v
      have ha' : a ∈ Gᶜ.neighborSet v := by
        have : a ∈ Gᶜ.neighborFinset v := hs_sub ha
        simpa [SimpleGraph.mem_neighborFinset] using this
      have hb' : b ∈ Gᶜ.neighborSet v := by
        have : b ∈ Gᶜ.neighborFinset v := hs_sub hb
        simpa [SimpleGraph.mem_neighborFinset] using this
      exact hInd ha' hb' hab
    exact hifCompl s hs_indep
  have hcomp : (Gᶜ.neighborFinset v).card =
      5 - (G.neighborFinset v).card := by
    rw [SimpleGraph.neighborFinset_compl]
    rw [Finset.card_sdiff_of_subset]
    · rw [Finset.card_singleton, Finset.card_compl, Fintype.card_fin]
      omega
    · intro x hx
      simp only [Finset.mem_singleton] at hx
      subst x
      simp
  omega

/-- The classical off-diagonal upper bound `R(3,4) ≤ 9`. -/
theorem ramseyProperty_three_four_nine : Ramsey.RamseyProperty 3 4 9 := by
  intro G hbad
  classical
  have hmax : ∀ v, G.degree v ≤ 3 := by
    intro v
    by_contra h
    have hfour : 4 ≤ (G.neighborFinset v).card := by
      rw [G.card_neighborFinset_eq_degree]
      omega
    obtain ⟨s, hs_sub, hs_card⟩ :=
      Finset.exists_subset_card_eq (s := G.neighborFinset v) hfour
    apply hbad.2 s
    refine ⟨?_, hs_card⟩
    rw [SimpleGraph.isIndepSet_iff]
    intro a ha b hb hab
    have hInd := G.isIndepSet_neighborSet_of_triangleFree hbad.1 v
    apply hInd
    · simpa [SimpleGraph.mem_neighborFinset] using hs_sub ha
    · simpa [SimpleGraph.mem_neighborFinset] using hs_sub hb
    · exact hab
  have hmin : ∀ v, 3 ≤ G.degree v := by
    intro v
    by_contra h
    have hcompdeg : 6 ≤ Gᶜ.degree v := by
      rw [G.degree_compl (v := v), Fintype.card_fin]
      omega
    let H : SimpleGraph (Gᶜ.neighborSet v) := G.induce (Gᶜ.neighborSet v)
    have hcf : H.CliqueFree 3 :=
      hbad.1.comap
        (SimpleGraph.Embedding.induce (G := G) (s := Gᶜ.neighborSet v)).isContained
    have hif : H.IndepSetFree 3 := by
      intro t ht
      let t' : Finset (Fin 9) :=
        Finset.map ⟨Subtype.val, Subtype.val_injective⟩ t
      have htInd :
          (((⊤ : SimpleGraph.Subgraph G).induce
            (Gᶜ.neighborSet v)).coe).IsNIndepSet 3 t := by
        rw [← SimpleGraph.induce_eq_coe_induce_top]
        exact ht
      have ht' : G.IsNIndepSet 3 t' := by
        simpa [H, t'] using
          (SimpleGraph.isNIndepSet_induce
            (G := G) (F := Gᶜ.neighborSet v) (s := t) (n := 3)).1 htInd
      have ht'compl : Gᶜ.IsNClique 3 t' := by simpa using ht'
      have hvt : ∀ b ∈ t', Gᶜ.Adj v b := by
        intro b hb
        rcases Finset.mem_map.mp hb with ⟨x, hx, rfl⟩
        exact x.property
      exact hbad.2 _ (by simpa using ht'compl.insert hvt)
    exact (Ramsey.ramseyProperty_of_card
      (Gᶜ.card_neighborSet_eq_degree v)
      (Ramsey.ramseyProperty_mono hcompdeg ramseyProperty_three_three_six)
      H) ⟨hcf, hif⟩
  have hregular : ∀ v, G.degree v = 3 := fun v ↦
    Nat.le_antisymm (hmax v) (hmin v)
  have hhand := G.sum_degrees_eq_twice_card_edges
  have hsum : ∑ v : Fin 9, G.degree v = 27 := by
    simp [hregular]
  rw [hsum] at hhand
  omega

/-- The recurrence `R(4,4) ≤ R(3,4)+R(4,3)` gives `R(4,4) ≤ 18`. -/
theorem ramseyProperty_four_four_eighteen : Ramsey.RamseyProperty 4 4 18 := by
  simpa using Ramsey.ramseyProperty_succ_succ_of_sum
    ramseyProperty_three_four_nine
    (ramseyProperty_symm ramseyProperty_three_four_nine)
    (by decide : 0 < 9 + 9)

/-- Every graph on two vertices needs at most one cochromatic colour. -/
theorem uniformBound_two_one : UniformBound 2 1 := by
  classical
  intro G
  refine ⟨fun _ ↦ 0, ?_⟩
  intro i
  fin_cases i
  by_cases h : G.Adj 0 1
  · left
    intro u v _ _ huv
    fin_cases u <;> fin_cases v
    all_goals first | exact h | exact h.symm | exact (huv rfl).elim
  · right
    intro u v _ _ huv
    fin_cases u <;> fin_cases v
    all_goals first
      | exact h
      | exact fun hadj ↦ h hadj.symm
      | exact (huv rfl).elim

/-- Every graph on four vertices needs at most two cochromatic colours. -/
theorem uniformBound_four_two : UniformBound 4 2 := by
  classical
  intro G
  let c : Fin 4 → Fin 2 := fun v ↦ if v.1 < 2 then 0 else 1
  refine ⟨c, ?_⟩
  intro i
  fin_cases i
  · by_cases h : G.Adj 0 1
    · left
      intro u v hu hv huv
      fin_cases u <;> fin_cases v <;> simp [c] at hu hv
      all_goals first | exact h | exact h.symm | exact (huv rfl).elim
    · right
      intro u v hu hv huv
      fin_cases u <;> fin_cases v <;> simp [c] at hu hv
      all_goals first
        | exact h
        | exact fun hadj ↦ h hadj.symm
        | exact (huv rfl).elim
  · by_cases h : G.Adj 2 3
    · left
      intro u v hu hv huv
      fin_cases u <;> fin_cases v <;> simp [c] at hu hv
      all_goals first | exact h | exact h.symm | exact (huv rfl).elim
    · right
      intro u v hu hv huv
      fin_cases u <;> fin_cases v <;> simp [c] at hu hv
      all_goals first
        | exact h
        | exact fun hadj ↦ h hadj.symm
        | exact (huv rfl).elim

/-- All upper bounds in the known table through nineteen vertices, parameterized
by the two finite certificates used in the argument. -/
theorem small_values_upper_through_nineteen_of_eight_twelve
    (upper8 : UniformBound 8 3) (upper12 : UniformBound 12 4) :
    z 1 ≤ 1 ∧ z 2 ≤ 1 ∧ z 3 ≤ 2 ∧ z 4 ≤ 2 ∧
    z 5 ≤ 3 ∧ z 6 ≤ 3 ∧ z 7 ≤ 3 ∧ z 8 ≤ 3 ∧
    z 9 ≤ 4 ∧ z 10 ≤ 4 ∧ z 11 ≤ 4 ∧ z 12 ≤ 4 ∧
    z 13 ≤ 5 ∧ z 14 ≤ 5 ∧ z 15 ≤ 5 ∧
    z 16 ≤ 6 ∧ z 17 ≤ 6 ∧ z 18 ≤ 6 ∧ z 19 ≤ 6 := by
  have u1 : UniformBound 1 1 :=
    uniformBound_mono_vertices (by decide) uniformBound_two_one
  have u2 : UniformBound 2 1 := uniformBound_two_one
  have u3 : UniformBound 3 2 :=
    uniformBound_mono_vertices (by decide) uniformBound_four_two
  have u4 : UniformBound 4 2 := uniformBound_four_two
  have u8 : UniformBound 8 3 := upper8
  have u5 : UniformBound 5 3 := uniformBound_mono_vertices (by decide) u8
  have u6 : UniformBound 6 3 := uniformBound_mono_vertices (by decide) u8
  have u7 : UniformBound 7 3 := uniformBound_mono_vertices (by decide) u8
  have r33 (n : ℕ) (hn : 6 ≤ n) : Ramsey.RamseyProperty 3 3 n :=
    Ramsey.ramseyProperty_mono hn ramseyProperty_three_three_six
  have u9 : UniformBound 9 4 := by
    simpa using uniformBound_of_ramsey (r33 9 (by decide)) u6
  have u10 : UniformBound 10 4 := by
    simpa using uniformBound_of_ramsey (r33 10 (by decide)) u7
  have u11 : UniformBound 11 4 := by
    simpa using uniformBound_of_ramsey (r33 11 (by decide)) u8
  have u12 : UniformBound 12 4 := upper12
  have u13 : UniformBound 13 5 := by
    simpa using uniformBound_of_ramsey (r33 13 (by decide)) u10
  have u14 : UniformBound 14 5 := by
    simpa using uniformBound_of_ramsey (r33 14 (by decide)) u11
  have u15 : UniformBound 15 5 := by
    simpa using uniformBound_of_ramsey (r33 15 (by decide)) u12
  have u16 : UniformBound 16 6 := by
    simpa using uniformBound_of_ramsey (r33 16 (by decide)) u13
  have u17 : UniformBound 17 6 := by
    simpa using uniformBound_of_ramsey (r33 17 (by decide)) u14
  have u18 : UniformBound 18 6 := by
    simpa using uniformBound_of_ramsey ramseyProperty_four_four_eighteen u14
  have u19 : UniformBound 19 6 := by
    simpa using uniformBound_of_ramsey
      (Ramsey.ramseyProperty_mono (by decide : 18 ≤ 19)
        ramseyProperty_four_four_eighteen) u15
  exact ⟨z_le u1, z_le u2, z_le u3, z_le u4,
    z_le u5, z_le u6, z_le u7, z_le u8,
    z_le u9, z_le u10, z_le u11, z_le u12,
    z_le u13, z_le u14, z_le u15,
    z_le u16, z_le u17, z_le u18, z_le u19⟩

/-- The upper-bound half of the complete table of values through nineteen vertices. -/
theorem small_values_upper_bounds :
    z 1 ≤ 1 ∧ z 2 ≤ 1 ∧ z 3 ≤ 2 ∧ z 4 ≤ 2 ∧
    z 5 ≤ 3 ∧ z 6 ≤ 3 ∧ z 7 ≤ 3 ∧ z 8 ≤ 3 ∧
    z 9 ≤ 4 ∧ z 10 ≤ 4 ∧ z 11 ≤ 4 ∧ z 12 ≤ 4 ∧
    z 13 ≤ 5 ∧ z 14 ≤ 5 ∧ z 15 ≤ 5 ∧
    z 16 ≤ 6 ∧ z 17 ≤ 6 ∧ z 18 ≤ 6 ∧ z 19 ≤ 6 :=
  small_values_upper_through_nineteen_of_eight_twelve
    every_graph_on_eight_colorable_three every_graph_on_twelve_colorable_four

#print axioms ramseyProperty_three_three_six
#print axioms ramseyProperty_three_four_nine
#print axioms ramseyProperty_four_four_eighteen
#print axioms small_values_upper_bounds

end Erdos758
