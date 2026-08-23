import ErdosProblems.Erdos1105.OrePath

/-!
# Degree-sequence obstructions to Hamiltonicity

The counting form of Chvátal's theorem, obtained by taking two maximal-degree
nonadjacent vertices in the Bondy--Chvátal closure. This is an ingredient in
the finite-order extremal and stability arguments for the path upper bound.
-/

namespace Erdos1105

open SimpleGraph Finset

theorem closed_degree_obstruction {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G ≠ ⊤)
    (hclosed : ∀ x y, x ≠ y → ¬G.Adj x y → G.degree x + G.degree y < Fintype.card V) :
    ∃ x : V, 2 * G.degree x < Fintype.card V ∧
      G.degree x ≤ (univ.filter fun v ↦ G.degree v ≤ G.degree x).card ∧
      (univ.filter fun v ↦ Fintype.card V - G.degree x ≤ G.degree v).card ≤ G.degree x := by
  classical
  have hnonedge : ∃ a b, a ≠ b ∧ ¬G.Adj a b := by
    by_contra h
    push Not at h
    apply hG
    apply le_antisymm le_top
    intro a b hab
    exact h a b hab
  let U : Finset V := univ.filter fun v ↦ ¬G.IsUniversal v
  have hU : U.Nonempty := by
    obtain ⟨a, b, hab, hnab⟩ := hnonedge
    exact ⟨a, mem_filter.mpr ⟨mem_univ _, fun ha ↦ hnab (ha hab)⟩⟩
  obtain ⟨y, hy, hymax⟩ := U.exists_max_image (fun v ↦ G.degree v) hU
  have hyU : ¬G.IsUniversal y := (mem_filter.mp hy).2
  have hN : (Gᶜ.neighborFinset y).Nonempty := by
    rw [← card_pos, card_neighborFinset_eq_degree, degree_compl]
    have := (G.degree_lt_card_sub_one y).mpr hyU
    omega
  obtain ⟨x, hx, hxmax⟩ := (Gᶜ.neighborFinset y).exists_max_image (fun v ↦ G.degree v) hN
  have hxy : y ≠ x ∧ ¬G.Adj y x := by simpa using hx
  have hxU : x ∈ U := by
    simp only [U, mem_filter, mem_univ, true_and]
    exact fun h ↦ hxy.2 (h hxy.1.symm).symm
  have hdxdy := hymax x hxU
  have hsum := hclosed y x hxy.1 hxy.2
  refine ⟨x, by omega, ?_, ?_⟩
  · have hsub : Gᶜ.neighborFinset y ⊆ univ.filter (fun v ↦ G.degree v ≤ G.degree x) := by
      intro z hz
      exact mem_filter.mpr ⟨mem_univ _, hxmax z hz⟩
    have hcard := card_le_card hsub
    rw [card_neighborFinset_eq_degree, degree_compl] at hcard
    omega
  · have hsub : (univ.filter fun v ↦ Fintype.card V - G.degree x ≤ G.degree v) ⊆
        G.neighborFinset x := by
      intro z hz
      have hzdeg := (mem_filter.mp hz).2
      have hzU : G.IsUniversal z := by
        by_contra h
        have hzmax := hymax z (mem_filter.mpr ⟨mem_univ _, h⟩)
        omega
      have hzx : z ≠ x := by
        intro h
        subst z
        omega
      simpa using (hzU hzx).symm
    simpa using card_le_card hsub

/-- Chvátal's non-Hamiltonian degree-sequence obstruction, stated without
choosing a sorted enumeration of the vertices. -/
theorem nonhamiltonian_degree_obstruction {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hV : 3 ≤ Fintype.card V)
    (hG : ¬G.IsHamiltonian) {d : ℕ} (hmin : ∀ v, d ≤ G.degree v) :
    ∃ i : ℕ, d ≤ i ∧ 2 * i < Fintype.card V ∧
      i ≤ (univ.filter fun v ↦ G.degree v ≤ i).card ∧
      (univ.filter fun v ↦ Fintype.card V - i ≤ G.degree v).card ≤ i := by
  classical
  have hnot : G.closure ≠ ⊤ := by
    intro htop
    apply hG
    apply (from_closure_iff (G := G)).mp
    rw [htop]
    exact hamiltonian_of_distinct_degree_sum ⊤ hV (by
      intro x y hxy
      rw [((⊤ : SimpleGraph V).degree_eq_card_sub_one x).mpr (by simp [IsUniversal]),
        ((⊤ : SimpleGraph V).degree_eq_card_sub_one y).mpr (by simp [IsUniversal])]
      omega)
  have hclosed : ∀ x y, x ≠ y → ¬G.closure.Adj x y →
      G.closure.degree x + G.closure.degree y < Fintype.card V := by
    intro x y hxy hnxy
    by_contra h
    exact hnxy (G.closure_spec hxy (by omega))
  obtain ⟨x, hi, hlow, hhigh⟩ := closed_degree_obstruction G.closure hnot hclosed
  refine ⟨G.closure.degree x, (hmin x).trans (G.degree_le_of_le G.self_le_closure), hi, ?_, ?_⟩
  · apply hlow.trans (card_le_card ?_)
    intro v hv
    exact mem_filter.mpr ⟨mem_univ _, (G.degree_le_of_le G.self_le_closure).trans
      (mem_filter.mp hv).2⟩
  · apply le_trans (card_le_card ?_) hhigh
    intro v hv
    exact mem_filter.mpr ⟨mem_univ _, ((mem_filter.mp hv).2).trans
      (G.degree_le_of_le G.self_le_closure)⟩

/-- Counting the degrees in Chvátal's two exceptional sets. -/
theorem edges_le_of_degree_obstruction {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {i : ℕ}
    (hi : 2 * i < Fintype.card V)
    (hlow : i ≤ (univ.filter fun v ↦ G.degree v ≤ i).card)
    (hhigh : (univ.filter fun v ↦ Fintype.card V - i ≤ G.degree v).card ≤ i) :
    G.edgeFinset.card ≤ (Fintype.card V - i).choose 2 + i * i := by
  classical
  let n := Fintype.card V
  obtain ⟨S, hS, hScard⟩ := exists_subset_card_eq hlow
  have hSbound : ∑ v ∈ S, G.degree v ≤ i * i := by
    calc
      _ ≤ ∑ _v ∈ S, i := sum_le_sum fun v hv ↦ (mem_filter.mp (hS hv)).2
      _ = i * i := by simp [hScard]
  have hrest (v : V) : G.degree v ≤ n - i - 1 + if n - i ≤ G.degree v then i else 0 := by
    have hv := G.degree_lt_card_verts v
    dsimp only [n]
    split_ifs <;> omega
  have hfreq : ∑ v ∈ Sᶜ, (if n - i ≤ G.degree v then i else 0) ≤ i * i := by
    calc
      _ = (Sᶜ.filter fun v ↦ n - i ≤ G.degree v).card * i := by simp [sum_ite]
      _ ≤ i * i := Nat.mul_le_mul_right i ((card_le_card (by
        intro v hv
        exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hv).2⟩)).trans hhigh)
  have hrestbound : ∑ v ∈ Sᶜ, G.degree v ≤ (n - i) * (n - i - 1) + i * i := by
    calc
      _ ≤ ∑ v ∈ Sᶜ, (n - i - 1 + if n - i ≤ G.degree v then i else 0) :=
        sum_le_sum fun v _ ↦ hrest v
      _ = (n - i) * (n - i - 1) +
          ∑ v ∈ Sᶜ, (if n - i ≤ G.degree v then i else 0) := by
        rw [sum_add_distrib]
        simp only [sum_const, smul_eq_mul, card_compl, hScard, n]
      _ ≤ _ := Nat.add_le_add_left hfreq _
  have hsum := sum_add_sum_compl S (fun v ↦ G.degree v)
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  have hchoose : 2 * (n - i).choose 2 = (n - i) * (n - i - 1) := by
    have hr := Nat.cast_choose_two ℝ (n - i)
    have hni : 1 ≤ n - i := by dsimp [n]; omega
    have hcast : ((n - i - 1 : ℕ) : ℝ) = (n - i : ℕ) - 1 := by
      rw [Nat.cast_sub hni, Nat.cast_one]
    have hh : (2 : ℝ) * ((n - i).choose 2 : ℝ) =
        (n - i : ℕ) * (n - i - 1 : ℕ) := by rw [hr, hcast]; ring
    exact_mod_cast hh
  dsimp only [n] at hchoose hrestbound
  omega

/-- The Erdős non-Hamiltonian edge bound at the obstructing degree. -/
theorem nonhamiltonian_edge_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hV : 3 ≤ Fintype.card V)
    (hG : ¬G.IsHamiltonian) {d : ℕ} (hmin : ∀ v, d ≤ G.degree v) :
    ∃ i : ℕ, d ≤ i ∧ 2 * i < Fintype.card V ∧
      G.edgeFinset.card ≤ (Fintype.card V - i).choose 2 + i * i := by
  classical
  obtain ⟨i, hdi, hi, hlow, hhigh⟩ := nonhamiltonian_degree_obstruction G hV hG hmin
  exact ⟨i, hdi, hi, edges_le_of_degree_obstruction G hi hlow hhigh⟩

end Erdos1105

#print axioms Erdos1105.nonhamiltonian_degree_obstruction
#print axioms Erdos1105.nonhamiltonian_edge_bound
