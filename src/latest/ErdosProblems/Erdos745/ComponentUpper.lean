import ErdosProblems.Erdos745.PathProbability

/-!
# Finite critical component upper bounds

A component is either visible at height `h` or fits in the short-path ball.
A second first-moment argument counts vertices in large components.
-/

open scoped BigOperators

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The size of the connected component containing a specified vertex. -/
def rootComponentOrder {n : ℕ} (G : SimpleGraph (Fin n)) (r : Fin n) : ℕ :=
  (G.connectedComponentMk r).supp.ncard

theorem rootComponentOrder_le_shortPathCount {n h : ℕ} (G : SimpleGraph (Fin n))
    (r : Fin n) (hno : ¬ VertexPathFrom G Finset.univ r h) :
    rootComponentOrder G r ≤ shortPathCount G Finset.univ r h := by
  unfold rootComponentOrder shortPathCount
  rw [Set.ncard_eq_toFinset_card']
  apply Finset.card_le_card
  intro v hv
  have hvr : v ∈ (G.connectedComponentMk r).supp := Set.mem_toFinset.mp hv
  obtain ⟨p, hp⟩ := ((G.connectedComponentMk r).reachable_of_mem_supp
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem hvr).exists_isPath
  have hlen : p.length < h := by
    by_contra hnot
    have hhp : h ≤ p.length := by omega
    have hpath := vertexPath_of_walk (p.take h) (hp.take h) Finset.univ
      (fun _ _ ↦ Finset.mem_univ _)
    rw [SimpleGraph.Walk.take_length, inf_eq_left.mpr hhp] at hpath
    exact hno ⟨_, hpath⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.length, Finset.mem_range.mpr hlen,
    vertexPath_of_walk p hp Finset.univ (fun _ _ ↦ Finset.mem_univ _)⟩

theorem probability_rootComponentOrder_le {n : ℕ} (hn : 2 ≤ n)
    (r : Fin n) {k : ℕ} (hk : 0 < k) (h : ℕ) :
    probability 1 n (fun G ↦ k ≤ rootComponentOrder G r) ≤
      (1 / pathHeightDecay) / ((h : ℝ) + 1) + (h : ℝ) / k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsubset : probability 1 n (fun G ↦ k ≤ rootComponentOrder G r) ≤
      probability 1 n (fun G ↦ VertexPathFrom G Finset.univ r h ∨
        (k : ℝ) ≤ (shortPathCount G Finset.univ r h : ℝ)) := by
    apply probability_mono
    intro G hG
    by_cases hp : VertexPathFrom G Finset.univ r h
    · exact Or.inl hp
    · right
      exact_mod_cast hG.trans (rootComponentOrder_le_shortPathCount G r hp)
  have hmarkov : probability 1 n
      (fun G ↦ (k : ℝ) ≤ (shortPathCount G Finset.univ r h : ℝ)) ≤ (h : ℝ) / k := by
    apply (probability_ge_le_expectation_div hkR (fun _ ↦ Nat.cast_nonneg _)).trans
    exact div_le_div_of_nonneg_right
      (expectation_shortPathCount_le (by omega) h Finset.univ r) hkR.le
  exact hsubset.trans ((probability_or_le 1 n _ _).trans
    (add_le_add (probability_vertexPathFrom_le_inverse hn h Finset.univ r) hmarkov))

/-- Number of vertices in components whose order is at least `k`. -/
def largeComponentVertexCount {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun r ↦ k ≤ rootComponentOrder G r).card

theorem componentOrder_le_largeComponentVertexCount {n k : ℕ} (G : SimpleGraph (Fin n))
    (C : G.ConnectedComponent) (hC : k ≤ C.supp.ncard) :
    C.supp.ncard ≤ largeComponentVertexCount G k := by
  unfold largeComponentVertexCount
  rw [Set.ncard_eq_toFinset_card']
  apply Finset.card_le_card
  intro r hr
  have heq := (C.mem_supp_iff r).mp (Set.mem_toFinset.mp hr)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  simpa only [rootComponentOrder, heq] using hC

theorem le_largeComponentVertexCount_of_le_second {n k : ℕ}
    (G : SimpleGraph (Fin n)) (hk : 0 < k) (hG : k ≤ secondLargestComponentOrder G) :
    k ≤ largeComponentVertexCount G k := by
  obtain ⟨C, D, _, hC, _⟩ := (le_secondLargestComponentOrder_iff_exists G hk).mp hG
  exact hC.trans (componentOrder_le_largeComponentVertexCount G C hC)

theorem expectation_largeComponentVertexCount_le {n : ℕ} (hn : 2 ≤ n)
    {k : ℕ} (hk : 0 < k) (h : ℕ) :
    expectation 1 n (fun G ↦ (largeComponentVertexCount G k : ℝ)) ≤
      (n : ℝ) * ((1 / pathHeightDecay) / ((h : ℝ) + 1) + (h : ℝ) / k) := by
  have hcount : expectation 1 n (fun G ↦ (largeComponentVertexCount G k : ℝ)) =
      ∑ r : Fin n, probability 1 n (fun G ↦ k ≤ rootComponentOrder G r) := by
    convert! expectation_card_filter 1 n Finset.univ
      (fun r G ↦ k ≤ rootComponentOrder G r) using 1
    congr 1
    funext G
    unfold largeComponentVertexCount
    congr 2
    ext r
    simp only [Finset.mem_filter]
  rw [hcount]
  calc
    _ ≤ ∑ _r : Fin n, ((1 / pathHeightDecay) / ((h : ℝ) + 1) + (h : ℝ) / k) :=
      Finset.sum_le_sum (fun r _ ↦ probability_rootComponentOrder_le hn r hk h)
    _ = _ := by simp; ring

/-- A finite two-parameter tail bound, valid before any asymptotic limit. -/
theorem critical_secondLargest_tail {n : ℕ} (hn : 2 ≤ n) {k : ℕ} (hk : 0 < k)
    (h : ℕ) :
    probability 1 n (fun G ↦ k ≤ secondLargestComponentOrder G) ≤
      (n : ℝ) / k * ((1 / pathHeightDecay) / ((h : ℝ) + 1) + (h : ℝ) / k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    _ ≤ probability 1 n (fun G ↦ (k : ℝ) ≤ (largeComponentVertexCount G k : ℝ)) := by
      apply probability_mono
      intro G hG
      exact_mod_cast le_largeComponentVertexCount_of_le_second G hk hG
    _ ≤ expectation 1 n (fun G ↦ (largeComponentVertexCount G k : ℝ)) / k :=
      probability_ge_le_expectation_div hkR (fun _ ↦ Nat.cast_nonneg _)
    _ ≤ ((n : ℝ) * ((1 / pathHeightDecay) / ((h : ℝ) + 1) + (h : ℝ) / k)) / k :=
      div_le_div_of_nonneg_right (expectation_largeComponentVertexCount_le hn hk h) hkR.le
    _ = _ := by ring

end

end Erdos745
