import ErdosProblems.Erdos547.GreedyAllowances
import ErdosProblems.Erdos547.FractionalCut
import ErdosProblems.Erdos547.DeficitSaturation
import ErdosProblems.Erdos547.MatchingCombination

/-!
# Residual demand and capacity on an allowed vertex set
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {γ δ : ℝ}

open scoped Classical in
def freeCapacity (β : SkewMatching G γ) (U : Finset V) (u : V) : ℝ :=
  if u ∈ U then 1 - β.load u else 0

theorem freeCapacity_nonneg (β : SkewMatching G γ) (U : Finset V) (u : V) :
    0 ≤ freeCapacity β U u := by
  classical
  dsimp [freeCapacity]
  split_ifs
  · exact sub_nonneg.mpr (β.load_le_one u)
  · exact le_rfl

theorem freeCapacity_le_one (β : SkewMatching G γ) (U : Finset V) (u : V) :
    freeCapacity β U u ≤ 1 := by
  classical
  dsimp [freeCapacity]
  split_ifs <;> linarith [β.load_nonneg u]

theorem tailAllowance_le_freeCapacity (w : EdgeWeights G) (d : V)
    (β : SkewMatching G γ) (U : Finset V) (u : V) :
    tailAllowance w d β.load U u ≤ freeCapacity β U u := by
  classical
  by_cases hu : u ∈ U
  · rw [freeCapacity, if_pos hu]
    exact tailAllowance_le_capacity w d β.load β.load_le_one U u
  · simp only [tailAllowance, freeCapacity, if_neg hu, le_refl]

theorem inside_load_le_freeCapacity (μ : FractionalMatching G) (β : SkewMatching G γ)
    (hcap : ∀ u, μ.load u + β.load u ≤ 1) (U : Finset V) (u : V) :
    (μ.inside (U : Set V)).load u ≤ freeCapacity β U u := by
  classical
  by_cases hu : u ∈ U
  · rw [freeCapacity, if_pos hu]
    linarith [μ.inside_load_le (U : Set V) u, hcap u]
  · rw [freeCapacity, if_neg hu, μ.inside_load_of_notMem hu]

omit [DecidableEq V] in
theorem degreeOn_sub_load_le_total_allowance (w : EdgeWeights G) (d : V)
    (β : SkewMatching G γ) (U : Finset V) :
    w.degreeOn U d - (∑ u ∈ U, β.load u) ≤ ∑ u, tailAllowance w d β.load U u := by
  have hh := degreeOn_sub_load_le_allowance_sum w d β.load U U (fun _ h ↦ h)
  exact hh.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun u _ _ ↦ tailAllowance_nonneg w d β.load U u))

open scoped Classical in
theorem degreeOn_sub_load_le_neighbour_freeCapacity (w : EdgeWeights G) (d : V)
    (β : SkewMatching G γ) (U : Finset V) :
    w.degreeOn U d - (∑ u ∈ U, β.load u) ≤
      ∑ u ∈ Finset.univ.filter (G.Adj d), freeCapacity β U u := by
  classical
  apply (degreeOn_sub_load_le_total_allowance w d β U).trans
  calc
    _ = ∑ u ∈ Finset.univ.filter (G.Adj d), tailAllowance w d β.load U u := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro u _ hu
      have hdu : ¬ G.Adj d u := fun h ↦ hu (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      dsimp [tailAllowance]
      split_ifs
      · rw [w.supported d u hdu, max_eq_left (by linarith [β.load_nonneg u])]
      · rfl
    _ ≤ _ := Finset.sum_le_sum fun u _ ↦ tailAllowance_le_freeCapacity w d β U u

open scoped Classical in
theorem exists_skew_on_free_set_of_deficit_bound (w : EdgeWeights G) (d : V)
    (β : SkewMatching G δ) (U good : Finset V) (A D₀ γ : ℝ) (hA : 0 ≤ A) (hγ : 0 ≤ γ)
    (μ₀ : FractionalMatching G) (hcap : ∀ u, μ₀.load u ≤ freeCapacity β U u)
    (hgood : ∀ z ∈ good, A ≤ w.degreeOn U z - ∑ u ∈ U, β.load u)
    (hbad : (∑ u ∈ goodᶜ, max 0 (tailAllowance w d β.load U u - μ₀.load u)) ≤ D₀)
    (hsize : A + D₀ ≤ w.degreeOn U d - ∑ u ∈ U, β.load u) :
    ∃ α : SkewMatching G γ, α.total = A ∧
      α.Fits (w.truncate β.load β.load_nonneg) d ∧
      (∀ u, α.load u + β.load u ≤ 1) ∧ (∀ u ∉ U, α.load u = 0) := by
  classical
  obtain ⟨μ, hμ, hs⟩ := exists_fractional_saturation_of_deficit_bound G
    (tailAllowance w d β.load U) (freeCapacity β U) A D₀
    (tailAllowance_nonneg w d β.load U) (tailAllowance_le_freeCapacity w d β U)
    (freeCapacity_le_one β U) μ₀ hcap good
    (fun z hz ↦ (hgood z hz).trans (degreeOn_sub_load_le_neighbour_freeCapacity w z β U))
    hbad (hsize.trans (degreeOn_sub_load_le_total_allowance w d β U))
  have hsat : A ≤ (w.truncate β.load β.load_nonneg).saturation μ.load d := by
    apply hs.trans
    exact Finset.sum_le_sum fun u _ ↦ min_le_min_right _ (tailAllowance_le w d β.load U u)
  obtain ⟨α, hα, hfit, ht⟩ := exists_skew_of_saturation_exact μ
    (w.truncate β.load β.load_nonneg) d γ hγ A hA hsat
  refine ⟨α, ht, hfit, ?_, ?_⟩
  · intro u
    have hl : freeCapacity β U u ≤ 1 - β.load u := by
      dsimp [freeCapacity]
      split_ifs
      · exact le_rfl
      · exact sub_nonneg.mpr (β.load_le_one u)
    linarith [(hα.load_le u).trans ((hμ u).trans hl)]
  · intro u hu
    have hz : freeCapacity β U u = 0 := if_neg hu
    exact le_antisymm (by simpa only [hz] using (hα.load_le u).trans (hμ u))
      (α.load_nonneg u)

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_skew_on_free_set_of_deficit_bound
