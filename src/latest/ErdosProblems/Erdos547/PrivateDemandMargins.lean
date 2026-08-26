import ErdosProblems.Erdos547.ClusterPrivateSets
import ErdosProblems.Erdos547.SkewHeadBudgets
import ErdosProblems.Erdos547.SetupMargins

/-!
# Relative allocation slack supplies the separate and joint private-set demands
-/

namespace Erdos547

open Finset
open scoped BigOperators

theorem sum_two_distinct_colours (f : Fin 2 → ℝ) (a b : Fin 2) (hab : a ≠ b) :
    (∑ c, f c) = f a + f b := by
  fin_cases a <;> fin_cases b <;> simp_all [Fin.sum_univ_two, add_comm]

theorem max_two_distinct_colours (f : Fin 2 → ℝ) (a b : Fin 2) (hab : a ≠ b) :
    max (f 0) (f 1) = max (f a) (f b) := by
  fin_cases a <;> fin_cases b <;> simp_all [max_comm]

open scoped Classical in
theorem exists_private_sets_from_relative_demands {F V I : Type*} [Fintype F] [DecidableEq I]
    (cluster : I → Finset V) (head : F → I) (col : F → Fin 2)
    (demand : F → ℕ) (candidates : F → Finset V) (w density : Fin 2 → I → ℝ)
    (M s ε θ : ℝ) (hM : 0 ≤ M) (hs : 0 ≤ s) (hsone : s ≤ 1) (hε : ε ≤ s * θ)
    (hcluster : ∀ i j, i ≠ j → Disjoint (cluster i) (cluster j))
    (hsub : ∀ x, candidates x ⊆ cluster (head x))
    (hfit : ∀ c i, w c i ≤ density c i)
    (hjoint : ∀ i, w 0 i + w 1 i ≤ max (density 0 i) (density 1 i))
    (hactive : ∀ x, θ ≤ w (col x) (head x))
    (hload : ∀ c i, (∑ x ∈ (Finset.univ : Finset F).filter
      (fun x ↦ head x = i ∧ col x = c), (demand x : ℝ)) ≤ (1 - s) * M * w c i)
    (hsize : ∀ x, (density (col x) (head x) - ε) * M ≤ ((candidates x).card : ℝ)) :
    ∃ R : F → Finset V, (∀ x, R x ⊆ candidates x) ∧
      (∀ x, (R x).card = demand x) ∧ Pairwise (fun x y ↦ Disjoint (R x) (R y)) := by
  classical
  apply exists_clusterwise_private_sets cluster head col demand candidates
    (fun i c ↦ (density c i - ε) * M) hcluster hsub
  · intro x
    have herror : ε ≤ s * density (col x) (head x) := hε.trans
      (mul_le_mul_of_nonneg_left ((hactive x).trans (hfit _ _)) hs)
    exact (hload (col x) (head x)).trans
      (relative_capacity_fits M s ε (density (col x) (head x)) (w (col x) (head x))
        hM hsone (hfit _ _) herror)
  · intro x y _hhead hxy
    let load : Fin 2 → ℝ := fun c ↦ ∑ z ∈ (Finset.univ : Finset F).filter
      (fun z ↦ head z = head x ∧ col z = c), (demand z : ℝ)
    have hsum : (∑ z ∈ (Finset.univ : Finset F).filter (fun z ↦ head z = head x),
        (demand z : ℝ)) = load (col x) + load (col y) := by
      have hh := sum_group_condition col (fun z ↦ head z = head x) (fun z ↦ (demand z : ℝ))
      have he : (∑ c, load c) = ∑ z ∈ (Finset.univ : Finset F).filter
          (fun z ↦ head z = head x), (demand z : ℝ) := by
        simpa only [load, and_comm, Finset.sum_filter] using hh
      rw [← he]
      exact sum_two_distinct_colours load (col x) (col y) hxy
    have hw : w (col x) (head x) + w (col y) (head x) ≤
        max (density (col x) (head x)) (density (col y) (head x)) := by
      have hsumw := sum_two_distinct_colours (fun c ↦ w c (head x)) (col x) (col y) hxy
      rw [Fin.sum_univ_two] at hsumw
      have hmax := max_two_distinct_colours (fun c ↦ density c (head x)) (col x) (col y) hxy
      have hh := hjoint (head x)
      rwa [hsumw, hmax] at hh
    let D := max (density (col x) (head x)) (density (col y) (head x))
    have herror : ε ≤ s * D := hε.trans (mul_le_mul_of_nonneg_left
      (((hactive x).trans (hfit _ _)).trans (le_max_left _ _)) hs)
    have hfit' := relative_capacity_fits M s ε D (w (col x) (head x) + w (col y) (head x))
      hM hsone hw herror
    have htotal : load (col x) + load (col y) ≤
        (1 - s) * M * (w (col x) (head x) + w (col y) (head x)) := by
      have hx := hload (col x) (head x)
      have hy := hload (col y) (head x)
      change load (col x) ≤ _ at hx
      change load (col y) ≤ _ at hy
      nlinarith only [hx, hy]
    rw [hsum]
    apply (htotal.trans hfit').trans
    dsimp only [D]
    rcases le_total (density (col x) (head x)) (density (col y) (head x)) with h | h
    · rw [max_eq_right h]
      exact le_max_right _ _
    · rw [max_eq_left h]
      exact le_max_left _ _
  · exact hsize

end Erdos547

#print axioms Erdos547.exists_private_sets_from_relative_demands
