import ErdosProblems.Erdos745.FinitePaths
import ErdosProblems.Erdos745.Harris
import ErdosProblems.Erdos745.PathHeightBound
import ErdosProblems.Erdos745.ProbabilityBounds

/-! # Uniform critical simple-path probability estimates -/

open scoped BigOperators

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

theorem probability_vertexPathFrom_le {n : ℕ} (hn : 2 ≤ n) (h : ℕ)
    (S : Finset (Fin n)) (r : Fin n) :
    probability 1 n (fun G ↦ VertexPathFrom G S r h) ≤ pathHeightBound n h := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  induction h generalizing S r with
  | zero => exact probability_le_one _ _ _
  | succ h ih =>
    let B := fun u (G : SimpleGraph (Fin n)) ↦ G.Adj r u ∧ VertexPathFrom G (S.erase r) u h
    have hb (u : Fin n) (hu : u ∈ S.erase r) :
        probability 1 n (B u) ≤ pathHeightBound n h / n := by
      have hru : r ≠ u := (Finset.ne_of_mem_erase hu).symm
      change probability 1 n (fun G ↦ G.Adj r u ∧ VertexPathFrom G (S.erase r) u h) ≤ _
      rw [probability_vertexPathFrom_branch _ _ _ _ _ _ hru, edgeProbability_one,
        coe_criticalEdgeProbability hn0]
      have hi := mul_le_mul_of_nonneg_left (ih (S.erase r) u)
        (by positivity : (0 : ℝ) ≤ 1 / n)
      simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hi
    have harris := probability_lower_forall 1 n (S.erase r) (fun u G ↦ ¬ B u G)
      (by
        intro u _ G H hGH hH hG
        exact hH ⟨hGH hG.1, vertexPathFrom_mono hGH hG.2⟩)
    have hno : probability 1 n (fun G ↦ ∀ u ∈ S.erase r, ¬ B u G) ≤
        probability 1 n (fun G ↦ ¬ VertexPathFrom G S r (h + 1)) := by
      apply probability_mono
      intro G hG hp
      obtain ⟨_, u, hu, hru, ht⟩ := (vertexPathFrom_succ G S r).mp hp
      exact hG u hu ⟨hru, ht⟩
    have hq := pathHeightBound_mem hn h
    have hbase : 0 ≤ 1 - pathHeightBound n h / n := by
      have hd : pathHeightBound n h / n ≤ 1 :=
        (div_le_one (by positivity)).mpr (hq.2.trans hnR)
      linarith
    have hbase1 : 1 - pathHeightBound n h / n ≤ 1 := by
      have hd : 0 ≤ pathHeightBound n h / n := div_nonneg hq.1 (by positivity)
      linarith
    have hprod : (1 - pathHeightBound n h / n) ^ (S.erase r).card ≤
        ∏ u ∈ S.erase r, probability 1 n (fun G ↦ ¬ B u G) := by
      rw [← Finset.prod_const]
      apply Finset.prod_le_prod (fun _ _ ↦ hbase)
      intro u hu
      rw [probability_not]
      linarith [hb u hu]
    have hcard : (S.erase r).card ≤ n := by simpa using Finset.card_le_univ (S.erase r)
    have hpow := pow_le_pow_of_le_one hbase hbase1 hcard
    have htotal := hpow.trans (hprod.trans (harris.trans hno))
    rw [probability_not] at htotal
    change probability 1 n (fun G ↦ VertexPathFrom G S r (h + 1)) ≤
      1 - (1 - pathHeightBound n h / n) ^ n
    linarith

theorem probability_vertexPathFrom_le_inverse {n : ℕ} (hn : 2 ≤ n) (h : ℕ)
    (S : Finset (Fin n)) (r : Fin n) :
    probability 1 n (fun G ↦ VertexPathFrom G S r h) ≤
      (1 / pathHeightDecay) / ((h : ℝ) + 1) :=
  (probability_vertexPathFrom_le hn h S r).trans (pathHeightBound_le hn h)

theorem probability_const (lam : ℝ) (n : ℕ) (P : Prop) :
    probability lam n (fun _ ↦ P) = if P then 1 else 0 := by
  by_cases hP : P <;> simp [hP]

/-- The expected number of possible endpoints at a fixed simple-path length
is at most one at criticality. Multiple paths to the same endpoint cause no issue. -/
theorem sum_probability_vertexPath_le {n : ℕ} (hn : 0 < n) (h : ℕ)
    (S : Finset (Fin n)) (r : Fin n) :
    (∑ v : Fin n, probability 1 n (fun G ↦ VertexPath G S r v h)) ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  induction h generalizing S r with
  | zero =>
    by_cases hr : r ∈ S
    · simp only [VertexPath, hr, true_and, probability_const]
      rw [Finset.sum_eq_single r]
      · simp
      · intro v _ hvr
        exact if_neg hvr.symm
      · simp
    · simp [VertexPath, hr]
  | succ h ih =>
    have hrow (v : Fin n) :
        probability 1 n (fun G ↦ VertexPath G S r v (h + 1)) ≤
          ∑ u ∈ S.erase r, (1 / (n : ℝ)) *
            probability 1 n (fun G ↦ VertexPath G (S.erase r) u v h) := by
      calc
        _ ≤ probability 1 n (fun G ↦ ∃ u ∈ S.erase r,
            G.Adj r u ∧ VertexPath G (S.erase r) u v h) :=
          probability_mono (fun _ hp ↦ hp.2)
        _ ≤ ∑ u ∈ S.erase r, probability 1 n
            (fun G ↦ G.Adj r u ∧ VertexPath G (S.erase r) u v h) :=
          probability_exists_finset_le _ _ _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [probability_vertexPath_branch _ _ _ _ _ _ _
            (Finset.ne_of_mem_erase hu).symm, edgeProbability_one,
            coe_criticalEdgeProbability hn.ne']
    calc
      _ ≤ ∑ v : Fin n, ∑ u ∈ S.erase r, (1 / (n : ℝ)) *
          probability 1 n (fun G ↦ VertexPath G (S.erase r) u v h) :=
        Finset.sum_le_sum (fun v _ ↦ hrow v)
      _ = ∑ u ∈ S.erase r, (1 / (n : ℝ)) *
          ∑ v : Fin n, probability 1 n (fun G ↦ VertexPath G (S.erase r) u v h) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ ≤ ∑ _u ∈ S.erase r, (1 / (n : ℝ)) * 1 := by
        exact Finset.sum_le_sum (fun u _ ↦ mul_le_mul_of_nonneg_left (ih _ u) (by positivity))
      _ = ((S.erase r).card : ℝ) / n := by simp [div_eq_mul_inv]
      _ ≤ 1 := by
        rw [div_le_one hnR]
        exact_mod_cast (show (S.erase r).card ≤ n by simpa using Finset.card_le_univ (S.erase r))

/-- Vertices reached by a simple path of length strictly below `h`. -/
def shortPathCount {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (r : Fin n) (h : ℕ) : ℕ :=
  (Finset.univ.filter fun v ↦ ∃ j ∈ Finset.range h, VertexPath G S r v j).card

theorem expectation_shortPathCount_le {n : ℕ} (hn : 0 < n) (h : ℕ)
    (S : Finset (Fin n)) (r : Fin n) :
    expectation 1 n (fun G ↦ (shortPathCount G S r h : ℝ)) ≤ h := by
  have hcount : expectation 1 n (fun G ↦ (shortPathCount G S r h : ℝ)) =
      ∑ v : Fin n, probability 1 n (fun G ↦ ∃ j ∈ Finset.range h, VertexPath G S r v j) := by
    convert! expectation_card_filter 1 n Finset.univ
      (fun v G ↦ ∃ j ∈ Finset.range h, VertexPath G S r v j) using 1
    congr 1
    funext G
    unfold shortPathCount
    congr 2
    ext v
    simp only [Finset.mem_filter]
  rw [hcount]
  calc
    _ ≤ ∑ v : Fin n, ∑ j ∈ Finset.range h,
        probability 1 n (fun G ↦ VertexPath G S r v j) :=
      Finset.sum_le_sum (fun v _ ↦ probability_exists_finset_le _ _ _ _)
    _ = ∑ j ∈ Finset.range h, ∑ v : Fin n,
        probability 1 n (fun G ↦ VertexPath G S r v j) := Finset.sum_comm
    _ ≤ ∑ _j ∈ Finset.range h, (1 : ℝ) :=
      Finset.sum_le_sum (fun j _ ↦ sum_probability_vertexPath_le hn j S r)
    _ = _ := by simp

end

end Erdos745
