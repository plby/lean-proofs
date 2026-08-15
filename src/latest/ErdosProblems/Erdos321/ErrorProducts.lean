import ErdosProblems.Erdos321.KernelErrorOrbit

namespace Erdos321

open Filter
open scoped Topology

private theorem one_sub_sum_le_prod_one_sub
    (l : List ℝ) (h0 : ∀ a ∈ l, 0 ≤ a) (h1 : ∀ a ∈ l, a ≤ 1) :
    1 - l.sum ≤ (l.map (fun a => 1 - a)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha0 : 0 ≤ a := h0 a (by simp)
      have ha1 : a ≤ 1 := h1 a (by simp)
      have htail0 : ∀ b ∈ l, 0 ≤ b := by
        intro b hb
        exact h0 b (by simp [hb])
      have htail1 : ∀ b ∈ l, b ≤ 1 := by
        intro b hb
        exact h1 b (by simp [hb])
      have hsum0 : 0 ≤ l.sum := List.sum_nonneg htail0
      have hih := ih htail0 htail1
      simp only [List.sum_cons, List.map_cons, List.prod_cons]
      calc
        1 - (a + l.sum) ≤ (1 - a) * (1 - l.sum) := by
          nlinarith [mul_nonneg ha0 hsum0]
        _ ≤ (1 - a) * (l.map (fun b => 1 - b)).prod :=
          mul_le_mul_of_nonneg_left hih (by linarith)

private theorem prod_one_add_le_exp_sum
    (l : List ℝ) (h0 : ∀ a ∈ l, 0 ≤ a) :
    (l.map (fun a => 1 + a)).prod ≤ Real.exp l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha0 : 0 ≤ a := h0 a (by simp)
      have htail0 : ∀ b ∈ l, 0 ≤ b := by
        intro b hb
        exact h0 b (by simp [hb])
      have hih := ih htail0
      have hprod0 : 0 ≤ (l.map (fun b => 1 + b)).prod := by
        apply List.prod_nonneg
        intro b hb
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
        linarith [htail0 c hc]
      simp only [List.sum_cons, List.map_cons, List.prod_cons]
      calc
        (1 + a) * (l.map (fun b => 1 + b)).prod ≤
            Real.exp a * (l.map (fun b => 1 + b)).prod :=
          mul_le_mul_of_nonneg_right (by simpa [add_comm] using Real.add_one_le_exp a)
            hprod0
        _ ≤ Real.exp a * Real.exp l.sum :=
          mul_le_mul_of_nonneg_left hih (Real.exp_pos _).le
        _ = Real.exp (a + l.sum) := (Real.exp_add _ _).symm

/-- One threshold controls the products of all lower and upper perturbation
factors along every adaptive chain, by constants independent of depth. -/
theorem exists_uniform_kernelFactor_product_bounds
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ A : ℕ, 64 ≤ A ∧
      (∀ n, A ≤ n → AdaptiveCutoffData n) ∧
      ∀ {x : ℕ} {xs : List ℕ},
        (∀ n ∈ x :: xs, A ≤ n) →
        List.IsChain (fun child parent => child ≤ adaptiveEndpoint parent)
          (x :: xs) →
        1 / 2 ≤
            (List.map (fun n => 1 - 2 * uniformKernelError C n)
              (x :: xs)).prod ∧
          (List.map (fun n => 1 + 4 * uniformKernelError C n)
              (x :: xs)).prod ≤ 3 := by
  obtain ⟨A, hA64, hdataAll, hbudget⟩ :=
    exists_uniform_kernelError_orbit_budget hC
      (show (0 : ℝ) < 1 / 4 by norm_num)
  refine ⟨A, hA64, hdataAll, ?_⟩
  intro x xs hlarge hchain
  let nodes := x :: xs
  let errors := nodes.map (uniformKernelError C)
  have hsum : errors.sum ≤ 1 / 4 := by
    dsimp [errors, nodes]
    exact hbudget hlarge hchain
  have herr0 : ∀ e ∈ errors, 0 ≤ e := by
    intro e he
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp he
    apply uniformKernelError_nonneg_of_cutoffData hC
    exact hdataAll n (hlarge n hn)
  have hscaled2sum : (errors.map (fun e => 2 * e)).sum = 2 * errors.sum := by
    simpa using List.sum_map_mul_left errors id 2
  have hscaled4sum : (errors.map (fun e => 4 * e)).sum = 4 * errors.sum := by
    simpa using List.sum_map_mul_left errors id 4
  have hscaled2zero : ∀ e ∈ errors.map (fun e => 2 * e), 0 ≤ e := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    nlinarith [herr0 a ha]
  have hscaled2one : ∀ e ∈ errors.map (fun e => 2 * e), e ≤ 1 := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    have haSum := List.single_le_sum herr0 a ha
    linarith
  have hlower0 : 1 / 2 ≤ 1 - (errors.map (fun e => 2 * e)).sum := by
    rw [hscaled2sum]
    linarith
  have hlower1 := one_sub_sum_le_prod_one_sub
    (errors.map (fun e => 2 * e)) hscaled2zero hscaled2one
  have hlower : 1 / 2 ≤
      (nodes.map (fun n => 1 - 2 * uniformKernelError C n)).prod := by
    calc
      1 / 2 ≤ 1 - (errors.map (fun e => 2 * e)).sum := hlower0
      _ ≤ ((errors.map (fun e => 2 * e)).map (fun e => 1 - e)).prod := hlower1
      _ = (nodes.map (fun n => 1 - 2 * uniformKernelError C n)).prod := by
        simp [errors, nodes, List.map_map, Function.comp_def]
  have hscaled4zero : ∀ e ∈ errors.map (fun e => 4 * e), 0 ≤ e := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    nlinarith [herr0 a ha]
  have hupper0 := prod_one_add_le_exp_sum
    (errors.map (fun e => 4 * e)) hscaled4zero
  have hsum4 : (errors.map (fun e => 4 * e)).sum ≤ 1 := by
    rw [hscaled4sum]
    linarith
  have hupper :
      (nodes.map (fun n => 1 + 4 * uniformKernelError C n)).prod ≤ 3 := by
    calc
      (nodes.map (fun n => 1 + 4 * uniformKernelError C n)).prod =
          ((errors.map (fun e => 4 * e)).map (fun e => 1 + e)).prod := by
        simp [errors, nodes, List.map_map, Function.comp_def]
      _ ≤ Real.exp (errors.map (fun e => 4 * e)).sum := hupper0
      _ ≤ Real.exp 1 := Real.exp_monotone hsum4
      _ ≤ 3 := Real.exp_one_lt_three.le
  exact ⟨hlower, hupper⟩

end Erdos321
