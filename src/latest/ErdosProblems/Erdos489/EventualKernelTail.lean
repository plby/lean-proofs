import ErdosProblems.Erdos489.RankKernel

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open Filter
open scoped Topology BigOperators

/-- Eventual quadratic growth, rather than a global quadratic lower bound, is
enough for summability of the rank-pair kernel. -/
theorem summable_rankPairKernel_of_eventually_sq_le
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (hev : ∀ᶠ n : ℕ in atTop, (n + 1) ^ 2 ≤ a n) :
    Summable (rankPairKernel a) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  let K := 1 + ∑ n ∈ Finset.range N, (n + 1) ^ 2
  have hK : 0 < K := by dsimp [K]; omega
  have hglobal : ∀ n, (n + 1) ^ 2 ≤ K * a n := by
    intro n
    by_cases hn : n < N
    · have hterm : (n + 1) ^ 2 ≤ ∑ m ∈ Finset.range N, (m + 1) ^ 2 :=
        Finset.single_le_sum
          (s := Finset.range N) (f := fun m => (m + 1) ^ 2)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hn)
      have hleK : (n + 1) ^ 2 ≤ K := by dsimp [K]; omega
      have ha1 : 1 ≤ a n := ha n
      exact hleK.trans (by simpa using Nat.mul_le_mul_left K ha1)
    · have hnN : N ≤ n := by omega
      have hsq := hN n hnN
      have hmul : a n ≤ K * a n := by
        have := Nat.mul_le_mul_right (a n) (show 1 ≤ K by omega)
        simpa [Nat.mul_comm] using this
      exact hsq.trans hmul
  let A : ℕ → ℕ := fun n => K * a n
  have hsA : Summable (rankPairKernel A) :=
    summable_rankPairKernel_of_sq_le A hglobal
  have heq : ∀ z : ℕ × ℕ,
      rankPairKernel a z = (K : ℝ) ^ 2 * rankPairKernel A z := by
    intro z
    have ha1 : (0 : ℝ) < a z.1 := by exact_mod_cast ha z.1
    have ha2 : (0 : ℝ) < a z.2 := by exact_mod_cast ha z.2
    have hKR : (0 : ℝ) < K := by exact_mod_cast hK
    dsimp [rankPairKernel, A]
    norm_num only [Nat.cast_mul]
    field_simp
  apply (hsA.mul_left ((K : ℝ) ^ 2)).congr
  intro z
  exact (heq z).symm

/-- Uniform finite-set tails for the kernel under eventual quadratic growth. -/
theorem rankPairKernel_uniform_finset_tail_of_eventually
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (hev : ∀ᶠ n : ℕ in atTop, (n + 1) ^ 2 ≤ a n) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ t : Finset (ℕ × ℕ),
      (∀ z ∈ t, N ≤ z.1 ∧ N ≤ z.2) →
      ∑ z ∈ t, rankPairKernel a z < ε := by
  intro ε hε
  have hs := summable_rankPairKernel_of_eventually_sq_le a ha hev
  have hvanish := (summable_iff_vanishing.mp hs)
    (Metric.ball (0 : ℝ) ε) (Metric.ball_mem_nhds 0 hε)
  obtain ⟨core, hcore⟩ := hvanish
  let N : ℕ := ∑ z ∈ core, (z.1 + z.2 + 1)
  have hcoord : ∀ z ∈ core, z.1 < N ∧ z.2 < N := by
    intro z hz
    have hterm : z.1 + z.2 + 1 ≤ N := by
      dsimp [N]
      exact Finset.single_le_sum
        (s := core) (f := fun w : ℕ × ℕ => w.1 + w.2 + 1)
        (fun _ _ => Nat.zero_le _) hz
    omega
  refine ⟨N, ?_⟩
  intro t ht
  have hdisj : Disjoint t core := by
    rw [Finset.disjoint_left]
    intro z hzt hzc
    have := ht z hzt
    have := hcoord z hzc
    omega
  have hball := hcore t hdisj
  rw [Metric.mem_ball, Real.dist_eq] at hball
  have hnonneg : 0 ≤ ∑ z ∈ t, rankPairKernel a z := by
    apply Finset.sum_nonneg
    intro z hz
    dsimp [rankPairKernel]
    positivity
  have habs : |∑ z ∈ t, rankPairKernel a z| < ε := by simpa using hball
  exact (abs_lt.mp habs).2

end Erdos489
