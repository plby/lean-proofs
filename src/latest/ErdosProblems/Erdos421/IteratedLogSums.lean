import ErdosProblems.Erdos421.IteratedLogDifferences
import ErdosProblems.Erdos421.PhasePartition
import ErdosProblems.Erdos421.VanDerCorput

/-! # Exponential sums of logarithmic differences of every order -/

namespace Erdos421

noncomputable def iteratedLogarithmicPhase (M : ℕ) (hs : List ℝ) (τ : ℝ) (n : ℕ) : ℝ :=
  τ * iteratedDifference hs Real.log (M + n : ℕ)

theorem iteratedLogarithmicPhase_increment (M : ℕ) (hs : List ℝ) (τ : ℝ) (n : ℕ) :
    phaseIncrement (iteratedLogarithmicPhase M hs τ) n =
      τ * iteratedLogIncrement hs (M + n : ℝ) := by
  unfold phaseIncrement iteratedLogarithmicPhase iteratedLogIncrement
  simp only [Nat.cast_add, Nat.cast_one, ← add_assoc]
  ring

theorem iteratedLogarithmicPhase_antitone {M : ℕ} (hM : 0 < M)
    (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) {τ : ℝ} (hτ : 0 ≤ τ) :
    Antitone (phaseIncrement (iteratedLogarithmicPhase M hs τ)) := by
  intro i j hij
  rw [iteratedLogarithmicPhase_increment, iteratedLogarithmicPhase_increment]
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  apply mul_le_mul_of_nonneg_left _ hτ
  exact iteratedLogIncrement_antitone hs hhs (by positivity)
    (by exact_mod_cast Nat.add_le_add_left hij M)

theorem iteratedLogarithmicPhase_nonneg {M : ℕ} (hM : 0 < M)
    (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) :
    0 ≤ phaseIncrement (iteratedLogarithmicPhase M hs τ) n := by
  rw [iteratedLogarithmicPhase_increment]
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  exact mul_nonneg hτ (iteratedLogIncrement_nonneg hs hhs (by positivity))

theorem iteratedLogarithmicPhase_upper {M : ℕ} (hM : 0 < M)
    (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) :
    phaseIncrement (iteratedLogarithmicPhase M hs τ) n ≤
      τ * differenceCoefficient 0 hs / (M : ℝ) ^ (hs.length + 1) := by
  have ha := iteratedLogarithmicPhase_antitone hM hs hhs hτ (Nat.zero_le n)
  rw [iteratedLogarithmicPhase_increment M hs τ 0, Nat.cast_zero, add_zero] at ha
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hu := mul_le_mul_of_nonneg_left (iteratedLogIncrement_bounds hs hhs hMp).2 hτ
  exact ha.trans (by simpa only [mul_div_assoc] using hu)

theorem iteratedLogarithmicPhase_spacing {M N i j : ℕ} (hM : 0 < M)
    (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 ≤ h) {τ : ℝ} (hτ : 0 ≤ τ)
    (hij : i ≤ j) (hj : j ≤ N) :
    (τ * differenceCoefficient 0 (1 :: hs) / (M + N + hs.sum + 1 : ℝ) ^ (hs.length + 2)) *
        ((j : ℝ) - i) ≤ phaseIncrement (iteratedLogarithmicPhase M hs τ) i -
          phaseIncrement (iteratedLogarithmicPhase M hs τ) j := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  have hxy : (M + i : ℝ) ≤ M + j := by exact_mod_cast Nat.add_le_add_left hij M
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast hj
  have hd := iteratedLogIncrement_drop_lower_bounded hs hhs
    (by positivity : (0 : ℝ) < M + i) hxy
    (show (M + j : ℝ) + 1 + hs.sum ≤ M + N + hs.sum + 1 by linarith)
  have hm := mul_le_mul_of_nonneg_left hd hτ
  rw [iteratedLogarithmicPhase_increment, iteratedLogarithmicPhase_increment]
  calc
    _ = τ * (((M + j : ℝ) - (M + i)) * differenceCoefficient 0 (1 :: hs) /
        (M + N + hs.sum + 1 : ℝ) ^ (hs.length + 2)) := by ring
    _ ≤ _ := hm
    _ = _ := by ring

theorem iteratedLogarithmic_sum_spacing_bound {M : ℕ} (hM : 0 < M)
    (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) (N : ℕ) {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) :
    ‖∑ n ∈ Finset.range N, oscillatoryPhase 1 (iteratedLogarithmicPhase M hs τ n)‖ ≤
      ((⌈τ * differenceCoefficient 0 hs / (M : ℝ) ^ (hs.length + 1)⌉₊ : ℕ) + 2 : ℝ) *
        (2 + 12 / δ + 2 * δ * (M + N + hs.sum + 1 : ℝ) ^ (hs.length + 2) /
          (τ * differenceCoefficient 0 (1 :: hs))) := by
  let K := ⌈τ * differenceCoefficient 0 hs / (M : ℝ) ^ (hs.length + 1)⌉₊
  let η := τ * differenceCoefficient 0 (1 :: hs) /
    (M + N + hs.sum + 1 : ℝ) ^ (hs.length + 2)
  have hhs0 : ∀ h ∈ hs, 0 ≤ h := fun h hh ↦ (hhs h hh).le
  have hlist : ∀ h ∈ (1 : ℝ) :: hs, 0 < h := by
    intro h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · norm_num
    · exact hhs h hh
  have hC : 0 < differenceCoefficient 0 (1 :: hs) := differenceCoefficient_pos 0 _ hlist
  have hsum : 0 ≤ hs.sum := List.sum_nonneg hhs0
  have hη : 0 < η := by dsimp only [η]; positivity
  have ha := iteratedLogarithmicPhase_antitone hM hs hhs0 hτ.le
  have hrange : ∀ n < N, 0 ≤ phaseIncrement (iteratedLogarithmicPhase M hs τ) n ∧
      phaseIncrement (iteratedLogarithmicPhase M hs τ) n ≤ 2 * Real.pi * K := by
    intro n _
    refine ⟨iteratedLogarithmicPhase_nonneg hM hs hhs0 hτ.le n, ?_⟩
    have hu := iteratedLogarithmicPhase_upper hM hs hhs0 hτ.le n
    have hk : τ * differenceCoefficient 0 hs / (M : ℝ) ^ (hs.length + 1) ≤ K := Nat.le_ceil _
    have hkn : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hpi := Real.one_le_pi_div_two
    nlinarith
  have hsep : ∀ i < N, ∀ j < N, i ≤ j →
      η * ((j : ℝ) - i) ≤ phaseIncrement (iteratedLogarithmicPhase M hs τ) i -
        phaseIncrement (iteratedLogarithmicPhase M hs τ) j := by
    intro i _ j hj hij
    exact iteratedLogarithmicPhase_spacing hM hs hhs0 hτ.le hij hj.le
  have hb := separated_increment_sum_bound (iteratedLogarithmicPhase M hs τ) N K
    (fun _ _ _ _ hij ↦ ha hij) hδ hη hrange hsep
  have heq : 2 * δ / η = 2 * δ * (M + N + hs.sum + 1 : ℝ) ^ (hs.length + 2) /
      (τ * differenceCoefficient 0 (1 :: hs)) := by
    dsimp only [η]
    rw [div_div_eq_mul_div]
  rwa [heq] at hb

theorem oscillatoryPhase_comm (ω t : ℝ) : oscillatoryPhase ω t = oscillatoryPhase t ω := by
  unfold oscillatoryPhase
  congr 1
  ring

theorem oscillatoryPhase_one_inner (x y : ℝ) :
    inner ℂ (oscillatoryPhase 1 x) (oscillatoryPhase 1 y) = oscillatoryPhase 1 (y - x) := by
  rw [oscillatoryPhase_comm 1 x, oscillatoryPhase_comm 1 y,
    RCLike.inner_apply, oscillatoryPhase_mul_conj, oscillatoryPhase_comm]

theorem iteratedLogarithmic_finiteCorrelation_eq (M N h : ℕ) (hs : List ℝ) (τ : ℝ) :
    finiteCorrelation (fun n ↦ oscillatoryPhase 1 (iteratedLogarithmicPhase M hs τ n)) N h =
      ∑ n ∈ Finset.range (N - h),
        oscillatoryPhase 1 (iteratedLogarithmicPhase M ((h : ℝ) :: hs) τ n) := by
  unfold finiteCorrelation
  apply Finset.sum_congr rfl
  intro n _
  rw [oscillatoryPhase_one_inner]
  congr 1
  simp only [iteratedLogarithmicPhase, iteratedDifference, Nat.cast_add, ← add_assoc]
  ring

end Erdos421
