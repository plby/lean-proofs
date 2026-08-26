import ErdosProblems.Erdos491.Basic

/-!
# The uniform `2M` reduction

Keeping the additive constant in the geometric-sum estimate sharp improves
the existing completely additive approximation from `4M` to `2M`.
-/

open Filter
open scoped Topology

namespace Erdos491

lemma geometric_power_error
    {f : ℕ → ℝ} {M : ℝ} (hf : CoprimeAdditive f) (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ M)
    (n s : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s) (hcop : s.Coprime (n - 1)) :
    |f (n ^ s) - (s : ℝ) * f n| ≤ ((s : ℝ) + 1) * M := by
  have hf' : Erdos491MateScratch.CoprimeAdditive f :=
    fun _ _ _ _ hab ↦ hf hab
  by_cases hn1 : n = 1
  · subst n
    simp only [one_pow, hf.one_eq_zero, mul_zero, sub_self, abs_zero]
    positivity
  have hn2 : 2 ≤ n := by omega
  let G := Erdos491MateScratch.geom n (s - 1)
  have hmul : (n - 1) * G = n ^ s - 1 :=
    Erdos491MateScratch.geom_pred_mul n s hn hs
  have hGcop : (n - 1).Coprime G :=
    Erdos491MateScratch.geom_coprime_pred n s hn hs hcop
  have hadd : f (n ^ s - 1) = f (n - 1) + f G := by
    rw [← hmul]
    exact hf hGcop
  have hgeom := Erdos491MateScratch.geom_estimate hf' hM
    (fun n _ ↦ hgap n) n (s - 1) hn
  have heq : f (n ^ s) - (s : ℝ) * f n =
      (f (n ^ s) - f (n ^ s - 1)) + (f (n - 1) - f n) +
        (f G - ((s - 1 : ℕ) : ℝ) * f n) := by
    rw [hadd]
    push_cast [Nat.cast_sub hs]
    ring
  rw [heq]
  calc
    |(f (n ^ s) - f (n ^ s - 1)) + (f (n - 1) - f n) +
        (f G - ((s - 1 : ℕ) : ℝ) * f n)|
        ≤ |f (n ^ s) - f (n ^ s - 1)| + |f (n - 1) - f n| +
            |f G - ((s - 1 : ℕ) : ℝ) * f n| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ M + M + ((s - 1 : ℕ) : ℝ) * M := by
      have htop : |f (n ^ s) - f (n ^ s - 1)| ≤ M := by
        simpa only [Nat.sub_add_cancel (Nat.pow_pos hn)] using hgap (n ^ s - 1)
      have hbot : |f (n - 1) - f n| ≤ M := by
        rw [abs_sub_comm]
        simpa only [Nat.sub_add_cancel hn] using hgap (n - 1)
      exact add_le_add (add_le_add htop hbot) hgeom
    _ = ((s : ℝ) + 1) * M := by
      rw [Nat.cast_sub hs]
      push_cast
      ring

lemma dyadic_power_error_even
    {f : ℕ → ℝ} {M : ℝ} (hf : CoprimeAdditive f) (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ M)
    (n k : ℕ) (hn : 1 ≤ n) (heven : Even n) :
    |f (n ^ (2 ^ k)) - ((2 ^ k : ℕ) : ℝ) * f n| ≤
      (((2 ^ k : ℕ) : ℝ) + 1) * M := by
  have hodd : Odd (n - 1) := by
    obtain ⟨r, hr⟩ := heven
    refine ⟨r - 1, ?_⟩
    omega
  exact geometric_power_error hf hM hgap n (2 ^ k) hn
    (Nat.pow_pos (by omega)) ((Nat.coprime_two_left.2 hodd).pow_left k)

lemma dyadic_power_error
    {f : ℕ → ℝ} {M : ℝ} (hf : CoprimeAdditive f) (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ M)
    (n k : ℕ) (hn : 1 ≤ n) :
    |f (n ^ (2 ^ k)) - ((2 ^ k : ℕ) : ℝ) * f n| ≤
      2 * (((2 ^ k : ℕ) : ℝ) + 1) * M := by
  by_cases heven : Even n
  · apply (dyadic_power_error_even hf hM hgap n k hn heven).trans
    nlinarith [show (0 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) by positivity]
  have hcop : (2 : ℕ).Coprime n :=
    Nat.coprime_two_left.2 (Nat.not_even_iff_odd.mp heven)
  have h2n := dyadic_power_error_even hf hM hgap (2 * n) k (by omega) (by simp)
  have h2 := dyadic_power_error_even hf hM hgap 2 k (by omega) (by simp)
  have haddBase : f (2 * n) = f 2 + f n := hf hcop
  have haddPow : f ((2 * n) ^ (2 ^ k)) =
      f (2 ^ (2 ^ k)) + f (n ^ (2 ^ k)) := by
    rw [mul_pow]
    exact hf (hcop.pow _ _)
  have heq : f (n ^ (2 ^ k)) - ((2 ^ k : ℕ) : ℝ) * f n =
      (f ((2 * n) ^ (2 ^ k)) - ((2 ^ k : ℕ) : ℝ) * f (2 * n)) -
        (f (2 ^ (2 ^ k)) - ((2 ^ k : ℕ) : ℝ) * f 2) := by
    rw [haddBase, haddPow]
    ring
  rw [heq]
  calc
    _ ≤ |f ((2 * n) ^ (2 ^ k)) - ((2 ^ k : ℕ) : ℝ) * f (2 * n)| +
        |f (2 ^ (2 ^ k)) - ((2 ^ k : ℕ) : ℝ) * f 2| := abs_sub _ _
    _ ≤ ((((2 ^ k : ℕ) : ℝ) + 1) * M) +
        ((((2 ^ k : ℕ) : ℝ) + 1) * M) := add_le_add h2n h2
    _ = _ := by ring

/-- Complete additivity and any uniform approximation bound improve that
bound to `2M` by amplification along dyadic powers. -/
theorem uniform_approximation_le_two_mul
    {f g : ℕ → ℝ} {M B : ℝ} (hf : CoprimeAdditive f)
    (hg : PosCompletelyAdditive g) (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ M)
    (hbound : ∀ n : ℕ, 0 < n → |f n - g n| ≤ B)
    (n : ℕ) (hn : 0 < n) : |f n - g n| ≤ 2 * M := by
  have hb (k : ℕ) :
      |f n - g n| ≤ 2 * M + (2 * M + B) / (2 : ℝ) ^ k := by
    have hk : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have herr := dyadic_power_error hf hM hgap n k hn
    have happ := hbound (n ^ (2 ^ k)) (pow_pos hn _)
    rw [hg.pow hn] at happ
    push_cast at herr happ
    have htri : (2 : ℝ) ^ k * |f n - g n| ≤
        |f (n ^ (2 ^ k)) - (2 : ℝ) ^ k * f n| +
          |f (n ^ (2 ^ k)) - (2 : ℝ) ^ k * g n| := by
      calc
        _ = |(f (n ^ (2 ^ k)) - (2 : ℝ) ^ k * g n) -
            (f (n ^ (2 ^ k)) - (2 : ℝ) ^ k * f n)| := by
              rw [show (f (n ^ (2 ^ k)) - (2 : ℝ) ^ k * g n) -
                (f (n ^ (2 ^ k)) - (2 : ℝ) ^ k * f n) =
                (2 : ℝ) ^ k * (f n - g n) by ring,
                abs_mul, abs_of_pos hk]
        _ ≤ _ := (abs_sub _ _).trans_eq (add_comm _ _)
    rw [mul_comm ((2 : ℝ) ^ k)] at htri
    have htri' := (le_div_iff₀ hk).2 htri
    have hsum : |f (n ^ (2 ^ k)) - (2 : ℝ) ^ k * f n| +
        |f (n ^ (2 ^ k)) - (2 : ℝ) ^ k * g n| ≤
        2 * ((2 : ℝ) ^ k + 1) * M + B := add_le_add herr happ
    calc
      |f n - g n| ≤ _ := htri'
      _ ≤ (2 * ((2 : ℝ) ^ k + 1) * M + B) / (2 : ℝ) ^ k :=
        div_le_div_of_nonneg_right hsum hk.le
      _ = 2 * M + (2 * M + B) / (2 : ℝ) ^ k := by
        field_simp
        <;> ring
  have ht : Tendsto (fun k : ℕ ↦ 2 * M + (2 * M + B) / (2 : ℝ) ^ k)
      atTop (𝓝 (2 * M)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)))
  exact ge_of_tendsto ht (Filter.Eventually.of_forall hb)

/-- The original, only coprime-additive function admits a completely additive
approximation with a uniform `2M` error on all positive integers. -/
theorem homogenization
    {f : ℕ → ℝ} {M : ℝ} (hf : CoprimeAdditive f) (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, |f (n + 1) - f n| ≤ M) :
    ∃ g : ℕ → ℝ, PosCompletelyAdditive g ∧
      (∀ n : ℕ, 0 < n → |f n - g n| ≤ 2 * M) ∧
      (∀ n : ℕ, 0 < n → |g (n + 1) - g n| ≤ 5 * M) := by
  obtain ⟨g, hg, hbound⟩ := mate_decomposition hf hM hgap
  have hsharp := uniform_approximation_le_two_mul hf hg hM hgap hbound
  refine ⟨g, hg, hsharp, fun n hn ↦ ?_⟩
  have htri : |g (n + 1) - g n| ≤
      |f (n + 1) - g (n + 1)| + |f (n + 1) - f n| + |f n - g n| := by
    calc
      _ = |-(f (n + 1) - g (n + 1)) + (f (n + 1) - f n) +
          (f n - g n)| := by congr 1; ring
      _ ≤ _ := by
        simpa only [abs_neg] using
          (abs_add_le (-(f (n + 1) - g (n + 1)) + (f (n + 1) - f n))
            (f n - g n)).trans
            (add_le_add (abs_add_le _ _) le_rfl)
  linarith [hsharp (n + 1) (by omega), hsharp n hn, hgap n]

end Erdos491
