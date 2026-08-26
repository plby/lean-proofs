/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- No license was supplied with the original gist.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 765.
Informal authors: István Reiman, Paul Erdős, Alfréd Rényi, W. G. Brown;
following the exposition of Martin Aigner and Günter M. Ziegler.
Formal authors: Aristotle, Jeremy Tan Jie Rui (Parcly-Taxel).
Source: https://www.erdosproblems.com/765#post-6480
https://gist.githubusercontent.com/Parcly-Taxel/13d3bd0f1390b0832a42994a09cf91c5/raw/e267a3a494e64019a1a442b3b05438745923883b/Erdos765.lean
Original Lean/Mathlib version: 4.28.0 (the linked editor project).
The original prime_between axiom is discharged using this repository's PNT+ library.
-/
import ErdosProblems.Erdos765.Bounds
import PrimeNumberTheoremAnd.Consequences

open Finset Fintype SimpleGraph Filter Asymptotics Real

set_option linter.mathlibStandardSet false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos765

lemma prime_between' {ε : ℝ} (εpos : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ (1 - ε) * x < p ∧ p < x := by
  obtain lε | lε := le_or_gt 1 ε
  · refine (eventually_gt_atTop 2).mono fun x hx ↦ ⟨2, Nat.prime_two, ⟨?_, mod_cast hx⟩⟩
    apply (show (0 : ℝ) < (2 : ℕ) by simp).trans_le'
    apply mul_nonpos_of_nonpos_of_nonneg <;> linarith
  replace lε : 0 < 1 - ε := by linarith
  have tt : Tendsto ((1 - ε) * ·) atTop atTop := (tendsto_const_mul_atTop_of_pos lε).mpr tendsto_id
  convert tt.eventually (prime_between (div_pos εpos lε)) with x
  field

lemma exists_prime_near_sqrt' {ε : ℝ} (εpos : 0 < ε) :
    ∀ᶠ n in atTop, ∃ q : ℕ,
      q.Prime ∧ q ^ 2 + q + 1 ≤ n ∧ (1 - ε) * ((√(4 * n - 3) - 1) / 2) ≤ q := by
  obtain lε | lε := le_or_gt 1 ε
  · refine (eventually_gt_atTop 7).mono fun x hx ↦ ⟨2, Nat.prime_two, ⟨by lia, ?_⟩⟩
    apply (show (0 : ℝ) ≤ (2 : ℕ) by simp).trans'
    apply mul_nonpos_of_nonpos_of_nonneg (by linarith) (div_nonneg ?_ zero_le_two)
    rw [sub_nonneg, one_le_sqrt, le_sub_iff_add_le]
    norm_cast
    lia
  have tt : Tendsto (fun n : ℕ ↦ (√(4 * n - 3) - 1) / 2) atTop atTop := by
    conv =>
      enter [1, n]
      rw [div_eq_inv_mul]
    rw [tendsto_const_mul_atTop_of_pos (by norm_num)]
    refine tendsto_atTop_add_const_right _ _ (tendsto_sqrt_atTop.comp ?_)
    apply tendsto_atTop_add_const_right
    rw [tendsto_const_mul_atTop_of_pos (by norm_num)]
    exact tendsto_natCast_atTop_atTop
  filter_upwards [tt.eventually (prime_between' εpos)] with n ⟨q, pq, lbq, ubq⟩
  refine ⟨q, pq, ?_, lbq.le⟩
  rw [lt_div_iff₀' zero_lt_two, lt_sub_iff_add_lt, lt_sqrt (by positivity),
    lt_sub_iff_add_lt, show (2 * q + 1 : ℝ) ^ 2 + 3 = 4 * (q ^ 2 + q + 1) by ring,
    mul_lt_mul_iff_right₀ zero_lt_four] at ubq
  exact_mod_cast ubq.le

open Topology in
lemma sqrt_approx_eventually {ε : ℝ} (εpos : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (1 - ε) * √n ≤ (√(4 * n - 3) - 1) / 2 := by
  obtain hε | hε := lt_or_ge ε 2
  · have tt : Tendsto (fun n : ℕ ↦ (4 * (1 - ε) / √n + 4 / n) / (4 * ε * (2 - ε))) atTop (𝓝 0) := by
      have h₁ := tendsto_inv_atTop_nhds_zero_nat.sqrt.const_mul (4 * (1 - ε))
      have h₂ := tendsto_inv_atTop_nhds_zero_nat.const_mul (4 : ℝ)
      simpa [div_eq_mul_inv] using (h₁.add h₂).div_const (4 * ε * (2 - ε))
    replace tt :
        Tendsto (fun n : ℕ ↦ (4 * (1 - ε) * √n + 4) / (4 * ε * (2 - ε) * n)) atTop (𝓝 0) := by
      apply tt.congr'
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hspos : 0 < √(n : ℝ) := sqrt_pos.mpr hnpos
      field_simp
      nlinarith [sq_sqrt hnpos.le]
    replace tt : ∀ᶠ n : ℕ in atTop, 4 * (1 - ε) * √n + 4 ≤ 4 * ε * (2 - ε) * n := by
      filter_upwards [tt.eventually (gt_mem_nhds zero_lt_one), eventually_gt_atTop 0] with n hn hn'
      rw [div_lt_iff₀ (mul_pos (mul_pos (by linarith) (by linarith)) (by simp [hn']))] at hn
      linarith
    replace tt : ∀ᶠ n : ℕ in atTop, (2 * (1 - ε) * √n + 1) ^ 2 ≤ 4 * n - 3 := by grind
    filter_upwards [tt, eventually_ge_atTop 1] with n hn hn'
    replace hn' : (0 : ℝ) ≤ 4 * n - 3 := by norm_cast; lia
    nlinarith [sqrt_nonneg (4 * n - 3), mul_self_sqrt hn']
  · filter_upwards [eventually_gt_atTop 0] with n hn
    apply (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sqrt_nonneg _)).trans
    refine div_nonneg ?_ zero_le_two
    rw [sub_nonneg, one_le_sqrt, le_sub_iff_add_le]
    norm_cast
    lia

lemma exists_prime_near_sqrt {ε : ℝ} (εpos : 0 < ε) :
    ∀ᶠ n in atTop, ∃ q : ℕ, q.Prime ∧ q ^ 2 + q + 1 ≤ n ∧ (1 - ε) * √n ≤ q := by
  obtain hε | hε := le_or_gt 2 ε
  · filter_upwards [exists_prime_near_sqrt' εpos] with n ⟨q, hprime, hle, _⟩
    exact ⟨q, hprime, hle,
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sqrt_nonneg _)).trans q.cast_nonneg⟩
  · have hε2 : 0 < ε / 2 := by linarith
    have h1mε2 : 0 ≤ 1 - ε / 2 := by linarith
    filter_upwards [exists_prime_near_sqrt' hε2, sqrt_approx_eventually hε2]
      with n ⟨q, hprime, hle, hq_bound⟩ hsqrt
    refine ⟨q, hprime, hle, ?_⟩
    calc
      _ ≤ (1 - ε / 2) * ((1 - ε / 2) * √n) := by nlinarith [sq_nonneg (ε / 2), sqrt_nonneg n]
      _ ≤ (1 - ε / 2) * ((√(4 * n - 3) - 1) / 2) := mul_le_mul_of_nonneg_left hsqrt h1mε2
      _ ≤ _ := hq_bound

/-- If `H` has no isolated vertices, then `H.Free` is preserved under `SimpleGraph.map`. -/
lemma free_map {V W X : Type*} {G : SimpleGraph V} {H : SimpleGraph X}
    (hfree : H.Free G) (f : V ↪ W) (hH : ∀ x, ∃ y, H.Adj x y) : H.Free (G.map f) := by
  contrapose hfree
  obtain ⟨g, hg⟩ := hfree
  have hg2 {x y} (hxy : H.Adj x y) : (G.map f).Adj (g x) (g y) := g.map_rel' hxy
  have h_preimage (x) : g x ∈ Set.range f := by
    obtain ⟨y, hy⟩ := hH x
    obtain ⟨u, v, huv⟩ := hg2 hy
    grind
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ∀ x, f (ψ x) = g x :=
    ⟨fun x ↦ (h_preimage x).choose, fun x ↦ (h_preimage x).choose_spec⟩
  refine ⟨⟨ψ, ?_⟩, ?_⟩
  · grind [map_adj]
  · rw [RelHom.coeFn_mk]
    exact fun x y hxy ↦ hg (by rw [← hψ x, ← hψ y, hxy])

/-- Monotonicity of `extremalNumber` for graphs without isolated vertices. -/
lemma extremalNumber_mono_left_of_no_iso {W : Type*} {H : SimpleGraph W}
    {m n : ℕ} (hmn : m ≤ n) (hH : ∀ w, ∃ w', H.Adj w w') :
    extremalNumber m H ≤ extremalNumber n H := by
  rw [← Fintype.card_fin m, ← Fintype.card_fin n, extremalNumber_le_iff]
  intro G _ hG
  set G' : SimpleGraph (Fin n) := G.map (Fin.castLEEmb hmn)
  have hG'_free : H.Free G' := free_map hG (Fin.castLEEmb hmn) hH
  have hG'_edgeFinset : #G'.edgeFinset = #G.edgeFinset := by
    convert card_edgeFinset_map (Fin.castLEEmb hmn) G
  exact hG'_edgeFinset ▸ card_edgeFinset_le_extremalNumber hG'_free

lemma C4_no_isolated_vertices : ∀ v, ∃ w, C4.Adj v w := by simp [C4]

lemma extremalNumber_C4_mono {m n : ℕ} (hmn : m ≤ n) :
    extremalNumber m C4 ≤ extremalNumber n C4 :=
  extremalNumber_mono_left_of_no_iso hmn C4_no_isolated_vertices

lemma extremalNumber_C4_ge_of_isPrimePow_le {q n : ℕ} (hq : IsPrimePow q)
    (hle : q ^ 2 + q + 1 ≤ n) : q * (q + 1) ^ 2 / 2 ≤ extremalNumber n C4 :=
  (extremalNumber_C4_ge_of_isPrimePow hq).trans (extremalNumber_C4_mono hle)

lemma pow_three_div_two_eq {n : ℕ} : n ^ (3 / 2 : ℝ) = n * √n := by
  rw [sqrt_eq_rpow, ← rpow_one_add' (by simp) (by positivity)]
  norm_num

lemma upper_bound_le_rpow_add {n : ℕ} :
    n / 4 * (√(4 * n - 3) + 1) ≤ n ^ (3 / 2 : ℝ) / 2 + n / 4 := by
  suffices h_sqrt : √(4 * n - 3) ≤ 2 * √n by
    rw [pow_three_div_two_eq]
    nlinarith [sqrt_nonneg n, sq_sqrt n.cast_nonneg]
  exact sqrt_le_iff.mpr ⟨by positivity, by nlinarith [mul_self_sqrt n.cast_nonneg]⟩

lemma eventually_rpow_pos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < n ^ (3 / 2 : ℝ) / 2 :=
  eventually_atTop.mpr ⟨1, fun n hn ↦ by positivity⟩

lemma lower_bound_from_prime {n q : ℕ} {ε : ℝ} (hε1 : ε < 1) (hq : (1 - ε) * √n ≤ q) :
    (1 - ε) ^ 3 * (n ^ (3 / 2 : ℝ) / 2) ≤ q * (q + 1) ^ 2 / 2 := by
  have h_subst : (1 - ε) ^ 3 * (n ^ (3 / 2 : ℝ) / 2) ≤
      ((1 - ε) * √n) * ((1 - ε) * √n + 1) ^ 2 / 2 := by
    nth_rw 1 [pow_three_div_two_eq, ← mul_self_sqrt n.cast_nonneg,
      show (1 - ε) ^ 3 * (√n * √n * √n / 2) = (1 - ε) * √n * ((1 - ε) * √n + 0) ^ 2 / 2 by ring]
    replace hε1 : 0 < 1 - ε := by linarith
    gcongr
    positivity
  apply h_subst.trans
  gcongr

lemma nat_div_two_cast (q : ℕ) : (q * (q + 1) ^ 2 / 2 : ℝ) = (q * (q + 1) ^ 2 / 2 : ℕ) := by
  have h : 2 ∣ q * (q + 1) ^ 2 := by
    obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := q.even_or_odd <;> lia
  norm_cast

lemma eventually_n_le_c_rpow {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, n / 4 ≤ c * (n ^ (3 / 2 : ℝ) / 2) := by
  have h_bound : ∀ᶠ n : ℕ in atTop, √n ≥ 1 / (2 * c) :=
    eventually_atTop.mpr ⟨⌈(1 / (2 * c)) ^ 2⌉₊, fun n hn ↦ le_sqrt_of_sq_le (by simpa using hn)⟩
  filter_upwards [h_bound] with n hn
  rw [pow_three_div_two_eq]
  nlinarith [sqrt_nonneg n, sq_sqrt n.cast_nonneg,
    mul_div_cancel₀ (1 : ℝ) <| show (2 * c) ≠ 0 by positivity, show 0 ≤ n * c by positivity]

end Erdos765
