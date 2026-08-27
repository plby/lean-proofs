import Arxiv.Arxiv2411_18291.ExplicitReserveTypicality

/-! # The reserve lemma at the paper's explicit threshold -/

noncomputable section

namespace Arxiv2411_18291

/-- Lemma 2.1 at the printed threshold. The degree bound is strengthened from
`2*n^(-ρ)` to strict `n^(-ρ)`, and the extension count holds for every edge. -/
theorem exists_reserve_paper_threshold (q r n : ℕ) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    let K := q.choose (r + 1)
    let ρ := paperRho q (r + 1)
    ∃ R : Hypergraph (Fin n) (r + 1),
      IsGraphBounded R ((n : ℝ) ^ (-ρ)) ∧
      ∀ e : Block (Fin n) (r + 1),
        (n : ℝ) ^ (-((K : ℝ) * ρ)) * (n : ℝ) ^ (q - (r + 1)) ≤
          (puncturedCliques R e q).card := by
  dsimp only
  let K := q.choose (r + 1)
  let ρ := paperRho q (r + 1)
  let z := (n : ℝ) ^ (-ρ)
  let c := (n : ℝ) ^ (-(1 / 8 : ℝ))
  have hnNat : 0 < n := Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hz : 0 < z := Real.rpow_pos_of_pos hnpos _
  have hc : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hnormal : (4 + 2 * K * 2 ^ K : ℝ) * c ≤ 1 / 4 :=
    paper_reserve_normalization hqr hn
  have hcsmall : c ≤ 1 / 2 := by
    have hh : (0 : ℝ) ≤ c * K * 2 ^ K := by positivity
    nlinarith only [hnormal, hh]
  have hzsmall : z ≤ 1 / 4 := by
    have hlarge := paper_reserve_tail_constant_lt_rpow hqr hn
    have hfour : (4 : ℝ) ≤ (n : ℝ) ^ ρ := by
      change (48 * (r * K) + 24 * K + 36 : ℝ) < (n : ℝ) ^ ρ at hlarge
      nlinarith only [hlarge, (Nat.cast_nonneg K : (0 : ℝ) ≤ K),
        (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
    have hh := mul_le_mul_of_nonneg_right hfour hz.le
    change 4 * z ≤ (n : ℝ) ^ ρ * (n : ℝ) ^ (-ρ) at hh
    rw [← Real.rpow_add hnpos, add_neg_cancel, Real.rpow_zero] at hh
    linarith only [hh]
  let p : unitInterval := ⟨z / 4, by constructor <;> linarith⟩
  have hp : (n : ℝ) ^ (-(2 * ρ)) ≤ (p : ℝ) := by
    change (n : ℝ) ^ (-(2 * ρ)) ≤ z / 4
    calc
      _ = z ^ 2 := by
        rw [show -(2 * ρ) = (-ρ) * 2 by ring]
        simpa only [Nat.cast_ofNat, z] using Real.rpow_mul_natCast hnpos.le (-ρ) 2
      _ ≤ _ := by nlinarith only [hzsmall, hz]
  obtain ⟨R, hd, hT⟩ := exists_typicalGraph_paper_reserve_threshold hqr hn p hp
  have hderr : |density R - z / 4| ≤ z / 8 := by
    change |density R - z / 4| ≤ c * (z / 4) at hd
    have hh := mul_le_mul_of_nonneg_right hcsmall (by positivity : 0 ≤ z / 4)
    nlinarith only [hd, hh]
  have hdlo : z / 8 ≤ density R := by have hh := (abs_le.mp hderr).1; linarith
  have hdhi : density R ≤ z / 2 := by have hh := (abs_le.mp hderr).2; linarith
  obtain ⟨hsize, hsmall⟩ := paper_reserve_size_numerics hqr hn
  have hres := reserve_of_typical hT (q := q) le_rfl hnormal hqr.le
    (by simpa only [Fintype.card_fin] using hnNat) hz hdlo hdhi
    (by simpa only [Fintype.card_fin] using hsize) hsmall
  have heq : z ^ K = (n : ℝ) ^ (-((K : ℝ) * ρ)) := by
    dsimp only [z]
    rw [← Real.rpow_mul_natCast hnpos.le]
    congr 1
    ring
  refine ⟨R, hres.1, fun e => ?_⟩
  simpa only [Fintype.card_fin, heq, K, ρ] using hres.2 e

end Arxiv2411_18291
