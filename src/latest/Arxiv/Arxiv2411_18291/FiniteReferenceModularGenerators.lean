import Arxiv.Arxiv2411_18291.FiniteReferenceCliqueCounts
import Arxiv.Arxiv2411_18291.FiniteModularQuarterGenerators

/-! # Modular generators with the source's reference-density bounds -/

noncomputable section

namespace Arxiv2411_18291

theorem relative_count_of_quarter_error {x A B ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hB : 0 < B) (hcount : |x - A| < (ε / 4) * A)
    (href : |A - B| ≤ (ε / 2) * B) : |x - B| < ε * B := by
  have hεB := mul_le_mul_of_nonneg_right hε1 hB.le
  have hA : A ≤ (3 / 2 : ℝ) * B := by
    have hh := (abs_le.mp href).2
    nlinarith only [hh, hεB]
  have hprod := mul_le_mul_of_nonneg_left hA (div_nonneg hε.le (by norm_num : (0 : ℝ) ≤ 4))
  have htri := abs_sub_le x A B
  nlinarith only [htri, hcount, href, hprod, mul_pos hε hB]

theorem clique_reference_main_pos_paper_threshold {q r n m s : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n) (hm : m ≤ q) :
    0 < ((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ s * (n.choose m : ℝ) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hbin : (0 : ℝ) < n.choose m :=
    (by positivity : (0 : ℝ) < (n : ℝ) ^ m / (2 * m.factorial)).trans_le
      (paper_threshold_choose_ge_half_power (by omega) hqr hn hm)
  exact mul_pos (pow_pos (Real.rpow_pos_of_pos hn0 _) _) hbin

theorem cliqueFamily_reference_upper_paper_threshold {q r n h : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ h) (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1))) :
    ((cliqueFamily K q).card : ℝ) ≤
      2 * (((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ q.choose (r + 1) * (n.choose q : ℝ)) := by
  let ε := (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10))
  let M := cliqueMainTerm n (density K) q (r + 1) 0
  let B := ((n : ℝ) ^ (-paperAlpha q (r + 1))) ^ q.choose (r + 1) * (n.choose q : ℝ)
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hε1 : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1
    (by linarith only [paperAlpha_pos hqr])
  have hB : 0 < B := clique_reference_main_pos_paper_threshold hqr hn le_rfl
  have hM0 : 0 ≤ M := cliqueMainTerm_nonneg (Nat.cast_nonneg n) (density_nonneg K) _ _ _
  have hnorm : |M - B| ≤ (ε / 2) * B := by
    simpa only [Nat.choose_eq_zero_of_lt (Nat.succ_pos r), Nat.sub_zero] using
      cliqueMainTerm_reference_error_paper_threshold (a := 0) hqr hn (density_nonneg K) hd
  have hεB := mul_le_mul_of_nonneg_right hε1 hB.le
  have hM : M ≤ (3 / 2 : ℝ) * B := by
    have hh := (abs_le.mp hnorm).2
    nlinarith only [hh, hεB]
  have hc0 := Real.rpow_nonneg (Nat.cast_nonneg n) (-(1 / 10 : ℝ))
  have hsize : (q : ℝ) ≤ (2 * (n : ℝ) ^ (-(1 / 10 : ℝ)) -
      (n : ℝ) ^ (-(1 / 10 : ℝ))) * (Fintype.card (Fin n) * density K ^ q.choose (r + 1)) := by
    rw [Fintype.card_fin, show 2 * (n : ℝ) ^ (-(1 / 10 : ℝ)) -
      (n : ℝ) ^ (-(1 / 10 : ℝ)) = (n : ℝ) ^ (-(1 / 10 : ℝ)) by ring]
    exact modular_host_clique_size_paper_threshold hqr hn K hd
  have hcount := hT.cliqueFamily_relative hqh (by linarith only [hc0])
    (by positivity) (paper_host_error_small hqr hn) hsize
  simp only [Fintype.card_fin] at hcount
  have herror : (2 * (n : ℝ) ^ (-(1 / 10 : ℝ))) * q * 2 ^ q ≤ 1 / 8 := by
    have hh := generator_count_quarter_error_paper_threshold hqr hn
    change _ ≤ (ε / 4) / 2 at hh
    linarith only [hh, hε1]
  have hmerr := mul_le_mul_of_nonneg_right herror hM0
  have hu := (abs_le.mp hcount).2
  change ((cliqueFamily K q).card : ℝ) - M ≤ _ at hu
  change ((cliqueFamily K q).card : ℝ) ≤ 2 * B
  nlinarith only [hu, hmerr, hM, hB]

theorem exists_reference_modular_generators_of_margin {q r n h N : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hN : 0 < N) (hNb : (256 * q.choose (r + 1) * q.choose r * N : ℝ) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 10))
    (hqh : q.choose (r + 1) ≤ h) (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1))) :
    ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
      IsCliqueFamilyBounded r C.generators
        (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
      C.generators.card ≤ N * K.card ∧
      (C.saturated.card : ℝ) <
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10) -
          (q.choose (r + 1) : ℝ) * paperAlpha q (r + 1)) * (n.choose q : ℝ) ∧
      ((K \ C.good).card : ℝ) <
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card ∧
      ∀ e ∈ C.good,
        |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
          (n : ℝ) ^ (paperAlpha q (r + 1) -
            (q.choose (r + 1) : ℝ) * paperAlpha q (r + 1)) *
              (n.choose (q - (r + 1)) : ℝ)| <
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
            ((n : ℝ) ^ (paperAlpha q (r + 1) -
              (q.choose (r + 1) : ℝ) * paperAlpha q (r + 1)) *
                (n.choose (q - (r + 1)) : ℝ)) := by
  let α := paperAlpha q (r + 1)
  let p := (n : ℝ) ^ (-α)
  let ε := (n : ℝ) ^ (-(α / 10))
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hp : 0 < p := Real.rpow_pos_of_pos hn0 _
  have hε : 0 < ε := Real.rpow_pos_of_pos hn0 _
  have hε1 : ε ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1
    (by dsimp only [α]; linarith only [paperAlpha_pos hqr])
  have hKpos : (0 : ℝ) < K.card := by
    have hdpos : 0 < density K := (by positivity : (0 : ℝ) < (1 / 2 : ℝ) * p).trans_le
      (paper_host_density_bounds hqr hn K hd).1
    have hcard : K.card ≠ 0 := by
      intro hz
      simp only [density, hz, Nat.cast_zero, zero_div, lt_self_iff_false] at hdpos
    exact_mod_cast Nat.pos_of_ne_zero hcard
  obtain ⟨C, hbounded, hcard, hsat, hbad, hcount⟩ :=
    exists_good_modular_generators_quarter_of_margin hqr hn hN hNb hqh K hT hd
  have htotal := cliqueFamily_reference_upper_paper_threshold hqr hn hqh K hT hd
  have hB : 0 < p ^ q.choose (r + 1) * (n.choose q : ℝ) :=
    clique_reference_main_pos_paper_threshold hqr hn le_rfl
  have hSref : ε * (p ^ q.choose (r + 1) * (n.choose q : ℝ)) =
      (n : ℝ) ^ (-(α / 10) - (q.choose (r + 1) : ℝ) * α) * (n.choose q : ℝ) := by
    dsimp only [ε, p]
    rw [← Real.rpow_mul_natCast hn0.le, ← mul_assoc, ← Real.rpow_add hn0]
    congr 2
    ring
  have hk : 1 ≤ q.choose (r + 1) := Nat.choose_pos hqr.le
  have hEref : p ^ (q.choose (r + 1) - 1) =
      (n : ℝ) ^ (α - (q.choose (r + 1) : ℝ) * α) := by
    dsimp only [p]
    rw [← Real.rpow_mul_natCast hn0.le]
    congr 1
    rw [Nat.cast_sub hk, Nat.cast_one]
    ring
  refine ⟨C, hbounded, hcard, ?_, ?_, ?_⟩
  · rw [← hSref]
    have hh := mul_le_mul_of_nonneg_left htotal (div_nonneg hε.le (by norm_num : (0 : ℝ) ≤ 4))
    change (C.saturated.card : ℝ) ≤ (ε / 4) * (cliqueFamily K q).card at hsat
    nlinarith only [hsat, hh, mul_pos hε hB]
  · change ((K \ C.good).card : ℝ) ≤ (ε / 4) * K.card at hbad
    change ((K \ C.good).card : ℝ) < ε * K.card
    nlinarith only [hbad, mul_pos hε hKpos]
  · intro e he
    have hnorm := cliqueMainTerm_reference_error_paper_threshold (a := r + 1)
      hqr hn (density_nonneg K) hd
    simp only [Nat.choose_self] at hnorm
    have hBpos : 0 < p ^ (q.choose (r + 1) - 1) * (n.choose (q - (r + 1)) : ℝ) :=
      clique_reference_main_pos_paper_threshold hqr hn (Nat.sub_le q (r + 1))
    have hh := relative_count_of_quarter_error hε hε1 hBpos (hcount e he) hnorm
    rw [hEref] at hh
    exact hh

theorem exists_reference_modular_generators_paper_threshold {q r n h N : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hN : 0 < N) (hNb : N ≤ (r + 1).factorial * q.choose (r + 1))
    (hqh : q.choose (r + 1) ≤ h) (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1))) :
    ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
      IsCliqueFamilyBounded r C.generators
        (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
      C.generators.card ≤ N * K.card ∧
      (C.saturated.card : ℝ) <
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10) -
          (q.choose (r + 1) : ℝ) * paperAlpha q (r + 1)) * (n.choose q : ℝ) ∧
      ((K \ C.good).card : ℝ) <
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card ∧
      ∀ e ∈ C.good,
        |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
          (n : ℝ) ^ (paperAlpha q (r + 1) -
            (q.choose (r + 1) : ℝ) * paperAlpha q (r + 1)) *
              (n.choose (q - (r + 1)) : ℝ)| <
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
            ((n : ℝ) ^ (paperAlpha q (r + 1) -
              (q.choose (r + 1) : ℝ) * paperAlpha q (r + 1)) *
                (n.choose (q - (r + 1)) : ℝ)) := by
  exact exists_reference_modular_generators_of_margin hqr hn hN
    (generator_modulus_margin_paper_threshold hqr hn hNb) hqh K hT hd

end Arxiv2411_18291
