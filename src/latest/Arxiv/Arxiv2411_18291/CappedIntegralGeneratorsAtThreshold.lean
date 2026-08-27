import Arxiv.Arxiv2411_18291.CappedIntegralGeneratorsFromSystem
import Arxiv.Arxiv2411_18291.CappedRainbowGeneratingSystem
import Arxiv.Arxiv2411_18291.LogarithmicPaletteGrowth
import Arxiv.Arxiv2411_18291.PaperIntegralGeneratorsAtThreshold

/-! # Constructed integral generators with a small edge cap at the printed threshold

For q at least three, the logarithmic palette, focusing, and local decoders
all fit at n0. The exchange, host, and generator family are constructed;
no modular or integral generation hypothesis is supplied by the caller.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem integral_generator_edge_cap_paper_threshold {q r n p : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hp : (p : ℝ) * 2 ^ q + 1 ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 20)) :
    (p : ℝ) * (n : ℝ) ^ (paperAlpha q (r + 1) / 20) + 1 + q.choose (r + 1) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 10) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hb : (1 : ℝ) ≤ 2 ^ q := one_le_pow₀ (by norm_num)
  have hpx : (p : ℝ) + 1 ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 20) := by
    nlinarith only [hp, mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg p)]
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hkb : (q.choose (r + 1) : ℝ) ≤ (4 * q : ℝ) ^ q := by
    exact_mod_cast (Nat.choose_le_two_pow q (r + 1)).trans
      (Nat.pow_le_pow_left (by omega : 2 ≤ 4 * q) q)
  have hone : (1 : ℝ) ≤ (4 * q : ℝ) ^ q := one_le_pow₀ (by linarith only [hq])
  have hk : (1 : ℝ) + q.choose (r + 1) ≤
      (n : ℝ) ^ (paperAlpha q (r + 1) / 20) := by
    calc
      _ ≤ 2 * (4 * q : ℝ) ^ q := by linarith only [hkb, hone]
      _ ≤ (4 * q : ℝ) * (4 * q : ℝ) ^ q :=
        mul_le_mul_of_nonneg_right (by linarith only [hq]) (by positivity)
      _ = (4 * q : ℝ) ^ (q + 1) := (pow_succ' _ _).symm
      _ ≤ _ := by
        have hh := paper_threshold_alpha_rpow_lower hqr hn (s := q + 1)
          (t := (1 / 20 : ℝ)) (by norm_num) (by push_cast; linarith only [hq])
        convert hh using 1
        congr 1
        ring
  calc
    _ ≤ ((p : ℝ) + 1) * (n : ℝ) ^ (paperAlpha q (r + 1) / 20) := by
      linarith only [hk]
    _ ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 20) *
        (n : ℝ) ^ (paperAlpha q (r + 1) / 20) :=
      mul_le_mul_of_nonneg_right hpx (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

theorem exists_capped_integral_generators_with_exchange_paper_threshold
    {U W : Type*} [Fintype U] [Fintype W] [DecidableEq W] {q r : ℕ}
    (F₀ : Block U (r + 1)) (hU : Fintype.card U = q)
    {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {P : Block W q} {e : Block W (r + 1)} (hpair : IsEliminationPair S P e)
    (hqr : r + 1 < q) (hq : 3 ≤ q)
    (hS : S.graph.card ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) {n : ℕ}
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    ∀ B : Hypergraph (Fin n) (r + 1),
      IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1))) →
      ∃ D : Finset (Block (Fin n) q),
        IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) / 2) ∧
        (∀ e : Block (Fin n) (r + 1),
          ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
            (n : ℝ) ^ (paperAlpha q (r + 1) / 10)) ∧
        ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
          IntegrallyDecomposable q J → GeneratedBy D J := by
  let N := (r + 1).factorial * q.choose (r + 1)
  let t := 2 * q.choose (r + 1)
  let p := relaxedGeneratorPaletteSize n S P
  let C : ℝ := p * 2 ^ q
  have hN : 0 < N := Nat.mul_pos (Nat.factorial_pos _) (Nat.choose_pos hqr.le)
  have hqh : q.choose (r + 1) ≤ S.graph.card :=
    (Nat.le_self_pow two_ne_zero _).trans
      (by simpa only [pow_two] using hA.choose_sq_le (Nat.succ_pos r))
  have hgrowth : C + 1 ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 20) :=
    relaxed_generator_coefficient_growth_paper_threshold hqr hq hn S P hqh hS
  obtain ⟨K, _, hd, M, _, _, hloss, _, σ, ρ, hE, hρ, hρcap, hspan⟩ :=
    exists_capped_avoiding_rainbow_generating_system_paper_threshold
      F₀ hU hA hpair hqr S.graph.card N t hN hqh le_rfl hS le_rfl hw hn
  intro B hB
  have hbound : IsCliqueFamilyBounded r (permutedUnion ρ M.generators)
      (C * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) := by
    simpa only [C, p, relaxedGeneratorPaletteSize, mul_assoc] using hρ
  obtain ⟨D, _, hD, hcap, hgen⟩ :=
    exists_integral_generators_from_system_with_cap_paper_threshold
      hA hqr hn hqh hS hpair.negative_mem (le_refl t) hgrowth
      K M.good hd M.good_subset hloss σ hE (permutedUnion ρ M.generators)
      hbound hρcap hspan B hB
  refine ⟨D, hD, fun e => ?_, hgen⟩
  exact (hcap e).trans (integral_generator_edge_cap_paper_threshold hqr hn hgrowth)

theorem exists_capped_integral_generators_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hq : 3 ≤ q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1)))) :
    ∃ D : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) / 2) ∧
      (∀ e : Block (Fin n) (r + 1),
        ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
          (n : ℝ) ^ (paperAlpha q (r + 1) / 10)) ∧
      ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
        IntegrallyDecomposable q J → GeneratedBy D J := by
  obtain ⟨T, A, hcard, hA, hcross, _, hw⟩ :=
    exists_small_carrier_clique_exchange q (r + 1) (Nat.succ_pos r) hqr
  obtain ⟨e, he⟩ := cliqueEdges_nonempty hqr.le T.system.base
  obtain ⟨P, hP, hPe⟩ := hA.2.2.1 e he
  have hpair : IsEliminationPair T.system P e := by
    refine ⟨hA.1 hP, ?_, fun f hf => hA.pair_local hP hf, hcross⟩
    rw [inter_comm]
    exact vertices_inter_eq_of_cliqueEdges_singleton (Nat.succ_pos r) P T.system.base e hPe
  obtain ⟨F, _, hF⟩ := exists_subset_card_eq (s := (univ : Finset (Fin q)))
    (show r + 1 ≤ univ.card by simpa only [card_univ, Fintype.card_fin] using hqr.le)
  exact exists_capped_integral_generators_with_exchange_paper_threshold ⟨F, hF⟩
    (Fintype.card_fin q) hA hpair hqr hq hcard hw hn B hB

end Arxiv2411_18291
