import Arxiv.Arxiv2411_18291.SharpGeneratorCoefficient

/-! # Unconditional integral generators at the printed size threshold

The complete coloured modular construction, focusing, local decoding, and
integral lifting all fit at `n0`, using half the `n^(-3*alpha/5)` budget.
The exchange configuration and its carrier are constructed, and no
integral-generation hypothesis is assumed.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_paper_integral_generators_with_exchange_paper_threshold
    {U W : Type*} [Fintype U] [Fintype W] [DecidableEq W] {q r : ℕ}
    (F₀ : Block U (r + 1)) (hU : Fintype.card U = q)
    {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {P : Block W q} {e : Block W (r + 1)} (hpair : IsEliminationPair S P e)
    (hqr : r + 1 < q)
    (hS : S.graph.card ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) {n : ℕ}
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    ∀ B : Hypergraph (Fin n) (r + 1),
      IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1))) →
      ∃ D : Finset (Block (Fin n) q),
        IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) / 2) ∧
        ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
          IntegrallyDecomposable q J → GeneratedBy D J := by
  let N := (r + 1).factorial * q.choose (r + 1)
  let t := 2 * q.choose (r + 1)
  have hN : 0 < N := Nat.mul_pos (Nat.factorial_pos _) (Nat.choose_pos hqr.le)
  have hqh : q.choose (r + 1) ≤ S.graph.card :=
    (Nat.le_self_pow two_ne_zero _).trans
      (by simpa only [pow_two] using hA.choose_sq_le (Nat.succ_pos r))
  let C := paperIntegralGeneratorCoefficient S P
  have hC : 0 ≤ C := by dsimp only [C, paperIntegralGeneratorCoefficient]; positivity
  have hCb : C + 1 ≤ (4 * q : ℝ) ^ (6 * q) :=
    paperIntegralGeneratorCoefficient_six_q hqr S P hqh hS
  obtain ⟨K, _, hd, M, _, hloss, σ, τ, hE, hτ, hspan⟩ :=
    exists_paper_avoiding_rainbow_generating_system_threshold
      F₀ hU hA hpair hqr S.graph.card N t hN hqh le_rfl hS le_rfl hw hn
  intro B hB
  have hbound : IsCliqueFamilyBounded r (permutedUnion τ M.generators)
      (C * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) := by
    simpa only [C, paperIntegralGeneratorCoefficient, t, mul_assoc] using hτ
  obtain ⟨D, _, hD, hgen⟩ := exists_integral_generators_from_system_paper_threshold
    hA hqr hn hpair.negative_mem (le_refl t) hC hCb
    K M.good hd M.good_subset hloss σ hE (permutedUnion τ M.generators) hbound hspan B hB
  exact ⟨D, hD, hgen⟩

theorem exists_paper_integral_generators_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1)))) :
    ∃ D : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) / 2) ∧
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
  exact exists_paper_integral_generators_with_exchange_paper_threshold ⟨F, hF⟩
    (Fintype.card_fin q) hA hpair hqr hcard hw hn B hB

end Arxiv2411_18291
