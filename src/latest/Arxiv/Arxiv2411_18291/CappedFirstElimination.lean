import Arxiv.Arxiv2411_18291.SharpVariableSplittingAtThreshold
import Arxiv.Arxiv2411_18291.VariableNearPairCounts
import Arxiv.Arxiv2411_18291.FiniteUniformElimination

/-! # First universal cancellation placements from the capped splitting family -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem first_variable_elimination_coefficient {q r H : ℕ} (hqr : r + 1 < q)
    (hH : H ≤ (4 * q) ^ (2 * q)) :
    1 + H * (4 * (r + 1).factorial) ≤ (4 * q) ^ (4 * q) := by
  have hq : 2 ≤ q := by omega
  have hf : (r + 1).factorial ≤ (4 * q) ^ q :=
    (Nat.factorial_le hqr.le).trans ((Nat.factorial_le_pow q).trans
      (Nat.pow_le_pow_left (by omega) q))
  have hp : H * (4 * (r + 1).factorial) ≤ (4 * q) ^ (3 * q + 1) := by
    calc
      _ ≤ (4 * q) ^ (2 * q) * ((4 * q) ^ 1 * (4 * q) ^ q) :=
        Nat.mul_le_mul hH (Nat.mul_le_mul (by simp only [pow_one]; omega) hf)
      _ = _ := by rw [← pow_add, ← pow_add]; congr 1; omega
  have hone : 1 ≤ (4 * q) ^ (3 * q + 1) := one_le_pow₀ (by omega)
  calc
    _ ≤ 2 * (4 * q) ^ (3 * q + 1) := by omega
    _ ≤ (4 * q) * (4 * q) ^ (3 * q + 1) := Nat.mul_le_mul_right _ (by omega)
    _ = (4 * q) ^ (3 * q + 2) := (pow_succ' _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem first_variable_elimination_density {q r n H : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) (hH : H ≤ (4 * q) ^ (2 * q)) :
    (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 45)) +
      H * (4 * (r + 1).factorial * (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 45))) ≤
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hc : (1 + H * (4 * (r + 1).factorial) : ℝ) ≤ (4 * q : ℝ) ^ (4 * q) := by
    exact_mod_cast first_variable_elimination_coefficient hqr hH
  have hg : (4 * q : ℝ) ^ (4 * q) ≤
      (n : ℝ) ^ (2 * paperAlpha q (r + 1) / 45) := by
    have hh := paper_threshold_alpha_rpow_lower hqr hn (s := 4 * q)
      (t := (2 / 45 : ℝ)) (by norm_num) (by push_cast; linarith)
    convert hh using 1
    congr 1
    ring
  calc
    _ = (1 + H * (4 * (r + 1).factorial)) *
        (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 45)) := by ring
    _ ≤ (n : ℝ) ^ (2 * paperAlpha q (r + 1) / 45) *
        (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 45)) :=
      mul_le_mul_of_nonneg_right (hc.trans hg) (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

theorem exists_capped_first_elimination_with_bounds_paper_threshold
    {W U : Type*} [Fintype W] [Fintype U] [DecidableEq W] [DecidableEq U] {q r n : ℕ}
    {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {D : Finset (Block (Fin n) q)} {B : Hypergraph (Fin n) (r + 1)}
    {C : Block (Fin n) q → ℕ}
    (F : VariableSplittingFamily S D B C ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))))
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hF : IsCliqueFamilyBounded r F.cliques
      ((n : ℝ) ^ (-(89 * paperAlpha q (r + 1) / 180))))
    (hcap : ∀ e : Block (Fin n) (r + 1),
      ((F.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
        (n : ℝ) ^ (7 * paperAlpha q (r + 1) / 60))
    (T : ExchangeSystem U q (r + 1)) (N : Block U q) (e : Block U (r + 1))
    (hpair : IsEliminationPair T N e) (hw : Fintype.card U ≤ (4 * q) ^ (2 * q))
    (hT : T.graph.card ≤ (4 * q) ^ (2 * q)) :
    ∃ E : EliminationFamily T N F.graph F.pairPositive F.pairNegative
        ((n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 45)) +
          T.graph.card * (4 * (r + 1).factorial *
            (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 45)))),
      IsGraphBounded E.graph ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hα := paperAlpha_pos hqr
  have hαmax := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  let θ : ℝ := (n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 45))
  have hpow : (n : ℝ) ^ (7 * paperAlpha q (r + 1) / 60) *
      (n : ℝ) ^ (-(89 * paperAlpha q (r + 1) / 180)) = θ := by
    dsimp only [θ]
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  obtain ⟨hP, hQ⟩ := F.near_pair_degree_bounds hA hqr.le
    (Real.rpow_pos_of_pos hn0 _) hcap hF
  simp only [Fintype.card_fin, hpow] at hP hQ
  have hlo : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ θ :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hαmax])
  have hhi : θ ≤ (4 * q : ℝ) ^ (24 * q) *
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)) := by
    calc
      _ ≤ (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hα])
      _ ≤ _ := le_mul_of_one_le_left (by positivity)
        (one_le_pow₀ (by exact_mod_cast (show 1 ≤ 4 * q by omega)))
  have hB : IsGraphBounded F.graph θ := F.bounded.mono
    (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith only [hα]))
  have hsupport (i : F.NearPairs) :
      cliqueEdges (r + 1) (F.pairPositive i) ∪ cliqueEdges (r + 1) (F.pairNegative i) ⊆
        F.graph := by
    intro f hf
    rcases mem_union.mp hf with hp | hq
    · exact F.cliques_support (mem_biUnion.mpr ⟨_, F.pairPositive_mem i, hp⟩)
    · exact F.cliques_support (mem_biUnion.mpr ⟨_, F.pairNegative_mem i, hq⟩)
  obtain ⟨E⟩ := exists_uniform_elimination_family_paper_threshold T N e hpair hqr hn hw hT
    hlo hhi F.graph hB F.NearPairs F.pairPositive F.pairNegative hsupport hP hQ
    (F.near_pair_inter hA)
  exact ⟨E, E.bounded.mono (first_variable_elimination_density hqr hn hT)⟩

theorem exists_capped_first_elimination_paper_threshold
    {W U : Type*} [Fintype W] [Fintype U] [DecidableEq W] [DecidableEq U] {q r n : ℕ}
    {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {D : Finset (Block (Fin n) q)} {B : Hypergraph (Fin n) (r + 1)}
    {C : Block (Fin n) q → ℕ}
    (F : VariableSplittingFamily S D B C ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))))
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hF : IsCliqueFamilyBounded r F.cliques
      ((n : ℝ) ^ (-(89 * paperAlpha q (r + 1) / 180))))
    (hcap : ∀ e : Block (Fin n) (r + 1),
      ((F.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
        (n : ℝ) ^ (7 * paperAlpha q (r + 1) / 60))
    (T : ExchangeSystem U q (r + 1)) (N : Block U q) (e : Block U (r + 1))
    (hpair : IsEliminationPair T N e) (hw : Fintype.card U ≤ (4 * q) ^ (2 * q))
    (hT : T.graph.card ≤ (4 * q) ^ (2 * q)) :
    Nonempty (EliminationFamily T N F.graph F.pairPositive F.pairNegative
      ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))) := by
  obtain ⟨E, hE⟩ := exists_capped_first_elimination_with_bounds_paper_threshold
    hA F hqr hn hF hcap T N e hpair hw hT
  exact ⟨{ E with bounded := hE }⟩

end Arxiv2411_18291
