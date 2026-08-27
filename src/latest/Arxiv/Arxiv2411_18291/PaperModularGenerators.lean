import Arxiv.Arxiv2411_18291.FiniteSparseModularGenerators

/-! # KSG for the paper's fixed decoder modulus

The source defines N := r! * choose(q,r) in its local-decoder lemma,
uses this N in Gamma = Z/NZ, and uses the same local decoder in the
integral lift. KSG does not quantify a separate arbitrary modulus.
The stronger arbitrary-modulus APIs remain available at their stated
modulus-dependent thresholds.
-/

noncomputable section

namespace Arxiv2411_18291

def paperModulus (q r : ℕ) : ℕ := r.factorial * q.choose r

theorem paperModulus_pos {q r : ℕ} (hqr : r ≤ q) : 0 < paperModulus q r :=
  Nat.mul_pos (Nat.factorial_pos r) (Nat.choose_pos hqr)

theorem paperModulus_eq_descFactorial (q r : ℕ) :
    paperModulus q r = q.descFactorial r :=
  (Nat.descFactorial_eq_factorial_mul_choose q r).symm

theorem paper_modular_generators_whp {q r n h : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (p : unitInterval) (hp : (p : ℝ) = (n : ℝ) ^ (-paperAlpha q (r + 1))) :
    1 - Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) <
      (BernoulliSubset.probability (Block (Fin n) (r + 1)) p).real
        {ω | let K := sampleGraph ω
          IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
          |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
            (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ∧
          ∃ C : ModularGeneratingData K (cliqueFamily K q) (paperModulus q (r + 1)),
            IsCliqueFamilyBounded r C.generators
              (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
            C.generators.card ≤ (paperModulus q (r + 1)) * K.card ∧
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
                      (n.choose (q - (r + 1)) : ℝ))} := by
  exact reference_modular_generators_paper_whp_corrected hqr hn
    (paperModulus_pos hqr.le) le_rfl hqh hH p hp

theorem exists_paper_modular_generators {q r n h : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2) :
    ∃ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
      |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
        (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ∧
      ∃ C : ModularGeneratingData K (cliqueFamily K q) (paperModulus q (r + 1)),
        IsCliqueFamilyBounded r C.generators
          (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
        C.generators.card ≤ (paperModulus q (r + 1)) * K.card ∧
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
  exact exists_sparse_reference_modular_generators_paper_threshold hqr hn
    (paperModulus_pos hqr.le) le_rfl hqh hH

end Arxiv2411_18291
