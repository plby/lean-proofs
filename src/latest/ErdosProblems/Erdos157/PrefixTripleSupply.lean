import ErdosProblems.Erdos157.PrimeTripleCounts
import ErdosProblems.Erdos157.PrimeSupplySize

/-! Quantitative triple supply in each short-prefix residue class. -/

namespace Erdos157.Elementary

open Polynomial PolynomialCharacters Filter

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

theorem primeTriple_fiber_lower_of_primeSupply {n : ℕ} (g : K[X]) (hg : g.Monic)
    (hn : 0 < n) (hc : ∀ f : PrimeDegree K n, IsCoprime g f.1.1)
    (hsize : (6 : ℝ) ≤ (Fintype.card K : ℝ) ^ n / (2 * (n : ℝ) * Nat.card (AdjoinRoot g)ˣ))
    (hlower : ∀ a : (AdjoinRoot g)ˣ,
      (Fintype.card K : ℝ) ^ n / (2 * (n : ℝ) * Nat.card (AdjoinRoot g)ˣ) ≤
        primeProgressionCount g n ↑a) (u : (AdjoinRoot g)ˣ) :
    (Fintype.card K : ℝ) ^ (3 * n) / (512 * (n : ℝ) ^ 3 * Nat.card (AdjoinRoot g)ˣ) ≤
      Nat.card {T : PrimeTriple K n // T.residueUnit g hc = u} := by
  let : Finite (AdjoinRoot g) :=
    Finite.of_injective (AdjoinRoot.powerBasisAux' hg).equivFun
      (AdjoinRoot.powerBasisAux' hg).equivFun.injective
  let q : ℝ := Fintype.card K
  let φ : ℝ := Nat.card (AdjoinRoot g)ˣ
  let L : ℝ := q ^ n / (2 * (n : ℝ) * φ)
  have hφ : 0 < φ := by dsimp only [φ]; exact_mod_cast Nat.card_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmain := PrimeTriple.residueUnit_fiber_card_lower g hg hc L hsize hlower u
  have heq : φ ^ 2 * L ^ 3 / 54 = q ^ (3 * n) / (432 * (n : ℝ) ^ 3 * φ) := by
    dsimp only [L]
    rw [show 3 * n = n * 3 by omega, pow_mul]
    field_simp
    ring
  change φ ^ 2 * L ^ 3 / 54 ≤ _ at hmain
  rw [heq] at hmain
  calc
    _ ≤ q ^ (3 * n) / (432 * (n : ℝ) ^ 3 * φ) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      change 432 * (n : ℝ) ^ 3 * φ ≤ 512 * (n : ℝ) ^ 3 * φ
      nlinarith [mul_pos (pow_pos hn' 3) hφ]
    _ ≤ _ := hmain

variable [CharP K 2]

/-- A level-`k` triple, reduced modulo the first `j` auxiliary factors. -/
noncomputable def levelTripleResidue (k j : ℕ) (T : PrimeTriple K (levelDegree k)) :
    (AdjoinRoot (AuxiliaryModuli.product K j))ˣ :=
  T.residueUnit (AuxiliaryModuli.product K j)
    (fun f => AuxiliaryModuli.product_isCoprime_even_prime K (levelDegree_even k) f j)

theorem eventually_prefix_tripleSupply :
    ∀ᶠ k in atTop, ∀ u : (AdjoinRoot (AuxiliaryModuli.product K (prefixLength k)))ˣ,
      (Fintype.card K : ℝ) ^ (3 * levelDegree k) /
        (512 * (levelDegree k : ℝ) ^ 3 * Nat.card (AdjoinRoot (AuxiliaryModuli.product K (prefixLength k)))ˣ) ≤
      Nat.card {T : PrimeTriple K (levelDegree k) // levelTripleResidue k (prefixLength k) T = u} := by
  filter_upwards [AuxiliaryModuli.eventually_prefix_prime_lower (K := K),
    eventually_six_le_prefix_primeSupply (K := K), eventually_prefixDegree_lt_levelDegree]
      with k hprimes hsize hdeg
  intro u
  apply primeTriple_fiber_lower_of_primeSupply _ (AuxiliaryModuli.product_monic K _)
    (lt_of_le_of_lt (Nat.zero_le _) hdeg)
    (fun f => AuxiliaryModuli.product_isCoprime_even_prime K (levelDegree_even k) f _)
  · exact hsize _ (AuxiliaryModuli.product_monic K _) (AuxiliaryModuli.product_natDegree K _)
  · exact hprimes

end Erdos157.Elementary
