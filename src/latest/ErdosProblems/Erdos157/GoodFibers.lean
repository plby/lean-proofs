import ErdosProblems.Erdos157.QuotientPrefixes

/-! Many large, disjoint triple-product fibers above every short-prefix class. -/

namespace Erdos157.Elementary

open Polynomial PolynomialCharacters FiniteFiberCounts AuxiliaryModuli Filter

theorem fiber_mass_comparison (q φ N : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (n m : ℕ) (hn : 0 < n) (hm : m ≤ 3 * n) (hN : N * φ ≤ q ^ m) :
    2 * N * (1 / (1024 * (n : ℝ) ^ 3)) * q ^ (3 * n - m) ≤
      q ^ (3 * n) / (512 * (n : ℝ) ^ 3 * φ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ = (N * φ) * q ^ (3 * n - m) := by field_simp; ring
    _ ≤ q ^ m * q ^ (3 * n - m) := mul_le_mul_of_nonneg_right hN (by positivity)
    _ = q ^ (3 * n) := by rw [← pow_add, Nat.add_sub_of_le hm]

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

noncomputable def fiberThreshold (k : ℕ) : ℝ :=
  (Fintype.card K : ℝ) ^ (3 * levelDegree k - k ^ 2) / (1024 * (levelDegree k : ℝ) ^ 3)

noncomputable def GoodResidue (k : ℕ) (v : (AdjoinRoot (product K k))ˣ) : Prop :=
  fiberThreshold (K := K) k ≤ (fiberCard (levelTripleResidue k k) v : ℝ)

theorem good_extensions_lower (k h : ℕ) (hhk : h ≤ k) (hn : 0 < levelDegree k)
    (u : (AdjoinRoot (product K h))ˣ)
    (hmass : (Fintype.card K : ℝ) ^ (3 * levelDegree k) /
      (512 * (levelDegree k : ℝ) ^ 3 * Nat.card (AdjoinRoot (product K h))ˣ) ≤
        fiberCard (levelTripleResidue k h) u) :
    (fiberCard (quotientProjection K hhk) u : ℝ) / (1024 * (levelDegree k : ℝ) ^ 3) ≤
      Nat.card {v : {v : (AdjoinRoot (product K k))ˣ // quotientProjection K hhk v = u} //
        GoodResidue k v.1} := by
  classical
  let f : PrimeTriple K (levelDegree k) → (AdjoinRoot (product K k))ˣ := levelTripleResidue k k
  let p := quotientProjection K hhk
  let A := {T : PrimeTriple K (levelDegree k) // p (f T) = u}
  let B := {v : (AdjoinRoot (product K k))ˣ // p v = u}
  let : Fintype A := Fintype.ofFinite _
  let : Fintype B := Fintype.ofFinite _
  let F : A → B := fiberRestriction f p u
  let q : ℝ := Fintype.card K
  let φ : ℝ := Nat.card (AdjoinRoot (product K h))ˣ
  let N : ℝ := Fintype.card B
  let ε : ℝ := 1 / (1024 * (levelDegree k : ℝ) ^ 3)
  let U : ℝ := q ^ (3 * levelDegree k - k ^ 2)
  have hq : 0 < q := by dsimp only [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hφ : 0 < φ := by dsimp only [φ]; exact_mod_cast Nat.card_pos
  have hn' : (0 : ℝ) < levelDegree k := by exact_mod_cast hn
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hU : 0 < U := pow_pos hq _
  have hcardA : Fintype.card A = fiberCard (levelTripleResidue k h) u := by
    rw [← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro T
    change quotientProjection K hhk (levelTripleResidue k k T) = u ↔ _
    rw [quotientProjection_levelTripleResidue]
  have hN : N * φ ≤ q ^ (k ^ 2) := by
    have hproj := quotientProjection_fiberCard_mul K hhk u
    have hcap := natCard_adjoinRoot_units_le (product K k) (product_monic K k)
    rw [product_natDegree] at hcap
    have hB : Fintype.card B = fiberCard p u := by
      rw [← Nat.card_eq_fintype_card]
      rfl
    have hncard : Fintype.card B * Nat.card (AdjoinRoot (product K h))ˣ ≤ Fintype.card K ^ (k ^ 2) := by
      rw [hB]
      exact hproj.trans_le hcap
    dsimp only [N, φ, q]
    exact_mod_cast hncard
  have hmass' : 2 * (Fintype.card B : ℝ) * ε * U ≤ Fintype.card A := by
    calc
      _ ≤ q ^ (3 * levelDegree k) / (512 * (levelDegree k : ℝ) ^ 3 * φ) :=
        fiber_mass_comparison q φ N hq hφ _ _ hn (square_le_triple_levelDegree k) hN
      _ ≤ (fiberCard (levelTripleResidue k h) u : ℝ) := hmass
      _ = _ := by rw [hcardA]
  have hcap : ∀ v : B, (fiberCard F v : ℝ) ≤ U := by
    intro v
    change (fiberCard (fiberRestriction f p u) v : ℝ) ≤ U
    rw [fiberCard_restriction]
    have hb := PrimeTriple.residueUnit_fiber_card_le (product K k) (product_monic K k)
      (by rw [product_natDegree]; exact square_le_triple_levelDegree k)
      (fun f => product_isCoprime_even_prime K (levelDegree_even k) f k) v.1
    rw [product_natDegree] at hb
    dsimp only [fiberCard, f, U, q, levelTripleResidue]
    exact_mod_cast hb
  have hgood := many_large_fibers_fraction F ε U hε hU hmass' hcap
  have hpred (v : B) : ε * U ≤ (fiberCard F v : ℝ) ↔ GoodResidue k v.1 := by
    change ε * U ≤ (fiberCard (fiberRestriction f p u) v : ℝ) ↔ _
    rw [fiberCard_restriction]
    have hthreshold : ε * U = fiberThreshold (K := K) k := by
      dsimp only [ε, U, q, fiberThreshold]
      ring
    rw [hthreshold]
    rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight hpred)] at hgood
  have hB : Fintype.card B = fiberCard p u := by rw [← Nat.card_eq_fintype_card]; rfl
  rw [hB] at hgood
  have hleft : ε * (fiberCard p u : ℝ) =
      (fiberCard p u : ℝ) / (1024 * (levelDegree k : ℝ) ^ 3) := by
    dsimp only [ε]
    ring
  rw [hleft] at hgood
  exact hgood

theorem eventually_good_extensions :
    ∀ᶠ k in atTop, prefixLength k ≤ k ∧ ∀ (hhk : prefixLength k ≤ k)
      (u : (AdjoinRoot (product K (prefixLength k)))ˣ),
      (fiberCard (quotientProjection K hhk) u : ℝ) / (1024 * (levelDegree k : ℝ) ^ 3) ≤
        Nat.card {v : {v : (AdjoinRoot (product K k))ˣ // quotientProjection K hhk v = u} //
          GoodResidue k v.1} := by
  filter_upwards [eventually_prefixLength_le, eventually_prefix_tripleSupply (K := K),
    eventually_prefixDegree_lt_levelDegree] with k hk hmass hdeg
  refine ⟨hk, fun hhk u => ?_⟩
  exact good_extensions_lower k (prefixLength k) hhk (lt_of_le_of_lt (Nat.zero_le _) hdeg) u (hmass u)

theorem levelTripleResidue_fiber_pairwise_disjoint (k : ℕ) (hk : 4 ≤ k)
    (u : (AdjoinRoot (product K k))ˣ) :
    Set.Pairwise {T : PrimeTriple K (levelDegree k) | levelTripleResidue k k T = u}
      (fun U V => Disjoint U.1 V.1) := by
  apply PrimeTriple.residueUnit_fiber_pairwise_disjoint
  rw [product_natDegree]
  exact double_levelDegree_lt_square k hk

end Erdos157.Elementary
