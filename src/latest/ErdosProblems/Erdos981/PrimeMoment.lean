import ErdosProblems.Erdos981.Core
import BoundedGaps.BombieriVinogradov.Proof.MainTheorem
import BoundedGaps.Maynard.Distribution
import BoundedGaps.Maynard.MaynardCoprimeHarmonic
import ErdosProblems.Erdos387.UniformAnalyticInputs

open scoped BigOperators
open Filter Finset Asymptotics

namespace Erdos981

noncomputable def test_primeQuadraticDenominatorSum (k x : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (x + 1),
    if p.Prime then (quadraticDenominatorTerm k p : ℝ) else 0

def test_bvPrimeResidueFinset (x q a : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun p => p.Prime ∧ p % q = a

lemma test_bvPrimeResidueFinset_card {x q a : ℕ} (ha : a < q) :
    (test_bvPrimeResidueFinset x q a).card =
      BoundedGaps.Maynard.primeCountUpTo x q a := by
  classical
  unfold test_bvPrimeResidueFinset BoundedGaps.Maynard.primeCountUpTo
  congr 1
  ext p
  simp [Nat.mod_eq_of_lt ha]

lemma test_bvPrimeResidueFinset_pairwiseDisjoint (x q : ℕ) :
    Set.PairwiseDisjoint
      (↑(BoundedGaps.Maynard.coprimeResidues q) : Set ℕ)
      (fun a => test_bvPrimeResidueFinset x q a) := by
  classical
  let t := (Finset.range (x + 1)).filter Nat.Prime
  have h := Set.pairwiseDisjoint_filter (fun p : ℕ => p % q)
    (↑(BoundedGaps.Maynard.coprimeResidues q) : Set ℕ) t
  simpa [t, test_bvPrimeResidueFinset, Finset.filter_filter, and_assoc] using h

lemma test_biUnion_bvPrimeResidueFinset_eq (x q : ℕ) (hq : 0 < q) :
    (BoundedGaps.Maynard.coprimeResidues q).biUnion
        (fun a => test_bvPrimeResidueFinset x q a) =
      (Finset.range (x + 1)).filter fun p => p.Prime ∧ p.Coprime q := by
  classical
  ext p
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range,
    BoundedGaps.Maynard.coprimeResidues, test_bvPrimeResidueFinset]
  constructor
  · rintro ⟨a, ⟨haq, hacop⟩, hpRange, hpPrime, hpa⟩
    have hmod : Nat.ModEq q p a := by
      change p % q = a % q
      rw [hpa, Nat.mod_eq_of_lt haq]
    have hpcop : p.Coprime q := by
      rw [Nat.coprime_iff_gcd_eq_one, hmod.gcd_eq]
      exact hacop.gcd_eq_one
    exact ⟨hpRange, hpPrime, hpcop⟩
  · rintro ⟨hpRange, hpPrime, hpcop⟩
    let a := p % q
    have haq : a < q := Nat.mod_lt p hq
    have hmod : Nat.ModEq q p a := by
      change p % q = a % q
      simp [a, Nat.mod_eq_of_lt haq]
    have hacop : a.Coprime q := by
      rw [Nat.coprime_iff_gcd_eq_one, ← hmod.gcd_eq]
      exact hpcop.gcd_eq_one
    exact ⟨a, ⟨haq, hacop⟩, hpRange, hpPrime, rfl⟩

lemma test_primeQuadraticDenominatorSum_eq_residue_sum
    {k : ℕ} (hk : 0 < k) (x : ℕ) :
    test_primeQuadraticDenominatorSum k x =
      ∑ a ∈ BoundedGaps.Maynard.coprimeResidues (4 * k),
        (quadraticDenominatorTerm k a : ℝ) *
          BoundedGaps.Maynard.primeCountUpTo x (4 * k) a := by
  classical
  let q := 4 * k
  have hq : 0 < q := by positivity
  have hdisj := test_bvPrimeResidueFinset_pairwiseDisjoint x q
  have hnoncop : ∀ p ∈ Finset.range (x + 1), p.Prime → ¬p.Coprime q →
      quadraticDenominatorTerm k p = 0 := by
    intro p hpRange hpPrime hpcop
    rw [quadraticDenominatorTerm_eq_attached hk]
    exact (attachedQuadraticCharacter k q (dvd_refl q)).map_non_coprime hpcop
  rw [test_primeQuadraticDenominatorSum]
  calc
    (∑ p ∈ Finset.range (x + 1),
        if p.Prime then (quadraticDenominatorTerm k p : ℝ) else 0) =
      ∑ p ∈ Finset.range (x + 1),
        if p.Prime ∧ p.Coprime q then
          (quadraticDenominatorTerm k p : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          by_cases hpPrime : p.Prime
          · by_cases hpCop : p.Coprime q
            · simp [hpPrime, hpCop]
            · simp [hpPrime, hpCop, hnoncop p hp hpPrime hpCop]
          · simp [hpPrime]
    _ =
      ∑ p ∈ (Finset.range (x + 1)).filter (fun p => p.Prime ∧ p.Coprime q),
        (quadraticDenominatorTerm k p : ℝ) := by
          rw [Finset.sum_filter]
    _ = ∑ a ∈ BoundedGaps.Maynard.coprimeResidues q,
        ∑ p ∈ test_bvPrimeResidueFinset x q a,
          (quadraticDenominatorTerm k p : ℝ) := by
      rw [← Finset.sum_biUnion hdisj, test_biUnion_bvPrimeResidueFinset_eq x q hq]
    _ = ∑ a ∈ BoundedGaps.Maynard.coprimeResidues q,
        (quadraticDenominatorTerm k a : ℝ) *
          BoundedGaps.Maynard.primeCountUpTo x q a := by
      apply Finset.sum_congr rfl
      intro a ha
      have haData := Finset.mem_filter.mp ha
      have haq : a < q := Finset.mem_range.mp haData.1
      have hacop : a.Coprime q := haData.2
      calc
        ∑ p ∈ test_bvPrimeResidueFinset x q a,
            (quadraticDenominatorTerm k p : ℝ) =
          ∑ _p ∈ test_bvPrimeResidueFinset x q a,
            (quadraticDenominatorTerm k a : ℝ) := by
              apply Finset.sum_congr rfl
              intro p hp
              have hpData := Finset.mem_filter.mp hp
              have hpa := hpData.2.2
              have hmod : Nat.ModEq q p a := by
                change p % q = a % q
                rw [hpa, Nat.mod_eq_of_lt haq]
              rw [quadraticDenominatorTerm_eq_attached hk,
                quadraticDenominatorTerm_eq_attached hk]
              exact_mod_cast
                (attachedQuadraticCharacter k q (dvd_refl q)).periodic hmod
        _ = (quadraticDenominatorTerm k a : ℝ) *
            BoundedGaps.Maynard.primeCountUpTo x q a := by
          rw [← test_bvPrimeResidueFinset_card haq]
          simp [mul_comm]

lemma test_sum_quadraticDenominatorTerm_coprimeResidues_eq_zero
    {k : ℕ} (hk : 0 < k) (hksq : ¬IsSquare k) :
    ∑ a ∈ BoundedGaps.Maynard.coprimeResidues (4 * k),
      quadraticDenominatorTerm k a = 0 := by
  classical
  let q := 4 * k
  have hq : 0 < q := by positivity
  have hnoncop : ∀ a ∈ Finset.range q, ¬a.Coprime q →
      quadraticDenominatorTerm k a = 0 := by
    intro a ha hcop
    rw [quadraticDenominatorTerm_eq_attached hk]
    exact (attachedQuadraticCharacter k q (dvd_refl q)).map_non_coprime hcop
  calc
    ∑ a ∈ BoundedGaps.Maynard.coprimeResidues q,
        quadraticDenominatorTerm k a =
      ∑ a ∈ Finset.range q, quadraticDenominatorTerm k a := by
        rw [BoundedGaps.Maynard.coprimeResidues, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hcop : a.Coprime q
        · simp [hcop]
        · simp [hcop, hnoncop a ha hcop]
    _ = 0 := sum_quadraticDenominatorTerm_period_eq_zero hk hksq

lemma test_abs_primeQuadraticDenominatorSum_le
    {k : ℕ} (hk : 0 < k) (hksq : ¬IsSquare k) (x : ℕ) :
    |test_primeQuadraticDenominatorSum k x| ≤
      (4 * k : ℝ) * BoundedGaps.Maynard.maxProgressionDiscrepancy x (4 * k) := by
  classical
  let q := 4 * k
  let P : ℝ := BoundedGaps.Maynard.primeCountTotal x
  let φ : ℝ := Nat.totient q
  let D : ℝ := BoundedGaps.Maynard.maxProgressionDiscrepancy x q
  have hq : 0 < q := by positivity
  have hzeroZ := test_sum_quadraticDenominatorTerm_coprimeResidues_eq_zero hk hksq
  have hzeroR :
      ∑ a ∈ BoundedGaps.Maynard.coprimeResidues q,
        (quadraticDenominatorTerm k a : ℝ) = 0 := by
    exact_mod_cast hzeroZ
  have hcenter :
      (∑ a ∈ BoundedGaps.Maynard.coprimeResidues q,
        (quadraticDenominatorTerm k a : ℝ) *
          BoundedGaps.Maynard.primeCountUpTo x q a) =
      ∑ a ∈ BoundedGaps.Maynard.coprimeResidues q,
        (quadraticDenominatorTerm k a : ℝ) *
          ((BoundedGaps.Maynard.primeCountUpTo x q a : ℝ) - P / φ) := by
    calc
      (∑ a ∈ BoundedGaps.Maynard.coprimeResidues q,
          (quadraticDenominatorTerm k a : ℝ) *
            BoundedGaps.Maynard.primeCountUpTo x q a) =
        ∑ a ∈ BoundedGaps.Maynard.coprimeResidues q,
          ((quadraticDenominatorTerm k a : ℝ) *
              ((BoundedGaps.Maynard.primeCountUpTo x q a : ℝ) - P / φ) +
            (quadraticDenominatorTerm k a : ℝ) * (P / φ)) := by
              apply Finset.sum_congr rfl
              intro a ha
              ring
      _ = (∑ a ∈ BoundedGaps.Maynard.coprimeResidues q,
          (quadraticDenominatorTerm k a : ℝ) *
            ((BoundedGaps.Maynard.primeCountUpTo x q a : ℝ) - P / φ)) +
          (∑ a ∈ BoundedGaps.Maynard.coprimeResidues q,
            (quadraticDenominatorTerm k a : ℝ)) * (P / φ) := by
              rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = _ := by rw [hzeroR, zero_mul, add_zero]
  have hχabs (a : ℕ) : |(quadraticDenominatorTerm k a : ℝ)| ≤ 1 := by
    unfold quadraticDenominatorTerm
    split_ifs with hodd
    · rcases jacobiSym.trichotomy (a := (k : ℤ)) (b := a) with h | h | h
      · rw [h]
        norm_num
      · rw [h]
        norm_num
      · rw [h]
        norm_num
    · norm_num
  have hterm : ∀ a ∈ BoundedGaps.Maynard.coprimeResidues q,
      |(quadraticDenominatorTerm k a : ℝ) *
          ((BoundedGaps.Maynard.primeCountUpTo x q a : ℝ) - P / φ)| ≤ D := by
    intro a ha
    have hdisc := BoundedGaps.Maynard.progressionDiscrepancy_le_max
      (x := x) hq ha
    have habsDiff :
        |(BoundedGaps.Maynard.primeCountUpTo x q a : ℝ) - P / φ| =
          BoundedGaps.Maynard.progressionDiscrepancy x q a := by
      rfl
    rw [abs_mul, habsDiff]
    exact (mul_le_mul (hχabs a) hdisc
      (BoundedGaps.Maynard.progressionDiscrepancy_nonneg x q a)
      (by norm_num)).trans_eq (one_mul D)
  rw [test_primeQuadraticDenominatorSum_eq_residue_sum hk x, hcenter]
  calc
    |∑ a ∈ BoundedGaps.Maynard.coprimeResidues q,
        (quadraticDenominatorTerm k a : ℝ) *
          ((BoundedGaps.Maynard.primeCountUpTo x q a : ℝ) - P / φ)| ≤
      ∑ a ∈ BoundedGaps.Maynard.coprimeResidues q,
        |(quadraticDenominatorTerm k a : ℝ) *
          ((BoundedGaps.Maynard.primeCountUpTo x q a : ℝ) - P / φ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ BoundedGaps.Maynard.coprimeResidues q, D :=
      Finset.sum_le_sum hterm
    _ = (Nat.totient q : ℝ) * D := by
      rw [Finset.sum_const, nsmul_eq_mul,
        BoundedGaps.Maynard.card_coprimeResidues]
    _ ≤ (q : ℝ) * D := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le q)
        (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg x q)
    _ = (4 * k : ℝ) *
        BoundedGaps.Maynard.maxProgressionDiscrepancy x (4 * k) := by
      dsimp [q, D]
      norm_num

noncomputable def test_oddPrimeMoment (r N x : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (x + 1),
    if p.Prime ∧ Odd p then (legendrePartialSum p N : ℝ) ^ (2 * r) else 0

lemma test_oddPrimeMoment_eq_tuple_sum (r N x : ℕ) :
    test_oddPrimeMoment r N x =
      ∑ ab ∈ (tupleBox r N).product (tupleBox r N),
        test_primeQuadraticDenominatorSum
          (tupleProduct ab.1 * tupleProduct ab.2) x := by
  classical
  unfold test_oddPrimeMoment test_primeQuadraticDenominatorSum
  calc
    (∑ p ∈ Finset.range (x + 1),
        if p.Prime ∧ Odd p then (legendrePartialSum p N : ℝ) ^ (2 * r) else 0) =
      ∑ p ∈ Finset.range (x + 1),
        ∑ ab ∈ (tupleBox r N).product (tupleBox r N),
          if p.Prime then (quadraticDenominatorTerm
            (tupleProduct ab.1 * tupleProduct ab.2) p : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hpPrime : p.Prime
      · by_cases hpOdd : Odd p
        · simp only [hpPrime, hpOdd, and_self, if_true]
          norm_cast
          rw [legendrePartialSum_evenMoment_eq]
          apply Finset.sum_congr rfl
          intro ab hab
          simp [quadraticDenominatorTerm, hpOdd]
        · simp [hpPrime, hpOdd, quadraticDenominatorTerm]
      · simp [hpPrime]
    _ = _ := by rw [Finset.sum_comm]

lemma test_primeQuadraticDenominatorSum_le_primeCount_of_square
    {k : ℕ} (hk : IsSquare k) (x : ℕ) :
    test_primeQuadraticDenominatorSum k x ≤
      BoundedGaps.Maynard.primeCountTotal x := by
  classical
  unfold test_primeQuadraticDenominatorSum
  calc
    (∑ p ∈ Finset.range (x + 1),
        if p.Prime then (quadraticDenominatorTerm k p : ℝ) else 0) ≤
      ∑ p ∈ Finset.range (x + 1), if p.Prime then (1 : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro p hp
        by_cases hpPrime : p.Prime
        · simp only [hpPrime, if_true]
          exact_mod_cast quadraticDenominatorTerm_le_one k p
        · simp [hpPrime]
    _ = BoundedGaps.Maynard.primeCountTotal x := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast (by
        unfold BoundedGaps.Maynard.primeCountTotal
        rw [Nat.primeCounting_eq_primeCounting'_succ]
        simpa [Nat.primesBelow] using
          Nat.primesBelow_card_eq_primeCounting' (x + 1))

lemma test_oddPrimeMoment_le (r N x : ℕ) :
    test_oddPrimeMoment r N x ≤
      (BoundedGaps.Maynard.primeCountTotal x : ℝ) *
          ((squareTuplePairs r N).card : ℝ) +
        (4 * N ^ (2 * r) : ℕ) *
          (((tupleBox r N).product (tupleBox r N)).card : ℝ) *
            (∑ q ∈ Finset.Icc 1 (4 * N ^ (2 * r)),
              BoundedGaps.Maynard.maxProgressionDiscrepancy x q) := by
  classical
  rw [test_oddPrimeMoment_eq_tuple_sum]
  let S := (tupleBox r N).product (tupleBox r N)
  let Q := 4 * N ^ (2 * r)
  let E := ∑ q ∈ Finset.Icc 1 Q,
    BoundedGaps.Maynard.maxProgressionDiscrepancy x q
  have hE : 0 ≤ E := Finset.sum_nonneg fun q hq =>
    BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg x q
  have hterm : ∀ ab ∈ S,
      test_primeQuadraticDenominatorSum
          (tupleProduct ab.1 * tupleProduct ab.2) x ≤
        (if IsSquare (tupleProduct ab.1 * tupleProduct ab.2) then
            (BoundedGaps.Maynard.primeCountTotal x : ℝ) else 0) +
          (Q : ℝ) * E := by
    intro ab hab
    let k := tupleProduct ab.1 * tupleProduct ab.2
    have habData := Finset.mem_product.mp hab
    have hkpos : 0 < k := by
      dsimp [k]
      exact Nat.mul_pos (tupleProduct_pos_of_mem habData.1)
        (tupleProduct_pos_of_mem habData.2)
    have hkQ : 4 * k ≤ Q := by
      dsimp [k, Q]
      exact Nat.mul_le_mul_left 4 (tuplePairProduct_le_pow hab)
    change test_primeQuadraticDenominatorSum k x ≤
      (if IsSquare k then
          (BoundedGaps.Maynard.primeCountTotal x : ℝ) else 0) +
        (Q : ℝ) * E
    by_cases hksq : IsSquare k
    · calc
        test_primeQuadraticDenominatorSum k x ≤
            BoundedGaps.Maynard.primeCountTotal x :=
          test_primeQuadraticDenominatorSum_le_primeCount_of_square hksq x
        _ ≤ (BoundedGaps.Maynard.primeCountTotal x : ℝ) + (Q : ℝ) * E := by
          exact le_add_of_nonneg_right (mul_nonneg (by positivity) hE)
        _ = _ := by simp [hksq]
    · have habs := test_abs_primeQuadraticDenominatorSum_le hkpos hksq x
      have hqmem : 4 * k ∈ Finset.Icc 1 Q := Finset.mem_Icc.mpr ⟨by omega, hkQ⟩
      have hdisc : BoundedGaps.Maynard.maxProgressionDiscrepancy x (4 * k) ≤ E := by
        exact Finset.single_le_sum (fun q hq =>
          BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg x q) hqmem
      calc
        test_primeQuadraticDenominatorSum k x ≤
            |test_primeQuadraticDenominatorSum k x| := le_abs_self _
        _ ≤ (4 * k : ℝ) *
            BoundedGaps.Maynard.maxProgressionDiscrepancy x (4 * k) := habs
        _ ≤ (Q : ℝ) * E := by
          exact mul_le_mul (by exact_mod_cast hkQ) hdisc
            (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg x (4 * k))
            (by positivity)
        _ = _ := by simp [hksq]
  calc
    (∑ ab ∈ S, test_primeQuadraticDenominatorSum
        (tupleProduct ab.1 * tupleProduct ab.2) x) ≤
      ∑ ab ∈ S,
        ((if IsSquare (tupleProduct ab.1 * tupleProduct ab.2) then
            (BoundedGaps.Maynard.primeCountTotal x : ℝ) else 0) +
          (Q : ℝ) * E) := Finset.sum_le_sum hterm
    _ = (BoundedGaps.Maynard.primeCountTotal x : ℝ) *
          ((squareTuplePairs r N).card : ℝ) +
        (Q : ℝ) * ((S.card : ℝ) * E) := by
      rw [Finset.sum_add_distrib]
      have hsq : (∑ ab ∈ S,
          if IsSquare (tupleProduct ab.1 * tupleProduct ab.2) then
            (BoundedGaps.Maynard.primeCountTotal x : ℝ) else 0) =
          (BoundedGaps.Maynard.primeCountTotal x : ℝ) *
            ((squareTuplePairs r N).card : ℝ) := by
        rw [← Finset.sum_filter]
        rw [← squareTuplePairs_eq_filter]
        simp [mul_comm]
      rw [hsq]
      simp
      ring
    _ = _ := by
      dsimp [S, Q, E]
      ring

noncomputable def test_oddPrimeBad (ε : ℝ) (N x : ℕ) : Finset ℕ :=
  (Finset.range (x + 1)).filter fun p =>
    p.Prime ∧ Odd p ∧ ε * (N : ℝ) ≤ (legendrePartialSum p N : ℝ)

lemma test_oddPrimeBad_card_mul_le_moment
    {ε : ℝ} (hε : 0 ≤ ε) (N x : ℕ) :
    ((test_oddPrimeBad ε N x).card : ℝ) * (ε * (N : ℝ)) ^ 20 ≤
      test_oddPrimeMoment 10 N x := by
  classical
  unfold test_oddPrimeMoment
  calc
    ((test_oddPrimeBad ε N x).card : ℝ) * (ε * (N : ℝ)) ^ 20 =
      ∑ _p ∈ test_oddPrimeBad ε N x, (ε * (N : ℝ)) ^ 20 := by
        simp [mul_comm]
    _ ≤ ∑ p ∈ test_oddPrimeBad ε N x,
        (legendrePartialSum p N : ℝ) ^ 20 := by
      apply Finset.sum_le_sum
      intro p hp
      have hpge := (Finset.mem_filter.mp hp).2.2.2
      exact pow_le_pow_left₀ (mul_nonneg hε (by positivity)) hpge 20
    _ ≤ ∑ p ∈ Finset.range (x + 1),
        if p.Prime ∧ Odd p then (legendrePartialSum p N : ℝ) ^ 20 else 0 := by
      rw [show (∑ p ∈ test_oddPrimeBad ε N x,
          (legendrePartialSum p N : ℝ) ^ 20) =
        ∑ p ∈ test_oddPrimeBad ε N x,
          if p.Prime ∧ Odd p then (legendrePartialSum p N : ℝ) ^ 20 else 0 by
        apply Finset.sum_congr rfl
        intro p hp
        have hpd := (Finset.mem_filter.mp hp).2
        rw [if_pos ⟨hpd.1, hpd.2.1⟩]]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro p hp hnot
        split_ifs <;> positivity
    _ = _ := by norm_num

lemma test_oddPrimeMoment_twentieth_le
    {N : ℕ} (hN : 1 ≤ N) (hdiag :
      ((squareTuplePairs 10 N).card : ℝ) ≤ (N : ℝ) ^ 17) (x : ℕ) :
    test_oddPrimeMoment 10 N x ≤
      (BoundedGaps.Maynard.primeCountTotal x : ℝ) * (N : ℝ) ^ 17 +
        4 * (N : ℝ) ^ 40 *
          (∑ q ∈ Finset.Icc 1 (4 * N ^ 20),
            BoundedGaps.Maynard.maxProgressionDiscrepancy x q) := by
  have h := test_oddPrimeMoment_le 10 N x
  norm_num at h ⊢
  rw [tupleBox_card] at h
  norm_num at h
  have hpi : (0 : ℝ) ≤ BoundedGaps.Maynard.primeCountTotal x := by positivity
  calc
    test_oddPrimeMoment 10 N x ≤
      (BoundedGaps.Maynard.primeCountTotal x : ℝ) *
          ((squareTuplePairs 10 N).card : ℝ) +
        4 * (N : ℝ) ^ 20 * ((N : ℝ) ^ 10 * (N : ℝ) ^ 10) *
          (∑ q ∈ Finset.Icc 1 (4 * N ^ 20),
            BoundedGaps.Maynard.maxProgressionDiscrepancy x q) := h
    _ = (BoundedGaps.Maynard.primeCountTotal x : ℝ) *
          ((squareTuplePairs 10 N).card : ℝ) +
        4 * (N : ℝ) ^ 40 *
          (∑ q ∈ Finset.Icc 1 (4 * N ^ 20),
            BoundedGaps.Maynard.maxProgressionDiscrepancy x q) := by ring
    _ ≤ (BoundedGaps.Maynard.primeCountTotal x : ℝ) * (N : ℝ) ^ 17 +
        4 * (N : ℝ) ^ 40 *
          (∑ q ∈ Finset.Icc 1 (4 * N ^ 20),
            BoundedGaps.Maynard.maxProgressionDiscrepancy x q) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hdiag hpi) le_rfl

lemma test_exists_squareTuplePairs_ten_card_le :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((squareTuplePairs 10 N).card : ℝ) ≤ (N : ℝ) ^ 17 := by
  obtain ⟨N₀, hN₀⟩ := exists_squareTuplePairs_card_le 10 (by omega)
  refine ⟨max 1 N₀, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := (le_max_left 1 N₀).trans hN
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have henv : Erdos439.PowerDecay.divisorSubpowerEnvelope N ≤ (N : ℝ) := by
    exact Real.rpow_le_self_of_one_le hbase (by norm_num)
  calc
    ((squareTuplePairs 10 N).card : ℝ) ≤
        Erdos439.PowerDecay.divisorSubpowerEnvelope N ^ 2 *
          ((N ^ 10 : ℕ) * Nat.sqrt (N ^ 10) : ℕ) :=
      hN₀ N ((le_max_right 1 N₀).trans hN)
    _ = Erdos439.PowerDecay.divisorSubpowerEnvelope N ^ 2 *
          ((N : ℝ) ^ 10 * (N : ℝ) ^ 5) := by
      rw [show Nat.sqrt (N ^ 10) = N ^ 5 by
        rw [show N ^ 10 = (N ^ 5) ^ 2 by ring]
        simp]
      push_cast
      rfl
    _ ≤ (N : ℝ) ^ 2 * ((N : ℝ) ^ 10 * (N : ℝ) ^ 5) := by
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by
        show 0 ≤ (N : ℝ) ^ (1 / 8 : ℝ)
        exact Real.rpow_nonneg (by positivity) _) henv 2) (by positivity)
    _ = (N : ℝ) ^ 17 := by ring

lemma test_four_mul_pow_le_binaryLogScale_pow
    {N x : ℕ} (hL : 2 ≤ Erdos387.binaryLogScale x)
    (hN : N ≤ Erdos387.binaryLogScale x ^ 3) :
    4 * N ^ 20 ≤ Erdos387.binaryLogScale x ^ 62 := by
  let L := Erdos387.binaryLogScale x
  have hpow : N ^ 20 ≤ (L ^ 3) ^ 20 := Nat.pow_le_pow_left hN 20
  have hfour : 4 ≤ L ^ 2 := by nlinarith
  calc
    4 * N ^ 20 ≤ L ^ 2 * (L ^ 3) ^ 20 := Nat.mul_le_mul hfour hpow
    _ = L ^ 62 := by ring

lemma test_exists_uniform_oddPrimeBad_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ X₀ : ℕ,
      ∀ x ≥ X₀, ∀ N ≥ N₀, N ≤ Erdos387.binaryLogScale x ^ 3 →
        ((test_oddPrimeBad ε N x).card : ℝ) ≤
          (ε ^ 20)⁻¹ *
            ((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) / (N : ℝ) ^ 3 +
              4 * C * ((2 * x : ℕ) : ℝ) * (N : ℝ) ^ 20 /
                Real.rpow (Real.log ((2 * x : ℕ) : ℝ)) 100) := by
  obtain ⟨Ndiag, hdiag⟩ := test_exists_squareTuplePairs_ten_card_le
  have hBV := BoundedGaps.Maynard.unconditional_bombieriVinogradov
    (1 / 4 : ℝ) (by norm_num) (by norm_num)
  obtain ⟨C, hC, Xbv, hXbv, hdist⟩ := hBV 100 (by norm_num)
  obtain ⟨Xcut, hXcut⟩ := eventually_atTop.mp
    (Erdos387.eventually_binaryLogScale_pow_le_quarterCutoff 62)
  refine ⟨C, hC, max 1 Ndiag, max 4 (max Xbv Xcut), ?_⟩
  intro x hx N hN hNL
  have hx4 : 4 ≤ x := (le_max_left 4 (max Xbv Xcut)).trans hx
  have hxBV : Xbv ≤ x := (le_max_left Xbv Xcut).trans
    ((le_max_right 4 (max Xbv Xcut)).trans hx)
  have hxCut : Xcut ≤ x := (le_max_right Xbv Xcut).trans
    ((le_max_right 4 (max Xbv Xcut)).trans hx)
  have hN1 : 1 ≤ N := (le_max_left 1 Ndiag).trans hN
  have hNdiag : Ndiag ≤ N := (le_max_right 1 Ndiag).trans hN
  have hL2 : 2 ≤ Erdos387.binaryLogScale x := by
    unfold Erdos387.binaryLogScale
    have : 1 ≤ Nat.log 2 x := Nat.log_pos (by omega) (by omega)
    omega
  have hQcut : 4 * N ^ 20 ≤
      BoundedGaps.Maynard.modulusCutoff (1 / 4 : ℝ) (2 * x) :=
    (test_four_mul_pow_le_binaryLogScale_pow hL2 hNL).trans (hXcut x hxCut)
  have hE : (∑ q ∈ Finset.Icc 1 (4 * N ^ 20),
      BoundedGaps.Maynard.maxProgressionDiscrepancy (2 * x) q) ≤
      C * ((2 * x : ℕ) : ℝ) /
        Real.rpow (Real.log ((2 * x : ℕ) : ℝ)) 100 := by
    calc
      (∑ q ∈ Finset.Icc 1 (4 * N ^ 20),
          BoundedGaps.Maynard.maxProgressionDiscrepancy (2 * x) q) ≤
        ∑ q ∈ Finset.Icc 1
            (BoundedGaps.Maynard.modulusCutoff (1 / 4 : ℝ) (2 * x)),
          BoundedGaps.Maynard.maxProgressionDiscrepancy (2 * x) q := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.Icc_subset_Icc_right hQcut
            · intro q hq hnot
              exact BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg (2 * x) q
      _ ≤ _ := hdist (2 * x) (by omega)
  have hmoment := test_oddPrimeMoment_twentieth_le hN1 (hdiag N hNdiag) (2 * x)
  have hmarkov2 := test_oddPrimeBad_card_mul_le_moment hε.le N (2 * x)
  have hbadsub : test_oddPrimeBad ε N x ⊆ test_oddPrimeBad ε N (2 * x) := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by
          have := Finset.mem_range.mp hpData.1
          omega), hpData.2⟩
  have hcard : ((test_oddPrimeBad ε N x).card : ℝ) ≤
      ((test_oddPrimeBad ε N (2 * x)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hbadsub
  have hmarkov : ((test_oddPrimeBad ε N x).card : ℝ) *
      (ε * (N : ℝ)) ^ 20 ≤ test_oddPrimeMoment 10 N (2 * x) :=
    (mul_le_mul_of_nonneg_right hcard (by positivity)).trans hmarkov2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN1)
  have hden : 0 < (ε * (N : ℝ)) ^ 20 := pow_pos (mul_pos hε hNpos) 20
  calc
    ((test_oddPrimeBad ε N x).card : ℝ) ≤
        test_oddPrimeMoment 10 N (2 * x) / (ε * (N : ℝ)) ^ 20 :=
      (le_div_iff₀ hden).2 hmarkov
    _ ≤ ((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) * (N : ℝ) ^ 17 +
        4 * (N : ℝ) ^ 40 *
          (∑ q ∈ Finset.Icc 1 (4 * N ^ 20),
            BoundedGaps.Maynard.maxProgressionDiscrepancy (2 * x) q)) /
          (ε * (N : ℝ)) ^ 20 := by
      exact div_le_div_of_nonneg_right hmoment hden.le
    _ ≤ ((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) * (N : ℝ) ^ 17 +
        4 * (N : ℝ) ^ 40 *
          (C * ((2 * x : ℕ) : ℝ) /
            Real.rpow (Real.log ((2 * x : ℕ) : ℝ)) 100)) /
          (ε * (N : ℝ)) ^ 20 := by
      have hcoeff : (0 : ℝ) ≤ 4 * (N : ℝ) ^ 40 := by positivity
      exact div_le_div_of_nonneg_right
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hE hcoeff)) hden.le
    _ = (ε ^ 20)⁻¹ *
        ((BoundedGaps.Maynard.primeCountTotal (2 * x) : ℝ) / (N : ℝ) ^ 3 +
          4 * C * ((2 * x : ℕ) : ℝ) * (N : ℝ) ^ 20 /
            Real.rpow (Real.log ((2 * x : ℕ) : ℝ)) 100) := by
      have hx2pos : (0 : ℝ) < (2 * x : ℕ) := by positivity
      have hlogpos : 0 < Real.log ((2 * x : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < 2 * x))
      have hrpowpos : 0 < Real.rpow (Real.log ((2 * x : ℕ) : ℝ)) 100 :=
        Real.rpow_pos_of_pos hlogpos _
      field_simp [hε.ne', hNpos.ne', hrpowpos.ne']

end Erdos981
