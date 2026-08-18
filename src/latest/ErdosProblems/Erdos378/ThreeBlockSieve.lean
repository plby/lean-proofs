/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.FiniteResiduePolynomial

/-!
# A three-block quadratic sieve

The sieve weight is a product of three squared linear forms.  Each block
has independent mean `B`; hence its model mean is a variance divided by
`B²`, of order the reciprocal of the block cardinality.  Expanding the
three factors produces only monomials of degree at most six, so the CRT
endpoint error remains polynomial.
-/

open scoped BigOperators

namespace Erdos378
namespace ThreeBlockSieve

open FiniteResiduePolynomial

noncomputable section

variable {ι : Type*} [DecidableEq ι]

abbrev BlockTerm (G : Finset ι) := Unit ⊕ (↑G ⊕ (↑G × ↑G))

def blockTermSupport {G : Finset ι} : BlockTerm G → Finset ι
  | Sum.inl _ => ∅
  | Sum.inr (Sum.inl p) => {(p : ι)}
  | Sum.inr (Sum.inr pq) => {(pq.1 : ι), (pq.2 : ι)}

def blockTermCoeff {G : Finset ι} (B : ℝ) : BlockTerm G → ℝ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => -2 / B
  | Sum.inr (Sum.inr _) => 1 / B ^ 2

def blockMass (q : ι → ℕ) (A : ι → Finset ℕ) (G : Finset ι) : ℝ :=
  ∑ p ∈ G, ((A p).card : ℝ) / q p

def blockHitCount (q : ι → ℕ) (A : ι → Finset ℕ)
    (G : Finset ι) (n : ℕ) : ℝ :=
  ∑ p ∈ G, localIndicator q A p n

def blockWeight (q : ι → ℕ) (A : ι → Finset ℕ)
    (G : Finset ι) (n : ℕ) : ℝ :=
  (1 - blockHitCount q A G n / blockMass q A G) ^ 2

lemma indicatorMonomial_empty (q : ι → ℕ) (A : ι → Finset ℕ) (n : ℕ) :
    indicatorMonomial q A ∅ n = 1 := by simp [indicatorMonomial]

lemma densityMonomial_empty (q : ι → ℕ) (A : ι → Finset ℕ) :
    densityMonomial q A ∅ = 1 := by simp [densityMonomial]

lemma indicatorMonomial_singleton (q : ι → ℕ) (A : ι → Finset ℕ)
    (p : ι) (n : ℕ) :
    indicatorMonomial q A {p} n = localIndicator q A p n := by
  simp [indicatorMonomial]

lemma densityMonomial_singleton (q : ι → ℕ) (A : ι → Finset ℕ)
    (p : ι) :
    densityMonomial q A {p} = ((A p).card : ℝ) / q p := by
  simp [densityMonomial]

lemma indicatorMonomial_pair (q : ι → ℕ) (A : ι → Finset ℕ)
    (p r : ι) (n : ℕ) :
    indicatorMonomial q A {p, r} n =
      localIndicator q A p n * localIndicator q A r n := by
  by_cases hpr : p = r
  · subst r
    rw [show ({p, p} : Finset ι) = {p} by simp,
      indicatorMonomial_singleton]
    simpa only [pow_two] using (localIndicator_sq q A p n).symm
  · simp [indicatorMonomial, hpr]

lemma densityMonomial_pair (q : ι → ℕ) (A : ι → Finset ℕ)
    (p r : ι) :
    densityMonomial q A {p, r} =
      if p = r then ((A p).card : ℝ) / q p
      else (((A p).card : ℝ) / q p) * (((A r).card : ℝ) / q r) := by
  by_cases hpr : p = r
  · subst r
    simp [densityMonomial]
  · simp [densityMonomial, hpr]
    ring

lemma sum_blockTerm_indicator
    (q : ι → ℕ) (A : ι → Finset ℕ) (G : Finset ι)
    (B : ℝ) (n : ℕ) :
    (∑ t : BlockTerm G,
      blockTermCoeff B t * indicatorMonomial q A (blockTermSupport t) n) =
      (1 - blockHitCount q A G n / B) ^ 2 := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [blockTermCoeff, blockTermSupport, indicatorMonomial_empty,
    indicatorMonomial_singleton, Finset.univ_unique, Finset.sum_singleton]
  rw [Fintype.sum_prod_type]
  simp_rw [indicatorMonomial_pair]
  have hsingle :
      (∑ p : ↑G, -2 / B * localIndicator q A (p : ι) n) =
        ∑ p ∈ G, -2 / B * localIndicator q A p n :=
    Finset.sum_coe_sort G
      (fun p : ι ↦ -2 / B * localIndicator q A p n)
  have hdouble :
      (∑ p : ↑G, ∑ r : ↑G,
        1 / B ^ 2 *
          (localIndicator q A (p : ι) n * localIndicator q A (r : ι) n)) =
        ∑ p ∈ G, ∑ r ∈ G,
          1 / B ^ 2 *
            (localIndicator q A p n * localIndicator q A r n) := by
    calc
      _ = ∑ p ∈ G, ∑ r : ↑G,
          1 / B ^ 2 *
            (localIndicator q A p n * localIndicator q A (r : ι) n) :=
        Finset.sum_coe_sort G
          (fun p : ι ↦ ∑ r : ↑G,
            1 / B ^ 2 *
              (localIndicator q A p n * localIndicator q A (r : ι) n))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        exact Finset.sum_coe_sort G
          (fun r : ι ↦ 1 / B ^ 2 *
            (localIndicator q A p n * localIndicator q A r n))
  rw [hsingle, hdouble]
  unfold blockHitCount
  have hpairs :
      (∑ p ∈ G, ∑ r ∈ G,
        1 / B ^ 2 *
          (localIndicator q A p n * localIndicator q A r n)) =
        1 / B ^ 2 *
          (∑ p ∈ G, localIndicator q A p n) ^ 2 := by
    rw [pow_two]
    calc
      _ = ∑ p ∈ G, (1 / B ^ 2 * localIndicator q A p n) *
          (∑ r ∈ G, localIndicator q A r n) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      _ = (∑ p ∈ G, 1 / B ^ 2 * localIndicator q A p n) *
          (∑ r ∈ G, localIndicator q A r n) := by rw [Finset.sum_mul]
      _ = _ := by
        have hc : (∑ p ∈ G, 1 / B ^ 2 * localIndicator q A p n) =
            1 / B ^ 2 * (∑ p ∈ G, localIndicator q A p n) := by
          rw [Finset.mul_sum]
        rw [hc]
        rw [pow_two]
        ring
  rw [hpairs]
  have hlinear :
      (∑ p ∈ G, -2 / B * localIndicator q A p n) =
        -2 / B * (∑ p ∈ G, localIndicator q A p n) := by
    rw [Finset.mul_sum]
  rw [hlinear]
  ring

def blockVariance (q : ι → ℕ) (A : ι → Finset ℕ) (G : Finset ι) : ℝ :=
  ∑ p ∈ G,
    (((A p).card : ℝ) / q p) * (1 - ((A p).card : ℝ) / q p)

lemma sum_blockTerm_density
    (q : ι → ℕ) (A : ι → Finset ℕ) (G : Finset ι)
    (B : ℝ) (hB : B = blockMass q A G) (hB0 : B ≠ 0) :
    (∑ t : BlockTerm G,
      blockTermCoeff B t * densityMonomial q A (blockTermSupport t)) =
      blockVariance q A G / B ^ 2 := by
  let b : ι → ℝ := fun p ↦ ((A p).card : ℝ) / q p
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [blockTermCoeff, blockTermSupport, densityMonomial_empty,
    densityMonomial_singleton, Finset.univ_unique, Finset.sum_singleton]
  rw [Fintype.sum_prod_type]
  simp_rw [densityMonomial_pair]
  have hsingle :
      (∑ p : ↑G, -2 / B * (((A (p : ι)).card : ℝ) / q p)) =
        ∑ p ∈ G, -2 / B * (((A p).card : ℝ) / q p) :=
    Finset.sum_coe_sort G
      (fun p : ι ↦ -2 / B * (((A p).card : ℝ) / q p))
  have hdouble :
      (∑ p : ↑G, ∑ r : ↑G,
        1 / B ^ 2 *
          (if (p : ι) = (r : ι) then ((A p).card : ℝ) / q p
          else (((A p).card : ℝ) / q p) * (((A r).card : ℝ) / q r))) =
        ∑ p ∈ G, ∑ r ∈ G,
          1 / B ^ 2 *
            (if p = r then ((A p).card : ℝ) / q p
            else (((A p).card : ℝ) / q p) * (((A r).card : ℝ) / q r)) := by
    calc
      _ = ∑ p ∈ G, ∑ r : ↑G,
          1 / B ^ 2 *
            (if p = (r : ι) then ((A p).card : ℝ) / q p
            else (((A p).card : ℝ) / q p) *
              (((A (r : ι)).card : ℝ) / q r)) :=
        Finset.sum_coe_sort G
          (fun p : ι ↦ ∑ r : ↑G,
            1 / B ^ 2 *
              (if p = (r : ι) then ((A p).card : ℝ) / q p
              else (((A p).card : ℝ) / q p) *
                (((A (r : ι)).card : ℝ) / q r)))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro p hp
        exact Finset.sum_coe_sort G
          (fun r : ι ↦ 1 / B ^ 2 *
            (if p = r then ((A p).card : ℝ) / q p
            else (((A p).card : ℝ) / q p) * (((A r).card : ℝ) / q r)))
  rw [hsingle, hdouble]
  have hdiag :
      (∑ p ∈ G, ∑ r ∈ G,
        1 / B ^ 2 * (if p = r then b p else b p * b r)) =
      1 / B ^ 2 *
        ((∑ p ∈ G, b p) ^ 2 + ∑ p ∈ G, b p * (1 - b p)) := by
    have hpair :
        (∑ p ∈ G, ∑ r ∈ G, if p = r then b p else b p * b r) =
          (∑ p ∈ G, b p) ^ 2 + ∑ p ∈ G, b p * (1 - b p) := by
      calc
        _ = ∑ p ∈ G, (b p + ∑ r ∈ G.erase p, b p * b r) := by
          apply Finset.sum_congr rfl
          intro p hp
          calc
            (∑ r ∈ G, if p = r then b p else b p * b r) =
                (if p = p then b p else b p * b p) +
                  ∑ r ∈ G.erase p,
                    (if p = r then b p else b p * b r) := by
              exact (Finset.add_sum_erase G _ hp).symm
            _ = b p + ∑ r ∈ G.erase p, b p * b r := by
              simp only [if_pos]
              congr 1
              apply Finset.sum_congr rfl
              intro r hr
              rw [if_neg]
              exact fun h ↦ (Finset.mem_erase.mp hr).1 h.symm
        _ = (∑ p ∈ G, b p) ^ 2 + ∑ p ∈ G, b p * (1 - b p) := by
          rw [Finset.sum_add_distrib]
          have hoff :
              (∑ p ∈ G, ∑ r ∈ G.erase p, b p * b r) =
                (∑ p ∈ G, b p) ^ 2 - ∑ p ∈ G, b p ^ 2 := by
            rw [pow_two, Finset.sum_mul]
            apply eq_sub_iff_add_eq.mpr
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro p hp
            rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ hp]
            ring
          rw [hoff]
          have hv :
              (∑ p ∈ G, b p * (1 - b p)) =
                (∑ p ∈ G, b p) - ∑ p ∈ G, b p ^ 2 := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro p hp
            ring
          rw [hv]
          ring
    have hc :
        (∑ p ∈ G, ∑ r ∈ G,
          1 / B ^ 2 * (if p = r then b p else b p * b r)) =
          1 / B ^ 2 *
            (∑ p ∈ G, ∑ r ∈ G,
              if p = r then b p else b p * b r) := by
      symm
      calc
        _ = ∑ p ∈ G, 1 / B ^ 2 *
            (∑ r ∈ G, if p = r then b p else b p * b r) := by
          rw [Finset.mul_sum]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.mul_sum]
    rw [hc, hpair]
  have hmass : (∑ p ∈ G, b p) = B := by
    rw [hB]
    rfl
  have hlinear :
      (∑ p ∈ G, -2 / B * b p) = -2 / B * B := by
    calc
      _ = -2 / B * (∑ p ∈ G, b p) :=
        (Finset.mul_sum G (fun p ↦ b p) (-2 / B)).symm
      _ = _ := by rw [hmass]
  change 1 * 1 + ((∑ p ∈ G, -2 / B * b p) +
      (∑ p ∈ G, ∑ r ∈ G,
        1 / B ^ 2 * (if p = r then b p else b p * b r))) = _
  rw [hlinear, hdiag, hmass]
  unfold blockVariance
  dsimp only [b]
  field_simp [hB0]
  ring

lemma blockVariance_nonneg
    (q : ι → ℕ) (A : ι → Finset ℕ) (G : Finset ι)
    (hAq : ∀ p ∈ G, (A p).card ≤ q p) :
    0 ≤ blockVariance q A G := by
  unfold blockVariance
  apply Finset.sum_nonneg
  intro p hp
  have hq0 : (0 : ℝ) ≤ q p := by positivity
  have hb0 : 0 ≤ ((A p).card : ℝ) / q p := by positivity
  have hb1 : ((A p).card : ℝ) / q p ≤ 1 := by
    by_cases hq : q p = 0
    · simp [hq]
    · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hq)).mpr
        (by exact_mod_cast hAq p hp)
  positivity

lemma blockVariance_le_card
    (q : ι → ℕ) (A : ι → Finset ℕ) (G : Finset ι)
    (hAq : ∀ p ∈ G, (A p).card ≤ q p) :
    blockVariance q A G ≤ G.card := by
  unfold blockVariance
  calc
    _ ≤ ∑ _p ∈ G, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hb0 : 0 ≤ ((A p).card : ℝ) / q p := by positivity
      have hb1 : ((A p).card : ℝ) / q p ≤ 1 := by
        by_cases hq : q p = 0
        · simp [hq]
        · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hq)).mpr
            (by exact_mod_cast hAq p hp)
      nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hb1)]
    _ = G.card := by simp

/-! ## Three independent blocks -/

abbrev TripleTerm (G₀ G₁ G₂ : Finset ι) :=
  BlockTerm G₀ × (BlockTerm G₁ × BlockTerm G₂)

def tripleTermSupport {G₀ G₁ G₂ : Finset ι}
    (t : TripleTerm G₀ G₁ G₂) : Finset ι :=
  blockTermSupport t.1 ∪ blockTermSupport t.2.1 ∪ blockTermSupport t.2.2

def tripleTermCoeff {G₀ G₁ G₂ : Finset ι}
    (B₀ B₁ B₂ : ℝ) (t : TripleTerm G₀ G₁ G₂) : ℝ :=
  blockTermCoeff B₀ t.1 * blockTermCoeff B₁ t.2.1 * blockTermCoeff B₂ t.2.2

lemma blockTermSupport_subset {G : Finset ι} (t : BlockTerm G) :
    blockTermSupport t ⊆ G := by
  rcases t with _ | p | pq
  · simp [blockTermSupport]
  · simp [blockTermSupport]
  · intro x hx
    simp only [blockTermSupport, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact pq.1.property
    · exact pq.2.property

lemma indicatorMonomial_union (q : ι → ℕ) (A : ι → Finset ℕ)
    (S T : Finset ι) (hST : Disjoint S T) (n : ℕ) :
    indicatorMonomial q A (S ∪ T) n =
      indicatorMonomial q A S n * indicatorMonomial q A T n := by
  simp only [indicatorMonomial]
  rw [Finset.prod_union hST]

lemma densityMonomial_union (q : ι → ℕ) (A : ι → Finset ℕ)
    (S T : Finset ι) (hST : Disjoint S T) :
    densityMonomial q A (S ∪ T) =
      densityMonomial q A S * densityMonomial q A T := by
  simp only [densityMonomial]
  rw [Finset.prod_union hST]

lemma tripleTerm_indicator_factor
    (q : ι → ℕ) (A : ι → Finset ℕ)
    (G₀ G₁ G₂ : Finset ι)
    (h₀₁ : Disjoint G₀ G₁) (h₀₂ : Disjoint G₀ G₂)
    (h₁₂ : Disjoint G₁ G₂) (t : TripleTerm G₀ G₁ G₂) (n : ℕ) :
    indicatorMonomial q A (tripleTermSupport t) n =
      indicatorMonomial q A (blockTermSupport t.1) n *
        indicatorMonomial q A (blockTermSupport t.2.1) n *
          indicatorMonomial q A (blockTermSupport t.2.2) n := by
  have hs₀₁ : Disjoint (blockTermSupport t.1) (blockTermSupport t.2.1) :=
    h₀₁.mono (blockTermSupport_subset _) (blockTermSupport_subset _)
  have hs₀₂ : Disjoint (blockTermSupport t.1) (blockTermSupport t.2.2) :=
    h₀₂.mono (blockTermSupport_subset _) (blockTermSupport_subset _)
  have hs₁₂ : Disjoint (blockTermSupport t.2.1) (blockTermSupport t.2.2) :=
    h₁₂.mono (blockTermSupport_subset _) (blockTermSupport_subset _)
  unfold tripleTermSupport
  rw [indicatorMonomial_union q A _ _
      (Finset.disjoint_union_left.mpr ⟨hs₀₂, hs₁₂⟩),
    indicatorMonomial_union q A _ _ hs₀₁]

lemma tripleTerm_density_factor
    (q : ι → ℕ) (A : ι → Finset ℕ)
    (G₀ G₁ G₂ : Finset ι)
    (h₀₁ : Disjoint G₀ G₁) (h₀₂ : Disjoint G₀ G₂)
    (h₁₂ : Disjoint G₁ G₂) (t : TripleTerm G₀ G₁ G₂) :
    densityMonomial q A (tripleTermSupport t) =
      densityMonomial q A (blockTermSupport t.1) *
        densityMonomial q A (blockTermSupport t.2.1) *
          densityMonomial q A (blockTermSupport t.2.2) := by
  have hs₀₁ : Disjoint (blockTermSupport t.1) (blockTermSupport t.2.1) :=
    h₀₁.mono (blockTermSupport_subset _) (blockTermSupport_subset _)
  have hs₀₂ : Disjoint (blockTermSupport t.1) (blockTermSupport t.2.2) :=
    h₀₂.mono (blockTermSupport_subset _) (blockTermSupport_subset _)
  have hs₁₂ : Disjoint (blockTermSupport t.2.1) (blockTermSupport t.2.2) :=
    h₁₂.mono (blockTermSupport_subset _) (blockTermSupport_subset _)
  unfold tripleTermSupport
  rw [densityMonomial_union q A _ _
      (Finset.disjoint_union_left.mpr ⟨hs₀₂, hs₁₂⟩),
    densityMonomial_union q A _ _ hs₀₁]

lemma sum_triple_product {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → ℝ) (g : β → ℝ) (h : γ → ℝ) :
    (∑ t : α × (β × γ), f t.1 * g t.2.1 * h t.2.2) =
      (∑ a, f a) * (∑ b, g b) * (∑ c, h c) := by
  rw [Fintype.sum_prod_type]
  have hinner :
      (∑ t : β × γ, g t.1 * h t.2) = (∑ b, g b) * (∑ c, h c) := by
    rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]
  calc
    (∑ a, ∑ t : β × γ, f a * g t.1 * h t.2) =
        ∑ a, ∑ t : β × γ, f a * (g t.1 * h t.2) := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro t _ht
      ring
    _ = ∑ a, f a * (∑ t : β × γ, g t.1 * h t.2) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
    _ = (∑ a, f a) * ((∑ b, g b) * (∑ c, h c)) := by
      rw [hinner]
      exact (Finset.sum_mul Finset.univ f _).symm
    _ = _ := by ring

lemma sum_tripleTerm_indicator
    (q : ι → ℕ) (A : ι → Finset ℕ)
    (G₀ G₁ G₂ : Finset ι) (B₀ B₁ B₂ : ℝ)
    (h₀₁ : Disjoint G₀ G₁) (h₀₂ : Disjoint G₀ G₂)
    (h₁₂ : Disjoint G₁ G₂) (n : ℕ) :
    (∑ t : TripleTerm G₀ G₁ G₂,
      tripleTermCoeff B₀ B₁ B₂ t *
        indicatorMonomial q A (tripleTermSupport t) n) =
      (1 - blockHitCount q A G₀ n / B₀) ^ 2 *
        (1 - blockHitCount q A G₁ n / B₁) ^ 2 *
          (1 - blockHitCount q A G₂ n / B₂) ^ 2 := by
  let f₀ : BlockTerm G₀ → ℝ := fun t ↦
    blockTermCoeff B₀ t * indicatorMonomial q A (blockTermSupport t) n
  let f₁ : BlockTerm G₁ → ℝ := fun t ↦
    blockTermCoeff B₁ t * indicatorMonomial q A (blockTermSupport t) n
  let f₂ : BlockTerm G₂ → ℝ := fun t ↦
    blockTermCoeff B₂ t * indicatorMonomial q A (blockTermSupport t) n
  calc
    _ = ∑ t : TripleTerm G₀ G₁ G₂, f₀ t.1 * f₁ t.2.1 * f₂ t.2.2 := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [tripleTerm_indicator_factor q A G₀ G₁ G₂ h₀₁ h₀₂ h₁₂]
      simp only [tripleTermCoeff, f₀, f₁, f₂]
      ring
    _ = (∑ t : BlockTerm G₀, f₀ t) *
        (∑ t : BlockTerm G₁, f₁ t) * (∑ t : BlockTerm G₂, f₂ t) :=
      sum_triple_product f₀ f₁ f₂
    _ = _ := by
      simp only [f₀, f₁, f₂]
      rw [sum_blockTerm_indicator, sum_blockTerm_indicator,
        sum_blockTerm_indicator]

lemma sum_tripleTerm_density
    (q : ι → ℕ) (A : ι → Finset ℕ)
    (G₀ G₁ G₂ : Finset ι) (B₀ B₁ B₂ : ℝ)
    (h₀₁ : Disjoint G₀ G₁) (h₀₂ : Disjoint G₀ G₂)
    (h₁₂ : Disjoint G₁ G₂)
    (hB₀ : B₀ = blockMass q A G₀) (hB₁ : B₁ = blockMass q A G₁)
    (hB₂ : B₂ = blockMass q A G₂)
    (hB₀0 : B₀ ≠ 0) (hB₁0 : B₁ ≠ 0) (hB₂0 : B₂ ≠ 0) :
    (∑ t : TripleTerm G₀ G₁ G₂,
      tripleTermCoeff B₀ B₁ B₂ t *
        densityMonomial q A (tripleTermSupport t)) =
      (blockVariance q A G₀ / B₀ ^ 2) *
        (blockVariance q A G₁ / B₁ ^ 2) *
          (blockVariance q A G₂ / B₂ ^ 2) := by
  let f₀ : BlockTerm G₀ → ℝ := fun t ↦
    blockTermCoeff B₀ t * densityMonomial q A (blockTermSupport t)
  let f₁ : BlockTerm G₁ → ℝ := fun t ↦
    blockTermCoeff B₁ t * densityMonomial q A (blockTermSupport t)
  let f₂ : BlockTerm G₂ → ℝ := fun t ↦
    blockTermCoeff B₂ t * densityMonomial q A (blockTermSupport t)
  calc
    _ = ∑ t : TripleTerm G₀ G₁ G₂, f₀ t.1 * f₁ t.2.1 * f₂ t.2.2 := by
      apply Finset.sum_congr rfl
      intro t _ht
      rw [tripleTerm_density_factor q A G₀ G₁ G₂ h₀₁ h₀₂ h₁₂]
      simp only [tripleTermCoeff, f₀, f₁, f₂]
      ring
    _ = (∑ t : BlockTerm G₀, f₀ t) *
        (∑ t : BlockTerm G₁, f₁ t) * (∑ t : BlockTerm G₂, f₂ t) :=
      sum_triple_product f₀ f₁ f₂
    _ = _ := by
      simp only [f₀, f₁, f₂]
      rw [sum_blockTerm_density q A G₀ B₀ hB₀ hB₀0,
        sum_blockTerm_density q A G₁ B₁ hB₁ hB₁0,
        sum_blockTerm_density q A G₂ B₂ hB₂ hB₂0]

/-! ## Uniform coefficient and support bounds -/

lemma sum_abs_blockTermCoeff (G : Finset ι) (B : ℝ) (hB : 0 < B) :
    (∑ t : BlockTerm G, |blockTermCoeff B t|) =
      1 + (G.card : ℝ) * (2 / B) + (G.card : ℝ) ^ 2 * (1 / B ^ 2) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [blockTermCoeff, Finset.univ_unique, Finset.sum_singleton]
  rw [Fintype.sum_prod_type]
  have hB0 : B ≠ 0 := ne_of_gt hB
  have habsB : |B| = B := abs_of_pos hB
  simp only [abs_one, abs_div, abs_neg, habsB, abs_pow]
  norm_num
  field_simp [hB0]
  ring

lemma sum_abs_blockTermCoeff_le_nine (G : Finset ι) (B : ℝ)
    (hB : 0 < B) (hcard : (G.card : ℝ) ≤ 2 * B) :
    (∑ t : BlockTerm G, |blockTermCoeff B t|) ≤ 9 := by
  rw [sum_abs_blockTermCoeff G B hB]
  have hB0 : 0 ≤ B := le_of_lt hB
  have hlin : (G.card : ℝ) * (2 / B) ≤ 4 := by
    rw [show (G.card : ℝ) * (2 / B) = (2 * G.card) / B by ring]
    exact (div_le_iff₀ hB).mpr (by nlinarith)
  have hquad : (G.card : ℝ) ^ 2 * (1 / B ^ 2) ≤ 4 := by
    rw [show (G.card : ℝ) ^ 2 * (1 / B ^ 2) =
      (G.card : ℝ) ^ 2 / B ^ 2 by ring]
    apply (div_le_iff₀ (sq_pos_of_pos hB)).mpr
    nlinarith [sq_nonneg ((G.card : ℝ) - 2 * B)]
  linarith

lemma sum_abs_tripleTermCoeff_le_729
    (G₀ G₁ G₂ : Finset ι) (B₀ B₁ B₂ : ℝ)
    (hB₀ : 0 < B₀) (hB₁ : 0 < B₁) (hB₂ : 0 < B₂)
    (hcard₀ : (G₀.card : ℝ) ≤ 2 * B₀)
    (hcard₁ : (G₁.card : ℝ) ≤ 2 * B₁)
    (hcard₂ : (G₂.card : ℝ) ≤ 2 * B₂) :
    (∑ t : TripleTerm G₀ G₁ G₂, |tripleTermCoeff B₀ B₁ B₂ t|) ≤ 729 := by
  let f₀ : BlockTerm G₀ → ℝ := fun t ↦ |blockTermCoeff B₀ t|
  let f₁ : BlockTerm G₁ → ℝ := fun t ↦ |blockTermCoeff B₁ t|
  let f₂ : BlockTerm G₂ → ℝ := fun t ↦ |blockTermCoeff B₂ t|
  have hfactor :
      (∑ t : TripleTerm G₀ G₁ G₂, |tripleTermCoeff B₀ B₁ B₂ t|) =
        (∑ t : BlockTerm G₀, f₀ t) *
          (∑ t : BlockTerm G₁, f₁ t) * (∑ t : BlockTerm G₂, f₂ t) := by
    calc
      _ = ∑ t : TripleTerm G₀ G₁ G₂, f₀ t.1 * f₁ t.2.1 * f₂ t.2.2 := by
        apply Finset.sum_congr rfl
        intro t _ht
        simp only [tripleTermCoeff, f₀, f₁, f₂, abs_mul]
      _ = _ := sum_triple_product f₀ f₁ f₂
  rw [hfactor]
  have h₀ := sum_abs_blockTermCoeff_le_nine G₀ B₀ hB₀ hcard₀
  have h₁ := sum_abs_blockTermCoeff_le_nine G₁ B₁ hB₁ hcard₁
  have h₂ := sum_abs_blockTermCoeff_le_nine G₂ B₂ hB₂ hcard₂
  have hn₀ : 0 ≤ ∑ t : BlockTerm G₀, f₀ t := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hn₁ : 0 ≤ ∑ t : BlockTerm G₁, f₁ t := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hn₂ : 0 ≤ ∑ t : BlockTerm G₂, f₂ t := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  dsimp only [f₀, f₁, f₂] at h₀ h₁ h₂ ⊢
  calc
    (∑ t : BlockTerm G₀, |blockTermCoeff B₀ t|) *
          (∑ t : BlockTerm G₁, |blockTermCoeff B₁ t|) *
        (∑ t : BlockTerm G₂, |blockTermCoeff B₂ t|) ≤
        81 * (∑ t : BlockTerm G₂, |blockTermCoeff B₂ t|) := by
      apply mul_le_mul_of_nonneg_right _ hn₂
      nlinarith
    _ ≤ 81 * 9 := mul_le_mul_of_nonneg_left h₂ (by norm_num)
    _ = 729 := by norm_num

lemma triplePolynomial_endpoint_error
    (q : ι → ℕ) (A : ι → Finset ℕ)
    (G₀ G₁ G₂ : Finset ι) (B₀ B₁ B₂ E : ℝ)
    (hB₀ : 0 < B₀) (hB₁ : 0 < B₁) (hB₂ : 0 < B₂)
    (hcard₀ : (G₀.card : ℝ) ≤ 2 * B₀)
    (hcard₁ : (G₁.card : ℝ) ≤ 2 * B₁)
    (hcard₂ : (G₂.card : ℝ) ≤ 2 * B₂)
    (hE : 0 ≤ E)
    (hq : ∀ t : TripleTerm G₀ G₁ G₂,
      ∀ i ∈ tripleTermSupport t, q i ≠ 0)
    (hcop : ∀ t : TripleTerm G₀ G₁ G₂,
      ∀ i ∈ tripleTermSupport t, ∀ j ∈ tripleTermSupport t,
        i ≠ j → Nat.Coprime (q i) (q j))
    (hA : ∀ t : TripleTerm G₀ G₁ G₂,
      ∀ i ∈ tripleTermSupport t, ∀ a ∈ A i, a < q i)
    (hprod : ∀ t : TripleTerm G₀ G₁ G₂,
      (∏ i ∈ tripleTermSupport t, ((A i).card : ℝ)) ≤ E)
    (N : ℕ) :
    |(∑ n ∈ Finset.range N,
          ∑ t : TripleTerm G₀ G₁ G₂,
            tripleTermCoeff B₀ B₁ B₂ t *
              indicatorMonomial q A (tripleTermSupport t) n) -
        (N : ℝ) *
          (∑ t : TripleTerm G₀ G₁ G₂,
            tripleTermCoeff B₀ B₁ B₂ t *
              densityMonomial q A (tripleTermSupport t))| ≤ 729 * E := by
  calc
    _ ≤ ∑ t : TripleTerm G₀ G₁ G₂,
        |tripleTermCoeff B₀ B₁ B₂ t| *
          ∏ i ∈ tripleTermSupport t, (A i).card :=
      abs_sum_polynomial_sub_model q A tripleTermSupport
        (tripleTermCoeff B₀ B₁ B₂) hq hcop hA N
    _ ≤ ∑ t : TripleTerm G₀ G₁ G₂,
        |tripleTermCoeff B₀ B₁ B₂ t| * E := by
      apply Finset.sum_le_sum
      intro t _ht
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      push_cast
      exact hprod t
    _ = E * (∑ t : TripleTerm G₀ G₁ G₂,
        |tripleTermCoeff B₀ B₁ B₂ t|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _ht
      ring
    _ ≤ E * 729 := mul_le_mul_of_nonneg_left
      (sum_abs_tripleTermCoeff_le_729 G₀ G₁ G₂ B₀ B₁ B₂
        hB₀ hB₁ hB₂ hcard₀ hcard₁ hcard₂) hE
    _ = 729 * E := by ring

lemma card_filter_le_triple_model
    (q : ι → ℕ) (A : ι → Finset ℕ)
    (G₀ G₁ G₂ : Finset ι) (B₀ B₁ B₂ E : ℝ)
    (P : ℕ → Prop) [DecidablePred P]
    (hB₀ : 0 < B₀) (hB₁ : 0 < B₁) (hB₂ : 0 < B₂)
    (hcard₀ : (G₀.card : ℝ) ≤ 2 * B₀)
    (hcard₁ : (G₁.card : ℝ) ≤ 2 * B₁)
    (hcard₂ : (G₂.card : ℝ) ≤ 2 * B₂)
    (hE : 0 ≤ E)
    (hq : ∀ t : TripleTerm G₀ G₁ G₂,
      ∀ i ∈ tripleTermSupport t, q i ≠ 0)
    (hcop : ∀ t : TripleTerm G₀ G₁ G₂,
      ∀ i ∈ tripleTermSupport t, ∀ j ∈ tripleTermSupport t,
        i ≠ j → Nat.Coprime (q i) (q j))
    (hA : ∀ t : TripleTerm G₀ G₁ G₂,
      ∀ i ∈ tripleTermSupport t, ∀ a ∈ A i, a < q i)
    (hprod : ∀ t : TripleTerm G₀ G₁ G₂,
      (∏ i ∈ tripleTermSupport t, ((A i).card : ℝ)) ≤ E)
    (N : ℕ)
    (hmajor : ∀ n ∈ Finset.range N,
      (if P n then (1 : ℝ) else 0) ≤
        ∑ t : TripleTerm G₀ G₁ G₂,
          tripleTermCoeff B₀ B₁ B₂ t *
            indicatorMonomial q A (tripleTermSupport t) n) :
    (((Finset.range N).filter P).card : ℝ) ≤
      (N : ℝ) *
        (∑ t : TripleTerm G₀ G₁ G₂,
          tripleTermCoeff B₀ B₁ B₂ t *
            densityMonomial q A (tripleTermSupport t)) + 729 * E := by
  let F : ℕ → ℝ := fun n ↦
    ∑ t : TripleTerm G₀ G₁ G₂,
      tripleTermCoeff B₀ B₁ B₂ t *
        indicatorMonomial q A (tripleTermSupport t) n
  let M : ℝ :=
    ∑ t : TripleTerm G₀ G₁ G₂,
      tripleTermCoeff B₀ B₁ B₂ t *
        densityMonomial q A (tripleTermSupport t)
  have herr : |(∑ n ∈ Finset.range N, F n) - (N : ℝ) * M| ≤ 729 * E := by
    exact triplePolynomial_endpoint_error q A G₀ G₁ G₂ B₀ B₁ B₂ E
      hB₀ hB₁ hB₂ hcard₀ hcard₁ hcard₂ hE hq hcop hA hprod N
  have hsum : (((Finset.range N).filter P).card : ℝ) ≤
      ∑ n ∈ Finset.range N, F n := by
    calc
      (((Finset.range N).filter P).card : ℝ) =
          ∑ n ∈ Finset.range N, if P n then (1 : ℝ) else 0 := by
        rw [Finset.card_eq_sum_ones]
        push_cast
        rw [Finset.sum_filter]
      _ ≤ _ := Finset.sum_le_sum fun n hn ↦ hmajor n hn
  dsimp only [F, M] at herr hsum ⊢
  linarith [le_of_abs_le herr]

lemma blockTermSupport_card_le_two {G : Finset ι} (t : BlockTerm G) :
    (blockTermSupport t).card ≤ 2 := by
  rcases t with _ | p | pq
  · simp [blockTermSupport]
  · simp [blockTermSupport]
  · unfold blockTermSupport
    calc
      ({(pq.1 : ι), (pq.2 : ι)} : Finset ι).card ≤
          ({(pq.2 : ι)} : Finset ι).card + 1 := by
        exact Finset.card_insert_le (pq.1 : ι) {(pq.2 : ι)}
      _ ≤ 2 := by simp

lemma tripleTermSupport_card_le_six {G₀ G₁ G₂ : Finset ι}
    (t : TripleTerm G₀ G₁ G₂) :
    (tripleTermSupport t).card ≤ 6 := by
  have h₀ := blockTermSupport_card_le_two t.1
  have h₁ := blockTermSupport_card_le_two t.2.1
  have h₂ := blockTermSupport_card_le_two t.2.2
  unfold tripleTermSupport
  calc
    ((blockTermSupport t.1 ∪ blockTermSupport t.2.1) ∪
        blockTermSupport t.2.2).card ≤
        (blockTermSupport t.1 ∪ blockTermSupport t.2.1).card +
          (blockTermSupport t.2.2).card :=
      Finset.card_union_le _ _
    _ ≤ ((blockTermSupport t.1).card + (blockTermSupport t.2.1).card) +
          (blockTermSupport t.2.2).card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ 6 := by omega

lemma product_local_cards_le_pow_six
    (A : ι → Finset ℕ) (G₀ G₁ G₂ : Finset ι) (R : ℝ)
    (hR : 1 ≤ R)
    (hcard : ∀ i ∈ G₀ ∪ G₁ ∪ G₂, ((A i).card : ℝ) ≤ R)
    (t : TripleTerm G₀ G₁ G₂) :
    (∏ i ∈ tripleTermSupport t, ((A i).card : ℝ)) ≤ R ^ 6 := by
  have hs : tripleTermSupport t ⊆ G₀ ∪ G₁ ∪ G₂ := by
    intro i hi
    change i ∈ (blockTermSupport t.1 ∪ blockTermSupport t.2.1) ∪
      blockTermSupport t.2.2 at hi
    change i ∈ (G₀ ∪ G₁) ∪ G₂
    rcases Finset.mem_union.mp hi with hi₀₁ | hi₂
    · rcases Finset.mem_union.mp hi₀₁ with hi₀ | hi₁
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr
            (Or.inl (blockTermSupport_subset t.1 hi₀))))
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_union.mpr
            (Or.inr (blockTermSupport_subset t.2.1 hi₁))))
    · exact Finset.mem_union.mpr
        (Or.inr (blockTermSupport_subset t.2.2 hi₂))
  calc
    (∏ i ∈ tripleTermSupport t, ((A i).card : ℝ)) ≤
        ∏ _i ∈ tripleTermSupport t, R := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        exact hcard i (hs hi)
    _ = R ^ (tripleTermSupport t).card := by simp
    _ ≤ R ^ 6 := pow_le_pow_right₀ hR (tripleTermSupport_card_le_six t)

lemma blockVariance_div_sq_le_four_div
    (q : ι → ℕ) (A : ι → Finset ℕ) (G : Finset ι)
    (B T : ℝ) (hAq : ∀ p ∈ G, (A p).card ≤ q p)
    (hB : 0 < B) (hT : 0 < T)
    (hTG : T ≤ (G.card : ℝ)) (hGB : (G.card : ℝ) ≤ 2 * B) :
    blockVariance q A G / B ^ 2 ≤ 4 / T := by
  have hv := blockVariance_le_card q A G hAq
  have hv0 := blockVariance_nonneg q A G hAq
  have hG0 : 0 ≤ (G.card : ℝ) := by positivity
  have hmul : blockVariance q A G * T ≤ (G.card : ℝ) * G.card :=
    mul_le_mul hv hTG (le_of_lt hT) hG0
  have hsq : (G.card : ℝ) * G.card ≤ 4 * B ^ 2 := by
    nlinarith [sq_nonneg ((G.card : ℝ) - 2 * B)]
  exact (div_le_div_iff₀ (sq_pos_of_pos hB) hT).mpr (hmul.trans hsq)

lemma triple_model_le_sixtyfour_div_cube
    (q : ι → ℕ) (A : ι → Finset ℕ)
    (G₀ G₁ G₂ : Finset ι) (B₀ B₁ B₂ T : ℝ)
    (hAq₀ : ∀ p ∈ G₀, (A p).card ≤ q p)
    (hAq₁ : ∀ p ∈ G₁, (A p).card ≤ q p)
    (hAq₂ : ∀ p ∈ G₂, (A p).card ≤ q p)
    (hB₀ : 0 < B₀) (hB₁ : 0 < B₁) (hB₂ : 0 < B₂)
    (hT : 0 < T)
    (hTG₀ : T ≤ (G₀.card : ℝ)) (hTG₁ : T ≤ (G₁.card : ℝ))
    (hTG₂ : T ≤ (G₂.card : ℝ))
    (hG₀B : (G₀.card : ℝ) ≤ 2 * B₀)
    (hG₁B : (G₁.card : ℝ) ≤ 2 * B₁)
    (hG₂B : (G₂.card : ℝ) ≤ 2 * B₂) :
    (blockVariance q A G₀ / B₀ ^ 2) *
        (blockVariance q A G₁ / B₁ ^ 2) *
          (blockVariance q A G₂ / B₂ ^ 2) ≤ 64 / T ^ 3 := by
  have h₀ := blockVariance_div_sq_le_four_div q A G₀ B₀ T
    hAq₀ hB₀ hT hTG₀ hG₀B
  have h₁ := blockVariance_div_sq_le_four_div q A G₁ B₁ T
    hAq₁ hB₁ hT hTG₁ hG₁B
  have h₂ := blockVariance_div_sq_le_four_div q A G₂ B₂ T
    hAq₂ hB₂ hT hTG₂ hG₂B
  have hn₀ : 0 ≤ blockVariance q A G₀ / B₀ ^ 2 :=
    div_nonneg (blockVariance_nonneg q A G₀ hAq₀) (sq_nonneg _)
  have hn₁ : 0 ≤ blockVariance q A G₁ / B₁ ^ 2 :=
    div_nonneg (blockVariance_nonneg q A G₁ hAq₁) (sq_nonneg _)
  have hn₂ : 0 ≤ blockVariance q A G₂ / B₂ ^ 2 :=
    div_nonneg (blockVariance_nonneg q A G₂ hAq₂) (sq_nonneg _)
  have h4T : 0 ≤ 4 / T := by positivity
  calc
    _ ≤ (4 / T) * (4 / T) * (4 / T) := by
      exact mul_le_mul (mul_le_mul h₀ h₁ hn₁ h4T) h₂ hn₂
        (mul_nonneg h4T h4T)
    _ = 64 / T ^ 3 := by field_simp [ne_of_gt hT]; ring

lemma exists_three_pairwise_disjoint_subsets_card_eq
    (P : Finset ι) {t : ℕ} (ht : 3 * t ≤ P.card) :
    ∃ G₀ G₁ G₂ : Finset ι,
      G₀ ⊆ P ∧ G₁ ⊆ P ∧ G₂ ⊆ P ∧
      Disjoint G₀ G₁ ∧ Disjoint G₀ G₂ ∧ Disjoint G₁ G₂ ∧
      G₀.card = t ∧ G₁.card = t ∧ G₂.card = t := by
  obtain ⟨G₀, hG₀P, hG₀card⟩ :=
    Finset.exists_subset_card_eq (show t ≤ P.card by omega)
  let R₁ := P \ G₀
  have hR₁card : R₁.card = P.card - t := by
    dsimp only [R₁]
    rw [Finset.card_sdiff_of_subset hG₀P, hG₀card]
  have htR₁ : t ≤ R₁.card := by omega
  obtain ⟨G₁, hG₁R₁, hG₁card⟩ := Finset.exists_subset_card_eq htR₁
  let R₂ := R₁ \ G₁
  have hR₂card : R₂.card = R₁.card - t := by
    dsimp only [R₂]
    rw [Finset.card_sdiff_of_subset hG₁R₁, hG₁card]
  have htR₂ : t ≤ R₂.card := by omega
  obtain ⟨G₂, hG₂R₂, hG₂card⟩ := Finset.exists_subset_card_eq htR₂
  have hR₁P : R₁ ⊆ P := Finset.sdiff_subset
  have hR₂R₁ : R₂ ⊆ R₁ := Finset.sdiff_subset
  have hG₁P : G₁ ⊆ P := hG₁R₁.trans hR₁P
  have hG₂P : G₂ ⊆ P := hG₂R₂.trans (hR₂R₁.trans hR₁P)
  have h₀R₁ : Disjoint G₀ R₁ := by
    dsimp only [R₁]
    exact Finset.disjoint_sdiff
  have h₀₁ : Disjoint G₀ G₁ := h₀R₁.mono_right hG₁R₁
  have h₀₂ : Disjoint G₀ G₂ :=
    h₀R₁.mono_right (hG₂R₂.trans hR₂R₁)
  have h₁R₂ : Disjoint G₁ R₂ := by
    dsimp only [R₂]
    exact Finset.disjoint_sdiff
  have h₁₂ : Disjoint G₁ G₂ := h₁R₂.mono_right hG₂R₂
  exact ⟨G₀, G₁, G₂, hG₀P, hG₁P, hG₂P,
    h₀₁, h₀₂, h₁₂, hG₀card, hG₁card, hG₂card⟩

end

end ThreeBlockSieve
end Erdos378
