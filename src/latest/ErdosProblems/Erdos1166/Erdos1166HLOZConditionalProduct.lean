/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZUrn
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.Pi
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
Finite conditional-product and negative-binomial identities used in the
Hao--Li--Okada--Zheng argument for planar favorite sites.
-/

open scoped BigOperators ENNReal

namespace Erdos1166.HLOZConditionalProduct

open Finset

section ConditionalProduct

variable {β : Type*} [Fintype β]
variable {X : β → Type*}

/-- The product event obtained by imposing one constraint on each block. -/
def blockEvent (E : ∀ b, Finset (X b)) : Set (∀ b, X b) :=
  {x | ∀ b, x b ∈ E b}

/-- Under a product singleton-mass law, the indicator of a product event is the
product of the coordinate indicators. -/
theorem indicator_blockEvent_eq_prod
    (μ : PMF (∀ b, X b)) (μb : ∀ b, PMF (X b))
    (hprod : ∀ x, μ x = ∏ b, μb b (x b))
    (E : ∀ b, Finset (X b)) (x : ∀ b, X b) :
    (blockEvent E).indicator μ x =
      ∏ b, (E b : Set (X b)).indicator (μb b) (x b) := by
  classical
  by_cases hx : ∀ b, x b ∈ E b
  · rw [Set.indicator_of_mem (show x ∈ blockEvent E from hx)]
    rw [hprod x]
    apply Finset.prod_congr rfl
    intro b _hb
    exact (Set.indicator_of_mem (show x b ∈ (E b : Set _) from hx b) (μb b)).symm
  · rw [Set.indicator_of_notMem (show x ∉ blockEvent E from hx)]
    push Not at hx
    obtain ⟨b, hb⟩ := hx
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ b)
      (Set.indicator_of_notMem (show x b ∉ (E b : Set _) from hb) (μb b))

/-- The mass of a product event under a finite product singleton-mass law is
the product of the coordinate event masses. -/
theorem blockEvent_mass_eq_prod
    (μ : PMF (∀ b, X b)) (μb : ∀ b, PMF (X b))
    (hprod : ∀ x, μ x = ∏ b, μb b (x b))
    (E : ∀ b, Finset (X b)) :
    ∑' x, (blockEvent E).indicator μ x =
      ∏ b, ∑' y, (E b : Set (X b)).indicator (μb b) y := by
  classical
  calc
    ∑' x, (blockEvent E).indicator μ x =
        ∑ x ∈ Fintype.piFinset E, (blockEvent E).indicator μ x := by
      apply tsum_eq_sum
      intro x hx
      apply Set.indicator_of_notMem
      intro hmem
      exact hx (Fintype.mem_piFinset.mpr hmem)
    _ = ∑ x ∈ Fintype.piFinset E,
          ∏ b, (E b : Set (X b)).indicator (μb b) (x b) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact indicator_blockEvent_eq_prod μ μb hprod E x
    _ = ∏ b, ∑ y ∈ E b, (E b : Set (X b)).indicator (μb b) y := by
      exact (Finset.prod_univ_sum E fun b y ↦
        (E b : Set (X b)).indicator (μb b) y).symm
    _ = ∏ b, ∑' y, (E b : Set (X b)).indicator (μb b) y := by
      apply Finset.prod_congr rfl
      intro b _hb
      symm
      apply tsum_eq_sum
      intro y hy
      exact Set.indicator_of_notMem (show y ∉ (E b : Set _) from hy) (μb b)

/-- Positivity of every coordinate event implies positivity of the corresponding
product event under a product singleton-mass law. -/
theorem blockEvent_meets_support
    (μ : PMF (∀ b, X b)) (μb : ∀ b, PMF (X b))
    (hprod : ∀ x, μ x = ∏ b, μb b (x b))
    (E : ∀ b, Finset (X b))
    (hE : ∀ b, ∃ y ∈ (E b : Set (X b)), y ∈ (μb b).support) :
    ∃ x ∈ blockEvent E, x ∈ μ.support := by
  classical
  choose x hxE hxSupport using hE
  refine ⟨x, hxE, ?_⟩
  rw [PMF.mem_support_iff, hprod x, Finset.prod_ne_zero_iff]
  intro b _hb
  exact (PMF.mem_support_iff (μb b) (x b)).mp (hxSupport b)

/-- For finitely many independent blocks, conditioning on one event in each
block preserves the product law. This is the finite conditional-product step
used at the end of HLOZ Proposition 4.3. -/
theorem filter_blockEvent_apply_eq_prod
    (μ : PMF (∀ b, X b)) (μb : ∀ b, PMF (X b))
    (hprod : ∀ x, μ x = ∏ b, μb b (x b))
    (E : ∀ b, Finset (X b))
    (hE : ∀ b, ∃ y ∈ (E b : Set (X b)), y ∈ (μb b).support)
    (x : ∀ b, X b) :
    (μ.filter (blockEvent E) (blockEvent_meets_support μ μb hprod E hE)) x =
      ∏ b, ((μb b).filter (E b : Set (X b)) (hE b)) (x b) := by
  classical
  simp only [PMF.filter_apply, ← div_eq_mul_inv]
  rw [indicator_blockEvent_eq_prod μ μb hprod E x]
  rw [blockEvent_mass_eq_prod μ μb hprod E]
  rw [ENNReal.prod_div_distrib_of_ne_top]
  intro b _hb
  exact (μb b).tsum_coe_indicator_ne_top (E b : Set (X b))

end ConditionalProduct

section GeometricBlock

variable {ι : Type*} [DecidableEq ι]

/-- The finite fiber of vectors of natural numbers whose coordinate sum is
`n`, represented via finitely-supported functions. -/
noncomputable def natSumFiber [Fintype ι] (n : ℕ) : Finset (ι → ℕ) :=
  (Finset.univ.finsuppAntidiag n).map Finsupp.equivFunOnFinite.toEmbedding

@[simp]
theorem mem_natSumFiber_iff [Fintype ι] (x : ι → ℕ) (n : ℕ) :
    x ∈ natSumFiber n ↔ ∑ i, x i = n := by
  classical
  simp [natSumFiber, Finset.mem_finsuppAntidiag]

/-- The total mass at sum `n` of `s.card` independent coordinates having
unnormalized geometric mass `p * q ^ k`. -/
theorem geometric_block_sum_mass (s : Finset ι) (n : ℕ) (p q : ℝ≥0∞) :
    ∑ f ∈ s.finsuppAntidiag n, ∏ i ∈ s, p * q ^ f i =
      ((s.card + n - 1).choose n : ℝ≥0∞) * p ^ s.card * q ^ n := by
  calc
    ∑ f ∈ s.finsuppAntidiag n, ∏ i ∈ s, p * q ^ f i =
        ∑ _f ∈ s.finsuppAntidiag n, p ^ s.card * q ^ n := by
      apply sum_congr rfl
      intro f hf
      have hsum : ∑ i ∈ s, f i = n := (mem_finsuppAntidiag.mp hf).1
      calc
        ∏ i ∈ s, p * q ^ f i =
            (∏ i ∈ s, p) * ∏ i ∈ s, q ^ f i := by
              rw [prod_mul_distrib]
        _ = p ^ s.card * q ^ (∑ i ∈ s, f i) := by
              rw [prod_const, prod_pow_eq_pow_sum]
        _ = p ^ s.card * q ^ n := by rw [hsum]
    _ = ((s.finsuppAntidiag n).card : ℝ≥0∞) * (p ^ s.card * q ^ n) := by
      rw [sum_const, nsmul_eq_mul]
    _ = ((s.card + n - 1).choose n : ℝ≥0∞) * p ^ s.card * q ^ n := by
      have hcard : (s.finsuppAntidiag n).card = (s.card + n - 1).choose n := by
        simpa using card_finsuppAntidiag_nat_eq_choose (s := s) n
      rw [hcard]
      ring

/-- If a PMF has the singleton masses of independent geometric coordinates,
then its coordinate sum has the negative-binomial mass. -/
theorem independent_geometric_sum_mass [Fintype ι]
    (μ : PMF (ι → ℕ)) (p q : ℝ≥0∞)
    (hgeom : ∀ x, μ x = ∏ i, p * q ^ x i) (n : ℕ) :
    ∑ x ∈ natSumFiber n, μ x =
      ((Fintype.card ι + n - 1).choose n : ℝ≥0∞) *
        p ^ Fintype.card ι * q ^ n := by
  classical
  rw [natSumFiber, Finset.sum_map]
  calc
    ∑ f ∈ Finset.univ.finsuppAntidiag n,
        μ (Finsupp.equivFunOnFinite f) =
        ∑ f ∈ Finset.univ.finsuppAntidiag n,
          ∏ i ∈ (Finset.univ : Finset ι), p * q ^ f i := by
      apply Finset.sum_congr rfl
      intro f _hf
      rw [hgeom]
      simp
    _ = ((Fintype.card ι + n - 1).choose n : ℝ≥0∞) *
          p ^ Fintype.card ι * q ^ n := by
      simpa using geometric_block_sum_mass (Finset.univ : Finset ι) n p q

/-- The finite event that the sum of the coordinates is strictly below `T`. -/
noncomputable def natSumBelow [Fintype ι] (T : ℕ) : Finset (ι → ℕ) :=
  (Finset.range T).biUnion natSumFiber

@[simp]
theorem mem_natSumBelow_iff [Fintype ι] (x : ι → ℕ) (T : ℕ) :
    x ∈ natSumBelow T ↔ ∑ i, x i < T := by
  classical
  simp [natSumBelow, mem_natSumFiber_iff]

/-- The mass of the bounded-sum conditioning event is the finite cumulative
negative-binomial mass. -/
theorem independent_geometric_sum_lt_mass [Fintype ι]
    (μ : PMF (ι → ℕ)) (p q : ℝ≥0∞)
    (hgeom : ∀ x, μ x = ∏ i, p * q ^ x i) (T : ℕ) :
    ∑ x ∈ natSumBelow T, μ x =
      ∑ n ∈ Finset.range T,
        ((Fintype.card ι + n - 1).choose n : ℝ≥0∞) *
          p ^ Fintype.card ι * q ^ n := by
  classical
  have hdisjoint : ((Finset.range T : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (natSumFiber : ℕ → Finset (ι → ℕ)) := by
    intro m _hm n _hn hmn
    change Disjoint (natSumFiber m) (natSumFiber n)
    rw [Finset.disjoint_left]
    intro x hxm hxn
    have hm : ∑ i, x i = m := (mem_natSumFiber_iff x m).mp hxm
    have hn : ∑ i, x i = n := (mem_natSumFiber_iff x n).mp hxn
    exact hmn (hm.symm.trans hn)
  rw [natSumBelow, Finset.sum_biUnion hdisjoint]
  apply Finset.sum_congr rfl
  intro n _hn
  exact independent_geometric_sum_mass μ p q hgeom n

/-- Inside a bounded-sum event, the conditioned point mass is the geometric
product mass divided by the cumulative negative-binomial normalizer. -/
theorem filter_natSumBelow_apply [Fintype ι]
    (μ : PMF (ι → ℕ)) (p q : ℝ≥0∞)
    (hgeom : ∀ x, μ x = ∏ i, p * q ^ x i) (T : ℕ)
    (hpos : ∃ x ∈ (natSumBelow (ι := ι) T : Set (ι → ℕ)), x ∈ μ.support)
    (x : ι → ℕ) (hx : ∑ i, x i < T) :
    (μ.filter (natSumBelow (ι := ι) T : Set (ι → ℕ)) hpos) x =
      (∏ i, p * q ^ x i) /
        ∑ n ∈ Finset.range T,
          ((Fintype.card ι + n - 1).choose n : ℝ≥0∞) *
            p ^ Fintype.card ι * q ^ n := by
  classical
  have hxmem : x ∈ natSumBelow (ι := ι) T := (mem_natSumBelow_iff x T).mpr hx
  have hnormalizer :
      ∑' y, (natSumBelow (ι := ι) T : Set (ι → ℕ)).indicator μ y =
        ∑ n ∈ Finset.range T,
          ((Fintype.card ι + n - 1).choose n : ℝ≥0∞) *
            p ^ Fintype.card ι * q ^ n := by
    calc
      ∑' y, (natSumBelow (ι := ι) T : Set (ι → ℕ)).indicator μ y =
          ∑ y ∈ natSumBelow (ι := ι) T,
            (natSumBelow (ι := ι) T : Set (ι → ℕ)).indicator μ y := by
        apply tsum_eq_sum
        intro y hy
        exact Set.indicator_of_notMem
          (show y ∉ (natSumBelow (ι := ι) T : Set (ι → ℕ)) from hy) μ
      _ = ∑ y ∈ natSumBelow (ι := ι) T, μ y := by
        apply Finset.sum_congr rfl
        intro y hy
        exact Set.indicator_of_mem
          (show y ∈ (natSumBelow (ι := ι) T : Set (ι → ℕ)) from hy) μ
      _ = _ := independent_geometric_sum_lt_mass μ p q hgeom T
  rw [PMF.filter_apply,
    Set.indicator_of_mem
      (show x ∈ (natSumBelow (ι := ι) T : Set (ι → ℕ)) from hxmem),
    hgeom x, hnormalizer, div_eq_mul_inv]

/-- The exact HLOZ block mass for geometric success probability `15/16`. -/
theorem hloz_geometric_sum_mass [Fintype ι]
    (μ : PMF (ι → ℕ))
    (hgeom : ∀ x, μ x =
      ∏ i, (15 / 16 : ℝ≥0∞) * (1 / 16 : ℝ≥0∞) ^ x i)
    (n : ℕ) :
    ∑ x ∈ natSumFiber n, μ x =
      ((Fintype.card ι + n - 1).choose n : ℝ≥0∞) *
        (15 / 16 : ℝ≥0∞) ^ Fintype.card ι * (1 / 16 : ℝ≥0∞) ^ n := by
  exact independent_geometric_sum_mass μ (15 / 16) (1 / 16) hgeom n

end GeometricBlock

end HLOZConditionalProduct
end Erdos1166
