import ErdosProblems.Erdos67b.MRFiniteRamareLargeValues

/-!
# Typical cofactor supports in the finite Ramaré factorization

The typical-set indicator belongs in the cofactor support, with the
selected prime block removed. The original function is never replaced
by an asserted multiplicative restriction to the typical set.
-/

open scoped BigOperators Interval
open Finset

namespace Erdos67b

noncomputable section

/-- Regroup a finite multiplicative convolution by its first factor. -/
theorem finiteProductCoefficient_eq_sum_divisors
    {A B : Finset ℕ} (hA : ∀ p ∈ A, 0 < p)
    (a b : ℕ → ℂ) (n : ℕ) :
    finiteProductCoefficient A B a b n =
      ∑ p ∈ A, if p ∣ n ∧ n / p ∈ B then a p * b (n / p) else 0 := by
  classical
  unfold finiteProductCoefficient natProductFiber
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpn : p ∣ n
  · by_cases hm : n / p ∈ B
    · rw [if_pos ⟨hpn, hm⟩]
      have hprod := Nat.mul_div_cancel' hpn
      apply (Finset.sum_eq_single (n / p) ?_ ?_).trans
      · simp only [hprod, ↓reduceIte]
      · intro m _ hne
        have hmul : p * m ≠ n := by
          intro hmul
          have heq : n / p = m := by rw [← hmul, Nat.mul_div_cancel_left _ (hA p hp)]
          exact hne heq.symm
        simp only [hmul, ↓reduceIte]
      · exact fun hnot ↦ False.elim (hnot hm)
    · rw [if_neg (by simp only [hm, and_false, not_false_eq_true])]
      apply Finset.sum_eq_zero
      intro m hmB
      have hmul : p * m ≠ n := by
        intro hmul
        apply hm
        rwa [← hmul, Nat.mul_div_cancel_left _ (hA p hp)]
      simp only [hmul, ↓reduceIte]
  · rw [if_neg (by simp only [hpn, false_and, not_false_eq_true])]
    apply Finset.sum_eq_zero
    intro m _
    have hmul : p * m ≠ n := fun hh ↦ hpn ⟨m, hh.symm⟩
    simp only [hmul, ↓reduceIte]

/-- The line-one finite convolution coefficient is its arithmetic
Ramaré coefficient divided by the product index. -/
theorem mrFiniteRamareSubblockRectangleCoefficient_eq_div
    {P D S : Finset ℕ} (hD : ∀ p ∈ D, 0 < p)
    (f : ℕ → ℂ) {n : ℕ} (hn : 0 < n) :
    mrFiniteRamareSubblockRectangleCoefficient P D S f n =
      mrRestrictedRamareCoefficient P D S f n / (n : ℂ) := by
  classical
  unfold mrFiniteRamareSubblockRectangleCoefficient mrRestrictedRamareCoefficient
  rw [finiteProductCoefficient_eq_sum_divisors hD, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  split_ifs with hh
  · have hmpos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hh.1) (hD p hp)
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (hD p hp).ne'
    have hm0 : ((n / p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hmpos.ne'
    have hprod : (p : ℂ) * (n / p : ℕ) = n := by exact_mod_cast Nat.mul_div_cancel' hh.1
    unfold mrFinitePrimeLineCoefficient mrFiniteCofactorLineCoefficient
    rw [← hprod]
    field_simp
  · simp

theorem finiteProductCoefficient_eq_zero_of_not_mem
    {A B : Finset ℕ} {a b : ℕ → ℂ} {n : ℕ} (hn : n ∉ natProductImage A B) :
    finiteProductCoefficient A B a b n = 0 := by
  classical
  unfold finiteProductCoefficient
  apply Finset.sum_eq_zero
  intro x hx
  have hxx := mem_natProductFiber.mp hx
  exact False.elim (hn (Finset.mem_image.mpr
    ⟨x, Finset.mem_product.mpr ⟨hxx.1, hxx.2.1⟩, hxx.2.2⟩))

/-- Splitting a finite product into its desired interval and exact
outside boundary requires no infinite-series interchange. -/
theorem logarithmicDirichletPolynomial_mul_eq_interval_add_boundary
    {A B : Finset ℕ} (hA : ∀ p ∈ A, 0 < p) (hB : ∀ m ∈ B, 0 < m)
    (a b : ℕ → ℂ) (W : Finset ℕ) (t : ℝ) :
    logarithmicDirichletPolynomial A a t * logarithmicDirichletPolynomial B b t =
      logarithmicDirichletPolynomial W (finiteProductCoefficient A B a b) t +
        logarithmicDirichletPolynomial (natProductImage A B \ W)
          (finiteProductCoefficient A B a b) t := by
  classical
  rw [logarithmicDirichletPolynomial_mul_eq_product hA hB]
  unfold logarithmicDirichletPolynomial
  have hinter : (∑ n ∈ natProductImage A B ∩ W,
      finiteProductCoefficient A B a b n * logarithmicPhase n t) =
      ∑ n ∈ W, finiteProductCoefficient A B a b n * logarithmicPhase n t := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro n hnW hninter
    have hn : n ∉ natProductImage A B := fun hh ↦ hninter (Finset.mem_inter.mpr ⟨hh, hnW⟩)
    rw [finiteProductCoefficient_eq_zero_of_not_mem hn, zero_mul]
  rw [← hinter]
  exact (Finset.sum_inter_add_sum_sdiff (natProductImage A B) W _).symm

/-- A prime from the selected block supplies that block and cannot supply
any other disjoint prime block. -/
theorem hasTypicalFactorization_prime_mul_iff_erase
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} {p m : ℕ}
    (hp : p ∈ primesInBlock I)
    (hdisj : ∀ J ∈ blocks, J ≠ I → Disjoint (primesInBlock I) (primesInBlock J)) :
    HasTypicalFactorization blocks (p * m) ↔
      HasTypicalFactorization (blocks.erase I) m := by
  classical
  have hpprime := (mem_primesInBlock.mp hp).1
  constructor
  · intro h J hJ
    obtain ⟨hJI, hJB⟩ := Finset.mem_erase.mp hJ
    obtain ⟨q, hq, hqdiv⟩ := h J hJB
    have hqprime := (mem_primesInBlock.mp hq).1
    rcases hqprime.dvd_mul.mp hqdiv with hqp | hqm
    · have hqpEq : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hpprime).mp hqp
      subst q
      exact False.elim (Finset.disjoint_left.mp (hdisj J hJB hJI) hp hq)
    · exact ⟨q, hq, hqm⟩
  · intro h J hJ
    by_cases hJI : J = I
    · subst J
      exact ⟨p, hp, dvd_mul_right p m⟩
    · obtain ⟨q, hq, hqm⟩ := h J (Finset.mem_erase.mpr ⟨hJI, hJ⟩)
      exact ⟨q, hq, dvd_mul_of_dvd_right hqm p⟩

/-- The common rectangle, restricted only by the other prime blocks. -/
def mrTypicalCofactorRectangle
    (blocks : Finset (ℕ × ℕ)) (I J : ℕ × ℕ) (X : ℕ) : Finset ℕ := by
  classical
  exact (mrDyadicCofactorRectangle J X).filter (HasTypicalFactorization (blocks.erase I))

theorem mrTypicalCofactorRectangle_subset
    (blocks : Finset (ℕ × ℕ)) (I J : ℕ × ℕ) (X : ℕ) :
    mrTypicalCofactorRectangle blocks I J X ⊆ mrDyadicCofactorRectangle J X := by
  classical
  exact Finset.filter_subset _ _

theorem mrTypicalCofactorRectangle_pos
    {blocks : Finset (ℕ × ℕ)} {I J : ℕ × ℕ} {X m : ℕ}
    (hm : m ∈ mrTypicalCofactorRectangle blocks I J X) : 0 < m := by
  have hh := (Finset.mem_Ioc.mp (mrTypicalCofactorRectangle_subset blocks I J X hm)).1
  exact (Nat.zero_le (X / J.2)).trans_lt hh

/-- On the product interval, the quotient belongs to the filtered
rectangle exactly when the product belongs to the full typical set. -/
theorem div_mem_mrTypicalCofactorRectangle_iff
    {blocks : Finset (ℕ × ℕ)} {I J : ℕ × ℕ} {X n p : ℕ}
    (hp : p ∈ primesInBlock I) (hJ : 0 < J.1)
    (hpJ : J.1 ≤ p ∧ p ≤ J.2)
    (hdisj : ∀ K ∈ blocks, K ≠ I → Disjoint (primesInBlock I) (primesInBlock K))
    (hn : n ∈ Finset.Ioc X (2 * X)) (hpn : p ∣ n) :
    n / p ∈ mrTypicalCofactorRectangle blocks I J X ↔
      n ∈ typicalFactorizationSet blocks (2 * X) := by
  classical
  have hrect : n / p ∈ mrDyadicCofactorRectangle J X := by
    apply divisorCofactorImage_Ioc_subset_mrDyadicCofactorRectangle hJ
      (mem_primesInBlock.mpr ⟨(mem_primesInBlock.mp hp).1, hpJ⟩)
    exact mem_divisorCofactorImage.mpr ⟨n, hn, hpn, rfl⟩
  have htyp := hasTypicalFactorization_prime_mul_iff_erase (m := n / p) hp hdisj
  rw [Nat.mul_div_cancel' hpn] at htyp
  have hnB := Finset.mem_Ioc.mp hn
  have hn1 : 1 ≤ n := by omega
  simp only [mrTypicalCofactorRectangle, Finset.mem_filter, hrect, true_and,
    mem_typicalFactorizationSet, hn1, hnB.2, true_and]
  exact htyp.symm

/-- Exact coefficient restriction, for one narrow prime set. -/
theorem mrRestrictedRamareCoefficient_typical_rectangle
    {blocks : Finset (ℕ × ℕ)} {I J : ℕ × ℕ} {D : Finset ℕ}
    (hD : D ⊆ primesInBlock I) (hJ : 0 < J.1)
    (hDJ : ∀ p ∈ D, J.1 ≤ p ∧ p ≤ J.2)
    (hdisj : ∀ K ∈ blocks, K ≠ I → Disjoint (primesInBlock I) (primesInBlock K))
    (f : ℕ → ℂ) {X n : ℕ} (hn : n ∈ Finset.Ioc X (2 * X)) :
    mrRestrictedRamareCoefficient (primesInBlock I) D
        (mrTypicalCofactorRectangle blocks I J X) f n =
      if n ∈ typicalFactorizationSet blocks (2 * X) then
        ∑ p ∈ D, if p ∣ n then
          f p * f (n / p) / (mrCommonDenominator (primesInBlock I) (n / p) : ℂ)
        else 0
      else 0 := by
  classical
  unfold mrRestrictedRamareCoefficient
  by_cases htyp : n ∈ typicalFactorizationSet blocks (2 * X)
  · rw [if_pos htyp]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpn : p ∣ n
    · have hm := (div_mem_mrTypicalCofactorRectangle_iff (hD hp) hJ (hDJ p hp) hdisj hn hpn).mpr htyp
      simp only [hpn, hm, and_self, ↓reduceIte]
    · simp only [hpn, false_and, ↓reduceIte]
  · rw [if_neg htyp]
    apply Finset.sum_eq_zero
    intro p hp
    by_cases hpn : p ∣ n
    · have hm : n / p ∉ mrTypicalCofactorRectangle blocks I J X := by
        intro hm
        exact htyp ((div_mem_mrTypicalCofactorRectangle_iff (hD hp) hJ (hDJ p hp)
          hdisj hn hpn).mp hm)
      simp only [hm, and_false, ↓reduceIte]
    · simp only [hpn, false_and, ↓reduceIte]

/-- Summing a disjoint narrow prime partition gives the original typical
common coefficient, with no boundary error inside the product interval. -/
theorem sum_mrRestrictedRamareCoefficient_typical_rectangle
    {ι : Type*} [DecidableEq ι] {V : Finset ι}
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} {D : ι → Finset ℕ} {J : ι → ℕ × ℕ}
    (hpartition : Set.PairwiseDisjoint (↑V) D) (hcover : V.biUnion D = primesInBlock I)
    (hJ : ∀ v ∈ V, 0 < (J v).1)
    (hDJ : ∀ v ∈ V, ∀ p ∈ D v, (J v).1 ≤ p ∧ p ≤ (J v).2)
    (hdisj : ∀ K ∈ blocks, K ≠ I → Disjoint (primesInBlock I) (primesInBlock K))
    (f : ℕ → ℂ) {X n : ℕ} (hn : n ∈ Finset.Ioc X (2 * X)) :
    (∑ v ∈ V, mrRestrictedRamareCoefficient (primesInBlock I) (D v)
      (mrTypicalCofactorRectangle blocks I (J v) X) f n) =
        mrTypicalCommonCoefficient blocks (2 * X) (primesInBlock I) f n := by
  classical
  have hD (v : ι) (hv : v ∈ V) : D v ⊆ primesInBlock I := by
    rw [← hcover]
    exact Finset.subset_biUnion_of_mem D hv
  rw [show (∑ v ∈ V, mrRestrictedRamareCoefficient (primesInBlock I) (D v)
      (mrTypicalCofactorRectangle blocks I (J v) X) f n) =
      ∑ v ∈ V, if n ∈ typicalFactorizationSet blocks (2 * X) then
        ∑ p ∈ D v, if p ∣ n then
          f p * f (n / p) / (mrCommonDenominator (primesInBlock I) (n / p) : ℂ)
        else 0
      else 0 by
    apply Finset.sum_congr rfl
    intro v hv
    exact mrRestrictedRamareCoefficient_typical_rectangle (hD v hv) (hJ v hv) (hDJ v hv) hdisj f hn]
  unfold mrTypicalCommonCoefficient mrCommonRamareCoefficient
  split_ifs with htyp
  · simpa only [hcover] using
      (Finset.sum_biUnion (f := fun p ↦ if p ∣ n then
        f p * f (n / p) / (mrCommonDenominator (primesInBlock I) (n / p) : ℂ)
        else 0) hpartition).symm
  · simp

/-- Products outside the desired interval, after the typical cofactor
restriction. -/
def mrTypicalRamareBoundarySupport
    (blocks : Finset (ℕ × ℕ)) (I J : ℕ × ℕ) (D : Finset ℕ) (X : ℕ) : Finset ℕ :=
  natProductImage D (mrTypicalCofactorRectangle blocks I J X) \ Finset.Ioc X (2 * X)

def mrTypicalRamareBoundaryPolynomial
    (blocks : Finset (ℕ × ℕ)) (I J : ℕ × ℕ) (D : Finset ℕ)
    (f : ℕ → ℂ) (X : ℕ) (t : ℝ) : ℂ :=
  logarithmicDirichletPolynomial (mrTypicalRamareBoundarySupport blocks I J D X)
    (mrFiniteRamareSubblockRectangleCoefficient (primesInBlock I) D
      (mrTypicalCofactorRectangle blocks I J X) f) t

/-- The typical finite polynomial is exactly the sum of narrow products
minus their outside boundaries. All factors use the same phase sign. -/
theorem mrTypicalCommonPolynomial_eq_products_sub_boundary
    {ι : Type*} [DecidableEq ι] {V : Finset ι}
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} {D : ι → Finset ℕ} {J : ι → ℕ × ℕ}
    (hpartition : Set.PairwiseDisjoint (↑V) D) (hcover : V.biUnion D = primesInBlock I)
    (hJ : ∀ v ∈ V, 0 < (J v).1)
    (hDJ : ∀ v ∈ V, ∀ p ∈ D v, (J v).1 ≤ p ∧ p ≤ (J v).2)
    (hdisj : ∀ K ∈ blocks, K ≠ I → Disjoint (primesInBlock I) (primesInBlock K))
    (f : ℕ → ℂ) (X : ℕ) (t : ℝ) :
    logarithmicDirichletPolynomial (Finset.Ioc X (2 * X))
        (fun n ↦ mrTypicalCommonCoefficient blocks (2 * X) (primesInBlock I) f n / (n : ℂ)) t =
      ∑ v ∈ V,
        (logarithmicDirichletPolynomial (D v) (mrFinitePrimeLineCoefficient f) t *
            logarithmicDirichletPolynomial (mrTypicalCofactorRectangle blocks I (J v) X)
              (mrFiniteCofactorLineCoefficient (primesInBlock I) f) t -
          mrTypicalRamareBoundaryPolynomial blocks I (J v) (D v) f X t) := by
  classical
  let S (v : ι) := mrTypicalCofactorRectangle blocks I (J v) X
  let c (v : ι) := mrFiniteRamareSubblockRectangleCoefficient (primesInBlock I) (D v) (S v) f
  have hDpos (v : ι) (hv : v ∈ V) : ∀ p ∈ D v, 0 < p :=
    fun p hp ↦ (hJ v hv).trans_le (hDJ v hv p hp).1
  have hcoeff (n : ℕ) (hn : n ∈ Finset.Ioc X (2 * X)) :
      (∑ v ∈ V, c v n) =
        mrTypicalCommonCoefficient blocks (2 * X) (primesInBlock I) f n / (n : ℂ) := by
    have hn0 : 0 < n := (Nat.zero_le X).trans_lt (Finset.mem_Ioc.mp hn).1
    calc
      _ = ∑ v ∈ V, mrRestrictedRamareCoefficient (primesInBlock I) (D v) (S v) f n / (n : ℂ) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact mrFiniteRamareSubblockRectangleCoefficient_eq_div (hDpos v hv) f hn0
      _ = (∑ v ∈ V, mrRestrictedRamareCoefficient (primesInBlock I) (D v) (S v) f n) / (n : ℂ) :=
        (Finset.sum_div _ _ _).symm
      _ = _ := by rw [sum_mrRestrictedRamareCoefficient_typical_rectangle
        hpartition hcover hJ hDJ hdisj f hn]
  have hproduct (v : ι) (hv : v ∈ V) :
      logarithmicDirichletPolynomial (D v) (mrFinitePrimeLineCoefficient f) t *
          logarithmicDirichletPolynomial (S v) (mrFiniteCofactorLineCoefficient (primesInBlock I) f) t -
          mrTypicalRamareBoundaryPolynomial blocks I (J v) (D v) f X t =
        logarithmicDirichletPolynomial (Finset.Ioc X (2 * X)) (c v) t := by
    have hh := logarithmicDirichletPolynomial_mul_eq_interval_add_boundary (B := S v) (hDpos v hv)
      (fun m hm ↦ mrTypicalCofactorRectangle_pos hm)
      (mrFinitePrimeLineCoefficient f) (mrFiniteCofactorLineCoefficient (primesInBlock I) f)
      (Finset.Ioc X (2 * X)) t
    change _ = logarithmicDirichletPolynomial (Finset.Ioc X (2 * X)) (c v) t +
      mrTypicalRamareBoundaryPolynomial blocks I (J v) (D v) f X t at hh
    rw [hh, add_sub_cancel_right]
  symm
  calc
    _ = ∑ v ∈ V, logarithmicDirichletPolynomial (Finset.Ioc X (2 * X)) (c v) t :=
      Finset.sum_congr rfl hproduct
    _ = ∑ n ∈ Finset.Ioc X (2 * X), (∑ v ∈ V, c v n) * logarithmicPhase n t := by
      unfold logarithmicDirichletPolynomial
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hcoeff n hn]

/-- Typical filtering cannot enlarge the already controlled endpoint
support of a finite Ramaré rectangle. -/
theorem mrTypicalRamareBoundarySupport_subset
    (blocks : Finset (ℕ × ℕ)) (I J : ℕ × ℕ) (D : Finset ℕ) (X : ℕ) :
    mrTypicalRamareBoundarySupport blocks I J D X ⊆
      mrFiniteRamareSubblockBoundaryProductSupport D J X := by
  classical
  intro n hn
  obtain ⟨hnprod, hnout⟩ := Finset.mem_sdiff.mp hn
  obtain ⟨⟨p, m⟩, hpm, hprod⟩ := Finset.mem_image.mp hnprod
  obtain ⟨hp, hm⟩ := Finset.mem_product.mp hpm
  apply Finset.mem_image.mpr
  refine ⟨(p, m), Finset.mem_filter.mpr ⟨?_, ?_⟩, hprod⟩
  · exact Finset.mem_product.mpr ⟨hp, mrTypicalCofactorRectangle_subset blocks I J X hm⟩
  · simpa only [hprod] using hnout

/-- The endpoint energy estimate applies to any supported coefficients
bounded by `1/n`, hence remains valid after typical cofactor filtering. -/
theorem intervalIntegral_norm_sq_le_ramareBoundary
    {A D : Finset ℕ} {J : ℕ × ℕ} {X : ℕ}
    (hA : A ⊆ mrFiniteRamareSubblockBoundaryProductSupport D J X)
    (hlo : 0 < J.1) (hJle : J.1 ≤ J.2) (hJX : J.1 ≤ X)
    (hD : ∀ p ∈ D, J.1 ≤ p ∧ p ≤ J.2)
    {a : ℕ → ℂ} (ha : ∀ n ∈ A, ‖a n‖ ≤ (n : ℝ)⁻¹)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖logarithmicDirichletPolynomial A a t‖ ^ 2) ≤
      mrFiniteRamareSubblockBoundaryEnergyBound J X T := by
  let L : ℕ := J.1 * (X / J.2 + 1)
  let N : ℕ := J.2 * ((2 * X) / J.1)
  let M : ℕ := (Finset.Icc L X).card + (Finset.Ioc (2 * X) N).card
  have hL : 0 < L := Nat.mul_pos hlo (Nat.succ_pos _)
  have hN : 0 < N := by
    apply Nat.mul_pos (hlo.trans_le hJle)
    exact Nat.div_pos (by omega) hlo
  have hbounds (n : ℕ) (hn : n ∈ A) : L ≤ n ∧ n ≤ N :=
    mem_mrFiniteRamareSubblockBoundaryProductSupport_bounds hD (hA hn)
  have hApos (n : ℕ) (hn : n ∈ A) : 0 < n := hL.trans_le (hbounds n hn).1
  have hcard : A.card ≤ M :=
    (Finset.card_le_card hA).trans (card_mrFiniteRamareSubblockBoundaryProductSupport_le hD)
  have hmass : (∑ n ∈ A, Complex.normSq (a n)) ≤ (M : ℝ) * (L : ℝ)⁻¹ ^ 2 := by
    calc
      _ ≤ ∑ _n ∈ A, (L : ℝ)⁻¹ ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        have hLn : (L : ℝ) ≤ n := by exact_mod_cast (hbounds n hn).1
        have hinv : (n : ℝ)⁻¹ ≤ (L : ℝ)⁻¹ := inv_anti₀ (by exact_mod_cast hL) hLn
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ (norm_nonneg _) ((ha n hn).trans hinv) 2
      _ = (A.card : ℝ) * (L : ℝ)⁻¹ ^ 2 := by simp
      _ ≤ (M : ℝ) * (L : ℝ)⁻¹ ^ 2 := by gcongr
  calc
    _ = ‖∫ t in -T..T,
        star (logarithmicDirichletPolynomial A a t) * logarithmicDirichletPolynomial A a t‖ :=
      intervalIntegral_norm_sq_eq_norm_conj_mul_self _ hT
    _ ≤ (2 * T + 2 * Real.pi * (N : ℝ)) * ∑ n ∈ A, Complex.normSq (a n) :=
      norm_logarithmicDirichletPolynomial_intervalIntegral_le_support hN hApos
        (fun n hn ↦ (hbounds n hn).2) a hT
    _ ≤ (2 * T + 2 * Real.pi * (N : ℝ)) * ((M : ℝ) * (L : ℝ)⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by unfold mrFiniteRamareSubblockBoundaryEnergyBound M L N; ring

/-- Typical filtering has exactly the old endpoint energy budget. -/
theorem intervalIntegral_mrTypicalRamareBoundaryPolynomial_le
    (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ) {J : ℕ × ℕ} {D : Finset ℕ} {X : ℕ}
    (hDP : D ⊆ primesInBlock I)
    (hlo : 0 < J.1) (hJle : J.1 ≤ J.2) (hJX : J.1 ≤ X)
    (hD : ∀ p ∈ D, J.1 ≤ p ∧ p ≤ J.2)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖mrTypicalRamareBoundaryPolynomial blocks I J D f X t‖ ^ 2) ≤
      mrFiniteRamareSubblockBoundaryEnergyBound J X T := by
  apply intervalIntegral_norm_sq_le_ramareBoundary
    (mrTypicalRamareBoundarySupport_subset blocks I J D X) hlo hJle hJX hD ?_ hT
  intro n hn
  have hnB := mem_mrFiniteRamareSubblockBoundaryProductSupport_bounds hD
    (mrTypicalRamareBoundarySupport_subset blocks I J D X hn)
  have hn0 : 0 < n := (Nat.mul_pos hlo (Nat.succ_pos _)).trans_le hnB.1
  exact norm_mrFiniteRamareSubblockRectangleCoefficient_le_inv
    (fun p hp ↦ (mem_primesInBlock.mp hp).1) hDP hbound
    (fun m hm ↦ mrTypicalCofactorRectangle_pos hm) hn0

/-- Regrouping a disjoint prime partition retains the common-denominator
unit bound even when every subblock has a different cofactor support. -/
theorem norm_sum_mrRestrictedRamareCoefficient_le_one
    {ι : Type*} {V : Finset ι} {P : Finset ℕ} {D S : ι → Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hD : ∀ v ∈ V, D v ⊆ P)
    (hdisj : Set.PairwiseDisjoint (↑V) D)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    ‖∑ v ∈ V, mrRestrictedRamareCoefficient P (D v) (S v) f n‖ ≤ 1 := by
  classical
  let R (v : ι) := (D v).filter (fun p ↦ n / p ∈ S v)
  let F (p : ℕ) : ℂ := if p ∣ n then
    f p * f (n / p) / (mrCommonDenominator P (n / p) : ℂ) else 0
  have hRdisj : Set.PairwiseDisjoint (↑V) R := by
    intro v hv w hw hne
    exact (hdisj hv hw hne).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hRP : V.biUnion R ⊆ P := by
    intro p hp
    obtain ⟨v, hv, hpR⟩ := Finset.mem_biUnion.mp hp
    exact hD v hv (Finset.mem_filter.mp hpR).1
  have hsingle (v : ι) : mrRestrictedRamareCoefficient P (D v) (S v) f n = ∑ p ∈ R v, F p := by
    unfold mrRestrictedRamareCoefficient R
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only [F]
    by_cases hpn : p ∣ n <;> by_cases hm : n / p ∈ S v <;> simp [hpn, hm]
  have heq : (∑ v ∈ V, mrRestrictedRamareCoefficient P (D v) (S v) f n) =
      mrRestrictedRamareCoefficient P (V.biUnion R) (Finset.Icc 0 n) f n := by
    calc
      _ = ∑ v ∈ V, ∑ p ∈ R v, F p := Finset.sum_congr rfl (fun v _ ↦ hsingle v)
      _ = ∑ p ∈ V.biUnion R, F p := (Finset.sum_biUnion hRdisj).symm
      _ = _ := by
        unfold mrRestrictedRamareCoefficient
        apply Finset.sum_congr rfl
        intro p hp
        have hm : n / p ∈ Finset.Icc 0 n :=
          Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.div_le_self _ _⟩
        simp only [F, hm, and_true]
  rw [heq]
  exact norm_mrRestrictedRamareCoefficient_le_one hP hRP hbound hn

/-- The grouped line-one coefficients have the sharp `1/n` bound,
without a factor for the number of narrow prime blocks. -/
theorem norm_sum_mrFiniteRamareSubblockRectangleCoefficient_le_inv
    {ι : Type*} {V : Finset ι} {P : Finset ℕ} {D S : ι → Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hD : ∀ v ∈ V, D v ⊆ P)
    (hdisj : Set.PairwiseDisjoint (↑V) D)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    ‖∑ v ∈ V, mrFiniteRamareSubblockRectangleCoefficient P (D v) (S v) f n‖ ≤ (n : ℝ)⁻¹ := by
  have heq : (∑ v ∈ V, mrFiniteRamareSubblockRectangleCoefficient P (D v) (S v) f n) =
      (∑ v ∈ V, mrRestrictedRamareCoefficient P (D v) (S v) f n) / (n : ℂ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro v hv
    exact mrFiniteRamareSubblockRectangleCoefficient_eq_div
      (fun p hp ↦ (hP p (hD v hv hp)).pos) f hn
  rw [heq, norm_div, Complex.norm_natCast, div_eq_mul_inv]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (norm_sum_mrRestrictedRamareCoefficient_le_one hP hD hdisj hbound hn) (by positivity : 0 ≤ (n : ℝ)⁻¹)

end

end Erdos67b
