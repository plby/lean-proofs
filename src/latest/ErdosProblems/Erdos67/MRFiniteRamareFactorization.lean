import ErdosProblems.Erdos67.MRRamarePerronProjection
import ErdosProblems.Erdos67.MRRamareMeanSquare

/-!
# Finite Ramaré factorisation on a dyadic interval

The complete-`LSeries` factorisation is not the finite factorisation used
in the Matomäki--Radziwiłł mean-value argument.  Here the coefficient on
`(Z,2Z]` is written as an exact prime--cofactor sum.  Enlarging the
prime-dependent cofactor supports to one common rectangle produces the
finite product to which a Dirichlet-polynomial mean-value theorem applies;
the only difference is an explicit boundary polynomial.

For a prime block `I=(L,U)` the common cofactor rectangle is

`Z/U < k ≤ 2Z/L`.

Thus its length has the required scale `Z/L`, rather than the length `Z`
of an unrestricted cofactor series.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67

noncomputable section

/-- The common finite cofactor rectangle attached to the prime interval
`I` and the dyadic product interval `(Z,2Z]`. -/
def mrDyadicCofactorRectangle (I : ℕ × ℕ) (Z : ℕ) : Finset ℕ :=
  Finset.Ioc (Z / I.2) ((2 * Z) / I.1)

/-- One denominator-corrected prime--cofactor Mellin monomial. -/
def mrFiniteRamareTerm
    (P : Finset ℕ) (f : ℕ → ℂ) (sigma t : ℝ) (p k : ℕ) : ℂ :=
  (f p * f k / (mrCommonDenominator P k : ℂ)) *
    Complex.ofReal ((p : ℝ) ^ (-sigma)) *
    Complex.ofReal ((k : ℝ) ^ (-sigma)) *
    logarithmicPhase (p * k) (-t)

/-- The exact finite Ramaré polynomial on `(Z,2Z]`, before enlarging the
cofactor support to a rectangle. -/
def mrFiniteDyadicRamarePolynomial
    (I : ℕ × ℕ) (f : ℕ → ℂ) (Z : ℕ) (sigma t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc Z (2 * Z),
    ∑ p ∈ primesInBlock I,
      if p ∣ n then
        mrFiniteRamareTerm (primesInBlock I) f sigma t p (n / p)
      else 0

/-- The exact boundary introduced by replacing every prime-dependent
cofactor support by the common rectangle. -/
def mrFiniteRamareBoundaryPolynomial
    (I : ℕ × ℕ) (f : ℕ → ℂ) (Z : ℕ) (sigma t : ℝ) : ℂ :=
  ∑ p ∈ primesInBlock I,
    ∑ k ∈ mrDyadicCofactorRectangle I Z \
        divisorCofactorImage (Finset.Ioc Z (2 * Z)) p,
      mrFiniteRamareTerm (primesInBlock I) f sigma t p k

theorem mem_divisorCofactorImage_Ioc_iff
    {Z p k : ℕ} (hp : 0 < p) :
    k ∈ divisorCofactorImage (Finset.Ioc Z (2 * Z)) p ↔
      p * k ∈ Finset.Ioc Z (2 * Z) := by
  constructor
  · intro hk
    obtain ⟨n, hn, hpn, rfl⟩ := mem_divisorCofactorImage.mp hk
    simpa [Nat.mul_div_cancel' hpn] using hn
  · intro hk
    apply mem_divisorCofactorImage.mpr
    refine ⟨p * k, hk, dvd_mul_right p k, ?_⟩
    exact Nat.mul_div_cancel_left k hp

/-- Every cofactor which actually occurs in the dyadic polynomial lies in
the common rectangle `Z/I.hi < k ≤ 2Z/I.lo`. -/
theorem divisorCofactorImage_Ioc_subset_mrDyadicCofactorRectangle
    {I : ℕ × ℕ} {Z p : ℕ} (hlo : 0 < I.1)
    (hp : p ∈ primesInBlock I) :
    divisorCofactorImage (Finset.Ioc Z (2 * Z)) p ⊆
      mrDyadicCofactorRectangle I Z := by
  intro k hk
  have hpdata := mem_primesInBlock.mp hp
  have hhi : 0 < I.2 :=
    lt_of_lt_of_le (lt_of_lt_of_le hlo hpdata.2.1) hpdata.2.2
  have hpk := (mem_divisorCofactorImage_Ioc_iff hpdata.1.pos).mp hk
  rw [mrDyadicCofactorRectangle, Finset.mem_Ioc]
  constructor
  · rw [Nat.div_lt_iff_lt_mul hhi]
    calc
      Z < p * k := (Finset.mem_Ioc.mp hpk).1
      _ ≤ k * I.2 := by
        rw [mul_comm p k]
        exact Nat.mul_le_mul_left k hpdata.2.2
  · rw [Nat.le_div_iff_mul_le hlo]
    calc
      k * I.1 ≤ p * k := by
        rw [mul_comm k I.1]
        exact Nat.mul_le_mul_right k hpdata.2.1
      _ ≤ 2 * Z := (Finset.mem_Ioc.mp hpk).2

/-- Coefficientwise form of the finite dyadic polynomial. -/
theorem mrFiniteDyadicRamarePolynomial_eq_commonCoefficient
    (I : ℕ × ℕ) (f : ℕ → ℂ) (Z : ℕ) (sigma t : ℝ) :
    mrFiniteDyadicRamarePolynomial I f Z sigma t =
      ∑ n ∈ Finset.Ioc Z (2 * Z),
        mrCommonRamareCoefficient (primesInBlock I) f n *
          Complex.ofReal ((n : ℝ) ^ (-sigma)) *
          logarithmicPhase n (-t) := by
  classical
  unfold mrFiniteDyadicRamarePolynomial mrCommonRamareCoefficient
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hpn : p ∣ n
  · rw [if_pos hpn, if_pos hpn]
    have hp0 : 0 < p := (mem_primesInBlock.mp hp).1.pos
    have hn0 : 0 < n := by
      have := (Finset.mem_Ioc.mp hn).1
      omega
    have hk0 : 0 < n / p :=
      Nat.div_pos (Nat.le_of_dvd hn0 hpn) hp0
    have hnprod : p * (n / p) = n := Nat.mul_div_cancel' hpn
    have hrpow :
        Complex.ofReal ((p : ℝ) ^ (-sigma)) *
            Complex.ofReal (((n / p : ℕ) : ℝ) ^ (-sigma)) =
          Complex.ofReal ((n : ℝ) ^ (-sigma)) := by
      rw [← Complex.ofReal_mul, ← Real.mul_rpow (by positivity) (by positivity)]
      norm_cast
      rw [hnprod]
    unfold mrFiniteRamareTerm
    rw [hnprod]
    calc
      f p * f (n / p) /
            (mrCommonDenominator (primesInBlock I) (n / p) : ℂ) *
          Complex.ofReal ((p : ℝ) ^ (-sigma)) *
          Complex.ofReal (((n / p : ℕ) : ℝ) ^ (-sigma)) *
          logarithmicPhase n (-t) =
        (f p * f (n / p) /
            (mrCommonDenominator (primesInBlock I) (n / p) : ℂ)) *
          (Complex.ofReal ((p : ℝ) ^ (-sigma)) *
            Complex.ofReal (((n / p : ℕ) : ℝ) ^ (-sigma))) *
          logarithmicPhase n (-t) := by ring
      _ = _ := by rw [hrpow]
  · simp [hpn]

/-- Reindexing the exact dyadic polynomial by the cofactor gives the
prime-dependent finite supports occurring in Ramaré's identity. -/
theorem mrFiniteDyadicRamarePolynomial_eq_cofactorSum
    (I : ℕ × ℕ) (f : ℕ → ℂ) (Z : ℕ) (sigma t : ℝ) :
    mrFiniteDyadicRamarePolynomial I f Z sigma t =
      ∑ p ∈ primesInBlock I,
        ∑ k ∈ divisorCofactorImage (Finset.Ioc Z (2 * Z)) p,
          mrFiniteRamareTerm (primesInBlock I) f sigma t p k := by
  classical
  unfold mrFiniteDyadicRamarePolynomial
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  exact sum_dvd_eq_sum_divisorCofactorImage
    (Finset.Ioc Z (2 * Z)) (mem_primesInBlock.mp hp).1.pos
    (fun _ k ↦ mrFiniteRamareTerm
      (primesInBlock I) f sigma t p k)

/-- At real part one the exact finite Ramaré polynomial is precisely the
dyadic vertical polynomial used by `MRLemma14`. -/
theorem mrFiniteDyadicRamarePolynomial_one_eq_mrDyadicMellinPolynomial
    (I : ℕ × ℕ) (f : ℕ → ℂ) (Z : ℕ) (t : ℝ) :
    mrFiniteDyadicRamarePolynomial I f Z 1 t =
      mrDyadicMellinPolynomial
        (mrRamareConvolutionCoefficient (primesInBlock I) f) Z 1 t := by
  rw [mrFiniteDyadicRamarePolynomial_eq_commonCoefficient]
  unfold mrDyadicMellinPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : 0 < n := by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  rw [mrMellinShiftedCoefficient_one_eq _ t hn0]
  rw [mrRamareConvolutionCoefficient, if_neg hn0.ne']
  rw [Real.rpow_neg_one, Complex.ofReal_inv, Complex.ofReal_natCast]
  ring

/-- The finite rectangular prime--cofactor product is the exact dyadic
polynomial plus the explicitly supported boundary polynomial. -/
theorem ramareFiniteRectangleProduct_eq_dyadic_add_boundary
    {I : ℕ × ℕ} (hlo : 0 < I.1) (f : ℕ → ℂ)
    (Z : ℕ) (sigma t : ℝ) :
    ramarePrimePerronFactorAt sigma I f t *
        mrCofactorPerronPolynomial (primesInBlock I)
          (mrDyadicCofactorRectangle I Z) f sigma t =
      mrFiniteDyadicRamarePolynomial I f Z sigma t +
        mrFiniteRamareBoundaryPolynomial I f Z sigma t := by
  classical
  rw [ramarePrimePerronFactorAt_mul_mrCofactorPerronPolynomial]
  · rw [mrFiniteDyadicRamarePolynomial_eq_cofactorSum]
    unfold mrFiniteRamareBoundaryPolynomial
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    unfold mrFiniteRamareTerm
    have hsub :=
      divisorCofactorImage_Ioc_subset_mrDyadicCofactorRectangle
        (I := I) (Z := Z) hlo hp
    have hsplit := Finset.sum_sdiff hsub
      (f := fun k ↦ mrFiniteRamareTerm
        (primesInBlock I) f sigma t p k)
    simpa only [mrFiniteRamareTerm, add_comm] using hsplit.symm
  · intro k hk
    have hk' := (Finset.mem_Ioc.mp hk).1
    exact Nat.zero_lt_of_lt hk'

/-- Equivalent subtraction form, convenient when estimating the dyadic
polynomial by the finite product and the boundary error separately. -/
theorem mrFiniteDyadicRamarePolynomial_eq_rectangleProduct_sub_boundary
    {I : ℕ × ℕ} (hlo : 0 < I.1) (f : ℕ → ℂ)
    (Z : ℕ) (sigma t : ℝ) :
    mrFiniteDyadicRamarePolynomial I f Z sigma t =
      ramarePrimePerronFactorAt sigma I f t *
          mrCofactorPerronPolynomial (primesInBlock I)
            (mrDyadicCofactorRectangle I Z) f sigma t -
        mrFiniteRamareBoundaryPolynomial I f Z sigma t := by
  have h := ramareFiniteRectangleProduct_eq_dyadic_add_boundary
    hlo f Z sigma t
  rw [h]
  ring

/-- The boundary support is exactly the part of the common rectangle for
which the product leaves `(Z,2Z]`. -/
theorem mem_mrFiniteRamareBoundarySupport_iff
    {I : ℕ × ℕ} {Z p k : ℕ} (hp : p ∈ primesInBlock I) :
    k ∈ mrDyadicCofactorRectangle I Z \
        divisorCofactorImage (Finset.Ioc Z (2 * Z)) p ↔
      k ∈ mrDyadicCofactorRectangle I Z ∧
        p * k ∉ Finset.Ioc Z (2 * Z) := by
  rw [Finset.mem_sdiff,
    mem_divisorCofactorImage_Ioc_iff (mem_primesInBlock.mp hp).1.pos]

/-! ## Narrow subblocks with the full denominator retained -/

/-- A prime polynomial on an arbitrary finite subblock.  The denominator
does not occur here; in the accompanying cofactor polynomial it will still
be computed using the full selected prime set `P`. -/
def mrFinitePrimePerronPolynomial
    (D : Finset ℕ) (f : ℕ → ℂ) (sigma t : ℝ) : ℂ :=
  logarithmicDirichletPolynomial D
    (weightedPrimeCoefficient f sigma) (-t)

/-- The contribution of an arbitrary prime subblock `D` to the exact
dyadic Ramaré polynomial with full denominator `P`. -/
def mrFiniteDyadicRamareSubblockPolynomial
    (P D : Finset ℕ) (f : ℕ → ℂ) (Z : ℕ) (sigma t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc Z (2 * Z),
    ∑ p ∈ D,
      if p ∣ n then mrFiniteRamareTerm P f sigma t p (n / p) else 0

/-- Boundary for a narrow subblock `D` lying between the endpoints of
`J`; the cofactor rectangle has the source scale `Z/J.hi < k ≤ 2Z/J.lo`. -/
def mrFiniteRamareSubblockBoundaryPolynomial
    (P D : Finset ℕ) (J : ℕ × ℕ) (f : ℕ → ℂ)
    (Z : ℕ) (sigma t : ℝ) : ℂ :=
  ∑ p ∈ D,
    ∑ k ∈ mrDyadicCofactorRectangle J Z \
        divisorCofactorImage (Finset.Ioc Z (2 * Z)) p,
      mrFiniteRamareTerm P f sigma t p k

theorem divisorCofactorImage_Ioc_subset_rectangle_of_mem_subblock
    {D : Finset ℕ} {J : ℕ × ℕ} {Z p : ℕ}
    (hlo : 0 < J.1)
    (hD : ∀ q ∈ D, J.1 ≤ q ∧ q ≤ J.2)
    (hp : p ∈ D) :
    divisorCofactorImage (Finset.Ioc Z (2 * Z)) p ⊆
      mrDyadicCofactorRectangle J Z := by
  intro k hk
  have hpbounds := hD p hp
  have hp0 : 0 < p := hlo.trans_le hpbounds.1
  have hhi : 0 < J.2 :=
    lt_of_lt_of_le hp0 hpbounds.2
  have hpk := (mem_divisorCofactorImage_Ioc_iff hp0).mp hk
  rw [mrDyadicCofactorRectangle, Finset.mem_Ioc]
  constructor
  · rw [Nat.div_lt_iff_lt_mul hhi]
    calc
      Z < p * k := (Finset.mem_Ioc.mp hpk).1
      _ ≤ k * J.2 := by
        rw [mul_comm p k]
        exact Nat.mul_le_mul_left k hpbounds.2
  · rw [Nat.le_div_iff_mul_le hlo]
    calc
      k * J.1 ≤ p * k := by
        rw [mul_comm k J.1]
        exact Nat.mul_le_mul_right k hpbounds.1
      _ ≤ 2 * Z := (Finset.mem_Ioc.mp hpk).2

/-- Exact cofactor reindexing for one arbitrary narrow subblock. -/
theorem mrFiniteDyadicRamareSubblockPolynomial_eq_cofactorSum
    {P D : Finset ℕ} (hDpos : ∀ p ∈ D, 0 < p)
    (f : ℕ → ℂ) (Z : ℕ) (sigma t : ℝ) :
    mrFiniteDyadicRamareSubblockPolynomial P D f Z sigma t =
      ∑ p ∈ D,
        ∑ k ∈ divisorCofactorImage (Finset.Ioc Z (2 * Z)) p,
          mrFiniteRamareTerm P f sigma t p k := by
  classical
  unfold mrFiniteDyadicRamareSubblockPolynomial
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  exact sum_dvd_eq_sum_divisorCofactorImage
    (Finset.Ioc Z (2 * Z)) (hDpos p hp)
    (fun _ k ↦ mrFiniteRamareTerm P f sigma t p k)

/-- Expansion of a finite narrow-prime polynomial times a finite cofactor
polynomial.  Crucially, the cofactor denominator uses `P`, not `D`. -/
theorem mrFinitePrimePerronPolynomial_mul_mrCofactorPerronPolynomial
    (P D S : Finset ℕ) (f : ℕ → ℂ) (sigma t : ℝ)
    (hDpos : ∀ p ∈ D, 0 < p) (hSpos : ∀ k ∈ S, 0 < k) :
    mrFinitePrimePerronPolynomial D f sigma t *
        mrCofactorPerronPolynomial P S f sigma t =
      ∑ p ∈ D, ∑ k ∈ S, mrFiniteRamareTerm P f sigma t p k := by
  unfold mrFinitePrimePerronPolynomial mrCofactorPerronPolynomial
    logarithmicDirichletPolynomial weightedPrimeCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hp0 : p ≠ 0 := (hDpos p hp).ne'
  have hk0 : k ≠ 0 := (hSpos k hk).ne'
  have hphase : logarithmicPhase p (-t) * logarithmicPhase k (-t) =
      logarithmicPhase (p * k) (-t) := by
    unfold logarithmicPhase
    rw [← Complex.exp_add]
    congr 1
    rw [Nat.cast_mul, Real.log_mul
      (by exact_mod_cast hp0) (by exact_mod_cast hk0)]
    push_cast
    ring
  unfold mrFiniteRamareTerm
  calc
    f p * Complex.ofReal ((p : ℝ) ^ (-sigma)) *
          logarithmicPhase p (-t) *
        ((f k / (mrCommonDenominator P k : ℂ) *
          Complex.ofReal ((k : ℝ) ^ (-sigma))) *
          logarithmicPhase k (-t)) =
      (f p * f k / (mrCommonDenominator P k : ℂ)) *
        Complex.ofReal ((p : ℝ) ^ (-sigma)) *
        Complex.ofReal ((k : ℝ) ^ (-sigma)) *
        (logarithmicPhase p (-t) * logarithmicPhase k (-t)) := by ring
    _ = _ := by rw [hphase]

/-- Source-shaped exact finite factorisation for one narrow subblock.
The full-selected-prime denominator is retained, and the only error is the
explicit product-boundary support. -/
theorem ramareFiniteSubblockRectangleProduct_eq_dyadic_add_boundary
    {P D : Finset ℕ} {J : ℕ × ℕ}
    (hlo : 0 < J.1) (hD : ∀ p ∈ D, J.1 ≤ p ∧ p ≤ J.2)
    (f : ℕ → ℂ) (Z : ℕ) (sigma t : ℝ) :
    mrFinitePrimePerronPolynomial D f sigma t *
        mrCofactorPerronPolynomial P
          (mrDyadicCofactorRectangle J Z) f sigma t =
      mrFiniteDyadicRamareSubblockPolynomial P D f Z sigma t +
        mrFiniteRamareSubblockBoundaryPolynomial
          P D J f Z sigma t := by
  classical
  have hDpos : ∀ p ∈ D, 0 < p := fun p hp ↦
    hlo.trans_le (hD p hp).1
  rw [mrFinitePrimePerronPolynomial_mul_mrCofactorPerronPolynomial
    P D (mrDyadicCofactorRectangle J Z) f sigma t hDpos]
  · rw [mrFiniteDyadicRamareSubblockPolynomial_eq_cofactorSum
      hDpos]
    unfold mrFiniteRamareSubblockBoundaryPolynomial
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hsub :=
      divisorCofactorImage_Ioc_subset_rectangle_of_mem_subblock
        (J := J) (Z := Z) hlo hD hp
    have hsplit := Finset.sum_sdiff hsub
      (f := fun k ↦ mrFiniteRamareTerm P f sigma t p k)
    simpa only [add_comm] using hsplit.symm
  · intro k hk
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hk).1

/-- Coefficient-explicit partition identity, with an arbitrary full prime
set `P`. -/
theorem sum_mrFiniteDyadicRamareSubblockPolynomial_eq_full
    {ι : Type*} [DecidableEq ι] {V : Finset ι}
    {P : Finset ℕ} {D : ι → Finset ℕ}
    (hdisj : Set.PairwiseDisjoint (↑V) D)
    (hcover : V.biUnion D = P)
    (f : ℕ → ℂ) (Z : ℕ) (sigma t : ℝ) :
    (∑ v ∈ V,
        mrFiniteDyadicRamareSubblockPolynomial P (D v) f Z sigma t) =
      ∑ n ∈ Finset.Ioc Z (2 * Z),
        ∑ p ∈ P,
          if p ∣ n then mrFiniteRamareTerm P f sigma t p (n / p)
          else 0 := by
  classical
  unfold mrFiniteDyadicRamareSubblockPolynomial
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  let F : ℕ → ℂ := fun p ↦ if p ∣ n then
    mrFiniteRamareTerm P f sigma t p (n / p) else 0
  change (∑ v ∈ V, ∑ p ∈ D v, F p) = ∑ p ∈ P, F p
  calc
    (∑ v ∈ V, ∑ p ∈ D v, F p) =
        ∑ p ∈ V.biUnion D, F p :=
      (Finset.sum_biUnion (f := F) hdisj).symm
    _ = ∑ p ∈ P, F p := by rw [hcover]

/-- Exact finite source decomposition over a family of narrow prime
subblocks.  Each subblock has its own cofactor range of length on the
scale `Z/J(v).lo`; the sum of explicitly displayed boundary polynomials
is the entire error. -/
theorem mrFiniteDyadicRamarePolynomial_eq_sum_subblockProducts_sub_boundary
    {ι : Type*} [DecidableEq ι] {V : Finset ι}
    {I : ℕ × ℕ} {D : ι → Finset ℕ} {J : ι → ℕ × ℕ}
    (hdisj : Set.PairwiseDisjoint (↑V) D)
    (hcover : V.biUnion D = primesInBlock I)
    (hlo : ∀ v ∈ V, 0 < (J v).1)
    (hD : ∀ v ∈ V, ∀ p ∈ D v, (J v).1 ≤ p ∧ p ≤ (J v).2)
    (f : ℕ → ℂ) (Z : ℕ) (sigma t : ℝ) :
    mrFiniteDyadicRamarePolynomial I f Z sigma t =
      ∑ v ∈ V,
        (mrFinitePrimePerronPolynomial (D v) f sigma t *
            mrCofactorPerronPolynomial (primesInBlock I)
              (mrDyadicCofactorRectangle (J v) Z) f sigma t -
          mrFiniteRamareSubblockBoundaryPolynomial
            (primesInBlock I) (D v) (J v) f Z sigma t) := by
  classical
  have hpartition :=
    sum_mrFiniteDyadicRamareSubblockPolynomial_eq_full
      hdisj hcover f Z sigma t
  change _ = ∑ n ∈ Finset.Ioc Z (2 * Z),
      ∑ p ∈ primesInBlock I,
        if p ∣ n then
          mrFiniteRamareTerm (primesInBlock I) f sigma t p (n / p)
        else 0 at hpartition
  unfold mrFiniteDyadicRamarePolynomial
  rw [← hpartition]
  apply Finset.sum_congr rfl
  intro v hv
  have hfactor :=
    ramareFiniteSubblockRectangleProduct_eq_dyadic_add_boundary
      (P := primesInBlock I) (D := D v) (J := J v)
      (hlo v hv) (hD v hv) f Z sigma t
  rw [hfactor]
  ring

theorem continuous_mrFiniteDyadicRamarePolynomial
    (I : ℕ × ℕ) (f : ℕ → ℂ) (Z : ℕ) (sigma : ℝ) :
    Continuous (fun t ↦
      mrFiniteDyadicRamarePolynomial I f Z sigma t) := by
  unfold mrFiniteDyadicRamarePolynomial
  apply continuous_finsetSum
  intro n hn
  apply continuous_finsetSum
  intro p hp
  by_cases hpn : p ∣ n
  · simp only [hpn, if_true]
    unfold mrFiniteRamareTerm logarithmicPhase
    fun_prop
  · simp only [hpn, if_false]
    fun_prop

theorem continuous_mrFinitePrimePerronPolynomial
    (D : Finset ℕ) (f : ℕ → ℂ) (sigma : ℝ) :
    Continuous (fun t ↦ mrFinitePrimePerronPolynomial D f sigma t) := by
  unfold mrFinitePrimePerronPolynomial logarithmicDirichletPolynomial
    weightedPrimeCoefficient logarithmicPhase
  fun_prop

theorem continuous_mrFiniteCofactorPerronPolynomial
    (P S : Finset ℕ) (f : ℕ → ℂ) (sigma : ℝ) :
    Continuous (fun t ↦ mrCofactorPerronPolynomial P S f sigma t) := by
  unfold mrCofactorPerronPolynomial logarithmicDirichletPolynomial
    logarithmicPhase
  fun_prop

theorem continuous_mrFiniteRamareSubblockBoundaryPolynomial
    (P D : Finset ℕ) (J : ℕ × ℕ) (f : ℕ → ℂ)
    (Z : ℕ) (sigma : ℝ) :
    Continuous (fun t ↦
      mrFiniteRamareSubblockBoundaryPolynomial
        P D J f Z sigma t) := by
  unfold mrFiniteRamareSubblockBoundaryPolynomial mrFiniteRamareTerm
    logarithmicPhase
  fun_prop

/-- Integrated finite Cauchy--Schwarz form of the exact partition.  This
is the algebraic `H log Q` part of source Lemma 12: the number of narrow
subblocks is displayed exactly, and the product energies and boundary
energies remain separate. -/
theorem intervalIntegral_normSq_mrFiniteDyadicRamarePolynomial_le_partition
    {ι : Type*} [DecidableEq ι] {V : Finset ι}
    {I : ℕ × ℕ} {D : ι → Finset ℕ} {J : ι → ℕ × ℕ}
    (hdisj : Set.PairwiseDisjoint (↑V) D)
    (hcover : V.biUnion D = primesInBlock I)
    (hlo : ∀ v ∈ V, 0 < (J v).1)
    (hD : ∀ v ∈ V, ∀ p ∈ D v, (J v).1 ≤ p ∧ p ≤ (J v).2)
    (f : ℕ → ℂ) (Z : ℕ) (sigma : ℝ)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T,
        Complex.normSq (mrFiniteDyadicRamarePolynomial I f Z sigma t)) ≤
      2 * (V.card : ℝ) *
        ∑ v ∈ V,
          ((∫ t in -T..T, Complex.normSq
              (mrFinitePrimePerronPolynomial (D v) f sigma t *
                mrCofactorPerronPolynomial (primesInBlock I)
                  (mrDyadicCofactorRectangle (J v) Z) f sigma t)) +
            ∫ t in -T..T, Complex.normSq
              (mrFiniteRamareSubblockBoundaryPolynomial
                (primesInBlock I) (D v) (J v) f Z sigma t)) := by
  classical
  let Q : ι → ℝ → ℂ := fun v t ↦
    mrFinitePrimePerronPolynomial (D v) f sigma t *
      mrCofactorPerronPolynomial (primesInBlock I)
        (mrDyadicCofactorRectangle (J v) Z) f sigma t
  let E : ι → ℝ → ℂ := fun v t ↦
    mrFiniteRamareSubblockBoundaryPolynomial
      (primesInBlock I) (D v) (J v) f Z sigma t
  have hQ : ∀ v, Continuous (Q v) := by
    intro v
    exact (continuous_mrFinitePrimePerronPolynomial (D v) f sigma).mul
      (continuous_mrFiniteCofactorPerronPolynomial
        (primesInBlock I) (mrDyadicCofactorRectangle (J v) Z) f sigma)
  have hE : ∀ v, Continuous (E v) := by
    intro v
    exact continuous_mrFiniteRamareSubblockBoundaryPolynomial
      (primesInBlock I) (D v) (J v) f Z sigma
  have hfactor : ∀ t : ℝ,
      mrFiniteDyadicRamarePolynomial I f Z sigma t =
        ∑ v ∈ V, (Q v t - E v t) := by
    intro t
    exact mrFiniteDyadicRamarePolynomial_eq_sum_subblockProducts_sub_boundary
      hdisj hcover hlo hD f Z sigma t
  have hpoint : ∀ t : ℝ,
      Complex.normSq (mrFiniteDyadicRamarePolynomial I f Z sigma t) ≤
        2 * (V.card : ℝ) *
          ∑ v ∈ V,
            (Complex.normSq (Q v t) + Complex.normSq (E v t)) := by
    intro t
    rw [hfactor t]
    calc
      Complex.normSq (∑ v ∈ V, (Q v t - E v t)) ≤
          (V.card : ℝ) *
            ∑ v ∈ V, Complex.normSq (Q v t - E v t) :=
        normSq_finset_sum_le_card_mul_sum_normSq V
          (fun v ↦ Q v t - E v t)
      _ ≤ (V.card : ℝ) *
          ∑ v ∈ V,
            (2 * (Complex.normSq (Q v t) +
              Complex.normSq (E v t))) := by
        gcongr with v hv
        exact normSq_sub_le_two_mul_add (Q v t) (E v t)
      _ = 2 * (V.card : ℝ) *
          ∑ v ∈ V,
            (Complex.normSq (Q v t) + Complex.normSq (E v t)) := by
        rw [← Finset.mul_sum]
        ring
  have hleft : IntervalIntegrable
      (fun t ↦ Complex.normSq
        (mrFiniteDyadicRamarePolynomial I f Z sigma t))
      MeasureTheory.volume (-T) T := by
    apply Continuous.intervalIntegrable
    exact Complex.continuous_normSq.comp
      (continuous_mrFiniteDyadicRamarePolynomial I f Z sigma)
  have hright : IntervalIntegrable
      (fun t ↦ 2 * (V.card : ℝ) *
        ∑ v ∈ V,
          (Complex.normSq (Q v t) + Complex.normSq (E v t)))
      MeasureTheory.volume (-T) T := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (continuous_finsetSum V fun v _ ↦
      (Complex.continuous_normSq.comp (hQ v)).add
        (Complex.continuous_normSq.comp (hE v)))
  have hmono := intervalIntegral.integral_mono_on
    (by linarith : -T ≤ T) hleft hright
    (fun t ht ↦ hpoint t)
  calc
    (∫ t in -T..T,
        Complex.normSq (mrFiniteDyadicRamarePolynomial I f Z sigma t)) ≤
        ∫ t in -T..T, 2 * (V.card : ℝ) *
          ∑ v ∈ V,
            (Complex.normSq (Q v t) + Complex.normSq (E v t)) := hmono
    _ = 2 * (V.card : ℝ) *
        ∑ v ∈ V,
          ((∫ t in -T..T, Complex.normSq (Q v t)) +
            ∫ t in -T..T, Complex.normSq (E v t)) := by
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_finsetSum]
      · apply congrArg (fun x : ℝ ↦ 2 * (V.card : ℝ) * x)
        apply Finset.sum_congr rfl
        intro v hv
        simpa only [Function.comp_apply] using
          intervalIntegral.integral_add
            ((Complex.continuous_normSq.comp (hQ v)).intervalIntegrable _ _)
            ((Complex.continuous_normSq.comp (hE v)).intervalIntegrable _ _)
      · intro v hv
        apply Continuous.intervalIntegrable
        exact (Complex.continuous_normSq.comp (hQ v)).add
          (Complex.continuous_normSq.comp (hE v))
    _ = _ := by rfl

/-! ## Quantitative endpoint support and restricted coefficients -/

/-- Prime--cofactor pairs in the enlarged rectangle whose product lies
outside the original dyadic interval. -/
def mrFiniteRamareSubblockBoundaryPairs
    (D : Finset ℕ) (J : ℕ × ℕ) (Z : ℕ) : Finset (ℕ × ℕ) :=
  (D ×ˢ mrDyadicCofactorRectangle J Z).filter
    (fun x ↦ x.1 * x.2 ∉ Finset.Ioc Z (2 * Z))

/-- Products occurring in one subblock boundary, grouped without
multiplicity. -/
def mrFiniteRamareSubblockBoundaryProductSupport
    (D : Finset ℕ) (J : ℕ × ℕ) (Z : ℕ) : Finset ℕ :=
  (mrFiniteRamareSubblockBoundaryPairs D J Z).image
    (fun x ↦ x.1 * x.2)

/-- The two endpoint bands containing every product in the boundary. -/
def mrFiniteRamareSubblockEndpointBands
    (J : ℕ × ℕ) (Z : ℕ) : Finset ℕ :=
  Finset.Icc (J.1 * (Z / J.2 + 1)) Z ∪
    Finset.Ioc (2 * Z) (J.2 * ((2 * Z) / J.1))

theorem boundary_pair_product_mem_endpointBands
    {D : Finset ℕ} {J : ℕ × ℕ} {Z p k : ℕ}
    (hD : ∀ q ∈ D, J.1 ≤ q ∧ q ≤ J.2)
    (hp : p ∈ D)
    (hk : k ∈ mrDyadicCofactorRectangle J Z)
    (hout : p * k ∉ Finset.Ioc Z (2 * Z)) :
    p * k ∈ mrFiniteRamareSubblockEndpointBands J Z := by
  have hpBounds := hD p hp
  have hkBounds := Finset.mem_Ioc.mp hk
  unfold mrFiniteRamareSubblockEndpointBands
  rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
  have hlower : J.1 * (Z / J.2 + 1) ≤ p * k := by
    apply Nat.mul_le_mul hpBounds.1
    omega
  have hupper : p * k ≤ J.2 * ((2 * Z) / J.1) := by
    exact Nat.mul_le_mul hpBounds.2 hkBounds.2
  by_cases hlow : p * k ≤ Z
  · exact Or.inl ⟨hlower, hlow⟩
  · have hhigh : 2 * Z < p * k := by
      have hnmem := hout
      rw [Finset.mem_Ioc] at hnmem
      omega
    exact Or.inr ⟨hhigh, hupper⟩

theorem mrFiniteRamareSubblockBoundaryProductSupport_subset_endpointBands
    {D : Finset ℕ} {J : ℕ × ℕ} {Z : ℕ}
    (hD : ∀ q ∈ D, J.1 ≤ q ∧ q ≤ J.2) :
    mrFiniteRamareSubblockBoundaryProductSupport D J Z ⊆
      mrFiniteRamareSubblockEndpointBands J Z := by
  intro n hn
  rw [mrFiniteRamareSubblockBoundaryProductSupport,
    Finset.mem_image] at hn
  obtain ⟨x, hx, rfl⟩ := hn
  have hx' := Finset.mem_filter.mp hx
  have hxprod := Finset.mem_product.mp hx'.1
  exact boundary_pair_product_mem_endpointBands hD hxprod.1 hxprod.2 hx'.2

theorem card_mrFiniteRamareSubblockBoundaryProductSupport_le
    {D : Finset ℕ} {J : ℕ × ℕ} {Z : ℕ}
    (hD : ∀ q ∈ D, J.1 ≤ q ∧ q ≤ J.2) :
    (mrFiniteRamareSubblockBoundaryProductSupport D J Z).card ≤
      (Finset.Icc (J.1 * (Z / J.2 + 1)) Z).card +
        (Finset.Ioc (2 * Z) (J.2 * ((2 * Z) / J.1))).card := by
  calc
    (mrFiniteRamareSubblockBoundaryProductSupport D J Z).card ≤
        (mrFiniteRamareSubblockEndpointBands J Z).card :=
      Finset.card_le_card
        (mrFiniteRamareSubblockBoundaryProductSupport_subset_endpointBands hD)
    _ ≤ (Finset.Icc (J.1 * (Z / J.2 + 1)) Z).card +
        (Finset.Ioc (2 * Z) (J.2 * ((2 * Z) / J.1))).card := by
      unfold mrFiniteRamareSubblockEndpointBands
      exact Finset.card_union_le _ _

/-- A common-denominator coefficient restricted simultaneously in the
prime and cofactor variables. -/
def mrRestrictedRamareCoefficient
    (P D S : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ D, if p ∣ n ∧ n / p ∈ S then
    f p * f (n / p) / (mrCommonDenominator P (n / p) : ℂ)
  else 0

/-- Restricting prime/cofactor pairs cannot destroy the unit bound supplied
by the corrected Ramaré denominator. -/
theorem norm_mrRestrictedRamareCoefficient_le_one
    {P D S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hDP : D ⊆ P) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    ‖mrRestrictedRamareCoefficient P D S f n‖ ≤ 1 := by
  classical
  let R : Finset ℕ :=
    (primeDivisorSet P n).filter fun p ↦ p ∈ D ∧ n / p ∈ S
  by_cases hdiv : ∃ p ∈ P, p ∣ n
  · have hcount : 0 < primeDivisorCount P n := primeDivisorCount_pos hdiv
    have hrewrite : mrRestrictedRamareCoefficient P D S f n =
        ∑ p ∈ R,
          f p * f (n / p) /
            (mrCommonDenominator P (n / p) : ℂ) := by
      unfold mrRestrictedRamareCoefficient R primeDivisorSet
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext p
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hpD, hpn, hkS⟩
          exact ⟨⟨hDP hpD, hpn⟩, hpD, hkS⟩
        · rintro ⟨⟨hpP, hpn⟩, hpD, hkS⟩
          exact ⟨hpD, hpn, hkS⟩
      · intro p hp
        rfl
    rw [hrewrite]
    calc
      ‖∑ p ∈ R,
          f p * f (n / p) /
            (mrCommonDenominator P (n / p) : ℂ)‖ ≤
          ∑ p ∈ R,
            ‖f p * f (n / p) /
              (mrCommonDenominator P (n / p) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ R,
          ((ramareDenominator P p (n / p) : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro p hpR
        have hpData := mem_primeDivisorSet.mp
          (Finset.mem_filter.mp hpR).1
        have hpPrime := hP p hpData.1
        have hkpos : 0 < n / p :=
          Nat.div_pos (Nat.le_of_dvd hn hpData.2) hpPrime.pos
        have hdenEq : ramareDenominator P p (n / p) =
            primeDivisorCount P n :=
          ramareDenominator_eq_primeDivisorCount hP hpData.1 hpData.2
        have hramPos : (0 : ℝ) < ramareDenominator P p (n / p) := by
          exact_mod_cast (hdenEq.symm ▸ hcount)
        have hcommonPos : (0 : ℝ) < mrCommonDenominator P (n / p) := by
          exact_mod_cast (show 0 < mrCommonDenominator P (n / p) by
            unfold mrCommonDenominator
            omega)
        rw [norm_div, norm_mul, Complex.norm_natCast]
        calc
          ‖f p‖ * ‖f (n / p)‖ /
              (mrCommonDenominator P (n / p) : ℝ) ≤
              1 / (mrCommonDenominator P (n / p) : ℝ) := by
            apply div_le_div_of_nonneg_right _ hcommonPos.le
            calc
              ‖f p‖ * ‖f (n / p)‖ ≤ 1 * 1 :=
                mul_le_mul (hbound p hpPrime.pos) (hbound (n / p) hkpos)
                  (norm_nonneg _) zero_le_one
              _ = 1 := one_mul 1
          _ ≤ 1 / (ramareDenominator P p (n / p) : ℝ) := by
            have hdenle :
                (ramareDenominator P p (n / p) : ℝ) ≤
                  (mrCommonDenominator P (n / p) : ℝ) := by
              exact_mod_cast
                (ramareDenominator_le_mrCommonDenominator P p (n / p))
            exact one_div_le_one_div_of_le hramPos hdenle
          _ = ((ramareDenominator P p (n / p) : ℝ)⁻¹) := by
            rw [one_div]
      _ ≤ ∑ p ∈ primeDivisorSet P n,
          ((ramareDenominator P p (n / p) : ℝ)⁻¹) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro p hpP hpnot
          positivity
      _ = 1 := ramare_identity hP hdiv
  · have hzero : mrRestrictedRamareCoefficient P D S f n = 0 := by
      unfold mrRestrictedRamareCoefficient
      apply Finset.sum_eq_zero
      intro p hpD
      have hpnot : ¬p ∣ n := fun hpn ↦ hdiv ⟨p, hDP hpD, hpn⟩
      simp [hpnot]
    rw [hzero, norm_zero]
    norm_num

/-- The line-one coefficient after grouping all boundary pairs with the
same product.  The numerator is the common-denominator Ramaré coefficient;
the single division by `n` is what retains the inverse dyadic scale. -/
def mrFiniteRamareSubblockBoundaryLineCoefficient
    (P D : Finset ℕ) (J : ℕ × ℕ) (f : ℕ → ℂ)
    (Z n : ℕ) : ℂ :=
  mrRestrictedRamareCoefficient P D (mrDyadicCofactorRectangle J Z) f n /
    (n : ℂ)

/-- Reindex the fiber of boundary prime--cofactor pairs by its prime
coordinate.  The hypothesis that the product is outside `(Z,2Z]` is
exactly what makes every restricted divisor pair a boundary pair. -/
theorem sum_mrFiniteRamareSubblockBoundaryPairFiber_eq_restricted
    {P D : Finset ℕ} {J : ℕ × ℕ} {Z n : ℕ}
    (hDpos : ∀ p ∈ D, 0 < p)
    (hout : n ∉ Finset.Ioc Z (2 * Z)) (f : ℕ → ℂ) :
    (∑ x ∈ (mrFiniteRamareSubblockBoundaryPairs D J Z).filter
        (fun x ↦ x.1 * x.2 = n),
      f x.1 * f x.2 / (mrCommonDenominator P x.2 : ℂ)) =
      mrRestrictedRamareCoefficient P D
        (mrDyadicCofactorRectangle J Z) f n := by
  classical
  let R : Finset ℕ := D.filter fun p ↦
    p ∣ n ∧ n / p ∈ mrDyadicCofactorRectangle J Z
  have hrewrite : mrRestrictedRamareCoefficient P D
      (mrDyadicCofactorRectangle J Z) f n =
      ∑ p ∈ R,
        f p * f (n / p) /
          (mrCommonDenominator P (n / p) : ℂ) := by
    unfold mrRestrictedRamareCoefficient R
    rw [← Finset.sum_filter]
  rw [hrewrite]
  apply Finset.sum_bij (fun x _ ↦ x.1)
  · intro x hx
    have hxFiber := Finset.mem_filter.mp hx
    have hxPair := Finset.mem_filter.mp hxFiber.1
    have hxProd := Finset.mem_product.mp hxPair.1
    change x.1 ∈ D.filter (fun p ↦
      p ∣ n ∧ n / p ∈ mrDyadicCofactorRectangle J Z)
    rw [Finset.mem_filter]
    refine ⟨hxProd.1, ?_, ?_⟩
    · exact ⟨x.2, hxFiber.2.symm⟩
    · have hdiv : n / x.1 = x.2 := by
        rw [← hxFiber.2]
        exact Nat.mul_div_cancel_left x.2 (hDpos x.1 hxProd.1)
      simpa [hdiv] using hxProd.2
  · intro x hx y hy hxy
    apply Prod.ext hxy
    have hxFiber := Finset.mem_filter.mp hx
    have hyFiber := Finset.mem_filter.mp hy
    have hxPair := Finset.mem_filter.mp hxFiber.1
    have hxProd := Finset.mem_product.mp hxPair.1
    apply Nat.eq_of_mul_eq_mul_left (hDpos x.1 hxProd.1)
    calc
      x.1 * x.2 = n := hxFiber.2
      _ = y.1 * y.2 := hyFiber.2.symm
      _ = x.1 * y.2 := by rw [← hxy]
  · intro p hp
    have hpR := Finset.mem_filter.mp hp
    let x : ℕ × ℕ := (p, n / p)
    have hprod : p * (n / p) = n := Nat.mul_div_cancel' hpR.2.1
    refine ⟨x, ?_, rfl⟩
    rw [Finset.mem_filter, mrFiniteRamareSubblockBoundaryPairs,
      Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨⟨hpR.1, hpR.2.2⟩, hprod ▸ hout⟩, hprod⟩
  · intro x hx
    have hxFiber := Finset.mem_filter.mp hx
    have hxPair := Finset.mem_filter.mp hxFiber.1
    have hxProd := Finset.mem_product.mp hxPair.1
    have hdiv : n / x.1 = x.2 := by
      rw [← hxFiber.2]
      exact Nat.mul_div_cancel_left x.2 (hDpos x.1 hxProd.1)
    simp only [hdiv]

/-- At `sigma = 1`, one prime--cofactor monomial has the ordinary
line-one coefficient `1/(pk)`. -/
theorem mrFiniteRamareTerm_one_eq_line
    (P : Finset ℕ) (f : ℕ → ℂ) (t : ℝ)
    (p k : ℕ) :
    mrFiniteRamareTerm P f 1 t p k =
      (f p * f k / (mrCommonDenominator P k : ℂ) / (p * k : ℂ)) *
        logarithmicPhase (p * k) (-t) := by
  have hdenNat : mrCommonDenominator P k ≠ 0 := by
    unfold mrCommonDenominator
    omega
  unfold mrFiniteRamareTerm
  simp only [Real.rpow_neg_one, Complex.ofReal_inv,
    Complex.ofReal_natCast]
  ring_nf

/-- The boundary double sum is exactly the sum over the explicit finite set
of out-of-range prime--cofactor pairs. -/
theorem mrFiniteRamareSubblockBoundaryPolynomial_eq_pairSum
    {P D : Finset ℕ} {J : ℕ × ℕ}
    (hDpos : ∀ p ∈ D, 0 < p)
    (f : ℕ → ℂ) (Z : ℕ) (sigma t : ℝ) :
    mrFiniteRamareSubblockBoundaryPolynomial P D J f Z sigma t =
      ∑ x ∈ mrFiniteRamareSubblockBoundaryPairs D J Z,
        mrFiniteRamareTerm P f sigma t x.1 x.2 := by
  classical
  unfold mrFiniteRamareSubblockBoundaryPolynomial
    mrFiniteRamareSubblockBoundaryPairs
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sdiff_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k hk
  have hmem := mem_divisorCofactorImage_Ioc_iff
    (Z := Z) (k := k) (hDpos p hp)
  by_cases hpk : p * k ∈ Finset.Ioc Z (2 * Z)
  · have hkImage := hmem.mpr hpk
    simp only [hkImage, hpk, not_true_eq_false, if_false]
  · have hkNotImage : k ∉ divisorCofactorImage
        (Finset.Ioc Z (2 * Z)) p := fun hkImage ↦ hpk (hmem.mp hkImage)
    simp only [hkNotImage, hpk, not_false_eq_true, if_true]

/-- The line-one boundary is a single finite logarithmic Dirichlet
polynomial.  Products with several selected prime divisors are combined
before applying the mean-value theorem. -/
theorem mrFiniteRamareSubblockBoundaryPolynomial_one_eq_logarithmic
    {P D : Finset ℕ} {J : ℕ × ℕ}
    (hDpos : ∀ p ∈ D, 0 < p)
    (f : ℕ → ℂ) (Z : ℕ) (t : ℝ) :
    mrFiniteRamareSubblockBoundaryPolynomial P D J f Z 1 t =
      logarithmicDirichletPolynomial
        (mrFiniteRamareSubblockBoundaryProductSupport D J Z)
        (mrFiniteRamareSubblockBoundaryLineCoefficient P D J f Z) (-t) := by
  classical
  rw [mrFiniteRamareSubblockBoundaryPolynomial_eq_pairSum hDpos]
  let B := mrFiniteRamareSubblockBoundaryPairs D J Z
  let N := mrFiniteRamareSubblockBoundaryProductSupport D J Z
  have hmaps : ∀ x ∈ B, x.1 * x.2 ∈ N := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := B) (t := N) (g := fun x : ℕ × ℕ ↦ x.1 * x.2)
    hmaps (fun x ↦ mrFiniteRamareTerm P f 1 t x.1 x.2)
  change (∑ x ∈ B, mrFiniteRamareTerm P f 1 t x.1 x.2) = _
  rw [← hfiber]
  unfold logarithmicDirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hnData := Finset.mem_image.mp hn
  obtain ⟨y, hyB, hyprod⟩ := hnData
  have hyPair := Finset.mem_filter.mp hyB
  have hyProdMem := Finset.mem_product.mp hyPair.1
  have hnout : n ∉ Finset.Ioc Z (2 * Z) := by
    rw [← hyprod]
    exact hyPair.2
  have hfiberEq :=
    sum_mrFiniteRamareSubblockBoundaryPairFiber_eq_restricted
      (P := P) (J := J) hDpos hnout f
  calc
    (∑ x ∈ B.filter (fun x ↦ x.1 * x.2 = n),
        mrFiniteRamareTerm P f 1 t x.1 x.2) =
        ∑ x ∈ B.filter (fun x ↦ x.1 * x.2 = n),
          (f x.1 * f x.2 /
              (mrCommonDenominator P x.2 : ℂ) / (n : ℂ)) *
            logarithmicPhase n (-t) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxFiber := Finset.mem_filter.mp hx
      rw [mrFiniteRamareTerm_one_eq_line P f t x.1 x.2]
      rw [← Nat.cast_mul, hxFiber.2]
    _ = ((∑ x ∈ B.filter (fun x ↦ x.1 * x.2 = n),
          f x.1 * f x.2 /
            (mrCommonDenominator P x.2 : ℂ)) / (n : ℂ)) *
          logarithmicPhase n (-t) := by
      rw [Finset.sum_div, Finset.sum_mul]
    _ = mrFiniteRamareSubblockBoundaryLineCoefficient P D J f Z n *
          logarithmicPhase n (-t) := by
      unfold mrFiniteRamareSubblockBoundaryLineCoefficient
      rw [← hfiberEq]

/-- The grouped boundary coefficient retains the full line-one decay. -/
theorem norm_mrFiniteRamareSubblockBoundaryLineCoefficient_le_inv
    {P D : Finset ℕ} {J : ℕ × ℕ} {Z n : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hDP : D ⊆ P)
    {f : ℕ → ℂ} (hbound : ∀ m, 0 < m → ‖f m‖ ≤ 1)
    (hn : 0 < n) :
    ‖mrFiniteRamareSubblockBoundaryLineCoefficient P D J f Z n‖ ≤
      (n : ℝ)⁻¹ := by
  unfold mrFiniteRamareSubblockBoundaryLineCoefficient
  rw [norm_div, Complex.norm_natCast, div_eq_mul_inv]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (norm_mrRestrictedRamareCoefficient_le_one hP hDP hbound hn)
    (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ n))

/-- Every grouped boundary product has the exact lower and upper scales
forced by its prime block and common cofactor rectangle. -/
theorem mem_mrFiniteRamareSubblockBoundaryProductSupport_bounds
    {D : Finset ℕ} {J : ℕ × ℕ} {Z n : ℕ}
    (hD : ∀ q ∈ D, J.1 ≤ q ∧ q ≤ J.2)
    (hn : n ∈ mrFiniteRamareSubblockBoundaryProductSupport D J Z) :
    J.1 * (Z / J.2 + 1) ≤ n ∧
      n ≤ J.2 * ((2 * Z) / J.1) := by
  rw [mrFiniteRamareSubblockBoundaryProductSupport,
    Finset.mem_image] at hn
  obtain ⟨x, hx, rfl⟩ := hn
  have hxPair := Finset.mem_filter.mp hx
  have hxProd := Finset.mem_product.mp hxPair.1
  have hpBounds := hD x.1 hxProd.1
  have hkBounds := Finset.mem_Ioc.mp hxProd.2
  constructor
  · apply Nat.mul_le_mul hpBounds.1
    omega
  · exact Nat.mul_le_mul hpBounds.2 hkBounds.2

/-- Continuous mean-value theorem on an arbitrary positive finite support
bounded above by `N`.  This local version is kept in the factorisation
module so its boundary theorem has no dependency cycle. -/
theorem norm_logarithmicDirichletPolynomial_intervalIntegral_le_support
    {A : Finset ℕ} {N : ℕ} (hN : 0 < N)
    (hApos : ∀ n ∈ A, 0 < n) (hAN : ∀ n ∈ A, n ≤ N)
    (a : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in -T..T,
        conj (logarithmicDirichletPolynomial A a t) *
          logarithmicDirichletPolynomial A a t‖ ≤
      (2 * T + 2 * Real.pi * (N : ℝ)) *
        ∑ n ∈ A, Complex.normSq (a n) := by
  let freq : ↑A → ℝ := fun n ↦ Real.log (n : ℕ)
  let coeff : ↑A → ℂ := fun n ↦ a n
  have hdelta : (0 : ℝ) < (N : ℝ)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast hN)
  have hsep : ∀ r s : ↑A, r ≠ s →
      (N : ℝ)⁻¹ ≤ |freq r - freq s| := by
    intro r s hrs
    exact inv_nat_le_abs_log_sub_log
      (hApos r r.property) (hApos s s.property)
      (hAN r r.property) (hAN s s.property)
      (fun h ↦ hrs (Subtype.ext h))
  have hmean := norm_finiteFrequencyPolynomial_intervalIntegral_le
    freq coeff hT hdelta hsep
  have hpoly : finiteFrequencyPolynomial freq coeff =
      logarithmicDirichletPolynomial A a := by
    funext t
    unfold finiteFrequencyPolynomial logarithmicDirichletPolynomial
    rw [show (∑ n ∈ A, a n * logarithmicPhase n t) =
      ∑ n : ↑A, a n * logarithmicPhase n t by
        exact Finset.sum_subtype A (fun _ ↦ Iff.rfl)
          (fun n ↦ a n * logarithmicPhase n t)]
    apply Finset.sum_congr rfl
    intro n hn
    rfl
  rw [hpoly] at hmean
  simpa only [coeff, inv_inv, Complex.normSq_eq_norm_sq,
    Finset.sum_subtype A (fun _ ↦ Iff.rfl)
      (fun n ↦ ‖a n‖ ^ 2)] using hmean

/-- Square mass of the grouped boundary coefficients.  The endpoint-card
factor measures only the two thin bands, while the inverse square factor
is at the full product scale. -/
theorem sum_normSq_mrFiniteRamareSubblockBoundaryLineCoefficient_le
    {P D : Finset ℕ} {J : ℕ × ℕ} {Z : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hDP : D ⊆ P)
    (hlo : 0 < J.1)
    (hD : ∀ q ∈ D, J.1 ≤ q ∧ q ≤ J.2)
    {f : ℕ → ℂ} (hbound : ∀ m, 0 < m → ‖f m‖ ≤ 1) :
    (∑ n ∈ mrFiniteRamareSubblockBoundaryProductSupport D J Z,
        Complex.normSq
          (mrFiniteRamareSubblockBoundaryLineCoefficient P D J f Z n)) ≤
      (((Finset.Icc (J.1 * (Z / J.2 + 1)) Z).card +
          (Finset.Ioc (2 * Z) (J.2 * ((2 * Z) / J.1))).card : ℕ) : ℝ) *
        ((J.1 * (Z / J.2 + 1) : ℕ) : ℝ)⁻¹ ^ 2 := by
  let L : ℕ := J.1 * (Z / J.2 + 1)
  have hL : 0 < L := Nat.mul_pos hlo (Nat.succ_pos _)
  have hterm : ∀ n ∈
      mrFiniteRamareSubblockBoundaryProductSupport D J Z,
      Complex.normSq
          (mrFiniteRamareSubblockBoundaryLineCoefficient P D J f Z n) ≤
        ((L : ℝ)⁻¹) ^ 2 := by
    intro n hn
    have hnBounds :=
      mem_mrFiniteRamareSubblockBoundaryProductSupport_bounds hD hn
    have hnpos : 0 < n := hL.trans_le hnBounds.1
    have hcoeff :=
      norm_mrFiniteRamareSubblockBoundaryLineCoefficient_le_inv
        (J := J) (Z := Z) hP hDP hbound hnpos
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL
    have hLn : (L : ℝ) ≤ n := by exact_mod_cast hnBounds.1
    have hinv : (n : ℝ)⁻¹ ≤ (L : ℝ)⁻¹ := inv_anti₀ hLR hLn
    rw [Complex.normSq_eq_norm_sq]
    calc
      ‖mrFiniteRamareSubblockBoundaryLineCoefficient P D J f Z n‖ ^ 2 ≤
          ((n : ℝ)⁻¹) ^ 2 := by gcongr
      _ ≤ ((L : ℝ)⁻¹) ^ 2 := by gcongr
  calc
    (∑ n ∈ mrFiniteRamareSubblockBoundaryProductSupport D J Z,
        Complex.normSq
          (mrFiniteRamareSubblockBoundaryLineCoefficient P D J f Z n)) ≤
        ∑ _n ∈ mrFiniteRamareSubblockBoundaryProductSupport D J Z,
          ((L : ℝ)⁻¹) ^ 2 :=
      Finset.sum_le_sum fun n hn ↦ hterm n hn
    _ = ((mrFiniteRamareSubblockBoundaryProductSupport D J Z).card : ℝ) *
        ((L : ℝ)⁻¹) ^ 2 := by simp
    _ ≤ (((Finset.Icc (J.1 * (Z / J.2 + 1)) Z).card +
          (Finset.Ioc (2 * Z) (J.2 * ((2 * Z) / J.1))).card : ℕ) : ℝ) *
        ((L : ℝ)⁻¹) ^ 2 := by
      gcongr
      exact_mod_cast card_mrFiniteRamareSubblockBoundaryProductSupport_le hD
    _ = _ := by rfl

/-- Explicit endpoint-boundary energy.  Its first factor is the standard
Dirichlet-polynomial vertical length, its second is the number of endpoint
integers, and its last factor is the inverse square full-product scale. -/
def mrFiniteRamareSubblockBoundaryEnergyBound
    (J : ℕ × ℕ) (Z : ℕ) (T : ℝ) : ℝ :=
  (2 * T + 2 * Real.pi *
      ((J.2 * ((2 * Z) / J.1) : ℕ) : ℝ)) *
    (((Finset.Icc (J.1 * (Z / J.2 + 1)) Z).card +
        (Finset.Ioc (2 * Z) (J.2 * ((2 * Z) / J.1))).card : ℕ) : ℝ) *
      ((J.1 * (Z / J.2 + 1) : ℕ) : ℝ)⁻¹ ^ 2

/-- The endpoint-card term is controlled by the relative prime-block
width, plus the unavoidable integer-endpoint term.  For source blocks of
multiplicative width `exp(1/H)`, the two terms containing `J.hi-J.lo`
are the finite `1/H` contribution; the middle `J.hi` is the floor-error
contribution. -/
theorem card_mrFiniteRamareSubblockEndpointBands_le_width
    {J : ℕ × ℕ} {Z : ℕ} (hlo : 0 < J.1) (hJle : J.1 ≤ J.2) :
    (Finset.Icc (J.1 * (Z / J.2 + 1)) Z).card +
        (Finset.Ioc (2 * Z) (J.2 * ((2 * Z) / J.1))).card ≤
      (J.2 - J.1) * (Z / J.2) + J.2 +
        (J.2 - J.1) * ((2 * Z) / J.1) := by
  have hhi : 0 < J.2 := hlo.trans_le hJle
  let q : ℕ := Z / J.2
  let r : ℕ := Z % J.2
  let q₂ : ℕ := (2 * Z) / J.1
  let r₂ : ℕ := (2 * Z) % J.1
  have hdecomp : J.2 * q + r = Z := by
    simpa only [q, r, Nat.mul_comm] using Nat.div_add_mod Z J.2
  have hr : r < J.2 := Nat.mod_lt Z hhi
  have hdecomp₂ : J.1 * q₂ + r₂ = 2 * Z := by
    simpa only [q₂, r₂, Nat.mul_comm] using Nat.div_add_mod (2 * Z) J.1
  have hr₂ : r₂ < J.1 := Nat.mod_lt (2 * Z) hlo
  have hsplit : J.1 + (J.2 - J.1) = J.2 := Nat.add_sub_of_le hJle
  have hmul : J.2 * q = J.1 * q + (J.2 - J.1) * q := by
    conv_lhs => rw [← hsplit]
    rw [Nat.add_mul]
  have hmul₂ : J.2 * q₂ = J.1 * q₂ + (J.2 - J.1) * q₂ := by
    conv_lhs => rw [← hsplit]
    rw [Nat.add_mul]
  rw [Nat.card_Icc, Nat.card_Ioc]
  change Z + 1 - J.1 * (q + 1) +
      (J.2 * q₂ - 2 * Z) ≤
    (J.2 - J.1) * q + J.2 + (J.2 - J.1) * q₂
  have hlow : Z + 1 - J.1 * (q + 1) ≤
      (J.2 - J.1) * q + J.2 := by
    rw [Nat.mul_add]
    omega
  have hhigh : J.2 * q₂ - 2 * Z ≤ (J.2 - J.1) * q₂ := by
    omega
  omega

/-- Under the usual width-at-most-two hypothesis, the grouped product
lower endpoint is at least `Z/2`.  This records explicitly that the
coefficient square mass has `1/Z²`, rather than `1/Z`, scale. -/
theorem half_scale_le_mrFiniteRamareSubblock_lowerEndpoint
    {J : ℕ × ℕ} {Z : ℕ} (hlo : 0 < J.1)
    (hJle : J.1 ≤ J.2) (hwidth : J.2 ≤ 2 * J.1) :
    Z ≤ 2 * (J.1 * (Z / J.2 + 1)) := by
  have hhi : 0 < J.2 := hlo.trans_le hJle
  let q : ℕ := Z / J.2
  let r : ℕ := Z % J.2
  have hdecomp : J.2 * q + r = Z := by
    simpa only [q, r, Nat.mul_comm] using Nat.div_add_mod Z J.2
  have hr : r < J.2 := Nat.mod_lt Z hhi
  have hmul : J.2 * (q + 1) ≤ 2 * J.1 * (q + 1) :=
    Nat.mul_le_mul_right (q + 1) hwidth
  calc
    Z ≤ J.2 * (q + 1) := by
      rw [Nat.mul_add]
      omega
    _ ≤ 2 * J.1 * (q + 1) := hmul
    _ = 2 * (J.1 * (Z / J.2 + 1)) := by
      simp only [q, Nat.mul_assoc]

/-- A width-explicit corollary of the exact boundary energy. -/
theorem mrFiniteRamareSubblockBoundaryEnergyBound_le_width
    {J : ℕ × ℕ} {Z : ℕ} {T : ℝ}
    (hlo : 0 < J.1) (hJle : J.1 ≤ J.2) (hT : 0 ≤ T) :
    mrFiniteRamareSubblockBoundaryEnergyBound J Z T ≤
      (2 * T + 2 * Real.pi *
          ((J.2 * ((2 * Z) / J.1) : ℕ) : ℝ)) *
        ((((J.2 - J.1) * (Z / J.2) + J.2 +
            (J.2 - J.1) * ((2 * Z) / J.1) : ℕ) : ℝ) *
          ((J.1 * (Z / J.2 + 1) : ℕ) : ℝ)⁻¹ ^ 2) := by
  unfold mrFiniteRamareSubblockBoundaryEnergyBound
  have hfactor : 0 ≤ 2 * T + 2 * Real.pi *
      ((J.2 * ((2 * Z) / J.1) : ℕ) : ℝ) := by positivity
  have hcard := card_mrFiniteRamareSubblockEndpointBands_le_width
    (J := J) (Z := Z) hlo hJle
  have hcardR :
      (((Finset.Icc (J.1 * (Z / J.2 + 1)) Z).card +
          (Finset.Ioc (2 * Z) (J.2 * ((2 * Z) / J.1))).card : ℕ) : ℝ) ≤
        (((J.2 - J.1) * (Z / J.2) + J.2 +
          (J.2 - J.1) * ((2 * Z) / J.1) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  calc
    (2 * T + 2 * Real.pi *
        ((J.2 * ((2 * Z) / J.1) : ℕ) : ℝ)) *
        (((Finset.Icc (J.1 * (Z / J.2 + 1)) Z).card +
          (Finset.Ioc (2 * Z) (J.2 * ((2 * Z) / J.1))).card : ℕ) : ℝ) *
        ((J.1 * (Z / J.2 + 1) : ℕ) : ℝ)⁻¹ ^ 2 ≤
      (2 * T + 2 * Real.pi *
        ((J.2 * ((2 * Z) / J.1) : ℕ) : ℝ)) *
        ((((J.2 - J.1) * (Z / J.2) + J.2 +
          (J.2 - J.1) * ((2 * Z) / J.1) : ℕ) : ℝ) *
        ((J.1 * (Z / J.2 + 1) : ℕ) : ℝ)⁻¹ ^ 2) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hfactor
      exact mul_le_mul_of_nonneg_right hcardR (sq_nonneg _)
    _ = _ := by rfl

/-- Quantitative source-scale boundary estimate for one narrow prime
subblock.  No row-count loss occurs: equal products were grouped before
the continuous mean-value theorem was applied. -/
theorem intervalIntegral_normSq_mrFiniteRamareSubblockBoundaryPolynomial_le
    {P D : Finset ℕ} {J : ℕ × ℕ} {Z : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hDP : D ⊆ P)
    (hlo : 0 < J.1) (hJle : J.1 ≤ J.2) (hJZ : J.1 ≤ Z)
    (hD : ∀ q ∈ D, J.1 ≤ q ∧ q ≤ J.2)
    {f : ℕ → ℂ} (hbound : ∀ m, 0 < m → ‖f m‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, Complex.normSq
        (mrFiniteRamareSubblockBoundaryPolynomial P D J f Z 1 t)) ≤
      mrFiniteRamareSubblockBoundaryEnergyBound J Z T := by
  let A := mrFiniteRamareSubblockBoundaryProductSupport D J Z
  let a := mrFiniteRamareSubblockBoundaryLineCoefficient P D J f Z
  let N : ℕ := J.2 * ((2 * Z) / J.1)
  have hL : 0 < J.1 * (Z / J.2 + 1) :=
    Nat.mul_pos hlo (Nat.succ_pos _)
  have hN : 0 < N := by
    have hJhi : 0 < J.2 := hlo.trans_le hJle
    have hquot : 0 < (2 * Z) / J.1 := by
      apply Nat.div_pos
      · omega
      · exact hlo
    exact Nat.mul_pos hJhi hquot
  have hApos : ∀ n ∈ A, 0 < n := by
    intro n hn
    exact hL.trans_le
      (mem_mrFiniteRamareSubblockBoundaryProductSupport_bounds hD hn).1
  have hAN : ∀ n ∈ A, n ≤ N := by
    intro n hn
    exact (mem_mrFiniteRamareSubblockBoundaryProductSupport_bounds hD hn).2
  have hDpos : ∀ p ∈ D, 0 < p := fun p hp ↦
    hlo.trans_le (hD p hp).1
  have hflip :
      (∫ t in -T..T, Complex.normSq
          (mrFiniteRamareSubblockBoundaryPolynomial P D J f Z 1 t)) =
        ∫ t in -T..T,
          Complex.normSq (logarithmicDirichletPolynomial A a t) := by
    calc
      (∫ t in -T..T, Complex.normSq
          (mrFiniteRamareSubblockBoundaryPolynomial P D J f Z 1 t)) =
          ∫ t in -T..T,
            Complex.normSq (logarithmicDirichletPolynomial A a (-t)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        simpa only [A, a] using congrArg Complex.normSq
          (mrFiniteRamareSubblockBoundaryPolynomial_one_eq_logarithmic
            hDpos f Z t)
      _ = ∫ t in -T..T,
          Complex.normSq (logarithmicDirichletPolynomial A a t) := by
        simpa only [neg_neg] using
          (intervalIntegral.integral_comp_neg (a := -T) (b := T)
            (fun t ↦ Complex.normSq
              (logarithmicDirichletPolynomial A a t)))
  have hmean :=
    norm_logarithmicDirichletPolynomial_intervalIntegral_le_support
      hN hApos hAN a hT
  have hmass :=
    sum_normSq_mrFiniteRamareSubblockBoundaryLineCoefficient_le
      (Z := Z) hP hDP hlo hD hbound
  have hfactor : 0 ≤ 2 * T + 2 * Real.pi * (N : ℝ) := by positivity
  calc
    (∫ t in -T..T, Complex.normSq
        (mrFiniteRamareSubblockBoundaryPolynomial P D J f Z 1 t)) =
        ∫ t in -T..T,
          Complex.normSq (logarithmicDirichletPolynomial A a t) := hflip
    _ = ∫ t in -T..T,
        ‖logarithmicDirichletPolynomial A a t‖ ^ 2 := by
      simp only [Complex.normSq_eq_norm_sq]
    _ = ‖∫ t in -T..T,
        conj (logarithmicDirichletPolynomial A a t) *
          logarithmicDirichletPolynomial A a t‖ :=
      intervalIntegral_norm_sq_eq_norm_conj_mul_self
        (fun t ↦ logarithmicDirichletPolynomial A a t) hT
    _ ≤ (2 * T + 2 * Real.pi * (N : ℝ)) *
          ∑ n ∈ A, Complex.normSq (a n) := hmean
    _ ≤ (2 * T + 2 * Real.pi * (N : ℝ)) *
        ((((Finset.Icc (J.1 * (Z / J.2 + 1)) Z).card +
            (Finset.Ioc (2 * Z) (J.2 * ((2 * Z) / J.1))).card : ℕ) : ℝ) *
          ((J.1 * (Z / J.2 + 1) : ℕ) : ℝ)⁻¹ ^ 2) :=
      mul_le_mul_of_nonneg_left hmass hfactor
    _ = mrFiniteRamareSubblockBoundaryEnergyBound J Z T := by
      unfold mrFiniteRamareSubblockBoundaryEnergyBound N
      ring

/-- Lemma-12-style finite recombination with every boundary integral
eliminated.  The only analytic terms left are the genuine finite
prime-polynomial times finite-cofactor-polynomial energies; all support
enlargement errors are the explicit endpoint quantities above. -/
theorem intervalIntegral_normSq_mrFiniteDyadicRamarePolynomial_le_products_add_boundary
    {ι : Type*} [DecidableEq ι] {V : Finset ι}
    {I : ℕ × ℕ} {D : ι → Finset ℕ} {J : ι → ℕ × ℕ} {Z : ℕ}
    (hdisj : Set.PairwiseDisjoint (↑V) D)
    (hcover : V.biUnion D = primesInBlock I)
    (hlo : ∀ v ∈ V, 0 < (J v).1)
    (hJle : ∀ v ∈ V, (J v).1 ≤ (J v).2)
    (hJZ : ∀ v ∈ V, (J v).1 ≤ Z)
    (hD : ∀ v ∈ V, ∀ p ∈ D v,
      (J v).1 ≤ p ∧ p ≤ (J v).2)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T,
        Complex.normSq (mrFiniteDyadicRamarePolynomial I f Z 1 t)) ≤
      2 * (V.card : ℝ) *
        ((∑ v ∈ V,
            ∫ t in -T..T, Complex.normSq
              (mrFinitePrimePerronPolynomial (D v) f 1 t *
                mrCofactorPerronPolynomial (primesInBlock I)
                  (mrDyadicCofactorRectangle (J v) Z) f 1 t)) +
          ∑ v ∈ V, mrFiniteRamareSubblockBoundaryEnergyBound (J v) Z T) := by
  classical
  have hP : ∀ p ∈ primesInBlock I, p.Prime := fun p hp ↦
    (mem_primesInBlock.mp hp).1
  have hDP : ∀ v ∈ V, D v ⊆ primesInBlock I := by
    intro v hv p hp
    rw [← hcover]
    exact Finset.mem_biUnion.mpr ⟨v, hv, hp⟩
  have hbase :=
    intervalIntegral_normSq_mrFiniteDyadicRamarePolynomial_le_partition
      hdisj hcover hlo hD f Z 1 hT
  calc
    (∫ t in -T..T,
        Complex.normSq (mrFiniteDyadicRamarePolynomial I f Z 1 t)) ≤
      2 * (V.card : ℝ) *
        ∑ v ∈ V,
          ((∫ t in -T..T, Complex.normSq
              (mrFinitePrimePerronPolynomial (D v) f 1 t *
                mrCofactorPerronPolynomial (primesInBlock I)
                  (mrDyadicCofactorRectangle (J v) Z) f 1 t)) +
            ∫ t in -T..T, Complex.normSq
              (mrFiniteRamareSubblockBoundaryPolynomial
                (primesInBlock I) (D v) (J v) f Z 1 t)) := hbase
    _ ≤ 2 * (V.card : ℝ) *
        ∑ v ∈ V,
          ((∫ t in -T..T, Complex.normSq
              (mrFinitePrimePerronPolynomial (D v) f 1 t *
                mrCofactorPerronPolynomial (primesInBlock I)
                  (mrDyadicCofactorRectangle (J v) Z) f 1 t)) +
            mrFiniteRamareSubblockBoundaryEnergyBound (J v) Z T) := by
      gcongr with v hv
      exact intervalIntegral_normSq_mrFiniteRamareSubblockBoundaryPolynomial_le
        hP (hDP v hv) (hlo v hv) (hJle v hv) (hJZ v hv)
          (hD v hv) hbound hT
    _ = 2 * (V.card : ℝ) *
        ((∑ v ∈ V,
            ∫ t in -T..T, Complex.normSq
              (mrFinitePrimePerronPolynomial (D v) f 1 t *
                mrCofactorPerronPolynomial (primesInBlock I)
                  (mrDyadicCofactorRectangle (J v) Z) f 1 t)) +
          ∑ v ∈ V,
            mrFiniteRamareSubblockBoundaryEnergyBound (J v) Z T) := by
      rw [Finset.sum_add_distrib]

end

end Erdos67
