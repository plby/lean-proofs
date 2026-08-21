import ErdosProblems.Erdos239.External.Erdos67.MRAppendixLargeValues
import ErdosProblems.Erdos239.External.Erdos67.MRCofactorPerron
import ErdosProblems.Erdos239.External.Erdos67.MRCommonCoefficient
import ErdosProblems.Erdos239.External.Erdos67.MRFiniteRamareFactorization

/-!
# Finite large values for a denominator-corrected Ramaré rectangle

The complete cofactor `LSeries` is the wrong object for the finite
Matomäki--Radziwiłł large-values argument: its absolute tail loses the
crucial inverse long scale.  This file works only with finite supports.

The corrected common denominator gives an especially economical version
of the argument.  The coefficient of the first prime--cofactor product has
norm at most `1/n`.  The remaining prime factors are then added with the
finite `l¹ * l²` Young inequality.  Consequently the square coefficient
mass retains the inverse square of the lower product scale.
-/

open scoped BigOperators ComplexConjugate Interval
open Finset

namespace Erdos67

noncomputable section

/-! ## Finite multiplicative convolution -/

/-- Products represented by a finite rectangle. -/
def natProductImage (A B : Finset ℕ) : Finset ℕ :=
  (A ×ˢ B).image fun x ↦ x.1 * x.2

/-- The fiber of a finite multiplication map. -/
def natProductFiber (A B : Finset ℕ) (n : ℕ) : Finset (ℕ × ℕ) :=
  (A ×ˢ B).filter fun x ↦ x.1 * x.2 = n

@[simp]
theorem mem_natProductFiber {A B : Finset ℕ} {n : ℕ} {x : ℕ × ℕ} :
    x ∈ natProductFiber A B n ↔
      x.1 ∈ A ∧ x.2 ∈ B ∧ x.1 * x.2 = n := by
  simp only [natProductFiber, Finset.mem_filter, Finset.mem_product]
  tauto

/-- Coefficient obtained by grouping a finite product by the integer
product of its two indices. -/
def finiteProductCoefficient
    (A B : Finset ℕ) (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ x ∈ natProductFiber A B n, a x.1 * b x.2

theorem natProductFiber_mapsTo_image (A B : Finset ℕ) :
    ∀ x ∈ A ×ˢ B, x.1 * x.2 ∈ natProductImage A B := by
  intro x hx
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- Finite weighted Young inequality in the precise form needed below. -/
theorem sum_normSq_finiteProductCoefficient_le
    (A B : Finset ℕ) (hApos : ∀ r ∈ A, 0 < r)
    (a b : ℕ → ℂ) :
    (∑ n ∈ natProductImage A B,
        Complex.normSq (finiteProductCoefficient A B a b n)) ≤
      (∑ r ∈ A, ‖a r‖) ^ 2 *
        ∑ s ∈ B, Complex.normSq (b s) := by
  classical
  let M : ℝ := ∑ r ∈ A, ‖a r‖
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hfiber (n : ℕ) :
      Complex.normSq (finiteProductCoefficient A B a b n) ≤
        M * ∑ x ∈ natProductFiber A B n,
          ‖a x.1‖ * Complex.normSq (b x.2) := by
    rw [Complex.normSq_eq_norm_sq]
    calc
      ‖finiteProductCoefficient A B a b n‖ ^ 2 ≤
          (∑ x ∈ natProductFiber A B n,
            ‖a x.1 * b x.2‖) ^ 2 := by
        gcongr
        exact norm_sum_le _ _
      _ ≤ (∑ x ∈ natProductFiber A B n, ‖a x.1‖) *
          ∑ x ∈ natProductFiber A B n,
            ‖a x.1‖ * ‖b x.2‖ ^ 2 := by
        have hnorm : (∑ x ∈ natProductFiber A B n,
            ‖a x.1 * b x.2‖) =
            ∑ x ∈ natProductFiber A B n, ‖a x.1‖ * ‖b x.2‖ := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [norm_mul]
        rw [hnorm]
        refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
          (natProductFiber A B n)
          (r := fun x ↦ ‖a x.1‖ * ‖b x.2‖)
          (f := fun x ↦ ‖a x.1‖)
          (g := fun x ↦ ‖a x.1‖ * ‖b x.2‖ ^ 2)
          (fun _ _ ↦ norm_nonneg _)
          (fun _ _ ↦ mul_nonneg (norm_nonneg _) (sq_nonneg _)) ?_
        intro x hx
        ring_nf
        exact le_rfl
      _ ≤ M * ∑ x ∈ natProductFiber A B n,
            ‖a x.1‖ * ‖b x.2‖ ^ 2 := by
        gcongr
        unfold M
        let F := natProductFiber A B n
        have hinj : Set.InjOn (fun x : ℕ × ℕ ↦ x.1) F := by
          intro x hx y hy hxy
          have hxmem := mem_natProductFiber.mp hx
          have hymem := mem_natProductFiber.mp hy
          have hxpos := hApos x.1 hxmem.1
          change x.1 = y.1 at hxy
          apply Prod.ext hxy
          apply Nat.eq_of_mul_eq_mul_left hxpos
          calc
            x.1 * x.2 = n := hxmem.2.2
            _ = y.1 * y.2 := hymem.2.2.symm
            _ = x.1 * y.2 := by rw [← hxy]
        change (∑ x ∈ F, ‖a x.1‖) ≤ ∑ r ∈ A, ‖a r‖
        rw [← Finset.sum_image (f := fun r ↦ ‖a r‖) hinj]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro r hr
          rcases Finset.mem_image.mp hr with ⟨x, hx, rfl⟩
          exact (mem_natProductFiber.mp hx).1
        · intro r hrA hrnot
          exact norm_nonneg _
      _ = M * ∑ x ∈ natProductFiber A B n,
            ‖a x.1‖ * Complex.normSq (b x.2) := by
        simp only [Complex.normSq_eq_norm_sq]
  calc
    (∑ n ∈ natProductImage A B,
        Complex.normSq (finiteProductCoefficient A B a b n)) ≤
        ∑ n ∈ natProductImage A B,
          M * ∑ x ∈ natProductFiber A B n,
            ‖a x.1‖ * Complex.normSq (b x.2) := by
      exact Finset.sum_le_sum fun n hn ↦ hfiber n
    _ = M * ∑ n ∈ natProductImage A B,
          ∑ x ∈ natProductFiber A B n,
            ‖a x.1‖ * Complex.normSq (b x.2) := by
      rw [Finset.mul_sum]
    _ = M * ∑ x ∈ A ×ˢ B,
          ‖a x.1‖ * Complex.normSq (b x.2) := by
      congr 1
      simpa only [natProductFiber] using
        (Finset.sum_fiberwise_of_maps_to
          (s := A ×ˢ B) (t := natProductImage A B)
          (g := fun x : ℕ × ℕ ↦ x.1 * x.2)
          (natProductFiber_mapsTo_image A B)
          (fun x ↦ ‖a x.1‖ * Complex.normSq (b x.2)))
    _ = M * ((∑ r ∈ A, ‖a r‖) *
          ∑ s ∈ B, Complex.normSq (b s)) := by
      congr 1
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_mul]
    _ = (∑ r ∈ A, ‖a r‖) ^ 2 *
          ∑ s ∈ B, Complex.normSq (b s) := by
      dsimp only [M]
      ring

/-! ## Polynomial grouping and mean value -/

theorem logarithmicDirichletPolynomial_mul_eq_product
    {A B : Finset ℕ}
    (hA : ∀ n ∈ A, 0 < n) (hB : ∀ n ∈ B, 0 < n)
    (a b : ℕ → ℂ) (t : ℝ) :
    logarithmicDirichletPolynomial A a t *
        logarithmicDirichletPolynomial B b t =
      logarithmicDirichletPolynomial (natProductImage A B)
        (finiteProductCoefficient A B a b) t := by
  classical
  unfold logarithmicDirichletPolynomial finiteProductCoefficient
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [show (∑ x ∈ A, ∑ y ∈ B,
      a x * logarithmicPhase x t * (b y * logarithmicPhase y t)) =
      ∑ z ∈ A ×ˢ B,
        (a z.1 * b z.2) * logarithmicPhase (z.1 * z.2) t by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    rw [logarithmicPhase_mul (hA x hx) (hB y hy)]
    ring]
  symm
  have hfiber := Finset.sum_fiberwise_of_maps_to
      (s := A ×ˢ B) (t := natProductImage A B)
      (g := fun x : ℕ × ℕ ↦ x.1 * x.2)
      (natProductFiber_mapsTo_image A B)
      (fun z ↦ (a z.1 * b z.2) *
        logarithmicPhase (z.1 * z.2) t)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  rw [(mem_natProductFiber.mp hz).2.2]

/-- Mean-value theorem on an arbitrary positive finite support bounded by
`N`. -/
theorem norm_logarithmicDirichletPolynomial_intervalIntegral_le
    {D : Finset ℕ} {N : ℕ} (hN : 0 < N)
    (hDpos : ∀ n ∈ D, 0 < n) (hDN : ∀ n ∈ D, n ≤ N)
    (a : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in -T..T,
        conj (logarithmicDirichletPolynomial D a t) *
          logarithmicDirichletPolynomial D a t‖ ≤
      (2 * T + 2 * Real.pi * (N : ℝ)) *
        ∑ n ∈ D, Complex.normSq (a n) := by
  let freq : ↑D → ℝ := fun n ↦ Real.log (n : ℕ)
  let coeff : ↑D → ℂ := fun n ↦ a n
  have hdelta : (0 : ℝ) < (N : ℝ)⁻¹ :=
    inv_pos.mpr (by exact_mod_cast hN)
  have hsep : ∀ r s : ↑D, r ≠ s →
      (N : ℝ)⁻¹ ≤ |freq r - freq s| := by
    intro r s hrs
    exact inv_nat_le_abs_log_sub_log
      (hDpos r r.property) (hDpos s s.property)
      (hDN r r.property) (hDN s s.property)
      (fun h ↦ hrs (Subtype.ext h))
  have hmean := norm_finiteFrequencyPolynomial_intervalIntegral_le
    freq coeff hT hdelta hsep
  have hpoly : finiteFrequencyPolynomial freq coeff =
      logarithmicDirichletPolynomial D a := by
    funext t
    unfold finiteFrequencyPolynomial logarithmicDirichletPolynomial
    rw [show (∑ n ∈ D, a n * logarithmicPhase n t) =
      ∑ n : ↑D, a n * logarithmicPhase n t by
        exact Finset.sum_subtype D (fun _ ↦ Iff.rfl)
          (fun n ↦ a n * logarithmicPhase n t)]
    apply Finset.sum_congr rfl
    intro n hn
    rfl
  rw [hpoly] at hmean
  simpa only [coeff, inv_inv, Complex.normSq_eq_norm_sq,
    Finset.sum_subtype D (fun _ ↦ Iff.rfl)
      (fun n ↦ ‖a n‖ ^ 2)] using hmean

/-! ## The line-one Ramaré rectangle -/

/-- Prime coefficient on the line `Re s = 1`. -/
def mrFinitePrimeLineCoefficient (f : ℕ → ℂ) (p : ℕ) : ℂ :=
  f p / (p : ℂ)

/-- Corrected denominator-weighted cofactor coefficient on `Re s = 1`. -/
def mrFiniteCofactorLineCoefficient
    (P : Finset ℕ) (f : ℕ → ℂ) (m : ℕ) : ℂ :=
  f m / ((mrCommonDenominator P m : ℂ) * (m : ℂ))

/-- Coefficient of a finite prime--cofactor rectangle on `Re s = 1`. -/
def mrFiniteRamareRectangleCoefficient
    (P S : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  finiteProductCoefficient P S (mrFinitePrimeLineCoefficient f)
    (mrFiniteCofactorLineCoefficient P f) n

/-- Rectangle coefficient for a narrow support `D`, while retaining the
common denominator belonging to the full selected prime set `P`. -/
def mrFiniteRamareSubblockRectangleCoefficient
    (P D S : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  finiteProductCoefficient D S (mrFinitePrimeLineCoefficient f)
    (mrFiniteCofactorLineCoefficient P f) n

theorem norm_mrFinitePrimeLineCoefficient_le
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {p : ℕ} (hp : 0 < p) :
    ‖mrFinitePrimeLineCoefficient f p‖ ≤ (p : ℝ)⁻¹ := by
  unfold mrFinitePrimeLineCoefficient
  rw [norm_div, Complex.norm_natCast, div_eq_mul_inv]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (hbound p hp) (inv_nonneg.mpr (by positivity))

/-- The corrected denominator makes every finite rectangular coefficient
no larger than the ordinary line-one weight `1/n`. -/
theorem norm_mrFiniteRamareRectangleCoefficient_le_inv
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (hSpos : ∀ m ∈ S, 0 < m) {n : ℕ} (hn : 0 < n) :
    ‖mrFiniteRamareRectangleCoefficient P S f n‖ ≤ (n : ℝ)⁻¹ := by
  classical
  let F := natProductFiber P S n
  by_cases hF : F.Nonempty
  · obtain ⟨x, hxF⟩ := hF
    have hx := mem_natProductFiber.mp hxF
    have hxprime : x.1.Prime := hP x.1 hx.1
    have hxpos : 0 < x.1 := hxprime.pos
    have hypos : 0 < x.2 := hSpos x.2 hx.2.1
    have hdiv : ∃ p ∈ P, p ∣ n :=
      ⟨x.1, hx.1, ⟨x.2, hx.2.2.symm⟩⟩
    have hcpos : 0 < primeDivisorCount P n := primeDivisorCount_pos hdiv
    let c : ℕ := primeDivisorCount P n
    have hterm (z : ℕ × ℕ) (hzF : z ∈ F) :
        ‖mrFinitePrimeLineCoefficient f z.1 *
            mrFiniteCofactorLineCoefficient P f z.2‖ ≤
          ((c : ℝ) * (n : ℝ))⁻¹ := by
      have hz := mem_natProductFiber.mp hzF
      have hzprime : z.1.Prime := hP z.1 hz.1
      have hzpos : 0 < z.1 := hzprime.pos
      have hwpos : 0 < z.2 := hSpos z.2 hz.2.1
      have hdenEq : ramareDenominator P z.1 z.2 = c := by
        dsimp only [c]
        rw [ramareDenominator_eq_primeDivisorCount_mul hP hz.1,
          hz.2.2]
      have hcommon : c ≤ mrCommonDenominator P z.2 := by
        rw [← hdenEq]
        exact ramareDenominator_le_mrCommonDenominator P z.1 z.2
      have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
      have hzR : (0 : ℝ) < z.1 := by exact_mod_cast hzpos
      have hwR : (0 : ℝ) < z.2 := by exact_mod_cast hwpos
      have hcommonR : (0 : ℝ) < mrCommonDenominator P z.2 := by
        exact_mod_cast (show 0 < mrCommonDenominator P z.2 by
          unfold mrCommonDenominator
          omega)
      have hpBound := norm_mrFinitePrimeLineCoefficient_le hbound hzpos
      have hmBound : ‖mrFiniteCofactorLineCoefficient P f z.2‖ ≤
          ((c : ℝ) * (z.2 : ℝ))⁻¹ := by
        unfold mrFiniteCofactorLineCoefficient
        rw [norm_div, norm_mul, Complex.norm_natCast,
          Complex.norm_natCast, div_eq_mul_inv]
        have hdenle : (c : ℝ) * (z.2 : ℝ) ≤
            (mrCommonDenominator P z.2 : ℝ) * (z.2 : ℝ) := by
          gcongr
        calc
          ‖f z.2‖ *
              ((mrCommonDenominator P z.2 : ℝ) * (z.2 : ℝ))⁻¹ ≤
              ((mrCommonDenominator P z.2 : ℝ) * (z.2 : ℝ))⁻¹ := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right
              (hbound z.2 hwpos) (inv_nonneg.mpr (by positivity))
          _ ≤ ((c : ℝ) * (z.2 : ℝ))⁻¹ := by
            exact inv_anti₀ (mul_pos hcR hwR) hdenle
      rw [norm_mul]
      calc
        ‖mrFinitePrimeLineCoefficient f z.1‖ *
            ‖mrFiniteCofactorLineCoefficient P f z.2‖ ≤
            (z.1 : ℝ)⁻¹ * ((c : ℝ) * (z.2 : ℝ))⁻¹ :=
          mul_le_mul hpBound hmBound (norm_nonneg _) (inv_nonneg.mpr (by positivity))
        _ = ((c : ℝ) * (n : ℝ))⁻¹ := by
          rw [← hz.2.2]
          push_cast
          field_simp
    have hinj : Set.InjOn (fun z : ℕ × ℕ ↦ z.1) F := by
      intro u hu v hv huv
      have hu' := mem_natProductFiber.mp hu
      have hv' := mem_natProductFiber.mp hv
      change u.1 = v.1 at huv
      apply Prod.ext huv
      apply Nat.eq_of_mul_eq_mul_left (hP u.1 hu'.1).pos
      calc
        u.1 * u.2 = n := hu'.2.2
        _ = v.1 * v.2 := hv'.2.2.symm
        _ = u.1 * v.2 := by rw [← huv]
    have hcardImage : F.card = (F.image fun z ↦ z.1).card := by
      exact (Finset.card_image_of_injOn hinj).symm
    have hsubset : (F.image fun z ↦ z.1) ⊆ primeDivisorSet P n := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨z, hzF, rfl⟩
      have hz := mem_natProductFiber.mp hzF
      exact mem_primeDivisorSet.mpr ⟨hz.1, ⟨z.2, hz.2.2.symm⟩⟩
    have hcard : F.card ≤ c := by
      rw [hcardImage]
      exact (Finset.card_le_card hsubset).trans_eq rfl
    unfold mrFiniteRamareRectangleCoefficient finiteProductCoefficient
    change ‖∑ z ∈ F, mrFinitePrimeLineCoefficient f z.1 *
      mrFiniteCofactorLineCoefficient P f z.2‖ ≤ _
    calc
      ‖∑ z ∈ F, mrFinitePrimeLineCoefficient f z.1 *
          mrFiniteCofactorLineCoefficient P f z.2‖ ≤
          ∑ _z ∈ F, (((c : ℝ) * (n : ℝ))⁻¹) := by
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun z hz ↦ hterm z hz)
      _ = (F.card : ℝ) * (((c : ℝ) * (n : ℝ))⁻¹) := by simp
      _ ≤ (c : ℝ) * (((c : ℝ) * (n : ℝ))⁻¹) := by
        gcongr
      _ = (n : ℝ)⁻¹ := by
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
        field_simp [hcR.ne']
  · have hzero : mrFiniteRamareRectangleCoefficient P S f n = 0 := by
      unfold mrFiniteRamareRectangleCoefficient finiteProductCoefficient
      change ∑ x ∈ F, mrFinitePrimeLineCoefficient f x.1 *
        mrFiniteCofactorLineCoefficient P f x.2 = 0
      rw [Finset.not_nonempty_iff_eq_empty.mp hF]
      simp
    rw [hzero, norm_zero]
    positivity

/-- The coefficient bound remains valid on a narrow prime subblock,
provided its primes belong to the full set used by the common denominator. -/
theorem norm_mrFiniteRamareSubblockRectangleCoefficient_le_inv
    {P D S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hDP : D ⊆ P)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (hSpos : ∀ m ∈ S, 0 < m) {n : ℕ} (hn : 0 < n) :
    ‖mrFiniteRamareSubblockRectangleCoefficient P D S f n‖ ≤
      (n : ℝ)⁻¹ := by
  classical
  let F := natProductFiber D S n
  by_cases hF : F.Nonempty
  · obtain ⟨x, hxF⟩ := hF
    have hx := mem_natProductFiber.mp hxF
    have hxP : x.1 ∈ P := hDP hx.1
    have hxprime : x.1.Prime := hP x.1 hxP
    have hxpos : 0 < x.1 := hxprime.pos
    have hdiv : ∃ p ∈ P, p ∣ n :=
      ⟨x.1, hxP, ⟨x.2, hx.2.2.symm⟩⟩
    have hcpos : 0 < primeDivisorCount P n := primeDivisorCount_pos hdiv
    let c : ℕ := primeDivisorCount P n
    have hterm (z : ℕ × ℕ) (hzF : z ∈ F) :
        ‖mrFinitePrimeLineCoefficient f z.1 *
            mrFiniteCofactorLineCoefficient P f z.2‖ ≤
          ((c : ℝ) * (n : ℝ))⁻¹ := by
      have hz := mem_natProductFiber.mp hzF
      have hzP : z.1 ∈ P := hDP hz.1
      have hzprime : z.1.Prime := hP z.1 hzP
      have hzpos : 0 < z.1 := hzprime.pos
      have hwpos : 0 < z.2 := hSpos z.2 hz.2.1
      have hdenEq : ramareDenominator P z.1 z.2 = c := by
        dsimp only [c]
        rw [ramareDenominator_eq_primeDivisorCount_mul hP hzP,
          hz.2.2]
      have hcommon : c ≤ mrCommonDenominator P z.2 := by
        rw [← hdenEq]
        exact ramareDenominator_le_mrCommonDenominator P z.1 z.2
      have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
      have hwR : (0 : ℝ) < z.2 := by exact_mod_cast hwpos
      have hpBound := norm_mrFinitePrimeLineCoefficient_le hbound hzpos
      have hmBound : ‖mrFiniteCofactorLineCoefficient P f z.2‖ ≤
          ((c : ℝ) * (z.2 : ℝ))⁻¹ := by
        unfold mrFiniteCofactorLineCoefficient
        rw [norm_div, norm_mul, Complex.norm_natCast,
          Complex.norm_natCast, div_eq_mul_inv]
        have hdenle : (c : ℝ) * (z.2 : ℝ) ≤
            (mrCommonDenominator P z.2 : ℝ) * (z.2 : ℝ) := by
          gcongr
        calc
          ‖f z.2‖ *
              ((mrCommonDenominator P z.2 : ℝ) * (z.2 : ℝ))⁻¹ ≤
              ((mrCommonDenominator P z.2 : ℝ) * (z.2 : ℝ))⁻¹ := by
            simpa only [one_mul] using mul_le_mul_of_nonneg_right
              (hbound z.2 hwpos) (inv_nonneg.mpr (by positivity))
          _ ≤ ((c : ℝ) * (z.2 : ℝ))⁻¹ := by
            exact inv_anti₀ (mul_pos hcR hwR) hdenle
      rw [norm_mul]
      calc
        ‖mrFinitePrimeLineCoefficient f z.1‖ *
            ‖mrFiniteCofactorLineCoefficient P f z.2‖ ≤
            (z.1 : ℝ)⁻¹ * ((c : ℝ) * (z.2 : ℝ))⁻¹ :=
          mul_le_mul hpBound hmBound (norm_nonneg _)
            (inv_nonneg.mpr (by positivity))
        _ = ((c : ℝ) * (n : ℝ))⁻¹ := by
          rw [← hz.2.2]
          push_cast
          field_simp
    have hinj : Set.InjOn (fun z : ℕ × ℕ ↦ z.1) F := by
      intro u hu v hv huv
      have hu' := mem_natProductFiber.mp hu
      have hv' := mem_natProductFiber.mp hv
      change u.1 = v.1 at huv
      apply Prod.ext huv
      apply Nat.eq_of_mul_eq_mul_left (hP u.1 (hDP hu'.1)).pos
      calc
        u.1 * u.2 = n := hu'.2.2
        _ = v.1 * v.2 := hv'.2.2.symm
        _ = u.1 * v.2 := by rw [← huv]
    have hcardImage : F.card = (F.image fun z ↦ z.1).card := by
      exact (Finset.card_image_of_injOn hinj).symm
    have hsubset : (F.image fun z ↦ z.1) ⊆ primeDivisorSet P n := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨z, hzF, rfl⟩
      have hz := mem_natProductFiber.mp hzF
      exact mem_primeDivisorSet.mpr
        ⟨hDP hz.1, ⟨z.2, hz.2.2.symm⟩⟩
    have hcard : F.card ≤ c := by
      rw [hcardImage]
      exact (Finset.card_le_card hsubset).trans_eq rfl
    unfold mrFiniteRamareSubblockRectangleCoefficient
      finiteProductCoefficient
    change ‖∑ z ∈ F, mrFinitePrimeLineCoefficient f z.1 *
      mrFiniteCofactorLineCoefficient P f z.2‖ ≤ _
    calc
      ‖∑ z ∈ F, mrFinitePrimeLineCoefficient f z.1 *
          mrFiniteCofactorLineCoefficient P f z.2‖ ≤
          ∑ _z ∈ F, (((c : ℝ) * (n : ℝ))⁻¹) := by
        exact (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun z hz ↦ hterm z hz)
      _ = (F.card : ℝ) * (((c : ℝ) * (n : ℝ))⁻¹) := by simp
      _ ≤ (c : ℝ) * (((c : ℝ) * (n : ℝ))⁻¹) := by
        gcongr
      _ = (n : ℝ)⁻¹ := by
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
        field_simp [hcR.ne']
  · have hzero :
        mrFiniteRamareSubblockRectangleCoefficient P D S f n = 0 := by
      unfold mrFiniteRamareSubblockRectangleCoefficient
        finiteProductCoefficient
      change ∑ x ∈ F, mrFinitePrimeLineCoefficient f x.1 *
        mrFiniteCofactorLineCoefficient P f x.2 = 0
      rw [Finset.not_nonempty_iff_eq_empty.mp hF]
      simp
    rw [hzero, norm_zero]
    positivity

/-- Square mass of a finite Ramaré rectangle.  The displayed denominator
is the retained inverse long scale; no complete `LSeries` or tail occurs. -/
theorem sum_normSq_mrFiniteRamareRectangleCoefficient_le
    {P S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (hSpos : ∀ m ∈ S, 0 < m)
    {L M : ℕ} (hL : 0 < L) (hM : 0 < M)
    (hPlow : ∀ p ∈ P, L ≤ p) (hSlow : ∀ m ∈ S, M ≤ m) :
    (∑ n ∈ natProductImage P S,
        Complex.normSq (mrFiniteRamareRectangleCoefficient P S f n)) ≤
      (((P.card * S.card : ℕ) : ℝ) / ((L * M : ℕ) : ℝ) ^ 2) := by
  classical
  have hLM : 0 < L * M := Nat.mul_pos hL hM
  have himagePos : ∀ n ∈ natProductImage P S, 0 < n := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨x, hx, rfl⟩
    have hx' := Finset.mem_product.mp hx
    exact Nat.mul_pos (hP x.1 hx'.1).pos (hSpos x.2 hx'.2)
  have hlower : ∀ n ∈ natProductImage P S, L * M ≤ n := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨x, hx, rfl⟩
    have hx' := Finset.mem_product.mp hx
    exact Nat.mul_le_mul (hPlow x.1 hx'.1) (hSlow x.2 hx'.2)
  calc
    (∑ n ∈ natProductImage P S,
        Complex.normSq (mrFiniteRamareRectangleCoefficient P S f n)) ≤
        ∑ _n ∈ natProductImage P S,
          ((((L * M : ℕ) : ℝ)⁻¹) ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Complex.normSq_eq_norm_sq]
      have hcoeff := norm_mrFiniteRamareRectangleCoefficient_le_inv
        hP hbound hSpos (himagePos n hn)
      have hinv : (n : ℝ)⁻¹ ≤ ((L * M : ℕ) : ℝ)⁻¹ := by
        apply inv_anti₀ (by exact_mod_cast hLM)
        exact_mod_cast hlower n hn
      exact pow_le_pow_left₀ (norm_nonneg _) (hcoeff.trans hinv) 2
    _ = ((natProductImage P S).card : ℝ) *
          ((((L * M : ℕ) : ℝ)⁻¹) ^ 2) := by simp
    _ ≤ ((P.card * S.card : ℕ) : ℝ) *
          ((((L * M : ℕ) : ℝ)⁻¹) ^ 2) := by
      gcongr
      exact (Finset.card_image_le.trans_eq (Finset.card_product P S))
    _ = ((P.card * S.card : ℕ) : ℝ) /
          ((L * M : ℕ) : ℝ) ^ 2 := by
      rw [div_eq_mul_inv, inv_pow]

/-- Square coefficient mass for a narrow support with a full denominator.
The inverse square of the lower product scale is unchanged. -/
theorem sum_normSq_mrFiniteRamareSubblockRectangleCoefficient_le
    {P D S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hDP : D ⊆ P)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (hSpos : ∀ m ∈ S, 0 < m)
    {L M : ℕ} (hL : 0 < L) (hM : 0 < M)
    (hDlow : ∀ p ∈ D, L ≤ p) (hSlow : ∀ m ∈ S, M ≤ m) :
    (∑ n ∈ natProductImage D S,
        Complex.normSq
          (mrFiniteRamareSubblockRectangleCoefficient P D S f n)) ≤
      (((D.card * S.card : ℕ) : ℝ) / ((L * M : ℕ) : ℝ) ^ 2) := by
  classical
  have hLM : 0 < L * M := Nat.mul_pos hL hM
  have himagePos : ∀ n ∈ natProductImage D S, 0 < n := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨x, hx, rfl⟩
    have hx' := Finset.mem_product.mp hx
    exact Nat.mul_pos (hP x.1 (hDP hx'.1)).pos (hSpos x.2 hx'.2)
  have hlower : ∀ n ∈ natProductImage D S, L * M ≤ n := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨x, hx, rfl⟩
    have hx' := Finset.mem_product.mp hx
    exact Nat.mul_le_mul (hDlow x.1 hx'.1) (hSlow x.2 hx'.2)
  calc
    (∑ n ∈ natProductImage D S,
        Complex.normSq
          (mrFiniteRamareSubblockRectangleCoefficient P D S f n)) ≤
        ∑ _n ∈ natProductImage D S,
          ((((L * M : ℕ) : ℝ)⁻¹) ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [Complex.normSq_eq_norm_sq]
      have hcoeff :=
        norm_mrFiniteRamareSubblockRectangleCoefficient_le_inv
          hP hDP hbound hSpos (himagePos n hn)
      have hinv : (n : ℝ)⁻¹ ≤ ((L * M : ℕ) : ℝ)⁻¹ := by
        apply inv_anti₀ (by exact_mod_cast hLM)
        exact_mod_cast hlower n hn
      exact pow_le_pow_left₀ (norm_nonneg _) (hcoeff.trans hinv) 2
    _ = ((natProductImage D S).card : ℝ) *
          ((((L * M : ℕ) : ℝ)⁻¹) ^ 2) := by simp
    _ ≤ ((D.card * S.card : ℕ) : ℝ) *
          ((((L * M : ℕ) : ℝ)⁻¹) ^ 2) := by
      gcongr
      exact (Finset.card_image_le.trans_eq (Finset.card_product D S))
    _ = ((D.card * S.card : ℕ) : ℝ) /
          ((L * M : ℕ) : ℝ) ^ 2 := by
      rw [div_eq_mul_inv, inv_pow]

theorem natCardRatio_le_sixteen_div
    {A B Z : ℕ} (hB : 0 < B) (hZ : 0 < Z)
    (hcard : A ≤ 4 * Z) (hscale : Z ≤ 2 * B) :
    ((A : ℝ) / (B : ℝ) ^ 2) ≤ 16 / (Z : ℝ) := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hZR : (0 : ℝ) < Z := by exact_mod_cast hZ
  have hcardR : (A : ℝ) ≤ 4 * (Z : ℝ) := by exact_mod_cast hcard
  have hscaleR : (Z : ℝ) ≤ 2 * (B : ℝ) := by exact_mod_cast hscale
  apply (div_le_div_iff₀ (sq_pos_of_pos hBR) hZR).2
  nlinarith [sq_nonneg ((Z : ℝ) - 2 * B)]

/-- On the genuine cofactor rectangle of a block with `U ≤ 2L`, the
corrected first-convolution square mass is at most `16/Z`. -/
theorem sum_normSq_mrFiniteRamareDyadicRectangleCoefficient_le
    {P D : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hDP : D ⊆ P)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {L U Z : ℕ} (hL : 0 < L) (hU : 0 < U) (hZ : 0 < Z)
    (hUL : U ≤ 2 * L)
    (hDlow : ∀ p ∈ D, L ≤ p) (hDup : ∀ p ∈ D, p ≤ U) :
    (∑ n ∈ natProductImage D (mrDyadicCofactorRectangle (L, U) Z),
        Complex.normSq
          (mrFiniteRamareSubblockRectangleCoefficient P D
            (mrDyadicCofactorRectangle (L, U) Z) f n)) ≤
      16 / (Z : ℝ) := by
  classical
  let S := mrDyadicCofactorRectangle (L, U) Z
  let M := Z / U + 1
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    have hm' : Z / U < m := by
      simpa only [S, mrDyadicCofactorRectangle] using
        (Finset.mem_Ioc.mp hm).1
    exact (Nat.zero_le _).trans_lt hm'
  have hM : 0 < M := by
    exact Nat.succ_pos _
  have hSlow : ∀ m ∈ S, M ≤ m := by
    intro m hm
    have hm' : Z / U < m := by
      simpa only [S, mrDyadicCofactorRectangle] using
        (Finset.mem_Ioc.mp hm).1
    exact Nat.succ_le_iff.mpr hm'
  have hmass :=
    sum_normSq_mrFiniteRamareSubblockRectangleCoefficient_le
      hP hDP hbound hSpos hL hM hDlow hSlow
  have hDpos : ∀ p ∈ D, 0 < p := fun p hp ↦
    hL.trans_le (hDlow p hp)
  have hDsubset : D ⊆ Finset.Icc 1 U := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨hDpos p hp, hDup p hp⟩
  have hDcard : D.card ≤ U := by
    calc
      D.card ≤ (Finset.Icc 1 U).card := Finset.card_le_card hDsubset
      _ = U := by rw [Nat.card_Icc]; omega
  have hScard : S.card ≤ (2 * Z) / L := by
    dsimp only [S, mrDyadicCofactorRectangle]
    rw [Nat.card_Ioc]
    exact Nat.sub_le _ _
  have hdiv : L * ((2 * Z) / L) ≤ 2 * Z := Nat.mul_div_le _ _
  have hcard : D.card * S.card ≤ 4 * Z := by
    calc
      D.card * S.card ≤ U * ((2 * Z) / L) :=
        Nat.mul_le_mul hDcard hScard
      _ ≤ (2 * L) * ((2 * Z) / L) :=
        Nat.mul_le_mul_right _ hUL
      _ = 2 * (L * ((2 * Z) / L)) := by ring
      _ ≤ 2 * (2 * Z) := Nat.mul_le_mul_left 2 hdiv
      _ = 4 * Z := by omega
  have hZUM : Z ≤ U * M := by
    exact (Nat.lt_mul_div_succ Z hU).le
  have hscale : Z ≤ 2 * (L * M) := by
    calc
      Z ≤ U * M := hZUM
      _ ≤ (2 * L) * M := Nat.mul_le_mul_right M hUL
      _ = 2 * (L * M) := by ring
  exact hmass.trans (natCardRatio_le_sixteen_div
    (Nat.mul_pos hL hM) hZ hcard hscale)

/-- Arithmetic form of the preceding `1/Z` scale, separated for use in
the final vertical-energy estimate. -/
theorem mrDyadicCofactorRectangle_cardRatio_le
    {D : Finset ℕ} {L U Z : ℕ}
    (hL : 0 < L) (hU : 0 < U) (hZ : 0 < Z) (hUL : U ≤ 2 * L)
    (hDlow : ∀ p ∈ D, L ≤ p) (hDup : ∀ p ∈ D, p ≤ U) :
    (((D.card * (mrDyadicCofactorRectangle (L, U) Z).card : ℕ) : ℝ) /
        ((L * (Z / U + 1) : ℕ) : ℝ) ^ 2) ≤
      16 / (Z : ℝ) := by
  classical
  let S := mrDyadicCofactorRectangle (L, U) Z
  let M := Z / U + 1
  have hDpos : ∀ p ∈ D, 0 < p := fun p hp ↦
    hL.trans_le (hDlow p hp)
  have hDsubset : D ⊆ Finset.Icc 1 U := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨hDpos p hp, hDup p hp⟩
  have hDcard : D.card ≤ U := by
    calc
      D.card ≤ (Finset.Icc 1 U).card := Finset.card_le_card hDsubset
      _ = U := by rw [Nat.card_Icc]; omega
  have hScard : S.card ≤ (2 * Z) / L := by
    dsimp only [S, mrDyadicCofactorRectangle]
    rw [Nat.card_Ioc]
    exact Nat.sub_le _ _
  have hdiv : L * ((2 * Z) / L) ≤ 2 * Z := Nat.mul_div_le _ _
  have hcard : D.card * S.card ≤ 4 * Z := by
    calc
      D.card * S.card ≤ U * ((2 * Z) / L) :=
        Nat.mul_le_mul hDcard hScard
      _ ≤ (2 * L) * ((2 * Z) / L) :=
        Nat.mul_le_mul_right _ hUL
      _ = 2 * (L * ((2 * Z) / L)) := by ring
      _ ≤ 2 * (2 * Z) := Nat.mul_le_mul_left 2 hdiv
      _ = 4 * Z := by omega
  have hM : 0 < M := Nat.succ_pos _
  have hZUM : Z ≤ U * M := (Nat.lt_mul_div_succ Z hU).le
  have hscale : Z ≤ 2 * (L * M) := by
    calc
      Z ≤ U * M := hZUM
      _ ≤ (2 * L) * M := Nat.mul_le_mul_right M hUL
      _ = 2 * (L * M) := by ring
  simpa only [S, M] using natCardRatio_le_sixteen_div
    (Nat.mul_pos hL hM) hZ hcard hscale

/-- The `l¹` mass of a grouped prime power is bounded by the corresponding
power of the original prime `l¹` mass. -/
theorem sum_norm_primePowerCoefficient_le
    {P : Finset ℕ} (hPpos : ∀ p ∈ P, 0 < p)
    {N k : ℕ} (hPN : ∀ p ∈ P, p ≤ N) (a : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 1 (N ^ k),
        ‖primePowerCoefficient P a k n‖) ≤
      (∑ p ∈ P, ‖a p‖) ^ k := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 (N ^ k),
        ‖primePowerCoefficient P a k n‖) ≤
        ∑ n ∈ Finset.Icc 1 (N ^ k),
          ∑ v ∈ primeTupleProductFiber P k n,
            ‖tupleFromCoefficient a v‖ := by
      apply Finset.sum_le_sum
      intro n hn
      unfold primePowerCoefficient
      exact norm_sum_le _ _
    _ = ∑ v : TupleFrom P k, ‖tupleFromCoefficient a v‖ := by
      simpa only [primeTupleProductFiber] using
        (Finset.sum_fiberwise_of_maps_to
          (s := (Finset.univ : Finset (TupleFrom P k)))
          (t := Finset.Icc 1 (N ^ k))
          (g := tupleFromProduct)
          (fun v hv ↦ Finset.mem_Icc.mpr
            ⟨tupleFromProduct_pos hPpos v,
              tupleFromProduct_le_pow hPN v⟩)
          (fun v ↦ ‖tupleFromCoefficient a v‖))
    _ = (∑ p ∈ P, ‖a p‖) ^ k := by
      rw [show (∑ p ∈ P, ‖a p‖) =
          ∑ p : {p // p ∈ P}, ‖a p‖ by
        exact Finset.sum_subtype P (fun _ ↦ Iff.rfl) (fun p ↦ ‖a p‖),
        Fintype.sum_pow]
      apply Finset.sum_congr rfl
      intro v hv
      simp only [tupleFromCoefficient, tupleCoefficient, norm_prod]

theorem sum_norm_mrFinitePrimeLineCoefficient_le
    {P : Finset ℕ} (hPpos : ∀ p ∈ P, 0 < p)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) :
    (∑ p ∈ P, ‖mrFinitePrimeLineCoefficient f p‖) ≤
      ∑ p ∈ P, (p : ℝ)⁻¹ := by
  exact Finset.sum_le_sum fun p hp ↦
    norm_mrFinitePrimeLineCoefficient_le hbound (hPpos p hp)

/-! ## Vertical energy with the long scale retained -/

/-- A corrected prime--cofactor rectangle, multiplied by `j` further
copies of its narrow prime polynomial. -/
def mrFiniteRamarePowerRectanglePolynomial
    (P D S : Finset ℕ) (f : ℕ → ℂ) (j : ℕ) (t : ℝ) : ℂ :=
  logarithmicDirichletPolynomial D (mrFinitePrimeLineCoefficient f) t ^ j *
    (logarithmicDirichletPolynomial D (mrFinitePrimeLineCoefficient f) t *
      logarithmicDirichletPolynomial S
        (mrFiniteCofactorLineCoefficient P f) t)

/-- Finite-product mean value for a denominator-corrected Ramaré
rectangle.  The first prime copy is paired with the cofactor before Young's
inequality is applied; this is what preserves the inverse long scale. -/
theorem norm_mrFiniteRamarePowerRectanglePolynomial_intervalIntegral_le
    {P D S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hDP : D ⊆ P)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (hSpos : ∀ m ∈ S, 0 < m)
    {L M U V j : ℕ} (hL : 0 < L) (hM : 0 < M)
    (hU : 0 < U) (hV : 0 < V)
    (hDlow : ∀ p ∈ D, L ≤ p) (hDup : ∀ p ∈ D, p ≤ U)
    (hSlow : ∀ m ∈ S, M ≤ m) (hSup : ∀ m ∈ S, m ≤ V)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in -T..T,
        conj (mrFiniteRamarePowerRectanglePolynomial P D S f j t) *
          mrFiniteRamarePowerRectanglePolynomial P D S f j t‖ ≤
      (2 * T + 2 * Real.pi *
          (((U ^ j) * (U * V) : ℕ) : ℝ)) *
        ((∑ p ∈ D, (p : ℝ)⁻¹) ^ (2 * j) *
          (((D.card * S.card : ℕ) : ℝ) /
            ((L * M : ℕ) : ℝ) ^ 2)) := by
  classical
  let A := Finset.Icc 1 (U ^ j)
  let B := natProductImage D S
  let a := primePowerCoefficient D (mrFinitePrimeLineCoefficient f) j
  let b := mrFiniteRamareSubblockRectangleCoefficient P D S f
  let C := natProductImage A B
  let c := finiteProductCoefficient A B a b
  let N : ℕ := (U ^ j) * (U * V)
  have hDprime : ∀ p ∈ D, p.Prime := fun p hp ↦ hP p (hDP hp)
  have hDpos : ∀ p ∈ D, 0 < p := fun p hp ↦ (hDprime p hp).pos
  have hApos : ∀ n ∈ A, 0 < n := by
    intro n hn
    exact (Finset.mem_Icc.mp hn).1
  have hAup : ∀ n ∈ A, n ≤ U ^ j := by
    intro n hn
    exact (Finset.mem_Icc.mp hn).2
  have hBpos : ∀ n ∈ B, 0 < n := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨x, hx, rfl⟩
    have hx' := Finset.mem_product.mp hx
    exact Nat.mul_pos (hDpos x.1 hx'.1) (hSpos x.2 hx'.2)
  have hBup : ∀ n ∈ B, n ≤ U * V := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨x, hx, rfl⟩
    have hx' := Finset.mem_product.mp hx
    exact Nat.mul_le_mul (hDup x.1 hx'.1) (hSup x.2 hx'.2)
  have hN : 0 < N := by
    dsimp only [N]
    exact Nat.mul_pos (pow_pos hU j) (Nat.mul_pos hU hV)
  have hCup : ∀ n ∈ C, n ≤ N := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨x, hx, rfl⟩
    have hx' := Finset.mem_product.mp hx
    exact Nat.mul_le_mul (hAup x.1 hx'.1) (hBup x.2 hx'.2)
  have hCpos : ∀ n ∈ C, 0 < n := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨x, hx, rfl⟩
    have hx' := Finset.mem_product.mp hx
    exact Nat.mul_pos (hApos x.1 hx'.1) (hBpos x.2 hx'.2)
  have hrect (t : ℝ) :
      logarithmicDirichletPolynomial D (mrFinitePrimeLineCoefficient f) t *
          logarithmicDirichletPolynomial S
            (mrFiniteCofactorLineCoefficient P f) t =
        logarithmicDirichletPolynomial B b t := by
    exact logarithmicDirichletPolynomial_mul_eq_product
      hDpos hSpos (mrFinitePrimeLineCoefficient f)
        (mrFiniteCofactorLineCoefficient P f) t
  have hpoly (t : ℝ) :
      mrFiniteRamarePowerRectanglePolynomial P D S f j t =
        logarithmicDirichletPolynomial C c t := by
    unfold mrFiniteRamarePowerRectanglePolynomial
    rw [logarithmicDirichletPolynomial_pow_eq_groupedPrimePowerPolynomial
      hDprime hDup, hrect]
    change logarithmicDirichletPolynomial A a t *
        logarithmicDirichletPolynomial B b t = _
    exact logarithmicDirichletPolynomial_mul_eq_product
      hApos hBpos a b t
  have hmean := norm_logarithmicDirichletPolynomial_intervalIntegral_le
    hN hCpos hCup c hT
  have hrectMass :=
    sum_normSq_mrFiniteRamareSubblockRectangleCoefficient_le
      hP hDP hbound hSpos hL hM hDlow hSlow
  have hpowerL1 := sum_norm_primePowerCoefficient_le
    (k := j) (N := U) hDpos hDup (mrFinitePrimeLineCoefficient f)
  have hprimeL1 := sum_norm_mrFinitePrimeLineCoefficient_le
    hDpos hbound
  have hpowerL1' :
      (∑ n ∈ A, ‖a n‖) ≤
        (∑ p ∈ D, (p : ℝ)⁻¹) ^ j := by
    exact hpowerL1.trans (pow_le_pow_left₀
      (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) hprimeL1 j)
  have hconv := sum_normSq_finiteProductCoefficient_le
    A B hApos a b
  have hmass :
      (∑ n ∈ C, Complex.normSq (c n)) ≤
        (∑ p ∈ D, (p : ℝ)⁻¹) ^ (2 * j) *
          (((D.card * S.card : ℕ) : ℝ) /
            ((L * M : ℕ) : ℝ) ^ 2) := by
    calc
      (∑ n ∈ C, Complex.normSq (c n)) ≤
          (∑ n ∈ A, ‖a n‖) ^ 2 *
            ∑ n ∈ B, Complex.normSq (b n) := hconv
      _ ≤ ((∑ p ∈ D, (p : ℝ)⁻¹) ^ j) ^ 2 *
          (((D.card * S.card : ℕ) : ℝ) /
            ((L * M : ℕ) : ℝ) ^ 2) := by
        exact mul_le_mul
          (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
            hpowerL1' 2)
          hrectMass
          (Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _)
          (sq_nonneg _)
      _ = (∑ p ∈ D, (p : ℝ)⁻¹) ^ (2 * j) *
          (((D.card * S.card : ℕ) : ℝ) /
            ((L * M : ℕ) : ℝ) ^ 2) := by
        rw [Nat.mul_comm 2 j, pow_mul]
  have hintegral :
      (∫ t in -T..T,
        conj (mrFiniteRamarePowerRectanglePolynomial P D S f j t) *
          mrFiniteRamarePowerRectanglePolynomial P D S f j t) =
        ∫ t in -T..T,
          conj (logarithmicDirichletPolynomial C c t) *
            logarithmicDirichletPolynomial C c t := by
    apply intervalIntegral.integral_congr
    intro t ht
    change conj (mrFiniteRamarePowerRectanglePolynomial P D S f j t) *
        mrFiniteRamarePowerRectanglePolynomial P D S f j t = _
    rw [hpoly]
  rw [hintegral]
  calc
    ‖∫ t in -T..T,
        conj (logarithmicDirichletPolynomial C c t) *
          logarithmicDirichletPolynomial C c t‖ ≤
        (2 * T + 2 * Real.pi * (N : ℝ)) *
          ∑ n ∈ C, Complex.normSq (c n) := hmean
    _ ≤ (2 * T + 2 * Real.pi * (N : ℝ)) *
        ((∑ p ∈ D, (p : ℝ)⁻¹) ^ (2 * j) *
          (((D.card * S.card : ℕ) : ℝ) /
            ((L * M : ℕ) : ℝ) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by rfl

/-! ## Connection with the finite Ramaré factorisation API -/

theorem weightedPrimeCoefficient_one_eq_mrFinitePrimeLineCoefficient
    (f : ℕ → ℂ) (p : ℕ) :
    weightedPrimeCoefficient f 1 p = mrFinitePrimeLineCoefficient f p := by
  unfold weightedPrimeCoefficient mrFinitePrimeLineCoefficient
  rw [Real.rpow_neg_one, Complex.ofReal_inv, Complex.ofReal_natCast]
  ring

theorem mrCofactorPerronPolynomial_one_eq_linePolynomial
    (P S : Finset ℕ) (f : ℕ → ℂ) (t : ℝ) :
    mrCofactorPerronPolynomial P S f 1 t =
      logarithmicDirichletPolynomial S
        (mrFiniteCofactorLineCoefficient P f) (-t) := by
  unfold mrCofactorPerronPolynomial mrFiniteCofactorLineCoefficient
  apply Finset.sum_congr rfl
  intro n hn
  change (f n / (mrCommonDenominator P n : ℂ) *
      Complex.ofReal ((n : ℝ) ^ (-(1 : ℝ)))) *
      logarithmicPhase n (-t) =
    (f n / ((mrCommonDenominator P n : ℂ) * (n : ℂ))) *
      logarithmicPhase n (-t)
  rw [Real.rpow_neg_one, Complex.ofReal_inv, Complex.ofReal_natCast]
  ring

theorem mrFinitePrimePerronPolynomial_one_eq_linePolynomial
    (D : Finset ℕ) (f : ℕ → ℂ) (t : ℝ) :
    mrFinitePrimePerronPolynomial D f 1 t =
      logarithmicDirichletPolynomial D
        (mrFinitePrimeLineCoefficient f) (-t) := by
  unfold mrFinitePrimePerronPolynomial logarithmicDirichletPolynomial
  apply Finset.sum_congr rfl
  intro p hp
  rw [weightedPrimeCoefficient_one_eq_mrFinitePrimeLineCoefficient]

/-- The source-shaped product `Q^(j+1) R`, with the full denominator set
`P` kept in `R`. -/
def mrFiniteRamareSubblockPowerProduct
    (P D S : Finset ℕ) (f : ℕ → ℂ) (j : ℕ) (t : ℝ) : ℂ :=
  mrFinitePrimePerronPolynomial D f 1 t ^ (j + 1) *
    mrCofactorPerronPolynomial P S f 1 t

theorem mrFiniteRamareSubblockPowerProduct_eq_powerRectangle_neg
    (P D S : Finset ℕ) (f : ℕ → ℂ) (j : ℕ) (t : ℝ) :
    mrFiniteRamareSubblockPowerProduct P D S f j t =
      mrFiniteRamarePowerRectanglePolynomial P D S f j (-t) := by
  unfold mrFiniteRamareSubblockPowerProduct
    mrFiniteRamarePowerRectanglePolynomial
  rw [mrFinitePrimePerronPolynomial_one_eq_linePolynomial,
    mrCofactorPerronPolynomial_one_eq_linePolynomial, pow_succ]
  ring

/-- The finite vertical-energy theorem in the notation of the exact
factorisation module. -/
theorem norm_mrFiniteRamareSubblockPowerProduct_intervalIntegral_le
    {P D S : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hDP : D ⊆ P)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (hSpos : ∀ m ∈ S, 0 < m)
    {L M U V j : ℕ} (hL : 0 < L) (hM : 0 < M)
    (hU : 0 < U) (hV : 0 < V)
    (hDlow : ∀ p ∈ D, L ≤ p) (hDup : ∀ p ∈ D, p ≤ U)
    (hSlow : ∀ m ∈ S, M ≤ m) (hSup : ∀ m ∈ S, m ≤ V)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in -T..T,
        conj (mrFiniteRamareSubblockPowerProduct P D S f j t) *
          mrFiniteRamareSubblockPowerProduct P D S f j t‖ ≤
      (2 * T + 2 * Real.pi *
          (((U ^ j) * (U * V) : ℕ) : ℝ)) *
        ((∑ p ∈ D, (p : ℝ)⁻¹) ^ (2 * j) *
          (((D.card * S.card : ℕ) : ℝ) /
            ((L * M : ℕ) : ℝ) ^ 2)) := by
  have hflip :
      (∫ t in -T..T,
        conj (mrFiniteRamareSubblockPowerProduct P D S f j t) *
          mrFiniteRamareSubblockPowerProduct P D S f j t) =
        ∫ t in -T..T,
          conj (mrFiniteRamarePowerRectanglePolynomial P D S f j t) *
            mrFiniteRamarePowerRectanglePolynomial P D S f j t := by
    simp_rw [mrFiniteRamareSubblockPowerProduct_eq_powerRectangle_neg]
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (a := -T) (b := T)
        (fun t ↦
          conj (mrFiniteRamarePowerRectanglePolynomial P D S f j t) *
            mrFiniteRamarePowerRectanglePolynomial P D S f j t))
  rw [hflip]
  exact norm_mrFiniteRamarePowerRectanglePolynomial_intervalIntegral_le
    hP hDP hbound hSpos hL hM hU hV hDlow hDup hSlow hSup hT

/-- Source-scale specialization.  For the genuine rectangle
`Z/U < m ≤ 2Z/L` and a block of multiplicative width at most two, the
long contribution is explicitly `16/Z`. -/
theorem norm_mrFiniteRamareSubblockPowerProduct_dyadic_intervalIntegral_le
    {P D : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hDP : D ⊆ P)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {L U Z j : ℕ} (hL : 0 < L) (hU : 0 < U) (hZ : 0 < Z)
    (hLZ : L ≤ Z) (hUL : U ≤ 2 * L)
    (hDlow : ∀ p ∈ D, L ≤ p) (hDup : ∀ p ∈ D, p ≤ U)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ t in -T..T,
        conj (mrFiniteRamareSubblockPowerProduct P D
          (mrDyadicCofactorRectangle (L, U) Z) f j t) *
        mrFiniteRamareSubblockPowerProduct P D
          (mrDyadicCofactorRectangle (L, U) Z) f j t‖ ≤
      (2 * T + 2 * Real.pi *
          (((U ^ j) * (U * ((2 * Z) / L)) : ℕ) : ℝ)) *
        ((∑ p ∈ D, (p : ℝ)⁻¹) ^ (2 * j) *
          (16 / (Z : ℝ))) := by
  let S := mrDyadicCofactorRectangle (L, U) Z
  let M := Z / U + 1
  let V := (2 * Z) / L
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    have hm' : Z / U < m := by
      simpa only [S, mrDyadicCofactorRectangle] using
        (Finset.mem_Ioc.mp hm).1
    exact (Nat.zero_le _).trans_lt hm'
  have hM : 0 < M := Nat.succ_pos _
  have hV : 0 < V := by
    dsimp only [V]
    exact Nat.div_pos (by omega) hL
  have hSlow : ∀ m ∈ S, M ≤ m := by
    intro m hm
    have hm' : Z / U < m := by
      simpa only [S, mrDyadicCofactorRectangle] using
        (Finset.mem_Ioc.mp hm).1
    exact Nat.succ_le_iff.mpr hm'
  have hSup : ∀ m ∈ S, m ≤ V := by
    intro m hm
    simpa only [S, V, mrDyadicCofactorRectangle] using
      (Finset.mem_Ioc.mp hm).2
  have hbase :=
    norm_mrFiniteRamareSubblockPowerProduct_intervalIntegral_le
      (P := P) (D := D) (S := S) (L := L) (M := M)
      (U := U) (V := V) (j := j)
      hP hDP hbound hSpos hL hM hU hV hDlow hDup hSlow hSup hT
  have hratio := mrDyadicCofactorRectangle_cardRatio_le
    (D := D) hL hU hZ hUL hDlow hDup
  have hDpos : ∀ p ∈ D, 0 < p := fun p hp ↦
    hL.trans_le (hDlow p hp)
  have hprimeNonneg : 0 ≤ ∑ p ∈ D, (p : ℝ)⁻¹ :=
    Finset.sum_nonneg fun p hp ↦ inv_nonneg.mpr (by
      exact_mod_cast (Nat.zero_le p))
  calc
    ‖∫ t in -T..T,
        conj (mrFiniteRamareSubblockPowerProduct P D S f j t) *
          mrFiniteRamareSubblockPowerProduct P D S f j t‖ ≤
        (2 * T + 2 * Real.pi *
            (((U ^ j) * (U * V) : ℕ) : ℝ)) *
          ((∑ p ∈ D, (p : ℝ)⁻¹) ^ (2 * j) *
            (((D.card * S.card : ℕ) : ℝ) /
              ((L * M : ℕ) : ℝ) ^ 2)) := hbase
    _ ≤ (2 * T + 2 * Real.pi *
            (((U ^ j) * (U * V) : ℕ) : ℝ)) *
          ((∑ p ∈ D, (p : ℝ)⁻¹) ^ (2 * j) *
            (16 / (Z : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left
        (by simpa only [S, M] using hratio)
        (pow_nonneg hprimeNonneg _)
    _ = _ := by rfl

theorem intervalIntegral_normSq_eq_norm_intervalIntegral_conj_mul
    (F : ℝ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, Complex.normSq (F t)) =
      ‖∫ t in -T..T, conj (F t) * F t‖ := by
  have hident :
      (∫ t in -T..T, conj (F t) * F t) =
        ∫ t in -T..T, ((Complex.normSq (F t) : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact Complex.normSq_eq_conj_mul_self.symm
  have hnonneg : 0 ≤ ∫ t in -T..T, Complex.normSq (F t) := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro t ht
    exact Complex.normSq_nonneg _
  calc
    (∫ t in -T..T, Complex.normSq (F t)) =
        ‖((∫ t in -T..T, Complex.normSq (F t) : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = ‖∫ t in -T..T,
          ((Complex.normSq (F t) : ℝ) : ℂ)‖ := by
      rw [intervalIntegral.integral_ofReal]
    _ = ‖∫ t in -T..T, conj (F t) * F t‖ := by rw [hident]

/-- Real square-energy form, directly consumable by the finite dyadic
partition inequality. -/
theorem intervalIntegral_normSq_mrFiniteRamareSubblockPowerProduct_dyadic_le
    {P D : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hDP : D ⊆ P)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {L U Z j : ℕ} (hL : 0 < L) (hU : 0 < U) (hZ : 0 < Z)
    (hLZ : L ≤ Z) (hUL : U ≤ 2 * L)
    (hDlow : ∀ p ∈ D, L ≤ p) (hDup : ∀ p ∈ D, p ≤ U)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, Complex.normSq
      (mrFiniteRamareSubblockPowerProduct P D
        (mrDyadicCofactorRectangle (L, U) Z) f j t)) ≤
      (2 * T + 2 * Real.pi *
          (((U ^ j) * (U * ((2 * Z) / L)) : ℕ) : ℝ)) *
        ((∑ p ∈ D, (p : ℝ)⁻¹) ^ (2 * j) *
          (16 / (Z : ℝ))) := by
  rw [intervalIntegral_normSq_eq_norm_intervalIntegral_conj_mul _ hT]
  exact norm_mrFiniteRamareSubblockPowerProduct_dyadic_intervalIntegral_le
    hP hDP hbound hL hU hZ hLZ hUL hDlow hDup hT

/-! ## Bad-frequency restriction -/

theorem normSq_mul_le_inv_pow_mul_normSq_power_mul
    {z w : ℂ} {W : ℝ} (hW : 0 < W) (hz : W ≤ ‖z‖) (j : ℕ) :
    Complex.normSq (z * w) ≤
      (W ^ (2 * j))⁻¹ * Complex.normSq (z ^ (j + 1) * w) := by
  have hWpow : 0 < W ^ (2 * j) := pow_pos hW _
  have hzpow : W ^ (2 * j) ≤ ‖z‖ ^ (2 * j) :=
    pow_le_pow_left₀ hW.le hz _
  have hrhs :
      (W ^ (2 * j))⁻¹ * Complex.normSq (z ^ (j + 1) * w) =
        Complex.normSq (z ^ (j + 1) * w) / W ^ (2 * j) := by
    rw [div_eq_mul_inv, mul_comm]
  rw [hrhs]
  apply (le_div_iff₀ hWpow).2
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    norm_mul, norm_mul, norm_pow]
  calc
    (‖z‖ * ‖w‖) ^ 2 * W ^ (2 * j) ≤
        (‖z‖ * ‖w‖) ^ 2 * ‖z‖ ^ (2 * j) :=
      mul_le_mul_of_nonneg_left hzpow (sq_nonneg _)
    _ = (‖z‖ ^ (j + 1) * ‖w‖) ^ 2 := by
      rw [Nat.mul_comm 2 j, pow_mul, pow_succ]
      ring

/-- Square energy of the first rectangle on frequencies where its narrow
prime factor is at least `W`. -/
def mrFiniteRamareSubblockBadFrequencyEnergy
    (P D S : Finset ℕ) (f : ℕ → ℂ) (T W : ℝ) : ℝ :=
  ∫ t in -T..T,
    ({t : ℝ | W ≤ ‖mrFinitePrimePerronPolynomial D f 1 t‖}.indicator
      (fun t ↦ Complex.normSq
        (mrFinitePrimePerronPolynomial D f 1 t *
          mrCofactorPerronPolynomial P S f 1 t))) t

/-- On the bad set, `j` extra prime copies pay exactly `W^(-2j)`. -/
theorem mrFiniteRamareSubblockBadFrequencyEnergy_le_power
    {P D S : Finset ℕ} {f : ℕ → ℂ}
    {T W : ℝ} (hT : 0 ≤ T) (hW : 0 < W) (j : ℕ) :
    mrFiniteRamareSubblockBadFrequencyEnergy P D S f T W ≤
      (W ^ (2 * j))⁻¹ *
        ∫ t in -T..T, Complex.normSq
          (mrFiniteRamareSubblockPowerProduct P D S f j t) := by
  let Q : ℝ → ℂ := mrFinitePrimePerronPolynomial D f 1
  let R : ℝ → ℂ := mrCofactorPerronPolynomial P S f 1
  let bad : Set ℝ := {t | W ≤ ‖Q t‖}
  let base : ℝ → ℝ := fun t ↦ Complex.normSq (Q t * R t)
  let high : ℝ → ℝ := fun t ↦
    Complex.normSq (mrFiniteRamareSubblockPowerProduct P D S f j t)
  let major : ℝ → ℝ := fun t ↦ (W ^ (2 * j))⁻¹ * high t
  have hQ : Continuous Q :=
    continuous_mrFinitePrimePerronPolynomial D f 1
  have hR : Continuous R :=
    continuous_mrFiniteCofactorPerronPolynomial P S f 1
  have hbad : MeasurableSet bad := by
    exact measurableSet_le measurable_const hQ.norm.measurable
  have hbase : Continuous base := by
    have hbaseEq : base = fun t ↦ ‖Q t * R t‖ ^ 2 := by
      funext t
      dsimp only [base]
      rw [Complex.normSq_eq_norm_sq]
    rw [hbaseEq]
    exact (hQ.mul hR).norm.pow 2
  have hpower : Continuous
      (mrFiniteRamareSubblockPowerProduct P D S f j) := by
    unfold mrFiniteRamareSubblockPowerProduct
    exact (hQ.pow _).mul hR
  have hhigh : Continuous high := by
    have hhighEq : high = fun t ↦
        ‖mrFiniteRamareSubblockPowerProduct P D S f j t‖ ^ 2 := by
      funext t
      dsimp only [high]
      rw [Complex.normSq_eq_norm_sq]
    rw [hhighEq]
    exact hpower.norm.pow 2
  have hmajor : Continuous major := by
    dsimp only [major]
    fun_prop
  have hbaseInt : IntervalIntegrable (bad.indicator base)
      MeasureTheory.volume (-T) T := by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_iff.mp
      (hbase.intervalIntegrable (-T) T)).indicator hbad
  have hmajorInt : IntervalIntegrable major MeasureTheory.volume (-T) T :=
    hmajor.intervalIntegrable _ _
  have hpoint : ∀ t ∈ Set.Icc (-T) T,
      bad.indicator base t ≤ major t := by
    intro t ht
    by_cases htbad : t ∈ bad
    · rw [Set.indicator_of_mem htbad]
      dsimp only [major, high, base]
      have hpowerEq :
          mrFiniteRamareSubblockPowerProduct P D S f j t =
            Q t ^ (j + 1) * R t := by
        rfl
      rw [hpowerEq]
      exact normSq_mul_le_inv_pow_mul_normSq_power_mul hW htbad j
    · rw [Set.indicator_of_notMem htbad]
      dsimp only [major, high]
      exact mul_nonneg (inv_nonneg.mpr (pow_nonneg hW.le _))
        (Complex.normSq_nonneg _)
  have hmono := intervalIntegral.integral_mono_on
    (by linarith : -T ≤ T) hbaseInt hmajorInt hpoint
  unfold mrFiniteRamareSubblockBadFrequencyEnergy
  change (∫ t in -T..T, bad.indicator base t) ≤ _
  calc
    (∫ t in -T..T, bad.indicator base t) ≤
        ∫ t in -T..T, major t := hmono
    _ = (W ^ (2 * j))⁻¹ *
        ∫ t in -T..T, high t := by
      dsimp only [major]
      rw [intervalIntegral.integral_const_mul]
    _ = _ := by rfl

/-- Bad-frequency estimate on the genuine dyadic cofactor rectangle.  The
`1/Z` factor and the large-value saving `W^(-2j)` are fully separated. -/
theorem mrFiniteRamareSubblockBadFrequencyEnergy_dyadic_le
    {P D : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hDP : D ⊆ P)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {L U Z j : ℕ} (hL : 0 < L) (hU : 0 < U) (hZ : 0 < Z)
    (hLZ : L ≤ Z) (hUL : U ≤ 2 * L)
    (hDlow : ∀ p ∈ D, L ≤ p) (hDup : ∀ p ∈ D, p ≤ U)
    {T W : ℝ} (hT : 0 ≤ T) (hW : 0 < W) :
    mrFiniteRamareSubblockBadFrequencyEnergy P D
        (mrDyadicCofactorRectangle (L, U) Z) f T W ≤
      (W ^ (2 * j))⁻¹ *
        ((2 * T + 2 * Real.pi *
            (((U ^ j) * (U * ((2 * Z) / L)) : ℕ) : ℝ)) *
          ((∑ p ∈ D, (p : ℝ)⁻¹) ^ (2 * j) *
            (16 / (Z : ℝ)))) := by
  have hbad := mrFiniteRamareSubblockBadFrequencyEnergy_le_power
    (P := P) (D := D) (S := mrDyadicCofactorRectangle (L, U) Z)
    (f := f) hT hW j
  have hhigh :=
    intervalIntegral_normSq_mrFiniteRamareSubblockPowerProduct_dyadic_le
      (j := j) hP hDP hbound hL hU hZ hLZ hUL hDlow hDup hT
  exact hbad.trans (mul_le_mul_of_nonneg_left hhigh
    (inv_nonneg.mpr (pow_nonneg hW.le _)))

/-- Elementary good/bad split for an arbitrary narrow subblock. -/
theorem intervalIntegral_normSq_mrFiniteSubblockProduct_le_good_add_bad
    {P D S : Finset ℕ} {f : ℕ → ℂ}
    {T W E : ℝ} (hT : 0 ≤ T) (hW : 0 ≤ W) (hE : 0 ≤ E)
    (hcofactor : ∀ t ∈ Set.Icc (-T) T,
      ‖mrCofactorPerronPolynomial P S f 1 t‖ ≤ E) :
    (∫ t in -T..T, Complex.normSq
      (mrFinitePrimePerronPolynomial D f 1 t *
        mrCofactorPerronPolynomial P S f 1 t)) ≤
      2 * T * (W ^ 2 * E ^ 2) +
        mrFiniteRamareSubblockBadFrequencyEnergy P D S f T W := by
  let Q : ℝ → ℂ := mrFinitePrimePerronPolynomial D f 1
  let R : ℝ → ℂ := mrCofactorPerronPolynomial P S f 1
  let bad : Set ℝ := {t | W ≤ ‖Q t‖}
  let base : ℝ → ℝ := fun t ↦ Complex.normSq (Q t * R t)
  let goodMajor : ℝ → ℝ := fun _ ↦ W ^ 2 * E ^ 2
  let rhs : ℝ → ℝ := fun t ↦ goodMajor t + bad.indicator base t
  have hQ : Continuous Q :=
    continuous_mrFinitePrimePerronPolynomial D f 1
  have hR : Continuous R :=
    continuous_mrFiniteCofactorPerronPolynomial P S f 1
  have hbad : MeasurableSet bad := by
    exact measurableSet_le measurable_const hQ.norm.measurable
  have hbase : Continuous base := by
    have hbaseEq : base = fun t ↦ ‖Q t * R t‖ ^ 2 := by
      funext t
      dsimp only [base]
      rw [Complex.normSq_eq_norm_sq]
    rw [hbaseEq]
    exact (hQ.mul hR).norm.pow 2
  have hbaseInt : IntervalIntegrable base MeasureTheory.volume (-T) T :=
    hbase.intervalIntegrable _ _
  have hgoodInt : IntervalIntegrable goodMajor MeasureTheory.volume (-T) T :=
    intervalIntegrable_const
  have hbadInt : IntervalIntegrable (bad.indicator base)
      MeasureTheory.volume (-T) T := by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_iff.mp hbaseInt).indicator hbad
  have hrhsInt : IntervalIntegrable rhs MeasureTheory.volume (-T) T :=
    hgoodInt.add hbadInt
  have hpoint : ∀ t ∈ Set.Icc (-T) T, base t ≤ rhs t := by
    intro t ht
    by_cases htbad : t ∈ bad
    · dsimp only [rhs]
      rw [Set.indicator_of_mem htbad]
      have : 0 ≤ goodMajor t := by
        dsimp only [goodMajor]
        positivity
      linarith
    · have hprime : ‖Q t‖ ≤ W := (not_le.mp htbad).le
      have hmul : ‖Q t‖ * ‖R t‖ ≤ W * E :=
        mul_le_mul hprime (hcofactor t ht) (norm_nonneg _) hW
      have hsq : (‖Q t‖ * ‖R t‖) ^ 2 ≤ (W * E) ^ 2 :=
        (sq_le_sq₀
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (mul_nonneg hW hE)).2 hmul
      dsimp only [rhs]
      rw [Set.indicator_of_notMem htbad, add_zero]
      dsimp only [base, goodMajor]
      rw [Complex.normSq_eq_norm_sq, norm_mul]
      nlinarith
  have hmono := intervalIntegral.integral_mono_on
    (by linarith : -T ≤ T) hbaseInt hrhsInt hpoint
  change (∫ t in -T..T, base t) ≤ _
  calc
    (∫ t in -T..T, base t) ≤ ∫ t in -T..T, rhs t := hmono
    _ = (∫ t in -T..T, goodMajor t) +
        ∫ t in -T..T, bad.indicator base t := by
      dsimp only [rhs]
      rw [intervalIntegral.integral_add hgoodInt hbadInt]
    _ = 2 * T * (W ^ 2 * E ^ 2) +
        mrFiniteRamareSubblockBadFrequencyEnergy P D S f T W := by
      unfold goodMajor mrFiniteRamareSubblockBadFrequencyEnergy
      change (∫ _ in -T..T, W ^ 2 * E ^ 2) + _ = _
      rw [intervalIntegral.integral_const]
      change (T - -T) * (W ^ 2 * E ^ 2) + _ = _
      dsimp only [bad, base, Q, R]
      ring

/-- Complete per-subblock energy estimate: the good term retains whatever
finite Halász decay is supplied through `E`, while the bad term retains the
inverse dyadic scale. -/
theorem intervalIntegral_normSq_mrFiniteSubblockProduct_dyadic_le
    {P D : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hDP : D ⊆ P)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {L U Z j : ℕ} (hL : 0 < L) (hU : 0 < U) (hZ : 0 < Z)
    (hLZ : L ≤ Z) (hUL : U ≤ 2 * L)
    (hDlow : ∀ p ∈ D, L ≤ p) (hDup : ∀ p ∈ D, p ≤ U)
    {T W E : ℝ} (hT : 0 ≤ T) (hW : 0 < W) (hE : 0 ≤ E)
    (hcofactor : ∀ t ∈ Set.Icc (-T) T,
      ‖mrCofactorPerronPolynomial P
        (mrDyadicCofactorRectangle (L, U) Z) f 1 t‖ ≤ E) :
    (∫ t in -T..T, Complex.normSq
      (mrFinitePrimePerronPolynomial D f 1 t *
        mrCofactorPerronPolynomial P
          (mrDyadicCofactorRectangle (L, U) Z) f 1 t)) ≤
      2 * T * (W ^ 2 * E ^ 2) +
        (W ^ (2 * j))⁻¹ *
          ((2 * T + 2 * Real.pi *
              (((U ^ j) * (U * ((2 * Z) / L)) : ℕ) : ℝ)) *
            ((∑ p ∈ D, (p : ℝ)⁻¹) ^ (2 * j) *
              (16 / (Z : ℝ)))) := by
  have hsplit :=
    intervalIntegral_normSq_mrFiniteSubblockProduct_le_good_add_bad
      (P := P) (D := D)
      (S := mrDyadicCofactorRectangle (L, U) Z) (f := f)
      hT hW.le hE hcofactor
  have hbad := mrFiniteRamareSubblockBadFrequencyEnergy_dyadic_le
    (j := j) hP hDP hbound hL hU hZ hLZ hUL hDlow hDup hT hW
  linarith

/-! ## Integrated finite-cofactor mean value -/

theorem norm_mrFiniteCofactorLineCoefficient_le_inv
    {P : Finset ℕ} {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {m : ℕ} (hm : 0 < m) :
    ‖mrFiniteCofactorLineCoefficient P f m‖ ≤ (m : ℝ)⁻¹ := by
  have hden : 0 < mrCommonDenominator P m := by
    unfold mrCommonDenominator
    omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdenR : (0 : ℝ) < mrCommonDenominator P m := by
    exact_mod_cast hden
  unfold mrFiniteCofactorLineCoefficient
  rw [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast,
    div_eq_mul_inv]
  calc
    ‖f m‖ *
        ((mrCommonDenominator P m : ℝ) * (m : ℝ))⁻¹ ≤
        ((mrCommonDenominator P m : ℝ) * (m : ℝ))⁻¹ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (hbound m hm) (inv_nonneg.mpr (by positivity))
    _ ≤ (m : ℝ)⁻¹ := by
      apply inv_anti₀ hmR
      nlinarith [show (1 : ℝ) ≤ mrCommonDenominator P m by
        exact_mod_cast hden]

theorem sum_normSq_mrFiniteCofactorLineCoefficient_le
    {P S : Finset ℕ} {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (hSpos : ∀ m ∈ S, 0 < m)
    {M : ℕ} (hM : 0 < M) (hSlow : ∀ m ∈ S, M ≤ m) :
    (∑ m ∈ S, Complex.normSq (mrFiniteCofactorLineCoefficient P f m)) ≤
      (S.card : ℝ) / (M : ℝ) ^ 2 := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  calc
    (∑ m ∈ S, Complex.normSq (mrFiniteCofactorLineCoefficient P f m)) ≤
        ∑ _m ∈ S, ((M : ℝ)⁻¹) ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      have hcoeff := norm_mrFiniteCofactorLineCoefficient_le_inv
        (P := P) hbound (hSpos m hm)
      have hinv : (m : ℝ)⁻¹ ≤ (M : ℝ)⁻¹ := by
        apply inv_anti₀ hMR
        exact_mod_cast hSlow m hm
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hcoeff.trans hinv) 2
    _ = (S.card : ℝ) * ((M : ℝ)⁻¹) ^ 2 := by simp
    _ = (S.card : ℝ) / (M : ℝ) ^ 2 := by
      rw [div_eq_mul_inv, inv_pow]

/-- Mean square of the finite cofactor polynomial itself.  This replaces
the incorrect pointwise use of an absolutely truncated complete series. -/
theorem intervalIntegral_normSq_mrCofactorPerronPolynomial_one_le
    {P S : Finset ℕ} {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (hSpos : ∀ m ∈ S, 0 < m)
    {M V : ℕ} (hM : 0 < M) (hV : 0 < V)
    (hSlow : ∀ m ∈ S, M ≤ m) (hSup : ∀ m ∈ S, m ≤ V)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T,
      Complex.normSq (mrCofactorPerronPolynomial P S f 1 t)) ≤
      (2 * T + 2 * Real.pi * (V : ℝ)) *
        ((S.card : ℝ) / (M : ℝ) ^ 2) := by
  let a := mrFiniteCofactorLineCoefficient P f
  have hflip :
      (∫ t in -T..T,
        Complex.normSq (mrCofactorPerronPolynomial P S f 1 t)) =
        ∫ t in -T..T,
          Complex.normSq (logarithmicDirichletPolynomial S a t) := by
    have hfirst : (∫ t in -T..T,
        Complex.normSq (mrCofactorPerronPolynomial P S f 1 t)) =
        ∫ t in -T..T,
          Complex.normSq (logarithmicDirichletPolynomial S a (-t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change Complex.normSq (mrCofactorPerronPolynomial P S f 1 t) = _
      rw [mrCofactorPerronPolynomial_one_eq_linePolynomial]
    have hsecond : (∫ t in -T..T,
        Complex.normSq (logarithmicDirichletPolynomial S a (-t))) =
        ∫ t in -T..T,
          Complex.normSq (logarithmicDirichletPolynomial S a t) := by
      simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (a := -T) (b := T)
        (fun t ↦ Complex.normSq
          (logarithmicDirichletPolynomial S a t)))
    exact hfirst.trans hsecond
  have hmean := norm_logarithmicDirichletPolynomial_intervalIntegral_le
    hV hSpos hSup a hT
  have hmass := sum_normSq_mrFiniteCofactorLineCoefficient_le
    (P := P) hbound hSpos hM hSlow
  rw [hflip,
    intervalIntegral_normSq_eq_norm_intervalIntegral_conj_mul _ hT]
  exact hmean.trans (mul_le_mul_of_nonneg_left hmass (by positivity))

theorem mrDyadicCofactorRectangle_cardRatio_cofactor_le
    {L U Z : ℕ} (_hL : 0 < L) (hU : 0 < U) (hZ : 0 < Z)
    (hUL : U ≤ 2 * L) :
    ((mrDyadicCofactorRectangle (L, U) Z).card : ℝ) /
        ((Z / U + 1 : ℕ) : ℝ) ^ 2 ≤
      4 * (U : ℝ) / (Z : ℝ) := by
  let S := mrDyadicCofactorRectangle (L, U) Z
  let M := Z / U + 1
  have hScard : S.card ≤ (2 * Z) / L := by
    dsimp only [S, mrDyadicCofactorRectangle]
    rw [Nat.card_Ioc]
    exact Nat.sub_le _ _
  have hdiv : L * ((2 * Z) / L) ≤ 2 * Z := Nat.mul_div_le _ _
  have hSL : S.card * L ≤ 2 * Z := by
    calc
      S.card * L ≤ ((2 * Z) / L) * L :=
        Nat.mul_le_mul_right L hScard
      _ = L * ((2 * Z) / L) := by rw [mul_comm]
      _ ≤ 2 * Z := hdiv
  have hSU : S.card * U ≤ 4 * Z := by
    calc
      S.card * U ≤ S.card * (2 * L) :=
        Nat.mul_le_mul_left S.card hUL
      _ = 2 * (S.card * L) := by ring
      _ ≤ 2 * (2 * Z) := Nat.mul_le_mul_left 2 hSL
      _ = 4 * Z := by omega
  have hM : 0 < M := Nat.succ_pos _
  have hZUM : Z ≤ U * M := (Nat.lt_mul_div_succ Z hU).le
  have hSU' : S.card * U ≤ (4 * M) * U := by
    calc
      S.card * U ≤ 4 * Z := hSU
      _ ≤ 4 * (U * M) := Nat.mul_le_mul_left 4 hZUM
      _ = (4 * M) * U := by ring
  have hS4M : S.card ≤ 4 * M :=
    Nat.le_of_mul_le_mul_right hSU' hU
  have hcross : S.card * Z ≤ (4 * U) * (M ^ 2) := by
    calc
      S.card * Z ≤ (4 * M) * Z := Nat.mul_le_mul_right Z hS4M
      _ ≤ (4 * M) * (U * M) := Nat.mul_le_mul_left (4 * M) hZUM
      _ = (4 * U) * (M ^ 2) := by ring
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hZR : (0 : ℝ) < Z := by exact_mod_cast hZ
  apply (div_le_div_iff₀ (sq_pos_of_pos hMR) hZR).2
  exact_mod_cast hcross

/-- The finite cofactor mean square on the genuine rectangle has size
`(T + Z/L) U/Z`; no complete-series tail is present. -/
theorem intervalIntegral_normSq_mrCofactorPerronPolynomial_dyadic_le
    {P : Finset ℕ} {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {L U Z : ℕ} (hL : 0 < L) (hU : 0 < U) (hZ : 0 < Z)
    (hLZ : L ≤ Z) (hUL : U ≤ 2 * L)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, Complex.normSq
      (mrCofactorPerronPolynomial P
        (mrDyadicCofactorRectangle (L, U) Z) f 1 t)) ≤
      (2 * T + 2 * Real.pi * (((2 * Z) / L : ℕ) : ℝ)) *
        (4 * (U : ℝ) / (Z : ℝ)) := by
  let S := mrDyadicCofactorRectangle (L, U) Z
  let M := Z / U + 1
  let V := (2 * Z) / L
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    have hm' : Z / U < m := by
      simpa only [S, mrDyadicCofactorRectangle] using
        (Finset.mem_Ioc.mp hm).1
    exact (Nat.zero_le _).trans_lt hm'
  have hM : 0 < M := Nat.succ_pos _
  have hV : 0 < V := by
    dsimp only [V]
    exact Nat.div_pos (by omega) hL
  have hSlow : ∀ m ∈ S, M ≤ m := by
    intro m hm
    have hm' : Z / U < m := by
      simpa only [S, mrDyadicCofactorRectangle] using
        (Finset.mem_Ioc.mp hm).1
    exact Nat.succ_le_iff.mpr hm'
  have hSup : ∀ m ∈ S, m ≤ V := by
    intro m hm
    simpa only [S, V, mrDyadicCofactorRectangle] using
      (Finset.mem_Ioc.mp hm).2
  have hbase := intervalIntegral_normSq_mrCofactorPerronPolynomial_one_le
    (P := P) (S := S) (f := f) hbound hSpos hM hV hSlow hSup hT
  have hratio := mrDyadicCofactorRectangle_cardRatio_cofactor_le
    hL hU hZ hUL
  exact hbase.trans (mul_le_mul_of_nonneg_left
    (by simpa only [S, M] using hratio) (by positivity))

/-! ## Good/bad product energy without a pointwise cofactor bound -/

/-- On the good set only the prime polynomial is bounded pointwise; the
finite cofactor is kept under its own square integral. -/
theorem intervalIntegral_normSq_mrFiniteSubblockProduct_le_integrated_good_add_bad
    {P D S : Finset ℕ} {f : ℕ → ℂ}
    {T W : ℝ} (hT : 0 ≤ T) (hW : 0 ≤ W) :
    (∫ t in -T..T, Complex.normSq
      (mrFinitePrimePerronPolynomial D f 1 t *
        mrCofactorPerronPolynomial P S f 1 t)) ≤
      W ^ 2 *
        (∫ t in -T..T,
          Complex.normSq (mrCofactorPerronPolynomial P S f 1 t)) +
        mrFiniteRamareSubblockBadFrequencyEnergy P D S f T W := by
  let Q : ℝ → ℂ := mrFinitePrimePerronPolynomial D f 1
  let R : ℝ → ℂ := mrCofactorPerronPolynomial P S f 1
  let bad : Set ℝ := {t | W ≤ ‖Q t‖}
  let base : ℝ → ℝ := fun t ↦ Complex.normSq (Q t * R t)
  let goodMajor : ℝ → ℝ := fun t ↦ W ^ 2 * Complex.normSq (R t)
  let rhs : ℝ → ℝ := fun t ↦ goodMajor t + bad.indicator base t
  have hQ : Continuous Q :=
    continuous_mrFinitePrimePerronPolynomial D f 1
  have hR : Continuous R :=
    continuous_mrFiniteCofactorPerronPolynomial P S f 1
  have hbad : MeasurableSet bad := by
    exact measurableSet_le measurable_const hQ.norm.measurable
  have hbase : Continuous base := by
    have hbaseEq : base = fun t ↦ ‖Q t * R t‖ ^ 2 := by
      funext t
      dsimp only [base]
      rw [Complex.normSq_eq_norm_sq]
    rw [hbaseEq]
    exact (hQ.mul hR).norm.pow 2
  have hgood : Continuous goodMajor := by
    have hgoodEq : goodMajor = fun t ↦ W ^ 2 * ‖R t‖ ^ 2 := by
      funext t
      dsimp only [goodMajor]
      rw [Complex.normSq_eq_norm_sq]
    rw [hgoodEq]
    fun_prop
  have hbaseInt : IntervalIntegrable base MeasureTheory.volume (-T) T :=
    hbase.intervalIntegrable _ _
  have hgoodInt : IntervalIntegrable goodMajor MeasureTheory.volume (-T) T :=
    hgood.intervalIntegrable _ _
  have hbadInt : IntervalIntegrable (bad.indicator base)
      MeasureTheory.volume (-T) T := by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_iff.mp hbaseInt).indicator hbad
  have hrhsInt : IntervalIntegrable rhs MeasureTheory.volume (-T) T :=
    hgoodInt.add hbadInt
  have hpoint : ∀ t ∈ Set.Icc (-T) T, base t ≤ rhs t := by
    intro t ht
    by_cases htbad : t ∈ bad
    · dsimp only [rhs]
      rw [Set.indicator_of_mem htbad]
      have : 0 ≤ goodMajor t := by
        dsimp only [goodMajor]
        exact mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
      linarith
    · have hprime : ‖Q t‖ ≤ W := (not_le.mp htbad).le
      have hsq : ‖Q t‖ ^ 2 ≤ W ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hW).2 hprime
      dsimp only [rhs]
      rw [Set.indicator_of_notMem htbad, add_zero]
      dsimp only [base, goodMajor]
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, norm_mul]
      calc
        (‖Q t‖ * ‖R t‖) ^ 2 = ‖Q t‖ ^ 2 * ‖R t‖ ^ 2 := by ring
        _ ≤ W ^ 2 * ‖R t‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖R t‖)
  have hmono := intervalIntegral.integral_mono_on
    (by linarith : -T ≤ T) hbaseInt hrhsInt hpoint
  change (∫ t in -T..T, base t) ≤ _
  calc
    (∫ t in -T..T, base t) ≤ ∫ t in -T..T, rhs t := hmono
    _ = (∫ t in -T..T, goodMajor t) +
        ∫ t in -T..T, bad.indicator base t := by
      dsimp only [rhs]
      rw [intervalIntegral.integral_add hgoodInt hbadInt]
    _ = W ^ 2 * (∫ t in -T..T, Complex.normSq (R t)) +
        mrFiniteRamareSubblockBadFrequencyEnergy P D S f T W := by
      dsimp only [goodMajor]
      rw [intervalIntegral.integral_const_mul]
      unfold mrFiniteRamareSubblockBadFrequencyEnergy
      rfl

/-- Far-frequency product bound in the form used by Appendix A,
Proposition A.3.  The good term uses only the integrated finite-cofactor
mean value, and the bad term uses the prime high moment. -/
theorem intervalIntegral_normSq_mrFiniteSubblockProduct_dyadic_le_integrated
    {P D : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hDP : D ⊆ P)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {L U Z j : ℕ} (hL : 0 < L) (hU : 0 < U) (hZ : 0 < Z)
    (hLZ : L ≤ Z) (hUL : U ≤ 2 * L)
    (hDlow : ∀ p ∈ D, L ≤ p) (hDup : ∀ p ∈ D, p ≤ U)
    {T W : ℝ} (hT : 0 ≤ T) (hW : 0 < W) :
    (∫ t in -T..T, Complex.normSq
      (mrFinitePrimePerronPolynomial D f 1 t *
        mrCofactorPerronPolynomial P
          (mrDyadicCofactorRectangle (L, U) Z) f 1 t)) ≤
      W ^ 2 *
          ((2 * T + 2 * Real.pi * (((2 * Z) / L : ℕ) : ℝ)) *
            (4 * (U : ℝ) / (Z : ℝ))) +
        (W ^ (2 * j))⁻¹ *
          ((2 * T + 2 * Real.pi *
              (((U ^ j) * (U * ((2 * Z) / L)) : ℕ) : ℝ)) *
            ((∑ p ∈ D, (p : ℝ)⁻¹) ^ (2 * j) *
              (16 / (Z : ℝ)))) := by
  have hsplit :=
    intervalIntegral_normSq_mrFiniteSubblockProduct_le_integrated_good_add_bad
      (P := P) (D := D) (S := mrDyadicCofactorRectangle (L, U) Z)
      (f := f) hT hW.le
  have hcofactor := intervalIntegral_normSq_mrCofactorPerronPolynomial_dyadic_le
    (P := P) (f := f) hbound hL hU hZ hLZ hUL hT
  have hbad := mrFiniteRamareSubblockBadFrequencyEnergy_dyadic_le
    (j := j) hP hDP hbound hL hU hZ hLZ hUL hDlow hDup hT hW
  calc
    (∫ t in -T..T, Complex.normSq
      (mrFinitePrimePerronPolynomial D f 1 t *
        mrCofactorPerronPolynomial P
          (mrDyadicCofactorRectangle (L, U) Z) f 1 t)) ≤
        W ^ 2 *
          (∫ t in -T..T, Complex.normSq
            (mrCofactorPerronPolynomial P
              (mrDyadicCofactorRectangle (L, U) Z) f 1 t)) +
          mrFiniteRamareSubblockBadFrequencyEnergy P D
            (mrDyadicCofactorRectangle (L, U) Z) f T W := hsplit
    _ ≤ W ^ 2 *
          ((2 * T + 2 * Real.pi * (((2 * Z) / L : ℕ) : ℝ)) *
            (4 * (U : ℝ) / (Z : ℝ))) +
        mrFiniteRamareSubblockBadFrequencyEnergy P D
          (mrDyadicCofactorRectangle (L, U) Z) f T W := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hcofactor (sq_nonneg W)) le_rfl
    _ ≤ _ := add_le_add le_rfl hbad

/-! ## Recombination over a finite prime partition -/

/-- The explicit integrated good/bad bound for one narrow block. -/
def mrFiniteSubblockIntegratedEnergyBound
    (D : Finset ℕ) (J : ℕ × ℕ) (Z j : ℕ) (T W : ℝ) : ℝ :=
  W ^ 2 *
      ((2 * T + 2 * Real.pi * (((2 * Z) / J.1 : ℕ) : ℝ)) *
        (4 * (J.2 : ℝ) / (Z : ℝ))) +
    (W ^ (2 * j))⁻¹ *
      ((2 * T + 2 * Real.pi *
          (((J.2 ^ j) * (J.2 * ((2 * Z) / J.1)) : ℕ) : ℝ)) *
        ((∑ p ∈ D, (p : ℝ)⁻¹) ^ (2 * j) *
          (16 / (Z : ℝ))))

/-- Explicit far-frequency energy of the original finite dyadic common
polynomial.  Every product term uses the integrated finite-cofactor mean
value, every bad-frequency term retains `1/Z`, and the endpoint-boundary
energy from the exact finite factorisation remains displayed. -/
theorem intervalIntegral_normSq_mrFiniteDyadicRamarePolynomial_le_integrated_partition
    {ι : Type*} [DecidableEq ι] {V₀ : Finset ι}
    {I : ℕ × ℕ} {D : ι → Finset ℕ} {J : ι → ℕ × ℕ}
    {Z j : ℕ}
    (hdisj : Set.PairwiseDisjoint (↑V₀) D)
    (hcover : V₀.biUnion D = primesInBlock I)
    (hlo : ∀ v ∈ V₀, 0 < (J v).1)
    (hJle : ∀ v ∈ V₀, (J v).1 ≤ (J v).2)
    (hJZ : ∀ v ∈ V₀, (J v).1 ≤ Z)
    (hwidth : ∀ v ∈ V₀, (J v).2 ≤ 2 * (J v).1)
    (hD : ∀ v ∈ V₀, ∀ p ∈ D v,
      (J v).1 ≤ p ∧ p ≤ (J v).2)
    (hZ : 0 < Z)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {T W : ℝ} (hT : 0 ≤ T) (hW : 0 < W) :
    (∫ t in -T..T,
      Complex.normSq (mrFiniteDyadicRamarePolynomial I f Z 1 t)) ≤
      2 * (V₀.card : ℝ) *
        ((∑ v ∈ V₀,
            mrFiniteSubblockIntegratedEnergyBound (D v) (J v) Z j T W) +
          ∑ v ∈ V₀,
            mrFiniteRamareSubblockBoundaryEnergyBound (J v) Z T) := by
  classical
  have hP : ∀ p ∈ primesInBlock I, p.Prime := fun p hp ↦
    (mem_primesInBlock.mp hp).1
  have hDP : ∀ v ∈ V₀, D v ⊆ primesInBlock I := by
    intro v hv p hp
    rw [← hcover]
    exact Finset.mem_biUnion.mpr ⟨v, hv, hp⟩
  have hbase :=
    intervalIntegral_normSq_mrFiniteDyadicRamarePolynomial_le_products_add_boundary
      hdisj hcover hlo hJle hJZ hD hbound hT
  calc
    (∫ t in -T..T,
      Complex.normSq (mrFiniteDyadicRamarePolynomial I f Z 1 t)) ≤
        2 * (V₀.card : ℝ) *
          ((∑ v ∈ V₀,
              ∫ t in -T..T, Complex.normSq
                (mrFinitePrimePerronPolynomial (D v) f 1 t *
                  mrCofactorPerronPolynomial (primesInBlock I)
                    (mrDyadicCofactorRectangle (J v) Z) f 1 t)) +
            ∑ v ∈ V₀,
              mrFiniteRamareSubblockBoundaryEnergyBound (J v) Z T) := hbase
    _ ≤ 2 * (V₀.card : ℝ) *
        ((∑ v ∈ V₀,
            mrFiniteSubblockIntegratedEnergyBound (D v) (J v) Z j T W) +
          ∑ v ∈ V₀,
            mrFiniteRamareSubblockBoundaryEnergyBound (J v) Z T) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · apply Finset.sum_le_sum
        intro v hv
        exact intervalIntegral_normSq_mrFiniteSubblockProduct_dyadic_le_integrated
          hP (hDP v hv) hbound (hlo v hv)
          ((hlo v hv).trans_le (hJle v hv)) hZ (hJZ v hv)
          (hwidth v hv) (fun p hp ↦ (hD v hv p hp).1)
          (fun p hp ↦ (hD v hv p hp).2) hT hW
      · exact le_rfl

/-! ## Removing a typical-support restriction near the Halász bands -/

/-- The restricted dyadic polynomial differs from the unrestricted one
only on the exceptional integers.  A direct finite mean-value theorem
charges this removal by their cardinality, with the full `1/X²` coefficient
scale. -/
theorem intervalIntegral_normSq_dyadicVerticalDirichletPolynomial_sub_full_le
    (S : Finset ℕ) {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X : ℕ} (hX : 0 < X) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, Complex.normSq
      (dyadicVerticalDirichletPolynomial S f X t -
        dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X)) f X t)) ≤
      (2 * T + 4 * Real.pi * (X : ℝ)) *
        (((Finset.Ioc X (2 * X) \ S).card : ℝ) / (X : ℝ) ^ 2) := by
  classical
  let B := Finset.Ioc X (2 * X)
  let A := B \ S
  let a := mrFinitePrimeLineCoefficient f
  have hApos : ∀ n ∈ A, 0 < n := by
    intro n hn
    have hnB : n ∈ B := (Finset.mem_sdiff.mp hn).1
    exact hX.trans (Finset.mem_Ioc.mp hnB).1
  have hAX : ∀ n ∈ A, X ≤ n := by
    intro n hn
    exact (Finset.mem_Ioc.mp (Finset.mem_sdiff.mp hn).1).1.le
  have hAup : ∀ n ∈ A, n ≤ 2 * X := by
    intro n hn
    exact (Finset.mem_Ioc.mp (Finset.mem_sdiff.mp hn).1).2
  have hpoly (t : ℝ) :
      dyadicVerticalDirichletPolynomial S f X t -
          dyadicVerticalDirichletPolynomial B f X t =
        -logarithmicDirichletPolynomial A a (-t) := by
    unfold dyadicVerticalDirichletPolynomial dyadicRestrictedSupport
      logarithmicDirichletPolynomial
    change (∑ n ∈ B ∩ S, a n * logarithmicPhase n (-t)) -
        (∑ n ∈ B ∩ B, a n * logarithmicPhase n (-t)) =
      -∑ n ∈ A, a n * logarithmicPhase n (-t)
    rw [Finset.inter_self]
    have hsub : B ∩ S ⊆ B := Finset.inter_subset_left
    have hsplit := Finset.sum_sdiff hsub
      (f := fun n ↦ a n * logarithmicPhase n (-t))
    have hdiff : B \ (B ∩ S) = A := by
      ext n
      simp only [A, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    rw [hdiff] at hsplit
    rw [← hsplit]
    ring
  have henergy :
      (∫ t in -T..T, Complex.normSq
        (dyadicVerticalDirichletPolynomial S f X t -
          dyadicVerticalDirichletPolynomial B f X t)) =
        ∫ t in -T..T,
          Complex.normSq (logarithmicDirichletPolynomial A a t) := by
    calc
      (∫ t in -T..T, Complex.normSq
        (dyadicVerticalDirichletPolynomial S f X t -
          dyadicVerticalDirichletPolynomial B f X t)) =
          ∫ t in -T..T,
            Complex.normSq (logarithmicDirichletPolynomial A a (-t)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        change Complex.normSq
            (dyadicVerticalDirichletPolynomial S f X t -
              dyadicVerticalDirichletPolynomial B f X t) = _
        rw [hpoly, Complex.normSq_neg]
      _ = ∫ t in -T..T,
          Complex.normSq (logarithmicDirichletPolynomial A a t) := by
        simpa only [neg_neg] using
          (intervalIntegral.integral_comp_neg (a := -T) (b := T)
            (fun t ↦ Complex.normSq
              (logarithmicDirichletPolynomial A a t)))
  have hmass :
      (∑ n ∈ A, Complex.normSq (a n)) ≤
        (A.card : ℝ) / (X : ℝ) ^ 2 := by
    have hXR : (0 : ℝ) < X := by exact_mod_cast hX
    calc
      (∑ n ∈ A, Complex.normSq (a n)) ≤
          ∑ _n ∈ A, ((X : ℝ)⁻¹) ^ 2 := by
        apply Finset.sum_le_sum
        intro n hn
        have hcoeff := norm_mrFinitePrimeLineCoefficient_le
          hbound (hApos n hn)
        have hinv : (n : ℝ)⁻¹ ≤ (X : ℝ)⁻¹ := by
          apply inv_anti₀ hXR
          exact_mod_cast hAX n hn
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ (norm_nonneg _) (hcoeff.trans hinv) 2
      _ = (A.card : ℝ) * ((X : ℝ)⁻¹) ^ 2 := by simp
      _ = (A.card : ℝ) / (X : ℝ) ^ 2 := by
        rw [div_eq_mul_inv, inv_pow]
  have hmean := norm_logarithmicDirichletPolynomial_intervalIntegral_le
    (N := 2 * X) (D := A) (a := a) (T := T)
    (by omega) hApos hAup hT
  rw [henergy,
    intervalIntegral_normSq_eq_norm_intervalIntegral_conj_mul _ hT]
  calc
    ‖∫ t in -T..T,
        conj (logarithmicDirichletPolynomial A a t) *
          logarithmicDirichletPolynomial A a t‖ ≤
        (2 * T + 2 * Real.pi * ((2 * X : ℕ) : ℝ)) *
          ∑ n ∈ A, Complex.normSq (a n) := hmean
    _ ≤ (2 * T + 2 * Real.pi * ((2 * X : ℕ) : ℝ)) *
        ((A.card : ℝ) / (X : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (2 * T + 4 * Real.pi * (X : ℝ)) *
        (((Finset.Ioc X (2 * X) \ S).card : ℝ) /
          (X : ℝ) ^ 2) := by
      dsimp only [A, B]
      push_cast
      ring

end

end Erdos67
