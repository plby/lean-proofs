import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# A finite Fourier sieve on ray-class quotients

The congruence quotients which occur in the odd-prime part of Elliott's
argument are finite abelian groups, rather than copies of `ZMod q`.  This
file isolates the purely finite Fourier certificate needed by the
number-field larger sieve.  It deliberately uses only the additive group
structure: a multiplicative ray-class group is passed to these definitions
through `Additive`.
-/

open RCLike
open scoped BigOperators ComplexConjugate

namespace Erdos980.ElliottTail

section OneGroup

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The complement of a prescribed set of forbidden classes. -/
def groupSurvivingClasses (vanishing : Finset G) : Finset G :=
  Finset.univ \ vanishing

lemma card_groupSurvivingClasses (vanishing : Finset G) :
    (groupSurvivingClasses vanishing).card =
      Fintype.card G - vanishing.card := by
  classical
  rw [groupSurvivingClasses,
    Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

/-- The mean-zero mask `|V| - |G| 1_V` attached to a set of forbidden
classes `V` in a finite abelian group. -/
noncomputable def finiteGroupMask (vanishing : Finset G) (x : G) : ℂ :=
  (vanishing.card : ℂ) - (Fintype.card G : ℂ) *
    if x ∈ vanishing then 1 else 0

@[simp]
lemma finiteGroupMask_of_mem {vanishing : Finset G} {x : G}
    (hx : x ∈ vanishing) :
    finiteGroupMask vanishing x =
      (vanishing.card : ℂ) - Fintype.card G := by
  simp [finiteGroupMask, hx]

@[simp]
lemma finiteGroupMask_of_notMem {vanishing : Finset G} {x : G}
    (hx : x ∉ vanishing) :
    finiteGroupMask vanishing x = (vanishing.card : ℂ) := by
  simp [finiteGroupMask, hx]

/-- The finite-group mask has mean zero. -/
lemma sum_finiteGroupMask (vanishing : Finset G) :
    ∑ x : G, finiteGroupMask vanishing x = 0 := by
  classical
  simp only [finiteGroupMask, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  have hindicator :
      (∑ x : G, if x ∈ vanishing then (1 : ℂ) else 0) =
        (vanishing.card : ℂ) := by simp
  rw [← Finset.mul_sum, hindicator]
  simp

/-- The normalized Fourier coefficient of `finiteGroupMask`. -/
noncomputable def finiteGroupMaskCoefficient
    (vanishing : Finset G) (psi : AddChar G ℂ) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ *
    ∑ y : G, finiteGroupMask vanishing y * (psi y)⁻¹

@[simp]
lemma finiteGroupMaskCoefficient_zero (vanishing : Finset G) :
    finiteGroupMaskCoefficient vanishing 0 = 0 := by
  simp [finiteGroupMaskCoefficient, sum_finiteGroupMask]

private lemma addChar_inv_mul_apply_eq_apply_sub
    (psi : AddChar G ℂ) (x y : G) :
    (psi y)⁻¹ * psi x = psi (x - y) := by
  rw [AddChar.map_sub_eq_div, div_eq_mul_inv]
  ring

/-- Fourier inversion for the finite-group mask.  The proof uses finite
Pontryagin duality, so it applies verbatim to ray-class quotients. -/
lemma finiteGroupMask_eq_fourierExpansion
    (vanishing : Finset G) (x : G) :
    finiteGroupMask vanishing x =
      ∑ psi : AddChar G ℂ,
        finiteGroupMaskCoefficient vanishing psi * psi x := by
  classical
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  symm
  simp_rw [finiteGroupMaskCoefficient]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  calc
    ∑ y : G, ∑ psi : AddChar G ℂ,
        (Fintype.card G : ℂ)⁻¹ *
          (finiteGroupMask vanishing y * (psi y)⁻¹) * psi x =
        ∑ y : G, finiteGroupMask vanishing y *
          ((Fintype.card G : ℂ)⁻¹ *
            ∑ psi : AddChar G ℂ, psi (x - y)) := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro psi _hpsi
      rw [← addChar_inv_mul_apply_eq_apply_sub psi x y]
      ring
    _ = ∑ y : G, finiteGroupMask vanishing y *
          ((Fintype.card G : ℂ)⁻¹ *
            if x - y = 0 then (Fintype.card G : ℂ) else 0) := by
      simp_rw [AddChar.sum_apply_eq_ite]
    _ = finiteGroupMask vanishing x := by
      rw [Finset.sum_eq_single x]
      · simp [hcard]
      · intro y _hy hyx
        have hsub : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyx)
        simp [hsub]
      · intro hx
        exact (hx (Finset.mem_univ x)).elim

lemma conj_finiteGroupMask (vanishing : Finset G) (x : G) :
    conj (finiteGroupMask vanishing x) = finiteGroupMask vanishing x := by
  by_cases hx : x ∈ vanishing <;>
    simp [finiteGroupMask, hx, map_sub, map_mul]

lemma norm_sq_finiteGroupMask (vanishing : Finset G) (x : G) :
    ‖finiteGroupMask vanishing x‖ ^ 2 =
      if x ∈ vanishing then
        ((Fintype.card G - vanishing.card : ℕ) : ℝ) ^ 2
      else (vanishing.card : ℝ) ^ 2 := by
  classical
  have hcard : vanishing.card ≤ Fintype.card G :=
    Finset.card_le_univ vanishing
  by_cases hx : x ∈ vanishing
  · simp only [hx, if_pos, finiteGroupMask_of_mem]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Nat.cast_sub hcard]
    norm_num
    ring
  · simp only [hx, if_false, finiteGroupMask_of_notMem]
    rw [finiteGroupMask_of_notMem hx]
    norm_num

lemma sum_norm_sq_finiteGroupMask (vanishing : Finset G) :
    (∑ x : G, ‖finiteGroupMask vanishing x‖ ^ 2) =
      (Fintype.card G : ℝ) * vanishing.card *
        (Fintype.card G - vanishing.card : ℕ) := by
  classical
  have hcard : vanishing.card ≤ Fintype.card G :=
    Finset.card_le_univ vanishing
  have hnotcard :
      ((Finset.univ : Finset G).filter
        (fun x => x ∉ vanishing)).card =
          Fintype.card G - vanishing.card := by
    rw [← card_groupSurvivingClasses vanishing]
    congr 1
    ext x
    simp [groupSurvivingClasses]
  simp_rw [norm_sq_finiteGroupMask]
  rw [Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul]
  rw [hnotcard]
  push_cast [Nat.cast_sub hcard]
  ring

lemma conj_finiteGroupMaskCoefficient
    (vanishing : Finset G) (psi : AddChar G ℂ) :
    conj (finiteGroupMaskCoefficient vanishing psi) =
      (Fintype.card G : ℂ)⁻¹ *
        ∑ x : G, finiteGroupMask vanishing x * psi x := by
  classical
  simp only [finiteGroupMaskCoefficient, map_mul, map_inv₀, map_natCast,
    map_sum, conj_finiteGroupMask]
  congr 1
  apply Finset.sum_congr rfl
  intro x _hx
  congr 1
  rw [← AddChar.inv_apply_eq_conj psi x, inv_inv]

private lemma complex_cast_norm_sq_eq_mul_conj (z : ℂ) :
    (Complex.ofReal ‖z‖) ^ 2 = z * conj z := by
  exact (RCLike.mul_conj z).symm

/-- Parseval for the normalized mask coefficients on an arbitrary finite
abelian group. -/
lemma sum_norm_sq_finiteGroupMaskCoefficient
    (vanishing : Finset G) :
    (∑ psi : AddChar G ℂ,
        ‖finiteGroupMaskCoefficient vanishing psi‖ ^ 2) =
      (Fintype.card G : ℝ)⁻¹ *
        ∑ x : G, ‖finiteGroupMask vanishing x‖ ^ 2 := by
  classical
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← Complex.ofReal_inj]
  push_cast
  calc
    ∑ psi : AddChar G ℂ,
        (Complex.ofReal ‖finiteGroupMaskCoefficient vanishing psi‖) ^ 2 =
        ∑ psi : AddChar G ℂ,
          finiteGroupMaskCoefficient vanishing psi *
            conj (finiteGroupMaskCoefficient vanishing psi) := by
      apply Finset.sum_congr rfl
      intro psi _hpsi
      exact complex_cast_norm_sq_eq_mul_conj _
    _ = ∑ x : G, ∑ psi : AddChar G ℂ,
        finiteGroupMaskCoefficient vanishing psi *
          ((Fintype.card G : ℂ)⁻¹ *
            (finiteGroupMask vanishing x * psi x)) := by
      simp_rw [conj_finiteGroupMaskCoefficient, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ =
        ∑ x : G, (Fintype.card G : ℂ)⁻¹ *
          (finiteGroupMask vanishing x *
            ∑ psi : AddChar G ℂ,
              finiteGroupMaskCoefficient vanishing psi * psi x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro psi _hpsi
      ring
    _ = ∑ x : G, (Fintype.card G : ℂ)⁻¹ *
          (finiteGroupMask vanishing x * finiteGroupMask vanishing x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [← finiteGroupMask_eq_fourierExpansion]
    _ = ((Fintype.card G : ℂ)⁻¹ : ℂ) *
        ∑ x : G,
          (Complex.ofReal ‖finiteGroupMask vanishing x‖) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [complex_cast_norm_sq_eq_mul_conj, conj_finiteGroupMask]
    _ = _ := by norm_num

/-- Exact coefficient energy of the mean-zero forbidden-class mask. -/
lemma sum_norm_sq_finiteGroupMaskCoefficient_eq
    (vanishing : Finset G) :
    (∑ psi : AddChar G ℂ,
        ‖finiteGroupMaskCoefficient vanishing psi‖ ^ 2) =
      (vanishing.card : ℝ) *
        (Fintype.card G - vanishing.card : ℕ) := by
  rw [sum_norm_sq_finiteGroupMaskCoefficient,
    sum_norm_sq_finiteGroupMask]
  have hcard : (Fintype.card G : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

end OneGroup

section ProductGroups

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : I → Type*) [∀ i, AddCommGroup (G i)]
  [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)]

/-- A tuple of classes in a finite family of abelian quotients. -/
abbrev finiteGroupVectors := ∀ i, G i

/-- A tuple of characters, one on each quotient. -/
abbrev finiteGroupCharacterVectors := ∀ i, AddChar (G i) ℂ

/-- Product of the coordinate mean-zero masks. -/
noncomputable def productFiniteGroupMask
    (vanishing : ∀ i, Finset (G i)) (x : finiteGroupVectors G) : ℂ :=
  ∏ i, finiteGroupMask (vanishing i) (x i)

/-- Product of the coordinate normalized Fourier coefficients. -/
noncomputable def productFiniteGroupMaskCoefficient
    (vanishing : ∀ i, Finset (G i))
    (psi : finiteGroupCharacterVectors G) : ℂ :=
  ∏ i, finiteGroupMaskCoefficient (vanishing i) (psi i)

/-- The product character attached to a tuple of coordinate characters. -/
noncomputable def productFiniteGroupAddChar
    (psi : finiteGroupCharacterVectors G) (x : finiteGroupVectors G) : ℂ :=
  ∏ i, psi i (x i)

lemma productFiniteGroupMask_eq_fourierExpansion
    (vanishing : ∀ i, Finset (G i)) (x : finiteGroupVectors G) :
    productFiniteGroupMask G vanishing x =
      ∑ psi : finiteGroupCharacterVectors G,
        productFiniteGroupMaskCoefficient G vanishing psi *
          productFiniteGroupAddChar G psi x := by
  classical
  calc
    productFiniteGroupMask G vanishing x =
        ∏ i, ∑ psi : AddChar (G i) ℂ,
          finiteGroupMaskCoefficient (vanishing i) psi * psi (x i) := by
      unfold productFiniteGroupMask
      apply Finset.prod_congr rfl
      intro i _hi
      exact finiteGroupMask_eq_fourierExpansion (vanishing i) (x i)
    _ = ∑ psi : finiteGroupCharacterVectors G,
        ∏ i, finiteGroupMaskCoefficient (vanishing i) (psi i) *
          psi i (x i) := by
      rw [Finset.prod_univ_sum]
      simp
    _ = ∑ psi : finiteGroupCharacterVectors G,
        productFiniteGroupMaskCoefficient G vanishing psi *
          productFiniteGroupAddChar G psi x := by
      apply Finset.sum_congr rfl
      intro psi _hpsi
      simp only [productFiniteGroupMaskCoefficient,
        productFiniteGroupAddChar, Finset.prod_mul_distrib]

lemma productFiniteGroupMaskCoefficient_eq_zero_of_exists_eq_zero
    (vanishing : ∀ i, Finset (G i))
    (psi : finiteGroupCharacterVectors G) (hzero : ∃ i, psi i = 0) :
    productFiniteGroupMaskCoefficient G vanishing psi = 0 := by
  classical
  obtain ⟨i, hi⟩ := hzero
  unfold productFiniteGroupMaskCoefficient
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa [hi] using finiteGroupMaskCoefficient_zero (vanishing i)

lemma sum_norm_sq_productFiniteGroupMaskCoefficient
    (vanishing : ∀ i, Finset (G i)) :
    (∑ psi : finiteGroupCharacterVectors G,
        ‖productFiniteGroupMaskCoefficient G vanishing psi‖ ^ 2) =
      ∏ i, ((vanishing i).card : ℝ) *
        (Fintype.card (G i) - (vanishing i).card : ℕ) := by
  classical
  calc
    (∑ psi : finiteGroupCharacterVectors G,
        ‖productFiniteGroupMaskCoefficient G vanishing psi‖ ^ 2) =
        ∑ psi : finiteGroupCharacterVectors G,
          ∏ i, ‖finiteGroupMaskCoefficient (vanishing i) (psi i)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro psi _hpsi
      simp only [productFiniteGroupMaskCoefficient, norm_prod,
        Finset.prod_pow]
    _ = ∏ i, ∑ psi : AddChar (G i) ℂ,
        ‖finiteGroupMaskCoefficient (vanishing i) psi‖ ^ 2 := by
      rw [Finset.prod_univ_sum]
      simp
    _ = ∏ i, ((vanishing i).card : ℝ) *
        (Fintype.card (G i) - (vanishing i).card : ℕ) := by
      apply Finset.prod_congr rfl
      intro i _hi
      exact sum_norm_sq_finiteGroupMaskCoefficient_eq (vanishing i)

/-- Character tuples which are nontrivial in every coordinate. -/
noncomputable def allNontrivialFiniteGroupCharacters :
    Finset (finiteGroupCharacterVectors G) := by
  classical
  exact Finset.univ.filter fun psi => ∀ i, psi i ≠ 0

/-- Fourier sum of a function on the product quotient. -/
noncomputable def productFiniteGroupFourierSum
    (f : finiteGroupVectors G → ℂ)
    (psi : finiteGroupCharacterVectors G) : ℂ :=
  ∑ x, f x * productFiniteGroupAddChar G psi x

lemma productFiniteGroupMask_of_avoids
    (vanishing : ∀ i, Finset (G i)) (x : finiteGroupVectors G)
    (hx : ∀ i, x i ∉ vanishing i) :
    productFiniteGroupMask G vanishing x =
      ∏ i, ((vanishing i).card : ℂ) := by
  classical
  unfold productFiniteGroupMask
  apply Finset.prod_congr rfl
  intro i _hi
  exact finiteGroupMask_of_notMem (hx i)

lemma productFiniteGroupMask_weighted_sum
    (vanishing : ∀ i, Finset (G i)) (f : finiteGroupVectors G → ℂ)
    (hvanish : ∀ x, (∃ i, x i ∈ vanishing i) → f x = 0) :
    (∏ i, ((vanishing i).card : ℂ)) * ∑ x, f x =
      ∑ x, f x * productFiniteGroupMask G vanishing x := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases havoid : ∀ i, x i ∉ vanishing i
  · rw [productFiniteGroupMask_of_avoids G vanishing x havoid]
    ring
  · push Not at havoid
    have hfx : f x = 0 := hvanish x havoid
    simp [hfx]

lemma productFiniteGroupMask_pairing_eq_fourierPairing
    (vanishing : ∀ i, Finset (G i)) (f : finiteGroupVectors G → ℂ) :
    (∑ x, f x * productFiniteGroupMask G vanishing x) =
      ∑ psi, productFiniteGroupMaskCoefficient G vanishing psi *
        productFiniteGroupFourierSum G f psi := by
  classical
  simp_rw [productFiniteGroupMask_eq_fourierExpansion G vanishing]
  unfold productFiniteGroupFourierSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro psi _hpsi
  apply Finset.sum_congr rfl
  intro x _hx
  ring

lemma productFiniteGroupFourierPairing_eq_sum_allNontrivial
    (vanishing : ∀ i, Finset (G i)) (f : finiteGroupVectors G → ℂ) :
    (∑ psi, productFiniteGroupMaskCoefficient G vanishing psi *
        productFiniteGroupFourierSum G f psi) =
      ∑ psi ∈ allNontrivialFiniteGroupCharacters G,
        productFiniteGroupMaskCoefficient G vanishing psi *
          productFiniteGroupFourierSum G f psi := by
  classical
  symm
  unfold allNontrivialFiniteGroupCharacters
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro psi _hpsi hnot
  have hnotAll : ¬ ∀ i, psi i ≠ 0 := by
    intro hall
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩)
  push Not at hnotAll
  rw [productFiniteGroupMaskCoefficient_eq_zero_of_exists_eq_zero
    G vanishing psi hnotAll]
  simp

theorem productFiniteGroup_fourier_certificate
    (vanishing : ∀ i, Finset (G i)) (f : finiteGroupVectors G → ℂ)
    (hvanish : ∀ x, (∃ i, x i ∈ vanishing i) → f x = 0) :
    (∏ i, ((vanishing i).card : ℂ)) * ∑ x, f x =
      ∑ psi ∈ allNontrivialFiniteGroupCharacters G,
        productFiniteGroupMaskCoefficient G vanishing psi *
          productFiniteGroupFourierSum G f psi := by
  rw [productFiniteGroupMask_weighted_sum G vanishing f hvanish,
    productFiniteGroupMask_pairing_eq_fourierPairing,
    productFiniteGroupFourierPairing_eq_sum_allNontrivial]

private lemma norm_sum_mul_sq_le
    {A : Type*} (s : Finset A) (a b : A → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
      (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  have hnorm :
      ‖∑ i ∈ s, a i * b i‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
    calc
      _ ≤ ∑ i ∈ s, ‖a i * b i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
        simp_rw [Complex.norm_mul]
  calc
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
        (∑ i ∈ s, ‖a i‖ * ‖b i‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ =>
        mul_nonneg (norm_nonneg (a i)) (norm_nonneg (b i)))).mpr hnorm
    _ ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun i => ‖b i‖)

/-- Montgomery's product uncertainty inequality for an arbitrary finite
family of finite abelian quotients. -/
theorem finiteAbelian_montgomery_uncertainty_product_cross
    (vanishing : ∀ i, Finset (G i)) (f : finiteGroupVectors G → ℂ)
    (hvanish : ∀ x, (∃ i, x i ∈ vanishing i) → f x = 0) :
    (∏ i, ((vanishing i).card : ℝ)) ^ 2 * ‖∑ x, f x‖ ^ 2 ≤
      (∏ i, ((vanishing i).card : ℝ) *
        ((Fintype.card (G i) - (vanishing i).card : ℕ) : ℝ)) *
      ∑ psi ∈ allNontrivialFiniteGroupCharacters G,
        ‖productFiniteGroupFourierSum G f psi‖ ^ 2 := by
  classical
  have hcertificate :=
    productFiniteGroup_fourier_certificate G vanishing f hvanish
  have hcauchy := norm_sum_mul_sq_le
    (allNontrivialFiniteGroupCharacters G)
    (productFiniteGroupMaskCoefficient G vanishing)
    (productFiniteGroupFourierSum G f)
  rw [← hcertificate] at hcauchy
  have hleft :
      ‖(∏ i, ((vanishing i).card : ℂ)) * ∑ x, f x‖ ^ 2 =
        (∏ i, ((vanishing i).card : ℝ)) ^ 2 * ‖∑ x, f x‖ ^ 2 := by
    rw [norm_mul, mul_pow]
    congr 1
    rw [norm_prod]
    simp only [Complex.norm_natCast]
  have hcoeff :
      (∑ psi ∈ allNontrivialFiniteGroupCharacters G,
          ‖productFiniteGroupMaskCoefficient G vanishing psi‖ ^ 2) ≤
        ∏ i, ((vanishing i).card : ℝ) *
          ((Fintype.card (G i) - (vanishing i).card : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ psi, ‖productFiniteGroupMaskCoefficient G vanishing psi‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
        intro psi _hpsi _hnot
        positivity
      _ = _ := sum_norm_sq_productFiniteGroupMaskCoefficient G vanishing
  rw [hleft] at hcauchy
  exact hcauchy.trans (mul_le_mul_of_nonneg_right hcoeff (by positivity))

/-- Ratio form of the finite-abelian product uncertainty principle. -/
theorem finiteAbelian_montgomery_uncertainty_product
    (vanishing : ∀ i, Finset (G i)) (f : finiteGroupVectors G → ℂ)
    (hvanish : ∀ x, (∃ i, x i ∈ vanishing i) → f x = 0)
    (hnonempty : ∀ i, (vanishing i).Nonempty)
    (hproper : ∀ i, (vanishing i).card < Fintype.card (G i)) :
    (∏ i, ((vanishing i).card : ℝ) /
        ((Fintype.card (G i) - (vanishing i).card : ℕ) : ℝ)) *
        ‖∑ x, f x‖ ^ 2 ≤
      ∑ psi ∈ allNontrivialFiniteGroupCharacters G,
        ‖productFiniteGroupFourierSum G f psi‖ ^ 2 := by
  classical
  let W : ℝ := ∏ i, ((vanishing i).card : ℝ)
  let D : ℝ := ∏ i,
    ((Fintype.card (G i) - (vanishing i).card : ℕ) : ℝ)
  let E : ℝ := ∑ psi ∈ allNontrivialFiniteGroupCharacters G,
    ‖productFiniteGroupFourierSum G f psi‖ ^ 2
  let F : ℝ := ‖∑ x, f x‖ ^ 2
  have hWpos : 0 < W := by
    unfold W
    apply Finset.prod_pos
    intro i _hi
    exact_mod_cast Finset.card_pos.mpr (hnonempty i)
  have hDpos : 0 < D := by
    unfold D
    apply Finset.prod_pos
    intro i _hi
    exact_mod_cast Nat.sub_pos_of_lt (hproper i)
  have hcross := finiteAbelian_montgomery_uncertainty_product_cross
    G vanishing f hvanish
  have hcoefficient :
      (∏ i, ((vanishing i).card : ℝ) *
          ((Fintype.card (G i) - (vanishing i).card : ℕ) : ℝ)) =
        W * D := by
    unfold W D
    exact Finset.prod_mul_distrib
  have hcancel : W * F ≤ D * E := by
    apply le_of_mul_le_mul_left (a := W) _ hWpos
    calc
      W * (W * F) = W ^ 2 * F := by ring
      _ ≤ (W * D) * E := by
        simpa only [W, D, E, F, hcoefficient] using hcross
      _ = W * (D * E) := by ring
  have hratio : W / D * F ≤ E := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hDpos]
    simpa [mul_comm] using hcancel
  have hprodRatio :
      (∏ i, ((vanishing i).card : ℝ) /
          ((Fintype.card (G i) - (vanishing i).card : ℕ) : ℝ)) =
        W / D := by
    unfold W D
    rw [Finset.prod_div_distrib]
  simpa only [hprodRatio, E, F] using hratio

/-- The product of coordinate characters, bundled as a character on the
product group. -/
noncomputable def productFiniteGroupAddCharBundled
    (psi : finiteGroupCharacterVectors G) :
    AddChar (finiteGroupVectors G) ℂ where
  toFun := productFiniteGroupAddChar G psi
  map_zero_eq_one' := by
    simp [productFiniteGroupAddChar]
  map_add_eq_mul' := by
    intro x y
    unfold productFiniteGroupAddChar
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _hi
    exact (psi i).map_add_eq_mul (x i) (y i)

@[simp]
lemma productFiniteGroupAddCharBundled_apply
    (psi : finiteGroupCharacterVectors G) (x : finiteGroupVectors G) :
    productFiniteGroupAddCharBundled G psi x =
      productFiniteGroupAddChar G psi x := rfl

private lemma productFiniteGroupAddChar_piSingle
    (psi : finiteGroupCharacterVectors G) (i : I) (x : G i) :
    productFiniteGroupAddChar G psi (Pi.single i x) = psi i x := by
  classical
  unfold productFiniteGroupAddChar
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _hj hji
    rw [Pi.single_eq_of_ne hji]
    simp
  · simp

theorem productFiniteGroupAddCharBundled_injective :
    Function.Injective
      (productFiniteGroupAddCharBundled G :
        finiteGroupCharacterVectors G → AddChar (finiteGroupVectors G) ℂ) := by
  classical
  intro psi chi h
  funext i
  apply DFunLike.ext _ _
  intro x
  let v : finiteGroupVectors G := Pi.single i x
  have hv := DFunLike.congr_fun h v
  change productFiniteGroupAddChar G psi v =
    productFiniteGroupAddChar G chi v at hv
  simpa only [v, productFiniteGroupAddChar_piSingle] using hv

end ProductGroups

end Erdos980.ElliottTail
