import Wikipedia.SzemeredisTheorem.Finite.Bonferroni
import Wikipedia.GreenTao.Sieve.LocalFactors

/-!
# Elementary Euler factors for affine-form systems

For a prime `p`, the local coprimality weight of an affine form is

`p / (p - 1) * 1_{p ∤ ψ(x)}`.

The normalization makes its mean exactly one.  Away from the explicit
exceptional-prime bound, two distinct forms are also exactly decorrelated.
These are the first two local identities in the Euler-product calculation
for the Goldston--Yıldırım estimate.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace AffineForm

/-- The normalized local weight for avoiding the congruence `ψ(x)=0 mod p`. -/
noncomputable def localCoprimeWeight {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (ψ : AffineForm ι ℤ)
    (x : ι → ZMod p) : ℝ :=
  (p : ℝ) / (p - 1 : ℕ) *
    (1 - finsetIndicator (ψ.zeroFinsetZMod p) x)

theorem localCoprimeWeight_eq_zero_of_eval_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (ψ : AffineForm ι ℤ)
    {x : ι → ZMod p} (hx : ψ.evalZMod p x = 0) :
    ψ.localCoprimeWeight p x = 0 := by
  simp [localCoprimeWeight, hx]

theorem localCoprimeWeight_eq_of_eval_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (ψ : AffineForm ι ℤ)
    {x : ι → ZMod p} (hx : ψ.evalZMod p x ≠ 0) :
    ψ.localCoprimeWeight p x =
      (p : ℝ) / (p - 1 : ℕ) := by
  simp [localCoprimeWeight, hx]

theorem localCoprimeWeight_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p]
    (ψ : AffineForm ι ℤ) (x : ι → ZMod p) :
    0 ≤ ψ.localCoprimeWeight p x := by
  by_cases hx : ψ.evalZMod p x = 0
  · rw [localCoprimeWeight_eq_zero_of_eval_eq_zero p ψ hx]
  · rw [localCoprimeWeight_eq_of_eval_ne_zero p ψ hx]
    exact div_nonneg (Nat.cast_nonneg p)
      (Nat.cast_nonneg (p - 1))

/-- A nondegenerate local coprimality weight has mean exactly one. -/
theorem mean_localCoprimeWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (ψ : AffineForm ι ℤ) {i : ι}
    (hi : (ψ.coefficient i : ZMod p) ≠ 0) :
    mean (ψ.localCoprimeWeight p) = 1 := by
  rw [show ψ.localCoprimeWeight p =
      fun x =>
        ((p : ℝ) / (p - 1 : ℕ)) *
          (1 - finsetIndicator (ψ.zeroFinsetZMod p) x) by
    rfl]
  rw [mean_smul, mean_sub, mean_const,
    mean_zeroFinsetZMod hp ψ hi]
  have hp1 : (1 : ℝ) < p := by
    exact_mod_cast hp.one_lt
  have hpred :
      ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    norm_num [Nat.cast_sub hp.one_le]
  rw [hpred]
  have hpm1 : (p : ℝ) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr hp1)
  field_simp [hpm1]

/-- Independent affine congruences have exactly decorrelated normalized
local coprimality weights. -/
theorem mean_localCoprimeWeight_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (ψ φ : AffineForm ι ℤ) {i j : ι}
    (hdet :
      (((ψ.coefficientMinor φ i j : ℤ) : ZMod p)) ≠ 0) :
    mean (fun x =>
      ψ.localCoprimeWeight p x *
        φ.localCoprimeWeight p x) = 1 := by
  let Iψ : (ι → ZMod p) → ℝ :=
    finsetIndicator (ψ.zeroFinsetZMod p)
  let Iφ : (ι → ZMod p) → ℝ :=
    finsetIndicator (φ.zeroFinsetZMod p)
  have hψcoeff :
      (ψ.coefficient i : ZMod p) ≠ 0 ∨
        (ψ.coefficient j : ZMod p) ≠ 0 := by
    by_contra h
    push Not at h
    apply hdet
    simp [coefficientMinor, h.1, h.2]
  have hφcoeff :
      (φ.coefficient i : ZMod p) ≠ 0 ∨
        (φ.coefficient j : ZMod p) ≠ 0 := by
    by_contra h
    push Not at h
    apply hdet
    simp [coefficientMinor, h.1, h.2]
  have hψ : mean Iψ = (1 : ℝ) / p :=
    hψcoeff.elim
      (mean_zeroFinsetZMod hp ψ)
      (mean_zeroFinsetZMod hp ψ)
  have hφ : mean Iφ = (1 : ℝ) / p :=
    hφcoeff.elim
      (mean_zeroFinsetZMod hp φ)
      (mean_zeroFinsetZMod hp φ)
  have hpair :
      mean (fun x => Iψ x * Iφ x) =
        (1 : ℝ) / (p : ℝ) ^ 2 := by
    exact mean_zeroFinsetZMod_mul hp ψ φ hdet
  have hexpand :
      mean (fun x => (1 - Iψ x) * (1 - Iφ x)) =
        1 - mean Iψ - mean Iφ +
          mean (fun x => Iψ x * Iφ x) := by
    calc
      mean (fun x => (1 - Iψ x) * (1 - Iφ x)) =
          mean (fun x =>
            1 - Iψ x - Iφ x + Iψ x * Iφ x) := by
        apply congrArg mean
        funext x
        ring
      _ = 1 - mean Iψ - mean Iφ +
          mean (fun x => Iψ x * Iφ x) := by
        rw [mean_add, mean_sub, mean_sub, mean_const]
  rw [show
    (fun x =>
      ψ.localCoprimeWeight p x *
        φ.localCoprimeWeight p x) =
      fun x =>
        (((p : ℝ) / (p - 1 : ℕ)) ^ 2) *
          ((1 - Iψ x) * (1 - Iφ x)) by
      funext x
      simp only [localCoprimeWeight, Iψ, Iφ]
      ring]
  rw [mean_smul, hexpand, hψ, hφ, hpair]
  have hp1 : (1 : ℝ) < p := by
    exact_mod_cast hp.one_lt
  have hpred :
      ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    norm_num [Nat.cast_sub hp.one_le]
  rw [hpred]
  have hpm1 : (p : ℝ) - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr hp1)
  field_simp [hpm1]
  ring

end AffineForm

/-- The unnormalized indicator that no form in the system vanishes modulo
`p`, written as a product of complementary zero indicators. -/
noncomputable def localAvoidanceProduct
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (x : ι → ZMod p) : ℝ :=
  ∏ q, (1 -
    finsetIndicator ((forms q).zeroFinsetZMod p) x)

/-- The product of all normalized local coprimality weights in a system. -/
noncomputable def systemLocalCoprimeWeight
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (x : ι → ZMod p) : ℝ :=
  ∏ q, (forms q).localCoprimeWeight p x

theorem systemLocalCoprimeWeight_eq
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ)
    (x : ι → ZMod p) :
    systemLocalCoprimeWeight p forms x =
      ((p : ℝ) / (p - 1 : ℕ)) ^ Fintype.card κ *
        localAvoidanceProduct p forms x := by
  unfold systemLocalCoprimeWeight AffineForm.localCoprimeWeight
    localAvoidanceProduct
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]

theorem mean_systemLocalCoprimeWeight_eq
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (p : ℕ) [NeZero p] (forms : κ → AffineForm ι ℤ) :
    mean (systemLocalCoprimeWeight p forms) =
      ((p : ℝ) / (p - 1 : ℕ)) ^ Fintype.card κ *
        mean (localAvoidanceProduct p forms) := by
  rw [show systemLocalCoprimeWeight p forms =
      fun x =>
        (((p : ℝ) / (p - 1 : ℕ)) ^ Fintype.card κ) *
          localAvoidanceProduct p forms x by
    funext x
    exact systemLocalCoprimeWeight_eq p forms x]
  exact mean_smul _ _

/-- The union bound, in complementary-product form, gives the lower local
factor estimate. -/
theorem one_sub_card_div_le_mean_localAvoidanceProduct
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : NonzeroCoefficientVectors forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p) :
    1 - (Fintype.card κ : ℝ) / p ≤
      mean (localAvoidanceProduct p forms) := by
  let I : κ → (ι → ZMod p) → ℝ :=
    fun q => finsetIndicator ((forms q).zeroFinsetZMod p)
  have hpoint (x : ι → ZMod p) :
      1 - ∑ q, I q x ≤
        localAvoidanceProduct p forms x := by
    change
      1 - ∑ q, I q x ≤
        ∏ q, (1 - I q x)
    apply one_sub_sum_le_prod_one_sub
    · intro q
      dsimp [I]
      unfold finsetIndicator
      split <;> norm_num
    · intro q
      dsimp [I]
      unfold finsetIndicator
      split <;> simp
  have hmeanSum :
      mean (fun x => ∑ q, I q x) =
        (Fintype.card κ : ℝ) / p := by
    calc
      mean (fun x => ∑ q, I q x) =
          ∑ q, mean (I q) :=
        mean_finset_sum Finset.univ I
      _ = ∑ _q : κ, (1 : ℝ) / p := by
        apply Fintype.sum_congr
        intro q
        exact mean_zeroFinsetZMod_of_bound
          hforms hp hlarge q
      _ = (Fintype.card κ : ℝ) / p := by
        simp [div_eq_mul_inv]
  calc
    1 - (Fintype.card κ : ℝ) / p =
        mean (fun x => 1 - ∑ q, I q x) := by
      rw [mean_sub, mean_const, hmeanSum]
    _ ≤ mean (localAvoidanceProduct p forms) :=
      mean_mono hpoint

/-- The second Bonferroni inequality and pairwise modular independence give
an `O(p⁻²)` upper correction for the unnormalized avoidance probability. -/
theorem mean_localAvoidanceProduct_le_secondOrder
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p) :
    mean (localAvoidanceProduct p forms) ≤
      1 - (Fintype.card κ : ℝ) / p +
        ((Fintype.card κ *
          (Fintype.card κ - 1) : ℕ) : ℝ) /
            (p : ℝ) ^ 2 := by
  let I : κ → (ι → ZMod p) → ℝ :=
    fun q => finsetIndicator ((forms q).zeroFinsetZMod p)
  let pairs : (ι → ZMod p) → ℝ :=
    fun x =>
      ∑ q, ∑ r ∈ (Finset.univ : Finset κ).erase q,
        I q x * I r x
  have hpoint (x : ι → ZMod p) :
      localAvoidanceProduct p forms x ≤
        1 - ∑ q, I q x + pairs x := by
    change
      (∏ q, (1 - I q x)) ≤
        1 - ∑ q, I q x +
          ∑ q, ∑ r ∈ (Finset.univ : Finset κ).erase q,
            I q x * I r x
    apply prod_one_sub_le_orderedPair_bonferroni
    · intro q
      dsimp [I]
      unfold finsetIndicator
      split <;> norm_num
    · intro q
      dsimp [I]
      unfold finsetIndicator
      split <;> simp
  have hmeanSum :
      mean (fun x => ∑ q, I q x) =
        (Fintype.card κ : ℝ) / p := by
    calc
      mean (fun x => ∑ q, I q x) =
          ∑ q, mean (I q) :=
        mean_finset_sum Finset.univ I
      _ = ∑ _q : κ, (1 : ℝ) / p := by
        apply Fintype.sum_congr
        intro q
        exact mean_zeroFinsetZMod_of_bound
          hnonzero hp hlarge q
      _ = (Fintype.card κ : ℝ) / p := by
        simp [div_eq_mul_inv]
  have hmeanPairs :
      mean pairs =
        ((Fintype.card κ *
          (Fintype.card κ - 1) : ℕ) : ℝ) /
            (p : ℝ) ^ 2 := by
    calc
      mean pairs =
          ∑ q, mean (fun x =>
            ∑ r ∈ (Finset.univ : Finset κ).erase q,
              I q x * I r x) := by
        exact mean_finset_sum Finset.univ
          (fun q x =>
            ∑ r ∈ (Finset.univ : Finset κ).erase q,
              I q x * I r x)
      _ = ∑ q, ∑ r ∈ (Finset.univ : Finset κ).erase q,
          mean (fun x => I q x * I r x) := by
        apply Fintype.sum_congr
        intro q
        exact mean_finset_sum
          ((Finset.univ : Finset κ).erase q)
          (fun r x => I q x * I r x)
      _ = ∑ q, ∑ _r ∈ (Finset.univ : Finset κ).erase q,
          (1 : ℝ) / (p : ℝ) ^ 2 := by
        apply Fintype.sum_congr
        intro q
        apply Finset.sum_congr rfl
        intro r hr
        exact mean_zeroFinsetZMod_mul_of_bound
          hindependent hp hlarge
          (Ne.symm (Finset.mem_erase.mp hr).1)
      _ =
          ((Fintype.card κ *
            (Fintype.card κ - 1) : ℕ) : ℝ) /
              (p : ℝ) ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul,
          Finset.card_erase_of_mem, Finset.mem_univ,
          Finset.card_univ]
        push_cast
        ring
  calc
    mean (localAvoidanceProduct p forms) ≤
        mean (fun x =>
          1 - ∑ q, I q x + pairs x) :=
      mean_mono hpoint
    _ =
        1 - (Fintype.card κ : ℝ) / p +
          ((Fintype.card κ *
            (Fintype.card κ - 1) : ℕ) : ℝ) /
              (p : ℝ) ^ 2 := by
      rw [mean_add, mean_sub, mean_const,
        hmeanSum, hmeanPairs]

/-- Explicit two-sided good-prime bound for the normalized local Euler
factor of a finite system.  The two displayed expressions have matching
constant and first-order terms; their gap starts at order `p⁻²`. -/
theorem mean_systemLocalCoprimeWeight_bounds
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hnonzero : NonzeroCoefficientVectors forms)
    (hindependent : PairwiseIndependentCoefficients forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p) :
    let scale :=
      ((p : ℝ) / (p - 1 : ℕ)) ^ Fintype.card κ
    scale * (1 - (Fintype.card κ : ℝ) / p) ≤
        mean (systemLocalCoprimeWeight p forms) ∧
      mean (systemLocalCoprimeWeight p forms) ≤
        scale *
          (1 - (Fintype.card κ : ℝ) / p +
            ((Fintype.card κ *
              (Fintype.card κ - 1) : ℕ) : ℝ) /
                (p : ℝ) ^ 2) := by
  dsimp only
  have hscale :
      0 ≤ ((p : ℝ) / (p - 1 : ℕ)) ^
        Fintype.card κ := by
    positivity
  rw [mean_systemLocalCoprimeWeight_eq]
  exact
    ⟨mul_le_mul_of_nonneg_left
        (one_sub_card_div_le_mean_localAvoidanceProduct
          hnonzero hp hlarge) hscale,
      mul_le_mul_of_nonneg_left
        (mean_localAvoidanceProduct_le_secondOrder
          hnonzero hindependent hp hlarge) hscale⟩

/-- System-level one-form normalization outside the exceptional-prime
range. -/
theorem mean_localCoprimeWeight_of_bound
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : NonzeroCoefficientVectors forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    (q : κ) :
    mean ((forms q).localCoprimeWeight p) = 1 := by
  obtain ⟨i, hi⟩ :=
    exists_coefficient_cast_ne_zero_of_bound hforms hlarge q
  exact AffineForm.mean_localCoprimeWeight hp (forms q) hi

/-- System-level pair decorrelation outside the exceptional-prime range. -/
theorem mean_localCoprimeWeight_mul_of_bound
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    (hforms : PairwiseIndependentCoefficients forms)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (hlarge : exceptionalPrimeBound forms < p)
    {q r : κ} (hqr : q ≠ r) :
    mean (fun x =>
      (forms q).localCoprimeWeight p x *
        (forms r).localCoprimeWeight p x) = 1 := by
  obtain ⟨i, j, hij⟩ :=
    exists_minor_cast_ne_zero_of_bound hforms hlarge hqr
  exact AffineForm.mean_localCoprimeWeight_mul
    hp (forms q) (forms r) hij

end Wikipedia.SzemeredisTheorem
