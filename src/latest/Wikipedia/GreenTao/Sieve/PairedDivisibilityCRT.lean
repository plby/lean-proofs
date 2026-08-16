import Mathlib.Data.ZMod.QuotientRing
import Wikipedia.SzemeredisTheorem.Finite.ProductMean
import Wikipedia.GreenTao.Sieve.LinearFormsExpansion

/-!
# CRT factorization of paired divisibility densities

The divisor expansion of a product of Selberg weights leaves an exact finite
density `pairedDivisibilityDensity`.  This file isolates the arithmetic steps
which can be performed without any analytic estimate.

First, the two divisor conditions attached to one form are replaced by their
least common multiple.  The resulting zero--one function is identified with
the indicator of its exact finite support, and each nonzero local modulus is
then decomposed into its prime-power divisibility conditions.

Second, normalized means are reindexed by the Chinese remainder theorem.
For any finite pairwise-coprime family of moduli, a product of functions which
depends separately on the corresponding CRT components has mean equal to the
product of its local means.  We specialize this both to two moduli and to the
canonical prime-power decomposition of a nonzero modulus.

For arbitrary natural-valued forms, CRT factorization is not automatic: one
must still show that the global paired divisibility indicator depends on the
CRT components as a product of local indicators.  The final definitions and
theorems package precisely that remaining obligation, without asserting a
false independence statement.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Collapsing paired divisibility conditions -/

/-- The least common multiple of the two divisor choices attached to one
member of the family. -/
def pairedLocalModulus
    {κ : Type*} (z : κ → ℕ × ℕ) (q : κ) : ℕ :=
  Nat.lcm (z q).1 (z q).2

/-- Divisibility by the local modulus is exactly the conjunction of the two
divisibility conditions which created it. -/
theorem pairedLocalModulus_dvd_iff
    {κ : Type*} (z : κ → ℕ × ℕ) (q : κ) (n : ℕ) :
    pairedLocalModulus z q ∣ n ↔
      (z q).1 ∣ n ∧ (z q).2 ∣ n := by
  exact Nat.lcm_dvd_iff

/-- Two divisibility indicators at the same value collapse to the indicator
of the least common multiple.  The statement includes zero moduli. -/
theorem natDivisibilityIndicator_mul_eq_lcm
    (a b n : ℕ) :
    natDivisibilityIndicator a n *
        natDivisibilityIndicator b n =
      natDivisibilityIndicator (Nat.lcm a b) n := by
  simp only [natDivisibilityIndicator, Nat.lcm_dvd_iff]
  by_cases ha : a ∣ n <;> by_cases hb : b ∣ n <;>
    simp [ha, hb]

/-- The paired indicator is the product of the indicators for the local
least common multiples. -/
theorem pairedDivisibilityIndicator_eq_lcmProduct
    {κ X : Type*} [Fintype κ]
    (values : κ → X → ℕ) (z : κ → ℕ × ℕ) (x : X) :
    pairedDivisibilityIndicator values z x =
      ∏ q, natDivisibilityIndicator
        (pairedLocalModulus z q) (values q x) := by
  unfold pairedDivisibilityIndicator
  apply Finset.prod_congr rfl
  intro q _hq
  exact natDivisibilityIndicator_mul_eq_lcm
    (z q).1 (z q).2 (values q x)

/-- The LCM of all paired choices is the LCM of the per-form local moduli. -/
theorem pairedDivisorLcm_eq_lcm_pairedLocalModulus
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z : κ → ℕ × ℕ) :
    pairedDivisorLcm z =
      Finset.univ.lcm (pairedLocalModulus z) := by
  apply Nat.dvd_antisymm
  · rw [pairedDivisorLcm, Finset.lcm_dvd_iff]
    intro q _hq
    cases q with
    | inl q =>
        exact (Nat.dvd_lcm_left (z q).1 (z q).2).trans
          (Finset.dvd_lcm (f := pairedLocalModulus z)
            (Finset.mem_univ q))
    | inr q =>
        exact (Nat.dvd_lcm_right (z q).1 (z q).2).trans
          (Finset.dvd_lcm (f := pairedLocalModulus z)
            (Finset.mem_univ q))
  · rw [Finset.lcm_dvd_iff]
    intro q _hq
    rw [pairedLocalModulus, Nat.lcm_dvd_iff]
    constructor
    · exact Finset.dvd_lcm
        (f := Sum.elim (fun i => (z i).1) (fun i => (z i).2))
        (Finset.mem_univ (Sum.inl q))
    · exact Finset.dvd_lcm
        (f := Sum.elim (fun i => (z i).1) (fun i => (z i).2))
        (Finset.mem_univ (Sum.inr q))

/-- Smooth divisor choices make every per-form local modulus nonzero. -/
theorem pairedLocalModulus_ne_zero_of_mem
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} {z : κ → ℕ × ℕ}
    (hz : z ∈ smoothDivisorFamilyChoices κ R) :
    ∀ q, pairedLocalModulus z q ≠ 0 := by
  intro q
  have hzq := Fintype.mem_piFinset.mp hz q
  have hleft : (z q).1 ≠ 0 :=
    Nat.ne_of_gt
      (Finset.mem_Icc.mp
        (Finset.mem_product.mp hzq).1).1
  have hright : (z q).2 ≠ 0 :=
    Nat.ne_of_gt
      (Finset.mem_Icc.mp
        (Finset.mem_product.mp hzq).2).1
  rw [pairedLocalModulus, ← lcm_eq_nat_lcm]
  exact lcm_ne_zero_iff.mpr ⟨hleft, hright⟩

/-- The exact support of one simultaneous paired-divisibility condition. -/
def pairedDivisibilitySupport
    {κ X : Type*} [Fintype κ] [Fintype X]
    [DecidableEq X]
    (values : κ → X → ℕ) (z : κ → ℕ × ℕ) : Finset X :=
  Finset.univ.filter fun x =>
    ∀ q, pairedLocalModulus z q ∣ values q x

/-- The paired indicator is literally the indicator of its finite support. -/
theorem pairedDivisibilityIndicator_eq_supportIndicator
    {κ X : Type*} [Fintype κ] [Fintype X]
    [DecidableEq X]
    (values : κ → X → ℕ) (z : κ → ℕ × ℕ) :
    pairedDivisibilityIndicator values z =
      finsetIndicator (pairedDivisibilitySupport values z) := by
  classical
  funext x
  rw [pairedDivisibilityIndicator_eq_lcmProduct]
  simp only [pairedDivisibilitySupport, finsetIndicator,
    Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hx :
      ∀ q, pairedLocalModulus z q ∣ values q x
  · simp [hx, natDivisibilityIndicator]
  · rw [if_neg hx]
    simp only [not_forall] at hx
    obtain ⟨q, hq⟩ := hx
    apply Finset.prod_eq_zero (Finset.mem_univ q)
    simp [natDivisibilityIndicator, hq]

/-- The exact density is the cardinality of the simultaneous congruence
support divided by the cardinality of the ambient finite type. -/
theorem pairedDivisibilityDensity_eq_card_support
    {κ X : Type*} [Fintype κ] [Fintype X]
    [DecidableEq X]
    (values : κ → X → ℕ) (z : κ → ℕ × ℕ) :
    pairedDivisibilityDensity values z =
      ((pairedDivisibilitySupport values z).card : ℝ) /
        Fintype.card X := by
  rw [pairedDivisibilityDensity,
    pairedDivisibilityIndicator_eq_supportIndicator]
  exact mean_finsetIndicator _

/-! ## Prime-power divisibility data -/

/-- A prime occurring in a natural-number factorization is nonzero.  This
instance lets the finite `ZMod` API infer finiteness at the associated prime
powers. -/
instance neZero_coe_primeFactor
    {D : ℕ} (p : D.primeFactors) : NeZero (p : ℕ) :=
  ⟨(Nat.prime_of_mem_primeFactors p.2).ne_zero⟩

/-- Divisibility by a nonzero integer is equivalent to divisibility by every
prime power in its canonical factorization. -/
theorem dvd_iff_primePower_dvd
    {d n : ℕ} (hd : d ≠ 0) :
    d ∣ n ↔
      ∀ p : d.primeFactors,
        (p : ℕ) ^ d.factorization p ∣ n := by
  constructor
  · intro h p
    have hp :
        (p : ℕ) ^ d.factorization p ∣
          ∏ q : d.primeFactors,
            (q : ℕ) ^ d.factorization q :=
      Finset.dvd_prod_of_mem
      (fun q : d.primeFactors =>
        (q : ℕ) ^ d.factorization q)
      (Finset.mem_univ p)
    rw [← Nat.prod_primeFactors_coe_pow_factorization hd] at hp
    exact hp.trans h
  · intro h
    have hlcm :
        Finset.univ.lcm
            (fun p : d.primeFactors =>
              (p : ℕ) ^ d.factorization p) ∣ n :=
      Finset.lcm_dvd fun p _hp => h p
    have hpair :
        Set.Pairwise (Finset.univ : Finset d.primeFactors)
          (Nat.Coprime.onFun fun p : d.primeFactors =>
            (p : ℕ) ^ d.factorization p) :=
      d.pairwise_coprime_pow_primeFactors_factorization.set_pairwise _
    rw [Finset.lcm_eq_prod hpair] at hlcm
    rw [← Nat.prod_primeFactors_coe_pow_factorization hd] at hlcm
    exact hlcm

/-- A nonzero-modulus divisibility indicator is the product of its canonical
prime-power divisibility indicators. -/
theorem natDivisibilityIndicator_eq_primePowerProduct
    {d n : ℕ} (hd : d ≠ 0) :
    natDivisibilityIndicator d n =
      ∏ p : d.primeFactors,
        natDivisibilityIndicator
          ((p : ℕ) ^ d.factorization p) n := by
  by_cases hdn : d ∣ n
  · have hlocal :=
      (dvd_iff_primePower_dvd hd).mp hdn
    simp [natDivisibilityIndicator, hdn, hlocal]
  · have hlocal :
        ¬ ∀ p : d.primeFactors,
          (p : ℕ) ^ d.factorization p ∣ n := by
      exact fun h => hdn ((dvd_iff_primePower_dvd hd).mpr h)
    simp only [not_forall] at hlocal
    obtain ⟨p, hp⟩ := hlocal
    rw [show natDivisibilityIndicator d n = 0 by
      simp [natDivisibilityIndicator, hdn]]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    simp [natDivisibilityIndicator, hp]

/-- Prime-power expansion of every local modulus in a paired divisibility
indicator.  Positivity of smooth divisor choices supplies the nonzero
hypothesis in the Selberg expansion. -/
theorem pairedDivisibilityIndicator_eq_primePowerProduct
    {κ X : Type*} [Fintype κ]
    (values : κ → X → ℕ) (z : κ → ℕ × ℕ)
    (hz : ∀ q, pairedLocalModulus z q ≠ 0)
    (x : X) :
    pairedDivisibilityIndicator values z x =
      ∏ q, ∏ p : (pairedLocalModulus z q).primeFactors,
        natDivisibilityIndicator
          ((p : ℕ) ^
            (pairedLocalModulus z q).factorization p)
          (values q x) := by
  rw [pairedDivisibilityIndicator_eq_lcmProduct]
  apply Finset.prod_congr rfl
  intro q _hq
  exact natDivisibilityIndicator_eq_primePowerProduct (hz q)

/-! ## Exact factorization of finite means by CRT -/

/-- Transpose two dependent function coordinates. -/
def piSwapEquiv
    {ι τ : Type*} {α : ι → τ → Type*} :
    (∀ i, ∀ t, α i t) ≃ (∀ t, ∀ i, α i t) where
  toFun x t i := x i t
  invFun x i t := x t i
  left_inv _ := rfl
  right_inv _ := rfl

/-- A dependent version of `prod_mean`: a product of normalized means is the
mean over an independent choice from each (possibly different) finite type. -/
theorem prod_mean_pi
    {τ : Type*} [Fintype τ] [DecidableEq τ]
    {β : τ → Type*}
    [∀ t, Fintype (β t)] [∀ t, Nonempty (β t)]
    (F : ∀ t, β t → ℝ) :
    (∏ t, mean (F t)) =
      mean (fun y : ∀ t, β t => ∏ t, F t (y t)) := by
  classical
  simp_rw [mean, Fintype.expect_eq_sum_div_card]
  rw [Finset.prod_div_distrib, Fintype.prod_sum]
  simp

/-- The mean of a product of functions on two independent finite variables
is the product of their means. -/
theorem mean_prod_separated
    {α β : Type*} [Fintype α] [Fintype β]
    (F : α → ℝ) (G : β → ℝ) :
    mean (fun x : α × β => F x.1 * G x.2) =
      mean F * mean G := by
  calc
    mean (fun x : α × β => F x.1 * G x.2) =
        mean₂ (fun a b => F a * G b) :=
      mean_prod_type
        (fun a : α => fun b : β => F a * G b)
    _ = mean (fun a => F a * mean G) := by
      unfold mean₂
      congr 1
      funext a
      exact mean_smul (F a) G
    _ = mean (fun a => mean G * F a) := by
      congr 1
      funext a
      exact mul_comm _ _
    _ = mean G * mean F :=
      mean_smul (mean G) F
    _ = mean F * mean G := by
      exact mul_comm _ _

/-- Coordinatewise two-modulus Chinese remainder equivalence. -/
def coordinateChineseRemainderEquiv
    {ι : Type*} {m n : ℕ} (h : m.Coprime n) :
    (ι → ZMod (m * n)) ≃
      ((ι → ZMod m) × (ι → ZMod n)) :=
  (Equiv.piCongrRight fun _ =>
      (ZMod.chineseRemainder h).toEquiv).trans
    piProdEquiv

@[simp]
theorem coordinateChineseRemainderEquiv_apply_fst
    {ι : Type*} {m n : ℕ} (h : m.Coprime n)
    (x : ι → ZMod (m * n)) (i : ι) :
    (coordinateChineseRemainderEquiv h x).1 i =
      (ZMod.chineseRemainder h (x i)).1 :=
  rfl

@[simp]
theorem coordinateChineseRemainderEquiv_apply_snd
    {ι : Type*} {m n : ℕ} (h : m.Coprime n)
    (x : ι → ZMod (m * n)) (i : ι) :
    (coordinateChineseRemainderEquiv h x).2 i =
      (ZMod.chineseRemainder h (x i)).2 :=
  rfl

/-- Exact multiplicativity of a separated mean under the two-modulus CRT. -/
theorem mean_coordinateChineseRemainder_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m n : ℕ}
    [NeZero m] [NeZero n]
    (h : m.Coprime n)
    (F : (ι → ZMod m) → ℝ)
    (G : (ι → ZMod n) → ℝ) :
    mean (fun x : ι → ZMod (m * n) =>
      F (coordinateChineseRemainderEquiv h x).1 *
        G (coordinateChineseRemainderEquiv h x).2) =
      mean F * mean G := by
  calc
    mean (fun x : ι → ZMod (m * n) =>
      F (coordinateChineseRemainderEquiv h x).1 *
        G (coordinateChineseRemainderEquiv h x).2) =
        mean (fun y : (ι → ZMod m) × (ι → ZMod n) =>
          F y.1 * G y.2) := by
      unfold mean
      apply Fintype.expect_equiv
        (coordinateChineseRemainderEquiv h)
      intro x
      rfl
    _ = mean F * mean G :=
      mean_prod_separated F G

/-- Coordinatewise CRT for an arbitrary finite pairwise-coprime family of
moduli.  Its output is indexed first by the modulus and then by the ambient
coordinate. -/
noncomputable def coordinateProdEquivPi
    {ι τ : Type*} [Fintype τ]
    (a : τ → ℕ)
    (h : Pairwise (Function.onFun Nat.Coprime a)) :
    (ι → ZMod (∏ t, a t)) ≃
      (∀ t, ι → ZMod (a t)) :=
  (Equiv.piCongrRight fun _ =>
      (ZMod.prodEquivPi a h).toEquiv).trans
    piSwapEquiv

/-- Exact multiplicativity of a separated mean for an arbitrary finite
pairwise-coprime family of moduli. -/
theorem mean_coordinateProdEquivPi
    {ι τ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (a : τ → ℕ) [∀ t, NeZero (a t)]
    [NeZero (∏ t, a t)]
    (h : Pairwise (Function.onFun Nat.Coprime a))
    (localFactor : ∀ t, (ι → ZMod (a t)) → ℝ) :
    mean (fun x : ι → ZMod (∏ t, a t) =>
      ∏ t, localFactor t (coordinateProdEquivPi a h x t)) =
      ∏ t, mean (localFactor t) := by
  classical
  calc
    mean (fun x : ι → ZMod (∏ t, a t) =>
      ∏ t, localFactor t (coordinateProdEquivPi a h x t)) =
        mean (fun y : ∀ t, ι → ZMod (a t) =>
          ∏ t, localFactor t (y t)) := by
      unfold mean
      apply Fintype.expect_equiv
        (coordinateProdEquivPi a h)
      intro x
      rfl
    _ = ∏ t, mean (localFactor t) :=
      (prod_mean_pi localFactor).symm

/-! ## Canonical prime-power CRT -/

/-- Coordinatewise CRT for the canonical prime-power factorization of a
nonzero modulus. -/
noncomputable def coordinatePrimePowerEquiv
    {ι : Type*} {D : ℕ} [NeZero D] :
    (ι → ZMod D) ≃
      (∀ p : D.primeFactors,
        ι → ZMod ((p : ℕ) ^ D.factorization p)) :=
  (Equiv.piCongrRight fun _ =>
      (ZMod.equivPi D (NeZero.ne D)).toEquiv).trans
    piSwapEquiv

/-- A product of prime-power-local functions has exactly multiplicative mean
when pulled back to residue vectors modulo the composite modulus. -/
theorem mean_coordinatePrimePowerEquiv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {D : ℕ} [NeZero D]
    (localFactor :
      ∀ p : D.primeFactors,
        (ι → ZMod ((p : ℕ) ^ D.factorization p)) → ℝ) :
    mean (fun x : ι → ZMod D =>
      ∏ p, localFactor p (coordinatePrimePowerEquiv x p)) =
      ∏ p, mean (localFactor p) := by
  classical
  calc
    mean (fun x : ι → ZMod D =>
      ∏ p, localFactor p (coordinatePrimePowerEquiv x p)) =
        mean (fun y :
          ∀ p : D.primeFactors,
            ι → ZMod ((p : ℕ) ^ D.factorization p) =>
          ∏ p, localFactor p (y p)) := by
      unfold mean
      apply Fintype.expect_equiv
        coordinatePrimePowerEquiv
      intro x
      rfl
    _ = ∏ p, mean (localFactor p) :=
      (prod_mean_pi localFactor).symm

/-! ## Conditional factorization interfaces for paired densities -/

/-- The exact hypothesis needed to factor a paired divisibility indicator
over a pairwise-coprime CRT decomposition. -/
def PairedDivisibilityFactorsOverCRT
    {κ ι τ : Type*} [Fintype κ] [Fintype τ]
    (a : τ → ℕ)
    (h : Pairwise (Function.onFun Nat.Coprime a))
    (values : κ → (ι → ZMod (∏ t, a t)) → ℕ)
    (z : κ → ℕ × ℕ)
    (localFactor : ∀ t, (ι → ZMod (a t)) → ℝ) : Prop :=
  ∀ x,
    pairedDivisibilityIndicator values z x =
      ∏ t, localFactor t (coordinateProdEquivPi a h x t)

/-- Once the pointwise paired indicator separates over the CRT components,
its exact density is the product of the local densities. -/
theorem pairedDivisibilityDensity_eq_prod_localMeans
    {κ ι τ : Type*} [Fintype κ]
    [Fintype ι] [DecidableEq ι]
    [Fintype τ] [DecidableEq τ]
    (a : τ → ℕ) [∀ t, NeZero (a t)]
    [NeZero (∏ t, a t)]
    (h : Pairwise (Function.onFun Nat.Coprime a))
    (values : κ → (ι → ZMod (∏ t, a t)) → ℕ)
    (z : κ → ℕ × ℕ)
    (localFactor : ∀ t, (ι → ZMod (a t)) → ℝ)
    (hfactor :
      PairedDivisibilityFactorsOverCRT
        a h values z localFactor) :
    pairedDivisibilityDensity values z =
      ∏ t, mean (localFactor t) := by
  calc
    pairedDivisibilityDensity values z =
        mean (fun x : ι → ZMod (∏ t, a t) =>
          ∏ t, localFactor t
            (coordinateProdEquivPi a h x t)) := by
      unfold pairedDivisibilityDensity
      congr 1
      funext x
      exact hfactor x
    _ = ∏ t, mean (localFactor t) :=
      mean_coordinateProdEquivPi a h localFactor

/-- The exact hypothesis needed to factor a paired indicator over the
canonical prime-power CRT decomposition of a nonzero modulus. -/
def PairedDivisibilityFactorsOverPrimePowers
    {κ ι : Type*} [Fintype κ]
    {D : ℕ} [NeZero D]
    (values : κ → (ι → ZMod D) → ℕ)
    (z : κ → ℕ × ℕ)
    (localFactor :
      ∀ p : D.primeFactors,
        (ι → ZMod ((p : ℕ) ^ D.factorization p)) → ℝ) : Prop :=
  ∀ x,
    pairedDivisibilityIndicator values z x =
      ∏ p, localFactor p (coordinatePrimePowerEquiv x p)

/-- Canonical prime-power factorization of a paired divisibility density,
conditional only on the explicit pointwise local-separation statement. -/
theorem pairedDivisibilityDensity_eq_prod_primePowerMeans
    {κ ι : Type*} [Fintype κ]
    [Fintype ι] [DecidableEq ι]
    {D : ℕ} [NeZero D]
    (values : κ → (ι → ZMod D) → ℕ)
    (z : κ → ℕ × ℕ)
    (localFactor :
      ∀ p : D.primeFactors,
        (ι → ZMod ((p : ℕ) ^ D.factorization p)) → ℝ)
    (hfactor :
      PairedDivisibilityFactorsOverPrimePowers
        values z localFactor) :
    pairedDivisibilityDensity values z =
      ∏ p, mean (localFactor p) := by
  calc
    pairedDivisibilityDensity values z =
        mean (fun x : ι → ZMod D =>
          ∏ p, localFactor p (coordinatePrimePowerEquiv x p)) := by
      unfold pairedDivisibilityDensity
      congr 1
      funext x
      exact hfactor x
    _ = ∏ p, mean (localFactor p) :=
      mean_coordinatePrimePowerEquiv localFactor

end Wikipedia.SzemeredisTheorem
