/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 235.
https://www.erdosproblems.com/forum/thread/235

Informal authors:
- Christopher Hooley

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos235.md
-/
import Mathlib
import Wikipedia.GreenTao.Sieve.CongruenceAverage
import ErdosProblems.Erdos387.BrunSieve

/-!
# Erdős Problem 235

Let `Nₖ` be the product of the first `k` primes and list the integers below
`Nₖ` which are coprime to `Nₖ`.  Hooley proved that the consecutive gaps,
divided by their mean `Nₖ / φ(Nₖ)`, have the exponential distribution of
mean one.  This file gives the finite definitions used by the statement and
formalizes that result.

The order-free predicate `IsInternalConsecutive` is equivalent to saying
that its two arguments occur consecutively in the increasing enumeration of
the reduced residues.  Thus `gapCDF` is exactly the quotient in the problem;
in particular, its denominator is `φ(Nₖ)`, although there are only
`φ(Nₖ) - 1` internal gaps.
-/

open Filter Finset Real Set Topology
open scoped BigOperators

namespace Erdos235

noncomputable section

/-- The `k`-th prime, with zero-based indexing. -/
def nthPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime k

/-- `Nₖ`, the product of the first `k` primes.  Consequently `N₀ = 1`,
`N₁ = 2`, and `N₂ = 2 * 3`.  Dropping this harmless initial shift has no
effect on the limit at infinity. -/
def primeProduct (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, nthPrime i

@[simp] theorem primeProduct_zero : primeProduct 0 = 1 := by
  simp [primeProduct]

@[simp] theorem primeProduct_succ (k : ℕ) :
    primeProduct (k + 1) = primeProduct k * nthPrime k := by
  simp [primeProduct, Finset.prod_range_succ]

theorem nthPrime_prime (k : ℕ) : (nthPrime k).Prime := by
  exact Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k

theorem nthPrime_two_le (k : ℕ) : 2 ≤ nthPrime k :=
  (nthPrime_prime k).two_le

theorem nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

theorem tendsto_nthPrime_atTop : Tendsto nthPrime atTop atTop :=
  nthPrime_strictMono.tendsto_atTop

/-- Increasing enumeration identifies the natural numbers with the subtype
of primes. -/
noncomputable def primeEquiv : ℕ ≃ Nat.Primes where
  toFun k := ⟨nthPrime k, nthPrime_prime k⟩
  invFun p := Nat.count Nat.Prime p
  left_inv k := Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime k
  right_inv p := Subtype.ext (Nat.nth_count p.property)

theorem tendsto_sum_reciprocal_nthPrime :
    Tendsto (fun k ↦ ∑ i ∈ Finset.range k, (1 : ℝ) / nthPrime i)
      atTop atTop := by
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun i ↦ by positivity)).mp
  intro hs
  apply Nat.Primes.not_summable_one_div
  apply (primeEquiv.summable_iff).mp
  have hs' : Summable
      ((fun p : Nat.Primes ↦ (1 : ℝ) / (p : ℕ)) ∘ primeEquiv) := by
    convert hs using 1
    funext i
    rfl
  exact hs'

theorem primeProduct_pos (k : ℕ) : 0 < primeProduct k := by
  unfold primeProduct
  exact Finset.prod_pos fun i hi ↦ (nthPrime_prime i).pos

theorem primeProduct_ne_zero (k : ℕ) : primeProduct k ≠ 0 :=
  (primeProduct_pos k).ne'

instance (k : ℕ) : NeZero (primeProduct k) :=
  ⟨primeProduct_ne_zero k⟩

theorem primeProduct_coprime_nthPrime (k : ℕ) :
    (primeProduct k).Coprime (nthPrime k) := by
  unfold primeProduct
  apply Nat.Coprime.prod_left
  intro i hi
  exact (Nat.coprime_primes (nthPrime_prime i) (nthPrime_prime k)).mpr
    (ne_of_lt (nthPrime_strictMono (Finset.mem_range.mp hi)))

theorem totient_primeProduct_succ (k : ℕ) :
    (primeProduct (k + 1)).totient =
      (primeProduct k).totient * (nthPrime k - 1) := by
  rw [primeProduct_succ, Nat.totient_mul (primeProduct_coprime_nthPrime k),
    Nat.totient_prime (nthPrime_prime k)]

theorem totient_primeProduct (k : ℕ) :
    (primeProduct k).totient =
      ∏ i ∈ Finset.range k, (nthPrime i - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [totient_primeProduct_succ, ih, Finset.prod_range_succ]

/-- Density of reduced residue classes modulo `Nₖ`. -/
noncomputable def primorialDensity (k : ℕ) : ℝ :=
  ((primeProduct k).totient : ℝ) / (primeProduct k : ℝ)

/-- Mean gap between reduced residue classes modulo `Nₖ`. -/
noncomputable def meanGap (k : ℕ) : ℝ :=
  (primeProduct k : ℝ) / ((primeProduct k).totient : ℝ)

/-- The integral threshold corresponding exactly to the real inequality
`gap ≤ c * N / φ(N)`. -/
def normalizedThreshold (N : ℕ) (c : ℝ) : ℕ :=
  ⌊c * (N : ℝ) / (N.totient : ℝ)⌋₊

theorem primorialDensity_pos (k : ℕ) : 0 < primorialDensity k := by
  unfold primorialDensity
  exact div_pos
    (by exact_mod_cast (Nat.totient_pos.mpr (primeProduct_pos k)))
    (by exact_mod_cast primeProduct_pos k)

theorem meanGap_pos (k : ℕ) : 0 < meanGap k := by
  unfold meanGap
  exact div_pos (by exact_mod_cast primeProduct_pos k)
    (by exact_mod_cast (Nat.totient_pos.mpr (primeProduct_pos k)))

theorem meanGap_eq_inv_density (k : ℕ) :
    meanGap k = (primorialDensity k)⁻¹ := by
  unfold meanGap primorialDensity
  rw [inv_div]

theorem primorialDensity_eq_prod (k : ℕ) :
    primorialDensity k =
      ∏ i ∈ Finset.range k, (1 - (1 : ℝ) / nthPrime i) := by
  rw [primorialDensity, totient_primeProduct, primeProduct]
  push_cast
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hp1 : 1 ≤ nthPrime i := (nthPrime_prime i).one_le
  rw [Nat.cast_sub hp1]
  have hp0 : (nthPrime i : ℝ) ≠ 0 := by
    exact_mod_cast (nthPrime_prime i).ne_zero
  field_simp
  norm_num

theorem tendsto_primorialDensity_zero :
    Tendsto primorialDensity atTop (𝓝 0) := by
  let reciprocalSum : ℕ → ℝ := fun k ↦
    ∑ i ∈ Finset.range k, (1 : ℝ) / nthPrime i
  have hsum : Tendsto reciprocalSum atTop atTop := by
    simpa [reciprocalSum] using tendsto_sum_reciprocal_nthPrime
  have hupper (k : ℕ) :
      primorialDensity k ≤ Real.exp (-reciprocalSum k) := by
    rw [primorialDensity_eq_prod]
    calc
      (∏ i ∈ Finset.range k, (1 - (1 : ℝ) / nthPrime i)) ≤
          ∏ i ∈ Finset.range k,
            Real.exp (-((1 : ℝ) / nthPrime i)) := by
        apply Finset.prod_le_prod
        · intro i hi
          have hp0 : (0 : ℝ) < nthPrime i := by
            exact_mod_cast (nthPrime_prime i).pos
          have hp1 : (1 : ℝ) ≤ nthPrime i := by
            exact_mod_cast (nthPrime_prime i).one_le
          exact sub_nonneg.mpr ((div_le_one₀ hp0).mpr hp1)
        · intro i hi
          linarith [Real.add_one_le_exp (-((1 : ℝ) / nthPrime i))]
      _ = Real.exp (-reciprocalSum k) := by
        rw [← Real.exp_sum]
        simp [reciprocalSum]
  apply squeeze_zero
  · exact fun k ↦ (primorialDensity_pos k).le
  · exact hupper
  · exact Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp hsum)

theorem tendsto_meanGap_atTop : Tendsto meanGap atTop atTop := by
  have hpositive : Tendsto primorialDensity atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_inf.mpr ⟨tendsto_primorialDensity_zero, ?_⟩
    exact tendsto_principal.mpr
      (Filter.Eventually.of_forall fun k ↦ primorialDensity_pos k)
  have hfun : meanGap = primorialDensity⁻¹ := by
    funext k
    exact meanGap_eq_inv_density k
  rw [hfun]
  exact hpositive.inv_tendsto_nhdsGT_zero

theorem tendsto_scaledThreshold_mul_density (c : ℝ) (hc : 0 ≤ c) :
    Tendsto
      (fun k ↦
        (normalizedThreshold (primeProduct k) c : ℝ) *
          primorialDensity k)
      atTop (𝓝 c) := by
  have hfloor :=
    (tendsto_nat_floor_mul_div_atTop (R := ℝ) hc).comp
      tendsto_meanGap_atTop
  have hfun :
      (fun k ↦
        (normalizedThreshold (primeProduct k) c : ℝ) *
          primorialDensity k) =
      (fun k ↦ (⌊c * meanGap k⌋₊ : ℝ) / meanGap k) := by
    funext k
    simp only [normalizedThreshold, primorialDensity, meanGap]
    have hN : (primeProduct k : ℝ) ≠ 0 := by
      exact_mod_cast primeProduct_ne_zero k
    have hφ : ((primeProduct k).totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr (primeProduct_pos k)).ne'
    have harg :
        c * (primeProduct k : ℝ) / ((primeProduct k).totient : ℝ) =
          c * ((primeProduct k : ℝ) /
            ((primeProduct k).totient : ℝ)) := by ring
    rw [harg]
    field_simp
  rw [hfun]
  exact hfloor

theorem tendsto_normalizedThreshold_atTop (c : ℝ) (hc : 0 < c) :
    Tendsto (fun k ↦ normalizedThreshold (primeProduct k) c)
      atTop atTop := by
  have hscaled : Tendsto (fun k ↦ c * meanGap k) atTop atTop :=
    tendsto_meanGap_atTop.const_mul_atTop hc
  have hfloor := tendsto_nat_floor_atTop.comp hscaled
  convert hfloor using 1
  funext k
  unfold normalizedThreshold meanGap
  congr 1
  ring

/-- The reduced residues in the standard interval `[0, N)`. -/
def reducedResidues (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun a ↦ a.Coprime N

@[simp] theorem mem_reducedResidues {N a : ℕ} :
    a ∈ reducedResidues N ↔ a < N ∧ a.Coprime N := by
  simp [reducedResidues]

theorem card_reducedResidues (N : ℕ) :
    (reducedResidues N).card = N.totient := by
  simpa [reducedResidues, Nat.Coprime, Nat.gcd_comm] using
    (Nat.totient_eq_card_coprime N).symm

/-! ## The cyclic reduced-residue model -/

/-- Reduced residue classes modulo `N`, represented intrinsically in
`ZMod N`. -/
noncomputable def cyclicReducedResidues (N : ℕ) [NeZero N] :
    Finset (ZMod N) := by
  classical
  exact Finset.univ.filter IsUnit

@[simp] theorem mem_cyclicReducedResidues {N : ℕ} [NeZero N]
    {a : ZMod N} :
    a ∈ cyclicReducedResidues N ↔ IsUnit a := by
  classical
  simp [cyclicReducedResidues]

/-- Units, regarded as elements of the ring, are equivalent to the subtype
of unit elements. -/
noncomputable def unitsEquivIsUnitSubtype (N : ℕ) [NeZero N] :
    (ZMod N)ˣ ≃ {a : ZMod N // IsUnit a} where
  toFun u := ⟨u, u.isUnit⟩
  invFun a := a.2.unit
  left_inv u := Units.ext (by simp)
  right_inv a := Subtype.ext (by simp)

theorem card_cyclicReducedResidues (N : ℕ) [NeZero N] :
    (cyclicReducedResidues N).card = N.totient := by
  classical
  have hcard : Fintype.card {a : ZMod N // IsUnit a} = N.totient := by
    calc
      Fintype.card {a : ZMod N // IsUnit a} = Fintype.card (ZMod N)ˣ :=
        (Fintype.card_congr (unitsEquivIsUnitSubtype N)).symm
      _ = N.totient := ZMod.card_units_eq_totient N
  change (Finset.univ.filter (fun a : ZMod N ↦ IsUnit a)).card = N.totient
  rw [← Fintype.card_subtype (fun a : ZMod N ↦ IsUnit a)]
  exact hcard

/-- Number of reduced classes among the first `m` positive cyclic
displacements from `a`. -/
noncomputable def cyclicLocalCount (N m : ℕ) [NeZero N]
    (a : ZMod N) : ℕ := by
  classical
  exact ((Finset.Icc 1 m).filter fun h : ℕ ↦
    IsUnit (a + (h : ZMod N))).card

/-- Reduced starting classes whose next `m` positive cyclic displacements
contain no reduced class. -/
noncomputable def cyclicVoidStarts (N m : ℕ) [NeZero N] :
    Finset (ZMod N) := by
  classical
  exact (cyclicReducedResidues N).filter fun a ↦
    cyclicLocalCount N m a = 0

/-- The cyclic void probability, normalized by `φ(N)`. -/
noncomputable def cyclicVoidRatio (N m : ℕ) [NeZero N] : ℝ :=
  ((cyclicVoidStarts N m).card : ℝ) / (N.totient : ℝ)

/-- The circular short-gap distribution obtained by complementing the void
event. -/
noncomputable def cyclicGapCDF (N m : ℕ) [NeZero N] : ℝ :=
  1 - cyclicVoidRatio N m

/-! ## Local correlations and the truncated singular series -/

/-- Residue classes occupied modulo `p` by the shifts
`0, h 0, ..., h (r-1)`. -/
noncomputable def shiftResidues {r : ℕ} (p : ℕ) (h : Fin r → ℕ) :
    Finset ℕ := by
  classical
  exact insert 0 (Finset.univ.image fun i ↦ h i % p)

/-- Number of distinct occupied residue classes modulo `p`. -/
noncomputable def localMultiplicity {r : ℕ} (p : ℕ) (h : Fin r → ℕ) : ℕ :=
  (shiftResidues p h).card

/-- The same occupied residue set, now represented in `ZMod p`. -/
noncomputable def zmodShiftResidues {r : ℕ} (p : ℕ) (h : Fin r → ℕ) :
    Finset (ZMod p) := by
  classical
  exact insert 0 (Finset.univ.image fun i ↦ (h i : ZMod p))

theorem mem_shiftResidues_iff {r p x : ℕ} {h : Fin r → ℕ} :
    x ∈ shiftResidues p h ↔ x = 0 ∨ ∃ i, h i % p = x := by
  classical
  simp [shiftResidues, eq_comm]

theorem zmodShiftResidues_eq_image {r p : ℕ} (h : Fin r → ℕ) :
    zmodShiftResidues p h =
      (shiftResidues p h).image (fun x : ℕ ↦ (x : ZMod p)) := by
  classical
  unfold zmodShiftResidues shiftResidues
  rw [Finset.image_insert, Finset.image_image]
  simp only [Nat.cast_zero]
  congr 1
  apply Finset.image_congr
  intro i hi
  exact ((ZMod.natCast_eq_natCast_iff' (h i % p) (h i) p).mpr
    (Nat.mod_mod_of_dvd (h i) (dvd_refl p))).symm

theorem card_zmodShiftResidues {r p : ℕ} (hp : 0 < p)
    (h : Fin r → ℕ) :
    (zmodShiftResidues p h).card = localMultiplicity p h := by
  classical
  rw [zmodShiftResidues_eq_image, localMultiplicity,
    Finset.card_image_iff.mpr]
  intro x hx y hy hxy
  have hxlt : x < p := by
    change x ∈ shiftResidues p h at hx
    rw [mem_shiftResidues_iff] at hx
    rcases hx with rfl | ⟨i, rfl⟩
    · exact hp
    · exact Nat.mod_lt _ hp
  have hylt : y < p := by
    change y ∈ shiftResidues p h at hy
    rw [mem_shiftResidues_iff] at hy
    rcases hy with rfl | ⟨i, rfl⟩
    · exact hp
    · exact Nat.mod_lt _ hp
  have hv := congrArg ZMod.val hxy
  simpa [ZMod.val_natCast_of_lt hxlt, ZMod.val_natCast_of_lt hylt] using hv

/-- Residues `a mod p` for which none of
`a, a + h 0, ..., a + h (r-1)` vanishes. -/
noncomputable def locallyAllowedResidues {r p : ℕ} [NeZero p]
    (h : Fin r → ℕ) : Finset (ZMod p) := by
  classical
  exact Finset.univ \ (zmodShiftResidues p h).image fun x ↦ -x

theorem mem_locallyAllowedResidues_iff {r p : ℕ} [NeZero p]
    {h : Fin r → ℕ} {a : ZMod p} :
    a ∈ locallyAllowedResidues h ↔
      a ≠ 0 ∧ ∀ i, a + (h i : ZMod p) ≠ 0 := by
  classical
  simp only [locallyAllowedResidues, Finset.mem_sdiff, Finset.mem_univ,
    true_and]
  have hmem :
      a ∈ (zmodShiftResidues p h).image (fun x ↦ -x) ↔
        -a ∈ zmodShiftResidues p h := by
    constructor
    · intro ha
      obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp ha
      have hax : -a = x := by
        rw [← hxa]
        simp
      simpa [hax] using hx
    · intro ha
      exact Finset.mem_image.mpr ⟨-a, ha, by simp⟩
  rw [hmem]
  simp only [zmodShiftResidues, Finset.mem_insert, Finset.mem_image,
    Finset.mem_univ, true_and, not_or, not_exists, neg_eq_zero]
  constructor
  · rintro ⟨ha0, ha⟩
    refine ⟨ha0, ?_⟩
    intro i hai
    apply ha i
    rw [add_eq_zero_iff_eq_neg] at hai
    simpa using (congrArg Neg.neg hai).symm
  · rintro ⟨ha0, ha⟩
    refine ⟨ha0, ?_⟩
    intro i hai
    apply ha i
    rw [hai]
    simp

theorem card_locallyAllowedResidues {r p : ℕ} [NeZero p]
    (hp : 0 < p) (h : Fin r → ℕ) :
    (locallyAllowedResidues (p := p) h).card =
      p - localMultiplicity p h := by
  classical
  change
    ((Finset.univ : Finset (ZMod p)) \
      (zmodShiftResidues p h).image (fun x : ZMod p ↦ -x)).card =
        p - localMultiplicity p h
  have hsubset :
      (zmodShiftResidues p h).image (fun x : ZMod p ↦ -x) ⊆
        (Finset.univ : Finset (ZMod p)) := Finset.subset_univ _
  rw [Finset.card_sdiff_of_subset hsubset,
    Finset.card_univ, ZMod.card]
  congr 1
  rw [Finset.card_image_of_injective]
  · exact card_zmodShiftResidues hp h
  · intro x y hxy
    simpa using congrArg Neg.neg hxy

theorem localMultiplicity_pos {r p : ℕ} (h : Fin r → ℕ) :
    0 < localMultiplicity p h := by
  unfold localMultiplicity
  exact Finset.card_pos.mpr (by
    classical
    exact ⟨0, mem_shiftResidues_iff.mpr (Or.inl rfl)⟩)

theorem localMultiplicity_le_card_add_one {r p : ℕ} (h : Fin r → ℕ) :
    localMultiplicity p h ≤ r + 1 := by
  classical
  unfold localMultiplicity shiftResidues
  calc
    (insert 0 (Finset.univ.image fun i : Fin r ↦ h i % p)).card ≤
        (Finset.univ.image fun i : Fin r ↦ h i % p).card + 1 :=
      Finset.card_insert_le _ _
    _ ≤ r + 1 := by
      gcongr
      exact (Finset.card_image_le.trans_eq (Fintype.card_fin r))

theorem localMultiplicity_le {r p : ℕ} (hp : 0 < p) (h : Fin r → ℕ) :
    localMultiplicity p h ≤ p := by
  classical
  unfold localMultiplicity
  calc
    (shiftResidues p h).card ≤ (Finset.range p).card := by
      apply Finset.card_le_card
      intro x hx
      rw [mem_shiftResidues_iff] at hx
      rw [Finset.mem_range]
      rcases hx with rfl | ⟨i, rfl⟩
      · exact hp
      · exact Nat.mod_lt _ hp
    _ = p := Finset.card_range p

theorem localMultiplicity_eq_card_add_one {r p : ℕ} (h : Fin r → ℕ)
    (hzero : ∀ i, h i % p ≠ 0)
    (hinj : Function.Injective fun i ↦ h i % p) :
    localMultiplicity p h = r + 1 := by
  classical
  unfold localMultiplicity shiftResidues
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_image_of_injective Finset.univ hinj]
    simp
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i hi
    exact hzero i hi

/-- The normalized local Euler factor belonging to the indexed shifts
`0, h 0, ..., h (r-1)`. -/
noncomputable def localFactor {r : ℕ} (p : ℕ) (h : Fin r → ℕ) : ℝ :=
  (1 - (localMultiplicity p h : ℝ) / p) /
    (1 - (1 : ℝ) / p) ^ (r + 1)

/-- Hooley's singular series, truncated at the prime cutoff `y`. -/
noncomputable def truncatedSingularSeries {r : ℕ} (y : ℕ)
    (h : Fin r → ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE y, localFactor p h

theorem localFactor_nonneg {r p : ℕ} (hp : p.Prime)
    (h : Fin r → ℕ) : 0 ≤ localFactor p h := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hν : (localMultiplicity p h : ℝ) ≤ p := by
    exact_mod_cast localMultiplicity_le hp.pos h
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hnum : 0 ≤ 1 - (localMultiplicity p h : ℝ) / p := by
    exact sub_nonneg.mpr (div_le_one₀ hp0 |>.mpr hν)
  have hden : 0 ≤ (1 - (1 : ℝ) / p) ^ (r + 1) := by
    exact pow_nonneg
      (sub_nonneg.mpr ((div_le_one₀ hp0).mpr hp1.le)) _
  unfold localFactor
  exact div_nonneg hnum hden

theorem truncatedSingularSeries_nonneg {r y : ℕ} (h : Fin r → ℕ) :
    0 ≤ truncatedSingularSeries y h := by
  unfold truncatedSingularSeries
  exact Finset.prod_nonneg fun p hp ↦
    localFactor_nonneg (Nat.mem_primesLE.mp hp).2 h

/-! ## Exact CRT correlation -/

/-- The prime modulus in coordinate `i` of the first-`k`-primes CRT. -/
def primeModulus (k : ℕ) (i : Fin k) : ℕ := nthPrime i

instance (k : ℕ) (i : Fin k) : NeZero (primeModulus k i) :=
  ⟨(nthPrime_prime i).ne_zero⟩

theorem primeModulus_pairwise_coprime (k : ℕ) :
    Pairwise (Function.onFun Nat.Coprime (primeModulus k)) := by
  intro i j hij
  exact (Nat.coprime_primes (nthPrime_prime i) (nthPrime_prime j)).mpr
    (fun h ↦ hij (Fin.ext ((nthPrime_strictMono.injective h))))

theorem prod_primeModulus (k : ℕ) :
    (∏ i : Fin k, primeModulus k i) = primeProduct k := by
  simpa [primeModulus, primeProduct] using
    (Fin.prod_univ_eq_prod_range nthPrime k)

/-- The Chinese-remainder equivalence for the product of the first `k`
primes. -/
noncomputable def primeProductCRT (k : ℕ) :
    ZMod (primeProduct k) ≃+* (∀ i : Fin k, ZMod (primeModulus k i)) :=
  (ZMod.ringEquivCongr (prod_primeModulus k).symm).trans
    (ZMod.prodEquivPi (primeModulus k) (primeModulus_pairwise_coprime k))

@[simp] theorem primeProductCRT_natCast_apply (k n : ℕ) (i : Fin k) :
    primeProductCRT k (n : ZMod (primeProduct k)) i =
      (n : ZMod (primeModulus k i)) := by
  exact congrFun (map_natCast (primeProductCRT k) n) i

/-- The singular series over precisely the first `k` primes. -/
noncomputable def indexedSingularSeries {r : ℕ} (k : ℕ)
    (h : Fin r → ℕ) : ℝ :=
  ∏ i : Fin k, localFactor (primeModulus k i) h

theorem indexedSingularSeries_nonneg {r k : ℕ} (h : Fin r → ℕ) :
    0 ≤ indexedSingularSeries k h := by
  unfold indexedSingularSeries
  exact Finset.prod_nonneg fun i hi ↦
    localFactor_nonneg (nthPrime_prime i) h

/-- Residues modulo `Nₖ` for which the starting class and all the displayed
shifts are reduced. -/
noncomputable def jointReducedResidues {r : ℕ} (k : ℕ)
    (h : Fin r → ℕ) : Finset (ZMod (primeProduct k)) := by
  classical
  exact Finset.univ.filter fun a ↦
    IsUnit a ∧ ∀ i, IsUnit (a + (h i : ZMod (primeProduct k)))

@[simp] theorem mem_jointReducedResidues {r k : ℕ} {h : Fin r → ℕ}
    {a : ZMod (primeProduct k)} :
    a ∈ jointReducedResidues k h ↔
      IsUnit a ∧ ∀ i, IsUnit (a + (h i : ZMod (primeProduct k))) := by
  classical
  simp [jointReducedResidues]

/-- Under the first-primes CRT, simultaneous coprimality of the starting
residue and all shifts is exactly coordinatewise avoidance of the local
forbidden residues. -/
theorem jointReduced_iff_coordinates {r k : ℕ} (h : Fin r → ℕ)
    (a : ZMod (primeProduct k)) :
    (IsUnit a ∧ ∀ j, IsUnit (a + (h j : ZMod (primeProduct k)))) ↔
      ∀ i : Fin k,
        primeProductCRT k a i ∈
          locallyAllowedResidues (p := primeModulus k i) h := by
  letI (i : Fin k) : Fact (Nat.Prime (primeModulus k i)) :=
    ⟨nthPrime_prime i⟩
  have hunit (x : ZMod (primeProduct k)) :
      IsUnit x ↔ ∀ i, primeProductCRT k x i ≠ 0 := by
    rw [← isUnit_map_iff (primeProductCRT k) x, Pi.isUnit_iff]
    simp only [isUnit_iff_ne_zero]
  simp only [mem_locallyAllowedResidues_iff, hunit, map_add]
  aesop

private theorem card_filter_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (P : α → Prop) [DecidablePred P] :
    ((Finset.univ : Finset α).filter P).card =
      ((Finset.univ : Finset β).filter (fun y ↦ P (e.symm y))).card := by
  let E : {x : α // P x} ≃ {y : β // P (e.symm y)} :=
    { toFun := fun x ↦ ⟨e x, by simpa using x.2⟩
      invFun := fun y ↦ ⟨e.symm y, y.2⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro y; apply Subtype.ext; simp }
  rw [← Fintype.card_subtype P,
    ← Fintype.card_subtype (fun y : β ↦ P (e.symm y))]
  exact Fintype.card_congr E

private theorem card_filter_pi_mem
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [(i : ι) → Fintype (α i)]
    [(i : ι) → DecidableEq (α i)] (s : (i : ι) → Finset (α i)) :
    ((Finset.univ : Finset ((i : ι) → α i)).filter
      (fun x ↦ ∀ i, x i ∈ s i)).card = ∏ i, (s i).card := by
  classical
  let E :
      {x : (i : ι) → α i // ∀ i, x i ∈ s i} ≃
        ((i : ι) → ↥(s i)) :=
    { toFun := fun x i ↦ ⟨x.1 i, x.2 i⟩
      invFun := fun x ↦ ⟨fun i ↦ x i, fun i ↦ (x i).2⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; funext i; rfl }
  rw [← Fintype.card_subtype (fun x : (i : ι) → α i ↦
    ∀ i, x i ∈ s i)]
  rw [Fintype.card_congr E, Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro i hi
  exact Fintype.card_coe (s i)

/-- Exact CRT count of simultaneous reduced shifts. -/
theorem card_jointReducedResidues {r k : ℕ} (h : Fin r → ℕ) :
    (jointReducedResidues k h).card =
      ∏ i : Fin k,
        (primeModulus k i - localMultiplicity (primeModulus k i) h) := by
  classical
  let P : ZMod (primeProduct k) → Prop := fun a ↦
    IsUnit a ∧ ∀ j, IsUnit (a + (h j : ZMod (primeProduct k)))
  change ((Finset.univ.filter P).card) = _
  rw [card_filter_equiv (primeProductCRT k).toEquiv P]
  calc
    ((Finset.univ.filter
        (fun y : (∀ i : Fin k, ZMod (primeModulus k i)) ↦
          P ((primeProductCRT k).symm y))).card) =
        ((Finset.univ.filter
          (fun y : (∀ i : Fin k, ZMod (primeModulus k i)) ↦ ∀ i, y i ∈
          locallyAllowedResidues (p := primeModulus k i) h)).card) := by
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro y hy
      simpa [P] using
        (jointReduced_iff_coordinates h ((primeProductCRT k).symm y))
    _ = ∏ i : Fin k,
        (locallyAllowedResidues
          (p := primeModulus k i) h).card :=
      by
        let s : (i : Fin k) → Finset (ZMod (primeModulus k i)) :=
          fun i ↦ locallyAllowedResidues
            (p := primeModulus k i) h
        calc
          ((Finset.univ.filter
              (fun y : (∀ i : Fin k, ZMod (primeModulus k i)) ↦
                ∀ i, y i ∈ s i)).card) =
              (Fintype.piFinset s).card := by
            apply congrArg Finset.card
            ext y
            simp [s]
          _ = ∏ i : Fin k, (s i).card := by
            exact Fintype.card_piFinset s
          _ = ∏ i : Fin k,
              (locallyAllowedResidues
                (p := primeModulus k i) h).card := by
            rfl
    _ = ∏ i : Fin k,
        (primeModulus k i - localMultiplicity (primeModulus k i) h) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact card_locallyAllowedResidues
        (p := primeModulus k i) (nthPrime_prime i).pos h

theorem primorialDensity_eq_prod_fin (k : ℕ) :
    primorialDensity k =
      ∏ i : Fin k,
        (1 - (1 : ℝ) / primeModulus k i) := by
  rw [primorialDensity_eq_prod]
  exact (Fin.prod_univ_eq_prod_range
    (fun i ↦ 1 - (1 : ℝ) / nthPrime i) k).symm

theorem totient_primeProduct_eq_prod_fin (k : ℕ) :
    (primeProduct k).totient =
      ∏ i : Fin k, (primeModulus k i - 1) := by
  rw [totient_primeProduct]
  exact (Fin.prod_univ_eq_prod_range
    (fun i ↦ nthPrime i - 1) k).symm

theorem localDensity_pow_mul_localFactor {r p : ℕ}
    (hp : p.Prime) (h : Fin r → ℕ) :
    (1 - (1 : ℝ) / p) ^ (r + 1) * localFactor p h =
      1 - (localMultiplicity p h : ℝ) / p := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (1 - (1 : ℝ) / p) ≠ 0 := by
    have hone : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact sub_ne_zero.mpr
      (ne_of_gt ((div_lt_one (by positivity)).mpr hone))
  unfold localFactor
  exact mul_div_cancel₀ _ (pow_ne_zero _ hp1)

/-- Exact conditional correlation formula.  Relative to a uniformly chosen
reduced starting residue modulo `Nₖ`, simultaneous success at `r` displayed
shifts has probability `δₖ^r` times the first-`k`-prime singular series. -/
theorem jointReduced_ratio_eq_density_mul_series {r k : ℕ}
    (h : Fin r → ℕ) :
    ((jointReducedResidues k h).card : ℝ) /
        ((primeProduct k).totient : ℝ) =
      primorialDensity k ^ r * indexedSingularSeries k h := by
  have hN0 : (primeProduct k : ℝ) ≠ 0 := by
    exact_mod_cast primeProduct_ne_zero k
  have hφ0 : ((primeProduct k).totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (primeProduct_pos k)).ne'
  have hδ0 : primorialDensity k ≠ 0 := (primorialDensity_pos k).ne'
  have hcountN :
      ((jointReducedResidues k h).card : ℝ) / (primeProduct k : ℝ) =
        primorialDensity k ^ (r + 1) * indexedSingularSeries k h := by
    rw [card_jointReducedResidues, ← prod_primeModulus]
    push_cast
    rw [← Finset.prod_div_distrib, primorialDensity_eq_prod_fin,
      indexedSingularSeries]
    have hpow :
        (∏ i : Fin k, (1 - (1 : ℝ) / primeModulus k i)) ^ (r + 1) =
          ∏ i : Fin k,
            (1 - (1 : ℝ) / primeModulus k i) ^ (r + 1) := by
      simpa only using
        (Finset.prod_pow (Finset.univ : Finset (Fin k)) (r + 1)
          (fun i ↦ 1 - (1 : ℝ) / primeModulus k i)).symm
    rw [hpow, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have hsub : localMultiplicity (primeModulus k i) h ≤
        primeModulus k i :=
      localMultiplicity_le (nthPrime_prime i).pos h
    rw [Nat.cast_sub hsub]
    calc
      ((primeModulus k i : ℝ) - localMultiplicity (primeModulus k i) h) /
          (primeModulus k i : ℝ) =
          1 - (localMultiplicity (primeModulus k i) h : ℝ) /
            primeModulus k i := by
        have hp0 : (primeModulus k i : ℝ) ≠ 0 := by
          exact_mod_cast (nthPrime_prime i).ne_zero
        field_simp
      _ = (1 - (1 : ℝ) / primeModulus k i) ^ (r + 1) *
          localFactor (primeModulus k i) h :=
        (localDensity_pow_mul_localFactor (nthPrime_prime i) h).symm
  rw [primorialDensity] at hδ0 hcountN ⊢
  calc
    ((jointReducedResidues k h).card : ℝ) /
          ((primeProduct k).totient : ℝ) =
        (((jointReducedResidues k h).card : ℝ) /
          (primeProduct k : ℝ)) /
        (((primeProduct k).totient : ℝ) /
          (primeProduct k : ℝ)) := by field_simp
    _ = ((((primeProduct k).totient : ℝ) /
          (primeProduct k : ℝ)) ^ (r + 1) *
          indexedSingularSeries k h) /
        (((primeProduct k).totient : ℝ) /
          (primeProduct k : ℝ)) := by rw [hcountN]
    _ = (((primeProduct k).totient : ℝ) /
          (primeProduct k : ℝ)) ^ r *
          indexedSingularSeries k h := by
      rw [pow_succ]
      field_simp [hδ0]

/-! ## Ordered distinct shifts -/

/-- All ordered `r`-tuples of positive shifts at most `m`. -/
def shiftBox (r m : ℕ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset fun _ : Fin r ↦ Finset.Icc 1 m

@[simp] theorem mem_shiftBox {r m : ℕ} {h : Fin r → ℕ} :
    h ∈ shiftBox r m ↔ ∀ i, 1 ≤ h i ∧ h i ≤ m := by
  classical
  simp [shiftBox]

/-- Ordered tuples of pairwise distinct positive shifts at most `m`. -/
def distinctShiftTuples (r m : ℕ) : Finset (Fin r → ℕ) :=
  (shiftBox r m).filter Function.Injective

@[simp] theorem mem_distinctShiftTuples {r m : ℕ} {h : Fin r → ℕ} :
    h ∈ distinctShiftTuples r m ↔
      (∀ i, 1 ≤ h i ∧ h i ≤ m) ∧ Function.Injective h := by
  classical
  simp [distinctShiftTuples]

/-- A tuple in the shift box, together with injectivity, is equivalently an
embedding into the finite interval of permitted shifts. -/
noncomputable def distinctShiftTupleEquivEmbedding (r m : ℕ) :
    {h : Fin r → ℕ // h ∈ distinctShiftTuples r m} ≃
      (Fin r ↪ ↥(Finset.Icc 1 m)) where
  toFun h :=
    { toFun := fun i ↦ ⟨h.1 i, Finset.mem_Icc.mpr
          ((mem_distinctShiftTuples.mp h.2).1 i)⟩
      inj' := by
        intro i j hij
        exact (mem_distinctShiftTuples.mp h.2).2
          (congrArg Subtype.val hij) }
  invFun e :=
    ⟨fun i ↦ e i, mem_distinctShiftTuples.mpr
      ⟨fun i ↦ Finset.mem_Icc.mp (e i).2, by
        intro i j hij
        exact e.injective (Subtype.ext hij)⟩⟩
  left_inv h := by
    apply Subtype.ext
    rfl
  right_inv e := by
    ext i
    rfl

theorem card_Icc_one (m : ℕ) : (Finset.Icc 1 m).card = m := by
  simp

theorem card_distinctShiftTuples (r m : ℕ) :
    (distinctShiftTuples r m).card = m.descFactorial r := by
  classical
  calc
    (distinctShiftTuples r m).card =
        Fintype.card {h : Fin r → ℕ // h ∈ distinctShiftTuples r m} := by
      exact (Fintype.card_coe _).symm
    _ = Fintype.card (Fin r ↪ ↥(Finset.Icc 1 m)) :=
      Fintype.card_congr (distinctShiftTupleEquivEmbedding r m)
    _ = m.descFactorial r := by
      rw [Fintype.card_embedding_eq, Fintype.card_fin,
        Fintype.card_coe, card_Icc_one]

theorem tendsto_card_distinctShiftTuples_div_pow (r : ℕ) :
    Tendsto
      (fun m ↦ ((distinctShiftTuples r m).card : ℝ) / (m : ℝ) ^ r)
      atTop (𝓝 1) := by
  have hpow : ∀ᶠ m : ℕ in atTop, (m ^ r : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    positivity
  have ht := (Asymptotics.isEquivalent_iff_tendsto_one hpow).mp
    (isEquivalent_descFactorial r)
  simp_rw [card_distinctShiftTuples]
  change Tendsto
    ((fun m : ℕ ↦ (m.descFactorial r : ℝ)) /
      (fun m : ℕ ↦ (m : ℝ) ^ r)) atTop (𝓝 1)
  exact ht

/-- The normalized mean of the first-`k`-prime singular series over ordered
distinct shifts in `[1,m]`. -/
noncomputable def singularSeriesMean (r k m : ℕ) : ℝ :=
  (∑ h ∈ distinctShiftTuples r m, indexedSingularSeries k h) /
    (m : ℝ) ^ r

/-! ## Segments of the singular series and periodicity -/

/-- Euler factors belonging to prime indices in the half-open interval
`[a,b)`. -/
noncomputable def singularSeriesSegment {r : ℕ} (a b : ℕ)
    (h : Fin r → ℕ) : ℝ :=
  ∏ i ∈ Finset.Ico a b, localFactor (nthPrime i) h

theorem indexedSingularSeries_eq_segment {r k : ℕ} (h : Fin r → ℕ) :
    indexedSingularSeries k h = singularSeriesSegment 0 k h := by
  unfold indexedSingularSeries singularSeriesSegment primeModulus
  rw [Nat.Ico_zero_eq_range]
  exact Fin.prod_univ_eq_prod_range
    (fun i ↦ localFactor (nthPrime i) h) k

theorem singularSeriesSegment_split {r a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (h : Fin r → ℕ) :
    singularSeriesSegment a c h =
      singularSeriesSegment a b h * singularSeriesSegment b c h := by
  unfold singularSeriesSegment
  exact Finset.prod_Ico_consecutive
    (fun i ↦ localFactor (nthPrime i) h) hab hbc |>.symm

theorem nthPrime_dvd_primeProduct {i k : ℕ} (hik : i < k) :
    nthPrime i ∣ primeProduct k := by
  unfold primeProduct
  exact Finset.dvd_prod_of_mem (fun j ↦ nthPrime j)
    (Finset.mem_range.mpr hik)

theorem localMultiplicity_eq_of_mod_eq {r p : ℕ}
    {h g : Fin r → ℕ} (hmod : ∀ i, h i % p = g i % p) :
    localMultiplicity p h = localMultiplicity p g := by
  unfold localMultiplicity shiftResidues
  congr 2
  apply Finset.image_congr
  intro i hi
  exact hmod i

theorem singularSeriesSegment_periodic {r ℓ : ℕ} :
    Wikipedia.SzemeredisTheorem.PeriodicInEachCoordinate
      (singularSeriesSegment (r := r) 0 ℓ) (primeProduct ℓ) := by
  intro h g hmod
  unfold singularSeriesSegment
  apply Finset.prod_congr rfl
  intro i hi
  have hiℓ : i < ℓ := (Finset.mem_Ico.mp hi).2
  have hpN : nthPrime i ∣ primeProduct ℓ :=
    nthPrime_dvd_primeProduct hiℓ
  have hlocal : localMultiplicity (nthPrime i) h =
      localMultiplicity (nthPrime i) g := by
    apply localMultiplicity_eq_of_mod_eq
    intro j
    calc
      h j % nthPrime i = (h j % primeProduct ℓ) % nthPrime i :=
        (Nat.mod_mod_of_dvd (h j) hpN).symm
      _ = (g j % primeProduct ℓ) % nthPrime i := by rw [hmod j]
      _ = g j % nthPrime i := Nat.mod_mod_of_dvd (g j) hpN
  unfold localFactor
  rw [hlocal]

/-! ### Exact one-prime mean -/

abbrev NonzeroZMod (p : ℕ) := {x : ZMod p // x ≠ 0}

theorem card_nonzeroZMod (p : ℕ) [NeZero p] :
    Fintype.card (NonzeroZMod p) = p - 1 := by
  rw [Fintype.card_subtype_compl (fun x : ZMod p ↦ x = 0)]
  simp

/-- A shift tuple together with an allowed starting residue at one prime. -/
abbrev LocalAvoidingData (p r : ℕ) :=
  {x : (Fin r → ZMod p) × ZMod p //
    x.2 ≠ 0 ∧ ∀ i, x.2 + x.1 i ≠ 0}

noncomputable def localAvoidingDataEquivSigma (p r : ℕ) :
    LocalAvoidingData p r ≃
      (Σ h : Fin r → ZMod p,
        {a : ZMod p // a ≠ 0 ∧ ∀ i, a + h i ≠ 0}) where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨(x.1, x.2.1), x.2.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    rfl

/-- Translation sends `(a,h₁,…,hᵣ)` to the independent nonzero coordinates
`(a,a+h₁,…,a+hᵣ)`. -/
noncomputable def localAvoidingEquiv (p r : ℕ) :
    LocalAvoidingData p r ≃ (Fin (r + 1) → NonzeroZMod p) where
  toFun x := Fin.cases ⟨x.1.2, x.2.1⟩
    (fun i ↦ ⟨x.1.2 + x.1.1 i, x.2.2 i⟩)
  invFun y :=
    ⟨(fun i ↦ y i.succ - y 0, y 0),
      ⟨(y 0).2, fun i ↦ by simpa using (y i.succ).2⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      simp
    · rfl
  right_inv y := by
    funext j
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      simp

theorem card_localAvoidingData (p r : ℕ) [NeZero p] :
    Fintype.card (LocalAvoidingData p r) = (p - 1) ^ (r + 1) := by
  calc
    Fintype.card (LocalAvoidingData p r) =
        Fintype.card (Fin (r + 1) → NonzeroZMod p) :=
      Fintype.card_congr (localAvoidingEquiv p r)
    _ = ∏ _i : Fin (r + 1), Fintype.card (NonzeroZMod p) :=
      Fintype.card_pi
    _ = (p - 1) ^ (r + 1) := by
      simp [card_nonzeroZMod]

theorem sum_allowed_local_counts (p r : ℕ) [NeZero p] :
    (∑ h : Fin r → ZMod p,
      (p - localMultiplicity p (fun i ↦ (h i).val))) =
        (p - 1) ^ (r + 1) := by
  rw [← card_localAvoidingData p r,
    Fintype.card_congr (localAvoidingDataEquivSigma p r),
    Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro h hh
  let g : Fin r → ℕ := fun i ↦ (h i).val
  have hsubtype :
      Fintype.card {a : ZMod p // a ≠ 0 ∧ ∀ i, a + h i ≠ 0} =
        (locallyAllowedResidues (p := p) g).card := by
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext a
    simpa [g] using (mem_locallyAllowedResidues_iff
      (p := p) (h := g) (a := a)).symm
  rw [hsubtype]
  exact card_locallyAllowedResidues (NeZero.pos p) g |>.symm

/-- The normalized local Euler factor has exact mean one over all shift
residues modulo its prime. -/
theorem sum_localFactor_over_zmod {r p : ℕ} [NeZero p] (hp : p.Prime) :
    (∑ h : Fin r → ZMod p,
      localFactor p (fun i ↦ (h i).val)) = (p : ℝ) ^ r := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd0 : (1 - (1 : ℝ) / p) ≠ 0 := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    exact sub_ne_zero.mpr
      (ne_of_gt ((div_lt_one (by positivity)).mpr hp1))
  have hsumNat := sum_allowed_local_counts p r
  have hsumReal :
      (∑ h : Fin r → ZMod p,
        ((p - localMultiplicity p (fun i ↦ (h i).val) : ℕ) : ℝ)) =
          ((p - 1 : ℕ) : ℝ) ^ (r + 1) := by
    exact_mod_cast hsumNat
  rw [show (∑ h : Fin r → ZMod p,
      localFactor p (fun i ↦ (h i).val)) =
      (∑ h : Fin r → ZMod p,
        (((p - localMultiplicity p (fun i ↦ (h i).val) : ℕ) : ℝ) /
          (p : ℝ) /
          (1 - (1 : ℝ) / p) ^ (r + 1))) by
    apply Finset.sum_congr rfl
    intro h hh
    unfold localFactor
    rw [Nat.cast_sub (localMultiplicity_le hp.pos _)]
    field_simp]
  rw [← Finset.sum_div, ← Finset.sum_div, hsumReal]
  rw [Nat.cast_sub hp.one_le]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpm1 : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr hp1).ne'
  have hd : 1 - (1 : ℝ) / p = ((p : ℝ) - 1) / p := by
    field_simp
  rw [hd]
  rw [div_pow]
  field_simp [hp0, hpm1]
  ring

/-! ### Exact mean over one small-prime period -/

noncomputable def primeResidueEquiv (ℓ : ℕ) :
    Fin (primeProduct ℓ) ≃
      (∀ i : Fin ℓ, ZMod (primeModulus ℓ i)) :=
  (ZMod.finEquiv (primeProduct ℓ)).toEquiv.trans
    (primeProductCRT ℓ).toEquiv

@[simp] theorem zmod_finEquiv_apply_natCast (n : ℕ) [NeZero n]
    (x : Fin n) :
    ZMod.finEquiv n x = (x.val : ZMod n) := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
      apply Fin.ext
      change x.val = ZMod.val (x.val : ZMod (n + 1))
      exact (ZMod.val_natCast_of_lt x.isLt).symm

/-- Apply CRT independently to every shift coordinate, then transpose the
two finite coordinate systems. -/
noncomputable def finiteShiftCRTEquiv (r ℓ : ℕ) :
    (Fin r → Fin (primeProduct ℓ)) ≃
      (∀ i : Fin ℓ, Fin r → ZMod (primeModulus ℓ i)) :=
  (Equiv.piCongrRight fun _ : Fin r ↦ primeResidueEquiv ℓ).trans
    (Equiv.piComm fun (_ : Fin r) (i : Fin ℓ) ↦
      ZMod (primeModulus ℓ i))

@[simp] theorem finiteShiftCRTEquiv_apply (r ℓ : ℕ)
    (x : Fin r → Fin (primeProduct ℓ)) (i : Fin ℓ) (j : Fin r) :
    finiteShiftCRTEquiv r ℓ x i j =
      ((x j : ℕ) : ZMod (primeModulus ℓ i)) := by
  simp [finiteShiftCRTEquiv, primeResidueEquiv, Function.swap]

theorem localFactor_val_eq_of_cast_eq {r p : ℕ} [NeZero p]
    (h : Fin r → ℕ) (g : Fin r → ZMod p)
    (heq : ∀ i, (h i : ZMod p) = g i) :
    localFactor p h = localFactor p (fun i ↦ (g i).val) := by
  have hmult : localMultiplicity p h =
      localMultiplicity p (fun i ↦ (g i).val) := by
    apply localMultiplicity_eq_of_mod_eq
    intro i
    have hv := congrArg ZMod.val (heq i)
    simpa [Nat.mod_eq_of_lt (ZMod.val_lt (g i))] using hv
  unfold localFactor
  rw [hmult]

/-- The small-prime singular series has exact mean one over its full CRT
period in every shift coordinate. -/
theorem boxMean_singularSeriesSegment_period (r ℓ : ℕ) :
    Wikipedia.SzemeredisTheorem.boxMean
      (fun _ : Fin r ↦ primeProduct ℓ)
      (singularSeriesSegment (r := r) 0 ℓ) = 1 := by
  let N := primeProduct ℓ
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast primeProduct_ne_zero ℓ
  have hsum :
      (∑ x : Fin r → Fin N,
        singularSeriesSegment 0 ℓ (fun j ↦ (x j : ℕ))) =
          (N : ℝ) ^ r := by
    rw [Fintype.sum_equiv (finiteShiftCRTEquiv r ℓ)
      (fun x : Fin r → Fin N ↦
        singularSeriesSegment 0 ℓ (fun j ↦ (x j : ℕ)))
      (fun y : (∀ i : Fin ℓ,
          Fin r → ZMod (primeModulus ℓ i)) ↦
        ∏ i : Fin ℓ,
          localFactor (primeModulus ℓ i)
            (fun j ↦ (y i j).val))]
    · calc
      (∑ y : (∀ i : Fin ℓ,
          Fin r → ZMod (primeModulus ℓ i)),
          ∏ i : Fin ℓ,
            localFactor (primeModulus ℓ i)
              (fun j ↦ (y i j).val)) =
          ∏ i : Fin ℓ,
            ∑ h : Fin r → ZMod (primeModulus ℓ i),
              localFactor (primeModulus ℓ i)
                (fun j ↦ (h j).val) := by
        exact (Fintype.prod_sum (fun i
          (h : Fin r → ZMod (primeModulus ℓ i)) ↦
            localFactor (primeModulus ℓ i)
              (fun j ↦ (h j).val))).symm
      _ = (N : ℝ) ^ r := by
        have hlocal (i : Fin ℓ) :
          (∑ h : Fin r → ZMod (primeModulus ℓ i),
            localFactor (primeModulus ℓ i)
              (fun j ↦ (h j).val)) =
            (primeModulus ℓ i : ℝ) ^ r :=
          sum_localFactor_over_zmod
            (p := primeModulus ℓ i) (nthPrime_prime i)
        simp_rw [hlocal]
        calc
          (∏ i : Fin ℓ, (primeModulus ℓ i : ℝ) ^ r) =
              (∏ i : Fin ℓ, (primeModulus ℓ i : ℝ)) ^ r := by
            simpa only using
              (Finset.prod_pow (Finset.univ : Finset (Fin ℓ)) r
                (fun i ↦ (primeModulus ℓ i : ℝ)))
          _ = (N : ℝ) ^ r := by
            congr 1
            exact_mod_cast prod_primeModulus ℓ
    · intro x
      unfold singularSeriesSegment
      rw [Nat.Ico_zero_eq_range]
      rw [← Fin.prod_univ_eq_prod_range]
      apply Finset.prod_congr rfl
      intro i hi
      letI : NeZero (nthPrime i) := ⟨(nthPrime_prime i).ne_zero⟩
      apply localFactor_val_eq_of_cast_eq
      intro j
      exact (finiteShiftCRTEquiv_apply r ℓ x i j).symm
  unfold Wikipedia.SzemeredisTheorem.boxMean
  change
    Wikipedia.SzemeredisTheorem.boxSum (fun _ : Fin r ↦ N)
        (singularSeriesSegment 0 ℓ) /
      (∏ _ : Fin r, (N : ℝ)) = 1
  rw [Wikipedia.SzemeredisTheorem.boxSum]
  rw [hsum]
  rw [show (∏ _ : Fin r, (N : ℝ)) = (N : ℝ) ^ r by simp]
  exact div_self (pow_ne_zero r hN0)

/-- Add one cyclically in `Fin D`, expressed through `ZMod D`. -/
noncomputable def finAddOneEquiv (D : ℕ) [NeZero D] : Fin D ≃ Fin D :=
  (ZMod.finEquiv D).toEquiv |>.trans (Equiv.addRight 1) |>.trans
    (ZMod.finEquiv D).symm.toEquiv

@[simp] theorem zmod_finEquiv_symm_val_cast (D : ℕ) [NeZero D]
    (z : ZMod D) :
    (((ZMod.finEquiv D).symm z).val : ZMod D) = z := by
  rw [← zmod_finEquiv_apply_natCast D ((ZMod.finEquiv D).symm z)]
  exact (ZMod.finEquiv D).apply_symm_apply z

@[simp] theorem finAddOneEquiv_cast (D : ℕ) [NeZero D] (x : Fin D) :
    ((finAddOneEquiv D x).val : ZMod D) = (x.val : ZMod D) + 1 := by
  unfold finAddOneEquiv
  change
    (((ZMod.finEquiv D).symm (ZMod.finEquiv D x + 1)).val : ZMod D) =
      (x.val : ZMod D) + 1
  rw [zmod_finEquiv_symm_val_cast,
    zmod_finEquiv_apply_natCast]

noncomputable def finiteShiftAddOneEquiv (r D : ℕ) [NeZero D] :
    (Fin r → Fin D) ≃ (Fin r → Fin D) :=
  Equiv.piCongrRight fun _ : Fin r ↦ finAddOneEquiv D

/-- The small-prime product evaluated at positive rather than zero-based
shifts. -/
noncomputable def positiveShiftSeries (r ℓ : ℕ) (h : Fin r → ℕ) : ℝ :=
  singularSeriesSegment 0 ℓ (fun i ↦ h i + 1)

theorem positiveShiftSeries_periodic {r ℓ : ℕ} :
    Wikipedia.SzemeredisTheorem.PeriodicInEachCoordinate
      (positiveShiftSeries r ℓ) (primeProduct ℓ) := by
  intro h g hmod
  apply singularSeriesSegment_periodic
  intro i
  simpa [Nat.add_mod, hmod i]

theorem boxMean_positiveShiftSeries_period (r ℓ : ℕ) :
    Wikipedia.SzemeredisTheorem.boxMean
      (fun _ : Fin r ↦ primeProduct ℓ)
      (positiveShiftSeries r ℓ) = 1 := by
  let N := primeProduct ℓ
  have hsum :
      Wikipedia.SzemeredisTheorem.boxSum (fun _ : Fin r ↦ N)
          (positiveShiftSeries r ℓ) =
        Wikipedia.SzemeredisTheorem.boxSum (fun _ : Fin r ↦ N)
          (singularSeriesSegment 0 ℓ) := by
    unfold Wikipedia.SzemeredisTheorem.boxSum
    apply Fintype.sum_equiv (finiteShiftAddOneEquiv r N)
    intro x
    apply singularSeriesSegment_periodic
    intro i
    change ((x i).val + 1) % N =
      (finAddOneEquiv N (x i)).val % N
    have hcast := finAddOneEquiv_cast N (x i)
    have hval := congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt ((finAddOneEquiv N (x i)).isLt),
      ZMod.val_add, ZMod.val_natCast_of_lt (x i).isLt] at hval
    have hone : ZMod.val (1 : ZMod N) = 1 % N := by
      simpa only [Nat.cast_one] using ZMod.val_natCast N 1
    rw [hone] at hval
    have hval' : (finAddOneEquiv N (x i)).val =
        ((x i).val + 1) % N := by
      simpa [Nat.add_mod] using hval
    rw [Nat.mod_eq_of_lt ((finAddOneEquiv N (x i)).isLt)]
    exact hval'.symm
  unfold Wikipedia.SzemeredisTheorem.boxMean at ⊢
  rw [hsum]
  exact boxMean_singularSeriesSegment_period r ℓ

/-! ### Long boxes for a fixed periodic product -/

theorem tendsto_mod_div_natCast_zero {D : ℕ} (hD : 0 < D) :
    Tendsto (fun m : ℕ ↦ ((m % D : ℕ) : ℝ) / (m : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun m : ℕ ↦ (D : ℝ) / (m : ℝ))
  · filter_upwards [] with m
    positivity
  · filter_upwards [eventually_ge_atTop 1] with m hm
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast (Nat.mod_lt m hD).le) (by positivity)
  · exact tendsto_const_div_atTop_nhds_zero_nat (D : ℝ)

theorem tendsto_trimToMultiple_div_natCast_one {D : ℕ} (hD : 0 < D) :
    Tendsto
      (fun m : ℕ ↦
        (Wikipedia.SzemeredisTheorem.trimToMultiple D m : ℝ) / (m : ℝ))
      atTop (𝓝 1) := by
  have hrem := tendsto_mod_div_natCast_zero hD
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have htarget := hone.sub hrem
  have heq :
      (fun m : ℕ ↦ (1 : ℝ) - ((m % D : ℕ) : ℝ) / (m : ℝ)) =ᶠ[atTop]
        (fun m : ℕ ↦
          (Wikipedia.SzemeredisTheorem.trimToMultiple D m : ℝ) / (m : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hmodle : m % D ≤ m := Nat.mod_le _ _
    rw [show Wikipedia.SzemeredisTheorem.trimToMultiple D m =
        m - m % D by
      have hadd := Wikipedia.SzemeredisTheorem.trimToMultiple_add_mod D m
      omega]
    rw [Nat.cast_sub hmodle]
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    field_simp
  simpa using htarget.congr' heq

theorem tendsto_boxBoundaryRatio_zero (r : ℕ) {D : ℕ} (hD : 0 < D) :
    Tendsto
      (fun m : ℕ ↦
        (((m ^ r -
          Wikipedia.SzemeredisTheorem.trimToMultiple D m ^ r : ℕ) : ℝ) /
          (m : ℝ) ^ r))
      atTop (𝓝 0) := by
  have htrim := (tendsto_trimToMultiple_div_natCast_one (D := D) hD).pow r
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have htarget := hone.sub htrim
  have heq :
      (fun m : ℕ ↦ (1 : ℝ) -
        ((Wikipedia.SzemeredisTheorem.trimToMultiple D m : ℝ) / (m : ℝ)) ^ r)
        =ᶠ[atTop]
      (fun m : ℕ ↦
        (((m ^ r -
          Wikipedia.SzemeredisTheorem.trimToMultiple D m ^ r : ℕ) : ℝ) /
          (m : ℝ) ^ r)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hle : Wikipedia.SzemeredisTheorem.trimToMultiple D m ^ r ≤ m ^ r :=
      Nat.pow_le_pow_left
        (Wikipedia.SzemeredisTheorem.trimToMultiple_le D m) r
    rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow]
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    rw [sub_div, div_self (pow_ne_zero r hm0), div_pow]
  simpa using htarget.congr' heq

/-- A convenient finite uniform bound for a periodic function: the sum of
absolute values over one complete residue box. -/
noncomputable def periodicBoxBound {r : ℕ} (D : ℕ)
    (F : (Fin r → ℕ) → ℝ) : ℝ :=
  ∑ x ∈ Wikipedia.SzemeredisTheorem.natBox
      (fun _ : Fin r ↦ D), |F x|

theorem abs_le_periodicBoxBound {r D : ℕ} (hD : 0 < D)
    {F : (Fin r → ℕ) → ℝ}
    (hF : Wikipedia.SzemeredisTheorem.PeriodicInEachCoordinate F D)
    (x : Fin r → ℕ) :
    |F x| ≤ periodicBoxBound D F := by
  let y : Fin r → ℕ := fun i ↦ x i % D
  have hy : y ∈ Wikipedia.SzemeredisTheorem.natBox
      (fun _ : Fin r ↦ D) := by
    rw [Wikipedia.SzemeredisTheorem.mem_natBox]
    intro i
    exact Nat.mod_lt _ hD
  have hxy : F x = F y := hF x y (fun i ↦ by simp [y])
  rw [hxy]
  unfold periodicBoxBound
  exact Finset.single_le_sum
    (fun z hz ↦ abs_nonneg (F z)) hy

/-- A bounded periodic function whose exact mean on one positive period is
one has mean tending to one on growing cubical boxes. -/
theorem tendsto_boxMean_periodic_one {r D : ℕ} (hD : 0 < D)
    (F : (Fin r → ℕ) → ℝ)
    (hperiodic :
      Wikipedia.SzemeredisTheorem.PeriodicInEachCoordinate F D)
    (hone : Wikipedia.SzemeredisTheorem.boxMean
      (fun _ : Fin r ↦ D) F = 1) :
    Tendsto
      (fun m ↦ Wikipedia.SzemeredisTheorem.boxMean
        (fun _ : Fin r ↦ m) F)
      atTop (𝓝 1) := by
  let B := periodicBoxBound D F
  let S : ℕ → ℝ := fun m ↦
    Wikipedia.SzemeredisTheorem.boxSum (fun _ : Fin r ↦ m) F
  let T : ℕ → ℝ := fun m ↦
    (Wikipedia.SzemeredisTheorem.trimToMultiple D m : ℝ) ^ r
  have hperiodSum :
      Wikipedia.SzemeredisTheorem.boxSum (fun _ : Fin r ↦ D) F =
        (D : ℝ) ^ r := by
    unfold Wikipedia.SzemeredisTheorem.boxMean at hone
    rw [show (∏ _ : Fin r, (D : ℝ)) = (D : ℝ) ^ r by simp] at hone
    exact (div_eq_one_iff_eq (pow_ne_zero r (by positivity))).mp hone
  have herror (m : ℕ) :
      |S m - T m| ≤
        (((m ^ r -
          Wikipedia.SzemeredisTheorem.trimToMultiple D m ^ r : ℕ) : ℝ) * B) := by
    have hb := Wikipedia.SzemeredisTheorem.abs_boxSum_sub_periodic_model_le
      D (fun _ : Fin r ↦ m) F B hperiodic
      (fun x hx ↦ abs_le_periodicBoxBound hD hperiodic x)
    simp only [S, T, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hb ⊢
    rw [hperiodSum] at hb
    have hq :
        (((m / D : ℕ) : ℝ) ^ r) * (D : ℝ) ^ r =
          (Wikipedia.SzemeredisTheorem.trimToMultiple D m : ℝ) ^ r := by
      rw [← mul_pow]
      norm_cast
    simpa [nsmul_eq_mul, hq] using hb
  have hnormalizedError :
      Tendsto (fun m ↦ (S m - T m) / (m : ℝ) ^ r)
        atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hboundT := (tendsto_boxBoundaryRatio_zero r hD).const_mul B
    have habsT : Tendsto
        (fun m ↦
          (((m ^ r -
            Wikipedia.SzemeredisTheorem.trimToMultiple D m ^ r : ℕ) : ℝ) /
            (m : ℝ) ^ r) * B)
        atTop (𝓝 0) := by
      simpa [mul_comm] using hboundT
    have hevent := (tendsto_order.1 habsT).2 ε hε
    filter_upwards [hevent, eventually_ge_atTop 1] with m hm hsmall
    rw [dist_zero_right, Real.norm_eq_abs, abs_div]
    have hden : 0 < |(m : ℝ) ^ r| := abs_pos.mpr (pow_ne_zero r (by positivity))
    calc
      |S m - T m| / |(m : ℝ) ^ r| ≤
          (((m ^ r -
            Wikipedia.SzemeredisTheorem.trimToMultiple D m ^ r : ℕ) : ℝ) * B) /
            |(m : ℝ) ^ r| :=
        div_le_div_of_nonneg_right (herror m) hden.le
      _ = (((m ^ r -
            Wikipedia.SzemeredisTheorem.trimToMultiple D m ^ r : ℕ) : ℝ) /
            (m : ℝ) ^ r) * B := by
        rw [abs_of_pos (pow_pos (by positivity) r)]
        ring
      _ < ε := hm
  have hnormalizedTrim :
      Tendsto (fun m ↦ T m / (m : ℝ) ^ r) atTop (𝓝 1) := by
    simpa [T, div_pow] using
      (tendsto_trimToMultiple_div_natCast_one (D := D) hD).pow r
  have hsumNorm : Tendsto (fun m ↦ S m / (m : ℝ) ^ r)
      atTop (𝓝 1) := by
    convert hnormalizedError.add hnormalizedTrim using 1
    · funext m
      ring
    · norm_num
  unfold Wikipedia.SzemeredisTheorem.boxMean
  simpa [S] using hsumNorm

/-! ### The fixed small-prime mean on distinct positive shifts -/

noncomputable def shiftBoxEquivFiniteBox (r m : ℕ) :
    ↥(shiftBox r m) ≃ (Fin r → Fin m) where
  toFun h i :=
    ⟨h.1 i - 1, by
      have hi := (mem_shiftBox.mp h.2 i)
      omega⟩
  invFun x :=
    ⟨fun i ↦ (x i).val + 1, mem_shiftBox.mpr (fun i ↦ by
      constructor
      · omega
      · exact (x i).isLt)⟩
  left_inv h := by
    apply Subtype.ext
    funext i
    have hi := (mem_shiftBox.mp h.2 i).1
    change h.1 i - 1 + 1 = h.1 i
    exact Nat.sub_add_cancel hi
  right_inv x := by
    funext i
    apply Fin.ext
    simp

theorem sum_shiftBox_singularSeriesSegment_eq_boxSum
    (r ℓ m : ℕ) :
    (∑ h ∈ shiftBox r m, singularSeriesSegment 0 ℓ h) =
      Wikipedia.SzemeredisTheorem.boxSum (fun _ : Fin r ↦ m)
        (positiveShiftSeries r ℓ) := by
  rw [← Finset.sum_coe_sort]
  unfold Wikipedia.SzemeredisTheorem.boxSum
  apply Fintype.sum_equiv (shiftBoxEquivFiniteBox r m)
  intro h
  unfold positiveShiftSeries
  congr 1
  funext i
  have hi := (mem_shiftBox.mp h.2 i).1
  exact (Nat.sub_add_cancel hi).symm

theorem card_shiftBox (r m : ℕ) : (shiftBox r m).card = m ^ r := by
  classical
  unfold shiftBox
  rw [Fintype.card_piFinset]
  simp [card_Icc_one]

theorem singularSeriesSegment_nonneg {r a b : ℕ}
    (h : Fin r → ℕ) : 0 ≤ singularSeriesSegment a b h := by
  unfold singularSeriesSegment
  exact Finset.prod_nonneg fun i hi ↦
    localFactor_nonneg (nthPrime_prime i) h

theorem tendsto_smallSeriesMean_all (r ℓ : ℕ) :
    Tendsto
      (fun m ↦ (∑ h ∈ shiftBox r m,
        singularSeriesSegment 0 ℓ h) / (m : ℝ) ^ r)
      atTop (𝓝 1) := by
  have hmean := tendsto_boxMean_periodic_one
    (r := r) (D := primeProduct ℓ) (primeProduct_pos ℓ)
    (positiveShiftSeries r ℓ) positiveShiftSeries_periodic
    (boxMean_positiveShiftSeries_period r ℓ)
  unfold Wikipedia.SzemeredisTheorem.boxMean at hmean
  simpa [sum_shiftBox_singularSeriesSegment_eq_boxSum] using hmean

theorem tendsto_repeatedShiftRatio_zero (r : ℕ) :
    Tendsto
      (fun m ↦
        (((shiftBox r m \ distinctShiftTuples r m).card : ℝ) /
          (m : ℝ) ^ r))
      atTop (𝓝 0) := by
  have hsub : ∀ m, distinctShiftTuples r m ⊆ shiftBox r m := by
    intro m h hh
    exact (Finset.mem_filter.mp hh).1
  have hcard (m : ℕ) :
      (shiftBox r m \ distinctShiftTuples r m).card =
        m ^ r - m.descFactorial r := by
    rw [Finset.card_sdiff_of_subset (hsub m), card_shiftBox,
      card_distinctShiftTuples]
  have hratio := tendsto_card_distinctShiftTuples_div_pow r
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hdiff := hone.sub hratio
  have heq :
      (fun m : ℕ ↦ (1 : ℝ) -
        ((distinctShiftTuples r m).card : ℝ) / (m : ℝ) ^ r) =ᶠ[atTop]
      (fun m ↦
        (((shiftBox r m \ distinctShiftTuples r m).card : ℝ) /
          (m : ℝ) ^ r)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    rw [hcard]
    have hle := Nat.descFactorial_le_pow m r
    rw [Nat.cast_sub hle, Nat.cast_pow]
    have hm0 : (m : ℝ) ^ r ≠ 0 := pow_ne_zero r (by positivity)
    rw [sub_div, div_self hm0, card_distinctShiftTuples]
  simpa using hdiff.congr' heq

theorem tendsto_smallSeriesMean_distinct (r ℓ : ℕ) :
    Tendsto
      (fun m ↦ (∑ h ∈ distinctShiftTuples r m,
        singularSeriesSegment 0 ℓ h) / (m : ℝ) ^ r)
      atTop (𝓝 1) := by
  let B := periodicBoxBound (primeProduct ℓ) (positiveShiftSeries r ℓ)
  have hsub : ∀ m, distinctShiftTuples r m ⊆ shiftBox r m := by
    intro m h hh
    exact (Finset.mem_filter.mp hh).1
  have hbound {m : ℕ} {h : Fin r → ℕ} (hh : h ∈ shiftBox r m) :
      singularSeriesSegment 0 ℓ h ≤ B := by
    let x : Fin r → ℕ := fun i ↦ h i - 1
    have hx : ∀ i, x i + 1 = h i := by
      intro i
      have hi := (mem_shiftBox.mp hh i).1
      simp [x, Nat.sub_add_cancel hi]
    have habs := abs_le_periodicBoxBound (primeProduct_pos ℓ)
      (positiveShiftSeries_periodic (r := r) (ℓ := ℓ)) x
    have hnonneg := singularSeriesSegment_nonneg
      (a := 0) (b := ℓ) h
    rw [abs_of_nonneg] at habs
    · simpa [positiveShiftSeries, hx] using habs
    · simpa [positiveShiftSeries, hx] using hnonneg
  have herror (m : ℕ) :
      0 ≤
        ((∑ h ∈ shiftBox r m, singularSeriesSegment 0 ℓ h) -
          ∑ h ∈ distinctShiftTuples r m,
            singularSeriesSegment 0 ℓ h) ∧
      ((∑ h ∈ shiftBox r m, singularSeriesSegment 0 ℓ h) -
          ∑ h ∈ distinctShiftTuples r m,
            singularSeriesSegment 0 ℓ h) ≤
        ((shiftBox r m \ distinctShiftTuples r m).card : ℝ) * B := by
    have hsplit :
        (∑ h ∈ shiftBox r m, singularSeriesSegment 0 ℓ h) -
            ∑ h ∈ distinctShiftTuples r m,
              singularSeriesSegment 0 ℓ h =
          ∑ h ∈ shiftBox r m \ distinctShiftTuples r m,
            singularSeriesSegment 0 ℓ h := by
      rw [← Finset.sum_sdiff (hsub m)]
      ring
    rw [hsplit]
    constructor
    · exact Finset.sum_nonneg fun h hh ↦
        singularSeriesSegment_nonneg h
    · calc
        (∑ h ∈ shiftBox r m \ distinctShiftTuples r m,
            singularSeriesSegment 0 ℓ h) ≤
            ∑ _h ∈ shiftBox r m \ distinctShiftTuples r m, B := by
          apply Finset.sum_le_sum
          intro h hh
          exact hbound (Finset.sdiff_subset hh)
        _ = ((shiftBox r m \ distinctShiftTuples r m).card : ℝ) * B := by
          simp [nsmul_eq_mul]
  have hvanish :
      Tendsto
        (fun m ↦
          ((∑ h ∈ shiftBox r m, singularSeriesSegment 0 ℓ h) -
            ∑ h ∈ distinctShiftTuples r m,
              singularSeriesSegment 0 ℓ h) / (m : ℝ) ^ r)
        atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun m ↦
      (((shiftBox r m \ distinctShiftTuples r m).card : ℝ) /
        (m : ℝ) ^ r) * B)
    · filter_upwards [] with m
      exact div_nonneg (herror m).1 (by positivity)
    · filter_upwards [eventually_ge_atTop 1] with m hm
      calc
        ((∑ h ∈ shiftBox r m, singularSeriesSegment 0 ℓ h) -
            ∑ h ∈ distinctShiftTuples r m,
              singularSeriesSegment 0 ℓ h) / (m : ℝ) ^ r ≤
            (((shiftBox r m \ distinctShiftTuples r m).card : ℝ) * B) /
              (m : ℝ) ^ r :=
          div_le_div_of_nonneg_right (herror m).2 (by positivity)
        _ = (((shiftBox r m \ distinctShiftTuples r m).card : ℝ) /
              (m : ℝ) ^ r) * B := by ring
    · simpa [mul_comm] using
        (tendsto_repeatedShiftRatio_zero r).const_mul B
  have hall := tendsto_smallSeriesMean_all r ℓ
  convert hall.sub hvanish using 1
  · funext m
    ring
  · norm_num

/-! ## Uniform control of the large-prime tail -/

/-- The local factor when all `r+1` augmented shifts are distinct modulo
`p`. -/
noncomputable def genericLocalFactor (r p : ℕ) : ℝ :=
  (1 - ((r + 1 : ℕ) : ℝ) / p) /
    (1 - (1 : ℝ) / p) ^ (r + 1)

/-- The excess caused by collisions, relative to the generic local factor. -/
noncomputable def collisionMultiplier {r : ℕ} (p : ℕ)
    (h : Fin r → ℕ) : ℝ :=
  ((p : ℝ) - localMultiplicity p h) /
    ((p : ℝ) - (r + 1 : ℕ))

theorem pow_one_sub_linear_remainder (n : ℕ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ (1 - x) ^ n - (1 - (n : ℝ) * x) ∧
      (1 - x) ^ n - (1 - (n : ℝ) * x) ≤
        (n : ℝ) ^ 2 * x ^ 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rcases ih with ⟨ih0, ih1⟩
      have hbase0 : 0 ≤ 1 - x := sub_nonneg.mpr hx1
      have hbase1 : 1 - x ≤ 1 := by linarith
      have hrec :
          (1 - x) ^ (n + 1) - (1 - ((n + 1 : ℕ) : ℝ) * x) =
            (1 - x) * ((1 - x) ^ n - (1 - (n : ℝ) * x)) +
              (n : ℝ) * x ^ 2 := by
        rw [pow_succ]
        push_cast
        ring
      rw [hrec]
      constructor
      · positivity
      · have hmul :
            (1 - x) * ((1 - x) ^ n - (1 - (n : ℝ) * x)) ≤
              (n : ℝ) ^ 2 * x ^ 2 := by
          calc
            (1 - x) * ((1 - x) ^ n - (1 - (n : ℝ) * x)) ≤
                1 * ((1 - x) ^ n - (1 - (n : ℝ) * x)) := by
              gcongr
            _ ≤ (n : ℝ) ^ 2 * x ^ 2 := by simpa using ih1
        calc
          (1 - x) * ((1 - x) ^ n - (1 - (n : ℝ) * x)) +
              (n : ℝ) * x ^ 2 ≤
              (n : ℝ) ^ 2 * x ^ 2 + (n : ℝ) * x ^ 2 := by
            gcongr
          _ ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * x ^ 2 := by
            push_cast
            nlinarith [sq_nonneg (n : ℝ), sq_nonneg x]

theorem genericLocalFactor_bounds {r p : ℕ}
    (hp : 2 * (r + 1) ≤ p) :
    0 ≤ genericLocalFactor r p ∧ genericLocalFactor r p ≤ 1 ∧
      1 - genericLocalFactor r p ≤
        ((r + 1 : ℕ) : ℝ) ^ 2 * 2 ^ (r + 1) / (p : ℝ) ^ 2 := by
  let n := r + 1
  let x : ℝ := 1 / (p : ℝ)
  have hp0n : 0 < p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp0n
  have hnpos : 0 < n := by omega
  have hnp : n ≤ p := by omega
  have hx0 : 0 ≤ x := by positivity
  have hxhalf : x ≤ (1 : ℝ) / 2 := by
    change 1 / (p : ℝ) ≤ 1 / 2
    exact (one_div_le_one_div hp0 (by norm_num : (0 : ℝ) < 2)).2
      (by exact_mod_cast (show 2 ≤ p by omega))
  have hx1 : x ≤ 1 := hxhalf.trans (by norm_num)
  have hrem := pow_one_sub_linear_remainder n hx0 hx1
  have hnum0 : 0 ≤ 1 - (n : ℝ) * x := by
    rw [sub_nonneg]
    change (n : ℝ) * (1 / (p : ℝ)) ≤ 1
    rw [mul_one_div, div_le_one hp0]
    exact_mod_cast hnp
  have hdenpos : 0 < (1 - x) ^ n := by
    have : 0 < 1 - x := sub_pos.mpr (hxhalf.trans_lt (by norm_num))
    positivity
  have hdenlower : (1 / 2 : ℝ) ^ n ≤ (1 - x) ^ n := by
    gcongr
    linarith
  have hdenInv : ((1 - x) ^ n)⁻¹ ≤ (2 : ℝ) ^ n := by
    have hhalfpos : 0 < (1 / 2 : ℝ) ^ n := by positivity
    have hinv := one_div_le_one_div_of_le hhalfpos hdenlower
    calc
      ((1 - x) ^ n)⁻¹ ≤ 1 / (1 / 2 : ℝ) ^ n := by
        simpa [one_div] using hinv
      _ = (2 : ℝ) ^ n := by
        rw [div_pow]
        norm_num
  have hnx : (n : ℝ) * x = (n : ℝ) / (p : ℝ) := by
    simp [x, div_eq_mul_inv]
  unfold genericLocalFactor
  rw [← hnx]
  change
    0 ≤ (1 - (n : ℝ) * x) / (1 - x) ^ n ∧
      (1 - (n : ℝ) * x) / (1 - x) ^ n ≤ 1 ∧
      1 - (1 - (n : ℝ) * x) / (1 - x) ^ n ≤
        (n : ℝ) ^ 2 * 2 ^ n / (p : ℝ) ^ 2
  constructor
  · exact div_nonneg hnum0 hdenpos.le
  constructor
  · rw [div_le_one hdenpos]
    linarith [hrem.1]
  · have hid :
        1 - (1 - (n : ℝ) * x) / (1 - x) ^ n =
          ((1 - x) ^ n - (1 - (n : ℝ) * x)) *
            ((1 - x) ^ n)⁻¹ := by
        field_simp
    rw [hid]
    calc
      ((1 - x) ^ n - (1 - (n : ℝ) * x)) *
            ((1 - x) ^ n)⁻¹ ≤
          ((n : ℝ) ^ 2 * x ^ 2) * ((1 - x) ^ n)⁻¹ := by
        exact mul_le_mul_of_nonneg_right hrem.2
          (inv_nonneg.mpr hdenpos.le)
      _ ≤ ((n : ℝ) ^ 2 * x ^ 2) * 2 ^ n := by
        exact mul_le_mul_of_nonneg_left hdenInv (by positivity)
      _ = (n : ℝ) ^ 2 * 2 ^ n / (p : ℝ) ^ 2 := by
        simp [x, div_pow]
        ring

/-- The elementary lower bound for the zero-indexed prime sequence. -/
theorem add_two_le_nthPrime (i : ℕ) : i + 2 ≤ nthPrime i := by
  induction i with
  | zero => exact nthPrime_two_le 0
  | succ i ih =>
      exact Nat.succ_le_of_lt
        (ih.trans_lt (nthPrime_strictMono (Nat.lt_succ_self i)))

/-- A summable numerical majorant for all large-prime errors. -/
noncomputable def reciprocalSquareTail (ℓ : ℕ) : ℝ :=
  ∑' i : ℕ, if ℓ ≤ i then (1 : ℝ) / (i + 2) ^ 2 else 0

theorem reciprocalSquareTail_nonneg (ℓ : ℕ) :
    0 ≤ reciprocalSquareTail ℓ := by
  unfold reciprocalSquareTail
  exact tsum_nonneg fun i ↦ by split_ifs <;> positivity

theorem tendsto_reciprocalSquareTail_zero :
    Tendsto reciprocalSquareTail atTop (𝓝 0) := by
  have hsummable : Summable (fun i : ℕ ↦ (1 : ℝ) / (i + 2) ^ 2) := by
    simpa [one_div] using
      (summable_nat_add_iff 2).2
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  have hpoint (i : ℕ) :
      Tendsto (fun ℓ : ℕ ↦ if ℓ ≤ i then (1 : ℝ) / (i + 2) ^ 2 else 0)
        atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop i] with ℓ hℓ
    rw [if_neg (not_le.mpr hℓ)]
  have hbound : ∀ᶠ ℓ : ℕ in atTop, ∀ i,
      ‖(if ℓ ≤ i then (1 : ℝ) / (i + 2) ^ 2 else 0)‖ ≤
        (1 : ℝ) / (i + 2) ^ 2 := by
    filter_upwards [] with ℓ i
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    · simp only [norm_zero]
      positivity
  have ht := tendsto_tsum_of_dominated_convergence hsummable hpoint hbound
  change Tendsto
    (fun ℓ : ℕ ↦ ∑' i : ℕ,
      if ℓ ≤ i then (1 : ℝ) / (i + 2) ^ 2 else 0) atTop (𝓝 0)
  simpa only [tsum_zero] using ht

/-- If every factor lies in `[0,1]`, the error of their product is at most
the sum of their individual errors. -/
theorem one_sub_prod_le_sum_one_sub {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ)
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∏ i ∈ s, f i ≤ ∑ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hfa0 := hf0 a (Finset.mem_insert_self a s)
      have hfa1 := hf1 a (Finset.mem_insert_self a s)
      have hprod0 : 0 ≤ ∏ i ∈ s, f i :=
        Finset.prod_nonneg fun i hi ↦ hf0 i (Finset.mem_insert_of_mem hi)
      have hprod1 : ∏ i ∈ s, f i ≤ 1 := by
        simpa using Finset.prod_le_one (fun i hi ↦ hf0 i
          (Finset.mem_insert_of_mem hi)) (fun i hi ↦ hf1 i
          (Finset.mem_insert_of_mem hi))
      have hih := ih
        (fun i hi ↦ hf0 i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hf1 i (Finset.mem_insert_of_mem hi))
      nlinarith

/-- Product of the collision-free local factors on a prime-index segment. -/
noncomputable def genericSeriesSegment (r a b : ℕ) : ℝ :=
  ∏ i ∈ Finset.Ico a b, genericLocalFactor r (nthPrime i)

theorem genericSeriesSegment_bounds {r a b : ℕ}
    (ha : 2 * (r + 1) ≤ nthPrime a) :
    0 ≤ genericSeriesSegment r a b ∧
      genericSeriesSegment r a b ≤ 1 := by
  unfold genericSeriesSegment
  constructor
  · apply Finset.prod_nonneg
    intro i hi
    exact (genericLocalFactor_bounds
      (ha.trans (nthPrime_strictMono.monotone
        (Finset.mem_Ico.mp hi).1))).1
  · apply Finset.prod_le_one
    · intro i hi
      exact (genericLocalFactor_bounds
        (ha.trans (nthPrime_strictMono.monotone
          (Finset.mem_Ico.mp hi).1))).1
    · intro i hi
      exact (genericLocalFactor_bounds
        (ha.trans (nthPrime_strictMono.monotone
          (Finset.mem_Ico.mp hi).1))).2.1

theorem one_sub_genericSeriesSegment_le_tail {r a b : ℕ}
    (ha : 2 * (r + 1) ≤ nthPrime a) :
    1 - genericSeriesSegment r a b ≤
      ((r + 1 : ℕ) : ℝ) ^ 2 * 2 ^ (r + 1) *
        reciprocalSquareTail a := by
  let C : ℝ := ((r + 1 : ℕ) : ℝ) ^ 2 * 2 ^ (r + 1)
  have hfactor (i : ℕ) (hi : i ∈ Finset.Ico a b) :
      0 ≤ genericLocalFactor r (nthPrime i) ∧
      genericLocalFactor r (nthPrime i) ≤ 1 ∧
      1 - genericLocalFactor r (nthPrime i) ≤
        C * ((1 : ℝ) / (i + 2) ^ 2) := by
    have hai : a ≤ i := (Finset.mem_Ico.mp hi).1
    have hp := ha.trans (nthPrime_strictMono.monotone hai)
    have hb := genericLocalFactor_bounds hp
    refine ⟨hb.1, hb.2.1, hb.2.2.trans ?_⟩
    have hpos : (0 : ℝ) < (i + 2) := by positivity
    have hle : (i + 2 : ℝ) ≤ nthPrime i := by
      exact_mod_cast add_two_le_nthPrime i
    change C / (nthPrime i : ℝ) ^ 2 ≤ C * (1 / (i + 2 : ℝ) ^ 2)
    have hC : 0 ≤ C := by positivity
    have hsquare : (i + 2 : ℝ) ^ 2 ≤ (nthPrime i : ℝ) ^ 2 := by
      exact (sq_le_sq₀ (show (0 : ℝ) ≤ i + 2 by positivity)
        (show (0 : ℝ) ≤ nthPrime i by positivity)).2 hle
    calc
      C / (nthPrime i : ℝ) ^ 2 ≤ C / (i + 2 : ℝ) ^ 2 := by
        have hp0 : (0 : ℝ) < nthPrime i := by
          exact_mod_cast (nthPrime_prime i).pos
        rw [div_le_div_iff₀ (sq_pos_of_pos hp0) (sq_pos_of_pos hpos)]
        exact mul_le_mul_of_nonneg_left hsquare hC
      _ = C * (1 / (i + 2 : ℝ) ^ 2) := by ring
  calc
    1 - genericSeriesSegment r a b ≤
        ∑ i ∈ Finset.Ico a b,
          (1 - genericLocalFactor r (nthPrime i)) := by
      exact one_sub_prod_le_sum_one_sub _ _
        (fun i hi ↦ (hfactor i hi).1)
        (fun i hi ↦ (hfactor i hi).2.1)
    _ ≤ ∑ i ∈ Finset.Ico a b, C * ((1 : ℝ) / (i + 2) ^ 2) := by
      exact Finset.sum_le_sum fun i hi ↦ (hfactor i hi).2.2
    _ ≤ ∑' i : ℕ, if a ≤ i then C * ((1 : ℝ) / (i + 2) ^ 2) else 0 := by
      have hs : Summable (fun i : ℕ ↦
          if a ≤ i then C * ((1 : ℝ) / (i + 2) ^ 2) else 0) := by
        have hsumC : Summable
            (fun i : ℕ ↦ C * ((1 : ℝ) / (i + 2) ^ 2)) :=
          by simpa using ((summable_nat_add_iff 2).2
            (Real.summable_one_div_nat_pow.mpr
              (by norm_num : 1 < 2))).mul_left C
        refine Summable.of_nonneg_of_le ?_ ?_ hsumC
        · intro i; split_ifs <;> positivity
        · intro i
          by_cases hi : a ≤ i
          · rw [if_pos hi]
          · simp only [if_neg hi]
            positivity
      calc
        (∑ i ∈ Finset.Ico a b, C * ((1 : ℝ) / (i + 2) ^ 2)) =
            ∑ i ∈ Finset.Ico a b,
              (if a ≤ i then C * ((1 : ℝ) / (i + 2) ^ 2) else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [if_pos (Finset.mem_Ico.mp hi).1]
        _ ≤ ∑' i : ℕ,
            if a ≤ i then C * ((1 : ℝ) / (i + 2) ^ 2) else 0 := by
          exact hs.sum_le_tsum (Finset.Ico a b) fun i hi ↦ by
            split_ifs <;> positivity
    _ = C * reciprocalSquareTail a := by
      rw [reciprocalSquareTail]
      calc
        (∑' i : ℕ, if a ≤ i then C * ((1 : ℝ) / (i + 2) ^ 2) else 0) =
            ∑' i : ℕ, C * (if a ≤ i then (1 : ℝ) / (i + 2) ^ 2 else 0) := by
          apply tsum_congr
          intro i
          split_ifs <;> ring
        _ = C * ∑' i : ℕ,
            if a ≤ i then (1 : ℝ) / (i + 2) ^ 2 else 0 := tsum_mul_left

theorem localFactor_eq_generic_mul_collision {r p : ℕ}
    (hp : r + 1 < p) (h : Fin r → ℕ) :
    localFactor p h =
      genericLocalFactor r p * collisionMultiplier p h := by
  have hp0n : 0 < p := by omega
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp0n.ne'
  have hpn : (p : ℝ) - ((r + 1 : ℕ) : ℝ) ≠ 0 := by
    have : ((r + 1 : ℕ) : ℝ) < p := by exact_mod_cast hp
    exact ne_of_gt (sub_pos.mpr this)
  unfold localFactor genericLocalFactor collisionMultiplier
  field_simp

theorem collisionMultiplier_bounds {r p : ℕ}
    (hp : 2 * (r + 1) ≤ p) (h : Fin r → ℕ) :
    1 ≤ collisionMultiplier p h ∧
      collisionMultiplier p h ≤
        1 + 2 * ((r + 1 : ℕ) : ℝ) / p := by
  let n : ℝ := (r + 1 : ℕ)
  let ν : ℝ := localMultiplicity p h
  have hp0n : 0 < p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp0n
  have hnp : n ≤ (p : ℝ) / 2 := by
    have hpR : (2 * (r + 1 : ℕ) : ℕ) ≤ p := hp
    have hpR' : (2 : ℝ) * ((r + 1 : ℕ) : ℝ) ≤ p := by
      exact_mod_cast hpR
    dsimp [n]
    linarith
  have hden : 0 < (p : ℝ) - n := by linarith
  have hνn : ν ≤ n := by
    dsimp [ν, n]
    exact_mod_cast localMultiplicity_le_card_add_one h
  have hν0 : 0 ≤ ν := by positivity
  unfold collisionMultiplier
  change 1 ≤ ((p : ℝ) - ν) / ((p : ℝ) - n) ∧
    ((p : ℝ) - ν) / ((p : ℝ) - n) ≤ 1 + 2 * n / p
  constructor
  · rw [le_div_iff₀ hden]
    linarith
  · rw [div_le_iff₀ hden]
    have htwo : 2 * n / (p : ℝ) ≤ 1 := by
      rw [div_le_one hp0]
      linarith
    have hprod : (2 * n / (p : ℝ)) * ((p : ℝ) - n) ≥ n := by
      rw [ge_iff_le]
      field_simp
      nlinarith
    nlinarith

theorem collisionMultiplier_eq_one {r p : ℕ} (h : Fin r → ℕ)
    (hp : r + 1 < p) (hν : localMultiplicity p h = r + 1) :
    collisionMultiplier p h = 1 := by
  unfold collisionMultiplier
  rw [hν]
  have : (p : ℝ) - ((r + 1 : ℕ) : ℝ) ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hp))
  exact div_self this

/-- The augmented tuple `(0,h₁,…,hᵣ)`. -/
def augmentedShift {r : ℕ} (h : Fin r → ℕ) : Fin (r + 1) → ℕ :=
  Fin.cases 0 h

@[simp] theorem augmentedShift_zero {r : ℕ} (h : Fin r → ℕ) :
    augmentedShift h 0 = 0 := by
  simp [augmentedShift]

@[simp] theorem augmentedShift_succ {r : ℕ} (h : Fin r → ℕ) (i : Fin r) :
    augmentedShift h i.succ = h i := by
  simp [augmentedShift]

theorem augmentedShift_injective {r m : ℕ} {h : Fin r → ℕ}
    (hh : h ∈ distinctShiftTuples r m) :
    Function.Injective (augmentedShift h) := by
  have hpos : ∀ i, h i ≠ 0 := fun i ↦
    Nat.ne_of_gt ((mem_distinctShiftTuples.mp hh).1 i).1
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
          simp only [augmentedShift_zero, augmentedShift_succ] at hij
          exact (hpos j hij.symm).elim
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          simp only [augmentedShift_zero, augmentedShift_succ] at hij
          exact (hpos i hij).elim
      | succ j =>
          simp only [augmentedShift_succ] at hij
          exact congrArg Fin.succ ((mem_distinctShiftTuples.mp hh).2 hij)

/-- Unordered pairs of coordinates of an augmented shift tuple, represented
by the strict order on their finite indices. -/
def collisionEdges (r : ℕ) : Finset (Fin (r + 1) × Fin (r + 1)) :=
  Finset.univ.filter fun e ↦ e.1 < e.2

@[simp] theorem mem_collisionEdges {r : ℕ}
    {e : Fin (r + 1) × Fin (r + 1)} :
    e ∈ collisionEdges r ↔ e.1 < e.2 := by
  simp [collisionEdges]

theorem collisionEdges_nonempty {r : ℕ} (hr : 0 < r) :
    (collisionEdges r).Nonempty := by
  let i : Fin (r + 1) := ⟨0, by omega⟩
  let j : Fin (r + 1) := ⟨1, by omega⟩
  refine ⟨(i, j), mem_collisionEdges.mpr ?_⟩
  change (0 : ℕ) < 1
  omega

/-- The positive absolute difference attached to an augmented-coordinate
pair. -/
def collisionDifference {r : ℕ} (h : Fin r → ℕ)
    (e : Fin (r + 1) × Fin (r + 1)) : ℕ :=
  Nat.dist (augmentedShift h e.1) (augmentedShift h e.2)

theorem collisionDifference_pos {r m : ℕ} {h : Fin r → ℕ}
    (hh : h ∈ distinctShiftTuples r m) {e} (he : e ∈ collisionEdges r) :
    0 < collisionDifference h e := by
  apply Nat.dist_pos_of_ne
  intro hc
  exact ne_of_lt (mem_collisionEdges.mp he) (augmentedShift_injective hh hc)

theorem augmentedShift_le {r m : ℕ} {h : Fin r → ℕ}
    (hh : h ∈ distinctShiftTuples r m) (i : Fin (r + 1)) :
    augmentedShift h i ≤ m := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simpa using ((mem_distinctShiftTuples.mp hh).1 j).2

theorem collisionDifference_le {r m : ℕ} {h : Fin r → ℕ}
    (hh : h ∈ distinctShiftTuples r m) (e) :
    collisionDifference h e ≤ m := by
  unfold collisionDifference
  have h1 := augmentedShift_le hh e.1
  have h2 := augmentedShift_le hh e.2
  unfold Nat.dist
  omega

theorem dvd_dist_iff_mod_eq {p a b : ℕ} :
    p ∣ Nat.dist a b ↔ a % p = b % p := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab, ← Nat.modEq_iff_dvd' hab]
    rfl
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hba,
      ← Nat.modEq_iff_dvd' hba]
    exact eq_comm

/-- Every deficient local multiplicity is witnessed by a prime dividing
one of the finitely many augmented-coordinate differences. -/
theorem exists_collisionEdge_dvd {r p : ℕ} (h : Fin r → ℕ)
    (hν : localMultiplicity p h < r + 1) :
    ∃ e ∈ collisionEdges r, p ∣ collisionDifference h e := by
  by_contra hnone
  push_neg at hnone
  have hzero : ∀ i, h i % p ≠ 0 := by
    intro i hi
    let e : Fin (r + 1) × Fin (r + 1) := (0, i.succ)
    have he : e ∈ collisionEdges r := by
      apply mem_collisionEdges.mpr
      change (0 : ℕ) < i.val + 1
      omega
    apply hnone e he
    have hdvd : p ∣ h i := Nat.dvd_iff_mod_eq_zero.mpr hi
    simpa [collisionDifference, e, Nat.dist_zero_left] using hdvd
  have hinj : Function.Injective fun i : Fin r ↦ h i % p := by
    intro i j hij
    by_contra hijFin
    rcases lt_or_gt_of_ne hijFin with hijlt | hjilt
    · let e : Fin (r + 1) × Fin (r + 1) := (i.succ, j.succ)
      have he : e ∈ collisionEdges r := by
        apply mem_collisionEdges.mpr
        exact Fin.succ_lt_succ_iff.mpr hijlt
      apply hnone e he
      have hdvd : p ∣ Nat.dist (h i) (h j) :=
        dvd_dist_iff_mod_eq.mpr hij
      simpa [collisionDifference, e] using hdvd
    · let e : Fin (r + 1) × Fin (r + 1) := (j.succ, i.succ)
      have he : e ∈ collisionEdges r := by
        apply mem_collisionEdges.mpr
        exact Fin.succ_lt_succ_iff.mpr hjilt
      apply hnone e he
      have hdvd : p ∣ Nat.dist (h j) (h i) :=
        dvd_dist_iff_mod_eq.mpr hij.symm
      simpa [collisionDifference, e] using hdvd
  have heq := localMultiplicity_eq_card_add_one h hzero hinj
  omega

/-- Product of the primes indexed by a finite set. -/
def indexedPrimeProduct (T : Finset ℕ) : ℕ :=
  ∏ i ∈ T, nthPrime i

theorem indexedPrimeProduct_pos (T : Finset ℕ) :
    0 < indexedPrimeProduct T := by
  unfold indexedPrimeProduct
  exact Finset.prod_pos fun i hi ↦ (nthPrime_prime i).pos

theorem indexedPrimeProduct_dvd_iff (T : Finset ℕ) (n : ℕ) :
    indexedPrimeProduct T ∣ n ↔ ∀ i ∈ T, nthPrime i ∣ n := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [indexedPrimeProduct]
  | @insert a T ha ih =>
      have hcop : (nthPrime a).Coprime (indexedPrimeProduct T) := by
        unfold indexedPrimeProduct
        apply Nat.Coprime.prod_right
        intro i hi
        exact (Nat.coprime_primes (nthPrime_prime a) (nthPrime_prime i)).mpr
          (fun hai ↦ by
            have hai' : a = i := nthPrime_strictMono.injective hai
            subst i
            exact ha hi)
      rw [indexedPrimeProduct, Finset.prod_insert ha]
      change nthPrime a * indexedPrimeProduct T ∣ n ↔ _
      rw [Finset.forall_mem_insert, ← ih]
      constructor
      · intro hd
        exact ⟨dvd_trans (dvd_mul_right _ _) hd,
          dvd_trans (dvd_mul_left _ _) hd⟩
      · rintro ⟨haD, hTD⟩
        exact hcop.mul_dvd_of_dvd_of_dvd haD hTD

/-- The `E`-th power of the standard divisor weight supported on a segment
of prime indices. -/
noncomputable def divisorWeightPower (A : ℝ) (E a b n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Ico a b,
    if nthPrime i ∣ n then (1 + A / nthPrime i) ^ E else 1

noncomputable def divisorWeightCoefficient (A : ℝ) (E i : ℕ) : ℝ :=
  (1 + A / nthPrime i) ^ E - 1

theorem divisorWeightCoefficient_nonneg {A : ℝ} (hA : 0 ≤ A)
    (E i : ℕ) : 0 ≤ divisorWeightCoefficient A E i := by
  unfold divisorWeightCoefficient
  have hbase : 1 ≤ 1 + A / (nthPrime i : ℝ) := by
    have hp : (0 : ℝ) < nthPrime i := by
      exact_mod_cast (nthPrime_prime i).pos
    linarith [div_nonneg hA hp.le]
  have hpow : 1 ≤ (1 + A / (nthPrime i : ℝ)) ^ E :=
    one_le_pow₀ hbase
  linarith

theorem divisorWeightPower_eq_powerset_sum {A : ℝ} (E a b n : ℕ) :
    divisorWeightPower A E a b n =
      ∑ T ∈ (Finset.Ico a b).powerset,
        if indexedPrimeProduct T ∣ n then
          ∏ i ∈ T, divisorWeightCoefficient A E i
        else 0 := by
  classical
  let S := Finset.Ico a b
  let β := divisorWeightCoefficient A E
  calc
    divisorWeightPower A E a b n =
        ∏ i ∈ S, (1 + if nthPrime i ∣ n then β i else 0) := by
      unfold divisorWeightPower
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hd : nthPrime i ∣ n
      · simp [hd, β, divisorWeightCoefficient]
      · simp [hd]
    _ = ∑ T ∈ S.powerset,
        ∏ i ∈ T, (if nthPrime i ∣ n then β i else 0) := by
      exact Finset.prod_one_add S
    _ = ∑ T ∈ S.powerset,
        if indexedPrimeProduct T ∣ n then ∏ i ∈ T, β i else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      by_cases hdiv : indexedPrimeProduct T ∣ n
      · rw [if_pos hdiv]
        have hall := (indexedPrimeProduct_dvd_iff T n).mp hdiv
        apply Finset.prod_congr rfl
        intro i hi
        rw [if_pos (hall i hi)]
      · rw [if_neg hdiv]
        have hnot : ¬∀ i ∈ T, nthPrime i ∣ n := by
          intro hall
          exact hdiv ((indexedPrimeProduct_dvd_iff T n).mpr hall)
        push Not at hnot
        obtain ⟨i, hiT, hi⟩ := hnot
        exact Finset.prod_eq_zero hiT (if_neg hi)
    _ = _ := rfl

theorem sum_divisorWeightPower_le {A : ℝ} (hA : 0 ≤ A)
    (E a b m : ℕ) :
    (∑ n ∈ Finset.Ioc 0 m, divisorWeightPower A E a b n) ≤
      (m : ℝ) * ∏ i ∈ Finset.Ico a b,
        (1 + divisorWeightCoefficient A E i / nthPrime i) := by
  classical
  let S := Finset.Ico a b
  let β := divisorWeightCoefficient A E
  have hβ (i : ℕ) : 0 ≤ β i :=
    divisorWeightCoefficient_nonneg hA E i
  have hinner (T : Finset ℕ) :
      (∑ n ∈ Finset.Ioc 0 m,
          if indexedPrimeProduct T ∣ n then ∏ i ∈ T, β i else 0) =
        ((m / indexedPrimeProduct T : ℕ) : ℝ) * ∏ i ∈ T, β i := by
    rw [← Finset.sum_filter]
    have hcard :
        ((Finset.Ioc 0 m).filter (fun n ↦ indexedPrimeProduct T ∣ n)).card =
          m / indexedPrimeProduct T := by
      exact Nat.Ioc_filter_dvd_card_eq_div m (indexedPrimeProduct T)
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  have hterm (T : Finset ℕ) :
      ((m / indexedPrimeProduct T : ℕ) : ℝ) * ∏ i ∈ T, β i ≤
        (m : ℝ) * ∏ i ∈ T, (β i / nthPrime i) := by
    have hB : 0 ≤ ∏ i ∈ T, β i :=
      Finset.prod_nonneg fun i hi ↦ hβ i
    have hqpos : (0 : ℝ) < indexedPrimeProduct T := by
      exact_mod_cast indexedPrimeProduct_pos T
    have hdiv : ((m / indexedPrimeProduct T : ℕ) : ℝ) ≤
        (m : ℝ) / indexedPrimeProduct T := Nat.cast_div_le
    calc
      ((m / indexedPrimeProduct T : ℕ) : ℝ) * ∏ i ∈ T, β i ≤
          ((m : ℝ) / indexedPrimeProduct T) * ∏ i ∈ T, β i :=
        mul_le_mul_of_nonneg_right hdiv hB
      _ = (m : ℝ) * ∏ i ∈ T, (β i / nthPrime i) := by
        rw [Finset.prod_div_distrib]
        unfold indexedPrimeProduct
        push_cast
        field_simp
  calc
    (∑ n ∈ Finset.Ioc 0 m, divisorWeightPower A E a b n) =
        ∑ T ∈ S.powerset,
          ((m / indexedPrimeProduct T : ℕ) : ℝ) * ∏ i ∈ T, β i := by
      simp_rw [divisorWeightPower_eq_powerset_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T hT
      exact hinner T
    _ ≤ ∑ T ∈ S.powerset,
        (m : ℝ) * ∏ i ∈ T, (β i / nthPrime i) := by
      exact Finset.sum_le_sum fun T hT ↦ hterm T
    _ = (m : ℝ) * ∑ T ∈ S.powerset,
        ∏ i ∈ T, (β i / nthPrime i) := by
      rw [Finset.mul_sum]
    _ = (m : ℝ) * ∏ i ∈ S, (1 + β i / nthPrime i) := by
      rw [Finset.prod_one_add]
    _ = _ := rfl

theorem pow_one_add_sub_one_le (E : ℕ) {A x : ℝ}
    (hx0 : 0 ≤ x) (hxA : x ≤ A) :
    (1 + x) ^ E - 1 ≤ (E : ℝ) * x * (1 + A) ^ E := by
  have hA0 : 0 ≤ A := hx0.trans hxA
  induction E with
  | zero => simp
  | succ E ih =>
      have hbase0 : 0 ≤ 1 + x := by positivity
      have hbig1 : 1 ≤ (1 + A) ^ (E + 1) := by
        exact one_le_pow₀ (by linarith)
      rw [pow_succ]
      have hid : (1 + x) ^ E * (1 + x) - 1 =
          (1 + x) * ((1 + x) ^ E - 1) + x := by ring
      rw [hid]
      calc
        (1 + x) * ((1 + x) ^ E - 1) + x ≤
            (1 + x) * ((E : ℝ) * x * (1 + A) ^ E) + x := by
          gcongr
        _ ≤ (1 + A) * ((E : ℝ) * x * (1 + A) ^ E) + x := by
          gcongr
        _ = (E : ℝ) * x * (1 + A) ^ (E + 1) + x := by
          rw [pow_succ]
          ring
        _ ≤ ((E + 1 : ℕ) : ℝ) * x * (1 + A) ^ (E + 1) := by
          push_cast
          nlinarith [mul_nonneg hx0 (zero_le_one.trans hbig1)]

theorem divisorWeightCoefficient_le {A : ℝ} (hA : 0 ≤ A)
    (E i : ℕ) :
    divisorWeightCoefficient A E i ≤
      ((E : ℝ) * A * (1 + A) ^ E) / nthPrime i := by
  have hp1 : (1 : ℝ) ≤ nthPrime i := by
    exact_mod_cast (nthPrime_prime i).one_le
  have hp0 : (0 : ℝ) < nthPrime i := by
    exact_mod_cast (nthPrime_prime i).pos
  have hx0 : 0 ≤ A / (nthPrime i : ℝ) := div_nonneg hA hp0.le
  have hxA : A / (nthPrime i : ℝ) ≤ A := by
    exact (div_le_iff₀ hp0).mpr (by nlinarith)
  unfold divisorWeightCoefficient
  calc
    (1 + A / (nthPrime i : ℝ)) ^ E - 1 ≤
        (E : ℝ) * (A / (nthPrime i : ℝ)) * (1 + A) ^ E :=
      pow_one_add_sub_one_le E hx0 hxA
    _ = ((E : ℝ) * A * (1 + A) ^ E) / nthPrime i := by ring

theorem divisorWeightEulerProduct_le_exp {A : ℝ} (hA : 0 ≤ A)
    (E a b : ℕ) :
    (∏ i ∈ Finset.Ico a b,
        (1 + divisorWeightCoefficient A E i / nthPrime i)) ≤
      Real.exp (((E : ℝ) * A * (1 + A) ^ E) *
        reciprocalSquareTail a) := by
  let B : ℝ := (E : ℝ) * A * (1 + A) ^ E
  have hterm (i : ℕ) :
      0 ≤ divisorWeightCoefficient A E i / (nthPrime i : ℝ) :=
    div_nonneg (divisorWeightCoefficient_nonneg hA E i)
      (by positivity)
  calc
    (∏ i ∈ Finset.Ico a b,
        (1 + divisorWeightCoefficient A E i / nthPrime i)) ≤
        Real.exp (∑ i ∈ Finset.Ico a b,
          divisorWeightCoefficient A E i / nthPrime i) := by
      exact Real.prod_one_add_le_exp_sum _ hterm
    _ ≤ Real.exp (∑ i ∈ Finset.Ico a b,
          B * ((1 : ℝ) / (i + 2) ^ 2)) := by
      apply Real.exp_le_exp.mpr
      apply Finset.sum_le_sum
      intro i hi
      have hcoef := divisorWeightCoefficient_le hA E i
      have hp0 : (0 : ℝ) < nthPrime i := by
        exact_mod_cast (nthPrime_prime i).pos
      have hindex : (i + 2 : ℝ) ≤ nthPrime i := by
        exact_mod_cast add_two_le_nthPrime i
      have hB : 0 ≤ B := by positivity
      calc
        divisorWeightCoefficient A E i / (nthPrime i : ℝ) ≤
            B / (nthPrime i : ℝ) ^ 2 := by
          calc
            divisorWeightCoefficient A E i / (nthPrime i : ℝ) ≤
                (B / (nthPrime i : ℝ)) / (nthPrime i : ℝ) :=
              div_le_div_of_nonneg_right hcoef hp0.le
            _ = B / (nthPrime i : ℝ) ^ 2 := by ring
        _ ≤ B * ((1 : ℝ) / (i + 2 : ℝ) ^ 2) := by
          have hsquare : (i + 2 : ℝ) ^ 2 ≤ (nthPrime i : ℝ) ^ 2 :=
            (sq_le_sq₀ (by positivity) hp0.le).2 hindex
          calc
            B / (nthPrime i : ℝ) ^ 2 ≤ B / (i + 2 : ℝ) ^ 2 := by
              rw [div_le_div_iff₀ (sq_pos_of_pos hp0) (by positivity)]
              exact mul_le_mul_of_nonneg_left hsquare hB
            _ = B * (1 / (i + 2 : ℝ) ^ 2) := by ring
    _ ≤ Real.exp (B * reciprocalSquareTail a) := by
      apply Real.exp_le_exp.mpr
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hs : Summable (fun i : ℕ ↦
          if a ≤ i then (1 : ℝ) / (i + 2) ^ 2 else 0) := by
        have hbase : Summable (fun i : ℕ ↦ (1 : ℝ) / (i + 2) ^ 2) := by
          simpa using (summable_nat_add_iff 2).2
            (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
        refine Summable.of_nonneg_of_le ?_ ?_ hbase
        · intro i; split_ifs <;> positivity
        · intro i
          by_cases hi : a ≤ i
          · rw [if_pos hi]
          · rw [if_neg hi]
            positivity
      calc
        (∑ i ∈ Finset.Ico a b, (1 : ℝ) / (i + 2) ^ 2) =
            ∑ i ∈ Finset.Ico a b,
              (if a ≤ i then (1 : ℝ) / (i + 2) ^ 2 else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [if_pos (Finset.mem_Ico.mp hi).1]
        _ ≤ ∑' i : ℕ,
            if a ≤ i then (1 : ℝ) / (i + 2) ^ 2 else 0 := by
          exact hs.sum_le_tsum _ fun i hi ↦ by split_ifs <;> positivity
        _ = reciprocalSquareTail a := rfl
    _ = _ := rfl

/-- Product of the collision multipliers on a prime-index segment. -/
noncomputable def collisionSeriesSegment {r : ℕ} (a b : ℕ)
    (h : Fin r → ℕ) : ℝ :=
  ∏ i ∈ Finset.Ico a b, collisionMultiplier (nthPrime i) h

theorem singularSeriesSegment_eq_generic_mul_collision {r a b : ℕ}
    (ha : r + 1 < nthPrime a) (h : Fin r → ℕ) :
    singularSeriesSegment a b h =
      genericSeriesSegment r a b * collisionSeriesSegment a b h := by
  unfold singularSeriesSegment genericSeriesSegment collisionSeriesSegment
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact localFactor_eq_generic_mul_collision
    (ha.trans_le (nthPrime_strictMono.monotone (Finset.mem_Ico.mp hi).1)) h

theorem one_le_product_factor {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) {a : α} (ha : a ∈ s)
    (hf : ∀ i ∈ s, 1 ≤ f i) :
    f a ≤ ∏ i ∈ s, f i := by
  calc
    f a = f a * 1 := by ring
    _ ≤ f a * ∏ i ∈ s.erase a, f i := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.one_le_prod fun i hi ↦ hf i (Finset.mem_of_mem_erase hi)
      · exact zero_le_one.trans (hf a ha)
    _ = ∏ i ∈ s, f i := Finset.mul_prod_erase s f ha

theorem collisionMultiplier_le_edgeProduct {r a i : ℕ}
    (ha : 2 * (r + 1) ≤ nthPrime a) (hai : a ≤ i)
    (h : Fin r → ℕ) :
    collisionMultiplier (nthPrime i) h ≤
      ∏ e ∈ collisionEdges r,
        if nthPrime i ∣ collisionDifference h e then
          1 + (2 * ((r + 1 : ℕ) : ℝ)) / nthPrime i else 1 := by
  let p := nthPrime i
  let A : ℝ := 2 * ((r + 1 : ℕ) : ℝ)
  have hp : 2 * (r + 1) ≤ p :=
    ha.trans (nthPrime_strictMono.monotone hai)
  have hmult := collisionMultiplier_bounds hp h
  have hedge (e) : 1 ≤
      (if p ∣ collisionDifference h e then 1 + A / p else 1) := by
    by_cases hd : p ∣ collisionDifference h e
    · rw [if_pos hd]
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (nthPrime_prime i).pos
      dsimp [A]
      exact le_add_of_nonneg_right (div_nonneg (by positivity) hp0.le)
    · rw [if_neg hd]
  by_cases hν : localMultiplicity p h = r + 1
  · rw [collisionMultiplier_eq_one h (by omega) hν]
    exact Finset.one_le_prod fun e he ↦ hedge e
  · have hνlt : localMultiplicity p h < r + 1 := by
      have := localMultiplicity_le_card_add_one (p := p) h
      omega
    obtain ⟨e, he, hd⟩ := exists_collisionEdge_dvd h hνlt
    calc
      collisionMultiplier p h ≤ 1 + A / p := by
        simpa [A] using hmult.2
      _ = (if p ∣ collisionDifference h e then 1 + A / p else 1) := by
        rw [if_pos hd]
      _ ≤ ∏ e ∈ collisionEdges r,
          (if p ∣ collisionDifference h e then 1 + A / p else 1) := by
        exact one_le_product_factor _ _ he fun e he ↦ hedge e

theorem collisionSeriesSegment_le_edgeWeights {r a b : ℕ}
    (ha : 2 * (r + 1) ≤ nthPrime a) (h : Fin r → ℕ) :
    collisionSeriesSegment a b h ≤
      ∏ e ∈ collisionEdges r,
        divisorWeightPower (2 * ((r + 1 : ℕ) : ℝ)) 1 a b
          (collisionDifference h e) := by
  unfold collisionSeriesSegment
  calc
    (∏ i ∈ Finset.Ico a b, collisionMultiplier (nthPrime i) h) ≤
        ∏ i ∈ Finset.Ico a b,
          ∏ e ∈ collisionEdges r,
            if nthPrime i ∣ collisionDifference h e then
              1 + (2 * ((r + 1 : ℕ) : ℝ)) / nthPrime i else 1 := by
      apply Finset.prod_le_prod
      · intro i hi
        exact (collisionMultiplier_bounds
          (ha.trans (nthPrime_strictMono.monotone
            (Finset.mem_Ico.mp hi).1)) h).1.trans' zero_le_one
      · intro i hi
        exact collisionMultiplier_le_edgeProduct ha
          (Finset.mem_Ico.mp hi).1 h
    _ = ∏ e ∈ collisionEdges r,
        divisorWeightPower (2 * ((r + 1 : ℕ) : ℝ)) 1 a b
          (collisionDifference h e) := by
      rw [Finset.prod_comm]
      apply Finset.prod_congr rfl
      intro e he
      unfold divisorWeightPower
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hd : nthPrime i ∣ collisionDifference h e
      · simp [hd]
      · simp [hd]

theorem prod_le_sum_pow_card {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) (z : α → ℝ)
    (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∏ i ∈ s, z i) ≤ ∑ i ∈ s, (z i) ^ s.card := by
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s z hs
  calc
    (∏ i ∈ s, z i) ≤ ∏ _i ∈ s, z a := by
      exact Finset.prod_le_prod hz fun i hi ↦ hmax i hi
    _ = (z a) ^ s.card := by simp
    _ ≤ ∑ i ∈ s, (z i) ^ s.card := by
      exact Finset.single_le_sum
        (fun i hi ↦ pow_nonneg (hz i hi) _) ha

theorem divisorWeightPower_one_pow (A : ℝ) (E a b n : ℕ) :
    (divisorWeightPower A 1 a b n) ^ E =
      divisorWeightPower A E a b n := by
  unfold divisorWeightPower
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hd : nthPrime i ∣ n
  · simp [hd, pow_mul]
  · simp [hd]

theorem collisionSeriesSegment_le_edgeWeightSum {r a b : ℕ}
    (hr : 0 < r) (ha : 2 * (r + 1) ≤ nthPrime a)
    (h : Fin r → ℕ) :
    collisionSeriesSegment a b h ≤
      ∑ e ∈ collisionEdges r,
        divisorWeightPower (2 * ((r + 1 : ℕ) : ℝ))
          (collisionEdges r).card a b (collisionDifference h e) := by
  let A : ℝ := 2 * ((r + 1 : ℕ) : ℝ)
  let z := fun e ↦ divisorWeightPower A 1 a b (collisionDifference h e)
  have hz : ∀ e ∈ collisionEdges r, 0 ≤ z e := by
    intro e he
    unfold z divisorWeightPower
    apply Finset.prod_nonneg
    intro i hi
    split_ifs <;> positivity
  calc
    collisionSeriesSegment a b h ≤ ∏ e ∈ collisionEdges r, z e := by
      simpa [A, z] using collisionSeriesSegment_le_edgeWeights ha h
    _ ≤ ∑ e ∈ collisionEdges r, (z e) ^ (collisionEdges r).card :=
      prod_le_sum_pow_card _ (collisionEdges_nonempty hr) z hz
    _ = ∑ e ∈ collisionEdges r,
        divisorWeightPower A (collisionEdges r).card a b
          (collisionDifference h e) := by
      apply Finset.sum_congr rfl
      intro e he
      exact divisorWeightPower_one_pow A _ a b _
    _ = _ := rfl

def collisionFiber (r m : ℕ)
    (e : Fin (r + 1) × Fin (r + 1)) (n : ℕ) :
    Finset (Fin r → ℕ) :=
  (shiftBox r m).filter fun h ↦ collisionDifference h e = n

@[simp] theorem mem_collisionFiber {r m n : ℕ}
    {e : Fin (r + 1) × Fin (r + 1)} {h : Fin r → ℕ} :
    h ∈ collisionFiber r m e n ↔
      h ∈ shiftBox r m ∧ collisionDifference h e = n := by
  simp [collisionFiber]

/-- Once all but the later coordinate of an edge are fixed, a prescribed
absolute difference permits at most two values of that coordinate. -/
theorem card_collisionFiber_le {r m n : ℕ}
    (hr : 0 < r) {e : Fin (r + 1) × Fin (r + 1)}
    (he : e ∈ collisionEdges r) :
    (collisionFiber r m e n).card ≤ 2 * m ^ (r - 1) := by
  classical
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have heLt : e.1 < e.2 := mem_collisionEdges.mp he
  have he2pos : 0 < e.2.val := by
    have : (0 : Fin (s + 2)) < e.2 :=
      (Fin.zero_le e.1).trans_lt heLt
    exact this
  let j : Fin (s + 1) := ⟨e.2.val - 1, by omega⟩
  have he2 : j.succ = e.2 := by
    apply Fin.ext
    simp [j]
    omega
  let encode : ↥(collisionFiber (s + 1) m e n) →
      Bool × (Fin s → Fin m) := fun H ↦
    (decide (augmentedShift H.1 e.1 ≤ augmentedShift H.1 e.2),
      fun q ↦ ⟨H.1 (j.succAbove q) - 1, by
        have hb := (mem_shiftBox.mp
          (mem_collisionFiber.mp H.2).1 (j.succAbove q))
        omega⟩)
  have hencode : Function.Injective encode := by
    intro H G hHG
    have hbool := congrArg Prod.fst hHG
    have hrest := congrArg Prod.snd hHG
    have hrestNat (q : Fin s) :
        H.1 (j.succAbove q) = G.1 (j.succAbove q) := by
      have hq := congrArg (fun f : Fin s → Fin m ↦ (f q).val) hrest
      dsimp [encode] at hq
      have hH := (mem_shiftBox.mp
        (mem_collisionFiber.mp H.2).1 (j.succAbove q)).1
      have hG := (mem_shiftBox.mp
        (mem_collisionFiber.mp G.2).1 (j.succAbove q)).1
      omega
    have heNe : e.1 ≠ e.2 := ne_of_lt heLt
    have hbase : augmentedShift H.1 e.1 = augmentedShift G.1 e.1 := by
      cases e1 : e.1 using Fin.cases with
      | zero => simp [e1]
      | succ q =>
          have hqj : q ≠ j := by
            intro hqj
            subst q
            exact heNe (e1.trans he2)
          obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hqj
          simpa [e1, hz] using hrestNat z
    have hdistH :
        Nat.dist (augmentedShift H.1 e.1) (H.1 j) = n := by
      have := (mem_collisionFiber.mp H.2).2
      unfold collisionDifference at this
      simpa [← he2] using this
    have hdistG :
        Nat.dist (augmentedShift G.1 e.1) (G.1 j) = n := by
      have := (mem_collisionFiber.mp G.2).2
      unfold collisionDifference at this
      simpa [← he2] using this
    have horient :
        (augmentedShift H.1 e.1 ≤ H.1 j) ↔
          (augmentedShift G.1 e.1 ≤ G.1 j) := by
      dsimp [encode] at hbool
      constructor
      · intro hH
        by_contra hG
        have hb := hbool
        simp [← he2, hH, hG] at hb
      · intro hG
        by_contra hH
        have hb := hbool
        simp [← he2, hH, hG] at hb
    have hpivot : H.1 j = G.1 j := by
      unfold Nat.dist at hdistH hdistG
      by_cases hle : augmentedShift H.1 e.1 ≤ H.1 j
      · have hleG := horient.mp hle
        omega
      · have hleG := not_le.mp fun h ↦ hle (horient.mpr h)
        omega
    apply Subtype.ext
    funext q
    by_cases hqj : q = j
    · simpa [hqj] using hpivot
    · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hqj
      simpa [hz] using hrestNat z
  calc
    (collisionFiber (s + 1) m e n).card =
        Fintype.card ↥(collisionFiber (s + 1) m e n) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Bool × (Fin s → Fin m)) :=
      Fintype.card_le_of_injective encode hencode
    _ = 2 * m ^ s := by simp [Fintype.card_fun]
    _ = 2 * m ^ (s + 1 - 1) := by simp

theorem sum_distinct_edgeWeight_le {r m : ℕ}
    (hr : 0 < r) {e : Fin (r + 1) × Fin (r + 1)}
    (he : e ∈ collisionEdges r) (W : ℕ → ℝ)
    (hW : ∀ n, 0 ≤ W n) :
    (∑ h ∈ distinctShiftTuples r m, W (collisionDifference h e)) ≤
      (2 * m ^ (r - 1) : ℕ) * ∑ n ∈ Finset.Icc 1 m, W n := by
  classical
  let F : ℕ → Finset (Fin r → ℕ) := fun n ↦
    (distinctShiftTuples r m).filter fun h ↦ collisionDifference h e = n
  have hmem (h : Fin r → ℕ) (hh : h ∈ distinctShiftTuples r m) :
      collisionDifference h e ∈ Finset.Icc 1 m := by
    exact Finset.mem_Icc.mpr
      ⟨collisionDifference_pos hh he, collisionDifference_le hh e⟩
  have hcard (n : ℕ) : (F n).card ≤ 2 * m ^ (r - 1) := by
    calc
      (F n).card ≤ (collisionFiber r m e n).card := by
        apply Finset.card_le_card
        intro h hh
        have hh' := Finset.mem_filter.mp hh
        exact mem_collisionFiber.mpr
          ⟨mem_shiftBox.mpr (mem_distinctShiftTuples.mp hh'.1).1, hh'.2⟩
      _ ≤ 2 * m ^ (r - 1) := card_collisionFiber_le hr he
  have hgroup :
      (∑ h ∈ distinctShiftTuples r m, W (collisionDifference h e)) =
        ∑ n ∈ Finset.Icc 1 m, ∑ h ∈ distinctShiftTuples r m with
          collisionDifference h e = n, W (collisionDifference h e) := by
    rw [Finset.sum_fiberwise_eq_sum_filter]
    apply Finset.sum_congr
    · ext h
      simp only [Finset.mem_filter]
      exact (and_iff_left_of_imp fun hh ↦ hmem h hh).symm
    · intro h hh
      rfl
  rw [hgroup]
  calc
    (∑ n ∈ Finset.Icc 1 m, ∑ h ∈ distinctShiftTuples r m with
        collisionDifference h e = n, W (collisionDifference h e)) =
        ∑ n ∈ Finset.Icc 1 m, ((F n).card : ℝ) * W n := by
      apply Finset.sum_congr rfl
      intro n hn
      change (∑ h ∈ F n, W (collisionDifference h e)) = _
      calc
        (∑ h ∈ F n, W (collisionDifference h e)) =
            ∑ _h ∈ F n, W n := by
          apply Finset.sum_congr rfl
          intro h hh
          rw [(Finset.mem_filter.mp hh).2]
        _ = ((F n).card : ℝ) * W n := by simp [nsmul_eq_mul]
    _ ≤ ∑ n ∈ Finset.Icc 1 m,
        ((2 * m ^ (r - 1) : ℕ) : ℝ) * W n := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard n) (hW n)
    _ = ((2 * m ^ (r - 1) : ℕ) : ℝ) *
        ∑ n ∈ Finset.Icc 1 m, W n := by
      rw [Finset.mul_sum]

theorem one_le_divisorWeightPower {A : ℝ} (hA : 0 ≤ A)
    (E a b n : ℕ) : 1 ≤ divisorWeightPower A E a b n := by
  unfold divisorWeightPower
  apply Finset.one_le_prod
  intro i hi
  by_cases hd : nthPrime i ∣ n
  · rw [if_pos hd]
    apply one_le_pow₀
    have hp0 : (0 : ℝ) < nthPrime i := by
      exact_mod_cast (nthPrime_prime i).pos
    exact le_add_of_nonneg_right (div_nonneg hA hp0.le)
  · rw [if_neg hd]

theorem prod_sub_one_le_sum_pow_sub_one {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) (z : α → ℝ)
    (hz : ∀ i ∈ s, 1 ≤ z i) :
    (∏ i ∈ s, z i) - 1 ≤
      ∑ i ∈ s, ((z i) ^ s.card - 1) := by
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s z hs
  have hprod : (∏ i ∈ s, z i) ≤ (z a) ^ s.card := by
    calc
      (∏ i ∈ s, z i) ≤ ∏ _i ∈ s, z a := by
        apply Finset.prod_le_prod
        · intro i hi
          exact zero_le_one.trans (hz i hi)
        · intro i hi
          exact hmax i hi
      _ = (z a) ^ s.card := by simp
  calc
    (∏ i ∈ s, z i) - 1 ≤ (z a) ^ s.card - 1 := sub_le_sub_right hprod 1
    _ ≤ ∑ i ∈ s, ((z i) ^ s.card - 1) := by
      exact Finset.single_le_sum
        (fun i hi ↦ sub_nonneg.mpr (one_le_pow₀ (hz i hi))) ha

theorem collisionSeriesSegment_sub_one_le_edgeErrors {r a b : ℕ}
    (hr : 0 < r) (ha : 2 * (r + 1) ≤ nthPrime a)
    (h : Fin r → ℕ) :
    collisionSeriesSegment a b h - 1 ≤
      ∑ e ∈ collisionEdges r,
        (divisorWeightPower (2 * ((r + 1 : ℕ) : ℝ))
          (collisionEdges r).card a b (collisionDifference h e) - 1) := by
  let A : ℝ := 2 * ((r + 1 : ℕ) : ℝ)
  let z := fun e ↦ divisorWeightPower A 1 a b (collisionDifference h e)
  have hz : ∀ e ∈ collisionEdges r, 1 ≤ z e := by
    intro e he
    exact one_le_divisorWeightPower (A := A) (by positivity) 1 a b _
  calc
    collisionSeriesSegment a b h - 1 ≤
        (∏ e ∈ collisionEdges r, z e) - 1 := by
      exact sub_le_sub_right (by
        simpa [A, z] using collisionSeriesSegment_le_edgeWeights ha h) 1
    _ ≤ ∑ e ∈ collisionEdges r,
        ((z e) ^ (collisionEdges r).card - 1) :=
      prod_sub_one_le_sum_pow_sub_one _ (collisionEdges_nonempty hr) z hz
    _ = ∑ e ∈ collisionEdges r,
        (divisorWeightPower A (collisionEdges r).card a b
          (collisionDifference h e) - 1) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [divisorWeightPower_one_pow]
    _ = _ := rfl

theorem sum_divisorWeightPower_sub_one_le {A : ℝ} (hA : 0 ≤ A)
    (E a b m : ℕ) :
    (∑ n ∈ Finset.Icc 1 m, (divisorWeightPower A E a b n - 1)) ≤
      (m : ℝ) *
    (Real.exp (((E : ℝ) * A * (1 + A) ^ E) *
          reciprocalSquareTail a) - 1) := by
  have hsum := sum_divisorWeightPower_le hA E a b m
  have hinterval : Finset.Ioc 0 m = Finset.Icc 1 m := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hinterval] at hsum
  have heuler := divisorWeightEulerProduct_le_exp hA E a b
  have hm : ((Finset.Icc 1 m).card : ℝ) = m := by simp
  calc
    (∑ n ∈ Finset.Icc 1 m, (divisorWeightPower A E a b n - 1)) =
        (∑ n ∈ Finset.Icc 1 m, divisorWeightPower A E a b n) - m := by
      rw [Finset.sum_sub_distrib]
      simp
    _ ≤ (m : ℝ) * (∏ i ∈ Finset.Ico a b,
          (1 + divisorWeightCoefficient A E i / nthPrime i)) - m := by
      linarith
    _ ≤ (m : ℝ) * Real.exp (((E : ℝ) * A * (1 + A) ^ E) *
          reciprocalSquareTail a) - m := by
      gcongr
    _ = (m : ℝ) *
        (Real.exp (((E : ℝ) * A * (1 + A) ^ E) *
          reciprocalSquareTail a) - 1) := by ring

theorem sum_collisionSeriesSegment_sub_one_le {r a b m : ℕ}
    (hr : 0 < r) (ha : 2 * (r + 1) ≤ nthPrime a) :
    (∑ h ∈ distinctShiftTuples r m,
        (collisionSeriesSegment a b h - 1)) ≤
      ((collisionEdges r).card : ℝ) *
        ((2 * m ^ (r - 1) : ℕ) : ℝ) * (m : ℝ) *
        (Real.exp
          ((((collisionEdges r).card : ℝ) *
              (2 * ((r + 1 : ℕ) : ℝ)) *
              (1 + 2 * ((r + 1 : ℕ) : ℝ)) ^ (collisionEdges r).card) *
            reciprocalSquareTail a) - 1) := by
  let A : ℝ := 2 * ((r + 1 : ℕ) : ℝ)
  let E : ℕ := (collisionEdges r).card
  let err : ℝ := Real.exp (((E : ℝ) * A * (1 + A) ^ E) *
    reciprocalSquareTail a) - 1
  have herr0 : 0 ≤ err := by
    dsimp [err]
    exact sub_nonneg.mpr (Real.one_le_exp
      (mul_nonneg (by positivity) (reciprocalSquareTail_nonneg a)))
  have hedge (e : Fin (r + 1) × Fin (r + 1))
      (he : e ∈ collisionEdges r) :
      (∑ h ∈ distinctShiftTuples r m,
        (divisorWeightPower A E a b (collisionDifference h e) - 1)) ≤
          ((2 * m ^ (r - 1) : ℕ) : ℝ) * (m : ℝ) * err := by
    let W := fun n ↦ divisorWeightPower A E a b n - 1
    have hW (n : ℕ) : 0 ≤ W n := by
      exact sub_nonneg.mpr (one_le_divisorWeightPower (A := A)
        (by positivity) E a b n)
    calc
      (∑ h ∈ distinctShiftTuples r m,
          (divisorWeightPower A E a b (collisionDifference h e) - 1)) =
          ∑ h ∈ distinctShiftTuples r m, W (collisionDifference h e) := rfl
      _ ≤ ((2 * m ^ (r - 1) : ℕ) : ℝ) *
          ∑ n ∈ Finset.Icc 1 m, W n :=
        sum_distinct_edgeWeight_le hr he W hW
      _ ≤ ((2 * m ^ (r - 1) : ℕ) : ℝ) * ((m : ℝ) * err) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa [A, E, err, W] using
          sum_divisorWeightPower_sub_one_le (A := A) (by positivity) E a b m
      _ = ((2 * m ^ (r - 1) : ℕ) : ℝ) * (m : ℝ) * err := by ring
  calc
    (∑ h ∈ distinctShiftTuples r m,
        (collisionSeriesSegment a b h - 1)) ≤
        ∑ h ∈ distinctShiftTuples r m,
          ∑ e ∈ collisionEdges r,
            (divisorWeightPower A E a b (collisionDifference h e) - 1) := by
      apply Finset.sum_le_sum
      intro h hh
      exact collisionSeriesSegment_sub_one_le_edgeErrors hr ha h
    _ = ∑ e ∈ collisionEdges r,
        ∑ h ∈ distinctShiftTuples r m,
          (divisorWeightPower A E a b (collisionDifference h e) - 1) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ _e ∈ collisionEdges r,
        (((2 * m ^ (r - 1) : ℕ) : ℝ) * (m : ℝ) * err) := by
      exact Finset.sum_le_sum fun e he ↦ hedge e he
    _ = ((collisionEdges r).card : ℝ) *
        ((2 * m ^ (r - 1) : ℕ) : ℝ) * (m : ℝ) * err := by
      simp [nsmul_eq_mul]
      ring
    _ = _ := by rfl

theorem one_le_collisionSeriesSegment {r a b : ℕ}
    (ha : 2 * (r + 1) ≤ nthPrime a) (h : Fin r → ℕ) :
    1 ≤ collisionSeriesSegment a b h := by
  unfold collisionSeriesSegment
  apply Finset.one_le_prod
  intro i hi
  exact (collisionMultiplier_bounds
    (ha.trans (nthPrime_strictMono.monotone (Finset.mem_Ico.mp hi).1)) h).1

theorem sum_collisionSeriesSegment_sub_one_le_pow {r a b m : ℕ}
    (hr : 0 < r) (ha : 2 * (r + 1) ≤ nthPrime a) :
    (∑ h ∈ distinctShiftTuples r m,
        (collisionSeriesSegment a b h - 1)) ≤
      (m : ℝ) ^ r *
        (2 * ((collisionEdges r).card : ℝ) *
          (Real.exp
            ((((collisionEdges r).card : ℝ) *
                (2 * ((r + 1 : ℕ) : ℝ)) *
                (1 + 2 * ((r + 1 : ℕ) : ℝ)) ^ (collisionEdges r).card) *
              reciprocalSquareTail a) - 1)) := by
  have h := sum_collisionSeriesSegment_sub_one_le
    (a := a) (b := b) (m := m) hr ha
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hcoef :
      ((collisionEdges (s + 1)).card : ℝ) *
          ((2 * m ^ (s + 1 - 1) : ℕ) : ℝ) * (m : ℝ) =
        (m : ℝ) ^ (s + 1) * (2 * ((collisionEdges (s + 1)).card : ℝ)) := by
    simp only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
      pow_succ]
    ring
  rw [hcoef] at h
  simpa only [mul_assoc] using h

theorem abs_mul_sub_one_le {G C : ℝ}
    (hG0 : 0 ≤ G) (hG1 : G ≤ 1) (hC : 1 ≤ C) :
    |G * C - 1| ≤ (1 - G) * C + (C - 1) := by
  have h1 : 0 ≤ C - 1 := sub_nonneg.mpr hC
  have h2 : 0 ≤ (1 - G) * C :=
    mul_nonneg (sub_nonneg.mpr hG1) (zero_le_one.trans hC)
  rw [show G * C - 1 = (C - 1) - (1 - G) * C by ring]
  calc
    |(C - 1) - (1 - G) * C| ≤ |C - 1| + |(1 - G) * C| :=
      abs_sub _ _
    _ = (1 - G) * C + (C - 1) := by
      rw [abs_of_nonneg h1, abs_of_nonneg h2]
      ring

noncomputable def genericTailError (r a : ℕ) : ℝ :=
  ((r + 1 : ℕ) : ℝ) ^ 2 * 2 ^ (r + 1) * reciprocalSquareTail a

noncomputable def collisionTailError (r a : ℕ) : ℝ :=
  2 * ((collisionEdges r).card : ℝ) *
    (Real.exp
      ((((collisionEdges r).card : ℝ) *
          (2 * ((r + 1 : ℕ) : ℝ)) *
          (1 + 2 * ((r + 1 : ℕ) : ℝ)) ^ (collisionEdges r).card) *
        reciprocalSquareTail a) - 1)

noncomputable def singularTailError (r a : ℕ) : ℝ :=
  genericTailError r a * (1 + collisionTailError r a) +
    collisionTailError r a

theorem genericTailError_nonneg (r a : ℕ) :
    0 ≤ genericTailError r a := by
  unfold genericTailError
  exact mul_nonneg (by positivity) (reciprocalSquareTail_nonneg a)

theorem collisionTailError_nonneg (r a : ℕ) :
    0 ≤ collisionTailError r a := by
  unfold collisionTailError
  apply mul_nonneg (by positivity)
  apply sub_nonneg.mpr
  apply Real.one_le_exp
  exact mul_nonneg (by positivity) (reciprocalSquareTail_nonneg a)

theorem singularTailError_nonneg (r a : ℕ) :
    0 ≤ singularTailError r a := by
  unfold singularTailError
  exact add_nonneg
    (mul_nonneg (genericTailError_nonneg r a)
      (by linarith [collisionTailError_nonneg r a]))
    (collisionTailError_nonneg r a)

theorem tendsto_genericTailError_zero (r : ℕ) :
    Tendsto (genericTailError r) atTop (𝓝 0) := by
  unfold genericTailError
  simpa using tendsto_reciprocalSquareTail_zero.const_mul
    (((r + 1 : ℕ) : ℝ) ^ 2 * 2 ^ (r + 1))

theorem tendsto_collisionTailError_zero (r : ℕ) :
    Tendsto (collisionTailError r) atTop (𝓝 0) := by
  let B : ℝ := ((collisionEdges r).card : ℝ) *
    (2 * ((r + 1 : ℕ) : ℝ)) *
    (1 + 2 * ((r + 1 : ℕ) : ℝ)) ^ (collisionEdges r).card
  have hexp : Tendsto
      (fun a ↦ Real.exp (B * reciprocalSquareTail a) - 1)
      atTop (𝓝 0) := by
    have harg : Tendsto (fun a ↦ B * reciprocalSquareTail a)
        atTop (𝓝 0) := by
      simpa using tendsto_reciprocalSquareTail_zero.const_mul B
    have he := Real.continuous_exp.continuousAt.tendsto.comp harg
    simpa using he.sub_const 1
  unfold collisionTailError
  simpa [B] using hexp.const_mul (2 * ((collisionEdges r).card : ℝ))

theorem tendsto_singularTailError_zero (r : ℕ) :
    Tendsto (singularTailError r) atTop (𝓝 0) := by
  unfold singularTailError
  have hone : Tendsto (fun a ↦ 1 + collisionTailError r a)
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_collisionTailError_zero r)
  simpa using ((tendsto_genericTailError_zero r).mul hone).add
    (tendsto_collisionTailError_zero r)

theorem localMultiplicity_fin_zero (p : ℕ) (h : Fin 0 → ℕ) :
    localMultiplicity p h = 1 := by
  classical
  simp [localMultiplicity, shiftResidues]

theorem collisionSeriesSegment_fin_zero {a b : ℕ}
    (ha : 1 < nthPrime a) (h : Fin 0 → ℕ) :
    collisionSeriesSegment a b h = 1 := by
  unfold collisionSeriesSegment
  apply Finset.prod_eq_one
  intro i hi
  apply collisionMultiplier_eq_one h
  · exact ha.trans_le
      (nthPrime_strictMono.monotone (Finset.mem_Ico.mp hi).1)
  · exact localMultiplicity_fin_zero _ h

theorem sum_abs_singularSeriesSegment_sub_one_le {r a b m : ℕ}
    (ha : 2 * (r + 1) ≤ nthPrime a) :
    (∑ h ∈ distinctShiftTuples r m,
        |singularSeriesSegment a b h - 1|) ≤
      (m : ℝ) ^ r * singularTailError r a := by
  by_cases hr : r = 0
  · subst r
    have hG := genericSeriesSegment_bounds (r := 0) (b := b) ha
    have hGe := one_sub_genericSeriesSegment_le_tail
      (r := 0) (b := b) ha
    have hseg (h : Fin 0 → ℕ) :
        singularSeriesSegment a b h = genericSeriesSegment 0 a b := by
      rw [singularSeriesSegment_eq_generic_mul_collision
        (r := 0) (by omega) h, collisionSeriesSegment_fin_zero (by omega) h,
        mul_one]
    have hsum :
        (∑ h ∈ distinctShiftTuples 0 m,
          |singularSeriesSegment a b h - 1|) =
          1 - genericSeriesSegment 0 a b := by
      rw [show (∑ h ∈ distinctShiftTuples 0 m,
          |singularSeriesSegment a b h - 1|) =
          (distinctShiftTuples 0 m).card *
            |genericSeriesSegment 0 a b - 1| by
        simp_rw [hseg]
        simp [nsmul_eq_mul]]
      rw [card_distinctShiftTuples]
      simp only [Nat.descFactorial_zero, Nat.cast_one, one_mul]
      rw [abs_of_nonpos (sub_nonpos.mpr hG.2)]
      ring
    rw [hsum]
    simp only [Nat.cast_ofNat, pow_zero, one_mul]
    unfold singularTailError collisionTailError
    have hedge0 : collisionEdges 0 = ∅ := by
      ext e
      simp [collisionEdges]
    rw [hedge0]
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero,
      sub_self, add_zero, mul_one]
    exact hGe
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    let G := genericSeriesSegment r a b
    let X := ∑ h ∈ distinctShiftTuples r m,
      (collisionSeriesSegment a b h - 1)
    have hGb := genericSeriesSegment_bounds (r := r) (b := b) ha
    have hGerr : 1 - G ≤ genericTailError r a := by
      simpa [G, genericTailError] using
        one_sub_genericSeriesSegment_le_tail (r := r) (b := b) ha
    have hX0 : 0 ≤ X := by
      dsimp [X]
      exact Finset.sum_nonneg fun h hh ↦ sub_nonneg.mpr
        (one_le_collisionSeriesSegment ha h)
    have hX : X ≤ (m : ℝ) ^ r * collisionTailError r a := by
      simpa [X, collisionTailError] using
        sum_collisionSeriesSegment_sub_one_le_pow hrpos ha
    have hcard : ((distinctShiftTuples r m).card : ℝ) ≤ (m : ℝ) ^ r := by
      rw [card_distinctShiftTuples]
      exact_mod_cast Nat.descFactorial_le_pow m r
    have hpoint (h : Fin r → ℕ) (hh : h ∈ distinctShiftTuples r m) :
        |singularSeriesSegment a b h - 1| ≤
          genericTailError r a * collisionSeriesSegment a b h +
            (collisionSeriesSegment a b h - 1) := by
      rw [singularSeriesSegment_eq_generic_mul_collision (by omega) h]
      calc
        |G * collisionSeriesSegment a b h - 1| ≤
            (1 - G) * collisionSeriesSegment a b h +
              (collisionSeriesSegment a b h - 1) :=
          abs_mul_sub_one_le hGb.1 hGb.2
            (one_le_collisionSeriesSegment ha h)
        _ ≤ genericTailError r a * collisionSeriesSegment a b h +
              (collisionSeriesSegment a b h - 1) := by
          gcongr
          exact zero_le_one.trans (one_le_collisionSeriesSegment ha h)
    calc
      (∑ h ∈ distinctShiftTuples r m,
          |singularSeriesSegment a b h - 1|) ≤
          ∑ h ∈ distinctShiftTuples r m,
            (genericTailError r a * collisionSeriesSegment a b h +
              (collisionSeriesSegment a b h - 1)) :=
        Finset.sum_le_sum fun h hh ↦ hpoint h hh
      _ = genericTailError r a *
            (((distinctShiftTuples r m).card : ℝ) + X) + X := by
        dsimp [X]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
          mul_one]
        ring
      _ ≤ genericTailError r a *
            ((m : ℝ) ^ r + (m : ℝ) ^ r * collisionTailError r a) +
          (m : ℝ) ^ r * collisionTailError r a := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left
          · exact add_le_add hcard hX
          · exact genericTailError_nonneg r a
        · exact hX
      _ = (m : ℝ) ^ r * singularTailError r a := by
        unfold singularTailError
        ring

noncomputable def collisionPowerTailError (r q a : ℕ) : ℝ :=
  2 * ((collisionEdges r).card : ℝ) *
    (Real.exp
      ((((q * (collisionEdges r).card : ℕ) : ℝ) *
          (2 * ((r + 1 : ℕ) : ℝ)) *
          (1 + 2 * ((r + 1 : ℕ) : ℝ)) ^
            (q * (collisionEdges r).card)) *
        reciprocalSquareTail a) - 1)

theorem collisionPowerTailError_nonneg (r q a : ℕ) :
    0 ≤ collisionPowerTailError r q a := by
  unfold collisionPowerTailError
  apply mul_nonneg (by positivity)
  apply sub_nonneg.mpr
  apply Real.one_le_exp
  exact mul_nonneg (by positivity) (reciprocalSquareTail_nonneg a)

theorem tendsto_collisionPowerTailError_zero (r q : ℕ) :
    Tendsto (collisionPowerTailError r q) atTop (𝓝 0) := by
  let B : ℝ := (((q * (collisionEdges r).card : ℕ) : ℝ) *
    (2 * ((r + 1 : ℕ) : ℝ)) *
    (1 + 2 * ((r + 1 : ℕ) : ℝ)) ^ (q * (collisionEdges r).card))
  have harg : Tendsto (fun a ↦ B * reciprocalSquareTail a)
      atTop (𝓝 0) := by
    simpa using tendsto_reciprocalSquareTail_zero.const_mul B
  have he : Tendsto (fun a ↦ Real.exp (B * reciprocalSquareTail a) - 1)
      atTop (𝓝 0) := by
    simpa using
      (Real.continuous_exp.continuousAt.tendsto.comp harg).sub_const 1
  unfold collisionPowerTailError
  simpa [B] using he.const_mul (2 * ((collisionEdges r).card : ℝ))

theorem collisionSeriesSegment_pow_sub_one_le_edgeErrors {r q a b : ℕ}
    (hr : 0 < r) (ha : 2 * (r + 1) ≤ nthPrime a)
    (h : Fin r → ℕ) :
    (collisionSeriesSegment a b h) ^ q - 1 ≤
      ∑ e ∈ collisionEdges r,
        (divisorWeightPower (2 * ((r + 1 : ℕ) : ℝ))
          (q * (collisionEdges r).card) a b (collisionDifference h e) - 1) := by
  let A : ℝ := 2 * ((r + 1 : ℕ) : ℝ)
  let z := fun e ↦ divisorWeightPower A 1 a b (collisionDifference h e)
  have hz : ∀ e ∈ collisionEdges r, 1 ≤ (z e) ^ q := by
    intro e he
    exact one_le_pow₀ (one_le_divisorWeightPower (A := A) (by positivity) 1 a b _)
  have hC0 : 0 ≤ collisionSeriesSegment a b h :=
    zero_le_one.trans (one_le_collisionSeriesSegment ha h)
  have hprod0 : 0 ≤ ∏ e ∈ collisionEdges r, z e :=
    Finset.prod_nonneg fun e he ↦ zero_le_one.trans
      (one_le_divisorWeightPower (A := A) (by positivity) 1 a b _)
  calc
    (collisionSeriesSegment a b h) ^ q - 1 ≤
        (∏ e ∈ collisionEdges r, z e) ^ q - 1 := by
      apply sub_le_sub_right
      exact pow_le_pow_left₀ hC0 (by
        simpa [A, z] using collisionSeriesSegment_le_edgeWeights ha h) q
    _ = (∏ e ∈ collisionEdges r, (z e) ^ q) - 1 := by
      rw [Finset.prod_pow]
    _ ≤ ∑ e ∈ collisionEdges r,
        (((z e) ^ q) ^ (collisionEdges r).card - 1) :=
      prod_sub_one_le_sum_pow_sub_one _ (collisionEdges_nonempty hr)
        (fun e ↦ (z e) ^ q) hz
    _ = ∑ e ∈ collisionEdges r,
        (divisorWeightPower A (q * (collisionEdges r).card) a b
          (collisionDifference h e) - 1) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [← pow_mul, divisorWeightPower_one_pow]
    _ = _ := rfl

theorem sum_collisionSeriesSegment_pow_sub_one_le {r q a b m : ℕ}
    (hr : 0 < r) (ha : 2 * (r + 1) ≤ nthPrime a) :
    (∑ h ∈ distinctShiftTuples r m,
        ((collisionSeriesSegment a b h) ^ q - 1)) ≤
      (m : ℝ) ^ r * collisionPowerTailError r q a := by
  let A : ℝ := 2 * ((r + 1 : ℕ) : ℝ)
  let E : ℕ := q * (collisionEdges r).card
  let err : ℝ := Real.exp (((E : ℝ) * A * (1 + A) ^ E) *
    reciprocalSquareTail a) - 1
  have hedge (e : Fin (r + 1) × Fin (r + 1))
      (he : e ∈ collisionEdges r) :
      (∑ h ∈ distinctShiftTuples r m,
        (divisorWeightPower A E a b (collisionDifference h e) - 1)) ≤
          ((2 * m ^ (r - 1) : ℕ) : ℝ) * (m : ℝ) * err := by
    let W := fun n ↦ divisorWeightPower A E a b n - 1
    have hW (n : ℕ) : 0 ≤ W n :=
      sub_nonneg.mpr (one_le_divisorWeightPower (A := A) (by positivity) E a b n)
    calc
      (∑ h ∈ distinctShiftTuples r m,
          (divisorWeightPower A E a b (collisionDifference h e) - 1)) =
          ∑ h ∈ distinctShiftTuples r m, W (collisionDifference h e) := rfl
      _ ≤ ((2 * m ^ (r - 1) : ℕ) : ℝ) *
          ∑ n ∈ Finset.Icc 1 m, W n :=
        sum_distinct_edgeWeight_le hr he W hW
      _ ≤ ((2 * m ^ (r - 1) : ℕ) : ℝ) * ((m : ℝ) * err) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa [A, E, err, W] using
          sum_divisorWeightPower_sub_one_le (A := A) (by positivity) E a b m
      _ = ((2 * m ^ (r - 1) : ℕ) : ℝ) * (m : ℝ) * err := by ring
  have hsum :
      (∑ h ∈ distinctShiftTuples r m,
          ((collisionSeriesSegment a b h) ^ q - 1)) ≤
        ((collisionEdges r).card : ℝ) *
          ((2 * m ^ (r - 1) : ℕ) : ℝ) * (m : ℝ) * err := by
    calc
      (∑ h ∈ distinctShiftTuples r m,
          ((collisionSeriesSegment a b h) ^ q - 1)) ≤
          ∑ h ∈ distinctShiftTuples r m,
            ∑ e ∈ collisionEdges r,
              (divisorWeightPower A E a b (collisionDifference h e) - 1) := by
        exact Finset.sum_le_sum fun h hh ↦
          collisionSeriesSegment_pow_sub_one_le_edgeErrors hr ha h
      _ = ∑ e ∈ collisionEdges r,
          ∑ h ∈ distinctShiftTuples r m,
            (divisorWeightPower A E a b (collisionDifference h e) - 1) := by
        rw [Finset.sum_comm]
      _ ≤ ∑ _e ∈ collisionEdges r,
          (((2 * m ^ (r - 1) : ℕ) : ℝ) * (m : ℝ) * err) :=
        Finset.sum_le_sum fun e he ↦ hedge e he
      _ = ((collisionEdges r).card : ℝ) *
          ((2 * m ^ (r - 1) : ℕ) : ℝ) * (m : ℝ) * err := by
        simp [nsmul_eq_mul]
        ring
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hcoef :
      ((collisionEdges (s + 1)).card : ℝ) *
          ((2 * m ^ (s + 1 - 1) : ℕ) : ℝ) * (m : ℝ) =
        (m : ℝ) ^ (s + 1) * (2 * ((collisionEdges (s + 1)).card : ℝ)) := by
    simp only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
      pow_succ]
    ring
  rw [hcoef] at hsum
  simpa [collisionPowerTailError, A, E, err, mul_assoc] using hsum

noncomputable def singularTailSquareError (r a : ℕ) : ℝ :=
  2 * (genericTailError r a) ^ 2 *
      (1 + collisionPowerTailError r 2 a) +
    2 * collisionPowerTailError r 2 a

theorem singularTailSquareError_nonneg (r a : ℕ) :
    0 ≤ singularTailSquareError r a := by
  unfold singularTailSquareError
  exact add_nonneg
    (mul_nonneg (by positivity)
      (by linarith [collisionPowerTailError_nonneg r 2 a]))
    (mul_nonneg (by norm_num) (collisionPowerTailError_nonneg r 2 a))

theorem tendsto_singularTailSquareError_zero (r : ℕ) :
    Tendsto (singularTailSquareError r) atTop (𝓝 0) := by
  have hg2 : Tendsto (fun a ↦ (genericTailError r a) ^ 2)
      atTop (𝓝 0) := by
    simpa using (tendsto_genericTailError_zero r).pow 2
  have hc := tendsto_collisionPowerTailError_zero r 2
  have hone : Tendsto (fun a ↦ 1 + collisionPowerTailError r 2 a)
      atTop (𝓝 1) := by simpa using tendsto_const_nhds.add hc
  unfold singularTailSquareError
  simpa using (((hg2.const_mul 2).mul hone).add (hc.const_mul 2))

theorem sq_abs_mul_sub_one_le {G C : ℝ}
    (hG0 : 0 ≤ G) (hG1 : G ≤ 1) (hC : 1 ≤ C) :
    |G * C - 1| ^ 2 ≤
      2 * ((1 - G) ^ 2 * C ^ 2) + 2 * (C ^ 2 - 1) := by
  have ha : 0 ≤ (1 - G) * C :=
    mul_nonneg (sub_nonneg.mpr hG1) (zero_le_one.trans hC)
  have hb : 0 ≤ C - 1 := sub_nonneg.mpr hC
  have habs := abs_mul_sub_one_le hG0 hG1 hC
  have hsquare : |G * C - 1| ^ 2 ≤
      ((1 - G) * C + (C - 1)) ^ 2 := by
    exact (sq_le_sq₀ (abs_nonneg _) (add_nonneg ha hb)).2 habs
  have hcsq : (C - 1) ^ 2 ≤ C ^ 2 - 1 := by
    nlinarith
  calc
    |G * C - 1| ^ 2 ≤ ((1 - G) * C + (C - 1)) ^ 2 := hsquare
    _ ≤ 2 * (((1 - G) * C) ^ 2) + 2 * ((C - 1) ^ 2) := by
      nlinarith [sq_nonneg ((1 - G) * C - (C - 1))]
    _ ≤ 2 * ((1 - G) ^ 2 * C ^ 2) + 2 * (C ^ 2 - 1) := by
      rw [mul_pow]
      gcongr

theorem sum_sq_abs_singularSeriesSegment_sub_one_le {r a b m : ℕ}
    (ha : 2 * (r + 1) ≤ nthPrime a) :
    (∑ h ∈ distinctShiftTuples r m,
        |singularSeriesSegment a b h - 1| ^ 2) ≤
      (m : ℝ) ^ r * singularTailSquareError r a := by
  by_cases hr : r = 0
  · subst r
    have hG := genericSeriesSegment_bounds (r := 0) (b := b) ha
    have hGe : 1 - genericSeriesSegment 0 a b ≤ genericTailError 0 a := by
      simpa [genericTailError] using
        one_sub_genericSeriesSegment_le_tail (r := 0) (b := b) ha
    have hseg (h : Fin 0 → ℕ) :
        singularSeriesSegment a b h = genericSeriesSegment 0 a b := by
      rw [singularSeriesSegment_eq_generic_mul_collision
        (r := 0) (by omega) h, collisionSeriesSegment_fin_zero (by omega) h,
        mul_one]
    have hsum :
        (∑ h ∈ distinctShiftTuples 0 m,
          |singularSeriesSegment a b h - 1| ^ 2) =
          (1 - genericSeriesSegment 0 a b) ^ 2 := by
      simp_rw [hseg]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [card_distinctShiftTuples]
      simp only [Nat.descFactorial_zero, Nat.cast_one, one_mul]
      rw [abs_of_nonpos (sub_nonpos.mpr hG.2)]
      ring
    rw [hsum]
    simp only [pow_zero, one_mul]
    unfold singularTailSquareError collisionPowerTailError
    have hedge0 : collisionEdges 0 = ∅ := by
      ext e
      simp [collisionEdges]
    rw [hedge0]
    simp only [Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero,
      sub_self, add_zero, mul_one]
    have hs := (sq_le_sq₀ (sub_nonneg.mpr hG.2)
      (genericTailError_nonneg 0 a)).2 hGe
    nlinarith [sq_nonneg (genericTailError 0 a)]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    let G := genericSeriesSegment r a b
    let Y := ∑ h ∈ distinctShiftTuples r m,
      ((collisionSeriesSegment a b h) ^ 2 - 1)
    have hGb := genericSeriesSegment_bounds (r := r) (b := b) ha
    have hGerr : 1 - G ≤ genericTailError r a := by
      simpa [G, genericTailError] using
        one_sub_genericSeriesSegment_le_tail (r := r) (b := b) ha
    have hY0 : 0 ≤ Y := by
      dsimp [Y]
      exact Finset.sum_nonneg fun h hh ↦ sub_nonneg.mpr
        (one_le_pow₀ (one_le_collisionSeriesSegment ha h))
    have hY : Y ≤ (m : ℝ) ^ r * collisionPowerTailError r 2 a := by
      simpa [Y] using
        sum_collisionSeriesSegment_pow_sub_one_le (q := 2) hrpos ha
    have hcard : ((distinctShiftTuples r m).card : ℝ) ≤ (m : ℝ) ^ r := by
      rw [card_distinctShiftTuples]
      exact_mod_cast Nat.descFactorial_le_pow m r
    have hpoint (h : Fin r → ℕ) (hh : h ∈ distinctShiftTuples r m) :
        |singularSeriesSegment a b h - 1| ^ 2 ≤
          2 * (genericTailError r a) ^ 2 *
              (collisionSeriesSegment a b h) ^ 2 +
            2 * ((collisionSeriesSegment a b h) ^ 2 - 1) := by
      rw [singularSeriesSegment_eq_generic_mul_collision (by omega) h]
      calc
        |G * collisionSeriesSegment a b h - 1| ^ 2 ≤
            2 * ((1 - G) ^ 2 * (collisionSeriesSegment a b h) ^ 2) +
              2 * ((collisionSeriesSegment a b h) ^ 2 - 1) :=
          sq_abs_mul_sub_one_le hGb.1 hGb.2
            (one_le_collisionSeriesSegment ha h)
        _ ≤ 2 * (genericTailError r a) ^ 2 *
              (collisionSeriesSegment a b h) ^ 2 +
            2 * ((collisionSeriesSegment a b h) ^ 2 - 1) := by
          have hs : (1 - G) ^ 2 ≤ (genericTailError r a) ^ 2 :=
            (sq_le_sq₀ (sub_nonneg.mpr hGb.2)
              (genericTailError_nonneg r a)).2 hGerr
          have hm := mul_le_mul_of_nonneg_right hs
            (sq_nonneg (collisionSeriesSegment a b h))
          apply add_le_add
          · nlinarith
          · exact le_rfl
    calc
      (∑ h ∈ distinctShiftTuples r m,
          |singularSeriesSegment a b h - 1| ^ 2) ≤
          ∑ h ∈ distinctShiftTuples r m,
            (2 * (genericTailError r a) ^ 2 *
                (collisionSeriesSegment a b h) ^ 2 +
              2 * ((collisionSeriesSegment a b h) ^ 2 - 1)) :=
        Finset.sum_le_sum fun h hh ↦ hpoint h hh
      _ = 2 * (genericTailError r a) ^ 2 *
            (((distinctShiftTuples r m).card : ℝ) + Y) + 2 * Y := by
        dsimp [Y]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
          mul_one]
        ring
      _ ≤ 2 * (genericTailError r a) ^ 2 *
            ((m : ℝ) ^ r + (m : ℝ) ^ r * collisionPowerTailError r 2 a) +
          2 * ((m : ℝ) ^ r * collisionPowerTailError r 2 a) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left
          · exact add_le_add hcard hY
          · positivity
        · exact mul_le_mul_of_nonneg_left hY (by norm_num)
      _ = (m : ℝ) ^ r * singularTailSquareError r a := by
        unfold singularTailSquareError
        ring

theorem singularSeriesSegment_le_periodicBoxBound {r ℓ m : ℕ}
    {h : Fin r → ℕ} (hh : h ∈ shiftBox r m) :
    singularSeriesSegment 0 ℓ h ≤
      periodicBoxBound (primeProduct ℓ) (positiveShiftSeries r ℓ) := by
  let x : Fin r → ℕ := fun i ↦ h i - 1
  have hx : ∀ i, x i + 1 = h i := by
    intro i
    exact Nat.sub_add_cancel (mem_shiftBox.mp hh i).1
  have habs := abs_le_periodicBoxBound (primeProduct_pos ℓ)
    (positiveShiftSeries_periodic (r := r) (ℓ := ℓ)) x
  rw [abs_of_nonneg] at habs
  · simpa [positiveShiftSeries, hx] using habs
  · simpa [positiveShiftSeries, hx] using
      (singularSeriesSegment_nonneg (a := 0) (b := ℓ) h)

def secondMomentCutoff (r : ℕ) : ℕ := 2 * (r + 1)

theorem secondMomentCutoff_large (r : ℕ) :
    2 * (r + 1) ≤ nthPrime (secondMomentCutoff r) := by
  exact (show 2 * (r + 1) ≤ 2 * (r + 1) + 2 by omega).trans
    (add_two_le_nthPrime (secondMomentCutoff r))

noncomputable def singularSecondMomentBound (r : ℕ) : ℝ :=
  2 * (periodicBoxBound (primeProduct (secondMomentCutoff r))
      (positiveShiftSeries r (secondMomentCutoff r))) ^ 2 *
    (singularTailSquareError r (secondMomentCutoff r) + 1)

theorem singularSecondMomentBound_nonneg (r : ℕ) :
    0 ≤ singularSecondMomentBound r := by
  unfold singularSecondMomentBound
  exact mul_nonneg (by positivity)
    (by linarith [singularTailSquareError_nonneg r (secondMomentCutoff r)])

theorem sum_sq_singularSeriesSegment_le {r b m : ℕ}
    (hb : secondMomentCutoff r ≤ b) :
    (∑ h ∈ distinctShiftTuples r m,
        (singularSeriesSegment 0 b h) ^ 2) ≤
      (m : ℝ) ^ r * singularSecondMomentBound r := by
  let a₀ := secondMomentCutoff r
  let B := periodicBoxBound (primeProduct a₀) (positiveShiftSeries r a₀)
  have hB0 : 0 ≤ B := by
    dsimp [B, periodicBoxBound]
    exact Finset.sum_nonneg fun x hx ↦ abs_nonneg _
  have htail := sum_sq_abs_singularSeriesSegment_sub_one_le
    (r := r) (a := a₀) (b := b) (m := m) (secondMomentCutoff_large r)
  have hpoint (h : Fin r → ℕ) (hh : h ∈ distinctShiftTuples r m) :
      (singularSeriesSegment 0 b h) ^ 2 ≤
        B ^ 2 * (2 * |singularSeriesSegment a₀ b h - 1| ^ 2 + 2) := by
    have hsmall0 := singularSeriesSegment_nonneg (a := 0) (b := a₀) h
    have hsmallB := singularSeriesSegment_le_periodicBoxBound
      (ℓ := a₀) (m := m)
      (mem_shiftBox.mpr (mem_distinctShiftTuples.mp hh).1)
    have htail0 := singularSeriesSegment_nonneg (a := a₀) (b := b) h
    rw [singularSeriesSegment_split (a := 0) (b := a₀) (c := b)
      (Nat.zero_le _) hb h, mul_pow]
    have hsmallSq : (singularSeriesSegment 0 a₀ h) ^ 2 ≤ B ^ 2 :=
      (sq_le_sq₀ hsmall0 hB0).2 hsmallB
    have htailSq : (singularSeriesSegment a₀ b h) ^ 2 ≤
        2 * |singularSeriesSegment a₀ b h - 1| ^ 2 + 2 := by
      rw [sq_abs]
      nlinarith [sq_nonneg (singularSeriesSegment a₀ b h - 2)]
    exact mul_le_mul hsmallSq htailSq (sq_nonneg _) (sq_nonneg _)
  calc
    (∑ h ∈ distinctShiftTuples r m,
        (singularSeriesSegment 0 b h) ^ 2) ≤
        ∑ h ∈ distinctShiftTuples r m,
          B ^ 2 * (2 * |singularSeriesSegment a₀ b h - 1| ^ 2 + 2) :=
      Finset.sum_le_sum fun h hh ↦ hpoint h hh
    _ = B ^ 2 *
        (2 * (∑ h ∈ distinctShiftTuples r m,
          |singularSeriesSegment a₀ b h - 1| ^ 2) +
          2 * ((distinctShiftTuples r m).card : ℝ)) := by
      rw [← Finset.mul_sum]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        nsmul_eq_mul]
      ring
    _ ≤ B ^ 2 *
        (2 * ((m : ℝ) ^ r * singularTailSquareError r a₀) +
          2 * (m : ℝ) ^ r) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left htail (by norm_num)
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [card_distinctShiftTuples]
        exact_mod_cast Nat.descFactorial_le_pow m r
    _ = (m : ℝ) ^ r * singularSecondMomentBound r := by
      unfold singularSecondMomentBound
      dsimp [a₀, B]
      ring

/-! ### Gallagher's mean singular-series theorem -/

/-- The error in replacing the full singular series by its first `a` Euler
factors.  The preceding two second-moment estimates make this error uniform
in both the box length and the upper prime cutoff. -/
noncomputable def singularMeanTailBound (r a : ℕ) : ℝ :=
  Real.sqrt (singularSecondMomentBound r * singularTailSquareError r a)

theorem singularMeanTailBound_nonneg (r a : ℕ) :
    0 ≤ singularMeanTailBound r a := Real.sqrt_nonneg _

theorem tendsto_singularMeanTailBound_zero (r : ℕ) :
    Tendsto (singularMeanTailBound r) atTop (𝓝 0) := by
  unfold singularMeanTailBound
  have hmul : Tendsto
      (fun a ↦ singularSecondMomentBound r * singularTailSquareError r a)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (tendsto_singularTailSquareError_zero r))
  change Tendsto
    (fun a ↦ Real.sqrt
      (singularSecondMomentBound r * singularTailSquareError r a))
    atTop (𝓝 0)
  convert (Real.continuous_sqrt.tendsto 0).comp hmul using 1 <;>
    simp [Function.comp_def]

/-- Cauchy--Schwarz comparison between a singular-series mean and its
small-prime truncation. -/
theorem abs_segmentMean_sub_smallMean_le {r a b m : ℕ}
    (hm : 0 < m) (ha : secondMomentCutoff r ≤ a)
    (hab : a ≤ b) (hlarge : 2 * (r + 1) ≤ nthPrime a) :
    |(∑ h ∈ distinctShiftTuples r m, singularSeriesSegment 0 b h) /
          (m : ℝ) ^ r -
        (∑ h ∈ distinctShiftTuples r m, singularSeriesSegment 0 a h) /
          (m : ℝ) ^ r| ≤ singularMeanTailBound r a := by
  let P : ℝ := (m : ℝ) ^ r
  let S : ℝ := ∑ h ∈ distinctShiftTuples r m,
    singularSeriesSegment 0 a h * (singularSeriesSegment a b h - 1)
  have hP : 0 < P := by dsimp [P]; positivity
  have hdiff :
      (∑ h ∈ distinctShiftTuples r m, singularSeriesSegment 0 b h) -
          ∑ h ∈ distinctShiftTuples r m, singularSeriesSegment 0 a h = S := by
    dsimp [S]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro h hh
    rw [singularSeriesSegment_split (a := 0) (b := a) (c := b)
      (Nat.zero_le _) hab h]
    ring
  have habs : |S| ≤ ∑ h ∈ distinctShiftTuples r m,
      singularSeriesSegment 0 a h * |singularSeriesSegment a b h - 1| := by
    calc
      |S| ≤ ∑ h ∈ distinctShiftTuples r m,
          |singularSeriesSegment 0 a h *
            (singularSeriesSegment a b h - 1)| := by
        dsimp [S]
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ h ∈ distinctShiftTuples r m,
          singularSeriesSegment 0 a h *
            |singularSeriesSegment a b h - 1| := by
        apply Finset.sum_congr rfl
        intro h hh
        rw [abs_mul, abs_of_nonneg (singularSeriesSegment_nonneg h)]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq
    (distinctShiftTuples r m)
    (fun h ↦ singularSeriesSegment 0 a h)
    (fun h ↦ |singularSeriesSegment a b h - 1|)
  have hsmall := sum_sq_singularSeriesSegment_le
    (r := r) (b := a) (m := m) ha
  have htail := sum_sq_abs_singularSeriesSegment_sub_one_le
    (r := r) (a := a) (b := b) (m := m) hlarge
  have hsum0 : 0 ≤ ∑ h ∈ distinctShiftTuples r m,
      singularSeriesSegment 0 a h * |singularSeriesSegment a b h - 1| :=
    Finset.sum_nonneg fun h hh ↦ mul_nonneg
      (singularSeriesSegment_nonneg h) (abs_nonneg _)
  have hSsq : |S| ^ 2 ≤
      P ^ 2 * (singularSecondMomentBound r * singularTailSquareError r a) := by
    have habssq := (sq_le_sq₀ (abs_nonneg S) hsum0).2 habs
    calc
      |S| ^ 2 ≤
          (∑ h ∈ distinctShiftTuples r m,
            singularSeriesSegment 0 a h *
              |singularSeriesSegment a b h - 1|) ^ 2 := habssq
      _ ≤ (∑ h ∈ distinctShiftTuples r m,
              (singularSeriesSegment 0 a h) ^ 2) *
            ∑ h ∈ distinctShiftTuples r m,
              |singularSeriesSegment a b h - 1| ^ 2 := hCS
      _ ≤ (P * singularSecondMomentBound r) *
            (P * singularTailSquareError r a) := by
        exact mul_le_mul hsmall htail
          (Finset.sum_nonneg fun h hh ↦ sq_nonneg _)
          (mul_nonneg hP.le (singularSecondMomentBound_nonneg r))
      _ = P ^ 2 *
          (singularSecondMomentBound r * singularTailSquareError r a) := by ring
  have hnormsq : |S / P| ^ 2 ≤
      singularSecondMomentBound r * singularTailSquareError r a := by
    rw [abs_div, abs_of_pos hP, div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hP)).2
    simpa [mul_comm] using hSsq
  rw [← sub_div, hdiff]
  exact Real.le_sqrt_of_sq_le hnormsq

/-- Gallagher's theorem in the diagonal form used below: the mean singular
series tends to one whenever both the prime cutoff and the shift box tend to
infinity. -/
theorem tendsto_singularSeriesMean_one {ι : Type*} {l : Filter ι}
    (r : ℕ) {k m : ι → ℕ}
    (hk : Tendsto k l atTop) (hm : Tendsto m l atTop) :
    Tendsto (fun x ↦ singularSeriesMean r (k x) (m x)) l (𝓝 1) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have htailMetric := (Metric.tendsto_atTop.mp
    (tendsto_singularMeanTailBound_zero r)) (ε / 2) (by positivity)
  obtain ⟨A₀, hA₀⟩ := htailMetric
  let A := max A₀ (secondMomentCutoff r)
  have hAtail : singularMeanTailBound r A < ε / 2 := by
    simpa [Real.dist_eq, abs_of_nonneg (singularMeanTailBound_nonneg r A)]
      using hA₀ A (le_max_left _ _)
  have hAcuto : secondMomentCutoff r ≤ A := le_max_right _ _
  have hAlarge : 2 * (r + 1) ≤ nthPrime A := by
    exact hAcuto.trans ((show A ≤ A + 2 by omega).trans
      (add_two_le_nthPrime A))
  have hsmall := (Metric.tendsto_nhds.mp
    ((tendsto_smallSeriesMean_distinct r A).comp hm))
      (ε / 2) (by positivity)
  have hkA : ∀ᶠ x in l, A ≤ k x := (tendsto_atTop.1 hk) A
  have hm1 : ∀ᶠ x in l, 1 ≤ m x := (tendsto_atTop.1 hm) 1
  filter_upwards [hsmall, hkA, hm1] with x hxsmall hxk hxm
  have hcompare := abs_segmentMean_sub_smallMean_le
    (r := r) (a := A) (b := k x) (m := m x) hxm hAcuto hxk hAlarge
  rw [Real.dist_eq]
  have htri := abs_sub_le
    (singularSeriesMean r (k x) (m x))
    ((∑ h ∈ distinctShiftTuples r (m x), singularSeriesSegment 0 A h) /
      (m x : ℝ) ^ r) 1
  have hcompare' :
      |singularSeriesMean r (k x) (m x) -
        (∑ h ∈ distinctShiftTuples r (m x), singularSeriesSegment 0 A h) /
          (m x : ℝ) ^ r| < ε / 2 := by
    unfold singularSeriesMean
    simp_rw [indexedSingularSeries_eq_segment]
    exact hcompare.trans_lt hAtail
  rw [Real.dist_eq] at hxsmall
  calc
    |singularSeriesMean r (k x) (m x) - 1| ≤
        |singularSeriesMean r (k x) (m x) -
          (∑ h ∈ distinctShiftTuples r (m x), singularSeriesSegment 0 A h) /
            (m x : ℝ) ^ r| +
        |(∑ h ∈ distinctShiftTuples r (m x), singularSeriesSegment 0 A h) /
            (m x : ℝ) ^ r - 1| := htri
    _ < ε / 2 + ε / 2 := add_lt_add hcompare' hxsmall
    _ = ε := by ring

/-! ## Factorial moments of the cyclic count -/

/-- The successful positive shifts from a fixed cyclic starting residue. -/
noncomputable def cyclicSuccessfulShifts (N m : ℕ) [NeZero N]
    (a : ZMod N) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 m).filter fun h : ℕ ↦
    IsUnit (a + (h : ZMod N))

theorem card_cyclicSuccessfulShifts (N m : ℕ) [NeZero N]
    (a : ZMod N) :
    (cyclicSuccessfulShifts N m a).card = cyclicLocalCount N m a := by
  rfl

/-- Ordered injective tuples of successful shifts from `a`. -/
noncomputable def cyclicOrderedSuccesses (N m r : ℕ) [NeZero N]
    (a : ZMod N) : Finset (Fin r → ℕ) := by
  classical
  exact (distinctShiftTuples r m).filter fun h ↦
    ∀ i, IsUnit (a + (h i : ZMod N))

noncomputable def cyclicOrderedSuccessesEquivEmbedding
    (N m r : ℕ) [NeZero N] (a : ZMod N) :
    {h : Fin r → ℕ // h ∈ cyclicOrderedSuccesses N m r a} ≃
      (Fin r ↪ ↥(cyclicSuccessfulShifts N m a)) where
  toFun h :=
    { toFun := fun i ↦ ⟨h.1 i, by
          have hm := (mem_distinctShiftTuples.mp
            (Finset.mem_filter.mp h.2).1).1 i
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr hm, (Finset.mem_filter.mp h.2).2 i⟩⟩
      inj' := by
        intro i j hij
        exact (mem_distinctShiftTuples.mp
          (Finset.mem_filter.mp h.2).1).2 (congrArg Subtype.val hij) }
  invFun e :=
    ⟨fun i ↦ e i, Finset.mem_filter.mpr
      ⟨mem_distinctShiftTuples.mpr
        ⟨fun i ↦ (Finset.mem_filter.mp (e i).2).1 |> Finset.mem_Icc.mp,
          fun i j hij ↦ e.injective (Subtype.ext hij)⟩,
        fun i ↦ (Finset.mem_filter.mp (e i).2).2⟩⟩
  left_inv h := by apply Subtype.ext; rfl
  right_inv e := by ext i; rfl

theorem card_cyclicOrderedSuccesses (N m r : ℕ) [NeZero N]
    (a : ZMod N) :
    (cyclicOrderedSuccesses N m r a).card =
      (cyclicLocalCount N m a).descFactorial r := by
  classical
  calc
    (cyclicOrderedSuccesses N m r a).card =
        Fintype.card {h : Fin r → ℕ //
          h ∈ cyclicOrderedSuccesses N m r a} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card (Fin r ↪ ↥(cyclicSuccessfulShifts N m a)) :=
      Fintype.card_congr (cyclicOrderedSuccessesEquivEmbedding N m r a)
    _ = (cyclicLocalCount N m a).descFactorial r := by
      rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe,
        card_cyclicSuccessfulShifts]

theorem card_cyclicOrderedSuccesses_eq_sum_indicator
    (N m r : ℕ) [NeZero N] (a : ZMod N) :
    (cyclicOrderedSuccesses N m r a).card =
      ∑ h ∈ distinctShiftTuples r m,
        if ∀ i, IsUnit (a + (h i : ZMod N)) then 1 else 0 := by
  classical
  unfold cyclicOrderedSuccesses
  rw [Finset.card_filter]

theorem sum_descFactorial_cyclicLocalCount (k m r : ℕ) :
    ∑ a ∈ cyclicReducedResidues (primeProduct k),
        (cyclicLocalCount (primeProduct k) m a).descFactorial r =
      ∑ h ∈ distinctShiftTuples r m, (jointReducedResidues k h).card := by
  classical
  simp_rw [← card_cyclicOrderedSuccesses]
  simp_rw [card_cyclicOrderedSuccesses_eq_sum_indicator]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← Finset.card_filter]
  congr 1
  ext a
  simp [jointReducedResidues]

/-- The normalized falling-factorial moment of the cyclic local count. -/
noncomputable def cyclicFactorialMoment (k m r : ℕ) : ℝ :=
  (∑ a ∈ cyclicReducedResidues (primeProduct k),
      (cyclicLocalCount (primeProduct k) m a).descFactorial r : ℕ) /
    ((primeProduct k).totient : ℝ)

/-- Exact factorial-moment formula obtained from CRT correlations. -/
theorem cyclicFactorialMoment_eq (k m r : ℕ) :
    cyclicFactorialMoment k m r =
      ((m : ℝ) * primorialDensity k) ^ r * singularSeriesMean r k m := by
  unfold cyclicFactorialMoment singularSeriesMean
  rw [sum_descFactorial_cyclicLocalCount]
  push_cast
  have hφ0 : ((primeProduct k).totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (primeProduct_pos k)).ne'
  rw [Finset.sum_div]
  simp_rw [jointReduced_ratio_eq_density_mul_series]
  rw [← Finset.mul_sum]
  by_cases hm : m = 0
  · subst m
    cases r <;> simp [distinctShiftTuples, shiftBox]
  · have hmR : (m : ℝ) ^ r ≠ 0 := pow_ne_zero r (by exact_mod_cast hm)
    field_simp
    ring

/-- At the Erdős--Hooley scaling, every fixed falling-factorial moment
converges to the corresponding Poisson moment. -/
theorem tendsto_cyclicFactorialMoment (c : ℝ) (hc : 0 < c) (r : ℕ) :
    Tendsto
      (fun k ↦ cyclicFactorialMoment k
        (normalizedThreshold (primeProduct k) c) r)
      atTop (𝓝 (c ^ r)) := by
  have hscale := (tendsto_scaledThreshold_mul_density c hc.le).pow r
  have hseries := tendsto_singularSeriesMean_one r
    (k := fun k : ℕ ↦ k)
    (m := fun k ↦ normalizedThreshold (primeProduct k) c)
    tendsto_id (tendsto_normalizedThreshold_atTop c hc)
  have hmul := hscale.mul hseries
  convert hmul using 1
  · funext k
    exact cyclicFactorialMoment_eq k
      (normalizedThreshold (primeProduct k) c) r
  · simp

/-! ## Bonferroni squeeze and the cyclic void probability -/

/-- Real-valued finite exponential series.  Its value at `-c` is the
Poisson void probability in the limit. -/
noncomputable def poissonPartial (n : ℕ) (c : ℝ) : ℝ :=
  ∑ r ∈ Finset.range n, (-1 : ℝ) ^ r * c ^ r / (r.factorial : ℝ)

/-- Average of the integral Brun truncation over reduced starting classes. -/
noncomputable def cyclicBrunAverage (k m L : ℕ) : ℝ :=
  (∑ a ∈ cyclicReducedResidues (primeProduct k),
      (Erdos387.brunTruncation L
        (cyclicLocalCount (primeProduct k) m a) : ℝ)) /
    ((primeProduct k).totient : ℝ)

theorem cast_brunTruncation_eq_descFactorial (L n : ℕ) :
    (Erdos387.brunTruncation L n : ℝ) =
      ∑ r ∈ Finset.range (L + 1),
        (-1 : ℝ) ^ r * (n.descFactorial r : ℝ) /
          (r.factorial : ℝ) := by
  classical
  unfold Erdos387.brunTruncation
  push_cast
  apply Finset.sum_congr rfl
  intro r hr
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hf : (r.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem cyclicBrunAverage_eq_factorialMoments (k m L : ℕ) :
    cyclicBrunAverage k m L =
      ∑ r ∈ Finset.range (L + 1),
        (-1 : ℝ) ^ r / (r.factorial : ℝ) *
          cyclicFactorialMoment k m r := by
  classical
  unfold cyclicBrunAverage cyclicFactorialMoment
  simp_rw [cast_brunTruncation_eq_descFactorial]
  rw [Finset.sum_div]
  simp_rw [Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.sum_div]
  push_cast
  have hfactor :
      (∑ x ∈ cyclicReducedResidues (primeProduct k),
        (-1 : ℝ) ^ r *
          ((cyclicLocalCount (primeProduct k) m x).descFactorial r : ℝ) /
            (r.factorial : ℝ)) =
        (-1 : ℝ) ^ r / (r.factorial : ℝ) *
          ∑ x ∈ cyclicReducedResidues (primeProduct k),
            ((cyclicLocalCount (primeProduct k) m x).descFactorial r : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hfactor]
  ring

theorem tendsto_cyclicBrunAverage (c : ℝ) (hc : 0 < c) (L : ℕ) :
    Tendsto
      (fun k ↦ cyclicBrunAverage k
        (normalizedThreshold (primeProduct k) c) L)
      atTop (𝓝 (poissonPartial (L + 1) c)) := by
  rw [show (fun k ↦ cyclicBrunAverage k
      (normalizedThreshold (primeProduct k) c) L) =
      fun k ↦ ∑ r ∈ Finset.range (L + 1),
        (-1 : ℝ) ^ r / (r.factorial : ℝ) *
          cyclicFactorialMoment k
            (normalizedThreshold (primeProduct k) c) r by
    funext k
    exact cyclicBrunAverage_eq_factorialMoments _ _ _]
  have hsum : Tendsto
      (fun k ↦ ∑ r ∈ Finset.range (L + 1),
        (-1 : ℝ) ^ r / (r.factorial : ℝ) *
          cyclicFactorialMoment k
            (normalizedThreshold (primeProduct k) c) r)
      atTop (𝓝 (∑ r ∈ Finset.range (L + 1),
        (-1 : ℝ) ^ r / (r.factorial : ℝ) * c ^ r)) := by
    apply tendsto_finsetSum
    intro r hr
    exact tendsto_const_nhds.mul (tendsto_cyclicFactorialMoment c hc r)
  convert hsum using 1
  unfold poissonPartial
  apply congrArg
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem tendsto_poissonPartial (c : ℝ) :
    Tendsto (fun n ↦ poissonPartial n c) atTop (𝓝 (Real.exp (-c))) := by
  have hsum := (NormedSpace.expSeries_div_hasSum_exp (-c : ℝ)).tendsto_sum_nat
  convert hsum using 1
  · funext n
    unfold poissonPartial
    apply Finset.sum_congr rfl
    intro r hr
    rw [neg_pow]
    ring
  · rw [Real.exp_eq_exp_ℝ]

theorem cyclicBrunAverage_le_void {k m L : ℕ} (hL : Odd L) :
    cyclicBrunAverage k m L ≤ cyclicVoidRatio (primeProduct k) m := by
  have hφ : (0 : ℝ) < (primeProduct k).totient := by
    exact_mod_cast Nat.totient_pos.mpr (primeProduct_pos k)
  apply (div_le_div_iff_of_pos_right hφ).2
  unfold cyclicVoidStarts
  push_cast
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_le_sum
  intro a ha
  exact_mod_cast Erdos387.brunTruncation_le_zeroIndicator
    (m := cyclicLocalCount (primeProduct k) m a) hL

theorem cyclicVoid_le_brunAverage {k m L : ℕ} (hL : Even L) :
    cyclicVoidRatio (primeProduct k) m ≤ cyclicBrunAverage k m L := by
  have hφ : (0 : ℝ) < (primeProduct k).totient := by
    exact_mod_cast Nat.totient_pos.mpr (primeProduct_pos k)
  apply (div_le_div_iff_of_pos_right hφ).2
  unfold cyclicVoidStarts
  push_cast
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_le_sum
  intro a ha
  exact_mod_cast Erdos387.zeroIndicator_le_brunTruncation
    (m := cyclicLocalCount (primeProduct k) m a) hL

/-- Hooley's cyclic void-probability limit for positive scaling parameter. -/
theorem tendsto_cyclicVoidRatio (c : ℝ) (hc : 0 < c) :
    Tendsto
      (fun k ↦ cyclicVoidRatio (primeProduct k)
        (normalizedThreshold (primeProduct k) c))
      atTop (𝓝 (Real.exp (-c))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp
    (tendsto_poissonPartial c)) (ε / 2) (by positivity)
  let Le : ℕ := 2 * N
  let Lo : ℕ := 2 * N + 1
  have hLe : Even Le := by
    refine ⟨N, ?_⟩
    dsimp [Le]
    omega
  have hLo : Odd Lo := by
    refine ⟨N, ?_⟩
    dsimp [Lo]
  have hpartialEven :
      dist (poissonPartial (Le + 1) c) (Real.exp (-c)) < ε / 2 :=
    hN (Le + 1) (by dsimp [Le]; omega)
  have hpartialOdd :
      dist (poissonPartial (Lo + 1) c) (Real.exp (-c)) < ε / 2 :=
    hN (Lo + 1) (by dsimp [Lo]; omega)
  have hupper := (Metric.tendsto_nhds.mp
    (tendsto_cyclicBrunAverage c hc Le)) (ε / 2) (by positivity)
  have hlower := (Metric.tendsto_nhds.mp
    (tendsto_cyclicBrunAverage c hc Lo)) (ε / 2) (by positivity)
  filter_upwards [hupper, hlower] with k hkupper hklower
  let m := normalizedThreshold (primeProduct k) c
  let V := cyclicVoidRatio (primeProduct k) m
  let U := cyclicBrunAverage k m Le
  let D := cyclicBrunAverage k m Lo
  let E := Real.exp (-c)
  have hDU : D ≤ V := cyclicBrunAverage_le_void hLo
  have hVU : V ≤ U := cyclicVoid_le_brunAverage hLe
  have hUE : |U - E| < ε := by
    calc
      |U - E| ≤ |U - poissonPartial (Le + 1) c| +
          |poissonPartial (Le + 1) c - E| := abs_sub_le _ _ _
      _ < ε / 2 + ε / 2 := by
        apply add_lt_add
        · simpa [U, m, Real.dist_eq] using hkupper
        · simpa [E, Real.dist_eq] using hpartialEven
      _ = ε := by ring
  have hDE : |D - E| < ε := by
    calc
      |D - E| ≤ |D - poissonPartial (Lo + 1) c| +
          |poissonPartial (Lo + 1) c - E| := abs_sub_le _ _ _
      _ < ε / 2 + ε / 2 := by
        apply add_lt_add
        · simpa [D, m, Real.dist_eq] using hklower
        · simpa [E, Real.dist_eq] using hpartialOdd
      _ = ε := by ring
  rw [Real.dist_eq, abs_lt]
  rw [abs_lt] at hUE hDE
  constructor <;> dsimp [V, E, U, D] at * <;> linarith

/-- `a` and `b` are successive elements of the increasing list of reduced
residues below `N`. -/
def IsInternalConsecutive (N a b : ℕ) : Prop :=
  a < b ∧ b < N ∧ a.Coprime N ∧ b.Coprime N ∧
    ∀ t, a < t → t < b → ¬t.Coprime N

/-- The internal consecutive reduced-residue pairs whose gap is at most
`T`. -/
noncomputable def internalShortGaps (N T : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range N).product (Finset.range N)).filter fun ab ↦
    IsInternalConsecutive N ab.1 ab.2 ∧ ab.2 - ab.1 ≤ T

@[simp] theorem mem_internalShortGaps {N T a b : ℕ} :
    (a, b) ∈ internalShortGaps N T ↔
      IsInternalConsecutive N a b ∧ b - a ≤ T := by
  classical
  simp only [internalShortGaps, Finset.mem_filter]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro h
    refine ⟨?_, h⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (h.1.1.trans h.1.2.1),
        Finset.mem_range.mpr h.1.2.1⟩

/-- Reduced starting integers which have a later reduced integer within
distance `T`. -/
noncomputable def linearShortStarts (N T : ℕ) : Finset ℕ := by
  classical
  exact (reducedResidues N).filter fun a ↦
    ∃ b, a < b ∧ b < N ∧ b.Coprime N ∧ b - a ≤ T

@[simp] theorem mem_linearShortStarts {N T a : ℕ} :
    a ∈ linearShortStarts N T ↔
      a < N ∧ a.Coprime N ∧
        ∃ b, a < b ∧ b < N ∧ b.Coprime N ∧ b - a ≤ T := by
  classical
  unfold linearShortStarts
  simp only [Finset.mem_filter, mem_reducedResidues]
  constructor
  · rintro ⟨⟨haN, haC⟩, hb⟩
    exact ⟨haN, haC, hb⟩
  · rintro ⟨haN, haC, hb⟩
    exact ⟨⟨haN, haC⟩, hb⟩

/-- Choosing the least later reduced integer is a bijection between short
internal gaps and their starting integers. -/
theorem card_internalShortGaps_eq_linearShortStarts (N T : ℕ) :
    (internalShortGaps N T).card = (linearShortStarts N T).card := by
  classical
  apply Finset.card_bij (fun ab _ ↦ ab.1)
  · rintro ⟨a, b⟩ hab
    rw [mem_internalShortGaps] at hab
    exact mem_linearShortStarts.mpr
      ⟨hab.1.1.trans hab.1.2.1, hab.1.2.2.1,
        ⟨b, hab.1.1, hab.1.2.1, hab.1.2.2.2.1, hab.2⟩⟩
  · rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' haa
    simp only at haa
    subst a'
    rw [mem_internalShortGaps] at hab hab'
    have hbeq : b = b' := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hbb' | hb'b
      · exact hab'.1.2.2.2.2 b hab.1.1 hbb' hab.1.2.2.2.1
      · exact hab.1.2.2.2.2 b' hab'.1.1 hb'b hab'.1.2.2.2.1
    rw [hbeq]
  · intro a ha
    rw [mem_linearShortStarts] at ha
    let P : ℕ → Prop := fun b ↦
      a < b ∧ b < N ∧ b.Coprime N ∧ b - a ≤ T
    have hex : ∃ b, P b := ha.2.2
    let b := Nat.find hex
    have hb : P b := Nat.find_spec hex
    refine ⟨(a, b), ?_, rfl⟩
    rw [mem_internalShortGaps]
    refine ⟨⟨hb.1, hb.2.1, ha.2.1, hb.2.2.1, ?_⟩, hb.2.2.2⟩
    intro t hat htb htcop
    have htP : P t := by
      refine ⟨hat, ?_, htcop, ?_⟩
      · exact htb.trans hb.2.1
      · omega
    have hmin : b ≤ t := Nat.find_min' hex htP
    omega

/-- Cyclic starting residues whose first `T` positive shifts contain a
reduced class. -/
noncomputable def cyclicShortStarts (N T : ℕ) [NeZero N] :
    Finset (ZMod N) := by
  classical
  exact (cyclicReducedResidues N).filter fun a ↦
    cyclicLocalCount N T a ≠ 0

@[simp] theorem mem_cyclicShortStarts {N T : ℕ} [NeZero N]
    {a : ZMod N} :
    a ∈ cyclicShortStarts N T ↔
      IsUnit a ∧ cyclicLocalCount N T a ≠ 0 := by
  classical
  simp [cyclicShortStarts]

/-- The same cyclic starts, represented by their standard natural values. -/
noncomputable def natCyclicShortStarts (N T : ℕ) [NeZero N] : Finset ℕ := by
  classical
  exact (Finset.range N).filter fun a ↦
    a.Coprime N ∧ cyclicLocalCount N T (a : ZMod N) ≠ 0

@[simp] theorem mem_natCyclicShortStarts {N T a : ℕ} [NeZero N] :
    a ∈ natCyclicShortStarts N T ↔
      a < N ∧ a.Coprime N ∧
        cyclicLocalCount N T (a : ZMod N) ≠ 0 := by
  classical
  simp [natCyclicShortStarts]

theorem card_cyclicShortStarts_eq_nat (N T : ℕ) [NeZero N] :
    (cyclicShortStarts N T).card = (natCyclicShortStarts N T).card := by
  classical
  apply Finset.card_bij (fun a _ ↦ a.val)
  · intro a ha
    rw [mem_cyclicShortStarts] at ha
    rw [mem_natCyclicShortStarts]
    refine ⟨a.val_lt, ?_, ?_⟩
    · exact (ZMod.isUnit_iff_coprime a.val N).mp
        (by simpa only [ZMod.natCast_zmod_val] using ha.1)
    · simpa only [ZMod.natCast_zmod_val] using ha.2
  · intro a ha b hb hab
    exact ZMod.val_injective N hab
  · intro a ha
    rw [mem_natCyclicShortStarts] at ha
    refine ⟨(a : ZMod N), ?_, ?_⟩
    · rw [mem_cyclicShortStarts]
      exact ⟨(ZMod.isUnit_iff_coprime a N).mpr ha.2.1, ha.2.2⟩
    · exact ZMod.val_natCast_of_lt ha.1

theorem linearShortStarts_subset_natCyclicShortStarts {N T : ℕ}
    [NeZero N] :
    linearShortStarts N T ⊆ natCyclicShortStarts N T := by
  intro a ha
  rw [mem_linearShortStarts] at ha
  rw [mem_natCyclicShortStarts]
  refine ⟨ha.1, ha.2.1, ?_⟩
  obtain ⟨b, hab, hbN, hbC, hgap⟩ := ha.2.2
  apply Finset.card_ne_zero.mpr
  refine ⟨b - a, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ?_, ?_⟩⟩
  · exact ⟨Nat.sub_pos_of_lt hab, hgap⟩
  · rw [← Nat.cast_add, Nat.add_sub_of_le hab.le]
    exact (ZMod.isUnit_iff_coprime b N).mpr hbC

/-- Apart from the last standard residue `N-1`, every cyclic short start
already has a later (non-wrapping) reduced integer within the same bound. -/
theorem natCyclicShortStarts_not_linear_eq_last {N T a : ℕ}
    [NeZero N] (hN : 1 < N)
    (ha : a ∈ natCyclicShortStarts N T)
    (halin : a ∉ linearShortStarts N T) :
    a = N - 1 := by
  rw [mem_natCyclicShortStarts] at ha
  by_contra hlast
  have haLast : a < N - 1 := by omega
  have hcount : 0 < cyclicLocalCount N T (a : ZMod N) :=
    Nat.pos_of_ne_zero ha.2.2
  obtain ⟨h, hh⟩ := Finset.card_pos.mp hcount
  rw [Finset.mem_filter] at hh
  have hhIcc := Finset.mem_Icc.mp hh.1
  let b := ((a : ZMod N) + (h : ZMod N)).val
  have hbN : b < N := ZMod.val_lt _
  have hbC : b.Coprime N :=
    (ZMod.isUnit_iff_coprime b N).mp
      (by simpa only [b, ZMod.natCast_zmod_val] using hh.2)
  have hbmod : b = (a + h) % N := by
    dsimp [b]
    rw [← Nat.cast_add, ZMod.val_natCast]
  rw [mem_linearShortStarts] at halin
  apply halin
  refine ⟨ha.1, ha.2.1, ?_⟩
  by_cases hab : a < b
  · exact ⟨b, hab, hbN, hbC, by
      have hb_le : b ≤ a + h := by rw [hbmod]; exact Nat.mod_le _ _
      omega⟩
  · have hNa : N ≤ a + h := by
      by_contra hsmall
      have hmod : (a + h) % N = a + h := Nat.mod_eq_of_lt (by omega)
      rw [hbmod, hmod] at hab
      omega
    refine ⟨N - 1, haLast, by omega, ?_, by omega⟩
    exact (Nat.coprime_self_sub_left hN.le).mpr (Nat.coprime_one_left N)

theorem card_natCyclicShortStarts_le_linear_add_one {N T : ℕ}
    [NeZero N] (hN : 1 < N) :
    (natCyclicShortStarts N T).card ≤ (linearShortStarts N T).card + 1 := by
  have hsub :
      natCyclicShortStarts N T \ linearShortStarts N T ⊆ {N - 1} := by
    intro a ha
    rw [Finset.mem_sdiff] at ha
    rw [Finset.mem_singleton]
    exact natCyclicShortStarts_not_linear_eq_last hN ha.1 ha.2
  have hlin := linearShortStarts_subset_natCyclicShortStarts
    (N := N) (T := T)
  have hcardSub := Finset.card_le_card hsub
  have hsplit := Finset.card_sdiff_of_subset hlin
  rw [Finset.card_singleton] at hcardSub
  omega

theorem cyclicShortStarts_eq_sdiff (N T : ℕ) [NeZero N] :
    cyclicShortStarts N T =
      cyclicReducedResidues N \ cyclicVoidStarts N T := by
  classical
  ext a
  simp only [cyclicShortStarts, cyclicVoidStarts, Finset.mem_filter,
    Finset.mem_sdiff, mem_cyclicReducedResidues]
  aesop

theorem cyclicGapCDF_eq_card_cyclicShortStarts (N T : ℕ) [NeZero N] :
    cyclicGapCDF N T =
      ((cyclicShortStarts N T).card : ℝ) / (N.totient : ℝ) := by
  have hvoid : cyclicVoidStarts N T ⊆ cyclicReducedResidues N :=
    Finset.filter_subset _ _
  have hvcard : (cyclicVoidStarts N T).card ≤ N.totient := by
    rw [← card_cyclicReducedResidues N]
    exact Finset.card_le_card hvoid
  have hcard : (cyclicShortStarts N T).card =
      N.totient - (cyclicVoidStarts N T).card := by
    rw [cyclicShortStarts_eq_sdiff,
      Finset.card_sdiff_of_subset hvoid, card_cyclicReducedResidues]
  rw [cyclicGapCDF, cyclicVoidRatio, hcard, Nat.cast_sub hvcard]
  have hφ : (N.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr
      (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  field_simp

/-- The internal and cyclic distribution functions differ by at most one
gap, namely the wrap-around gap. -/
theorem abs_internalRatio_sub_cyclicGapCDF_le {N T : ℕ} [NeZero N]
    (hN : 1 < N) :
    |((internalShortGaps N T).card : ℝ) / (N.totient : ℝ) -
        cyclicGapCDF N T| ≤ 1 / (N.totient : ℝ) := by
  have hlin : (linearShortStarts N T).card ≤
      (natCyclicShortStarts N T).card :=
    Finset.card_le_card linearShortStarts_subset_natCyclicShortStarts
  have hupper := card_natCyclicShortStarts_le_linear_add_one
    (N := N) (T := T) hN
  have hφ : (0 : ℝ) < N.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  rw [cyclicGapCDF_eq_card_cyclicShortStarts,
    card_cyclicShortStarts_eq_nat,
    card_internalShortGaps_eq_linearShortStarts]
  have hlinR : ((linearShortStarts N T).card : ℝ) ≤
      (natCyclicShortStarts N T).card := by exact_mod_cast hlin
  rw [abs_of_nonpos (sub_nonpos.mpr
    ((div_le_div_iff_of_pos_right hφ).2 hlinR))]
  rw [← sub_div]
  have hneg :
      -((((linearShortStarts N T).card : ℝ) -
          (natCyclicShortStarts N T).card) / (N.totient : ℝ)) =
        (((natCyclicShortStarts N T).card : ℝ) -
          (linearShortStarts N T).card) / (N.totient : ℝ) := by ring
  rw [hneg]
  apply (div_le_div_iff_of_pos_right hφ).2
  have hdiff : (natCyclicShortStarts N T).card -
      (linearShortStarts N T).card ≤ 1 := by omega
  exact_mod_cast hdiff

theorem le_totient_primeProduct (k : ℕ) :
    k ≤ (primeProduct k).totient := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [totient_primeProduct_succ]
      cases k with
      | zero =>
          simp only [primeProduct_zero, Nat.totient_one, one_mul]
          have hp := nthPrime_two_le 0
          omega
      | succ k =>
          have hpmono : nthPrime 0 < nthPrime (k + 1) :=
            nthPrime_strictMono (by omega)
          have hp0 := nthPrime_two_le 0
          have hfactor : 2 ≤ nthPrime (k + 1) - 1 := by omega
          calc
            k + 2 ≤ 2 * (k + 1) := by omega
            _ ≤ 2 * (primeProduct (k + 1)).totient :=
              Nat.mul_le_mul_left 2 ih
            _ = (primeProduct (k + 1)).totient * 2 := by omega
            _ ≤ (primeProduct (k + 1)).totient *
                (nthPrime (k + 1) - 1) :=
              Nat.mul_le_mul_left _ hfactor

theorem tendsto_totient_primeProduct_atTop :
    Tendsto (fun k ↦ (primeProduct k).totient) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  filter_upwards [eventually_ge_atTop B] with k hk
  exact hk.trans (le_totient_primeProduct k)

theorem tendsto_inv_totient_primeProduct_zero :
    Tendsto (fun k ↦ (1 : ℝ) / (primeProduct k).totient)
      atTop (𝓝 0) := by
  have hcast : Tendsto (fun k ↦ ((primeProduct k).totient : ℝ))
      atTop atTop := tendsto_natCast_atTop_atTop.comp
        tendsto_totient_primeProduct_atTop
  rw [show (fun k ↦ (1 : ℝ) / (primeProduct k).totient) =
      (fun k ↦ ((primeProduct k).totient : ℝ)⁻¹) by
    funext k
    simp [one_div]]
  convert tendsto_inv_atTop_zero.comp hcast using 1 <;>
    simp [Function.comp_def]

theorem eventually_one_lt_primeProduct :
    ∀ᶠ k : ℕ in atTop, 1 < primeProduct k := by
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hd : nthPrime 0 ∣ primeProduct k :=
    nthPrime_dvd_primeProduct (by omega)
  have hle : nthPrime 0 ≤ primeProduct k :=
    Nat.le_of_dvd (primeProduct_pos k) hd
  exact (lt_of_lt_of_le (by omega : 1 < 2) (nthPrime_two_le 0)).trans_le hle

/-- The distribution function in Erdős Problem 235, with precisely the
normalization used there. -/
def gapCDF (k : ℕ) (c : ℝ) : ℝ :=
  ((internalShortGaps (primeProduct k)
      (normalizedThreshold (primeProduct k) c)).card : ℝ) /
    ((primeProduct k).totient : ℝ)

/-- The claimed limiting distribution. -/
def exponentialGapCDF (c : ℝ) : ℝ :=
  1 - Real.exp (-c)

theorem continuous_exponentialGapCDF : Continuous exponentialGapCDF := by
  unfold exponentialGapCDF
  fun_prop

theorem continuousOn_exponentialGapCDF :
    ContinuousOn exponentialGapCDF (Set.Ici 0) :=
  continuous_exponentialGapCDF.continuousOn

theorem internalShortGaps_zero (N : ℕ) :
    internalShortGaps N 0 = ∅ := by
  classical
  ext ab
  rcases ab with ⟨a, b⟩
  rw [mem_internalShortGaps]
  constructor
  · intro h
    exfalso
    have hab := h.1.1
    omega
  · intro h
    simpa using h

@[simp] theorem gapCDF_zero (k : ℕ) : gapCDF k 0 = 0 := by
  unfold gapCDF normalizedThreshold
  simp [internalShortGaps_zero]

/-- The internal/cyclic discrepancy tends to zero uniformly in the choice
of threshold. -/
theorem tendsto_gapCDF_sub_cyclicGapCDF_zero (c : ℝ) :
    Tendsto
      (fun k ↦ gapCDF k c -
        cyclicGapCDF (primeProduct k)
          (normalizedThreshold (primeProduct k) c))
      atTop (𝓝 0) := by
  let d : ℕ → ℝ := fun k ↦ gapCDF k c -
    cyclicGapCDF (primeProduct k)
      (normalizedThreshold (primeProduct k) c)
  have hbound : ∀ᶠ k : ℕ in atTop,
      |d k| ≤ (1 : ℝ) / (primeProduct k).totient := by
    filter_upwards [eventually_one_lt_primeProduct] with k hk
    simpa [d, gapCDF] using
      (abs_internalRatio_sub_cyclicGapCDF_le
        (N := primeProduct k)
        (T := normalizedThreshold (primeProduct k) c) hk)
  have habs : Tendsto (fun k ↦ |d k|) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun k ↦ abs_nonneg _
    · exact hbound
    · exact tendsto_inv_totient_primeProduct_zero
  apply (tendsto_zero_iff_abs_tendsto_zero d).2
  convert habs using 1 <;> simp [Function.comp_def]

theorem tendsto_cyclicGapCDF (c : ℝ) (hc : 0 < c) :
    Tendsto
      (fun k ↦ cyclicGapCDF (primeProduct k)
        (normalizedThreshold (primeProduct k) c))
      atTop (𝓝 (exponentialGapCDF c)) := by
  have h : Tendsto
      (fun k : ℕ ↦ (1 : ℝ) - cyclicVoidRatio (primeProduct k)
        (normalizedThreshold (primeProduct k) c))
      atTop (𝓝 ((1 : ℝ) - Real.exp (-c))) :=
    tendsto_const_nhds.sub (tendsto_cyclicVoidRatio c hc)
  simpa [cyclicGapCDF, exponentialGapCDF] using h

/-- Hooley's exponential gap law in the exact normalization of Erdős
Problem 235. -/
theorem erdos_235_limit (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun k ↦ gapCDF k c) atTop
      (𝓝 (exponentialGapCDF c)) := by
  by_cases hzero : c = 0
  · subst c
    simp [exponentialGapCDF]
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hzero)
    have hdiff := tendsto_gapCDF_sub_cyclicGapCDF_zero c
    have hcyc := tendsto_cyclicGapCDF c hcpos
    have hadd := hdiff.add hcyc
    convert hadd using 1
    · funext k
      ring
    · simp

/-- Exact existence-and-continuity formulation requested in the problem. -/
theorem erdos_235 :
    ∃ f : ℝ → ℝ, Continuous f ∧
      ∀ c, 0 ≤ c → Tendsto (fun k ↦ gapCDF k c) atTop (𝓝 (f c)) := by
  exact ⟨exponentialGapCDF, continuous_exponentialGapCDF,
    fun c hc ↦ erdos_235_limit c hc⟩

#print axioms erdos_235_limit
#print axioms erdos_235

end

end Erdos235
