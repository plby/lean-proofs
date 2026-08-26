import ErdosProblems.Erdos796.GammaBound
import ErdosProblems.Erdos796.MultiplicativeSidon
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.CastCard
import Mathlib.Data.Nat.Factors
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A factor-graph cardinal bound for multiplicative Sidon sets

This file packages the two `C₄`-free graph counts in the explicit upper-bound
argument.  The number-theoretic part of that argument chooses one of two
factorizations for every element.  `SidonFactorCover` records exactly the
properties of those choices which enter the graph count; the theorem
`card_sub_one_sub_primeCounting_le_of_factorCover` then proves the cardinal
estimate without hiding any further compatibility assertion.
-/

namespace Erdos796

open scoped BigOperators

namespace SidonCardBound

/-- The three real scales used by the factor selection. -/
noncomputable def thirdScale (N : ℕ) : ℝ := (N : ℝ) ^ (1 / 3 : ℝ)

noncomputable def halfScale (N : ℕ) : ℝ := (N : ℝ) ^ (1 / 2 : ℝ)

noncomputable def twoThirdScale (N : ℕ) : ℝ := (N : ℝ) ^ (2 / 3 : ℝ)

theorem third_mul_twoThird {N : ℕ} (hN : 0 < N) :
    thirdScale N * twoThirdScale N = N := by
  rw [thirdScale, twoThirdScale, ← Real.rpow_add (by exact_mod_cast hN)]
  norm_num

theorem third_sq {N : ℕ} (hN : 0 < N) :
    thirdScale N ^ 2 = twoThirdScale N := by
  rw [thirdScale, twoThirdScale, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
  norm_num

theorem twoThird_mul_third {N : ℕ} (hN : 0 < N) :
    twoThirdScale N * thirdScale N = N := by
  rw [mul_comm]
  exact third_mul_twoThird hN

/-- If every prime divisor of `a` is at most `t`, then `a` has a divisor in
`(t,t²]` as soon as `a>t`.  This elementary strong-induction lemma is the
arithmetic mechanism behind the balanced-factor choice. -/
theorem exists_divisor_gt_le_sq {a : ℕ} {t : ℝ}
    (ht : 2 ≤ t) (ha0 : a ≠ 0) (hat : t < a)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ a → (p : ℝ) ≤ t) :
    ∃ d : ℕ, d ∣ a ∧ t < d ∧ (d : ℝ) ≤ t ^ 2 := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
      by_cases hasmall : (a : ℝ) ≤ t ^ 2
      · exact ⟨a, dvd_rfl, hat, hasmall⟩
      · have ha1 : a ≠ 1 := by
          intro ha
          subst a
          norm_num at hat
          linarith
        obtain ⟨p, hpPrime, hpDvd⟩ := Nat.exists_prime_and_dvd ha1
        let b := a / p
        have haPos : 0 < a := Nat.pos_of_ne_zero ha0
        have hbLt : b < a := by
          exact Nat.div_lt_self haPos hpPrime.one_lt
        have hbp : b * p = a := by
          exact Nat.div_mul_cancel hpDvd
        have hpLe : (p : ℝ) ≤ t := hprime p hpPrime hpDvd
        have hbPos : 0 < b := by
          by_contra hb
          have hb0 : b = 0 := Nat.eq_zero_of_not_pos hb
          rw [hb0, zero_mul] at hbp
          exact ha0 hbp.symm
        have hbNe : b ≠ 0 := Nat.ne_of_gt hbPos
        have hbDvd : b ∣ a := ⟨p, hbp.symm⟩
        have hbt : t < (b : ℝ) := by
          by_contra hnot
          have hbLe : (b : ℝ) ≤ t := le_of_not_gt hnot
          have hcast : (a : ℝ) = (b : ℝ) * p := by exact_mod_cast hbp.symm
          have : (a : ℝ) ≤ t ^ 2 := by
            rw [hcast, pow_two]
            exact mul_le_mul hbLe hpLe (by positivity) (by linarith)
          exact hasmall this
        have hprimeB : ∀ q : ℕ, q.Prime → q ∣ b → (q : ℝ) ≤ t := by
          intro q hqPrime hqDvd
          exact hprime q hqPrime (hqDvd.trans hbDvd)
        obtain ⟨d, hdB, htd, hdSq⟩ :=
          ih b hbLt hbNe hbt hprimeB
        exact ⟨d, hdB.trans hbDvd, htd, hdSq⟩

/-- Having a prime divisor above the two-thirds scale is the large-prime
case of the factor partition. -/
def HasLargePrimeFactor (N a : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ twoThirdScale N < p

/-- Every non-large element of `[N]` admits a factorization with one factor
at most `N^(1/2)` and the other at most `N^(2/3)`. -/
theorem exists_balanced_factor {N a : ℕ} (hN : 8 ≤ N)
    (haPos : 0 < a) (haN : a ≤ N) (hnotLarge : ¬HasLargePrimeFactor N a) :
    ∃ v u : ℕ, a = v * u ∧ 1 ≤ v ∧ 1 ≤ u ∧
      (v : ℝ) ≤ halfScale N ∧ (u : ℝ) ≤ twoThirdScale N := by
  have hNpos : 0 < N := by omega
  have hnpos : (0 : ℝ) < N := by exact_mod_cast hNpos
  have htNonneg : 0 ≤ thirdScale N := Real.rpow_nonneg hnpos.le _
  have hsNonneg : 0 ≤ twoThirdScale N := Real.rpow_nonneg hnpos.le _
  have htTwo : 2 ≤ thirdScale N := by
    have h8 : (8 : ℝ) ≤ N := by exact_mod_cast hN
    have hmono := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 8) h8
      (by norm_num : (0 : ℝ) ≤ (1 / 3 : ℝ))
    norm_num [thirdScale] at hmono ⊢
    exact hmono
  have hprimeLe : ∀ p : ℕ, p.Prime → p ∣ a →
      (p : ℝ) ≤ twoThirdScale N := by
    intro p hp hpa
    by_contra hpnot
    apply hnotLarge
    exact ⟨p, hp, hpa, lt_of_not_ge hpnot⟩
  by_cases hsmall : (a : ℝ) ≤ twoThirdScale N
  · have hhalfOne : (1 : ℝ) ≤ halfScale N := by
      have hnOne : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      exact Real.one_le_rpow hnOne (by norm_num)
    exact ⟨1, a, by simp, by simp, haPos, by simpa using! hhalfOne, hsmall⟩
  · have htscale : thirdScale N ≤ twoThirdScale N := by
      rw [← third_sq hNpos]
      nlinarith
    have hfind : ∃ d : ℕ, d ∣ a ∧ (thirdScale N : ℝ) ≤ d ∧
        (d : ℝ) ≤ twoThirdScale N := by
      by_cases hp : ∃ p : ℕ, p.Prime ∧ p ∣ a ∧ thirdScale N ≤ p
      · obtain ⟨p, hpPrime, hpDvd, htp⟩ := hp
        exact ⟨p, hpDvd, htp, hprimeLe p hpPrime hpDvd⟩
      · have hprimeT : ∀ p : ℕ, p.Prime → p ∣ a →
            (p : ℝ) ≤ thirdScale N := by
          intro p hpPrime hpDvd
          have hp' := not_exists.mp hp p
          push Not at hp'
          exact (hp' hpPrime hpDvd).le
        have hat : thirdScale N < (a : ℝ) :=
          htscale.trans_lt (lt_of_not_ge hsmall)
        obtain ⟨d, hd, htd, hdSq⟩ :=
          exists_divisor_gt_le_sq htTwo (Nat.ne_of_gt haPos) hat hprimeT
        exact ⟨d, hd, htd.le, by simpa [third_sq hNpos] using! hdSq⟩
    obtain ⟨d, hdDvd, htd, hds⟩ := hfind
    let e := a / d
    have hed : e * d = a := Nat.div_mul_cancel hdDvd
    have hdPos : 0 < d := by
      have : (0 : ℝ) < d :=
        lt_of_lt_of_le (by linarith : (0 : ℝ) < thirdScale N) htd
      exact_mod_cast this
    have hePos : 0 < e := by
      by_contra he
      have he0 : e = 0 := Nat.eq_zero_of_not_pos he
      rw [he0, zero_mul] at hed
      exact (Nat.ne_of_gt haPos) hed.symm
    have heS : (e : ℝ) ≤ twoThirdScale N := by
      have hea : (e : ℝ) * d = a := by exact_mod_cast hed
      have haNreal : (a : ℝ) ≤ N := by exact_mod_cast haN
      have hts : thirdScale N * twoThirdScale N = (N : ℝ) :=
        third_mul_twoThird hNpos
      by_contra heNot
      have hse : twoThirdScale N < (e : ℝ) := lt_of_not_ge heNot
      have hprodLt : (N : ℝ) < (e : ℝ) * d := by
        rw [← hts]
        calc
          thirdScale N * twoThirdScale N < thirdScale N * (e : ℝ) :=
            mul_lt_mul_of_pos_left hse (by linarith)
          _ ≤ (d : ℝ) * e :=
            mul_le_mul_of_nonneg_right htd (by positivity)
          _ = (e : ℝ) * d := by ring
      linarith
    let v := min d e
    let u := max d e
    have hdOne : 1 ≤ d := hdPos
    have heOne : 1 ≤ e := hePos
    have hvPos : 1 ≤ v := by
      exact le_min hdOne heOne
    have huPos : 1 ≤ u := by
      exact hdOne.trans (le_max_left d e)
    have hprodVU : v * u = a := by
      rw [min_mul_max]
      simpa [Nat.mul_comm] using! hed
    have huS : (u : ℝ) ≤ twoThirdScale N := by
      simp only [u, Nat.cast_max]
      exact max_le hds heS
    have hvSq : (v : ℝ) ^ 2 ≤ (N : ℝ) := by
      have hvd : v ≤ d := min_le_left _ _
      have hve : v ≤ e := min_le_right _ _
      have hvdR : (v : ℝ) ≤ d := by exact_mod_cast hvd
      have hveR : (v : ℝ) ≤ e := by exact_mod_cast hve
      have hea : (e : ℝ) * d = a := by exact_mod_cast hed
      have haNreal : (a : ℝ) ≤ N := by exact_mod_cast haN
      calc
        (v : ℝ) ^ 2 = (v : ℝ) * v := by ring
        _ ≤ (e : ℝ) * d :=
          mul_le_mul hveR hvdR (by positivity) (by positivity)
        _ = a := hea
        _ ≤ N := haNreal
    have hvHalf : (v : ℝ) ≤ halfScale N := by
      rw [halfScale, ← Real.sqrt_eq_rpow]
      exact Real.le_sqrt_of_sq_le hvSq
    exact ⟨v, u, hprodVU.symm, hvPos, huPos, hvHalf, huS⟩

/-! The product image of a factor graph. -/

/-- The products represented by a finite factor graph. -/
def productImage (E : Finset (ℕ × ℕ)) : Finset ℕ :=
  E.image GammaBound.edgeProduct

/-! ## The canonical two-graph factor cover -/

/-- A chosen large prime divisor.  It is used only under the corresponding
`HasLargePrimeFactor` hypothesis. -/
noncomputable def largePrime (N a : ℕ) : ℕ :=
  by
    classical
    exact if h : HasLargePrimeFactor N a then Classical.choose h else 1

theorem largePrime_spec {N a : ℕ} (h : HasLargePrimeFactor N a) :
    (largePrime N a).Prime ∧ largePrime N a ∣ a ∧
      twoThirdScale N < largePrime N a := by
  rw [largePrime, dif_pos h]
  exact Classical.choose_spec h

/-- The chosen edge for an element in the large-prime part. -/
noncomputable def largeEdge (N a : ℕ) : ℕ × ℕ :=
  (a / largePrime N a, largePrime N a)

theorem largeEdge_product {N a : ℕ} (h : HasLargePrimeFactor N a) :
    GammaBound.edgeProduct (largeEdge N a) = a := by
  rw [GammaBound.edgeProduct, largeEdge]
  exact Nat.div_mul_cancel (largePrime_spec h).2.1

/-- A proof-carrying balanced factor choice. -/
noncomputable def balancedFactorSubtype {N a : ℕ} (hN : 8 ≤ N)
    (haPos : 0 < a) (haN : a ≤ N) (hnot : ¬HasLargePrimeFactor N a) :
    {vu : ℕ × ℕ //
      a = vu.1 * vu.2 ∧ 1 ≤ vu.1 ∧ 1 ≤ vu.2 ∧
        (vu.1 : ℝ) ≤ halfScale N ∧
        (vu.2 : ℝ) ≤ twoThirdScale N} := by
  let hex := exists_balanced_factor hN haPos haN hnot
  let v := Classical.choose hex
  let hu := Classical.choose_spec hex
  let u := Classical.choose hu
  have hspec := Classical.choose_spec hu
  exact ⟨(v, u), hspec⟩

/-- The balanced edge, with a harmless fallback outside its intended domain. -/
noncomputable def balancedEdge (N a : ℕ) (hN : 8 ≤ N) : ℕ × ℕ :=
  by
    classical
    exact if h : 0 < a ∧ a ≤ N ∧ ¬HasLargePrimeFactor N a then
      (balancedFactorSubtype hN h.1 h.2.1 h.2.2).1
    else (1, a)

theorem balancedEdge_spec {N a : ℕ} (hN : 8 ≤ N) (haPos : 0 < a)
    (haN : a ≤ N) (hnot : ¬HasLargePrimeFactor N a) :
    a = (balancedEdge N a hN).1 * (balancedEdge N a hN).2 ∧
      1 ≤ (balancedEdge N a hN).1 ∧
      1 ≤ (balancedEdge N a hN).2 ∧
      ((balancedEdge N a hN).1 : ℝ) ≤ halfScale N ∧
      ((balancedEdge N a hN).2 : ℝ) ≤ twoThirdScale N := by
  rw [balancedEdge, dif_pos ⟨haPos, haN, hnot⟩]
  exact (balancedFactorSubtype hN haPos haN hnot).2

theorem balancedEdge_product {N a : ℕ} (hN : 8 ≤ N) (haPos : 0 < a)
    (haN : a ≤ N) (hnot : ¬HasLargePrimeFactor N a) :
    GammaBound.edgeProduct (balancedEdge N a hN) = a := by
  rw [GammaBound.edgeProduct]
  exact (balancedEdge_spec hN haPos haN hnot).1.symm

/-- The two parts of `U` used by the factor construction. -/
noncomputable def largePart (N : ℕ) (U : Finset ℕ) : Finset ℕ := by
  classical
  exact U.filter (HasLargePrimeFactor N)

noncomputable def balancedPart (N : ℕ) (U : Finset ℕ) : Finset ℕ := by
  classical
  exact U.filter (fun a => ¬HasLargePrimeFactor N a)

@[simp] theorem mem_largePart {N : ℕ} {U : Finset ℕ} {a : ℕ} :
    a ∈ largePart N U ↔ a ∈ U ∧ HasLargePrimeFactor N a := by
  classical
  simp [largePart]

@[simp] theorem mem_balancedPart {N : ℕ} {U : Finset ℕ} {a : ℕ} :
    a ∈ balancedPart N U ↔ a ∈ U ∧ ¬HasLargePrimeFactor N a := by
  classical
  simp [balancedPart]

/-- The canonical edge sets. -/
noncomputable def largeEdges (N : ℕ) (U : Finset ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (largePart N U).image (largeEdge N)

noncomputable def balancedEdges (N : ℕ) (U : Finset ℕ) (hN : 8 ≤ N) :
    Finset (ℕ × ℕ) := by
  classical
  exact (balancedPart N U).image (fun a => balancedEdge N a hN)

/-- The four finite vertex classes. -/
noncomputable def largeLeft (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 ⌊thirdScale N⌋₊

def largeRight (N : ℕ) : Finset ℕ := Nat.primesLE N

noncomputable def balancedLeft (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 ⌊halfScale N⌋₊

noncomputable def balancedRight (N : ℕ) : Finset ℕ :=
  Finset.Icc 1 ⌊twoThirdScale N⌋₊

theorem card_largeLeft_le (N : ℕ) :
    ((largeLeft N).card : ℝ) ≤ thirdScale N := by
  have ht : 0 ≤ thirdScale N := Real.rpow_nonneg (by positivity) _
  have hcard : (largeLeft N).card = ⌊thirdScale N⌋₊ := by
    simp [largeLeft]
  rw [hcard]
  exact Nat.floor_le ht

theorem card_largeRight (N : ℕ) :
    (largeRight N).card = Nat.primeCounting N := by
  exact Nat.primesLE_card_eq_primeCounting N

theorem card_balancedLeft_le (N : ℕ) :
    ((balancedLeft N).card : ℝ) ≤ halfScale N := by
  have ht : 0 ≤ halfScale N := Real.rpow_nonneg (by positivity) _
  have hcard : (balancedLeft N).card = ⌊halfScale N⌋₊ := by
    simp [balancedLeft]
  rw [hcard]
  exact Nat.floor_le ht

theorem card_balancedRight_le (N : ℕ) :
    ((balancedRight N).card : ℝ) ≤ twoThirdScale N := by
  have ht : 0 ≤ twoThirdScale N := Real.rpow_nonneg (by positivity) _
  have hcard : (balancedRight N).card = ⌊twoThirdScale N⌋₊ := by
    simp [balancedRight]
  rw [hcard]
  exact Nat.floor_le ht

theorem largeEdge_mem_product {N : ℕ} {U : Finset ℕ} (hN : 8 ≤ N)
    (hU : U ⊆ positiveIcc N) {a : ℕ} (ha : a ∈ largePart N U) :
    largeEdge N a ∈ largeLeft N ×ˢ largeRight N := by
  have ha' := mem_largePart.mp ha
  have haIcc := mem_positiveIcc.mp (hU ha'.1)
  have hp := largePrime_spec ha'.2
  let p := largePrime N a
  let b := a / p
  have hNpos : 0 < N := by omega
  have htPos : 0 < thirdScale N := Real.rpow_pos_of_pos (by exact_mod_cast hNpos) _
  have hbp : b * p = a := Nat.div_mul_cancel hp.2.1
  have hbPos : 0 < b := by
    by_contra hb
    have hb0 : b = 0 := Nat.eq_zero_of_not_pos hb
    rw [hb0, zero_mul] at hbp
    omega
  have hbLt : (b : ℝ) < thirdScale N := by
    by_contra hbnot
    have htb : thirdScale N ≤ (b : ℝ) := le_of_not_gt hbnot
    have hNid : thirdScale N * twoThirdScale N = (N : ℝ) :=
      third_mul_twoThird hNpos
    have hcast : (b : ℝ) * p = a := by exact_mod_cast hbp
    have hNa : (N : ℝ) < a := by
      rw [← hNid, ← hcast]
      calc
        thirdScale N * twoThirdScale N < thirdScale N * (p : ℝ) :=
          mul_lt_mul_of_pos_left hp.2.2 htPos
        _ ≤ (b : ℝ) * p :=
          mul_le_mul_of_nonneg_right htb (by positivity)
    have haNreal : (a : ℝ) ≤ N := by exact_mod_cast haIcc.2
    linarith
  have hbFloor : b ≤ ⌊thirdScale N⌋₊ :=
    Nat.le_floor hbLt.le
  have hpLeA : p ≤ a := Nat.le_of_dvd haIcc.1 hp.2.1
  have hpLeN : p ≤ N := hpLeA.trans haIcc.2
  apply Finset.mem_product.mpr
  constructor
  · exact Finset.mem_Icc.mpr ⟨hbPos, hbFloor⟩
  · exact Nat.mem_primesLE.mpr ⟨hpLeN, hp.1⟩

theorem balancedEdge_mem_product {N : ℕ} {U : Finset ℕ} (hN : 8 ≤ N)
    (hU : U ⊆ positiveIcc N) {a : ℕ} (ha : a ∈ balancedPart N U) :
    balancedEdge N a hN ∈ balancedLeft N ×ˢ balancedRight N := by
  have ha' := mem_balancedPart.mp ha
  have haIcc := mem_positiveIcc.mp (hU ha'.1)
  have hs := balancedEdge_spec hN (by omega) haIcc.2 ha'.2
  have hvFloor : (balancedEdge N a hN).1 ≤ ⌊halfScale N⌋₊ :=
    Nat.le_floor hs.2.2.2.1
  have huFloor : (balancedEdge N a hN).2 ≤ ⌊twoThirdScale N⌋₊ :=
    Nat.le_floor hs.2.2.2.2
  apply Finset.mem_product.mpr
  exact ⟨Finset.mem_Icc.mpr ⟨hs.2.1, hvFloor⟩,
    Finset.mem_Icc.mpr ⟨hs.2.2.1, huFloor⟩⟩

/-- A chosen factorization makes multiplication injective on the image of
the choice map, since multiplication recovers the original element. -/
theorem edgeProduct_injective_on_image {S : Finset ℕ} {f : ℕ → ℕ × ℕ}
    (hprod : ∀ a ∈ S, GammaBound.edgeProduct (f a) = a) :
    Set.InjOn GammaBound.edgeProduct (S.image f : Set (ℕ × ℕ)) := by
  intro e he e' he' heq
  rcases Finset.mem_image.mp he with ⟨a, ha, rfl⟩
  rcases Finset.mem_image.mp he' with ⟨a', ha', rfl⟩
  have haa' : a = a' := (hprod a ha).symm.trans (heq.trans (hprod a' ha'))
  subst a'
  rfl

theorem large_product_injective (N : ℕ) (U : Finset ℕ) :
    Set.InjOn GammaBound.edgeProduct
      (largeEdges N U : Set (ℕ × ℕ)) := by
  rw [largeEdges]
  apply edgeProduct_injective_on_image
  intro a ha
  exact largeEdge_product (mem_largePart.mp ha).2

theorem balanced_product_injective {N : ℕ} (U : Finset ℕ) (hN : 8 ≤ N)
    (hU : U ⊆ positiveIcc N) :
    Set.InjOn GammaBound.edgeProduct
      (balancedEdges N U hN : Set (ℕ × ℕ)) := by
  rw [balancedEdges]
  apply edgeProduct_injective_on_image
  intro a ha
  have ha' := mem_balancedPart.mp ha
  have haIcc := mem_positiveIcc.mp (hU ha'.1)
  exact balancedEdge_product hN (by omega) haIcc.2 ha'.2

theorem large_products_mem {N : ℕ} {U : Finset ℕ} :
    ∀ e ∈ largeEdges N U, GammaBound.edgeProduct e ∈ U := by
  intro e he
  rw [largeEdges] at he
  rcases Finset.mem_image.mp he with ⟨a, ha, rfl⟩
  rw [largeEdge_product (mem_largePart.mp ha).2]
  exact (mem_largePart.mp ha).1

theorem balanced_products_mem {N : ℕ} {U : Finset ℕ} (hN : 8 ≤ N)
    (hU : U ⊆ positiveIcc N) :
    ∀ e ∈ balancedEdges N U hN, GammaBound.edgeProduct e ∈ U := by
  intro e he
  rw [balancedEdges] at he
  rcases Finset.mem_image.mp he with ⟨a, ha, rfl⟩
  have ha' := mem_balancedPart.mp ha
  have haIcc := mem_positiveIcc.mp (hU ha'.1)
  rw [balancedEdge_product hN (by omega) haIcc.2 ha'.2]
  exact ha'.1

theorem factor_edges_cover {N : ℕ} {U : Finset ℕ} (hN : 8 ≤ N)
    (hU : U ⊆ positiveIcc N) :
    U.erase 1 ⊆
      productImage (largeEdges N U) ∪ productImage (balancedEdges N U hN) := by
  intro a ha
  have haU := (Finset.mem_erase.mp ha).2
  by_cases hlarge : HasLargePrimeFactor N a
  · apply Finset.mem_union_left
    rw [productImage]
    apply Finset.mem_image.mpr
    refine ⟨largeEdge N a, ?_, largeEdge_product hlarge⟩
    rw [largeEdges]
    exact Finset.mem_image.mpr ⟨a, mem_largePart.mpr ⟨haU, hlarge⟩, rfl⟩
  · apply Finset.mem_union_right
    rw [productImage]
    apply Finset.mem_image.mpr
    have haIcc := mem_positiveIcc.mp (hU haU)
    refine ⟨balancedEdge N a hN, ?_,
      balancedEdge_product hN (by omega) haIcc.2 hlarge⟩
    rw [balancedEdges]
    exact Finset.mem_image.mpr
      ⟨a, mem_balancedPart.mpr ⟨haU, hlarge⟩, rfl⟩

/-- A pair of factor graphs covering all non-unit elements of `U`.

The first graph is the large-prime graph.  The second is the balanced-factor
graph.  Keeping the four vertex classes in the certificate makes all finite
cardinality estimates explicit and independently checkable.
-/
structure SidonFactorCover (U : Finset ℕ) where
  largeEdges : Finset (ℕ × ℕ)
  balancedEdges : Finset (ℕ × ℕ)
  largeLeft : Finset ℕ
  largeRight : Finset ℕ
  balancedLeft : Finset ℕ
  balancedRight : Finset ℕ
  large_supported : largeEdges ⊆ largeLeft ×ˢ largeRight
  balanced_supported : balancedEdges ⊆ balancedLeft ×ˢ balancedRight
  large_products_mem : ∀ e ∈ largeEdges, GammaBound.edgeProduct e ∈ U
  balanced_products_mem : ∀ e ∈ balancedEdges, GammaBound.edgeProduct e ∈ U
  large_product_injective :
    Set.InjOn GammaBound.edgeProduct (largeEdges : Set (ℕ × ℕ))
  balanced_product_injective :
    Set.InjOn GammaBound.edgeProduct (balancedEdges : Set (ℕ × ℕ))
  covers : U.erase 1 ⊆ productImage largeEdges ∪ productImage balancedEdges

/-- The factor cover constructed above, packaged for the graph-counting API. -/
noncomputable def canonicalFactorCover {N : ℕ} (U : Finset ℕ) (hN : 8 ≤ N)
    (hU : U ⊆ positiveIcc N) : SidonFactorCover U where
  largeEdges := largeEdges N U
  balancedEdges := balancedEdges N U hN
  largeLeft := largeLeft N
  largeRight := largeRight N
  balancedLeft := balancedLeft N
  balancedRight := balancedRight N
  large_supported := by
    intro e he
    rw [largeEdges] at he
    rcases Finset.mem_image.mp he with ⟨a, ha, rfl⟩
    exact largeEdge_mem_product hN hU ha
  balanced_supported := by
    intro e he
    rw [balancedEdges] at he
    rcases Finset.mem_image.mp he with ⟨a, ha, rfl⟩
    exact balancedEdge_mem_product hN hU ha
  large_products_mem := large_products_mem
  balanced_products_mem := balanced_products_mem hN hU
  large_product_injective := large_product_injective N U
  balanced_product_injective := balanced_product_injective U hN hU
  covers := factor_edges_cover hN hU

/-- The factor graph of an unordered-product-unique set is `C₄`-free.

This is the direct multiplicative-Sidon version of
`GammaBound.c4Free_of_factor_edges`; it avoids passing back through ordered
representation counts.
-/
theorem c4Free_of_unorderedProductUnique
    {U : Finset ℕ} {E : Finset (ℕ × ℕ)}
    (hmem : ∀ e ∈ E, GammaBound.edgeProduct e ∈ U)
    (hinj : Set.InjOn GammaBound.edgeProduct (E : Set (ℕ × ℕ)))
    (hSidon : UnorderedProductUnique U) :
    Bipartite.C4Free E := by
  intro x₁ x₂ y₁ y₂ h11 h12 h21 h22
  let a := x₁ * y₁
  let b := x₁ * y₂
  let c := x₂ * y₁
  let d := x₂ * y₂
  have ha : a ∈ U := hmem (x₁, y₁) h11
  have hb : b ∈ U := hmem (x₁, y₂) h12
  have hc : c ∈ U := hmem (x₂, y₁) h21
  have hd : d ∈ U := hmem (x₂, y₂) h22
  have hprod : a * d = b * c := by
    dsimp [a, b, c, d]
    ring
  rcases hSidon ha hd hb hc hprod with hparallel | hcross
  · right
    have hab : a = b := hparallel.1
    exact congrArg Prod.snd (hinj h11 h12 hab)
  · left
    have hac : a = c := hcross.1
    exact congrArg Prod.fst (hinj h11 h21 hac)

/-- Injectivity of the product map converts the product image back to the
number of graph edges. -/
theorem card_productImage_of_injective {E : Finset (ℕ × ℕ)}
    (hinj : Set.InjOn GammaBound.edgeProduct (E : Set (ℕ × ℕ))) :
    (productImage E).card = E.card := by
  exact Finset.card_image_iff.mpr hinj

/-- A convenient square-root form of KST: a `C₄`-free bipartite graph has at
most `|R| + |L| sqrt |R|` edges. -/
theorem edgeCount_le_card_add_card_mul_sqrt
    {E : Finset (ℕ × ℕ)} (hfree : Bipartite.C4Free E)
    (L R : Finset ℕ) :
    (Bipartite.edgeCount E L R : ℝ) ≤
      (R.card : ℝ) + (L.card : ℝ) * Real.sqrt (R.card : ℝ) := by
  have hbase := Bipartite.edgeCount_le_card_add_sqrt hfree L R
  have hL : 0 ≤ (L.card : ℝ) := by positivity
  have hR : 0 ≤ (R.card : ℝ) := by positivity
  have hsqrtR : 0 ≤ Real.sqrt (R.card : ℝ) := Real.sqrt_nonneg _
  have hsqrtR_sq : Real.sqrt (R.card : ℝ) ^ 2 = (R.card : ℝ) :=
    Real.sq_sqrt hR
  have hrad :
      Real.sqrt
          (2 * (R.card : ℝ) * (Nat.choose L.card 2 : ℝ)) ≤
        (L.card : ℝ) * Real.sqrt (R.card : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · rw [Nat.cast_choose_two]
      calc
        2 * (R.card : ℝ) *
              ((L.card : ℝ) * ((L.card : ℝ) - 1) / 2) =
            (R.card : ℝ) *
              ((L.card : ℝ) * ((L.card : ℝ) - 1)) := by ring
        _ ≤ (R.card : ℝ) * ((L.card : ℝ) * (L.card : ℝ)) := by
          gcongr
          linarith
        _ = ((L.card : ℝ) * Real.sqrt (R.card : ℝ)) ^ 2 := by
          rw [mul_pow, hsqrtR_sq]
          ring
  linarith

/-- The two factor graphs cover at most the sum of their edge counts. -/
theorem card_erase_le_edge_cards {U : Finset ℕ} (C : SidonFactorCover U) :
    (U.erase 1).card ≤ C.largeEdges.card + C.balancedEdges.card := by
  calc
    (U.erase 1).card ≤
        (productImage C.largeEdges ∪ productImage C.balancedEdges).card :=
      Finset.card_le_card C.covers
    _ ≤ (productImage C.largeEdges).card +
        (productImage C.balancedEdges).card :=
      Finset.card_union_le _ _
    _ = C.largeEdges.card + C.balancedEdges.card := by
      rw [card_productImage_of_injective C.large_product_injective,
        card_productImage_of_injective C.balanced_product_injective]

/-- Removing the possible unit costs at most one element. -/
theorem card_sub_one_le_card_erase (U : Finset ℕ) :
    (U.card : ℝ) - 1 ≤ ((U.erase 1).card : ℝ) := by
  classical
  by_cases h1 : 1 ∈ U
  · have hcard := Finset.card_erase_add_one h1
    have hcardReal : ((U.erase 1).card : ℝ) + 1 = U.card := by
      exact_mod_cast hcard
    linarith
  · rw [Finset.erase_eq_of_notMem h1]
    linarith

/-- The graph-theoretic core of the explicit Sidon bound, with abstract real
upper bounds for the four vertex classes.

For the manuscript's factor choice one substitutes
`x=N^(1/3)`, `y=N^(1/2)`, and `z=N^(2/3)`.
-/
theorem card_sub_one_sub_primeCounting_le_of_factorCover
    {U : Finset ℕ} {N : ℕ} (C : SidonFactorCover U)
    (hSidon : UnorderedProductUnique U)
    {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (_hz : 0 ≤ z)
    (hlargeLeft : (C.largeLeft.card : ℝ) ≤ x)
    (hlargeRight : (C.largeRight.card : ℝ) ≤ Nat.primeCounting N)
    (hbalancedLeft : (C.balancedLeft.card : ℝ) ≤ y)
    (hbalancedRight : (C.balancedRight.card : ℝ) ≤ z) :
    (U.card : ℝ) - 1 - Nat.primeCounting N ≤
      x ^ 2 / 2 + z + y * Real.sqrt z := by
  have hlargeFree : Bipartite.C4Free C.largeEdges :=
    c4Free_of_unorderedProductUnique C.large_products_mem
      C.large_product_injective hSidon
  have hbalancedFree : Bipartite.C4Free C.balancedEdges :=
    c4Free_of_unorderedProductUnique C.balanced_products_mem
      C.balanced_product_injective hSidon
  have hlargeCount :
      (C.largeEdges.card : ℝ) ≤
        (C.largeRight.card : ℝ) +
          (Nat.choose C.largeLeft.card 2 : ℝ) := by
    have hcount := GammaBound.edgeCount_le_card_add_choose hlargeFree
      C.largeLeft C.largeRight
    rw [GammaBound.edgeCount_eq_card_of_subset_product C.large_supported] at hcount
    exact_mod_cast hcount
  have hchoose :
      (Nat.choose C.largeLeft.card 2 : ℝ) ≤ x ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    have hcard_nonneg : 0 ≤ (C.largeLeft.card : ℝ) := by positivity
    nlinarith
  have hlarge :
      (C.largeEdges.card : ℝ) ≤
        (Nat.primeCounting N : ℝ) + x ^ 2 / 2 := by
    exact hlargeCount.trans (add_le_add hlargeRight hchoose)
  have hbalancedCount :
      (C.balancedEdges.card : ℝ) ≤
        (C.balancedRight.card : ℝ) +
          (C.balancedLeft.card : ℝ) *
            Real.sqrt (C.balancedRight.card : ℝ) := by
    rw [← GammaBound.edgeCount_eq_card_of_subset_product C.balanced_supported]
    exact edgeCount_le_card_add_card_mul_sqrt hbalancedFree
      C.balancedLeft C.balancedRight
  have hsqrt_mono :
      Real.sqrt (C.balancedRight.card : ℝ) ≤ Real.sqrt z :=
    Real.sqrt_le_sqrt hbalancedRight
  have hbalanced :
      (C.balancedEdges.card : ℝ) ≤ z + y * Real.sqrt z := by
    refine hbalancedCount.trans ?_
    gcongr
  have hcoverNat := card_erase_le_edge_cards C
  have hcover :
      ((U.erase 1).card : ℝ) ≤
        (C.largeEdges.card : ℝ) + C.balancedEdges.card := by
    exact_mod_cast hcoverNat
  have herase := card_sub_one_le_card_erase U
  linarith

/-- The manuscript's numerical exponents, conditional only on the explicit
finite factor cover.  This is the exact output of the two `C₄` counts.
-/
theorem card_sub_one_sub_primeCounting_le_rpow
    {U : Finset ℕ} {N : ℕ} (hN : 1 ≤ N) (C : SidonFactorCover U)
    (hSidon : UnorderedProductUnique U)
    (hlargeLeft :
      (C.largeLeft.card : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (hlargeRight : (C.largeRight.card : ℝ) ≤ Nat.primeCounting N)
    (hbalancedLeft :
      (C.balancedLeft.card : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ))
    (hbalancedRight :
      (C.balancedRight.card : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ)) :
    (U.card : ℝ) - 1 - Nat.primeCounting N ≤
      (N : ℝ) ^ (5 / 6 : ℝ) +
        (3 / 2 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) := by
  let n : ℝ := N
  have hn : 0 < n := by
    have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
    have hNposReal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    simpa [n] using! hNposReal
  have hcore := card_sub_one_sub_primeCounting_le_of_factorCover C hSidon
    (x := n ^ (1 / 3 : ℝ)) (y := n ^ (1 / 2 : ℝ))
    (z := n ^ (2 / 3 : ℝ))
    (Real.rpow_nonneg hn.le _) (Real.rpow_nonneg hn.le _)
    (Real.rpow_nonneg hn.le _) hlargeLeft hlargeRight hbalancedLeft hbalancedRight
  have hx2 : (n ^ (1 / 3 : ℝ)) ^ 2 = n ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hn.le]
    norm_num
  have hsqrt : Real.sqrt (n ^ (2 / 3 : ℝ)) = n ^ (1 / 3 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      (n ^ (2 / 3 : ℝ)) ^ (1 / 2 : ℝ) =
          n ^ ((2 / 3 : ℝ) * (1 / 2 : ℝ)) :=
        (Real.rpow_mul hn.le _ _).symm
      _ = n ^ (1 / 3 : ℝ) := by norm_num
  have hprod :
      n ^ (1 / 2 : ℝ) * n ^ (1 / 3 : ℝ) = n ^ (5 / 6 : ℝ) := by
    rw [← Real.rpow_add hn]
    norm_num
  dsimp [n] at hcore hx2 hsqrt hprod ⊢
  rw [hx2, hsqrt, hprod] at hcore
  linarith

/-- The explicit multiplicative-Sidon bound from the manuscript.  The lower
cutoff `8` is only used to ensure `N^(1/3) ≥ 2` in the balanced-factor lemma. -/
theorem multiplicativeSidon_card_bound {N : ℕ} (hN : 8 ≤ N)
    {U : Finset ℕ} (hU : U ⊆ positiveIcc N)
    (hSidon : UnorderedProductUnique U) :
    (U.card : ℝ) - 1 - Nat.primeCounting N ≤
      (N : ℝ) ^ (5 / 6 : ℝ) +
        (3 / 2 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) := by
  let C := canonicalFactorCover U hN hU
  apply card_sub_one_sub_primeCounting_le_rpow (by omega) C hSidon
  · simpa [C, canonicalFactorCover, thirdScale] using! card_largeLeft_le N
  · simp [C, canonicalFactorCover, card_largeRight]
  · simpa [C, canonicalFactorCover, halfScale] using! card_balancedLeft_le N
  · simpa [C, canonicalFactorCover, twoThirdScale] using! card_balancedRight_le N

/-- Every sufficiently large fibre of a compatible family satisfies the
uniform `5/6`-power excess bound. -/
theorem compatible_fiber_card_bound {U : ℕ → Finset ℕ} (hU : Compatible U)
    {j : ℕ} (hj : 8 ≤ j) :
    ((U j).card : ℝ) - 1 - Nat.primeCounting j ≤
      (j : ℝ) ^ (5 / 6 : ℝ) +
        (3 / 2 : ℝ) * (j : ℝ) ^ (2 / 3 : ℝ) := by
  exact multiplicativeSidon_card_bound hj (hU.1 j)
    (compatible_fiber_unorderedProductUnique hU j)

/-- The same bound in the manuscript's `excess` notation. -/
theorem compatible_fiber_excess_le {U : ℕ → Finset ℕ} (hU : Compatible U)
    {j : ℕ} (hj : 8 ≤ j) :
    excess U j ≤
      (j : ℝ) ^ (5 / 6 : ℝ) +
        (3 / 2 : ℝ) * (j : ℝ) ^ (2 / 3 : ℝ) := by
  have h := compatible_fiber_card_bound hU hj
  simpa [excess, excessInt, Int.cast_sub, Int.cast_natCast] using! h

end SidonCardBound

end Erdos796
