import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Binomial and subset-counting bounds for Erdős problem 565

The container argument repeatedly chooses a fingerprint having at most a
small fraction of the ambient vertices.  This file records the required
finite counting statements.  In particular, `floorFingerprintCount_le`
keeps the cutoff as the literal natural-number floor `n / d`; there is no
suppressed integrality convention.

The exponential estimate is deliberately division-free at its interface.
Its constant `8` (rather than an asymptotically optimal constant) absorbs
both `Real.exp 1 < 3` and the possible final incomplete block in `n / d`.
-/

open scoped BigOperators

namespace Erdos565
namespace BinomialBounds

variable {α : Type*}

/-- The finite family of subsets of `L` having cardinality at most `s`. -/
def subsetsUpTo [DecidableEq α] (L : Finset α) (s : ℕ) : Finset (Finset α) :=
  L.powerset.filter fun A ↦ A.card ≤ s

@[simp]
theorem mem_subsetsUpTo [DecidableEq α] {L A : Finset α} {s : ℕ} :
    A ∈ subsetsUpTo L s ↔ A ⊆ L ∧ A.card ≤ s := by
  simp [subsetsUpTo]

/-- The number of subsets of size at most `s` is the corresponding partial
sum of a row of Pascal's triangle.  The formula remains valid when `s` is
larger than `L.card`, since the extra binomial coefficients vanish. -/
theorem card_subsetsUpTo_eq_sum_choose [DecidableEq α] (L : Finset α) (s : ℕ) :
    (subsetsUpTo L s).card = ∑ i ∈ Finset.range (s + 1), L.card.choose i := by
  classical
  rw [show subsetsUpTo L s =
      Finset.biUnion (Finset.range (s + 1)) (fun i ↦ L.powersetCard i) by
        ext A
        simp only [mem_subsetsUpTo, Finset.mem_biUnion, Finset.mem_range,
          Finset.mem_powersetCard]
        constructor
        · rintro ⟨hAL, hAs⟩
          exact ⟨A.card, Nat.lt_succ_of_le hAs, hAL, rfl⟩
        · rintro ⟨i, hi, hAL, hAi⟩
          exact ⟨hAL, hAi.symm ▸ Nat.le_of_lt_succ hi⟩,
    Finset.card_biUnion]
  · simp [Finset.card_powersetCard]
  · intro i hi j hj hij
    exact Finset.disjoint_left.mpr fun A hAi hAj ↦ hij <| by
      have hiA := (Finset.mem_powersetCard.mp hAi).2
      have hjA := (Finset.mem_powersetCard.mp hAj).2
      omega

/-- Exact count of the `s`-subsets of `L` which contain a fixed `T`.
This is a direct finite form of the containment probability used later. -/
theorem card_fixedSize_containing [DecidableEq α]
    (T L : Finset α) (s : ℕ) (hTL : T ⊆ L) (hTs : T.card ≤ s) :
    ((L.powersetCard s).filter (T ⊆ ·)).card =
      (L.card - T.card).choose (s - T.card) := by
  exact Finset.card_filter_powersetCard_subset T L s hTL hTs

/-- Division-free form of the binomial containment ratio
`C(n-t,s-t) / C(n,s) = C(s,t) / C(n,t)`. -/
theorem choose_containment_ratio (n s t : ℕ) (hts : t ≤ s) :
    n.choose s * s.choose t = n.choose t * (n - t).choose (s - t) := by
  exact Nat.choose_mul hts

/-- The exact containment count and the ratio identity combined, in a form
that can be used without division or nonzero side conditions. -/
theorem card_fixedSize_containing_mul_choose [DecidableEq α]
    (T L : Finset α) (s : ℕ) (hTL : T ⊆ L) (hTs : T.card ≤ s) :
    ((L.powersetCard s).filter (T ⊆ ·)).card * L.card.choose T.card =
      L.card.choose s * s.choose T.card := by
  rw [card_fixedSize_containing T L s hTL hTs]
  simpa [mul_comm] using (choose_containment_ratio L.card s T.card hTs).symm

/-- A weighted powerset estimate.  If `4 * |L| ≤ K * s`, then the number of
subsets of `L` of size at most `s` is at most `K^s`.  The proof is the usual
entropy calculation with `x=s/|L|`, written as an elementary finite sum. -/
theorem card_subsetsUpTo_le_pow_real [DecidableEq α]
    {L : Finset α} {s K : ℕ} (hs : 0 < s) (hsL : s ≤ L.card)
    (hscale : 4 * L.card ≤ K * s) :
    ((subsetsUpTo L s).card : ℝ) ≤ (K : ℝ) ^ s := by
  let x : ℝ := (s : ℝ) / L.card
  have hL : 0 < L.card := hs.trans_le hsL
  have hx : 0 < x := div_pos (by exact_mod_cast hs) (by exact_mod_cast hL)
  have hx1 : x ≤ 1 := by
    dsimp [x]
    rw [div_le_one (by exact_mod_cast hL)]
    exact_mod_cast hsL
  have hweighted :
      ((subsetsUpTo L s).card : ℝ) * x ^ s ≤ (x + 1) ^ L.card := by
    calc
      ((subsetsUpTo L s).card : ℝ) * x ^ s =
          ∑ A ∈ subsetsUpTo L s, x ^ s := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ A ∈ subsetsUpTo L s, x ^ A.card := by
        apply Finset.sum_le_sum
        intro A hA
        exact pow_le_pow_of_le_one hx.le hx1 (mem_subsetsUpTo.mp hA).2
      _ ≤ ∑ A ∈ L.powerset, x ^ A.card := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro A hA
          exact Finset.mem_powerset.mpr (mem_subsetsUpTo.mp hA).1
        · intro A _ _
          positivity
      _ = (x + 1) ^ L.card := by
        simpa using Finset.sum_pow_mul_eq_add_pow x 1 L
  have hexp : (x + 1) ^ L.card ≤ Real.exp 1 ^ s := by
    calc
      (x + 1) ^ L.card ≤ Real.exp x ^ L.card :=
        pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp x) _
      _ = Real.exp ((L.card : ℝ) * x) := by
        rw [← Real.exp_nat_mul]
      _ = Real.exp (s : ℝ) := by
        congr 1
        dsimp [x]
        field_simp
      _ = Real.exp 1 ^ s := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hKx : Real.exp 1 ≤ (K : ℝ) * x := by
    have hscaleR : (4 : ℝ) * L.card ≤ (K : ℝ) * s := by
      exact_mod_cast hscale
    have hfour : (4 : ℝ) ≤ (K : ℝ) * x := by
      dsimp [x]
      calc
        (4 : ℝ) ≤ ((K : ℝ) * s) / L.card :=
          (le_div_iff₀ (by exact_mod_cast hL)).2 (by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hscaleR)
        _ = (K : ℝ) * ((s : ℝ) / L.card) := by ring
    exact Real.exp_one_lt_three.le.trans ((by norm_num : (3 : ℝ) ≤ 4).trans hfour)
  have hcancel :
      ((subsetsUpTo L s).card : ℝ) * x ^ s ≤ (K : ℝ) ^ s * x ^ s := by
    calc
      ((subsetsUpTo L s).card : ℝ) * x ^ s ≤ (x + 1) ^ L.card := hweighted
      _ ≤ Real.exp 1 ^ s := hexp
      _ ≤ ((K : ℝ) * x) ^ s :=
        pow_le_pow_left₀ (Real.exp_pos 1).le hKx _
      _ = (K : ℝ) ^ s * x ^ s := by rw [mul_pow]
  exact le_of_mul_le_mul_right hcancel (pow_pos hx s)

/-- Natural-number version of the weighted powerset bound. -/
theorem card_subsetsUpTo_le_pow [DecidableEq α]
    {L : Finset α} {s K : ℕ} (hs : 0 < s) (hsL : s ≤ L.card)
    (hscale : 4 * L.card ≤ K * s) :
    (subsetsUpTo L s).card ≤ K ^ s := by
  exact_mod_cast card_subsetsUpTo_le_pow_real hs hsL hscale

/-- Entropy bound with the cutoff written as the exact floor `|L| / d`.
The case in which this floor is zero is treated separately; otherwise
`|L| < d * (|L|/d + 1) ≤ 2*d*(|L|/d)` supplies the factor `8`. -/
theorem floorFingerprintCount_le [DecidableEq α]
    (L : Finset α) (d : ℕ) (hd : 0 < d) :
    (subsetsUpTo L (L.card / d)).card ≤ (8 * d) ^ (L.card / d) := by
  by_cases hs0 : L.card / d = 0
  · have hzero : subsetsUpTo L 0 = {∅} := by
      ext A
      rw [mem_subsetsUpTo, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hcard⟩
        exact Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      · rintro rfl
        simp
    simp [hs0, hzero]
  · have hs : 0 < L.card / d := Nat.pos_of_ne_zero hs0
    have hsL : L.card / d ≤ L.card :=
      (Nat.div_le_self _ _)
    apply card_subsetsUpTo_le_pow hs hsL
    have hlt : L.card < d * (L.card / d + 1) := by
      simpa [Nat.succ_eq_add_one, Nat.mul_comm] using
        (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (L.card / d))
    have hsucc : L.card / d + 1 ≤ 2 * (L.card / d) := by omega
    calc
      4 * L.card ≤ 4 * (d * (L.card / d + 1)) :=
        Nat.mul_le_mul_left 4 hlt.le
      _ ≤ 4 * (d * (2 * (L.card / d))) :=
        Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left d hsucc)
      _ = (8 * d) * (L.card / d) := by ring

/-- The same estimate as a partial binomial-sum bound. -/
theorem partialChooseSum_floor_le (n d : ℕ) (hd : 0 < d) :
    (∑ i ∈ Finset.range (n / d + 1), n.choose i) ≤ (8 * d) ^ (n / d) := by
  let L : Finset (Fin n) := Finset.univ
  have h := floorFingerprintCount_le L d hd
  simpa [L, card_subsetsUpTo_eq_sum_choose] using h

/-- Two independently chosen fingerprints, with floor cutoffs `n/d` and
`m/d`, have at most the product entropy count shown here. -/
theorem mul_partialChooseSum_floor_le (n m d : ℕ) (hd : 0 < d) :
    (∑ i ∈ Finset.range (n / d + 1), n.choose i) *
        (∑ j ∈ Finset.range (m / d + 1), m.choose j) ≤
      (8 * d) ^ (n / d + m / d) := by
  calc
    (∑ i ∈ Finset.range (n / d + 1), n.choose i) *
          (∑ j ∈ Finset.range (m / d + 1), m.choose j)
        ≤ (8 * d) ^ (n / d) * (8 * d) ^ (m / d) :=
      Nat.mul_le_mul (partialChooseSum_floor_le n d hd)
        (partialChooseSum_floor_le m d hd)
    _ = (8 * d) ^ (n / d + m / d) := by rw [pow_add]

end BinomialBounds
end Erdos565
