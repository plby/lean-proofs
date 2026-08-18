/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos921.Definitions
import ErdosProblems.Erdos921.Padding
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

open Filter Function Set SimpleGraph
open scoped ENat NNReal Topology

namespace Erdos921

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Exact finite lower construction -/

lemma stableKneser_chromaticNumber {r d : ℕ} (hr : 0 < r) :
    (stableKneser (2 * r + d) r).chromaticNumber = ((d + 2 : ℕ) : ℕ∞) := by
  have h := (chromaticNumber_eq_iff_colorable_not_colorable
    (G := stableKneser (2 * r + d) r) (n := d + 1)).2
      ⟨stableKneser_colorable hr, stableKneser_not_colorable hr⟩
  calc
    (stableKneser (2 * r + d) r).chromaticNumber =
        ((d + 1 : ℕ) : ℕ∞) + 1 := h
    _ = (((d + 1) + 1 : ℕ) : ℕ∞) := by
      simpa using (Nat.cast_add (R := ℕ∞) (d + 1) 1).symm
    _ = ((d + 2 : ℕ) : ℕ∞) := by congr 1 <;> omega

lemma stableKneser_no_short_odd_cycle {r d : ℕ} (hr : 0 < r)
    (hd : 0 < d) :
    ¬ HasOddCycleAtMost (stableKneser (2 * r + d) r) (r / d) := by
  rintro ⟨v, w, _hwc, hwo, hwlen⟩
  have hb := stableKneser_cycle_bound hr hwo
  have hlenpos : 0 < w.length := Odd.pos hwo
  have hhalf : w.length / 2 < w.length :=
    Nat.div_lt_self hlenpos (by omega)
  have hmul_lt : (w.length / 2) * d < w.length * d :=
    Nat.mul_lt_mul_of_pos_right hhalf hd
  have hmul_le : w.length * d ≤ r :=
    (Nat.le_div_iff_mul_le hd).mp hwlen
  omega

/-- The padded stable-Kneser construction, stated directly in the extremal
predicate of Problem 921. -/
theorem stableKneser_admissible {d r n : ℕ} (hd : 0 < d) (hr : 0 < r)
    (hcard : Fintype.card (StableSet (2 * r + d) r) ≤ n) :
    Admissible (d + 2) n (r / d) := by
  let G := stableKneser (2 * r + d) r
  refine ⟨padGraph G hcard, ?_, padGraph_no_short_odd_cycle hcard
    (stableKneser_no_short_odd_cycle hr hd)⟩
  apply padGraph_chromaticNumber (c := d + 2) (by omega) hcard
  · exact stableKneser_colorable hr
  · change ¬(stableKneser (2 * r + d) r).Colorable (d + 2 - 1)
    simpa only [show d + 2 - 1 = d + 1 by omega] using
      stableKneser_not_colorable hr

/-! ## Pointwise KST upper bound -/

theorem admissible_lt_kst_bound {k n m : ℕ} (hk : 4 ≤ k)
    (h : Admissible k n m) :
    m < 4 * (k - 2) * (Nat.nthRoot (k - 2) n + 1) + 1 := by
  obtain ⟨G, hχ, hodd⟩ := h
  let d := k - 2
  let a := Nat.nthRoot d n + 1
  have hd : 0 < d := by omega
  have ha : 0 < a := by simp [a]
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst n
    have hcard := G.chromaticNumber_le_card
    rw [hχ] at hcard
    simp at hcard
    omega
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hcard : Fintype.card (Fin n) ≤ a ^ d := by
    simp only [Fintype.card_fin]
    exact (Nat.lt_pow_nthRoot_add_one hd.ne' n).le
  by_contra hm
  have hcut : 4 * d * a + 1 ≤ m := by
    change ¬ m < 4 * d * a + 1 at hm
    omega
  have hnoshort : ¬ HasOddCycleAtMost G (4 * d * a + 1) := by
    intro hshort
    apply hodd
    obtain ⟨v, w, hwc, hwo, hwlen⟩ := hshort
    exact ⟨v, w, hwc, hwo, hwlen.trans hcut⟩
  have hcol : G.Colorable (d + 1) :=
    colorable_of_no_short_odd_cycle ha hcard hnoshort
  have hχle := hcol.chromaticNumber_le
  rw [hχ] at hχle
  change (k : ℕ∞) ≤ ((d + 1 : ℕ) : ℕ∞) at hχle
  have hnat : k ≤ d + 1 := by exact_mod_cast hχle
  omega

theorem f_lt_kst_bound {k n : ℕ} (hk : 4 ≤ k) :
    f k n < 4 * (k - 2) * (Nat.nthRoot (k - 2) n + 1) + 1 := by
  by_cases hf : f k n = 0
  · simp [hf]
  · have hfpos : 0 < f k n := Nat.pos_of_ne_zero hf
    obtain ⟨m, hmpos, hmn, hmad⟩ := (Nat.findGreatest_pos.mp hfpos)
    have hspec : Admissible k n (f k n) :=
      Nat.findGreatest_spec hmn hmad
    exact admissible_lt_kst_bound hk hspec

/-! ## A uniform choice of the stable-Kneser parameter -/

/-- The fixed denominator used to choose the stable-set size from an integer
`d`-th root. -/
def lowerDivisor (d : ℕ) : ℕ := 4 * (d + 2)

/-- The stable-set size used for the lower construction. -/
def lowerParameter (d n : ℕ) : ℕ :=
  Nat.nthRoot d n / lowerDivisor d

lemma lowerParameter_pos_and_card {d n : ℕ} (hd : 2 ≤ d)
    (hn : (lowerDivisor d * d) ^ d ≤ n) :
    0 < lowerParameter d n ∧
      Fintype.card (StableSet (2 * lowerParameter d n + d) (lowerParameter d n)) ≤ n := by
  let s := Nat.nthRoot d n
  let A := lowerDivisor d
  let r := lowerParameter d n
  have hdpos : 0 < d := by omega
  have hApos : 0 < A := by simp [A, lowerDivisor]
  have hAs : A * d ≤ s := by
    rw [Nat.le_nthRoot_iff hdpos.ne']
    exact hn
  have hdr : d ≤ r := by
    dsimp [r, lowerParameter, A]
    rw [Nat.le_div_iff_mul_le hApos]
    simpa [Nat.mul_comm] using hAs
  have hr : 0 < r := lt_of_lt_of_le hdpos hdr
  refine ⟨hr, ?_⟩
  have hbasic := stableSet_card_le (d := d) hr
  have hN : 2 * r + d ≤ 3 * r := by omega
  have hdiv : A * r ≤ s := by
    simpa [A, r, lowerParameter] using Nat.mul_div_le s A
  have hscaled : (d + 2) * (3 * r) ≤ s := by
    calc
      (d + 2) * (3 * r) ≤ A * r := by
        dsimp [A, lowerDivisor]
        nlinarith
      _ ≤ s := hdiv
  have hcoeff : d + 2 ≤ (d + 2) ^ d :=
    Nat.le_pow (by omega)
  have hsPow : s ^ d ≤ n := by
    exact Nat.pow_nthRoot_le (.inl hdpos.ne')
  calc
    Fintype.card (StableSet (2 * r + d) r)
        ≤ (d + 2) * (2 * r + d) ^ d := hbasic
    _ ≤ (d + 2) * (3 * r) ^ d :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN d)
    _ ≤ (d + 2) ^ d * (3 * r) ^ d :=
      Nat.mul_le_mul_right _ hcoeff
    _ = ((d + 2) * (3 * r)) ^ d := (mul_pow _ _ _).symm
    _ ≤ s ^ d := Nat.pow_le_pow_left hscaled d
    _ ≤ n := hsPow

lemma nthRoot_le_self {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    Nat.nthRoot d n ≤ n := by
  rw [← Nat.pow_le_pow_iff_left hd.ne']
  exact (Nat.pow_nthRoot_le (.inl hd.ne')).trans
    (Nat.le_pow hd)

theorem lowerParameter_div_le_f {d n : ℕ} (hd : 2 ≤ d)
    (hn : (lowerDivisor d * d) ^ d ≤ n) :
    lowerParameter d n / d ≤ f (d + 2) n := by
  obtain ⟨hr, hcard⟩ := lowerParameter_pos_and_card hd hn
  have hbase : 0 < lowerDivisor d * d :=
    Nat.mul_pos (by simp [lowerDivisor]) (by omega)
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.pow_pos hbase) hn
  have hsle : Nat.nthRoot d n ≤ n := nthRoot_le_self (by omega) hnpos
  have hmle : lowerParameter d n / d ≤ n := by
    exact (Nat.div_le_self _ _).trans
      ((Nat.div_le_self _ _).trans hsle)
  exact le_f_of_admissible hmle
    (stableKneser_admissible (by omega) hr hcard)

/-! ## Relating integer roots to the real scale -/

def rootScale (d n : ℕ) : ℝ :=
  (n : ℝ) ^ ((d : ℝ)⁻¹)

lemma nthRoot_cast_le_rootScale {d n : ℕ} (hd : 0 < d) :
    (Nat.nthRoot d n : ℝ) ≤ rootScale d n := by
  rw [rootScale, Real.le_rpow_inv_iff_of_pos (by positivity) (by positivity)
    (by exact_mod_cast hd)]
  rw [Real.rpow_natCast]
  exact_mod_cast Nat.pow_nthRoot_le (.inl hd.ne')

lemma rootScale_lt_nthRoot_add_one {d n : ℕ} (hd : 0 < d) :
    rootScale d n < Nat.nthRoot d n + 1 := by
  rw [rootScale, Real.rpow_inv_lt_iff_of_pos (by positivity) (by positivity)
    (by exact_mod_cast hd)]
  rw [Real.rpow_natCast]
  exact_mod_cast Nat.lt_pow_nthRoot_add_one hd.ne' n

lemma rootScale_nonneg (d n : ℕ) : 0 ≤ rootScale d n :=
  Real.rpow_nonneg (by positivity) _

/-! ## Real-valued pointwise estimates -/

lemma f_cast_le_rootScale_mul {d n : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n) :
    (f (d + 2) n : ℝ) ≤ (8 * d + 1 : ℝ) * rootScale d n := by
  have hf0 := f_lt_kst_bound (k := d + 2) (n := n) (by omega)
  have hf : f (d + 2) n < 4 * d * (Nat.nthRoot d n + 1) + 1 := by
    simpa only [Nat.add_sub_cancel] using hf0
  have hfc : (f (d + 2) n : ℝ) <
      4 * d * (Nat.nthRoot d n + 1) + 1 := by
    exact_mod_cast hf
  have hs := nthRoot_cast_le_rootScale (d := d) (n := n) (by omega)
  have hrootOne : 1 ≤ rootScale d n := by
    apply Real.one_le_rpow
    · exact_mod_cast hn
    · positivity
  push_cast at hfc
  nlinarith [rootScale_nonneg d n]

lemma rootScale_le_f_cast_mul {d n : ℕ} (hd : 2 ≤ d)
    (hn : (lowerDivisor d * d) ^ d ≤ n) :
    rootScale d n ≤ (2 * (lowerDivisor d * d) : ℝ) * f (d + 2) n := by
  let s := Nat.nthRoot d n
  let B := lowerDivisor d * d
  let m := lowerParameter d n / d
  have hdpos : 0 < d := by omega
  have hBpos : 0 < B := Nat.mul_pos (by simp [B, lowerDivisor]) hdpos
  have hBs : B ≤ s := by
    rw [Nat.le_nthRoot_iff hdpos.ne']
    exact hn
  have hmdef : m = s / B := by
    dsimp [m, s, B, lowerParameter]
    exact Nat.div_div_eq_div_mul _ _ _
  have hmpos : 0 < m := by
    have hmone : 1 ≤ m := by
      rw [hmdef, Nat.le_div_iff_mul_le hBpos]
      simpa using hBs
    omega
  have hslt : s < (m + 1) * B := by
    rw [hmdef]
    exact (Nat.div_lt_iff_lt_mul hBpos).mp (Nat.lt_succ_self _)
  have hsadd : s + 1 ≤ (m + 1) * B := hslt
  have hmle : m ≤ f (d + 2) n := lowerParameter_div_le_f hd hn
  have hroot := rootScale_lt_nthRoot_add_one (d := d) (n := n) hdpos
  have hroot' : rootScale d n < (s + 1 : ℕ) := by simpa [s] using hroot
  have hmposR : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  have hsaddR : (s + 1 : ℝ) ≤ (m + 1) * B := by exact_mod_cast hsadd
  have hmleR : (m : ℝ) ≤ f (d + 2) n := by exact_mod_cast hmle
  rw [Nat.cast_add, Nat.cast_one] at hroot'
  push_cast at hsaddR
  calc
    rootScale d n ≤ (s : ℝ) + 1 := hroot'.le
    _ ≤ ((m : ℝ) + 1) * B := hsaddR
    _ ≤ (2 * (m : ℝ)) * B := by
      gcongr
      nlinarith
    _ = 2 * B * (m : ℝ) := by ring
    _ ≤ 2 * B * f (d + 2) n := by
      gcongr
    _ = (2 * (lowerDivisor d * d) : ℝ) * f (d + 2) n := by
      dsimp [B]
      push_cast
      ring

/-! ## The asymptotic theorem -/

theorem f_isBigO_rootScale (d : ℕ) (hd : 2 ≤ d) :
    (fun n : ℕ ↦ (f (d + 2) n : ℝ)) =O[atTop] rootScale d := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨(8 * d + 1 : ℝ), ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (f (d + 2) n : ℝ)),
    abs_of_nonneg (rootScale_nonneg d n)]
  exact f_cast_le_rootScale_mul hd hn

theorem rootScale_isBigO_f (d : ℕ) (hd : 2 ≤ d) :
    rootScale d =O[atTop] (fun n : ℕ ↦ (f (d + 2) n : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨(2 * (lowerDivisor d * d) : ℝ), ?_⟩
  filter_upwards [eventually_ge_atTop ((lowerDivisor d * d) ^ d)] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (rootScale_nonneg d n),
    abs_of_nonneg (by positivity : 0 ≤ (f (d + 2) n : ℝ))]
  exact rootScale_le_f_cast_mul hd hn

theorem erdos_921_aux (d : ℕ) (hd : 2 ≤ d) :
    (fun n : ℕ ↦ (f (d + 2) n : ℝ)) =Θ[atTop] rootScale d :=
  ⟨f_isBigO_rootScale d hd, rootScale_isBigO_f d hd⟩

end

end Erdos921
