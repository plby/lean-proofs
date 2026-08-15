import ErdosProblems.Erdos888.Foundations
import ErdosProblems.Erdos888.SquarePart
import Mathlib.Analysis.PSeries

/-!
# Erdős Problem 888: reduction to squarefree integers

This file partitions an admissible set according to the root of the exact
square dividing each of its elements.  On a fixed fiber, division by that
square is injective and produces an admissible set of squarefree integers.
Consequently the unrestricted extremal function is bounded by a sum of the
squarefree extremal function at the rescaled parameters.
-/

open Filter

namespace Erdos888

open scoped BigOperators

/-- All members of a finite set are squarefree. -/
def IsSquarefreeSet (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, Squarefree a

/-- There is a squarefree admissible set of cardinality `k`. -/
def squarefreeP (n k : ℕ) : Prop :=
  ∃ A : Finset ℕ, RequiredCondition A n ∧ IsSquarefreeSet A ∧ A.card = k

/-- The largest cardinality of a squarefree admissible subset of
`{1, ..., n}`. -/
noncomputable def squarefreeExtremalSize (n : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (squarefreeP n) n

theorem squarefreeP_zero (n : ℕ) : squarefreeP n 0 := by
  exact ⟨∅, requiredCondition_empty n, by simp [IsSquarefreeSet]⟩

theorem squarefreeP_le {n k : ℕ} (hk : squarefreeP n k) : k ≤ n := by
  obtain ⟨A, hA, -, rfl⟩ := hk
  exact requiredCondition_card_le hA

theorem squarefreeP_squarefreeExtremalSize (n : ℕ) :
    squarefreeP n (squarefreeExtremalSize n) := by
  classical
  unfold squarefreeExtremalSize
  exact Nat.findGreatest_spec (P := squarefreeP n) (m := 0)
    (Nat.zero_le n) (squarefreeP_zero n)

theorem squarefreeExtremalSize_le (n : ℕ) :
    squarefreeExtremalSize n ≤ n := by
  classical
  unfold squarefreeExtremalSize
  exact Nat.findGreatest_le n

theorem card_le_squarefreeExtremalSize {A : Finset ℕ} {n : ℕ}
    (hA : RequiredCondition A n) (hsf : IsSquarefreeSet A) :
    A.card ≤ squarefreeExtremalSize n := by
  classical
  unfold squarefreeExtremalSize
  exact Nat.le_findGreatest (P := squarefreeP n)
    (requiredCondition_card_le hA) ⟨A, hA, hsf, rfl⟩

/-- The squarefree cofactors occurring in the fiber with exact square-part
root `q`. -/
noncomputable def squarefreeImageFiber (A : Finset ℕ) (q : ℕ) : Finset ℕ := by
  classical
  exact (squarePartFiber A q).image squarefreePart

theorem mem_squarefreeImageFiber {A : Finset ℕ} {q s : ℕ} :
    s ∈ squarefreeImageFiber A q ↔
      ∃ a ∈ A, squarePartRoot a = q ∧ squarefreePart a = s := by
  classical
  simp only [squarefreeImageFiber, Finset.mem_image, mem_squarePartFiber]
  aesop

/-- On one exact-square-part fiber, the squarefree-cofactor map is
injective. -/
theorem injOn_squarefreePart_squarePartFiber (A : Finset ℕ) (q : ℕ) :
    Set.InjOn squarefreePart (squarePartFiber A q) := by
  intro a ha b hb hab
  exact eq_of_squarePartRoot_eq_of_squarefreePart_eq
    ((mem_squarePartFiber.mp ha).2.trans (mem_squarePartFiber.mp hb).2.symm) hab

/-- Passing to squarefree cofactors does not change the size of a fixed
exact-square-part fiber. -/
theorem card_squarefreeImageFiber (A : Finset ℕ) (q : ℕ) :
    (squarefreeImageFiber A q).card = (squarePartFiber A q).card := by
  classical
  exact Finset.card_image_iff.mpr (injOn_squarefreePart_squarePartFiber A q)

/-- Every cofactor in a positive exact-square-part fiber is positive and
squarefree. -/
theorem squarefreeImageFiber_isSquarefreeSet (A : Finset ℕ) (q : ℕ) :
    IsSquarefreeSet (squarefreeImageFiber A q) := by
  intro s hs
  obtain ⟨a, -, -, rfl⟩ := mem_squarefreeImageFiber.mp hs
  exact squarefreePart_squarefree a

/-- A cofactor in the `q`-fiber of a set contained in `{1, ..., n}` is at
most `n / q^2`. -/
theorem squarefreeImageFiber_subset_Ioc {A : Finset ℕ} {n q : ℕ}
    (hA : A ⊆ Finset.Ioc 0 n) (hq : 0 < q) :
    squarefreeImageFiber A q ⊆ Finset.Ioc 0 (n / q ^ 2) := by
  intro s hs
  obtain ⟨a, ha, hroot, hfree⟩ := mem_squarefreeImageFiber.mp hs
  have haIoc := Finset.mem_Ioc.mp (hA ha)
  have hspos : 0 < s := by
    rw [← hfree]
    exact squarefreePart_pos haIoc.1
  have hadecomp : q ^ 2 * s = a := by
    simpa [hroot, hfree] using squarePart_decomposition a
  have hmul : q ^ 2 * s ≤ n := by
    exact hadecomp.trans_le haIoc.2
  exact Finset.mem_Ioc.mpr
    ⟨hspos, (Nat.le_div_iff_mul_le (pow_pos hq 2)).2 (by simpa [Nat.mul_comm] using hmul)⟩

/-- Multiplying a square product by the four common square factors again
gives a square. -/
private theorem isSquare_common_square_factor {q a b c d : ℕ}
    (h : IsSquare (a * b * c * d)) :
    IsSquare ((q ^ 2 * a) * (q ^ 2 * b) * (q ^ 2 * c) * (q ^ 2 * d)) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨q ^ 4 * t, ?_⟩
  calc
    (q ^ 2 * a) * (q ^ 2 * b) * (q ^ 2 * c) * (q ^ 2 * d) =
        q ^ 8 * (a * b * c * d) := by ring
    _ = q ^ 8 * (t * t) := by rw [ht]
    _ = (q ^ 4 * t) * (q ^ 4 * t) := by ring

/-- The squarefree-cofactor image of a positive fixed-root fiber of an
admissible set is itself admissible at the rescaled parameter. -/
theorem requiredCondition_squarefreeImageFiber {A : Finset ℕ} {n q : ℕ}
    (hA : RequiredCondition A n) (hq : 0 < q) :
    RequiredCondition (squarefreeImageFiber A q) (n / q ^ 2) := by
  refine ⟨squarefreeImageFiber_subset_Ioc hA.1 hq, ?_⟩
  intro a ha b hb c hc d hd hab hbc hcd hsquare
  obtain ⟨a', ha'A, ha'root, ha'free⟩ := mem_squarefreeImageFiber.mp ha
  obtain ⟨b', hb'A, hb'root, hb'free⟩ := mem_squarefreeImageFiber.mp hb
  obtain ⟨c', hc'A, hc'root, hc'free⟩ := mem_squarefreeImageFiber.mp hc
  obtain ⟨d', hd'A, hd'root, hd'free⟩ := mem_squarefreeImageFiber.mp hd
  have ha'decomp : q ^ 2 * a = a' := by
    rw [← ha'root, ← ha'free]
    exact squarePart_decomposition a'
  have hb'decomp : q ^ 2 * b = b' := by
    rw [← hb'root, ← hb'free]
    exact squarePart_decomposition b'
  have hc'decomp : q ^ 2 * c = c' := by
    rw [← hc'root, ← hc'free]
    exact squarePart_decomposition c'
  have hd'decomp : q ^ 2 * d = d' := by
    rw [← hd'root, ← hd'free]
    exact squarePart_decomposition d'
  have hq2 : 0 < q ^ 2 := pow_pos hq 2
  have ha'b' : a' ≤ b' := by
    rw [← ha'decomp, ← hb'decomp]
    exact Nat.mul_le_mul_left _ hab
  have hb'c' : b' ≤ c' := by
    rw [← hb'decomp, ← hc'decomp]
    exact Nat.mul_le_mul_left _ hbc
  have hc'd' : c' ≤ d' := by
    rw [← hc'decomp, ← hd'decomp]
    exact Nat.mul_le_mul_left _ hcd
  have hadbc := hA.2 a' ha'A b' hb'A c' hc'A d' hd'A ha'b' hb'c' hc'd'
    (by rw [← ha'decomp, ← hb'decomp, ← hc'decomp, ← hd'decomp]
        exact isSquare_common_square_factor hsquare)
  rw [← ha'decomp, ← hb'decomp, ← hc'decomp, ← hd'decomp] at hadbc
  have hcancel : q ^ 4 * (a * d) = q ^ 4 * (b * c) := by
    calc
      q ^ 4 * (a * d) = (q ^ 2 * a) * (q ^ 2 * d) := by ring
      _ = (q ^ 2 * b) * (q ^ 2 * c) := hadbc
      _ = q ^ 4 * (b * c) := by ring
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hq 4) hcancel

/-- Every positive exact-square-part fiber is bounded by the squarefree
extremal function at the naturally rescaled parameter. -/
theorem card_squarePartFiber_le_squarefreeExtremalSize {A : Finset ℕ} {n q : ℕ}
    (hA : RequiredCondition A n) (hq : 0 < q) :
    (squarePartFiber A q).card ≤ squarefreeExtremalSize (n / q ^ 2) := by
  rw [← card_squarefreeImageFiber]
  exact card_le_squarefreeExtremalSize
    (requiredCondition_squarefreeImageFiber hA hq)
    (squarefreeImageFiber_isSquarefreeSet A q)

/-- The square-part roots which occur in a set contained in `{1, ..., n}`
also lie in `{1, ..., n}`. -/
theorem image_squarePartRoot_subset_Ioc {A : Finset ℕ} {n : ℕ}
    (hA : A ⊆ Finset.Ioc 0 n) :
    A.image squarePartRoot ⊆ Finset.Ioc 0 n := by
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  have haIoc := Finset.mem_Ioc.mp (hA ha)
  have hrootpos := squarePartRoot_pos haIoc.1
  have hrootle : squarePartRoot a ≤ a := by
    calc
      squarePartRoot a ≤ squarePartRoot a ^ 2 := by nlinarith
      _ ≤ a := squarePart_sq_le haIoc.1
  exact Finset.mem_Ioc.mpr ⟨hrootpos, hrootle.trans haIoc.2⟩

/-- The exact square-part partition gives the basic global reduction to the
squarefree extremal problem. -/
theorem card_le_sum_squarefreeExtremalSize {A : Finset ℕ} {n : ℕ}
    (hA : RequiredCondition A n) :
    A.card ≤ ∑ q ∈ Finset.Ioc 0 n,
      squarefreeExtremalSize (n / q ^ 2) := by
  rw [card_eq_sum_card_squarePartFiber A]
  calc
    ∑ q ∈ A.image squarePartRoot, (squarePartFiber A q).card
        ≤ ∑ q ∈ A.image squarePartRoot,
            squarefreeExtremalSize (n / q ^ 2) := by
          exact Finset.sum_le_sum fun q hq ↦
            card_squarePartFiber_le_squarefreeExtremalSize hA
              (Finset.mem_Ioc.mp (image_squarePartRoot_subset_Ioc hA.1 hq)).1
    _ ≤ ∑ q ∈ Finset.Ioc 0 n,
          squarefreeExtremalSize (n / q ^ 2) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (image_squarePartRoot_subset_Ioc hA.1) (fun _ _ _ ↦ Nat.zero_le _)

/-- In particular, the unrestricted extremal function is bounded by the
same square-part sum. -/
theorem extremalSize_le_sum_squarefreeExtremalSize (n : ℕ) :
    extremalSize n ≤ ∑ q ∈ Finset.Ioc 0 n,
      squarefreeExtremalSize (n / q ^ 2) := by
  obtain ⟨A, hA, hcard⟩ := exists_extremizer n
  rw [← hcard]
  exact card_le_sum_squarefreeExtremalSize hA

/-! ## The analytic cost of the square-part decomposition -/

/-- In the range `q^4 ≤ n`, the comparison scale at `n / q^2` is at
most a constant multiple of `scale n / q^2`.  Positivity is stated as a
hypothesis because that is exactly the eventual form used below. -/
theorem scale_div_square_le {n q : ℕ}
    (hn : 0 < n) (hq : 0 < q) (hq4 : q ^ 4 ≤ n)
    (hm4 : 4 ≤ n / q ^ 2)
    (hscale_m : 0 < scale (n / q ^ 2)) :
    scale (n / q ^ 2) ≤ 3 * scale n / (q : ℝ) ^ 2 := by
  let m := n / q ^ 2
  have hmpos : 0 < m := lt_of_lt_of_le (by omega : 0 < 4) hm4
  have hmle : m ≤ n := Nat.div_le_self n (q ^ 2)
  have hlogmpos : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlognpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by
      exact lt_of_lt_of_le (by omega : 1 < 4) (hm4.trans hmle)))
  have hlogmle : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (by exact_mod_cast hmpos : 0 < (m : ℝ))
      (by exact_mod_cast hn : 0 < (n : ℝ))
      (by exact_mod_cast hmle)
  have hloglogle :
      Real.log (Real.log (m : ℝ)) ≤ Real.log (Real.log (n : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn hlogmpos hlognpos hlogmle
  have hloglogmpos : 0 < Real.log (Real.log (m : ℝ)) := by
    rw [scale] at hscale_m
    rcases (div_pos_iff.mp hscale_m) with h | h
    · rcases mul_pos_iff.mp h.1 with hpos | hneg
      · exact hpos.2
      · exact (not_lt_of_ge (by positivity : (0 : ℝ) ≤ m) hneg.1).elim
    · exact (not_lt_of_ge hlogmpos.le h.2).elim
  have hloglognpos : 0 < Real.log (Real.log (n : ℝ)) :=
    hloglogmpos.trans_le hloglogle
  have hq2_le_m : q ^ 2 ≤ m := by
    apply (Nat.le_div_iff_mul_le (pow_pos hq 2)).2
    simpa [pow_succ, mul_assoc] using hq4
  have hn_lt : n < 2 * m ^ 2 := by
    have hdiv := Nat.lt_mul_div_succ n (pow_pos hq 2)
    have hstep : q ^ 2 * (m + 1) ≤ m * (m + 1) :=
      Nat.mul_le_mul_right (m + 1) hq2_le_m
    have hlast : m * (m + 1) ≤ 2 * m ^ 2 := by
      nlinarith
    exact hdiv.trans_le (hstep.trans hlast)
  have hlogn_le : Real.log (n : ℝ) ≤ 3 * Real.log (m : ℝ) := by
    calc
      Real.log (n : ℝ) ≤ Real.log (2 * (m : ℝ) ^ 2) :=
        Real.strictMonoOn_log.monotoneOn
          (by exact_mod_cast hn : 0 < (n : ℝ))
          (by positivity : 0 < (2 : ℝ) * (m : ℝ) ^ 2)
          (by exact_mod_cast hn_lt.le)
      _ = Real.log 2 + 2 * Real.log (m : ℝ) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
        norm_num
      _ ≤ Real.log (m : ℝ) + 2 * Real.log (m : ℝ) := by
        gcongr
        exact_mod_cast (show 2 ≤ m by omega)
      _ = 3 * Real.log (m : ℝ) := by ring
  have hm_div : (m : ℝ) ≤ (n : ℝ) / (q : ℝ) ^ 2 := by
    simpa [m, Nat.cast_pow] using (Nat.cast_div_le :
      ((n / q ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) / ((q ^ 2 : ℕ) : ℝ))
  have hmq : (m : ℝ) * (q : ℝ) ^ 2 ≤ (n : ℝ) :=
    (le_div_iff₀ (by positivity : 0 < (q : ℝ) ^ 2)).mp hm_div
  change scale m ≤ 3 * scale n / (q : ℝ) ^ 2
  rw [scale, scale]
  rw [show 3 * ((n : ℝ) * Real.log (Real.log (n : ℝ)) /
        Real.log (n : ℝ)) / (q : ℝ) ^ 2 =
      (3 * ((n : ℝ) * Real.log (Real.log (n : ℝ)))) /
        (Real.log (n : ℝ) * (q : ℝ) ^ 2) by ring]
  apply (div_le_div_iff₀ hlogmpos
    (mul_pos hlognpos (by positivity : 0 < (q : ℝ) ^ 2))).2
  calc
    ((m : ℝ) * Real.log (Real.log (m : ℝ))) *
          (Real.log (n : ℝ) * (q : ℝ) ^ 2) =
        ((m : ℝ) * (q : ℝ) ^ 2) *
          Real.log (Real.log (m : ℝ)) * Real.log (n : ℝ) := by ring
    _ ≤ (n : ℝ) * Real.log (Real.log (n : ℝ)) * Real.log (n : ℝ) := by
      gcongr
    _ ≤ (n : ℝ) * Real.log (Real.log (n : ℝ)) *
          (3 * Real.log (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hlogn_le
        (mul_nonneg (Nat.cast_nonneg n) hloglognpos.le)
    _ = 3 * ((n : ℝ) * Real.log (Real.log (n : ℝ))) *
          Real.log (m : ℝ) := by ring

/-- The fibers with `q^4 > n` contribute only a lower-order tail.  This
version records the uniform estimate needed for the eventual argument. -/
theorem large_squarePart_tail_le (n : ℕ) (hn : 1 < n)
    (hloglog : 1 ≤ Real.log (Real.log (n : ℝ))) :
    (∑ q ∈ (Finset.Ioc 0 n).filter (fun q ↦ n < q ^ 4),
        (squarefreeExtremalSize (n / q ^ 2) : ℝ)) ≤ 8 * scale n := by
  let k := Nat.sqrt (Nat.sqrt n)
  have hkpos : 0 < (k + 1 : ℕ) := by omega
  have hkcastpos : 0 < (k + 1 : ℝ) := by positivity
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlognpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn)
  have hn_lt_k : n < (k + 1) ^ 4 := by
    have hn_sqrt := Nat.lt_succ_sqrt n
    have hs_k := Nat.lt_succ_sqrt (Nat.sqrt n)
    have hs_le : Nat.sqrt n + 1 ≤ (k + 1) ^ 2 := by
      simpa [k, pow_two] using Nat.succ_le_of_lt hs_k
    calc
      n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := hn_sqrt
      _ ≤ ((k + 1) ^ 2) * ((k + 1) ^ 2) :=
        Nat.mul_le_mul hs_le hs_le
      _ = (k + 1) ^ 4 := by ring
  have hlogn_le_k : Real.log (n : ℝ) ≤ 4 * (k + 1 : ℝ) := by
    calc
      Real.log (n : ℝ) ≤ Real.log ((k + 1 : ℝ) ^ 4) :=
        Real.strictMonoOn_log.monotoneOn hnpos
          (pow_pos hkcastpos 4)
          (by exact_mod_cast hn_lt_k.le)
      _ = 4 * Real.log (k + 1 : ℝ) := by rw [Real.log_pow]; norm_num
      _ ≤ 4 * ((k + 1 : ℝ) - 1) := by
        gcongr
        exact Real.log_le_sub_one_of_pos hkcastpos
      _ ≤ 4 * (k + 1 : ℝ) := by linarith
  have htail_subset :
      (Finset.Ioc 0 n).filter (fun q ↦ n < q ^ 4) ⊆
        Finset.Ioo k (n + 1) := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqIoc := Finset.mem_Ioc.mp hq'.1
    apply Finset.mem_Ioo.mpr
    refine ⟨?_, by omega⟩
    by_contra hnot
    have hqk : q ≤ k := by omega
    have hk_sq : k ^ 2 ≤ Nat.sqrt n := by
      change (Nat.sqrt (Nat.sqrt n)) ^ 2 ≤ Nat.sqrt n
      simpa [pow_two] using Nat.sqrt_le (Nat.sqrt n)
    have hs_sq : (Nat.sqrt n) ^ 2 ≤ n := by
      simpa [pow_two] using Nat.sqrt_le n
    have hq4 : q ^ 4 ≤ n := by
      calc
        q ^ 4 ≤ k ^ 4 := Nat.pow_le_pow_left hqk 4
        _ = (k ^ 2) ^ 2 := by ring
        _ ≤ (Nat.sqrt n) ^ 2 := Nat.pow_le_pow_left hk_sq 2
        _ ≤ n := hs_sq
    exact (not_lt_of_ge hq4) hq'.2
  calc
    (∑ q ∈ (Finset.Ioc 0 n).filter (fun q ↦ n < q ^ 4),
        (squarefreeExtremalSize (n / q ^ 2) : ℝ))
        ≤ ∑ q ∈ (Finset.Ioc 0 n).filter (fun q ↦ n < q ^ 4),
            (n : ℝ) / (q : ℝ) ^ 2 := by
          gcongr with q hq
          exact (Nat.cast_le.mpr (squarefreeExtremalSize_le (n / q ^ 2))).trans
            (by simpa [Nat.cast_pow] using
              (Nat.cast_div_le : ((n / q ^ 2 : ℕ) : ℝ) ≤
                (n : ℝ) / ((q ^ 2 : ℕ) : ℝ)))
    _ ≤ ∑ q ∈ Finset.Ioo k (n + 1), (n : ℝ) / (q : ℝ) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg htail_subset
        (fun _ _ _ ↦ by positivity)
    _ = (n : ℝ) * ∑ q ∈ Finset.Ioo k (n + 1),
          ((q : ℝ) ^ 2)⁻¹ := by
      simp_rw [div_eq_mul_inv, Finset.mul_sum]
    _ ≤ (n : ℝ) * (2 / (k + 1 : ℝ)) := by
      gcongr
      exact (sum_Ioo_inv_sq_le k (n + 1) :
        (∑ q ∈ Finset.Ioo k (n + 1), ((q : ℝ) ^ 2)⁻¹) ≤
          2 / (k + 1 : ℝ))
    _ ≤ 8 * scale n := by
      have hfrac : 2 / (k + 1 : ℝ) ≤
          8 * Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ) := by
        apply (div_le_div_iff₀ hkcastpos hlognpos).2
        calc
          2 * Real.log (n : ℝ) ≤ 2 * (4 * (k + 1 : ℝ)) := by gcongr
          _ ≤ (8 * Real.log (Real.log (n : ℝ))) * (k + 1 : ℝ) := by
            nlinarith
      rw [scale]
      calc
        (n : ℝ) * (2 / (k + 1 : ℝ)) ≤
            (n : ℝ) * (8 * Real.log (Real.log (n : ℝ)) /
              Real.log (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg n)
        _ = 8 * ((n : ℝ) * Real.log (Real.log (n : ℝ)) /
              Real.log (n : ℝ)) := by ring

/-- The square-part reduction preserves an `O(n log log n / log n)` upper
bound.  This is the bridge from the squarefree core of the argument to the
original extremal problem. -/
theorem extremalSize_isBigO_of_squarefreeExtremalSize_isBigO
    (h : (fun n : ℕ ↦ (squarefreeExtremalSize n : ℝ)) =O[atTop] scale) :
    (fun n : ℕ ↦ (extremalSize n : ℝ)) =O[atTop] scale := by
  rw [Asymptotics.isBigO_iff] at h ⊢
  obtain ⟨C, hC⟩ := h
  have hloglog_one : ∀ᶠ n : ℕ in atTop,
      1 ≤ Real.log (Real.log (n : ℝ)) :=
    (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop 1)
  have hdata : ∀ᶠ m : ℕ in atTop,
      (squarefreeExtremalSize m : ℝ) ≤ |C| * scale m ∧
        0 < scale m ∧ 1 ≤ Real.log (Real.log (m : ℝ)) := by
    filter_upwards [hC, eventually_scale_pos, hloglog_one] with m hm hs hl
    refine ⟨?_, hs, hl⟩
    calc
      (squarefreeExtremalSize m : ℝ) =
          ‖(squarefreeExtremalSize m : ℝ)‖ := by simp
      _ ≤ C * ‖scale m‖ := hm
      _ = C * scale m := by rw [Real.norm_eq_abs, abs_of_pos hs]
      _ ≤ |C| * scale m := by gcongr; exact le_abs_self C
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hdata
  refine ⟨6 * |C| + 8, Filter.eventually_atTop.mpr ⟨
    max (N * (N + 1)) 20, ?_⟩⟩
  intro n hnlarge
  have hnN : N * (N + 1) ≤ n :=
    (le_max_left _ _).trans hnlarge
  have hn20 : 20 ≤ n :=
    (le_max_right (N * (N + 1)) 20).trans hnlarge
  have hn : 0 < n := by omega
  have hn1 : 1 < n := by omega
  have hNn : N ≤ n :=
    (Nat.le_mul_of_pos_right N (by omega : 0 < N + 1)).trans hnN
  have hnData := hN n hNn
  have hscaleN : 0 < scale n := hnData.2.1
  have hllN : 1 ≤ Real.log (Real.log (n : ℝ)) := hnData.2.2
  have hmain :
      (∑ q ∈ (Finset.Ioc 0 n).filter (fun q ↦ q ^ 4 ≤ n),
          (squarefreeExtremalSize (n / q ^ 2) : ℝ)) ≤
        6 * |C| * scale n := by
    calc
      (∑ q ∈ (Finset.Ioc 0 n).filter (fun q ↦ q ^ 4 ≤ n),
          (squarefreeExtremalSize (n / q ^ 2) : ℝ))
          ≤ ∑ q ∈ (Finset.Ioc 0 n).filter (fun q ↦ q ^ 4 ≤ n),
              (3 * |C| * scale n) * ((q : ℝ) ^ 2)⁻¹ := by
        gcongr with q hq
        have hqmem := Finset.mem_filter.mp hq
        have hqpos := (Finset.mem_Ioc.mp hqmem.1).1
        have hq4 := hqmem.2
        let m := n / q ^ 2
        have hq2_le_m : q ^ 2 ≤ m := by
          apply (Nat.le_div_iff_mul_le (pow_pos hqpos 2)).2
          simpa [pow_succ, mul_assoc] using hq4
        have hn_lt : n < m * (m + 1) := by
          have hdiv := Nat.lt_mul_div_succ n (pow_pos hqpos 2)
          exact hdiv.trans_le (Nat.mul_le_mul_right (m + 1) hq2_le_m)
        have hNm : N ≤ m := by
          by_contra hnot
          have hmN : m < N := by omega
          have : n < N * (N + 1) := hn_lt.trans_le <|
            Nat.mul_le_mul (Nat.le_of_lt hmN) (by omega)
          omega
        have hm4 : 4 ≤ m := by
          by_contra hmnot
          have hmle3 : m ≤ 3 := by omega
          have : n < 3 * 4 := hn_lt.trans_le
            (Nat.mul_le_mul hmle3 (by omega))
          omega
        have hmData := hN m hNm
        calc
          (squarefreeExtremalSize m : ℝ) ≤ |C| * scale m := hmData.1
          _ ≤ |C| * (3 * scale n / (q : ℝ) ^ 2) := by
            gcongr
            exact scale_div_square_le hn hqpos hq4 hm4 hmData.2.1
          _ = (3 * |C| * scale n) * ((q : ℝ) ^ 2)⁻¹ := by ring
      _ ≤ ∑ q ∈ Finset.Ioo 0 (n + 1),
            (3 * |C| * scale n) * ((q : ℝ) ^ 2)⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          have hq' := Finset.mem_filter.mp hq
          exact Finset.mem_Ioo.mpr ⟨(Finset.mem_Ioc.mp hq'.1).1, by
            have := (Finset.mem_Ioc.mp hq'.1).2
            omega⟩
        · intro q _ _
          positivity
      _ = (3 * |C| * scale n) *
            ∑ q ∈ Finset.Ioo 0 (n + 1), ((q : ℝ) ^ 2)⁻¹ := by
        simp_rw [Finset.mul_sum]
      _ ≤ (3 * |C| * scale n) * 2 := by
        gcongr
        have hseries :
            (∑ q ∈ Finset.Ioo 0 (n + 1), ((q : ℝ) ^ 2)⁻¹) ≤
              2 / (((0 : ℕ) : ℝ) + 1) :=
          sum_Ioo_inv_sq_le 0 (n + 1)
        norm_num at hseries
        exact hseries
      _ = 6 * |C| * scale n := by ring
  have htail := large_squarePart_tail_le n hn1 hllN
  have hsum :
      (∑ q ∈ Finset.Ioc 0 n,
          (squarefreeExtremalSize (n / q ^ 2) : ℝ)) ≤
        (6 * |C| + 8) * scale n := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.Ioc 0 n) (fun q ↦ q ^ 4 ≤ n)]
    have htail' :
        (∑ q ∈ (Finset.Ioc 0 n).filter (fun q ↦ ¬q ^ 4 ≤ n),
            (squarefreeExtremalSize (n / q ^ 2) : ℝ)) ≤ 8 * scale n := by
      simpa only [Nat.not_le] using htail
    linarith
  have hext : (extremalSize n : ℝ) ≤
      ∑ q ∈ Finset.Ioc 0 n,
        (squarefreeExtremalSize (n / q ^ 2) : ℝ) := by
    exact_mod_cast extremalSize_le_sum_squarefreeExtremalSize n
  rw [Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ extremalSize n),
    Real.norm_eq_abs, abs_of_pos hscaleN]
  exact hext.trans hsum

end Erdos888
