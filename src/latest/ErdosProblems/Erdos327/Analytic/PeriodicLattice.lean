import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

namespace Erdos327.Analytic

open Finset

/-- The members of `[a, a + X)` in a prescribed residue class modulo
`d`.  The representative is reduced in the definition, so no hypothesis
on `r` is needed. -/
def residueClassIco (d a X r : ℕ) : Finset ℕ :=
  (Ico a (a + X)).filter fun n ↦ n % d = r % d

@[simp] theorem mem_residueClassIco {d a X r n : ℕ} :
    n ∈ residueClassIco d a X r ↔
      a ≤ n ∧ n < a + X ∧ n % d = r % d := by
  simp only [residueClassIco, mem_filter, mem_Ico]
  tauto

/-- A residue class modulo `d > 0` occurs at most `X / d + 1` times in
an interval of length `X`.

The map sends `n` to the quotient of `n - a` by `d`.  It lands in
`range (X / d + 1)`.  Two members of the same residue class with the
same quotient have both the same quotient and remainder after
subtracting `a`, and hence are equal. -/
theorem card_residueClassIco_le
    {d : ℕ} (_hd : 0 < d) (a X r : ℕ) :
    (residueClassIco d a X r).card ≤ X / d + 1 := by
  let q : ℕ → ℕ := fun n ↦ (n - a) / d
  have hcard :
      (residueClassIco d a X r).card ≤ (range (X / d + 1)).card := by
    refine Finset.card_le_card_of_injOn q ?_ ?_
    · intro n hn
      have hn' := mem_residueClassIco.mp hn
      simp only [Finset.mem_coe, mem_range, q]
      have hsub : n - a < X := by omega
      exact Nat.lt_succ_of_le (Nat.div_le_div_right hsub.le)
    · intro n hn m hm hq
      have hn' := mem_residueClassIco.mp hn
      have hm' := mem_residueClassIco.mp hm
      change (n - a) / d = (m - a) / d at hq
      have hmodnm : n % d = m % d := hn'.2.2.trans hm'.2.2.symm
      have hmodsub : (n - a) % d = (m - a) % d := by
        have hcong : n ≡ m [MOD d] := hmodnm
        have hcong' : a + (n - a) ≡ a + (m - a) [MOD d] := by
          simpa [Nat.add_sub_of_le hn'.1, Nat.add_sub_of_le hm'.1] using hcong
        exact Nat.ModEq.add_left_cancel' a hcong'
      have hsubeq : n - a = m - a := by
        calc
          n - a = (n - a) % d + d * ((n - a) / d) :=
            (Nat.mod_add_div (n - a) d).symm
          _ = (m - a) % d + d * ((m - a) / d) := by
            rw [hmodsub, hq]
          _ = m - a := Nat.mod_add_div (m - a) d
      omega
  simpa using hcard

/-- Every interval of length `X` contains at least `X / d` members of
each residue class modulo `d > 0`. -/
theorem card_residueClassIco_ge
    {d : ℕ} (hd : 0 < d) (a X r : ℕ) :
    X / d ≤ (residueClassIco d a X r).card := by
  have hrange : r % d ∈ (Finset.range d) :=
    Finset.mem_range.mpr (Nat.mod_lt r hd)
  have himage :
      r % d ∈ (Finset.Ico a (a + d)).image (fun n ↦ n % d) := by
    rw [Nat.image_Ico_mod]
    exact hrange
  rcases Finset.mem_image.mp himage with ⟨n₀, hn₀, hn₀mod⟩
  have hn₀' := Finset.mem_Ico.mp hn₀
  let f : ℕ → ℕ := fun k ↦ n₀ + d * k
  have hcard :
      (range (X / d)).card ≤ (residueClassIco d a X r).card := by
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro k hk
      have hk' : k < X / d := by simpa using hk
      have hk1 : k + 1 ≤ X / d := Nat.succ_le_iff.mpr hk'
      apply mem_residueClassIco.mpr
      refine ⟨hn₀'.1.trans (Nat.le_add_right n₀ (d * k)), ?_, ?_⟩
      · calc
          f k < (a + d) + d * k := by
            exact Nat.add_lt_add_right hn₀'.2 (d * k)
          _ = a + (k + 1) * d := by
            ring
          _ ≤ a + (X / d) * d := by
            exact Nat.add_le_add_left (Nat.mul_le_mul_right d hk1) a
          _ ≤ a + X := by
            exact Nat.add_le_add_left (Nat.div_mul_le_self X d) a
      · change (n₀ + d * k) % d = r % d
        rw [Nat.add_mul_mod_self_left]
        exact hn₀mod
    · intro k _ l _ hkl
      change n₀ + d * k = n₀ + d * l at hkl
      exact Nat.mul_left_cancel hd (Nat.add_left_cancel hkl)
  simpa using hcard

/-- Clean integer form of the statement that a residue count differs
from the interval length divided by the modulus by at most one. -/
theorem card_residueClassIco_bounds
    {d : ℕ} (hd : 0 < d) (a X r : ℕ) :
    X / d ≤ (residueClassIco d a X r).card ∧
      (residueClassIco d a X r).card ≤ X / d + 1 :=
  ⟨card_residueClassIco_ge hd a X r,
    card_residueClassIco_le hd a X r⟩

/-- The fiber in `[a, a + X)` above a residue of `ZMod d`. -/
def zmodFiberIco (d a X : ℕ) (r : ZMod d) : Finset ℕ :=
  (Ico a (a + X)).filter fun n ↦ (n : ZMod d) = r

@[simp] theorem mem_zmodFiberIco {d a X n : ℕ} {r : ZMod d} :
    n ∈ zmodFiberIco d a X r ↔
      a ≤ n ∧ n < a + X ∧ (n : ZMod d) = r := by
  simp only [zmodFiberIco, mem_filter, mem_Ico]
  tauto

/-- The `ZMod` formulation of `card_residueClassIco_le`. -/
theorem card_zmodFiberIco_le
    {d : ℕ} (hd : 0 < d) (a X : ℕ) (r : ZMod d) :
    (zmodFiberIco d a X r).card ≤ X / d + 1 := by
  letI : NeZero d := ⟨hd.ne'⟩
  have hset :
      zmodFiberIco d a X r = residueClassIco d a X r.val := by
    ext n
    simp only [mem_zmodFiberIco, mem_residueClassIco]
    refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ ?_
    calc
      (n : ZMod d) = r ↔
          (n : ZMod d) = (r.val : ZMod d) := by
            rw [ZMod.natCast_zmod_val]
      _ ↔ n % d = r.val % d := ZMod.natCast_eq_natCast_iff' n r.val d
  rw [hset]
  exact card_residueClassIco_le hd a X r.val

/-- The product fiber above a pair of residues in a rectangular box. -/
def zmodFiberBox (d au Xu av Xv : ℕ) (r : ZMod d × ZMod d) :
    Finset (ℕ × ℕ) :=
  zmodFiberIco d au Xu r.1 ×ˢ zmodFiberIco d av Xv r.2

@[simp] theorem mem_zmodFiberBox
    {d au Xu av Xv : ℕ} {r : ZMod d × ZMod d} {x : ℕ × ℕ} :
    x ∈ zmodFiberBox d au Xu av Xv r ↔
      au ≤ x.1 ∧ x.1 < au + Xu ∧
      av ≤ x.2 ∧ x.2 < av + Xv ∧
      ((x.1 : ZMod d), (x.2 : ZMod d)) = r := by
  simp only [zmodFiberBox, mem_product, mem_zmodFiberIco]
  aesop

@[simp] theorem card_zmodFiberBox
    (d au Xu av Xv : ℕ) (r : ZMod d × ZMod d) :
    (zmodFiberBox d au Xu av Xv r).card =
      (zmodFiberIco d au Xu r.1).card *
        (zmodFiberIco d av Xv r.2).card := by
  simp [zmodFiberBox]

/-- A fixed residue pair occurs at most the product of the two
one-dimensional quotient-block bounds. -/
theorem card_zmodFiberBox_le
    {d : ℕ} (hd : 0 < d) (au Xu av Xv : ℕ)
    (r : ZMod d × ZMod d) :
    (zmodFiberBox d au Xu av Xv r).card ≤
      (Xu / d + 1) * (Xv / d + 1) := by
  rw [card_zmodFiberBox]
  exact Nat.mul_le_mul
    (card_zmodFiberIco_le hd au Xu r.1)
    (card_zmodFiberIco_le hd av Xv r.2)

/-- Real-valued form of the product-residue bound, with the natural
quotients relaxed to exact real quotients. -/
theorem card_zmodFiberBox_le_real
    {d : ℕ} (hd : 0 < d) (au Xu av Xv : ℕ)
    (r : ZMod d × ZMod d) :
    ((zmodFiberBox d au Xu av Xv r).card : ℝ) ≤
      ((Xu : ℝ) / d + 1) * ((Xv : ℝ) / d + 1) := by
  have hnat := card_zmodFiberBox_le hd au Xu av Xv r
  have hcast :
      ((zmodFiberBox d au Xu av Xv r).card : ℝ) ≤
        (((Xu / d + 1) * (Xv / d + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  calc
    ((zmodFiberBox d au Xu av Xv r).card : ℝ) ≤
        (((Xu / d + 1) * (Xv / d + 1) : ℕ) : ℝ) := hcast
    _ = (((Xu / d : ℕ) : ℝ) + 1) *
        (((Xv / d : ℕ) : ℝ) + 1) := by push_cast; rfl
    _ ≤ ((Xu : ℝ) / d + 1) * ((Xv : ℝ) / d + 1) := by
      gcongr <;> exact Nat.cast_div_le

/-- The rectangular fiber used for the three-linear-form estimates:
`X ≤ u < 2X` and `1 ≤ v ≤ 8X`. -/
def threeLineFiber (d X : ℕ) (r : ZMod d × ZMod d) :
    Finset (ℕ × ℕ) :=
  zmodFiberBox d X X 1 (8 * X) r

@[simp] theorem mem_threeLineFiber
    {d X : ℕ} {r : ZMod d × ZMod d} {x : ℕ × ℕ} :
    x ∈ threeLineFiber d X r ↔
      X ≤ x.1 ∧ x.1 < 2 * X ∧
      1 ≤ x.2 ∧ x.2 ≤ 8 * X ∧
      ((x.1 : ZMod d), (x.2 : ZMod d)) = r := by
  simp only [threeLineFiber, mem_zmodFiberBox]
  constructor
  · rintro ⟨hu₁, hu₂, hv₁, hv₂, hr⟩
    exact ⟨hu₁, by omega, hv₁, by omega, hr⟩
  · rintro ⟨hu₁, hu₂, hv₁, hv₂, hr⟩
    exact ⟨hu₁, by omega, hv₁, by omega, hr⟩

/-- Uniform product-residue bound for the three-line box. -/
theorem card_threeLineFiber_le
    {d : ℕ} (hd : 0 < d) (X : ℕ) (r : ZMod d × ZMod d) :
    (threeLineFiber d X r).card ≤
      (X / d + 1) * ((8 * X) / d + 1) := by
  exact card_zmodFiberBox_le hd X X 1 (8 * X) r

/-- The lift of a residue-pair weight to a finite rectangular box. -/
noncomputable def periodicBoxSum
    (d au Xu av Xv : ℕ) (h : ZMod d × ZMod d → ℝ) : ℝ :=
  ∑ x ∈ Ico au (au + Xu) ×ˢ Ico av (av + Xv),
    h ((x.1 : ZMod d), (x.2 : ZMod d))

/-- A periodic box sum decomposes exactly into its residue fibers. -/
theorem periodicBoxSum_eq_sum_fibers
    (d au Xu av Xv : ℕ) [NeZero d]
    (h : ZMod d × ZMod d → ℝ) :
    periodicBoxSum d au Xu av Xv h =
      ∑ r : ZMod d × ZMod d,
        (zmodFiberBox d au Xu av Xv r).card * h r := by
  classical
  let box : Finset (ℕ × ℕ) :=
    Ico au (au + Xu) ×ˢ Ico av (av + Xv)
  let residue : ℕ × ℕ → ZMod d × ZMod d :=
    fun x ↦ ((x.1 : ZMod d), (x.2 : ZMod d))
  have hfiber (r : ZMod d × ZMod d) :
      box.filter (fun x ↦ residue x = r) =
        zmodFiberBox d au Xu av Xv r := by
    ext x
    simp only [box, residue, mem_filter, mem_product, mem_Ico,
      mem_zmodFiberBox]
    aesop
  have hdecomp := Finset.sum_fiberwise_of_maps_to
    (s := box) (t := (univ : Finset (ZMod d × ZMod d)))
    (g := residue) (fun _ _ ↦ mem_univ _) (fun x ↦ h (residue x))
  unfold periodicBoxSum
  change (∑ x ∈ box, h (residue x)) =
    ∑ r, (zmodFiberBox d au Xu av Xv r).card * h r
  rw [← hdecomp]
  apply sum_congr rfl
  intro r _
  rw [← hfiber]
  calc
    (∑ x ∈ box with residue x = r, h (residue x)) =
        ∑ _x ∈ box.filter (fun x ↦ residue x = r), h r := by
          apply sum_congr rfl
          intro x hx
          rw [(mem_filter.mp hx).2]
    _ = (box.filter (fun x ↦ residue x = r)).card * h r := by
          simp

/-- The support of a residue-pair weight. -/
noncomputable def residueWeightSupport
    (d : ℕ) [NeZero d] (h : ZMod d × ZMod d → ℝ) :
    Finset (ZMod d × ZMod d) :=
  univ.filter fun r ↦ h r ≠ 0

@[simp] theorem mem_residueWeightSupport
    {d : ℕ} [NeZero d]
    {h : ZMod d × ZMod d → ℝ} {r : ZMod d × ZMod d} :
    r ∈ residueWeightSupport d h ↔ h r ≠ 0 := by
  simp [residueWeightSupport]

/-- A weight bounded by one has total mass at most the cardinality of
its support. -/
theorem sum_weight_le_support_card
    {d : ℕ} [NeZero d] {h : ZMod d × ZMod d → ℝ}
    (hle : ∀ r, h r ≤ 1) :
    (∑ r, h r) ≤ (residueWeightSupport d h).card := by
  classical
  have hsum :
      (∑ r ∈ residueWeightSupport d h, h r) = ∑ r, h r := by
    apply sum_subset (by simp [residueWeightSupport])
    intro r _ hr
    simpa [mem_residueWeightSupport] using hr
  rw [← hsum]
  calc
    (∑ r ∈ residueWeightSupport d h, h r) ≤
        ∑ _r ∈ residueWeightSupport d h, (1 : ℝ) :=
      sum_le_sum fun r _ ↦ hle r
    _ = (residueWeightSupport d h).card := by simp

/-- The elementary periodic-lattice estimate.  Its first term is the
box area divided by `d²`, multiplied by the average residue mass.  The
second term is the boundary error, charged only to residues in the
support of the weight. -/
theorem periodicBoxSum_le_mean_add_error
    {d : ℕ} [NeZero d] (hd : 0 < d) (au Xu av Xv : ℕ)
    (h : ZMod d × ZMod d → ℝ)
    (hnonneg : ∀ r, 0 ≤ h r) (hle : ∀ r, h r ≤ 1) :
    periodicBoxSum d au Xu av Xv h ≤
      ((Xu : ℝ) / d) * ((Xv : ℝ) / d) * (∑ r, h r) +
        ((Xu : ℝ) / d + (Xv : ℝ) / d + 1) *
          (residueWeightSupport d h).card := by
  rw [periodicBoxSum_eq_sum_fibers]
  have hsupport :
      (∑ r, h r) ≤ ((residueWeightSupport d h).card : ℝ) :=
    sum_weight_le_support_card hle
  calc
    (∑ r, ((zmodFiberBox d au Xu av Xv r).card : ℝ) * h r) ≤
        ∑ r, (((Xu : ℝ) / d + 1) * ((Xv : ℝ) / d + 1)) * h r := by
      apply sum_le_sum
      intro r _
      exact mul_le_mul_of_nonneg_right
        (card_zmodFiberBox_le_real hd au Xu av Xv r) (hnonneg r)
    _ = (((Xu : ℝ) / d + 1) * ((Xv : ℝ) / d + 1)) *
        (∑ r, h r) := by rw [mul_sum]
    _ = ((Xu : ℝ) / d) * ((Xv : ℝ) / d) * (∑ r, h r) +
        ((Xu : ℝ) / d + (Xv : ℝ) / d + 1) * (∑ r, h r) := by
      ring
    _ ≤ ((Xu : ℝ) / d) * ((Xv : ℝ) / d) * (∑ r, h r) +
        ((Xu : ℝ) / d + (Xv : ℝ) / d + 1) *
          (residueWeightSupport d h).card := by
      exact add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left hsupport (by positivity))

/-- The periodic-lattice estimate in the exact `X × 8X` box used for
the three-linear-form sieve.  The boundary error is
`(9X / d + 1)` times the number of supported residue pairs. -/
theorem threeLine_periodicBoxSum_le
    {d : ℕ} [NeZero d] (hd : 0 < d) (X : ℕ)
    (h : ZMod d × ZMod d → ℝ)
    (hnonneg : ∀ r, 0 ≤ h r) (hle : ∀ r, h r ≤ 1) :
    periodicBoxSum d X X 1 (8 * X) h ≤
      ((X : ℝ) / d) * ((8 * X : ℕ) : ℝ) / d * (∑ r, h r) +
        (9 * (X : ℝ) / d + 1) *
          (residueWeightSupport d h).card := by
  have hbound :=
    periodicBoxSum_le_mean_add_error hd X X 1 (8 * X) h hnonneg hle
  calc
    periodicBoxSum d X X 1 (8 * X) h ≤
        ((X : ℝ) / d) * (((8 * X : ℕ) : ℝ) / d) * (∑ r, h r) +
          ((X : ℝ) / d + ((8 * X : ℕ) : ℝ) / d + 1) *
            (residueWeightSupport d h).card := hbound
    _ = ((X : ℝ) / d) * ((8 * X : ℕ) : ℝ) / d * (∑ r, h r) +
        (9 * (X : ℝ) / d + 1) *
          (residueWeightSupport d h).card := by
      push_cast
      ring

end Erdos327.Analytic
