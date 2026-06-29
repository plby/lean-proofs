import Mathlib
import UnitFractions.Definitions
import UnitFractions.AuxiliaryLemmas
import UnitFractions.ForMathlib.BasicEstimates
import UnitFractions.ForMathlib.Misc

namespace UnitFractions

open scoped BigOperators
open Real Finset
open _root_.Finset

noncomputable section
attribute [local instance] Classical.propDecidable

/-!
This file ports the declaration surface of `src/fourier.lean`.

Mathlib 4 already provides much of the analytic API used here, especially the complex
exponential/trigonometric identities around:

* `Complex.exp_int_mul_two_pi_mul_I`
* `Complex.exp_ofReal_mul_I_re`
* `Complex.norm_exp_ofReal_mul_I`
* `Complex.two_cos`
-/

/-- Lean 3 used a local notation `[A]` for `A.lcm id`; we use an explicit alias in Lean 4. -/
abbrev lcmA (A : Finset ℕ) : ℕ := A.lcm id

/-- Def 4.1 -/
def integer_count (A : Finset ℕ) (k : ℕ) : ℕ := by
  classical
  exact (A.powerset.filter fun S => ∃ d : ℤ, rec_sum S * k = d).card

/-- Useful for def 4.2 and in other statements. -/
def valid_sum_range (t : ℕ) : Finset ℤ :=
  Finset.Ioc ((-(t : ℤ)) / 2) ((t : ℤ) / 2)

/-- Implementation lemma. -/
lemma dumb_subtraction_thing (t : ℕ) : ((t : ℤ) / 2 - -(t : ℤ) / 2) = t := by
  omega

lemma card_valid_sum_range (t : ℕ) : (valid_sum_range t).card = t := by
  rw [valid_sum_range, Int.card_Ioc, dumb_subtraction_thing]
  simp

lemma mem_valid_sum_range (t : ℕ) (h : ℤ) :
    h ∈ valid_sum_range t ↔ (-(t : ℤ)) / 2 < h ∧ h ≤ (t : ℤ) / 2 := by
  simp [valid_sum_range]

lemma of_mem_valid_sum_range {t : ℕ} {h : ℤ} :
    h ∈ valid_sum_range t → |(h : ℝ)| ≤ (t : ℝ) / 2 := by
  rw [mem_valid_sum_range, and_imp, Int.ediv_lt_iff_lt_mul zero_lt_two,
    Int.le_ediv_iff_mul_le zero_lt_two]
  intro h₁ h₂
  have h₁r : (-(t : ℝ)) < (h : ℝ) * 2 := by
    exact_mod_cast h₁
  have h₂r : (h : ℝ) * 2 ≤ (t : ℝ) := by
    exact_mod_cast h₂
  refine abs_le.mpr ?_
  constructor <;> linarith

lemma zero_mem_valid_sum_range {t : ℕ} (ht : t ≠ 0) : (0 : ℤ) ∈ valid_sum_range t := by
  rw [mem_valid_sum_range]
  have ht' : (0 : ℤ) < t := by
    exact_mod_cast Nat.pos_of_ne_zero ht
  constructor
  · omega
  · positivity

lemma lcm_ne_zero_of_zero_not_mem {A : Finset ℕ} (hA : 0 ∉ A) : A.lcm id ≠ 0 := by
  intro h
  rw [Finset.lcm_eq_zero_iff] at h
  rcases h with ⟨x, hx, hx0⟩
  subst hx0
  exact hA hx

/-- Def 4.2. -/
def j (A : Finset ℕ) : Finset ℤ :=
  (valid_sum_range (A.lcm id)).erase 0

lemma mem_j (A : Finset ℕ) (h : ℤ) :
    h ∈ j A ↔
      h ≠ 0 ∧
        (-((A.lcm id : ℕ) : ℤ)) / 2 < h ∧ h ≤ ((A.lcm id : ℕ) : ℤ) / 2 := by
  simp [j, mem_valid_sum_range]

lemma bound_of_mem_j (A : Finset ℕ) (h : ℤ) (h' : h ∈ j A) :
    |(h : ℝ)| ≤ ((A.lcm id : ℕ) : ℝ) / 2 := by
  rw [j, Finset.mem_erase] at h'
  simpa using of_mem_valid_sum_range h'.2

/-- Def 4.3. -/
def cos_prod (B : Finset ℕ) (t : ℤ) : ℝ :=
  B.prod fun n => |Real.cos (π * t / n)|

lemma cos_prod_nonneg {B : Finset ℕ} {t : ℤ} : 0 ≤ cos_prod B t := by
  exact Finset.prod_nonneg fun _ _ => abs_nonneg _

lemma cos_prod_le_one {B : Finset ℕ} {t : ℤ} : cos_prod B t ≤ 1 := by
  refine Finset.prod_le_one ?_ ?_
  · intro _ _
    exact abs_nonneg _
  · intro _ _
    exact abs_cos_le_one _

/-- Def 4.4 part one. -/
def major_arc_at (A : Finset ℕ) (k : ℕ) (K : ℝ) (t : ℤ) : Finset ℤ :=
  (j A).filter fun h => |(h : ℝ) - t * (A.lcm id) / k| ≤ K / (2 * k)

lemma mem_major_arc_at {A : Finset ℕ} {k : ℕ} {K : ℝ} {t : ℤ} (i : ℤ) :
    i ∈ major_arc_at A k K t ↔
      i ∈ j A ∧ |(i : ℝ) - t * (A.lcm id) / k| ≤ K / (2 * k) := by
  simp [major_arc_at]

lemma major_arc_at_of_neg {A : Finset ℕ} {k : ℕ} {K : ℝ}
    (hk : k ≠ 0) (hK : K < 0) (t : ℤ) :
    major_arc_at A k K t = ∅ := by
  ext i
  constructor
  · intro hi
    have hden : 0 < 2 * (k : ℝ) := by
      positivity
    have hneg : K / (2 * (k : ℝ)) < 0 := div_neg_of_neg_of_pos hK hden
    rw [mem_major_arc_at] at hi
    exfalso
    have habs : 0 ≤ |(i : ℝ) - t * (A.lcm id) / k| := abs_nonneg _
    linarith
  · intro hi
    exact False.elim (Finset.notMem_empty i hi)

/-- Def 4.4 part two. -/
def major_arc (A : Finset ℕ) (k : ℕ) (K : ℝ) : Finset ℤ := by
  classical
  exact (j A).filter fun h => ∃ t : ℤ, h ∈ major_arc_at A k K t

def e (x : ℝ) : ℂ :=
  Complex.exp (x * (2 * Real.pi * Complex.I))

lemma e_add {x y : ℝ} : e (x + y) = e x * e y := by
  simp [e, add_mul, Complex.exp_add, mul_add, mul_left_comm, mul_comm]

lemma e_int (z : ℤ) : e z = 1 := by
  simpa [e, mul_assoc, mul_left_comm, mul_comm] using Complex.exp_int_mul_two_pi_mul_I z

@[simp] lemma e_nat (n : ℕ) : e n = 1 := by
  simpa using e_int (n : ℤ)

@[simp] lemma e_zero : e 0 = 1 := by
  simpa using e_nat 0

lemma e_sum {ι : Type*} {s : Finset ι} (f : ι → ℝ) :
    e (s.sum f) = s.prod fun i => e (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [e]
  | @insert a s ha hs =>
      simp [ha, e_add, hs]

lemma e_half_re {x : ℝ} : (e (x / 2)).re = Real.cos (x * Real.pi) := by
  simpa [e, mul_assoc, mul_left_comm, mul_comm, two_mul] using
    Complex.exp_ofReal_mul_I_re (x * Real.pi)

lemma norm_e {x : ℝ} : ‖e x‖ = 1 := by
  simpa [e, mul_assoc, mul_left_comm, mul_comm] using
    Complex.norm_exp_ofReal_mul_I (x * (2 * Real.pi))

lemma mem_major_arc_at' {A : Finset ℕ} {k : ℕ} {K : ℝ} {t : ℤ} (hk : k ≠ 0) (i : ℤ) :
    i ∈ major_arc_at A k K t ↔ i ∈ j A ∧ (|i * k - t * lcmA A| : ℝ) ≤ K / 2 := by
  rw [mem_major_arc_at]
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hk
  have habs :
      |(i : ℝ) - t * (lcmA A : ℝ) / k| * (k : ℝ) = (|i * k - t * lcmA A| : ℝ) := by
    calc
      |(i : ℝ) - t * (lcmA A : ℝ) / k| * (k : ℝ)
          = |(i : ℝ) - t * (lcmA A : ℝ) / k| * |(k : ℝ)| := by
              rw [abs_of_pos hkpos]
      _ = |((i : ℝ) - t * (lcmA A : ℝ) / k) * k| := by
            rw [← abs_mul]
      _ = |((i * (k : ℤ) - t * (lcmA A : ℤ) : ℤ) : ℝ)| := by
            congr 1
            field_simp [hk0]
            push_cast
            ring
      _ = (|i * (k : ℤ) - t * (lcmA A : ℤ)| : ℝ) := by
            simp
  have hdiv : K / (2 * (k : ℝ)) = (K / 2) / k := by
    field_simp [hk0]
  have hmuldiv : (K / (2 * (k : ℝ))) * (k : ℝ) = K / 2 := by
    field_simp [hk0]
  constructor
  · rintro ⟨hi, hK⟩
    refine ⟨hi, ?_⟩
    have hmul := mul_le_mul_of_nonneg_right hK hkpos.le
    rwa [habs, hmuldiv] at hmul
  · rintro ⟨hi, hK⟩
    refine ⟨hi, ?_⟩
    rw [hdiv]
    apply (le_div_iff₀ hkpos).2
    rwa [habs]

lemma j_sdiff_major_arc {A k K} :
    j A \ major_arc A k K = (j A).filter (fun h => ∀ t, h ∉ major_arc_at A k K t) := by
  classical
  ext h
  constructor
  · intro hh
    rcases Finset.mem_sdiff.mp hh with ⟨hj, hmajor⟩
    rw [Finset.mem_filter]
    refine ⟨hj, ?_⟩
    intro t ht
    apply hmajor
    rw [major_arc, Finset.mem_filter]
    exact ⟨hj, ⟨t, ht⟩⟩
  · intro hh
    rcases Finset.mem_filter.mp hh with ⟨hj, hmajor⟩
    refine Finset.mem_sdiff.mpr ⟨hj, ?_⟩
    intro hm
    rw [major_arc, Finset.mem_filter] at hm
    rcases hm with ⟨_, ⟨t, ht⟩⟩
    exact hmajor t ht

/-- Centred at `x`, width `2 * y`. -/
def integer_range (x y : ℝ) : Finset ℤ := Finset.Icc ⌈x - y⌉ ⌊x + y⌋

lemma mem_integer_range_iff {x y : ℝ} {z : ℤ} :
    z ∈ integer_range x y ↔ |x - z| ≤ y := by
  rw [integer_range, Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨hz1, hz2⟩
    constructor
    · have h1 : x - y ≤ (z : ℝ) := Int.ceil_le.mp hz1
      have h2 : (z : ℝ) ≤ x + y := Int.le_floor.mp hz2
      linarith
    · have h1 : x - y ≤ (z : ℝ) := Int.ceil_le.mp hz1
      have h2 : (z : ℝ) ≤ x + y := Int.le_floor.mp hz2
      linarith
  · rintro ⟨hz1, hz2⟩
    constructor
    · exact Int.ceil_le.mpr (by linarith)
    · exact Int.le_floor.mpr (by linarith)

lemma card_integer_range_le {x y : ℝ} (hy : 0 ≤ y) :
    ↑(integer_range x y).card ≤ 2 * y + 1 := by
  have hnonneg : 0 ≤ ⌊x + y⌋ + 1 - ⌈x - y⌉ := by
    refine sub_nonneg.mpr ?_
    rw [Int.ceil_le]
    have hlt : x - y < ↑(⌊x + y⌋ + 1 : ℤ) := by
      calc
        x - y ≤ x + y := by linarith
        _ < (⌊x + y⌋ : ℝ) + 1 := Int.lt_floor_add_one (x + y)
        _ = ↑(⌊x + y⌋ + 1 : ℤ) := by norm_num
    exact le_of_lt hlt
  calc
    ↑(integer_range x y).card = ((⌊x + y⌋ + 1 - ⌈x - y⌉ : ℤ) : ℝ) := by
      rw [integer_range, Int.card_Icc]
      exact_mod_cast Int.toNat_of_nonneg hnonneg
    _ = (⌊x + y⌋ : ℝ) + 1 - ⌈x - y⌉ := by norm_num
    _ ≤ 2 * y + 1 := by
      have hfc : (⌊x + y⌋ : ℝ) - ⌈x - y⌉ ≤ y + y := by
        simpa using (floor_sub_ceil (z := x) (x := y) (y := y))
      linarith

def my_range (x : ℝ) : Finset ℤ := integer_range 0 x

lemma mem_my_range_iff {x : ℝ} {y : ℤ} :
    y ∈ my_range x ↔ |(y : ℝ)| ≤ x := by
  simpa [my_range] using (mem_integer_range_iff (x := 0) (y := x) (z := y))

def my_range' (A : Finset ℕ) (k : ℕ) (K : ℝ) : Finset ℤ :=
  my_range ((K / (2 * (k : ℝ)) + (lcmA A : ℝ) / 2) / |(lcmA A : ℝ) / k|)

def I (h : ℤ) (K : ℝ) (k : ℕ) : Finset ℤ := integer_range (h * k) (K / 2)

lemma mem_I' {h : ℤ} {K : ℝ} {k : ℕ} {z : ℤ} :
    z ∈ I h K k ↔ |(h * k : ℝ) - z| ≤ K / 2 := by
  simpa [I] using
    (mem_integer_range_iff (x := (h * k : ℝ)) (y := K / 2) (z := z))

lemma card_I_le {h K k} (hK : (0 : ℝ) ≤ K) : ↑(I h K k).card ≤ K + 1 := by
  calc
    ↑(I h K k).card ≤ 2 * (K / 2) + 1 := by
      simpa [I] using
        (card_integer_range_le (x := (h * k : ℝ)) (y := K / 2)
          (by exact div_nonneg hK (by positivity)))
    _ = K + 1 := by ring

/-- Def 4.5. -/
def minor_arc₁ (A : Finset ℕ) (k : ℕ) (K : ℝ) (δ : ℝ) : Finset ℤ :=
  (j A \ major_arc A k K).filter fun h =>
    δ ≤ (A.filter fun n : ℕ => ∀ z ∈ I h K k, ¬ ((n : ℤ) ∣ z)).card

def minor_arc₂ (A : Finset ℕ) (k : ℕ) (K : ℝ) (δ : ℝ) : Finset ℤ :=
  (j A \ major_arc A k K) \ minor_arc₁ A k K δ

lemma major_arc_eq_union {A k K} (hA : 0 ∉ A) (hk : k ≠ 0) :
    major_arc A k K = (my_range' A k K).biUnion (major_arc_at A k K) := by
  classical
  ext h
  constructor
  · intro hh
    rw [major_arc, Finset.mem_filter] at hh
    rcases hh with ⟨hj, t, ht⟩
    rw [Finset.mem_biUnion]
    refine ⟨t, ?_, ht⟩
    rw [my_range', mem_my_range_iff]
    have hlcm0 : ((lcmA A : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast lcm_ne_zero_of_zero_not_mem hA
    have hk0 : (k : ℝ) ≠ 0 := by
      exact_mod_cast hk
    have hden : 0 < |(lcmA A : ℝ) / k| := by
      exact abs_pos.mpr (div_ne_zero hlcm0 hk0)
    have hvalid : |(h : ℝ)| ≤ (lcmA A : ℝ) / 2 := bound_of_mem_j A h hj
    have harc : |(h : ℝ) - t * (lcmA A : ℝ) / k| ≤ K / (2 * k) :=
      (mem_major_arc_at h).mp ht |>.2
    have harc' : |(h : ℝ) - (t : ℝ) * ((lcmA A : ℝ) / k)| ≤ K / (2 * k) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using harc
    apply (le_div_iff₀ hden).2
    calc
      |(t : ℝ)| * |(lcmA A : ℝ) / k| = |(t : ℝ) * ((lcmA A : ℝ) / k)| := by
        rw [abs_mul]
      _ = |((t : ℝ) * ((lcmA A : ℝ) / k) - h) + h| := by
        congr 1
        ring
      _ ≤ |(t : ℝ) * ((lcmA A : ℝ) / k) - h| + |(h : ℝ)| := abs_add_le _ _
      _ = |(h : ℝ) - (t : ℝ) * ((lcmA A : ℝ) / k)| + |(h : ℝ)| := by
        rw [abs_sub_comm]
      _ ≤ K / (2 * k) + (lcmA A : ℝ) / 2 := add_le_add harc' hvalid
  · intro hh
    rw [Finset.mem_biUnion] at hh
    rcases hh with ⟨t, -, ht⟩
    rw [major_arc, Finset.mem_filter]
    exact ⟨(mem_major_arc_at h).mp ht |>.1, ⟨t, ht⟩⟩

lemma minor_arc₂_eq {A k K δ} :
    minor_arc₂ A k K δ =
      ((j A \ major_arc A k K).filter fun h =>
        ↑(A.filter fun n : ℕ => ∀ z ∈ I h K k, ¬ ((n : ℤ) ∣ z)).card < δ) := by
  ext h
  constructor
  · intro hh
    rw [minor_arc₂, Finset.mem_sdiff] at hh
    rcases hh with ⟨hs, hnot⟩
    rw [Finset.mem_filter]
    refine ⟨hs, ?_⟩
    by_contra hge
    apply hnot
    rw [minor_arc₁, Finset.mem_filter]
    exact ⟨hs, le_of_not_gt hge⟩
  · intro hh
    rw [Finset.mem_filter] at hh
    rcases hh with ⟨hs, hlt⟩
    rw [minor_arc₂, Finset.mem_sdiff]
    refine ⟨hs, ?_⟩
    intro hm
    rw [minor_arc₁, Finset.mem_filter] at hm
    exact (not_le.mpr hlt) hm.2

lemma e_eq_one_iff (x : ℝ) :
    e x = 1 ↔ ∃ z : ℤ, x = z := by
  constructor
  · intro hx
    rw [e] at hx
    obtain ⟨z, hz⟩ := Complex.exp_eq_one_iff.mp hx
    refine ⟨z, ?_⟩
    have hdiv := congrArg (fun w : ℂ => w / (2 * Real.pi * Complex.I)) hz
    have hxz : (x : ℂ) = z := by
      simpa [div_eq_mul_inv, mul_assoc, Complex.two_pi_I_ne_zero] using hdiv
    simpa using congrArg Complex.re hxz
  · rintro ⟨z, rfl⟩
    simpa using e_int z

lemma abs_e {x : ℝ} : ‖e x‖ = 1 := by
  simpa using norm_e (x := x)

lemma one_add_e (x : ℝ) : 1 + e x = 2 * e (x / 2) * cos (π * x) := by
  have hzero : e (-x / 2) * e (x / 2) = 1 := by
    simpa [show -x / 2 + x / 2 = 0 by ring] using
      (e_add (x := -x / 2) (y := x / 2)).symm
  have hsplit : e x = e (x / 2) * e (x / 2) := by
    simpa [show x / 2 + x / 2 = x by ring] using
      (e_add (x := x / 2) (y := x / 2))
  have hhalf : e (x / 2) = Complex.exp ((x * π) * Complex.I) := by
    simp [e, mul_left_comm, mul_comm, two_mul]
  have hnegHalf : e (-x / 2) = Complex.exp (-(x * π) * Complex.I) := by
    simp [e, mul_left_comm, mul_comm, two_mul]
  calc
    1 + e x = e (-x / 2) * e (x / 2) + e (x / 2) * e (x / 2) := by
      rw [hzero, hsplit]
    _ = e (x / 2) * (e (-x / 2) + e (x / 2)) := by ring
    _ = e (x / 2) *
        (Complex.exp (-(x * π) * Complex.I) + Complex.exp ((x * π) * Complex.I)) := by
      congr 1
      rw [hnegHalf, hhalf]
    _ = e (x / 2) * (2 * cos (π * x)) := by
      congr 1
      simpa [Complex.ofReal_cos, mul_comm, add_comm] using
        (Complex.two_cos (x * π : ℂ)).symm
    _ = 2 * e (x / 2) * cos (π * x) := by ring

lemma abs_one_add_e (x : ℝ) :
    ‖1 + e x‖ = 2 * |cos (π * x)| := by
  rw [one_add_e]
  rw [norm_mul, norm_mul, abs_e]
  norm_num
  simpa [Complex.ofReal_cos] using
    (RCLike.norm_ofReal (K := ℂ) (r := Real.cos (π * x)))

/-- Lemma 4.6. Note `r` in this statement is different to the `r` in the written proof. -/
lemma orthogonality {n m : ℕ} {r s : ℤ} (hm : m ≠ 0) {I : Finset ℤ}
    (hI : I = Finset.Ioc r s) (hrs₁ : r < s) (hrs₂ : I.card = m) :
    I.sum (fun h => e (h * n / m)) * (1 / m) = if m ∣ n then (1 : ℂ) else 0 := by
  classical
  have _ : r < s := hrs₁
  have hmℝ : (m : ℝ) ≠ 0 := by
    exact_mod_cast hm
  have hmℂ : (m : ℂ) ≠ 0 := by
    exact_mod_cast hm
  have hcardI : I.card = (s - r).toNat := by
    rw [hI, Int.card_Ioc]
  have hcard : (s - r).toNat = m := hcardI.symm.trans hrs₂
  by_cases hmn : m ∣ n
  · obtain ⟨k, rfl⟩ := hmn
    rw [if_pos (dvd_mul_right m k)]
    have hterm : ∀ h : ℤ, e (h * (((m * k : ℕ) : ℝ)) / m) = 1 := by
      intro h
      calc
        e (h * (((m * k : ℕ) : ℝ)) / m) = e ((h : ℝ) * k) := by
          congr 1
          field_simp [hmℝ]
          rw [Nat.cast_mul]
          ring
        _ = e (h * k : ℤ) := by
          congr 1
          push_cast
          rfl
        _ = 1 := e_int (h * k)
    have hsum : I.sum (fun h => e (h * (((m * k : ℕ) : ℝ)) / m)) = m := by
      calc
        I.sum (fun h => e (h * (((m * k : ℕ) : ℝ)) / m)) = I.sum (fun _ => (1 : ℂ)) := by
          apply Finset.sum_congr rfl
          intro h hh
          exact hterm h
        _ = m := by simp [hrs₂]
    calc
      I.sum (fun h => e (h * (((m * k : ℕ) : ℝ)) / m)) * (1 / m) = (m : ℂ) * (1 / m) := by
        rw [hsum]
      _ = 1 := by simp [one_div, hmℂ]
  · rw [if_neg hmn]
    let x : ℝ := (n : ℝ) / m
    let ξ : ℂ := e x
    have hpow : ∀ i : ℕ, e ((i : ℝ) * x) = ξ ^ i := by
      intro i
      induction i with
      | zero =>
          simp [ξ]
      | succ i ih =>
          calc
            e (((i + 1 : ℕ) : ℝ) * x) = e (x + (i : ℝ) * x) := by
              congr 1
              rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
            _ = e x * e ((i : ℝ) * x) := e_add
            _ = ξ * ξ ^ i := by simp [ξ, ih]
            _ = ξ ^ (i + 1) := by rw [pow_succ, mul_comm]
    have hξm : ξ ^ m = 1 := by
      rw [← hpow m]
      dsimp [x]
      rw [show (m : ℝ) * ((n : ℝ) / m) = n by
        field_simp [hmℝ]]
      exact e_nat n
    have hξ_ne : ξ ≠ 1 := by
      intro hξ
      apply hmn
      obtain ⟨z, hz⟩ := (e_eq_one_iff x).mp (by simpa [ξ] using hξ)
      have hnz : (n : ℝ) = z * m := by
        calc
          (n : ℝ) = x * m := by
            dsimp [x]
            field_simp [hmℝ]
          _ = z * m := by rw [hz]
      have hnz' : (n : ℤ) = z * m := by
        exact_mod_cast hnz
      exact Int.natCast_dvd_natCast.mp ⟨z, by simpa [mul_comm] using hnz'⟩
    have hsum :
        I.sum (fun h => e (h * n / m)) =
          e ((((r + 1 : ℤ) : ℝ) * n / m)) * ∑ i ∈ range m, ξ ^ i := by
      rw [hI, Int.Ioc_eq_finset_map, Finset.sum_map]
      simp_rw [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
      rw [hcard]
      have hsplit :
          ∑ i ∈ range m, e (((r + 1 + (i : ℤ) : ℤ) * n / m)) =
            ∑ i ∈ range m, e ((((r + 1 : ℤ) : ℝ) * n / m)) * ξ ^ i := by
        apply Finset.sum_congr rfl
        intro i hi
        have harg :
            (((r + 1 + (i : ℤ) : ℤ) : ℝ) * n / m) =
              (((r + 1 : ℤ) : ℝ) * n / m) + (i : ℝ) * x := by
          dsimp [x]
          push_cast
          ring
        rw [harg, e_add, hpow i]
      rw [hsplit, ← Finset.mul_sum]
    have hgeom0 : ∑ i ∈ range m, ξ ^ i = 0 := by
      have hmul : (∑ i ∈ range m, ξ ^ i) * (ξ - 1) = 0 := by
        simpa [hξm] using (geom_sum_mul ξ m)
      exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hξ_ne)
    calc
      I.sum (fun h => e (h * n / m)) * (1 / m) =
          (e ((((r + 1 : ℤ) : ℝ) * n / m)) * ∑ i ∈ range m, ξ ^ i) * (1 / m) := by
            rw [hsum]
      _ = 0 := by simp [hgeom0]

theorem Nat.lcm_smallest {a b d : ℕ} (hda : a ∣ d) (hdb : b ∣ d)
    (hd : ∀ e : ℕ, a ∣ e → b ∣ e → d ∣ e) : d = a.lcm b := by
  apply Nat.dvd_antisymm
  · exact hd _ (Nat.dvd_lcm_left a b) (Nat.dvd_lcm_right a b)
  · exact Nat.lcm_dvd hda hdb

lemma factorization_lcm {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x.lcm y).factorization = x.factorization ⊔ y.factorization := by
  exact Nat.factorization_lcm hx hy

/-- Lemma 4.7. -/
lemma lcm_desc {A : Finset ℕ} (hA : 0 ∉ A) :
    (lcmA A).factorization = A.sup Nat.factorization := by
  classical
  revert hA
  refine Finset.induction_on A ?_ ?_
  · intro hA
    simp [lcmA]
    rfl
  · intro a s ha ih hA
    have ha0 : a ≠ 0 := by
      intro h0
      apply hA
      simp [h0]
    have hs0 : 0 ∉ s := by
      intro hs
      apply hA
      simp [hs]
    rw [lcmA, Finset.lcm_insert, Finset.sup_insert]
    change (Nat.lcm a (s.lcm id)).factorization = a.factorization ⊔ s.sup Nat.factorization
    rw [factorization_lcm ha0 (lcm_ne_zero_of_zero_not_mem hs0), ih hs0]

lemma Finset.support_sup {α β : Type*} {f : α → β →₀ ℕ} (s : Finset α) :
    (s.sup f).support = s.biUnion (fun a => (f a).support) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sup_empty, Finset.biUnion_empty, bot_eq_zero]
    simp
  · intro a s _ ih
    rw [Finset.sup_insert, Finsupp.support_sup, ih, Finset.biUnion_insert]

lemma Finset.sup_eq_mem {α β : Type*} {s : Finset α} (f : α → β)
    [LinearOrder β] [OrderBot β] (hs : s.Nonempty) :
    ∃ x ∈ s, s.sup f = f x := by
  classical
  refine Finset.induction_on s ?_ ?_ hs
  · intro hs
    cases hs.ne_empty rfl
  · intro a s ha ih hs
    by_cases hs' : s.Nonempty
    · rcases ih hs' with ⟨x, hx, hsup⟩
      by_cases hax : f a ≤ f x
      · refine ⟨x, Finset.mem_insert_of_mem hx, ?_⟩
        rw [Finset.sup_insert, hsup, sup_eq_right.2 hax]
      · refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
        rw [Finset.sup_insert, hsup, sup_eq_left.2 (le_of_not_ge hax)]
    · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
      rw [hs0]
      refine ⟨a, by simp, ?_⟩
      simp

lemma Finset.finsupp_sup_apply {α β : Type*} {f : α → β →₀ ℕ} (s : Finset α) (x : β) :
    s.sup f x = s.sup (fun a => f a x) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · rfl
  · intro a s _ ih
    simp [Finset.sup_insert, Finsupp.sup_apply, ih]

lemma smooth_lcm_aux {X : ℕ} {A : Finset ℕ} (hX₀ : X ≠ 0)
    (hX : ∀ q ∈ ppowers_in_set A, q ≤ X) (hA : 0 ∉ A) :
    lcmA A ≤ X ^ Nat.primeCounting X := by
  have hlcm0 : lcmA A ≠ 0 := lcm_ne_zero_of_zero_not_mem hA
  have hprimecount : ((Finset.Icc 1 X).filter Nat.Prime).card = Nat.primeCounting X := by
    simpa [Nat.primeCounting] using (prime_counting_eq_card_primes (x := X)).symm
  have hpow_mem :
      ∀ p ∈ (lcmA A).primeFactors, p ^ (lcmA A).factorization p ∈ ppowers_in_set A := by
    intro p hp
    have hp' : p ∈ (lcmA A).factorization.support := by
      simpa [Nat.support_factorization] using hp
    have hfac0 : (lcmA A).factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp'
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hfac :
        (lcmA A).factorization p = A.sup (fun a => a.factorization p) := by
      rw [lcm_desc hA, Finset.finsupp_sup_apply]
    have hAne : A.Nonempty := by
      by_contra hAempty
      rw [Finset.not_nonempty_iff_eq_empty] at hAempty
      simp [hAempty] at hp
    rcases Finset.sup_eq_mem (s := A) (f := fun a => a.factorization p) hAne with ⟨a, haA, hsup⟩
    refine (mem_ppowers_in_set' hpprime hfac0).2 ⟨a, haA, ?_⟩
    rw [← hsup, ← hfac]
  have hcard :
      (lcmA A).primeFactors.card ≤ Nat.primeCounting X := by
    have hsubset : (lcmA A).primeFactors ⊆ (Finset.Icc 1 X).filter Nat.Prime := by
      intro p hp
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp' : p ∈ (lcmA A).factorization.support := by
        simpa [Nat.support_factorization] using hp
      have hfac0 : (lcmA A).factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp'
      have hpow_le : p ^ (lcmA A).factorization p ≤ X := hX _ (hpow_mem p hp)
      have hp_le : p ≤ X := (Nat.le_self_pow hfac0 p).trans hpow_le
      exact Finset.mem_filter.mpr ⟨by simp [hpprime.one_le, hp_le], hpprime⟩
    rw [← hprimecount]
    exact Finset.card_le_card hsubset
  calc
    lcmA A = (lcmA A).primeFactors.prod (fun p => p ^ (lcmA A).factorization p) := by
      symm
      exact Nat.prod_factorization_pow_eq_self hlcm0
    _ ≤ (lcmA A).primeFactors.prod (fun _ => X) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro p hp
        exact Nat.zero_le _
      · intro p hp
        exact hX (p ^ (lcmA A).factorization p) (hpow_mem p hp)
    _ = X ^ (lcmA A).primeFactors.card := by simp
    _ ≤ X ^ Nat.primeCounting X := by
      exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero hX₀) hcard

/-- Lemma 4.8. -/
lemma smooth_lcm :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 0 ≤ X →
      ∀ A : Finset ℕ, 0 ∉ A → (∀ q ∈ ppowers_in_set A, ↑q ≤ X) →
        ↑(lcmA A) ≤ exp (C * X) := by
  obtain ⟨c, hc, hprime⟩ := prime_counting_le_const_mul_div_log
  refine ⟨c, hc, ?_⟩
  intro X hX₀ A hA hAX
  by_cases hX : X ≤ 1
  · have hppow : ppowers_in_set A = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      have hqX : (q : ℝ) ≤ 1 := (hAX q hq).trans hX
      rw [mem_ppowers_in_set] at hq
      have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.1.one_lt
      exact not_le_of_gt hq1 hqX
    have hlcm : lcmA A = 1 := by
      simpa [lcmA] using ppowers_in_set_eq_empty' hppow hA
    rw [hlcm, Nat.cast_one]
    simpa using Real.one_le_exp (mul_nonneg hc.le hX₀)
  · have hX' : 1 < X := lt_of_not_ge hX
    have hfloor0 : ⌊X⌋₊ ≠ 0 := by
      simp [Nat.floor_eq_zero, not_lt, hX'.le]
    refine
      (Nat.cast_le.2
        (smooth_lcm_aux hfloor0 (fun q hq ↦ Nat.le_floor (hAX q hq)) hA)).trans ?_
    simp only [Nat.cast_pow]
    refine (pow_le_pow_left₀ (by positivity) (Nat.floor_le hX₀) _).trans ?_
    have hdiv_nonneg : 0 ≤ X / Real.log X := by
      exact div_nonneg hX₀ (Real.log_nonneg hX'.le)
    have hX₁ : (Nat.primeCounting ⌊X⌋₊ : ℝ) ≤ c * (X / Real.log X) := by
      simpa [Real.norm_of_nonneg hdiv_nonneg] using hprime X
    have hpowpos : 0 < X ^ Nat.primeCounting ⌊X⌋₊ := by
      exact pow_pos (zero_lt_one.trans hX') _
    rwa [← Real.log_le_iff_le_exp hpowpos, ← Real.rpow_natCast,
      Real.log_rpow (zero_lt_one.trans hX'), ← _root_.le_div_iff₀ (Real.log_pos hX'),
      mul_div_assoc]

lemma jordan_apply {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) : 2 * x ≤ sin (π * x) := by
  have hπx_nonneg : 0 ≤ π * x := mul_nonneg Real.pi_pos.le hx
  have hπx_le : π * x ≤ π / 2 := by
    nlinarith [hx', Real.pi_pos]
  simpa [div_eq_mul_inv, mul_assoc, Real.pi_ne_zero] using
    (Real.mul_le_sin (x := π * x) hπx_nonneg hπx_le)

/-- Lemma 4.9. -/
lemma cos_bound {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    |cos (π * x)| ≤ exp (-(2 * x ^ 2)) := by
  have hcos_nonneg : 0 ≤ cos (π * x) := by
    refine Real.cos_nonneg_of_mem_Icc ?_
    constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [hx', Real.pi_pos]
  rw [abs_of_nonneg hcos_nonneg]
  have hπx : |π * x| ≤ π := by
    rw [abs_of_nonneg (mul_nonneg Real.pi_pos.le hx)]
    nlinarith [hx', Real.pi_pos]
  have hcos :
      cos (π * x) ≤ 1 - 2 * x ^ 2 := by
    calc
      cos (π * x) ≤ 1 - 2 / π ^ 2 * (π * x) ^ 2 := Real.cos_le_one_sub_mul_cos_sq hπx
      _ = 1 - 2 * x ^ 2 := by
        field_simp [pow_two, Real.pi_ne_zero]
  have hexp : 1 - 2 * x ^ 2 ≤ exp (-(2 * x ^ 2)) := by
    simpa using Real.one_sub_le_exp_neg (2 * x ^ 2)
  exact hcos.trans hexp

lemma cos_bound_abs {x : ℝ} (hx' : |x| ≤ 1 / 2) :
    |cos (π * x)| ≤ exp (-(2 * x ^ 2)) := by
  rcases le_or_gt 0 x with hx | hx
  · exact cos_bound hx (by simpa [abs_of_nonneg hx] using hx')
  · have hxneg : 0 ≤ -x := by linarith
    have hxneg' : -x ≤ 1 / 2 := by
      have hxabs : |-x| ≤ 1 / 2 := by simpa [abs_neg] using hx'
      simpa [abs_of_nonneg hxneg] using hxabs
    have h := cos_bound hxneg hxneg'
    simpa [neg_mul, Real.cos_neg, pow_two] using h

lemma Nat.coprime_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ) (n : ℕ) :
    Nat.Coprime n (s.prod f) ↔ ∀ i ∈ s, Nat.Coprime n (f i) := by
  simpa [Nat.coprime_iff_isRelPrime] using
    (IsRelPrime.prod_right_iff (t := s) (s := f) (x := n))

lemma prod_dvd_of_dvd_of_pairwise_disjoint {ι : Type*} {s : Finset ι} {f : ι → ℕ} {n : ℕ}
    (hn : ∀ i ∈ s, f i ∣ n) (h : (s : Set ι).Pairwise fun i j => Nat.Coprime (f i) (f j)) :
    s.prod f ∣ n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a r har ihr =>
      rw [Finset.prod_insert har]
      have hcop : Nat.Coprime (f a) (r.prod f) := by
        rw [Nat.coprime_prod]
        intro i hi
        exact h (by simp) (by simp [hi]) (ne_of_mem_of_not_mem hi har).symm
      refine hcop.mul_dvd_of_dvd_of_dvd ?_ ?_
      · exact hn a (by simp)
      · refine ihr ?_ ?_
        · intro i hi
          exact hn i (by simp [hi])
        · intro i hi j hj hij
          exact h (by simp [hi]) (by simp [hj]) hij

/-- Lemma 4.10. -/
lemma triv_q_bound {A : Finset ℕ} (hA : 0 ∉ A) (n : ℕ) :
    ↑((ppowers_in_set A).filter fun q => n ∈ local_part A q).card ≤ log n / log 2 := by
  by_cases hn0 : n = 0
  · subst hn0
    simp [zero_mem_local_part_iff, hA, Real.log_zero]
  · have hsubset :
        (ppowers_in_set A).filter (fun q => n ∈ local_part A q) ⊆
          n.divisors.filter (fun q => IsPrimePow q ∧ Nat.Coprime q (n / q)) := by
      intro q hq
      rcases Finset.mem_filter.mp hq with ⟨hqppow, hqn⟩
      rcases (mem_ppowers_in_set.mp hqppow).1 with hqprime
      rcases (mem_local_part (A := A) (q := q) n).mp hqn with ⟨_, hqdvd, hqcop⟩
      refine Finset.mem_filter.mpr ?_
      constructor
      · rw [Nat.mem_divisors]
        exact ⟨hqdvd, hn0⟩
      · exact ⟨hqprime, hqcop⟩
    have hcard :
        ((ppowers_in_set A).filter (fun q => n ∈ local_part A q)).card ≤
          ArithmeticFunction.cardDistinctFactors n := by
      calc
        ((ppowers_in_set A).filter (fun q => n ∈ local_part A q)).card ≤
            (n.divisors.filter (fun q => IsPrimePow q ∧ Nat.Coprime q (n / q))).card := by
              exact Finset.card_le_card hsubset
        _ = ArithmeticFunction.cardDistinctFactors n := omega_count_eq_ppowers
    have hpow_nat : 2 ^ ArithmeticFunction.cardDistinctFactors n ≤ n := by
      calc
        2 ^ ArithmeticFunction.cardDistinctFactors n ≤ ArithmeticFunction.sigma 0 n :=
          two_pow_card_distinct_divisors_le_divisor_count hn0
        _ ≤ n := by
          rw [ArithmeticFunction.sigma_zero_apply]
          exact Nat.card_divisors_le_self n
    have hpow : (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors n ≤ n := by
      simpa [Real.rpow_natCast] using
        (show ((2 ^ ArithmeticFunction.cardDistinctFactors n : ℕ) : ℝ) ≤ n by
          exact_mod_cast hpow_nat)
    have hcardR :
        (((ppowers_in_set A).filter (fun q => n ∈ local_part A q)).card : ℝ) ≤
          ArithmeticFunction.cardDistinctFactors n := by
      exact_mod_cast hcard
    have hlog :
        (ArithmeticFunction.cardDistinctFactors n : ℝ) * log 2 ≤ log n := by
      have hlog_aux := Real.log_le_log
        (show 0 < (2 : ℝ) ^ ArithmeticFunction.cardDistinctFactors n by positivity) hpow
      simpa [Real.log_rpow, mul_comm] using hlog_aux
    have hlog2 : 0 < log 2 := Real.log_pos one_lt_two
    exact le_trans hcardR ((le_div_iff₀ hlog2).2 <| by simpa [mul_comm] using hlog)

lemma sum_powerset_prod {ι : Type*} (I : Finset ι) (x : ι → ℂ) :
    I.powerset.sum (fun J => J.prod x) = I.prod (fun i => 1 + x i) := by
  simpa using (Finset.prod_one_add (s := I) (f := x)).symm

/-- Lemma 4.11. -/
lemma orthog_rat {A : Finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0) :
    (integer_count A k : ℂ) =
      1 / (lcmA A) *
        (valid_sum_range (lcmA A)).sum (fun h => A.prod (fun n => 1 + e (k * h / n))) := by
  have hA' : ((lcmA A : ℕ) : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.2 (lcm_ne_zero_of_zero_not_mem hA)
  have hk' : (k : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.2 hk
  have hdiv :
      ∀ S : Finset ℕ, S ⊆ A →
        ((∃ z : ℤ, rec_sum S * (k : ℚ) = z) ↔
          lcmA A ∣ (k * S.sum (fun n => lcmA A / n))) := by
    intro S hS
    have hsum :
        S.sum (fun x => ((lcmA A / x : ℕ) : ℚ)) = rec_sum S * (lcmA A : ℚ) := by
      rw [rec_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x hx
      have hx0 : x ≠ 0 := by
        intro hx0
        apply hA
        exact hS (hx0 ▸ hx)
      calc
        (((lcmA A / x : ℕ) : ℚ)) = (lcmA A : ℚ) / x := by
          rw [Nat.cast_div (K := ℚ)]
          · exact Finset.dvd_lcm (hS hx)
          · exact Nat.cast_ne_zero.2 hx0
        _ = ((1 : ℚ) / x) * (lcmA A : ℚ) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, one_mul, mul_comm]
    rw [← Int.natCast_dvd_natCast, dvd_iff_exists_eq_mul_left]
    apply exists_congr
    intro z
    constructor
    · intro hz
      have hzQ :
          (k : ℚ) * S.sum (fun x => ↑(lcmA A / x)) = (z : ℚ) * (lcmA A : ℚ) := by
        calc
          (k : ℚ) * S.sum (fun x => ↑(lcmA A / x))
              = (k : ℚ) * (rec_sum S * (lcmA A : ℚ)) := by
            rw [hsum]
          _ = (rec_sum S * (k : ℚ)) * (lcmA A : ℚ) := by ring
          _ = (z : ℚ) * (lcmA A : ℚ) := by rw [hz]
      apply (Int.cast_inj (α := ℚ)).mp
      rw [Int.cast_natCast, Int.cast_mul, Int.cast_natCast, Nat.cast_mul, Nat.cast_sum]
      simpa [Rat.cast_natCast] using hzQ
    · intro hz
      have hzQ : (k : ℚ) * S.sum (fun x => ↑(lcmA A / x)) = (z : ℚ) * (lcmA A : ℚ) := by
        simpa [Int.cast_natCast, Int.cast_mul, Nat.cast_mul, Nat.cast_sum, Rat.cast_natCast] using
          congrArg (fun t : ℤ => (t : ℚ)) hz
      have hmul' :
          (lcmA A : ℚ) * (rec_sum S * (k : ℚ)) = (lcmA A : ℚ) * z := by
        calc
          (lcmA A : ℚ) * (rec_sum S * (k : ℚ))
              = (k : ℚ) * (rec_sum S * (lcmA A : ℚ)) := by ring
          _ = (k : ℚ) * S.sum (fun x => ↑(lcmA A / x)) := by rw [hsum]
          _ = (z : ℚ) * (lcmA A : ℚ) := hzQ
          _ = (lcmA A : ℚ) * z := by ring
      exact (mul_right_inj' hA').mp hmul'
  have horth :
      ∀ S : Finset ℕ, S ∈ A.powerset →
        (if (∃ z : ℤ, rec_sum S * (k : ℚ) = z) then (1 : ℕ) else 0 : ℂ) =
          1 / (lcmA A) * (valid_sum_range (lcmA A)).sum (fun h => e (k * h * rec_sum S)) := by
    intro S hS
    have ht : (-((lcmA A : ℕ) : ℤ) / 2 : ℤ) < (lcmA A : ℤ) / 2 := by
      apply Int.ediv_lt_of_lt_mul zero_lt_two
      apply lt_of_lt_of_le
      · rw [Right.neg_neg_iff, Int.natCast_pos]
        exact Nat.pos_iff_ne_zero.2 (lcm_ne_zero_of_zero_not_mem hA)
      · exact mul_nonneg (Int.ediv_nonneg (Int.natCast_nonneg _) zero_le_two) zero_le_two
    rw [Finset.mem_powerset] at hS
    rw [Nat.cast_one, if_congr (hdiv S hS) rfl rfl, mul_comm (_ : ℂ)]
    rw [← orthogonality (lcm_ne_zero_of_zero_not_mem hA) rfl ht (card_valid_sum_range _)]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.cast_mul, mul_div_assoc, mul_div_assoc, ← mul_assoc, mul_comm (i : ℝ)]
    congr 2
    rw [rec_sum, Nat.cast_sum, Finset.sum_div, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : n ≠ 0 := by
      intro hn0
      apply hA
      exact hS (hn0 ▸ hn)
    have hlcm0 : ((lcmA A : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast lcm_ne_zero_of_zero_not_mem hA
    rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_one]
    calc
      (((lcmA A / n : ℕ) : ℝ) / (lcmA A : ℝ))
          = (((lcmA A : ℕ) : ℝ) / n) / (lcmA A : ℝ) := by
              rw [Nat.cast_div (K := ℝ)]
              · exact Finset.dvd_lcm (hS hn)
              · exact Nat.cast_ne_zero.2 hn0
      _ = (1 : ℝ) / n := by
        field_simp [hlcm0, show (n : ℝ) ≠ 0 by exact_mod_cast hn0]
  rw [integer_count, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter,
    Finset.sum_congr rfl horth, ← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← sum_powerset_prod, ← e_sum, rec_sum, Rat.cast_sum, mul_sum,
    Rat.cast_div, Rat.cast_one, ← div_eq_mul_one_div, Rat.cast_natCast]

lemma integer_bound_thing {d : ℤ} (hd₀ : 0 ≤ d) (hd₁ : d ≠ 1) (hd₂ : d < 2) :
    d = 0 := by
  omega

lemma orthog_simp_aux {A : Finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
    (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k) (hA' : rec_sum A < 2 / k) :
    (valid_sum_range (lcmA A)).sum (fun h => A.prod (fun n => 1 + e (k * h / n))) = lcmA A := by
  have hcount : integer_count A k = 1 := by
    have hfilter :
        A.powerset.filter (fun S => ∃ d : ℤ, rec_sum S * k = d) = {∅} := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      constructor
      · rintro ⟨hSA, d, hd⟩
        have hkQ : (k : ℚ) ≠ 0 := by
          exact_mod_cast hk
        have hkQ_pos : (0 : ℚ) < k := by
          exact_mod_cast Nat.pos_of_ne_zero hk
        have hd0Q : (0 : ℚ) ≤ (d : ℚ) := by
          calc
            (0 : ℚ) ≤ rec_sum S * k := by
              exact mul_nonneg rec_sum_nonneg (show (0 : ℚ) ≤ k by exact_mod_cast Nat.zero_le k)
            _ = d := hd
        have hd0 : 0 ≤ d := by
          exact_mod_cast hd0Q
        have hdlt2Q : (d : ℚ) < 2 := by
          have hrec_lt : rec_sum S < 2 / k := (rec_sum_mono hSA).trans_lt hA'
          exact (by
            simpa [hd] using (_root_.lt_div_iff₀ hkQ_pos).mp hrec_lt : (d : ℚ) < 2)
        have hdlt2 : d < 2 := by
          exact_mod_cast hdlt2Q
        have hdne1 : d ≠ 1 := by
          intro hd1
          apply hS S hSA
          apply (eq_div_iff hkQ).2
          simpa [hd1] using hd
        have hdzero : d = 0 := integer_bound_thing hd0 hdne1 hdlt2
        have hrec0 : rec_sum S = 0 := by
          have hmul0 : rec_sum S * (k : ℚ) = 0 := by
            simpa [hdzero] using hd
          exact (mul_eq_zero.mp hmul0).resolve_right hkQ
        have hS0 : 0 ∉ S := by
          intro h0S
          exact hA (hSA h0S)
        exact (rec_sum_eq_zero_iff hS0).1 hrec0
      · intro hSe
        subst hSe
        exact ⟨by simp, 0, by simp⟩
    simp [integer_count, hfilter]
  have hlcm0 : ((lcmA A : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast lcm_ne_zero_of_zero_not_mem hA
  apply (div_eq_one_iff_eq hlcm0).mp
  rw [div_eq_mul_one_div, mul_comm, ← orthog_rat hA hk, hcount]
  norm_num

/-- Lemma 4.12. -/
lemma orthog_simp {A : Finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
    (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k) (hA' : rec_sum A < 2 / k) :
    (valid_sum_range (lcmA A)).sum
        (fun h => (A.prod (fun n => 1 + e (k * h / n))).re) =
      lcmA A := by
  simpa using congrArg Complex.re (orthog_simp_aux hA hk hS hA')

/-- Lemma 4.13. -/
lemma orthog_simp2 {A : Finset ℕ} {k : ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
    (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k) (hA' : rec_sum A < 2 / k)
    (hA'' : (lcmA A : ℝ) ≤ 2 ^ (A.card - 1 : ℤ)) :
    (j A).sum (fun h => (A.prod (fun n => 1 + e (k * h / n))).re) ≤ -2 ^ (A.card - 1 : ℤ) := by
  have hlcm0 := lcm_ne_zero_of_zero_not_mem hA
  rw [j, Finset.sum_erase_eq_sub (zero_mem_valid_sum_range hlcm0), orthog_simp hA hk hS hA']
  simp only [Int.cast_zero, zero_div, mul_zero, e_zero, Finset.prod_const]
  rw [sub_le_iff_le_add, neg_add_eq_sub]
  refine hA''.trans ?_
  rw [le_sub_iff_add_le]
  have hpow :
      (2 : ℝ) ^ (A.card - 1 : ℤ) + (2 : ℝ) ^ (A.card - 1 : ℤ) =
        ((1 + 1 : ℂ) ^ A.card).re := by
    calc
      (2 : ℝ) ^ (A.card - 1 : ℤ) + (2 : ℝ) ^ (A.card - 1 : ℤ)
          = (2 : ℝ) ^ (A.card - 1 : ℤ) * 2 := by ring
      _ = (2 : ℝ) ^ ((A.card - 1 : ℤ) + 1) := by
        rw [zpow_add₀ two_ne_zero, zpow_one]
      _ = (2 : ℝ) ^ (A.card : ℤ) := by simp
      _ = (2 : ℝ) ^ A.card := by rw [zpow_natCast]
      _ = ((2 : ℂ) ^ A.card).re := by
        simpa [Complex.ofReal_pow] using (Complex.ofReal_re ((2 : ℝ) ^ A.card)).symm
      _ = ((1 + 1 : ℂ) ^ A.card).re := by norm_num
  exact le_of_eq hpow

/-- Lemma 4.14. -/
lemma majorarcs_disjoint {A : Finset ℕ} {k : ℕ} {K : ℝ} (hk : k ≠ 0) (hA : K < lcmA A) :
    (Set.univ : Set ℤ).PairwiseDisjoint (major_arc_at A k K) := by
  intro t₁ _ t₂ _ ht
  change Disjoint (major_arc_at A k K t₁) (major_arc_at A k K t₂)
  rw [Finset.disjoint_left]
  by_cases hK : K < 0
  · intro h hh _
    rw [major_arc_at_of_neg hk hK] at hh
    simp at hh
  · intro h hh₁ hh₂
    have hK' : 0 ≤ K := le_of_not_gt hK
    have hh₁' :=
      (mem_major_arc_at' (A := A) (k := k) (K := K) (t := t₁) hk h).1 hh₁
    have hh₂' :=
      (mem_major_arc_at' (A := A) (k := k) (K := K) (t := t₂) hk h).1 hh₂
    have hbound : |((t₁ : ℝ) - t₂) * (lcmA A : ℝ)| ≤ K := by
      rw [sub_mul]
      refine le_trans (abs_sub_le _ ((h : ℝ) * k) _) ?_
      rw [abs_sub_comm]
      refine le_trans (add_le_add hh₁'.2 hh₂'.2) ?_
      nlinarith
    have hLnonneg : 0 ≤ (lcmA A : ℝ) := by positivity
    have hbound' : (|t₁ - t₂| : ℝ) * (lcmA A : ℝ) ≤ K := by
      simpa [Int.cast_sub, Int.cast_abs, abs_mul, abs_of_nonneg hLnonneg] using hbound
    have ht' : 1 ≤ |t₁ - t₂| := by
      rwa [← zero_add (1 : ℤ), Int.add_one_le_iff, abs_pos, sub_ne_zero]
    have ht'' : (1 : ℝ) ≤ (|t₁ - t₂| : ℝ) := by
      exact_mod_cast ht'
    have hge : (lcmA A : ℝ) ≤ (|t₁ - t₂| : ℝ) * (lcmA A : ℝ) := by
      nlinarith
    exact (not_lt.mpr hbound') (lt_of_lt_of_le hA hge)

/-- Lemma 4.15. -/
lemma useful_rewrite {A : Finset ℕ} {θ : ℝ} :
    (A.prod (fun n => 1 + e (θ / n))).re =
      2 ^ A.card * cos (π * θ * rec_sum A) * A.prod (fun n => cos (π * θ / n)) := by
  simp only [one_add_e, Finset.prod_mul_distrib, ← mul_div_assoc]
  rw [Finset.prod_const, ← Nat.cast_two, ← Nat.cast_pow, ← Complex.ofReal_prod]
  have houter :
      ((((2 ^ A.card : ℕ) : ℂ) * ∏ x ∈ A, e (θ / ↑x / 2)) *
          ↑(∏ i ∈ A, cos (π * θ / ↑i))).re =
        (((2 ^ A.card : ℕ) : ℂ) * ∏ x ∈ A, e (θ / ↑x / 2)).re *
          ∏ i ∈ A, cos (π * θ / ↑i) := by
    simpa using
      (Complex.re_mul_ofReal
        (((2 ^ A.card : ℕ) : ℂ) * ∏ x ∈ A, e (θ / ↑x / 2))
        (∏ i ∈ A, cos (π * θ / ↑i)))
  have hinner :
      (((2 ^ A.card : ℕ) : ℂ) * ∏ x ∈ A, e (θ / ↑x / 2)).re =
        (2 ^ A.card : ℝ) * (∏ x ∈ A, e (θ / ↑x / 2)).re := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Complex.re_mul_ofReal
        (∏ x ∈ A, e (θ / ↑x / 2))
        (2 ^ A.card : ℝ))
  have hsum : A.sum (fun n => θ / (n : ℝ)) = θ * rec_sum A := by
    rw [rec_sum, Rat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n hn
    simp [Rat.cast_natCast, div_eq_mul_inv, mul_comm]
  calc
    ((((2 ^ A.card : ℕ) : ℂ) * ∏ x ∈ A, e (θ / ↑x / 2)) *
        ↑(∏ i ∈ A, cos (π * θ / ↑i))).re
        = (((2 ^ A.card : ℕ) : ℂ) * ∏ x ∈ A, e (θ / ↑x / 2)).re *
            ∏ i ∈ A, cos (π * θ / ↑i) := houter
    _ = ((2 ^ A.card : ℝ) * (∏ x ∈ A, e (θ / ↑x / 2)).re) *
          ∏ i ∈ A, cos (π * θ / ↑i) := by
      rw [hinner]
    _ = ((2 ^ A.card : ℝ) * (e (∑ x ∈ A, θ / ↑x / 2)).re) *
          ∏ i ∈ A, cos (π * θ / ↑i) := by
      rw [← e_sum]
    _ = ((2 ^ A.card : ℝ) * cos ((∑ x ∈ A, θ / ↑x) * π)) *
          ∏ i ∈ A, cos (π * θ / ↑i) := by
      rw [← Finset.sum_div, e_half_re]
    _ = ((2 ^ A.card : ℝ) * cos (π * θ * rec_sum A)) *
          ∏ i ∈ A, cos (π * θ / ↑i) := by
      rw [hsum]
      simp [mul_assoc, mul_left_comm, mul_comm]
    _ = 2 ^ A.card * cos (π * θ * rec_sum A) * ∏ i ∈ A, cos (π * θ / ↑i) := by
      ring

lemma prod_major_arc_eq {α : Type*} [CommMonoid α] {A : Finset ℕ} {k : ℕ} {K : ℝ}
    (hA : 0 ∉ A) (hk : k ≠ 0) (hA' : K < lcmA A) {f : ℤ → α} :
    (major_arc A k K).prod f = (my_range' A k K).prod (fun t => (major_arc_at A k K t).prod f) := by
  rw [major_arc_eq_union hA hk]
  have hdisj : Set.PairwiseDisjoint (↑(my_range' A k K) : Set ℤ) (major_arc_at A k K) :=
    Set.PairwiseDisjoint.subset (majorarcs_disjoint hk hA') (by simp)
  simpa using
    (Finset.prod_biUnion (s := my_range' A k K) (t := major_arc_at A k K) (f := f) hdisj)

def jt (A : Finset ℕ) (k : ℕ) (K : ℝ) (t : ℝ) : Finset ℤ :=
  (my_range (K / (2 * (k : ℝ)))).filter fun h => ∃ i ∈ j A, (i : ℝ) - t * (lcmA A) / k = h

lemma prod_major_arc_at_eq {α : Type*} [CommMonoid α] {A : Finset ℕ} {k : ℕ} {K : ℝ} {t}
    {f : ℤ → α} (hk : k ∣ lcmA A) :
    (major_arc_at A k K t).prod f = (jt A k K t).prod (fun r => f (t * lcmA A / k + r)) := by
  by_cases hk0 : k = 0
  · have hlcm : lcmA A = 0 := Nat.zero_dvd.mp (by simpa [hk0] using hk)
    simp [major_arc_at, jt, j, valid_sum_range, hk0, hlcm]
  have hdiv : (k : ℤ) ∣ t * lcmA A := by
    exact dvd_mul_of_dvd_right (Int.natCast_dvd.mpr hk) t
  let c : ℤ := t * lcmA A / k
  have hc : ((c : ℤ) : ℝ) = t * (lcmA A : ℝ) / k := by
    calc
      ((c : ℤ) : ℝ) = (((t * lcmA A) / k : ℤ) : ℝ) := by rfl
      _ = (((t * lcmA A : ℤ) : ℝ) / ((k : ℤ) : ℝ)) := by
        rw [Int.cast_div hdiv (by exact_mod_cast hk0)]
      _ = (((t * lcmA A : ℤ) : ℝ) / (k : ℝ)) := by simp
      _ = ((((t : ℤ) : ℝ) * (lcmA A : ℝ)) / (k : ℝ)) := by simp
      _ = t * (lcmA A : ℝ) / k := by simp
  apply Eq.symm
  refine Finset.prod_bij (fun h _ => c + h) ?_ ?_ ?_ ?_
  · intro a ha
    rw [jt, Finset.mem_filter] at ha
    rw [mem_major_arc_at]
    rcases ha with ⟨ha, i, hi, hia⟩
    have hbounda : |(a : ℝ)| ≤ K / (2 * k) := (mem_my_range_iff).1 ha
    have hicast : (i : ℝ) = ((c + a : ℤ) : ℝ) := by
      calc
        (i : ℝ) = t * (lcmA A : ℝ) / k + a := by linarith
        _ = (c : ℝ) + a := by rw [hc]
        _ = ((c + a : ℤ) : ℝ) := by norm_num
    have hica : i = c + a := by
      exact Int.cast_inj.mp hicast
    constructor
    · simpa [hica] using hi
    · have hbound : |(c : ℝ) + a - t * (lcmA A : ℝ) / k| ≤ K / (2 * k) := by
        rw [hc]
        simpa using hbounda
      simpa [Int.cast_add] using hbound
  · intro a₁ h₁ a₂ h₂ h
    exact add_left_cancel h
  · intro b hb
    refine ⟨b - c, ?_, ?_⟩
    · rw [mem_major_arc_at] at hb
      rw [jt, Finset.mem_filter]
      rcases hb with ⟨hbj, hbbound⟩
      constructor
      · refine (mem_my_range_iff).2 ?_
        have hbc : (((b - c : ℤ) : ℤ) : ℝ) = (b : ℝ) - t * (lcmA A : ℝ) / k := by
          calc
            (((b - c : ℤ) : ℤ) : ℝ) = (b : ℝ) - c := by norm_num
            _ = (b : ℝ) - t * (lcmA A : ℝ) / k := by rw [hc]
        simpa [hbc] using hbbound
      · refine ⟨b, hbj, ?_⟩
        calc
          (b : ℝ) - t * (lcmA A : ℝ) / k = (b : ℝ) - c := by rw [hc]
          _ = (b - c : ℤ) := by norm_num
    · simp [c]
  · intro a ha
    rfl

lemma majorarcs_at {K : ℝ} {A : Finset ℕ} {k : ℕ}
    (hk : k ≠ 0) (hk' : k ∣ lcmA A) {t : ℤ} :
    (major_arc_at A k K t).sum (fun h => (A.prod (fun n => 1 + e (↑k * ↑h / ↑n))).re) =
      2 ^ A.card *
        (jt A k K t).sum
          (fun r => cos (π * k * r * rec_sum A) * A.prod (fun n => cos (π * (k * r) / n))) := by
  have hdivk : (k : ℤ) ∣ t * lcmA A := by
    exact dvd_mul_of_dvd_right (Int.natCast_dvd.mpr hk') t
  have hsum :
      (major_arc_at A k K t).sum (fun h => (A.prod (fun n => 1 + e (↑k * ↑h / ↑n))).re) =
        (jt A k K t).sum
          (fun r => (A.prod (fun n => 1 + e (↑k * ↑(t * lcmA A / k + r) / ↑n))).re) := by
    let c : ℤ := t * lcmA A / k
    have hc : c = t * lcmA A / k := rfl
    refine Eq.symm <| Finset.sum_bij (fun h _ => c + h) ?_ ?_ ?_ ?_
    · intro a ha
      rw [jt, Finset.mem_filter] at ha
      rw [mem_major_arc_at]
      rcases ha with ⟨ha, i, hi, hia⟩
      have hbounda : |(a : ℝ)| ≤ K / (2 * k) := (mem_my_range_iff).1 ha
      have hicast : (i : ℝ) = ((c + a : ℤ) : ℝ) := by
        calc
          (i : ℝ) = t * (lcmA A : ℝ) / k + a := by linarith
          _ = (c : ℝ) + a := by
            rw [hc]
            rw [Int.cast_div hdivk (by exact_mod_cast hk)]
            simp
          _ = ((c + a : ℤ) : ℝ) := by norm_num
      have hica : i = c + a := Int.cast_inj.mp hicast
      constructor
      · simpa [hica] using hi
      · have hbound : |(c : ℝ) + a - t * (lcmA A : ℝ) / k| ≤ K / (2 * k) := by
          rw [hc]
          rw [Int.cast_div hdivk (by exact_mod_cast hk)]
          simpa using hbounda
        simpa [Int.cast_add] using hbound
    · intro a₁ h₁ a₂ h₂ h
      exact add_left_cancel h
    · intro b hb
      refine ⟨b - c, ?_, ?_⟩
      · rw [mem_major_arc_at] at hb
        rw [jt, Finset.mem_filter]
        rcases hb with ⟨hbj, hbbound⟩
        constructor
        · refine (mem_my_range_iff).2 ?_
          have hbc : (((b - c : ℤ) : ℤ) : ℝ) = (b : ℝ) - t * (lcmA A : ℝ) / k := by
            calc
              (((b - c : ℤ) : ℤ) : ℝ) = (b : ℝ) - c := by norm_num
              _ = (b : ℝ) - t * (lcmA A : ℝ) / k := by
                rw [hc]
                rw [Int.cast_div hdivk (by exact_mod_cast hk)]
                simp
          simpa [hbc] using hbbound
        · refine ⟨b, hbj, ?_⟩
          calc
            (b : ℝ) - t * (lcmA A : ℝ) / k = (b : ℝ) - c := by
              rw [hc]
              rw [Int.cast_div hdivk (by exact_mod_cast hk)]
              simp
            _ = (b - c : ℤ) := by norm_num
      · simp [hc]
    · intro a ha
      simp [hc]
  rw [hsum]
  have hkR : (k : ℝ) ≠ 0 := by
    exact_mod_cast hk
  calc
    ∑ r ∈ jt A k K t, (A.prod (fun n => 1 + e (↑k * ↑(t * lcmA A / k + r) / ↑n))).re
        =
          ∑ r ∈ jt A k K t,
            2 ^ A.card *
              (cos (π * k * r * rec_sum A) * A.prod (fun n => cos (π * (k * r) / n))) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            have hprod :
                A.prod (fun n => 1 + e (↑k * ↑(t * lcmA A / k + r) / ↑n)) =
                  A.prod (fun n => 1 + e (↑k * ↑r / ↑n)) := by
              refine Finset.prod_congr rfl ?_
              intro n hn
              by_cases hn0 : n = 0
              · subst hn0
                simp
              · have hdivn : (n : ℤ) ∣ t * lcmA A := by
                  exact dvd_mul_of_dvd_right (Int.natCast_dvd.mpr <| Finset.dvd_lcm hn) t
                have hnZ : (n : ℤ) ≠ 0 := by
                  exact_mod_cast hn0
                have hnR : (n : ℝ) ≠ 0 := by
                  exact_mod_cast hn0
                have harg :
                    (↑k : ℝ) * ↑(t * lcmA A / k + r) / ↑n =
                      (((t * lcmA A / n : ℤ) : ℤ) : ℝ) + (↑k * ↑r / ↑n) := by
                  calc
                    (↑k : ℝ) * ↑(t * lcmA A / k + r) / ↑n
                        = ((↑k : ℝ) * ↑(t * lcmA A / k) + ↑k * ↑r) / ↑n := by
                            rw [Int.cast_add, mul_add]
                    _ = (↑k : ℝ) * ↑(t * lcmA A / k) / ↑n + ↑k * ↑r / ↑n := by
                          rw [add_div]
                    _ = ((((t * lcmA A : ℤ) : ℝ) / ↑n)) + ↑k * ↑r / ↑n := by
                          congr 1
                          rw [Int.cast_div_charZero hdivk]
                          field_simp [hkR, hnR]
                          simp [mul_comm, mul_left_comm]
                    _ = ((((t * lcmA A / n : ℤ) : ℤ) : ℝ)) + ↑k * ↑r / ↑n := by
                          rw [Int.cast_div_charZero hdivn]
                          simp
                calc
                  1 + e (↑k * ↑(t * lcmA A / k + r) / ↑n)
                      = 1 + e ((((t * lcmA A / n : ℤ) : ℤ) : ℝ) + (↑k * ↑r / ↑n)) := by
                          rw [harg]
                  _ = 1 + e ((((t * lcmA A / n : ℤ) : ℤ) : ℝ)) * e (↑k * ↑r / ↑n) := by
                        rw [e_add]
                  _ = 1 + e (↑k * ↑r / ↑n) := by
                        rw [e_int, one_mul]
            calc
              (A.prod (fun n => 1 + e (↑k * ↑(t * lcmA A / k + r) / ↑n))).re
                  = (A.prod (fun n => 1 + e (↑k * ↑r / ↑n))).re := by rw [hprod]
              _ = 2 ^ A.card * cos (π * ((k : ℝ) * r) * rec_sum A) *
                    A.prod (fun n => cos (π * ((k : ℝ) * r) / n)) := by
                    simpa using (useful_rewrite (A := A) (θ := (k : ℝ) * r))
              _ = 2 ^ A.card *
                    (cos (π * k * r * rec_sum A) * A.prod (fun n => cos (π * (k * r) / n))) := by
                      simp [mul_assoc, mul_left_comm, mul_comm]
    _ = 2 ^ A.card *
          (jt A k K t).sum
            (fun r => cos (π * k * r * rec_sum A) * A.prod (fun n => cos (π * (k * r) / n))) := by
          rw [Finset.mul_sum]

lemma cos_nonneg_of_abs_le {x : ℝ} (hx : |x| ≤ π / 2) : 0 ≤ cos x := by
  refine Real.cos_nonneg_of_mem_Icc ?_
  rw [Set.mem_Icc]
  exact abs_le.mp hx

/-- Lemma 4.16. -/
lemma majorarcs {M K : ℝ} {A : Finset ℕ} (hM : ∀ n : ℕ, n ∈ A → M ≤ n) (hK : 0 < K)
    (hKM : K < M) {k : ℕ} (hk' : k ∣ lcmA A) (hA₁ : (2 : ℝ) - k / M ≤ k * rec_sum A)
    (hA₂ : (k : ℝ) * rec_sum A ≤ 2) (hA₃ : A.Nonempty) :
    (0 : ℝ) ≤ (major_arc A k K).sum (fun h => (A.prod (fun n => 1 + e (k * h / n))).re) := by
  have hA : 0 ∉ A := by
    intro h0
    have hM0 : M ≤ 0 := by simpa using hM 0 h0
    linarith
  have hKlcm : K < lcmA A := by
    apply hKM.trans_le
    obtain ⟨n, hn⟩ := hA₃
    refine (hM n hn).trans ?_
    exact_mod_cast Nat.le_of_dvd
      (Nat.pos_of_ne_zero (lcm_ne_zero_of_zero_not_mem hA)) (Finset.dvd_lcm hn)
  have hk : k ≠ 0 := ne_zero_of_dvd_ne_zero (lcm_ne_zero_of_zero_not_mem hA) hk'
  have hdisj : Set.PairwiseDisjoint (↑(my_range' A k K) : Set ℤ) (major_arc_at A k K) :=
    Set.PairwiseDisjoint.subset (majorarcs_disjoint hk hKlcm) (by simp)
  rw [major_arc_eq_union hA hk, Finset.sum_biUnion hdisj]
  simp only [majorarcs_at hk hk', ← Finset.mul_sum, jt, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  refine mul_nonneg (pow_nonneg zero_le_two _) (Finset.sum_nonneg ?_)
  intro r hr
  rw [mem_my_range_iff] at hr
  refine mul_nonneg (Nat.cast_nonneg _) (mul_nonneg ?_ ?_)
  · have hcos :
      cos (π * k * r * rec_sum A) = cos (π * r * (2 - k * rec_sum A)) := by
        calc
          cos (π * k * r * rec_sum A)
              = cos (π * r * (k * rec_sum A - 2)) := by
                  rw [mul_sub, mul_mul_mul_comm, ← mul_assoc, mul_comm π r, mul_assoc ↑r π,
                    mul_comm π 2, Real.cos_sub_int_mul_two_pi]
          _ = cos (-(π * r * (k * rec_sum A - 2))) := by rw [Real.cos_neg]
          _ = cos (π * r * (2 - k * rec_sum A)) := by ring_nf
    rw [hcos]
    apply cos_nonneg_of_abs_le
    have hA₂' : 0 ≤ 2 - (k : ℝ) * (rec_sum A : ℝ) := sub_nonneg.mpr hA₂
    have hA₁' : 2 - (k : ℝ) * (rec_sum A : ℝ) ≤ (k : ℝ) / M := by linarith
    rw [abs_mul, abs_mul, abs_of_nonneg pi_pos.le, abs_of_nonneg hA₂']
    refine (mul_le_mul_of_nonneg_left hA₁' (mul_nonneg pi_pos.le (abs_nonneg _))).trans ?_
    have hM' : 0 < M := hK.trans hKM
    have hkpos : 0 < (k : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hk
    have hrk : |(r : ℝ)| * (k : ℝ) ≤ K / 2 := by
      calc
        |(r : ℝ)| * (k : ℝ) ≤ (K / (2 * (k : ℝ))) * (k : ℝ) :=
          mul_le_mul_of_nonneg_right hr hkpos.le
        _ = K / 2 := by
          field_simp [hkpos.ne']
    have hratio : |(r : ℝ)| * (k : ℝ) / M ≤ 1 / 2 := by
      apply (div_le_iff₀ hM').2
      linarith [hrk, hKM]
    calc
      π * |(r : ℝ)| * (k / M) = π * ((|(r : ℝ)| * (k : ℝ)) / M) := by ring
      _ ≤ π * (1 / 2) := mul_le_mul_of_nonneg_left hratio pi_pos.le
      _ = π / 2 := by ring
  · apply Finset.prod_nonneg
    intro n hn
    apply cos_nonneg_of_abs_le
    have h2k : 0 < 2 * (k : ℝ) := by
      exact mul_pos zero_lt_two (by exact_mod_cast Nat.pos_of_ne_zero hk)
    replace hr := ((le_div_iff₀ h2k).1 hr).trans (hKM.le.trans (hM n hn))
    have hnpos : 0 < |(n : ℝ)| := by
      apply abs_pos_of_pos
      exact hK.trans (hKM.trans_le (hM n hn))
    rw [abs_div, abs_mul, abs_mul, abs_of_nonneg pi_pos.le, div_le_div_iff₀ hnpos zero_lt_two,
      Nat.abs_cast k, Nat.abs_cast n, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ pi_pos.le
    convert hr using 1
    ring_nf

lemma prod_sdiff' {α M : Type*} [DecidableEq α] [CommGroup M]
    (f : α → M) (s₁ s₂ : Finset α) (h : s₁ ⊆ s₂) :
    (s₂ \ s₁).prod f = (s₂.prod f) / s₁.prod f := by
  rw [eq_div_iff_mul_eq', Finset.prod_sdiff h]

lemma minor_lbound {M : ℝ} {A : Finset ℕ} {K : ℝ} {k : ℕ}
    (hM : ∀ n ∈ A, M ≤ ↑n) (hK : 0 < K) (hKM : K < M) (hkA : k ∣ lcmA A) (hk : k ≠ 0)
    (hA₁ : (2 : ℝ) - k / M ≤ k * rec_sum A) (hA₂ : (k : ℝ) * rec_sum A < 2)
    (hA₃ : A.Nonempty) (hS : ∀ S ⊆ A, rec_sum S ≠ 1 / k)
    (hA₄ : (lcmA A : ℝ) ≤ 2 ^ (A.card - 1 : ℤ)) :
    1 / 2 ≤ (j A \ major_arc A k K).sum (fun h => cos_prod A (h * k)) := by
  have hA : 0 ∉ A := by
    intro h0
    have hM0 : M ≤ 0 := by simpa using hM 0 h0
    linarith
  have hkQ : (0 : ℚ) < k := by
    exact_mod_cast Nat.pos_of_ne_zero hk
  have hA₂' : rec_sum A < 2 / k := by
    have hA₂'' : (k : ℚ) * rec_sum A < 2 := by
      exact_mod_cast hA₂
    exact (_root_.lt_div_iff₀ hkQ).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hA₂'')
  let f : ℤ → ℝ := fun h => (A.prod (fun n => 1 + e (k * h / n))).re
  have hmajor : 0 ≤ (major_arc A k K).sum f := by
    simpa [f] using
      (majorarcs (M := M) (K := K) (A := A) hM hK hKM hkA hA₁ hA₂.le hA₃)
  have hsubset : major_arc A k K ⊆ j A := by
    intro h hh
    rw [major_arc, Finset.mem_filter] at hh
    exact hh.1
  have hsplit :
      (j A \ major_arc A k K).sum f + (major_arc A k K).sum f = (j A).sum f := by
    simpa [f] using (Finset.sum_sdiff hsubset (f := f))
  have hminor_re :
      (j A \ major_arc A k K).sum f ≤ -2 ^ (A.card - 1 : ℤ) := by
    have htotal : (j A).sum f ≤ -2 ^ (A.card - 1 : ℤ) :=
      orthog_simp2 hA hk hS hA₂' hA₄
    rw [← hsplit] at htotal
    linarith
  have hpoint :
      ∀ h ∈ j A \ major_arc A k K, -((2 : ℝ) ^ A.card * cos_prod A (h * k)) ≤ f h := by
    intro h hh
    let z : ℂ := A.prod (fun n => 1 + e (k * h / n))
    have hzre : |z.re| ≤ ‖z‖ := by
      simpa using Complex.abs_re_le_norm z
    have hznorm : ‖z‖ = (2 : ℝ) ^ A.card * cos_prod A (h * k) := by
      dsimp [z]
      rw [norm_prod]
      simp_rw [abs_one_add_e]
      rw [Finset.prod_mul_distrib]
      simp [cos_prod, Int.cast_mul, div_eq_mul_inv, mul_assoc, mul_comm]
    have hbound : -((2 : ℝ) ^ A.card * cos_prod A (h * k)) ≤ z.re := by
      rw [← hznorm]
      exact (abs_le.mp hzre).1
    simpa [f, z] using hbound
  have hminor_cp :
      -((2 : ℝ) ^ A.card * (j A \ major_arc A k K).sum (fun h => cos_prod A (h * k))) ≤
        (j A \ major_arc A k K).sum f := by
    calc
      -((2 : ℝ) ^ A.card * (j A \ major_arc A k K).sum (fun h => cos_prod A (h * k)))
          = (j A \ major_arc A k K).sum (fun h => -((2 : ℝ) ^ A.card * cos_prod A (h * k))) := by
              rw [Finset.sum_neg_distrib, Finset.mul_sum]
      _ ≤ (j A \ major_arc A k K).sum (fun h => f h) := by
            exact Finset.sum_le_sum hpoint
      _ = (j A \ major_arc A k K).sum f := rfl
  have hcard1 : 1 ≤ A.card := Finset.one_le_card.mpr hA₃
  have hpow : (2 : ℝ) ^ (A.card - 1 : ℤ) = (2 : ℝ) ^ A.card / 2 := by
    rw [zpow_sub₀ two_ne_zero]
    simp
  have hfinal :
      -((2 : ℝ) ^ A.card * (j A \ major_arc A k K).sum (fun h => cos_prod A (h * k))) ≤
        -(2 : ℝ) ^ (A.card - 1 : ℤ) := by
    exact le_trans hminor_cp hminor_re
  rw [hpow] at hfinal
  have hpowpos : 0 < (2 : ℝ) ^ A.card := pow_pos zero_lt_two _
  nlinarith

lemma Function.Antiperiodic.abs_periodic {f : ℝ → ℝ} {c : ℝ}
    (h : Function.Antiperiodic f c) :
    Function.Periodic (abs ∘ f) c := by
  intro x
  simp [Function.comp, h x, abs_neg]

lemma abs_cos_periodic : Function.Periodic (fun i => |cos i|) π := by
  exact Function.Antiperiodic.abs_periodic Real.cos_antiperiodic

lemma abs_cos_period {x y n : ℤ} (h : x % n = y % n) :
    |cos (π * (x / n))| = |cos (π * (y / n))| := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp at h
    simp [h]
  have hdiv : n ∣ x - y := by
    rwa [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero]
  obtain ⟨k, hk⟩ := hdiv
  rw [sub_eq_iff_eq_add'] at hk
  rw [hk, Int.cast_add, Int.cast_mul, add_div, mul_div_cancel_left₀]
  · rw [mul_add, mul_comm π k]
    exact abs_cos_periodic.int_mul k _
  · exact_mod_cast hn

lemma cos_prod_bound {A : Finset ℕ} {N : ℕ} (t : ℤ) (hA' : 0 ∉ A)
    (hA : ∀ n ∈ A, n ≤ N) (h' : ℕ → ℤ) (hh'₁ : ∀ n ∈ A, h' n % n = t % n)
    (hh'₂ : ∀ n ∈ A, (|h' n| : ℝ) ≤ n / 2) :
    cos_prod A t ≤ exp (- (2 / N ^ 2) * A.sum (fun n => h' n ^ 2)) := by
  rw [cos_prod]
  have hrhs :
      exp (- (2 / (N : ℝ) ^ 2) * ↑(A.sum fun n => h' n ^ 2)) =
        A.prod (fun n => exp (-(2 / (N : ℝ) ^ 2) * (h' n : ℝ) ^ 2)) := by
    rw [show -(2 / (N : ℝ) ^ 2) * ↑(A.sum fun n => h' n ^ 2) =
        A.sum (fun n => (-(2 / (N : ℝ) ^ 2) * (h' n : ℝ) ^ 2)) by
          rw [Int.cast_sum]
          rw [Finset.mul_sum]
          congr with n
          rw [Int.cast_pow]]
    rw [Real.exp_sum]
  rw [hrhs]
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) ?_
  intro n hn
  have hn' : n ≠ 0 := ne_of_mem_of_not_mem hn hA'
  rw [neg_mul, div_mul_comm, ← div_pow, ← mul_comm (2 : ℝ), mul_div_assoc,
    ← Int.cast_natCast n, abs_cos_period (hh'₁ _ hn).symm, Int.cast_natCast]
  apply (cos_bound_abs _).trans
  · have hn0 : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn'
    have hNn : (n : ℝ) ≤ N := by
      exact_mod_cast hA _ hn
    have hN0 : 0 < (N : ℝ) := lt_of_lt_of_le hn0 hNn
    apply Real.exp_le_exp.mpr
    have hcmp : 2 * ((h' n : ℝ) / N) ^ 2 ≤ 2 * ((h' n : ℝ) / n) ^ 2 := by
      have hsq : (n : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
        nlinarith
      field_simp [hn0.ne', hN0.ne']
      nlinarith [sq_nonneg ((h' n : ℝ)), hsq]
    linarith
  · have hn0 : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn'
    rw [abs_div, abs_of_pos hn0, div_le_iff₀ hn0]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hh'₂ _ hn

lemma minor1_bound_aux :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ {K M T : ℝ} {A : Finset ℕ},
      8 ≤ M → 0 ∉ A → 0 < T →
      (∀ q ∈ ppowers_in_set A, ↑q ≤ (T * K ^ 2) / (N ^ 2 * log N)) →
        ↑(lcmA A) ≤ exp ((T * K ^ 2) / (4 * N ^ 2)) := by
  obtain ⟨C, hC₀, hC⟩ := smooth_lcm
  filter_upwards
    [ Filter.eventually_gt_atTop (1 : ℕ)
    , (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (Filter.eventually_ge_atTop (4 * C)) ] with N hN₁ hN' K M T A hM hA hT hA₄
  change 4 * C ≤ log N at hN'
  have hN₁' : (1 : ℝ) < N := by
    exact_mod_cast hN₁
  have h₁ : (0 : ℝ) < N ^ 2 := by
    exact pow_pos (zero_lt_one.trans hN₁') 2
  have hden : 0 < (N : ℝ) ^ 2 * log N := by
    exact mul_pos h₁ (Real.log_pos hN₁')
  refine (hC _ (div_nonneg ?_ hden.le) _ hA hA₄).trans ?_
  · exact mul_nonneg hT.le (sq_nonneg K)
  rw [exp_le_exp, mul_div_assoc',
    div_le_div_iff₀ hden (mul_pos (show (0 : ℝ) < 4 by norm_num) h₁), mul_right_comm,
    mul_comm (T * K ^ 2), mul_comm _ (log N), ← mul_assoc C, mul_assoc, mul_assoc (log N),
    mul_comm C]
  exact mul_le_mul_of_nonneg_right hN' (mul_nonneg h₁.le (mul_nonneg hT.le (sq_nonneg K)))

lemma exists_representative (t : ℤ) {n : ℕ} (hn : n ≠ 0) :
    ∃ tn : ℤ, tn % n = t % n ∧ |tn| ≤ n / 2 := by
  refine ⟨Int.bmod t n, ?_, ?_⟩
  · exact
      (Int.emod_eq_emod_iff_emod_sub_eq_zero).2
        (Int.emod_eq_zero_of_dvd Int.dvd_bmod_sub_self)
  · refine abs_le.mpr ?_
    constructor
    · simpa using Int.le_bmod (x := t) (m := n) (Nat.pos_of_ne_zero hn)
    · have hlt : Int.bmod t n < (n + 1) / 2 :=
        Int.bmod_lt (x := t) (m := n) (Nat.pos_of_ne_zero hn)
      omega

lemma missing_bridge_sum {A : Finset ℕ} {t : ℤ} {K M : ℝ} {I : Finset ℤ} {tn : ℕ → ℤ}
    (hK : 0 < K) (hI : I = Finset.Icc ⌈(t : ℝ) - K / 2⌉ ⌊(t : ℝ) + K / 2⌋)
    (htn₁ : ∀ n : ℕ, n ∈ A → tn n % ↑n = t % ↑n)
    (hI' : M ≤ ((A.filter fun n : ℕ => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card : ℝ)) :
    M * (K ^ 2 / 4) ≤ A.sum (fun n => (tn n : ℝ) ^ 2) := by
  let A' := A.filter fun n : ℕ => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)
  have hsubset : A' ⊆ A := Finset.filter_subset _ _
  refine
    le_trans ?_
      (Finset.sum_le_sum_of_subset_of_nonneg hsubset fun _ _ _ => sq_nonneg _)
  have hcard : M * (K ^ 2 / 4) ≤ (A'.card : ℝ) * (K ^ 2 / 4) := by
    exact mul_le_mul_of_nonneg_right hI' (by positivity)
  refine hcard.trans ?_
  calc
    (A'.card : ℝ) * (K ^ 2 / 4) = A'.sum (fun _ : ℕ => K ^ 2 / 4) := by
      simp [nsmul_eq_mul]
    _ ≤ A'.sum (fun n => (tn n : ℝ) ^ 2) := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hnA : n ∈ A := (Finset.mem_filter.mp hn).1
      have hnodvd : ∀ x ∈ I, ¬ ((n : ℤ) ∣ x) := (Finset.mem_filter.mp hn).2
      have hnotlt : ¬ |(tn n : ℝ)| < K / 2 := by
        intro hi
        have hi' := abs_lt.mp hi
        have hx : t - tn n ∈ I := by
          rw [hI, Finset.mem_Icc]
          constructor
          · refine Int.ceil_le.mpr ?_
            have hleft : (t : ℝ) - K / 2 < (t : ℝ) - (tn n : ℝ) := by
              linarith
            exact le_of_lt (by simpa using hleft)
          · refine Int.le_floor.mpr ?_
            have hright : (t : ℝ) - (tn n : ℝ) < (t : ℝ) + K / 2 := by
              linarith
            exact le_of_lt (by simpa using hright)
        have hcontra := hnodvd _ hx
        rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero, eq_comm] at hcontra
        exact hcontra (htn₁ _ hnA)
      have habs : K / 2 ≤ |(tn n : ℝ)| := not_lt.mp hnotlt
      have hk2 : 0 ≤ K / 2 := by linarith
      calc
        K ^ 2 / 4 = (K / 2) ^ 2 := by ring
        _ ≤ |(tn n : ℝ)| ^ 2 := by
          nlinarith [habs, abs_nonneg (tn n : ℝ)]
        _ = (tn n : ℝ) ^ 2 := by rw [sq_abs]

lemma missing_bridge (A : Finset ℕ) {N : ℕ} {t : ℤ} {K M : ℝ} (hA' : 0 ∉ A)
    (hA : ∀ n ∈ A, n ≤ N) {I : Finset ℤ} (hK : 0 < K)
    (hI : I = Finset.Icc ⌈(t : ℝ) - K / 2⌉ ⌊(t : ℝ) + K / 2⌋)
    (hI' : M ≤ ((A.filter fun n : ℕ => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card : ℝ)) :
    cos_prod A t ≤ exp (- (M * K ^ 2 / (2 * N ^ 2))) := by
  have hrepr : ∀ n : ℕ, ∃ tn : ℤ, n ∈ A → tn % n = t % n ∧ |tn| ≤ n / 2 := by
    intro n
    by_cases hn : n ∈ A
    · have hn' : n ≠ 0 := ne_of_mem_of_not_mem hn hA'
      obtain ⟨tn, htn₁, htn₂⟩ := exists_representative t hn'
      exact ⟨tn, fun _ => ⟨htn₁, htn₂⟩⟩
    · refine ⟨0, ?_⟩
      simp [hn]
  choose tn htn₁ htn₂ using hrepr
  refine (cos_prod_bound (A := A) (N := N) t hA' hA tn htn₁ ?_).trans ?_
  · intro n hn
    have hz : |tn n| ≤ n / 2 := htn₂ n hn
    have hzInt : (((tn n).natAbs : ℕ) : ℤ) ≤ (n / 2 : ℕ) := by
      have hz' := hz
      rw [Int.abs_eq_natAbs] at hz'
      exact hz'
    have hzReal : (((tn n).natAbs : ℕ) : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by
      exact_mod_cast hzInt
    have hzReal' : |((tn n : ℤ) : ℝ)| ≤ ((n / 2 : ℕ) : ℝ) := by
      simpa [Int.cast_abs] using hzReal
    exact hzReal'.trans Nat.cast_div_le
  · have hsum : M * (K ^ 2 / 4) ≤ A.sum (fun n => (tn n : ℝ) ^ 2) :=
      missing_bridge_sum hK hI htn₁ hI'
    have hsum' : M * (K ^ 2 / 4) ≤ ↑(A.sum fun n => tn n ^ 2) := by
      simpa [Int.cast_sum, Int.cast_pow] using hsum
    have hmul :
        -((2 : ℝ) / N ^ 2) * ↑(A.sum fun n => tn n ^ 2) ≤
          -((2 : ℝ) / N ^ 2) * (M * (K ^ 2 / 4)) := by
      exact mul_le_mul_of_nonpos_left hsum'
        (neg_nonpos.2 (div_nonneg zero_le_two (sq_nonneg (N : ℝ))))
    refine (Real.exp_le_exp.mpr hmul).trans_eq ?_
    congr 1
    ring

lemma minor1_bound :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ {K M T : ℝ} (k : ℕ) {A : Finset ℕ},
      8 ≤ M → A.Nonempty → (∀ n ∈ A, M ≤ ↑n) → 0 < K → 0 < T →
      (∀ n ∈ A, n ≤ N) →
      (∀ q ∈ ppowers_in_set A, ↑q ≤ (T * K ^ 2) / (N ^ 2 * log N)) →
        (minor_arc₁ A k K T).sum (fun h => cos_prod A (h * k)) ≤ 8⁻¹ := by
  filter_upwards [minor1_bound_aux] with N hNaux K M T k A hM hAne hLower hK hT hUpper hSmooth
  have hA0 : 0 ∉ A := by
    intro h0
    have : M ≤ 0 := by simpa using hLower 0 h0
    linarith
  suffices hpoint :
      ∀ h ∈ minor_arc₁ A k K T, cos_prod A (h * k) ≤ ((lcmA A : ℝ) ^ 2)⁻¹ by
    have hsum :
        (minor_arc₁ A k K T).sum (fun h => cos_prod A (h * k)) ≤
          ((minor_arc₁ A k K T).card : ℝ) * (((lcmA A : ℝ) ^ 2)⁻¹) := by
      simpa [nsmul_eq_mul] using
        (Finset.sum_le_card_nsmul (minor_arc₁ A k K T) (fun h => cos_prod A (h * k))
          (((lcmA A : ℝ) ^ 2)⁻¹) hpoint)
    refine hsum.trans ?_
    have hjsubset : j A ⊆ valid_sum_range (lcmA A) := by
      intro x hx
      rw [j, Finset.mem_erase] at hx
      exact hx.2
    have hcard : ((minor_arc₁ A k K T).card : ℝ) ≤ lcmA A := by
      exact_mod_cast
        (Finset.card_le_card ((Finset.filter_subset _ _).trans Finset.sdiff_subset)).trans
          ((Finset.card_le_card hjsubset).trans_eq (card_valid_sum_range _))
    have hlcmge : (8 : ℝ) ≤ lcmA A := by
      obtain ⟨n, hn⟩ := hAne
      have hnle : (8 : ℝ) ≤ n := hM.trans (hLower n hn)
      exact hnle.trans (by
        exact_mod_cast Nat.le_of_dvd
          (Nat.pos_of_ne_zero (lcm_ne_zero_of_zero_not_mem hA0))
          (Finset.dvd_lcm hn))
    have hlcm0 : (lcmA A : ℝ) ≠ 0 := by
      exact_mod_cast lcm_ne_zero_of_zero_not_mem hA0
    calc
      ((minor_arc₁ A k K T).card : ℝ) * (((lcmA A : ℝ) ^ 2)⁻¹)
          = ((minor_arc₁ A k K T).card : ℝ) / (lcmA A : ℝ) ^ 2 := by
              rw [div_eq_mul_inv]
      _ ≤ (lcmA A : ℝ) / (lcmA A : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right hcard (sq_nonneg _)
      _ = 1 / (lcmA A : ℝ) := by
        field_simp [hlcm0]
      _ ≤ 1 / 8 := by
        exact one_div_le_one_div_of_le (by norm_num) hlcmge
      _ = (8 : ℝ)⁻¹ := by norm_num
  intro h hh
  rw [minor_arc₁, Finset.mem_filter] at hh
  have hI : I h K k =
      Finset.Icc ⌈((h * k : ℤ) : ℝ) - K / 2⌉ ⌊((h * k : ℤ) : ℝ) + K / 2⌋ := by
    simp [I, integer_range]
  refine (missing_bridge (A := A) (N := N) (t := h * k) hA0 hUpper hK hI hh.2).trans ?_
  have hlcm0 : (lcmA A : ℝ) ≠ 0 := by
    exact_mod_cast lcm_ne_zero_of_zero_not_mem hA0
  have hlcmpos : 0 < (lcmA A : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (lcm_ne_zero_of_zero_not_mem hA0)
  rw [Real.exp_neg]
  refine (inv_le_inv₀ (Real.exp_pos _) (sq_pos_iff.2 hlcm0)).2 ?_
  refine (pow_le_pow_left₀ hlcmpos.le (hNaux hM hA0 hT hSmooth) 2).trans ?_
  refine le_of_eq ?_
  rw [sq, ← Real.exp_add]
  congr 1
  ring_nf

lemma prod_swapping {A : Finset ℕ} (x : ℕ → ℝ) :
    A.prod
        (fun n => ((ppowers_in_set A).filter (fun q => n ∈ local_part A q)).prod (fun _ => x n)) =
      (ppowers_in_set A).prod (fun q => (local_part A q).prod x) := by
  simp only [Finset.prod_filter]
  rw [Finset.prod_comm]
  simp only [← Finset.prod_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr local_part_subset]

lemma minor2_ind_bound_part_one {N : ℕ} {A : Finset ℕ} {t : ℤ}
    (hA : 0 ∉ A) (hA' : ∀ n ∈ A, n ≤ N) (hN : 2 ≤ N) :
    cos_prod A t ≤
      (ppowers_in_set A).prod (fun q => (cos_prod (local_part A q) t) ^ (2 * log N)⁻¹) := by
  let Q_ : ℕ → Finset ℕ :=
    fun n ↦ (ppowers_in_set A).filter (fun q => n ∈ local_part A q)
  have hq : ∀ n ∈ A, ((Q_ n).card : ℝ) ≤ 2 * log N := by
    intro n hn
    have hn0 : n ≠ 0 := ne_of_mem_of_not_mem hn hA
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero hn0
    have hlogn_nonneg : 0 ≤ log n := by
      exact Real.log_nonneg (by exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0))
    have htriv : ((Q_ n).card : ℝ) ≤ log n / log 2 := by
      simpa [Q_] using (triv_q_bound hA n)
    refine htriv.trans ?_
    rw [div_eq_mul_inv, mul_comm]
    refine mul_le_mul ?_ (Real.log_le_log hnpos (by exact_mod_cast hA' n hn)) hlogn_nonneg
      zero_le_two
    have hhalf : (1 / 2 : ℝ) ≤ log 2 := le_trans (by norm_num) Real.log_two_gt_d9.le
    simpa [one_div] using ((one_div_le (Real.log_pos one_lt_two) zero_lt_two).2 hhalf)
  simp only [cos_prod]
  have hrewrite :
      (ppowers_in_set A).prod
          (fun q => (∏ n ∈ local_part A q, |cos (π * t / n)|) ^ (2 * log N)⁻¹) =
        (ppowers_in_set A).prod
          (fun q => ∏ n ∈ local_part A q, |cos (π * t / n)| ^ (2 * log N)⁻¹) := by
    refine Finset.prod_congr rfl ?_
    intro q hq'
    symm
    exact Real.finsetProd_rpow _ _ (fun n hn ↦ abs_nonneg _) _
  rw [hrewrite, ← prod_swapping]
  change ∏ n ∈ A, |cos (π * t / n)| ≤
    ∏ n ∈ A, ∏ _x ∈ Q_ n, |cos (π * t / n)| ^ (2 * log N)⁻¹
  simp_rw [Finset.prod_const]
  refine Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _) ?_
  intro n hn
  rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  refine Real.self_le_rpow_of_le_one (abs_nonneg _) (abs_cos_le_one _) ?_
  rw [← div_eq_inv_mul]
  refine (div_le_one ?_).2 (hq n hn)
  exact mul_pos zero_lt_two (Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN))

lemma minor2_ind_bound {N : ℕ} {A : Finset ℕ} {t : ℤ} {K L : ℝ} (I : Finset ℤ)
    (hA : 0 ∉ A) (hK : 0 < K) (hA' : ∀ n ∈ A, n ≤ N) (hN : 2 ≤ N)
    (hI : I = Finset.Icc ⌈(t : ℝ) - K / 2⌉ ⌊(t : ℝ) + K / 2⌋)
    (hq : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ L * K ^ 2 / (16 * N ^ 2 * (log N) ^ 2)) :
    cos_prod A t ≤ N ^ (-4 * (ppowers_in_set A \ interval_rare_ppowers I A L).card : ℝ) := by
  refine (minor2_ind_bound_part_one hA hA' hN).trans ?_
  rw [← Finset.prod_sdiff (interval_rare_ppowers_subset I L)]
  suffices hq' :
      ∀ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L,
        cos_prod (local_part A q) t ≤ (N : ℝ) ^ (-8 * log N) by
    have hq'' :
        ∀ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L,
          cos_prod (local_part A q) t ^ (2 * log N)⁻¹ ≤ (N : ℝ) ^ (-4 : ℝ) := by
      intro q hq
      have hlogpos : 0 < log (N : ℝ) := by
        exact Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN)
      calc
        cos_prod (local_part A q) t ^ (2 * log N)⁻¹
            ≤ ((N : ℝ) ^ (-8 * log N)) ^ (2 * log N)⁻¹ :=
              Real.rpow_le_rpow cos_prod_nonneg (hq' q hq)
                (inv_nonneg.2 <| mul_nonneg zero_le_two <|
                  Real.log_nonneg (Nat.one_le_cast.2 (one_le_two.trans hN)))
        _ = (N : ℝ) ^ (-4 : ℝ) := by
            rw [← Real.rpow_mul (show 0 ≤ (N : ℝ) by exact_mod_cast Nat.zero_le N)]
            congr 2
            field_simp [hlogpos.ne']
            ring
    have hq''' :
        ∀ q ∈ interval_rare_ppowers I A L,
          cos_prod (local_part A q) t ^ (2 * log N)⁻¹ ≤ 1 := by
      intro q hq
      apply Real.rpow_le_one cos_prod_nonneg cos_prod_le_one
      rw [inv_nonneg]
      exact mul_nonneg zero_le_two <| Real.log_nonneg <| by
        rw [Nat.one_le_cast]
        exact one_le_two.trans hN
    have hprod₁ :
        ∏ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L,
            cos_prod (local_part A q) t ^ (2 * log N)⁻¹ ≤
          ∏ q ∈ ppowers_in_set A \ interval_rare_ppowers I A L, (N : ℝ) ^ (-4 : ℝ) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro q hq
        exact Real.rpow_nonneg cos_prod_nonneg _
      · intro q hq
        exact hq'' q hq
    have hprod₂ :
        ∏ q ∈ interval_rare_ppowers I A L, cos_prod (local_part A q) t ^ (2 * log N)⁻¹ ≤
          ∏ q ∈ interval_rare_ppowers I A L, (1 : ℝ) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro q hq
        exact Real.rpow_nonneg cos_prod_nonneg _
      · intro q hq
        exact hq''' q hq
    refine (mul_le_mul hprod₁ hprod₂ ?_ ?_).trans ?_
    · exact Finset.prod_nonneg fun i hi ↦ Real.rpow_nonneg cos_prod_nonneg _
    · exact
        Finset.prod_nonneg fun i hi ↦
          Real.rpow_nonneg (show 0 ≤ (N : ℝ) by exact_mod_cast Nat.zero_le N) _
    · rw [Finset.prod_const, Finset.prod_const_one, mul_one, ← Real.rpow_natCast,
        ← Real.rpow_mul (show 0 ≤ (N : ℝ) by exact_mod_cast Nat.zero_le N)]
  intro q hq'
  have hqmem : q ∈ ppowers_in_set A := (Finset.mem_sdiff.mp hq').1
  have hqnot : q ∉ interval_rare_ppowers I A L := (Finset.mem_sdiff.mp hq').2
  have hqcount :
      L / q ≤
        (((local_part A q).filter
            fun n : ℕ => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card : ℝ) := by
    letI : DecidableEq ℤ := Classical.decEq ℤ
    let sZ : Finset ℤ := (local_part A q).image (fun n : ℕ => (n : ℤ))
    have hcardeq :
        (((sZ.filter fun n : ℤ => ∀ x ∈ I, ¬ n ∣ x).card : ℝ)) =
          (((local_part A q).filter
              fun n : ℕ => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card : ℝ) := by
      dsimp [sZ]
      rw [Finset.filter_image, Finset.card_image_of_injective _ Nat.cast_injective]
    by_contra hlt
    apply hqnot
    rw [interval_rare_ppowers, Finset.mem_filter]
    have hlt' :
        (((sZ.filter fun n : ℤ => ∀ x ∈ I, ¬ n ∣ x).card : ℝ)) < L / q := by
      rw [hcardeq]
      exact not_le.mp hlt
    simpa [sZ, Finset.bind_def, Finset.pure_def, Finset.biUnion_singleton] using
      (show q ∈ ppowers_in_set A ∧
          (((sZ.filter fun n : ℤ => ∀ x ∈ I, ¬ n ∣ x).card : ℝ)) < L / q from
        ⟨hqmem, hlt'⟩)
  refine (missing_bridge (A := local_part A q) (M := L / q) (zero_mem_local_part_iff hA)
    (fun _ hn ↦ hA' _ (filter_subset _ _ hn)) hK hI hqcount).trans ?_
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast zero_lt_two.trans_le hN
  have hlogpos : 0 < log (N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hN)
  rw [← Real.le_log_iff_exp_le (Real.rpow_pos_of_pos hN0 _), Real.log_rpow hN0]
  have hqpos : 0 < (q : ℝ) := by
    rw [Nat.cast_pos]
    rw [mem_ppowers_in_set] at hqmem
    exact hqmem.1.pos
  have hqbound : (q : ℝ) ≤ L * K ^ 2 / (16 * N ^ 2 * (log N) ^ 2) := hq q hqmem
  have hqbound' : 16 * (N : ℝ) ^ 2 * (log (N : ℝ)) ^ 2 * q ≤ L * K ^ 2 := by
    have hden' : 0 < 16 * (N : ℝ) ^ 2 * (log (N : ℝ)) ^ 2 := by positivity
    have hmul : q * (16 * (N : ℝ) ^ 2 * (log (N : ℝ)) ^ 2) ≤ L * K ^ 2 := by
      exact (_root_.le_div_iff₀ hden').1 hqbound
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hmain : 8 * log (N : ℝ) * log (N : ℝ) ≤ L * K ^ 2 / (2 * N ^ 2 * q) := by
    have hden : 0 < 2 * (N : ℝ) ^ 2 * q := by positivity
    refine (_root_.le_div_iff₀ hden).2 ?_
    nlinarith [hqbound', sq_nonneg (log (N : ℝ))]
  have hdiv : L / q * K ^ 2 / (2 * N ^ 2) = L * K ^ 2 / (2 * N ^ 2 * q) := by
    field_simp [hqpos.ne']
  rw [hdiv]
  nlinarith [hmain]

lemma powerset_sum_pow {α : Type*} {s : Finset α} {x : ℝ} :
    s.powerset.sum (fun t => x ^ t.card) = (1 + x) ^ s.card := by
  simpa using (Finset.prod_one_add (s := s) (f := fun _ : α => x)).symm

lemma powerset_sum_pow' {α : Type*} [DecidableEq α] {s : Finset α} {x : ℝ} :
    s.powerset.sum (fun t => x ^ (s \ t).card) = (1 + x) ^ s.card := by
  calc
    s.powerset.sum (fun t => x ^ (s \ t).card) = s.powerset.sum (fun t => x ^ t.card) := by
      refine Finset.sum_bij' (i := fun t _ => s \ t) (j := fun t _ => s \ t) ?_ ?_ ?_ ?_ ?_
      · intro t ht
        exact Finset.mem_powerset.2 (Finset.sdiff_subset : s \ t ⊆ s)
      · intro t ht
        exact Finset.mem_powerset.2 (Finset.sdiff_subset : s \ t ⊆ s)
      · intro t ht
        exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 ht)
      · intro t ht
        exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.1 ht)
      · intro t ht
        rfl
    _ = (1 + x) ^ s.card := powerset_sum_pow

lemma lcm_Q {A : Finset ℕ} (hA : 0 ∉ A) : lcmA (ppowers_in_set A) = lcmA A := by
  apply Nat.dvd_antisymm
  · refine Finset.lcm_dvd_iff.2 ?_
    intro i hi
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff i).1 (mem_ppowers_in_set.1 hi).1
    rw [mem_ppowers_in_set' hp hk.ne'] at hi
    obtain ⟨n, hn, rfl⟩ := hi
    exact (Nat.ordProj_dvd _ _).trans (Finset.dvd_lcm hn)
  · refine Finset.lcm_dvd_iff.2 ?_
    intro n hn
    have hn' : n ≠ 0 := ne_of_mem_of_not_mem hn hA
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    have hpow : p ^ n.factorization p ∣ lcmA (ppowers_in_set A) := by
      by_cases hnp : n.factorization p = 0
      · simp [hnp]
      · apply Finset.dvd_lcm
        rw [mem_ppowers_in_set' hp hnp]
        exact ⟨n, hn, rfl⟩
    by_cases hk : k = 0
    · simp [hk]
    · exact (pow_dvd_pow _ ((hp.pow_dvd_iff_le_factorization hn').1 hpk)).trans hpow

lemma d_strict_subset {K L δ : ℝ} {k : ℕ} {A : Finset ℕ} (hA : 0 ∉ A) (hk : k ≠ 0)
    (z : ∀ h ∈ minor_arc₂ A k K δ,
      ∃ x ∈ I h K k, ↑(lcmA (interval_rare_ppowers (I h K k) A L)) ∣ x) :
    (minor_arc₂ A k K δ).filter
        (fun h => interval_rare_ppowers (I h K k) A L ⊂ ppowers_in_set A) =
      minor_arc₂ A k K δ := by
  ext h
  constructor
  · intro hh
    exact (Finset.mem_filter.mp hh).1
  · intro hh
    rw [Finset.mem_filter]
    refine ⟨hh, (Finset.ssubset_iff_subset_ne.2 ?_)⟩
    refine ⟨interval_rare_ppowers_subset (I h K k) L, ?_⟩
    intro hEq
    have hhminor : h ∈ minor_arc₂ A k K δ := hh
    rw [minor_arc₂, Finset.mem_sdiff] at hh
    rcases hh with ⟨hh, _⟩
    rcases Finset.mem_sdiff.mp hh with ⟨hj, hmajor⟩
    rcases z h hhminor with ⟨x, hxI, hdivx⟩
    rw [hEq, lcm_Q hA] at hdivx
    rcases hdivx with ⟨t, rfl⟩
    have hxI' : (|h * k - t * lcmA A| : ℝ) ≤ K / 2 := by
      have hxI'' := (mem_I' (h := h) (K := K) (k := k) (z := (lcmA A : ℤ) * t)).1 hxI
      simpa [Int.cast_mul, mul_comm, mul_left_comm, mul_assoc, abs_sub_comm] using hxI''
    apply hmajor
    rw [major_arc, Finset.mem_filter]
    exact ⟨hj, ⟨t, (mem_major_arc_at' hk h).2 ⟨hj, hxI'⟩⟩⟩

lemma cast_lcm {x y : ℕ} : (lcm x y : ℤ) = lcm (x : ℤ) y := by
  rw [← Int.coe_lcm]

lemma Finset.cast_lcm {x : Finset ℕ} : ((x.lcm id : ℕ) : ℤ) = x.lcm (fun n => (n : ℤ)) := by
  classical
  refine Finset.induction_on x ?_ ?_
  · simp
  · intro a s ha hs
    simpa only [Finset.lcm_insert, id_eq] using
      hs ▸ (UnitFractions.cast_lcm (x := a) (y := s.lcm id))

lemma cast_lcm_dvd {x : Finset ℕ} {z : ℤ} (h : ∀ i ∈ x, ↑i ∣ z) :
    ↑(lcmA x) ∣ z := by
  rw [Finset.cast_lcm]
  exact Finset.lcm_dvd h

lemma ssubsets_subset_powerset {α : Type*} [DecidableEq α] {s : Finset α} :
    s.ssubsets ⊆ s.powerset := by
  intro t ht
  exact Finset.mem_powerset.2 (Finset.mem_ssubsets.1 ht).1

lemma thing_le_four {N : ℕ} : ((N : ℝ)⁻¹ + 1) ^ N ≤ 4 := by
  rcases eq_or_ne N 0 with rfl | hN
  · norm_num
  · refine le_trans ?_ (Real.exp_one_lt_d9.le.trans (by norm_num))
    refine (pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp ((N : ℝ)⁻¹)) N).trans ?_
    rw [← Real.exp_nat_mul ((N : ℝ)⁻¹) N]
    simp [hN]

lemma ppowers_in_set_le {N : ℕ} {A : Finset ℕ} (hA' : ∀ n : ℕ, n ∈ A → n ≤ N) :
    ∀ q ∈ ppowers_in_set A, 1 ≤ q ∧ q ≤ N := by
  intro q hq
  rcases Finset.mem_biUnion.mp hq with ⟨n, hnA, hq⟩
  rw [Finset.mem_filter, Nat.mem_divisors] at hq
  rcases hq with ⟨⟨hqdiv, hn0⟩, hpp, _⟩
  constructor
  · exact hpp.one_lt.le
  · exact (Nat.le_of_dvd hn0.bot_lt hqdiv).trans (hA' n hnA)

lemma minor2_bound_end {k : ℕ} {A : Finset ℕ} (N : ℕ) (hN : 2 ≤ N) (hkN : k ≤ N / 192)
    (hA' : ∀ n : ℕ, n ∈ A → n ≤ N) :
    6 * (k : ℝ) * (N : ℝ)⁻¹ *
        (ppowers_in_set A).ssubsets.sum
          (fun x => ((N : ℝ)⁻¹) ^ (ppowers_in_set A \ x).card) ≤
      8⁻¹ := by
  have hcard : (ppowers_in_set A).card ≤ N := by
    suffices hsubset : ppowers_in_set A ⊆ Finset.Icc 1 N by
      calc
        (ppowers_in_set A).card ≤ (Finset.Icc 1 N).card := Finset.card_le_card hsubset
        _ = N := by
          rw [Nat.card_Icc]
          omega
    intro x hx
    simpa [Finset.mem_Icc] using ppowers_in_set_le hA' x hx
  calc
    6 * (k : ℝ) * (N : ℝ)⁻¹ *
        (ppowers_in_set A).ssubsets.sum (fun x => ((N : ℝ)⁻¹) ^ (ppowers_in_set A \ x).card)
        ≤
      6 * (k : ℝ) * (N : ℝ)⁻¹ *
        (ppowers_in_set A).powerset.sum
          (fun x => ((N : ℝ)⁻¹) ^ (ppowers_in_set A \ x).card) := by
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · exact Finset.sum_le_sum_of_subset_of_nonneg
              (ssubsets_subset_powerset (s := ppowers_in_set A))
              (fun _ _ _ ↦ pow_nonneg (by positivity) _)
          · positivity
    _ = 6 * (k : ℝ) * (N : ℝ)⁻¹ * (1 + (N : ℝ)⁻¹) ^ (ppowers_in_set A).card := by
          rw [powerset_sum_pow' (s := ppowers_in_set A) (x := (N : ℝ)⁻¹), add_comm]
    _ ≤ 6 * (k : ℝ) * (N : ℝ)⁻¹ * 4 := by
          have hbase : (1 : ℝ) ≤ 1 + (N : ℝ)⁻¹ := by
            nlinarith [show 0 ≤ (N : ℝ)⁻¹ by positivity]
          have hfour : (1 + (N : ℝ)⁻¹) ^ N ≤ 4 := by
            simpa [add_comm] using (thing_le_four (N := N))
          refine mul_le_mul_of_nonneg_left ?_ ?_
          · exact (pow_le_pow_right₀ hbase hcard).trans hfour
          · positivity
    _ ≤ 8⁻¹ := by
          have hkN' : (k : ℝ) ≤ (N : ℝ) / 192 := by
            calc
              (k : ℝ) ≤ ((N / 192 : ℕ) : ℝ) := by exact_mod_cast hkN
              _ ≤ (N : ℝ) / 192 := Nat.cast_div_le
          have hN' : 0 < (N : ℝ) := by
            exact_mod_cast zero_lt_two.trans_le hN
          calc
            6 * (k : ℝ) * (N : ℝ)⁻¹ * 4
                ≤ 6 * ((N : ℝ) / 192) * (N : ℝ)⁻¹ * 4 := by
                  gcongr
            _ = 8⁻¹ := by
                field_simp [hN'.ne']
                norm_num

lemma count_multiples {m n : ℕ} (hm : 1 ≤ m) :
    ((Finset.Icc 1 n).filter fun k => m ∣ k).card = n / m := by
  have hcard : (Finset.Icc 1 (n / m)).card = n / m := by
    simp [Nat.card_Icc]
  rw [← hcard]
  refine (Finset.card_bij (fun i _ => i * m) ?_ ?_ ?_).symm
  · intro i hi
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ?_, dvd_mul_left _ _⟩
    constructor
    · exact one_le_mul (Finset.mem_Icc.1 hi).1 hm
    · exact (Nat.le_div_iff_mul_le (lt_of_lt_of_le Nat.zero_lt_one hm)).1
        (Finset.mem_Icc.1 hi).2
  · intro i _ j _ hij
    exact Nat.eq_of_mul_eq_mul_right (lt_of_lt_of_le Nat.zero_lt_one hm)
      (by simpa [Nat.mul_comm] using hij)
  · intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxIcc, hxdiv⟩
    rcases Finset.mem_Icc.mp hxIcc with ⟨hx1, hx2⟩
    rcases hxdiv with ⟨z, rfl⟩
    refine ⟨z, Finset.mem_Icc.2 ?_, by simp [Nat.mul_comm]⟩
    constructor
    · exact Nat.succ_le_of_lt <|
        Nat.pos_of_mul_pos_left (lt_of_lt_of_le Nat.zero_lt_one hx1)
    · exact (Nat.le_div_iff_mul_le (lt_of_lt_of_le Nat.zero_lt_one hm)).2
        (by simpa [Nat.mul_comm] using hx2)

lemma count_multiples' {m : ℕ} {n : ℝ} (hm : 1 ≤ m) (hn : 0 ≤ n) :
    ↑((Finset.Icc 1 ⌊n⌋₊).filter fun k => m ∣ k).card ≤ n / m := by
  rw [count_multiples hm]
  refine (Nat.cast_div_le).trans ?_
  exact div_le_div_of_nonneg_right (Nat.floor_le hn) (by positivity)

lemma count_real_multiples' {m : ℕ} {x y : ℝ} (hxy : x ≤ y) (hm : 1 ≤ m) :
    ↑((Finset.Icc ⌈x⌉ ⌊y⌋).filter fun k => (m : ℤ) ∣ k).card ≤ (y - x) / m + 1 := by
  let s : Finset ℤ := integer_range ((x + y) / (2 * (m : ℝ))) ((y - x) / (2 * (m : ℝ)))
  have hm0 : (0 : ℝ) < m := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hm
  have hm0' : (m : ℝ) ≠ 0 := ne_of_gt hm0
  have hsub :
      (Finset.Icc ⌈x⌉ ⌊y⌋).filter (fun k => (m : ℤ) ∣ k) ⊆
        s.image fun z : ℤ => (m : ℤ) * z := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkIcc, hkdiv⟩
    rcases Finset.mem_Icc.mp hkIcc with ⟨hkx, hky⟩
    rcases hkdiv with ⟨z, rfl⟩
    refine Finset.mem_image.mpr ⟨z, ?_, by simp⟩
    rw [mem_integer_range_iff, abs_le]
    have hx' : x ≤ (m : ℝ) * z := by
      have hx'' : x ≤ (((m : ℤ) * z : ℤ) : ℝ) := Int.ceil_le.mp hkx
      simpa using hx''
    have hy' : (m : ℝ) * z ≤ y := by
      have hy'' : ((((m : ℤ) * z : ℤ) : ℝ)) ≤ y := Int.le_floor.mp hky
      simpa using hy''
    constructor
    · field_simp [hm0']
      linarith
    · field_simp [hm0']
      linarith
  have hcard1 :
      ((Finset.Icc ⌈x⌉ ⌊y⌋).filter fun k => (m : ℤ) ∣ k).card ≤
        (s.image fun z : ℤ => (m : ℤ) * z).card :=
    Finset.card_le_card hsub
  have hcard2 : (s.image fun z : ℤ => (m : ℤ) * z).card ≤ s.card := Finset.card_image_le
  have hcard : ((Finset.Icc ⌈x⌉ ⌊y⌋).filter fun k => (m : ℤ) ∣ k).card ≤ s.card :=
    Nat.le_trans hcard1 hcard2
  calc
    ↑((Finset.Icc ⌈x⌉ ⌊y⌋).filter fun k => (m : ℤ) ∣ k).card ≤ ↑s.card := by
      exact_mod_cast hcard
    _ ≤ 2 * ((y - x) / (2 * (m : ℝ))) + 1 := by
      simpa [s] using
        (card_integer_range_le (x := (x + y) / (2 * (m : ℝ)))
          (y := (y - x) / (2 * (m : ℝ)))
          (by exact div_nonneg (sub_nonneg.mpr hxy) (by positivity)))
    _ = (y - x) / m + 1 := by ring_nf

lemma count_real_multiples {m : ℕ} {K : ℝ} {t : ℤ} (hK : 0 < K) (hm : 1 ≤ m) :
    ↑((integer_range t K).filter fun k => (m : ℤ) ∣ k).card ≤ (2 * K) / m + 1 := by
  simpa [integer_range, two_mul] using
    (count_real_multiples' (x := (t : ℝ) - K) (y := (t : ℝ) + K)
      (show (t : ℝ) - K ≤ (t : ℝ) + K by linarith) hm)

lemma candidate_count_one {N : ℕ} {K L T : ℝ} {k : ℕ} {A : Finset ℕ} {D : Finset ℕ}
    (_hN : 2 ≤ N) (_hA : 0 ∉ A) (hK : 1 ≤ K) (_hL : 0 < L) (hk : k ≠ 0)
    (_hKN : K ≤ ↑N)
    (_hq :
      ∀ q : ℕ, q ∈ ppowers_in_set A → ↑q ≤ L * K ^ 2 / (16 * ↑N ^ 2 * log ↑N ^ 2))
    (z : ∀ h ∈ minor_arc₂ A k K T,
      ∃ x ∈ I h K k, ↑((interval_rare_ppowers (I h K k) A L).lcm id) ∣ x)
    (hD : D ∈ (ppowers_in_set A).ssubsets) :
    (((minor_arc₂ A k K T).filter
        fun h => interval_rare_ppowers (I h K k) A L = D).card : ℝ) ≤
      (K + 1) * (((k : ℝ) * lcmA A + K) / lcmA D + 1) := by
  classical
  let R : ℝ := ((k : ℝ) * lcmA A + K) / 2
  let s : Finset ℤ := (integer_range 0 R).filter fun x => (lcmA D : ℤ) ∣ x
  let f : ℤ → Finset ℤ := fun x => (j A).filter fun h => x ∈ I h K k
  have hDsub : D ⊆ ppowers_in_set A := (Finset.mem_ssubsets.1 hD).1
  have hD0 : 0 ∉ D := by
    intro h0
    exact zero_not_mem_ppowers_in_set (A := A) (hDsub h0)
  have hlcmD : 1 ≤ lcmA D := Nat.one_le_iff_ne_zero.2 (lcm_ne_zero_of_zero_not_mem hD0)
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  have hsubset :
      (minor_arc₂ A k K T).filter (fun h => interval_rare_ppowers (I h K k) A L = D) ⊆
        s.biUnion f := by
    intro h hh
    rw [Finset.mem_filter] at hh
    rcases hh with ⟨hhminor, hrare⟩
    rcases z h hhminor with ⟨x, hxI, hxdiv⟩
    have hhj : h ∈ j A := by
      rw [minor_arc₂, Finset.mem_sdiff] at hhminor
      exact (Finset.mem_sdiff.mp hhminor.1).1
    have hxdiv' : (lcmA D : ℤ) ∣ x := by
      simpa [hrare] using hxdiv
    have hxI' : (|(h * k : ℝ) - x|) ≤ K / 2 := by
      exact (mem_I' (h := h) (K := K) (k := k) (z := x)).1 hxI
    have hhbound : |(h * k : ℝ)| ≤ (k : ℝ) * lcmA A / 2 := by
      calc
        |(h * k : ℝ)| = |(h : ℝ)| * (k : ℝ) := by
          rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ k by positivity)]
        _ ≤ ((lcmA A : ℝ) / 2) * (k : ℝ) := by
          gcongr
          exact bound_of_mem_j A h hhj
        _ = (k : ℝ) * lcmA A / 2 := by ring
    have hxbound : |(x : ℝ)| ≤ R := by
      dsimp [R]
      calc
        |(x : ℝ)| = |((x : ℝ) - h * k) + h * k| := by ring_nf
        _ ≤ |(x : ℝ) - h * k| + |(h * k : ℝ)| := abs_add_le _ _
        _ ≤ K / 2 + (k : ℝ) * lcmA A / 2 := by
          exact add_le_add (by simpa [abs_sub_comm] using hxI') hhbound
        _ = ((k : ℝ) * lcmA A + K) / 2 := by ring
    rw [Finset.mem_biUnion]
    refine ⟨x, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact
        ⟨(mem_integer_range_iff (x := 0) (y := R) (z := x)).2 (by simpa [R] using hxbound),
          hxdiv'⟩
    · rw [Finset.mem_filter]
      exact ⟨hhj, hxI⟩
  have hfiber :
      ∀ x ∈ s, (((f x).card : ℝ)) ≤ K + 1 := by
    intro x hx
    have hsubx : f x ⊆ integer_range ((x : ℝ) / k) (K / (2 * k)) := by
      intro h hh
      rw [Finset.mem_filter] at hh
      rw [mem_integer_range_iff]
      have hxI : |(h * k : ℝ) - x| ≤ K / 2 := by
        exact (mem_I' (h := h) (K := K) (k := k) (z := x)).1 hh.2
      have hdiv : K / (2 * (k : ℝ)) = (K / 2) / k := by
        field_simp [hk0]
      rw [hdiv]
      apply (le_div_iff₀ hkpos).2
      calc
        |(x : ℝ) / k - h| * (k : ℝ) = |(x : ℝ) / k - h| * |(k : ℝ)| := by
          rw [abs_of_pos hkpos]
        _ = |((x : ℝ) / k - h) * k| := by rw [← abs_mul]
        _ = |(x : ℝ) - h * k| := by
          congr 1
          field_simp [hk0]
        _ = |(h * k : ℝ) - x| := by rw [abs_sub_comm]
        _ ≤ K / 2 := hxI
    calc
      (((f x).card : ℝ)) ≤ ((integer_range ((x : ℝ) / k) (K / (2 * k))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubx
      _ ≤ 2 * (K / (2 * k)) + 1 := by
        apply card_integer_range_le
        positivity
      _ = K / k + 1 := by
        field_simp [hk0]
      _ ≤ K + 1 := by
        have hdivle : K / k ≤ K := by
          apply (div_le_iff₀ (show (0 : ℝ) < k by exact_mod_cast Nat.pos_of_ne_zero hk)).2
          have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
          nlinarith
        linarith
  have hs : ((s.card : ℝ)) ≤ ((k : ℝ) * lcmA A + K) / lcmA D + 1 := by
    simpa [s, R, two_mul] using
      (count_real_multiples (m := lcmA D) (K := R) (t := 0) hRpos hlcmD)
  calc
    ((((minor_arc₂ A k K T).filter
        fun h => interval_rare_ppowers (I h K k) A L = D).card : ℕ) : ℝ)
        ≤ ((s.biUnion f).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsubset
    _ ≤ ∑ x ∈ s, (((f x).card : ℝ)) := by
          exact_mod_cast (Finset.card_biUnion_le (s := s) (t := f))
    _ ≤ ∑ x ∈ s, (K + 1) := by
          refine Finset.sum_le_sum ?_
          intro x hx
          exact hfiber x hx
    _ = (s.card : ℝ) * (K + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((((k : ℝ) * lcmA A + K) / lcmA D + 1) : ℝ) * (K + 1) := by
          exact mul_le_mul_of_nonneg_right hs (by linarith)
    _ = (K + 1) * (((k : ℝ) * lcmA A + K) / lcmA D + 1) := by ring

lemma candidate_count {N : ℕ} {K L T : ℝ} {k : ℕ} {A : Finset ℕ} {D : Finset ℕ}
    (hN : 2 ≤ N) (hA : 0 ∉ A) (hK : 1 ≤ K) (hL : 0 < L) (hk : k ≠ 0) (hKN : K ≤ ↑N)
    (hA' : ∀ n ∈ A, n ≤ N)
    (hq :
      ∀ q : ℕ, q ∈ ppowers_in_set A → ↑q ≤ L * K ^ 2 / (16 * ↑N ^ 2 * log ↑N ^ 2))
    (z : ∀ h ∈ minor_arc₂ A k K T,
      ∃ x ∈ I h K k, ↑((interval_rare_ppowers (I h K k) A L).lcm id) ∣ x)
    (hD : D ∈ (ppowers_in_set A).ssubsets) :
    (((minor_arc₂ A k K T).filter
        fun h => interval_rare_ppowers (I h K k) A L = D).card : ℝ) ≤
      6 * (k : ℝ) * (N : ℝ) ^ (((ppowers_in_set A \ D).card) + 1 : ℝ) := by
  refine (candidate_count_one hN hA hK hL hk hKN hq z hD).trans ?_
  rw [Finset.mem_ssubsets] at hD
  have hD0 : 0 ∉ D := by
    intro h0
    exact zero_not_mem_ppowers_in_set (A := A) (hD.1 h0)
  have hlcmDpos_nat : 0 < lcmA D := Nat.pos_iff_ne_zero.2 (lcm_ne_zero_of_zero_not_mem hD0)
  have h₁ :
      (lcmA A : ℝ) ≤ (N : ℝ) ^ (ppowers_in_set A \ D).card * lcmA D := by
    have hprod :
        Finset.prod (ppowers_in_set A \ D) (fun q => q) ≤ N ^ (ppowers_in_set A \ D).card := by
      simpa using
        (Finset.prod_le_pow_card (s := ppowers_in_set A \ D) (f := fun q => q) (n := N)
          (fun q hq => (ppowers_in_set_le hA' q (Finset.mem_sdiff.mp hq).1).2))
    have hdiv :
        lcmA A ∣ Finset.prod (ppowers_in_set A \ D) (fun q => q) * lcmA D := by
      rw [← lcm_Q hA]
      refine Finset.lcm_dvd_iff.2 ?_
      intro q hq
      by_cases hqD : q ∈ D
      · exact dvd_mul_of_dvd_right (Finset.dvd_lcm hqD) _
      · exact dvd_mul_of_dvd_left (dvd_prod_of_mem id (Finset.mem_sdiff.mpr ⟨hq, hqD⟩)) _
    have hnat :
        lcmA A ≤ Finset.prod (ppowers_in_set A \ D) (fun q => q) * lcmA D := by
      refine Nat.le_of_dvd ?_ hdiv
      refine Nat.mul_pos (Finset.prod_pos ?_) hlcmDpos_nat
      intro q hq
      exact (ppowers_in_set_le hA' q (Finset.mem_sdiff.mp hq).1).1
    exact_mod_cast hnat.trans (Nat.mul_le_mul_right _ hprod)
  have h₂ : K + 1 ≤ 2 * N := by
    linarith
  have h₃ : (1 : ℝ) ≤ lcmA D := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (lcm_ne_zero_of_zero_not_mem hD0)
  have h₄ : (1 : ℝ) ≤ k := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
  have hdiff_nonempty : (ppowers_in_set A \ D).Nonempty := by
    refine Finset.sdiff_nonempty.2 ?_
    intro hsub
    exact hD.2 hsub
  have h₅ : (N : ℝ) ≤ (N : ℝ) ^ (ppowers_in_set A \ D).card := by
    have hN1 : (1 : ℝ) ≤ N := by
      exact_mod_cast (show 1 ≤ N by omega)
    have hcard1 : 1 ≤ (ppowers_in_set A \ D).card := by
      exact Nat.succ_le_iff.mpr (Finset.card_pos.mpr hdiff_nonempty)
    simpa [pow_one] using (pow_le_pow_right₀ hN1 hcard1)
  have hlcmDpos : 0 < (lcmA D : ℝ) := by
    exact_mod_cast hlcmDpos_nat
  have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
  have hpow_nonneg : 0 ≤ (N : ℝ) ^ (ppowers_in_set A \ D).card := by positivity
  have hterm_nonneg : 0 ≤ (N : ℝ) ^ (ppowers_in_set A \ D).card * lcmA D := by positivity
  have hmul₁ :
      (k : ℝ) * lcmA A ≤ (k : ℝ) * ((N : ℝ) ^ (ppowers_in_set A \ D).card * lcmA D) := by
    exact mul_le_mul_of_nonneg_left h₁ hk_nonneg
  have hmul₂ : K ≤ (k : ℝ) * ((N : ℝ) ^ (ppowers_in_set A \ D).card * lcmA D) := by
    refine (hKN.trans h₅).trans ?_
    refine (le_mul_of_one_le_right hpow_nonneg h₃).trans ?_
    exact le_mul_of_one_le_left hterm_nonneg h₄
  have hdivbound :
      (((k : ℝ) * lcmA A + K) / lcmA D) ≤
        2 * ((k : ℝ) * (N : ℝ) ^ (ppowers_in_set A \ D).card) := by
    apply (_root_.div_le_iff₀ hlcmDpos).2
    have hsum :
        (k : ℝ) * lcmA A + K ≤
          2 * ((k : ℝ) * ((N : ℝ) ^ (ppowers_in_set A \ D).card * lcmA D)) := by
      linarith
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsum
  have hmain :
      (K + 1) * (((k : ℝ) * lcmA A + K) / lcmA D + 1) ≤
        4 * (k : ℝ) * (N : ℝ) ^ (((ppowers_in_set A \ D).card) + 1 : ℝ) + 2 * N := by
    have hinner :
        (((k : ℝ) * lcmA A + K) / lcmA D + 1) ≤
          2 * ((k : ℝ) * (N : ℝ) ^ (ppowers_in_set A \ D).card) + 1 := by
      linarith
    calc
      (K + 1) * (((k : ℝ) * lcmA A + K) / lcmA D + 1)
          ≤ (2 * N) * (2 * ((k : ℝ) * (N : ℝ) ^ (ppowers_in_set A \ D).card) + 1) := by
            refine mul_le_mul h₂ hinner ?_ ?_
            · positivity
            · linarith
      _ = 4 * (k : ℝ) * ((N : ℝ) ^ (ppowers_in_set A \ D).card * N) + 2 * N := by
            ring
      _ = 4 * (k : ℝ) * (N : ℝ) ^ (((ppowers_in_set A \ D).card) + 1 : ℝ) + 2 * N := by
            congr 2
            rw [← Nat.cast_add_one, Real.rpow_natCast, pow_succ]
  refine hmain.trans ?_
  have hNle :
      (N : ℝ) ≤ (k : ℝ) * (N : ℝ) ^ (((ppowers_in_set A \ D).card) + 1 : ℝ) := by
    have hN1 : (1 : ℝ) ≤ (k : ℝ) * (N : ℝ) ^ (ppowers_in_set A \ D).card := by
      refine one_le_mul_of_one_le_of_one_le h₄ ?_
      exact (show (1 : ℝ) ≤ N by exact_mod_cast (show 1 ≤ N by omega)).trans h₅
    have hNnonneg : 0 ≤ (N : ℝ) := by positivity
    rw [← Nat.cast_add_one, Real.rpow_natCast, pow_succ, ← mul_assoc]
    simpa [mul_assoc, mul_left_comm, mul_comm] using (le_mul_of_one_le_right hNnonneg hN1)
  linarith

lemma minor2_bound :
    ∀ᶠ N : ℕ in Filter.atTop,
      ∀ {K L T : ℝ} {k : ℕ} {A : Finset ℕ},
      0 ∉ A → 1 ≤ K → 0 < L → k ≠ 0 → k ≤ N / 192 → K ≤ N →
        (∀ n ∈ A, n ≤ N) →
      (∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ L * K ^ 2 / (16 * N ^ 2 * (log N) ^ 2)) →
      (∀ (t : ℝ) (I : Finset ℤ), I = Finset.Icc ⌈t - K / 2⌉ ⌊t + K / 2⌋ →
        T ≤ (A.filter fun n => ∀ x ∈ I, ¬ ((n : ℤ) ∣ x)).card ∨
          ∃ x ∈ I, ∀ q ∈ interval_rare_ppowers I A L, (q : ℤ) ∣ x) →
      (minor_arc₂ A k K T).sum (fun h => cos_prod A (h * k)) ≤ 8⁻¹ := by
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with
    N hN K L T k A hA hK hL hk hkN hKN hA' hq hI
  have hgood :
      ∀ h ∈ minor_arc₂ A k K T,
        ∃ x ∈ I h K k, ∀ q ∈ interval_rare_ppowers (I h K k) A L, (q : ℤ) ∣ x := by
    intro h hh
    refine (hI (t := (h * k : ℝ)) (I := I h K k) (by simp [I, integer_range])).resolve_left ?_
    rw [minor_arc₂_eq, Finset.mem_filter] at hh
    letI : DecidableEq ℤ := Classical.decEq ℤ
    let sZ : Finset ℤ := A.image (fun n : ℕ => (n : ℤ))
    have hcardeq :
        (((sZ.filter fun n : ℤ => ∀ z ∈ I h K k, ¬ n ∣ z).card : ℝ)) =
          (((A.filter fun n : ℕ => ∀ z ∈ I h K k, ¬ ((n : ℤ) ∣ z)).card : ℝ)) := by
      dsimp [sZ]
      rw [Finset.filter_image, Finset.card_image_of_injective _ Nat.cast_injective]
    have hh' : (((sZ.filter fun n : ℤ => ∀ z ∈ I h K k, ¬ n ∣ z).card : ℝ)) < T := by
      rw [hcardeq]
      exact hh.2
    simpa [sZ] using (not_le.mpr hh')
  have hz :
      ∀ h ∈ minor_arc₂ A k K T,
        ∃ x ∈ I h K k, ↑((interval_rare_ppowers (I h K k) A L).lcm id) ∣ x := by
    intro h hh
    rcases hgood h hh with ⟨x, hx, hx'⟩
    exact ⟨x, hx, cast_lcm_dvd hx'⟩
  have hcard :
      ∀ D ∈ (ppowers_in_set A).ssubsets,
        (((minor_arc₂ A k K T).filter
            fun h => interval_rare_ppowers (I h K k) A L = D).card : ℝ) ≤
          6 * (k : ℝ) * (N : ℝ) ^ (((ppowers_in_set A \ D).card) + 1 : ℝ) := by
    intro D hD
    exact candidate_count hN hA hK hL hk hKN hA' hq hz hD
  have hsumD :
      ∀ D,
        D ∈ (ppowers_in_set A).ssubsets →
          Finset.sum
              ((minor_arc₂ A k K T).filter (fun h => interval_rare_ppowers (I h K k) A L = D))
              (fun h => cos_prod A (h * k)) ≤
            6 * (k : ℝ) * (N : ℝ)⁻¹ * ((N : ℝ)⁻¹) ^ (ppowers_in_set A \ D).card := by
    intro D hD
    refine
      (Finset.sum_le_card_nsmul
        _ _ ((N : ℝ) ^ (-4 * (ppowers_in_set A \ D).card : ℝ)) ?_).trans ?_
    · intro h hh
      rw [Finset.mem_filter] at hh
      rw [← hh.2]
      refine minor2_ind_bound (I h K k) hA (by linarith) hA' hN ?_ hq
      simp [I, integer_range]
    · rw [nsmul_eq_mul]
      refine (mul_le_mul_of_nonneg_right (hcard D hD)
        (Real.rpow_nonneg (show 0 ≤ (N : ℝ) by positivity) _)).trans ?_
      have hNpos : 0 < (N : ℝ) := by
        exact_mod_cast zero_lt_two.trans_le hN
      rw [mul_assoc, ← Real.rpow_add hNpos, mul_assoc (6 * (k : ℝ)), ← Real.rpow_neg_one,
        ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by positivity) (by positivity))
      refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
      · exact_mod_cast one_le_two.trans hN
      · have hcard1 : (1 : ℝ) ≤ (ppowers_in_set A \ D).card := by
          rw [Nat.one_le_cast, Nat.succ_le_iff, Finset.card_pos, Finset.sdiff_nonempty]
          rw [Finset.mem_ssubsets] at hD
          exact hD.2
        linarith
  have hsum :
      Finset.sum (ppowers_in_set A).ssubsets
          (fun D =>
          Finset.sum
              ((minor_arc₂ A k K T).filter (fun h => interval_rare_ppowers (I h K k) A L = D))
              (fun h => cos_prod A (h * k)))
        ≤
          Finset.sum (ppowers_in_set A).ssubsets
            (fun D =>
              6 * (k : ℝ) * (N : ℝ)⁻¹ * ((N : ℝ)⁻¹) ^ (ppowers_in_set A \ D).card) := by
    refine Finset.sum_le_sum ?_
    intro D hD
    exact hsumD D hD
  simp only [Finset.sum_filter] at hsum
  rw [Finset.sum_comm] at hsum
  simp only [Finset.sum_ite_eq, Finset.mem_ssubsets] at hsum
  rw [← Finset.sum_filter, d_strict_subset hA hk hz, ← Finset.mul_sum] at hsum
  exact hsum.trans (minor2_bound_end N hN hkN hA')

theorem circle_method_prop2 :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        ∀ {K L M T : ℝ} {k : ℕ} {A : Finset ℕ},
        0 < T → 0 < L → 8 ≤ K → K < M → M ≤ N → k ≠ 0 → (k : ℝ) ≤ M / 192 →
        (∀ n ∈ A, M ≤ ↑n) → (∀ n ∈ A, n ≤ N) → rec_sum A < 2 / k →
        (2 : ℝ) / k - 1 / M ≤ rec_sum A → k ∣ (A.lcm id : ℕ) →
        (∀ q ∈ ppowers_in_set A,
          ↑q ≤
            min (L * K ^ 2 / (16 * N ^ 2 * (log N) ^ 2))
              (min (c * M / k) (T * K ^ 2 / (N ^ 2 * log N)))) →
        good_condition A K T L → ∃ S ⊆ A, rec_sum S = 1 / k := by
  obtain ⟨C, hC₀, hClcm⟩ := smooth_lcm
  let C' : ℝ := max C 1
  let c : ℝ := log 2 / C'
  have hC'ge : C ≤ C' := by
    dsimp [C']
    exact le_max_left _ _
  have hC'one : (1 : ℝ) ≤ C' := by
    dsimp [C']
    exact le_max_right _ _
  have hC'pos : 0 < C' := lt_of_lt_of_le zero_lt_one hC'one
  have hc₀ : 0 < c := by
    dsimp [c]
    exact div_pos (Real.log_pos one_lt_two) hC'pos
  refine ⟨c, hc₀, ?_⟩
  filter_upwards [minor1_bound, minor2_bound] with
    N hm1 hm2 K L M T k A hT hL hK hKM hMN hk hkM hA₁ hA₂ hA₃ hA₄ hkA hq hI
  have hM₀ : 0 < M := by
    linarith
  have hk₀ : 0 < (k : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hk
  have hk₀ne : (k : ℝ) ≠ 0 := hk₀.ne'
  have hcCkM : C * (c * M / k) / log 2 / M + 1 / M + 1 / M ≤ 2 / k := by
    have hterm1 : C * (c * M / k) / log 2 / M ≤ (1 : ℝ) / k := by
      have hEq : C * (c * M / k) / log 2 / M = (C / C') / k := by
        dsimp [c]
        field_simp [hk₀ne, hM₀.ne', hC'pos.ne', (Real.log_pos one_lt_two).ne']
      calc
        C * (c * M / k) / log 2 / M = (C / C') / k := hEq
        _ ≤ 1 / k := by
          have hdiv : C / C' ≤ 1 := by
            rw [div_le_iff₀ hC'pos]
            simpa using hC'ge
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hdiv (inv_nonneg.2 hk₀.le)
    have hterm2 : 1 / M + 1 / M ≤ (1 : ℝ) / k := by
      have hkM2 : (2 : ℝ) * k ≤ M := by
        nlinarith
      have hdiv : (2 : ℝ) / M ≤ (1 : ℝ) / k := by
        exact (div_le_div_iff₀ hM₀ hk₀).2 (by simpa [mul_comm] using hkM2)
      simpa [two_mul, div_eq_mul_inv] using hdiv
    have hsum : C * (c * M / k) / log 2 / M + (1 / M + 1 / M) ≤ 1 / k + 1 / k := by
      exact add_le_add hterm1 hterm2
    calc
      C * (c * M / k) / log 2 / M + 1 / M + 1 / M
          = C * (c * M / k) / log 2 / M + (1 / M + 1 / M) := by ring
      _ ≤ 1 / k + 1 / k := hsum
      _ = 2 / k := by ring
  have hA₅ : A.Nonempty := by
    by_contra hA₅
    rw [Finset.not_nonempty_iff_eq_empty] at hA₅
    subst hA₅
    have hA₄' : (2 : ℝ) / k - 1 / M ≤ 0 := by
      simpa using hA₄
    have hbad'' : (2 : ℝ) / k ≤ 1 / M := by
      linarith
    have hbad' : (2 : ℝ) * M ≤ k := by
      simpa using (div_le_div_iff₀ hk₀ hM₀).mp hbad''
    nlinarith
  have hq' :
      ∀ q ∈ ppowers_in_set A,
        (q : ℝ) ≤ L * K ^ 2 / (16 * N ^ 2 * (log N) ^ 2) ∧
          (q : ℝ) ≤ c * M / k ∧ (q : ℝ) ≤ T * K ^ 2 / (N ^ 2 * log N) := by
    simpa [le_min_iff, and_assoc] using hq
  have hq₁ :
      ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ L * K ^ 2 / (16 * N ^ 2 * (log N) ^ 2) := by
    intro q hqpp
    exact (hq' q hqpp).1
  have hq₂ : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ c * M / k := by
    intro q hqpp
    exact (hq' q hqpp).2.1
  have hq₃ : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ T * K ^ 2 / (N ^ 2 * log N) := by
    intro q hqpp
    exact (hq' q hqpp).2.2
  have hm1' :
      (minor_arc₁ A k K T).sum (fun h => cos_prod A (h * k)) ≤ 8⁻¹ := by
    exact hm1 (K := K) (M := M) (T := T) (k := k) (A := A) (hK.trans hKM.le) hA₅ hA₁
      (by linarith) hT hA₂ hq₃
  have hA₆ : 0 ∉ A := by
    intro ht
    have : M ≤ 0 := by simpa using hA₁ 0 ht
    linarith
  have hkN : k ≤ N / 192 := by
    have hkN' : 192 * k ≤ N := by
      exact_mod_cast (show (192 : ℝ) * k ≤ N by nlinarith)
    omega
  have h0K : 0 < K := by
    linarith
  have hA₄' : (2 : ℝ) - k / M ≤ k * rec_sum A := by
    have hmul := mul_le_mul_of_nonneg_left hA₄ hk₀.le
    simpa [div_eq_mul_inv, mul_sub, hk₀ne, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hA₃' : (k : ℝ) * rec_sum A < 2 := by
    have hkQ : (0 : ℚ) < k := by
      exact_mod_cast Nat.pos_of_ne_zero hk
    have hA₃Q : (k : ℚ) * rec_sum A < 2 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using (_root_.lt_div_iff₀ hkQ).1 hA₃
    exact_mod_cast hA₃Q
  have hAlcm : (lcmA A : ℝ) ≤ 2 ^ (A.card - 1 : ℤ) := by
    have hClcm_nonneg : 0 ≤ c * M / k := by
      refine div_nonneg ?_ (Nat.cast_nonneg k)
      exact mul_nonneg hc₀.le hM₀.le
    have hClcm_bound : ∀ q ∈ ppowers_in_set A, (q : ℝ) ≤ c * M / k := by
      intro q hqpp
      exact hq₂ q hqpp
    have hClcmA := hClcm (c * M / k) hClcm_nonneg A hA₆ hClcm_bound
    refine hClcmA.trans ?_
    have hpowpos : 0 < (2 : ℝ) ^ (A.card - 1 : ℤ) := by
      rw [← Real.rpow_intCast]
      exact Real.rpow_pos_of_pos zero_lt_two _
    have hcard1 : 1 ≤ A.card := Finset.one_le_card.mpr hA₅
    rw [← Real.log_le_log_iff (Real.exp_pos _) hpowpos, Real.log_exp]
    rw [show (2 : ℝ) ^ (A.card - 1 : ℤ) = (2 : ℝ) ^ (((A.card - 1 : ℤ) : ℝ)) by
      rw [← Real.rpow_intCast]]
    rw [Real.log_rpow zero_lt_two]
    rw [← div_le_iff₀ (Real.log_pos one_lt_two)]
    push_cast
    have hscaled : C * (c * M / k) / log 2 / M + 1 / M ≤ A.card / M := by
      refine le_trans ?_ (rec_sum_le_card_div hM₀ hA₁)
      refine le_trans ?_ hA₄
      linarith
    have hscaled' : C * (c * M / k) / log 2 + 1 ≤ A.card := by
      have hscaled2 : (C * (c * M / k) / log 2 + 1) / M ≤ A.card / M := by
        simpa [add_div] using hscaled
      have hmul := mul_le_mul_of_nonneg_right hscaled2 hM₀.le
      simpa [div_eq_mul_inv, hM₀.ne', mul_assoc, mul_left_comm, mul_comm] using hmul
    linarith
  have hm2' :
      (minor_arc₂ A k K T).sum (fun h => cos_prod A (h * k)) ≤ 8⁻¹ := by
    exact hm2 (K := K) (L := L) (T := T) (k := k) (A := A) hA₆
      ((by norm_num : (1 : ℝ) ≤ 8).trans hK) hL hk hkN (hKM.le.trans hMN) hA₂ hq₁ hI
  by_contra hS
  have hS' : ∀ S ⊆ A, rec_sum S ≠ 1 / k := by
    intro S hSA hrec
    exact hS ⟨S, hSA, hrec⟩
  have hminorl := minor_lbound hA₁ h0K hKM hkA hk hA₄' hA₃' hA₅ hS' hAlcm
  have hminors : minor_arc₂ A k K T ∪ minor_arc₁ A k K T = j A \ major_arc A k K := by
    rw [minor_arc₂]
    exact Finset.sdiff_union_of_subset (Finset.filter_subset _ _)
  have hminorl' :
      1 / 2 ≤
        (minor_arc₂ A k K T).sum (fun h => cos_prod A (h * k)) +
          (minor_arc₁ A k K T).sum (fun h => cos_prod A (h * k)) := by
    have htmp := hminorl
    rw [← hminors] at htmp
    rw [minor_arc₂] at htmp
    have hdisj : Disjoint ((j A \ major_arc A k K) \ minor_arc₁ A k K T) (minor_arc₁ A k K T) :=
      (Finset.disjoint_sdiff : Disjoint (minor_arc₁ A k K T)
        ((j A \ major_arc A k K) \ minor_arc₁ A k K T)).symm
    rw [Finset.sum_union hdisj] at htmp
    simpa [add_comm, add_left_comm, add_assoc] using htmp
  have hupper :
      (minor_arc₂ A k K T).sum (fun h => cos_prod A (h * k)) +
          (minor_arc₁ A k K T).sum (fun h => cos_prod A (h * k)) < 1 / 2 := by
    calc
      (minor_arc₂ A k K T).sum (fun h => cos_prod A (h * k)) +
          (minor_arc₁ A k K T).sum (fun h => cos_prod A (h * k))
          ≤ 8⁻¹ + 8⁻¹ := add_le_add hm2' hm1'
      _ < 1 / 2 := by norm_num
  exact (not_lt_of_ge hminorl') hupper

end

end UnitFractions
