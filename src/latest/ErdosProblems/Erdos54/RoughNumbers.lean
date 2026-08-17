import Mathlib
import ErdosProblems.Erdos54.MertensLower

/-!
# Rough integers for the Conlon--Fox--Pham construction

This file contains the elementary sieve and cyclic-group facts used in the
probabilistic block lemma.  The parameter `w` is kept separate from the scale
`x` in the core lemmas; `roughCutoff x = floor (log x / 2)` is substituted only
at the end.  This makes all rounding issues explicit.
-/

open scoped BigOperators Pointwise

namespace Erdos54

/-- The primes at most `w`. -/
def smallPrimes (w : ℕ) : Finset ℕ :=
  (Finset.range (w + 1)).filter Nat.Prime

/-- The squarefree product of the primes at most `w`. -/
def roughModulus (w : ℕ) : ℕ :=
  ∏ p ∈ smallPrimes w, p

/-- The cutoff used in the CFP rough set. -/
noncomputable def roughCutoff (x : ℕ) : ℕ :=
  Nat.floor (Real.log (x : ℝ) / 2)

/-- Integers in `[x,2x)` with no prime divisor at most `w`. -/
def roughNumbersAt (x w : ℕ) : Finset ℕ :=
  (Finset.Ico x (2 * x)).filter fun n ↦
    ∀ p ∈ smallPrimes w, ¬p ∣ n

/-- The rough set at scale `x` used by CFP. -/
noncomputable def roughNumbers (x : ℕ) : Finset ℕ :=
  roughNumbersAt x (roughCutoff x)

@[simp] theorem mem_smallPrimes {p w : ℕ} :
    p ∈ smallPrimes w ↔ p ≤ w ∧ p.Prime := by
  simp [smallPrimes]

theorem smallPrimes_prime {p w : ℕ} (hp : p ∈ smallPrimes w) : p.Prime :=
  (mem_smallPrimes.mp hp).2

theorem roughModulus_pos (w : ℕ) : 0 < roughModulus w := by
  exact Finset.prod_pos fun p hp ↦ (smallPrimes_prime hp).pos

theorem roughModulus_ne_zero (w : ℕ) : roughModulus w ≠ 0 :=
  (roughModulus_pos w).ne'

@[simp] theorem roughModulus_primeFactors (w : ℕ) :
    (roughModulus w).primeFactors = smallPrimes w := by
  exact Nat.primeFactors_prod fun p hp ↦ smallPrimes_prime hp

/-- The rough modulus is Mathlib's primorial. -/
theorem roughModulus_eq_primorial (w : ℕ) :
    roughModulus w = primorial w := by
  rfl

/-- A convenient explicit upper bound for the small-prime product. -/
theorem roughModulus_le_four_pow (w : ℕ) : roughModulus w ≤ 4 ^ w := by
  rw [roughModulus_eq_primorial]
  exact primorial_le_four_pow w

/-- Euler's product formula, specialized to the squarefree rough modulus. -/
theorem roughModulus_totient_ratio (w : ℕ) :
    ((roughModulus w).totient : ℝ) / roughModulus w =
      ∏ p ∈ smallPrimes w, (1 - 1 / (p : ℝ)) := by
  rw [div_eq_iff (by exact_mod_cast roughModulus_ne_zero w)]
  have hQ := Nat.totient_eq_mul_prod_factors (roughModulus w)
  rw [roughModulus_primeFactors] at hQ
  have hR := congrArg (algebraMap ℚ ℝ) hQ
  norm_num [div_eq_mul_inv] at hR ⊢
  simpa [mul_comm] using hR

/-- Mertens' product lower bound in totient form. -/
theorem roughModulus_totient_ratio_lower {w : ℕ} (hw : 3 ≤ w) :
    1 / ((roughMertensConstant : ℝ) * Real.log w) ≤
      ((roughModulus w).totient : ℝ) / roughModulus w := by
  rw [roughModulus_totient_ratio]
  simpa [smallPrimes] using roughEulerProduct_lower (show 2 ≤ w by omega)

@[simp] theorem mem_roughNumbersAt {x w n : ℕ} :
    n ∈ roughNumbersAt x w ↔
      x ≤ n ∧ n < 2 * x ∧ ∀ p, p ≤ w → p.Prime → ¬p ∣ n := by
  simp only [roughNumbersAt, Finset.mem_filter, Finset.mem_Ico, mem_smallPrimes]
  aesop

@[simp] theorem mem_roughNumbers {x n : ℕ} :
    n ∈ roughNumbers x ↔
      x ≤ n ∧ n < 2 * x ∧
        ∀ p, p ≤ roughCutoff x → p.Prime → ¬p ∣ n := by
  simp [roughNumbers]

theorem roughModulus_coprime_iff {w n : ℕ} :
    (roughModulus w).Coprime n ↔ ∀ p ∈ smallPrimes w, ¬p ∣ n := by
  rw [roughModulus, Nat.coprime_prod_left_iff]
  refine forall_congr' fun p ↦ forall_congr' fun hp ↦ ?_
  exact (smallPrimes_prime hp).coprime_iff_not_dvd

theorem mem_roughNumbersAt_iff_coprime {x w n : ℕ} :
    n ∈ roughNumbersAt x w ↔
      n ∈ Finset.Ico x (2 * x) ∧ (roughModulus w).Coprime n := by
  simp only [roughNumbersAt, Finset.mem_filter, roughModulus_coprime_iff]

/-- A member of the rough set has least prime divisor beyond the cutoff. -/
theorem cutoff_lt_minFac_of_mem_roughNumbersAt {x w n : ℕ}
    (hn : n ∈ roughNumbersAt x w) (hn1 : 1 < n) : w < n.minFac := by
  by_contra h
  exact (mem_roughNumbersAt.mp hn).2.2 n.minFac (Nat.le_of_not_gt h)
    (Nat.minFac_prime hn1.ne') (Nat.minFac_dvd n)

/-- An integral number of consecutive periods contains exactly that many
copies of a reduced residue system. -/
theorem card_coprime_periods (M a t : ℕ) :
    ((Finset.Ico a (a + M * t)).filter (M.Coprime ·)).card =
      t * M.totient := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hsplit :
          Finset.Ico a (a + M * t.succ) =
            Finset.Ico a (a + M * t) ∪
              Finset.Ico (a + M * t) (a + M * t + M) := by
        rw [Nat.mul_succ]
        ext n
        simp only [Finset.mem_Ico, Finset.mem_union]
        omega
      rw [hsplit, Finset.filter_union]
      rw [Finset.card_union_of_disjoint]
      · rw [ih, Nat.filter_coprime_Ico_eq_totient]
        exact (Nat.succ_mul t M.totient).symm
      · exact Finset.disjoint_filter_filter <| by
          simp only [Finset.disjoint_left, Finset.mem_Ico]
          omega

/-- Exact lower sieve: retain the largest whole number of periods of the
rough modulus inside the interval of length `x`. -/
theorem roughNumbersAt_card_lower (x w : ℕ) :
    (x / roughModulus w) * (roughModulus w).totient ≤
      (roughNumbersAt x w).card := by
  let M := roughModulus w
  let B := (Finset.Ico x (x + M * (x / M))).filter (M.Coprime ·)
  have hBcard : B.card = (x / M) * M.totient := by
    simpa [B] using card_coprime_periods M x (x / M)
  have hBsub : B ⊆ roughNumbersAt x w := by
    intro n hn
    have hn' :
        n ∈ Finset.Ico x (x + M * (x / M)) ∧ M.Coprime n := by
      simpa [B] using hn
    apply (mem_roughNumbersAt_iff_coprime).2
    refine ⟨?_, hn'.2⟩
    have hlength : M * (x / M) ≤ x := Nat.mul_div_le x M
    have hnIco := Finset.mem_Ico.mp hn'.1
    exact Finset.mem_Ico.mpr ⟨hnIco.1, by omega⟩
  simpa [M, ← hBcard] using Finset.card_le_card hBsub

/-- Real-valued lower bound after the primorial error has become at most half
the interval length.  This is the exact quantitative input used by the random
sampling argument. -/
theorem roughNumbersAt_card_lower_real {x w : ℕ} (hw : 3 ≤ w)
    (hmod : 2 * roughModulus w ≤ x) :
    (x : ℝ) / (2 * roughMertensConstant * Real.log w) ≤
      (roughNumbersAt x w).card := by
  let M := roughModulus w
  let k := x / M
  let ph := M.totient
  have hMpos : 0 < M := roughModulus_pos w
  have hlogpos : 0 < Real.log (w : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < w by omega))
  have hmodM : 2 * M ≤ x := by simpa [M] using hmod
  have hk2 : 2 ≤ k := by
    apply (Nat.le_div_iff_mul_le hMpos).2
    simpa [k, Nat.mul_comm] using hmodM
  have hxkm : x ≤ 2 * M * k := by
    have hdecomp := Nat.mod_add_div x M
    change x % M + M * k = x at hdecomp
    have hrem := Nat.mod_lt x hMpos
    have hxle : x ≤ M * k + M := by omega
    have hMle : M ≤ M * k := by
      simpa using Nat.mul_le_mul_left M (show 1 ≤ k by omega)
    calc
      x ≤ M * k + M := hxle
      _ ≤ M * k + M * k := Nat.add_le_add_left hMle _
      _ = 2 * M * k := by ring
  have hratio : 1 / ((roughMertensConstant : ℝ) * Real.log w) ≤
      (ph : ℝ) / M := by
    simpa [M, ph] using roughModulus_totient_ratio_lower hw
  have hph : (M : ℝ) /
      ((roughMertensConstant : ℝ) * Real.log w) ≤ ph := by
    calc
      (M : ℝ) / ((roughMertensConstant : ℝ) * Real.log w) =
          (M : ℝ) *
            (1 / ((roughMertensConstant : ℝ) * Real.log w)) := by ring
      _ ≤ (M : ℝ) * ((ph : ℝ) / M) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = ph := by
        field_simp
  have hkph : (x : ℝ) /
      (2 * roughMertensConstant * Real.log w) ≤ (k : ℝ) * ph := by
    calc
      (x : ℝ) / (2 * roughMertensConstant * Real.log w) ≤
          ((2 * M * k : ℕ) : ℝ) /
            (2 * roughMertensConstant * Real.log w) := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hxkm) (by positivity)
      _ = (k : ℝ) * ((M : ℝ) /
          ((roughMertensConstant : ℝ) * Real.log w)) := by
        push_cast
        ring
      _ ≤ (k : ℝ) * ph :=
        mul_le_mul_of_nonneg_left hph (by positivity)
  exact hkph.trans (by
    exact_mod_cast (roughNumbersAt_card_lower x w))

/-- The chosen logarithmic cutoff makes the primorial a fixed power smaller
than the ambient scale. -/
theorem four_pow_roughCutoff_le_rpow {x : ℕ} (hx : 1 ≤ x) :
    ((4 ^ roughCutoff x : ℕ) : ℝ) ≤ (x : ℝ) ^ (7 / 10 : ℝ) := by
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hlog0 : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg hxR
  have hfloor : (roughCutoff x : ℝ) ≤ Real.log (x : ℝ) / 2 := by
    exact Nat.floor_le (by positivity)
  have hlog4 : Real.log (4 : ℝ) < 7 / 5 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    nlinarith [Real.log_two_lt_d9]
  have hexp : Real.log (4 : ℝ) * (roughCutoff x : ℝ) ≤
      Real.log (x : ℝ) * (7 / 10 : ℝ) := by
    have hcut0 : (0 : ℝ) ≤ roughCutoff x := by positivity
    nlinarith
  push_cast
  rw [← Real.rpow_natCast]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4),
    Real.rpow_def_of_pos (by positivity : (0 : ℝ) < x)]
  exact Real.exp_le_exp.mpr hexp

/-- Eventually the primorial error is at most half of the interval length. -/
theorem eventually_two_mul_roughModulus_le :
    ∀ᶠ x : ℕ in Filter.atTop,
      2 * roughModulus (roughCutoff x) ≤ x := by
  have hpowTop : Filter.Tendsto (fun x : ℕ ↦ (x : ℝ) ^ (3 / 10 : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 10)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop 1, hpowTop.eventually_ge_atTop 2]
      with x hx hpow
  have hreal : ((2 * roughModulus (roughCutoff x) : ℕ) : ℝ) ≤ x := by
    push_cast
    calc
      2 * (roughModulus (roughCutoff x) : ℝ) ≤
          2 * ((4 ^ roughCutoff x : ℕ) : ℝ) := by
        gcongr
        exact_mod_cast roughModulus_le_four_pow (roughCutoff x)
      _ ≤ 2 * (x : ℝ) ^ (7 / 10 : ℝ) := by
        gcongr
        exact four_pow_roughCutoff_le_rpow hx
      _ ≤ (x : ℝ) ^ (3 / 10 : ℝ) * (x : ℝ) ^ (7 / 10 : ℝ) := by
        gcongr
      _ = x := by
        rw [mul_comm, ← Real.rpow_add (by positivity)]
        norm_num
  exact_mod_cast hreal

/-- A concrete threshold after which the Mertens estimate applies to the
rounded cutoff. -/
theorem three_le_roughCutoff {x : ℕ} (hx : 512 ≤ x) :
    3 ≤ roughCutoff x := by
  apply Nat.le_floor
  have hlog512 : (6 : ℝ) ≤ Real.log 512 := by
    rw [show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow]
    norm_num
    nlinarith [Real.log_two_gt_d9]
  have hlogx : Real.log (512 : ℝ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hx)
  dsimp [roughCutoff]
  linarith

/-- The rough set has the `x / O(log log x)` supply required by CFP. -/
theorem eventually_roughNumbers_card_lower :
    ∀ᶠ x : ℕ in Filter.atTop,
      (x : ℝ) /
          (2 * roughMertensConstant * Real.log (Real.log (x : ℝ))) ≤
        (roughNumbers x).card := by
  filter_upwards [Filter.eventually_ge_atTop 512,
    eventually_two_mul_roughModulus_le] with x hx hmod
  have hw : 3 ≤ roughCutoff x := three_le_roughCutoff hx
  have hrough := roughNumbersAt_card_lower_real hw hmod
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hlog0 : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg hxone
  have hcut : (roughCutoff x : ℝ) ≤ Real.log (x : ℝ) := by
    calc
      (roughCutoff x : ℝ) ≤ Real.log (x : ℝ) / 2 :=
        Nat.floor_le (by positivity)
      _ ≤ Real.log (x : ℝ) := by linarith
  have hcutpos : (0 : ℝ) < roughCutoff x := by positivity
  have hloglogpos : 0 < Real.log (Real.log (x : ℝ)) := by
    apply Real.log_pos
    have hthree : (3 : ℝ) ≤ Real.log (x : ℝ) :=
      (by exact_mod_cast hw : (3 : ℝ) ≤ roughCutoff x).trans hcut
    linarith
  have hlogcutpos : 0 < Real.log (roughCutoff x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < roughCutoff x by omega))
  have hlogcut : Real.log (roughCutoff x : ℝ) ≤
      Real.log (Real.log (x : ℝ)) :=
    Real.log_le_log hcutpos hcut
  have hK : (0 : ℝ) < roughMertensConstant := by
    exact_mod_cast roughMertensConstant_pos
  have hdenLogLog :
      0 < 2 * roughMertensConstant * Real.log (Real.log (x : ℝ)) := by
    positivity
  have hdenCut :
      0 < 2 * roughMertensConstant * Real.log (roughCutoff x : ℝ) := by
    positivity
  calc
    (x : ℝ) /
        (2 * roughMertensConstant * Real.log (Real.log (x : ℝ))) ≤
        (x : ℝ) /
          (2 * roughMertensConstant * Real.log (roughCutoff x : ℝ)) := by
      apply (div_le_div_iff₀ hdenLogLog hdenCut).2
      gcongr
    _ ≤ (roughNumbers x).card := by
      simpa [roughNumbers] using hrough

/-- Reduction modulo `m` is injective on any interval `[x,2x)` once
`x ≤ m`: two distinct representatives differ by less than the modulus. -/
theorem natCast_zmod_injOn_Ico {x m : ℕ} (_hm : 0 < m) (hxm : x ≤ m) :
    Set.InjOn (fun n : ℕ ↦ (n : ZMod m)) (Finset.Ico x (2 * x) : Set ℕ) := by
  intro a ha b hb hab
  change a ∈ Finset.Ico x (2 * x) at ha
  change b ∈ Finset.Ico x (2 * x) at hb
  have ha' := Finset.mem_Ico.mp ha
  have hb' := Finset.mem_Ico.mp hb
  rw [ZMod.natCast_eq_natCast_iff] at hab
  have hab' : a - x ≡ b - x [MOD m] :=
    hab.sub ha'.1 hb'.1 (.refl x)
  rw [Nat.ModEq, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at hab'
  · omega
  · have : b < x + m := by omega
    omega
  · have : a < x + m := by omega
    omega

/-- In particular, reduction modulo any member `m` of the rough interval is
injective on the whole rough set. -/
theorem roughNumbersAt_cast_injective_of_mem {x w m : ℕ}
    (hm : m ∈ roughNumbersAt x w) :
    Set.InjOn (fun n : ℕ ↦ (n : ZMod m)) (roughNumbersAt x w : Set ℕ) := by
  have hm' := mem_roughNumbersAt.mp hm
  have hmpos : 0 < m := by omega
  apply (natCast_zmod_injOn_Ico hmpos hm'.1).mono
  intro n hn
  exact Finset.mem_Ico.mpr ⟨(mem_roughNumbersAt.mp hn).1,
    (mem_roughNumbersAt.mp hn).2.1⟩

/-- A proper additive subgroup of a cyclic group has at most `m/minFac(m)`
elements, in a denominator-free form. -/
theorem zmod_proper_addSubgroup_minFac_mul_card_le
    (m : ℕ) (hm : 1 < m) (H : AddSubgroup (ZMod m)) (hH : H ≠ ⊤) :
    m.minFac * Nat.card H ≤ m := by
  let _ : NeZero m := ⟨by omega⟩
  have hindex : 1 < H.index := AddSubgroup.one_lt_index_of_ne_top hH
  have hcard : Nat.card H * H.index = m := by
    simpa only [Nat.card_zmod] using H.card_mul_index
  have hindex_dvd : H.index ∣ m := by
    simpa only [hcard] using (dvd_mul_left H.index (Nat.card H))
  have hmin : m.minFac ≤ H.index :=
    Nat.minFac_le_of_dvd (by omega) hindex_dvd
  calc
    m.minFac * Nat.card H ≤ H.index * Nat.card H := Nat.mul_le_mul_right _ hmin
    _ = m := by rw [Nat.mul_comm, hcard]

theorem zmod_proper_addSubgroup_scale_card_le
    (m w : ℕ) (hm : 1 < m) (hw : w ≤ m.minFac)
    (H : AddSubgroup (ZMod m)) (hH : H ≠ ⊤) :
    w * Nat.card H ≤ m := by
  exact (Nat.mul_le_mul_right (Nat.card H) hw).trans
    (zmod_proper_addSubgroup_minFac_mul_card_le m hm H hH)

/-- Translation does not change the size of an additive subgroup. -/
theorem zmod_addSubgroup_coset_ncard
    (m : ℕ) (a : ZMod m) (H : AddSubgroup (ZMod m)) :
    (a +ᵥ (H : Set (ZMod m))).ncard = Nat.card H := by
  rw [Set.ncard_vadd_set]
  exact (Nat.card_coe_set_eq (H : Set (ZMod m))).symm

theorem zmod_proper_addSubgroup_coset_scale_ncard_le
    (m w : ℕ) (hm : 1 < m) (hw : w ≤ m.minFac)
    (a : ZMod m) (H : AddSubgroup (ZMod m)) (hH : H ≠ ⊤) :
    w * (a +ᵥ (H : Set (ZMod m))).ncard ≤ m := by
  rw [zmod_addSubgroup_coset_ncard]
  exact zmod_proper_addSubgroup_scale_card_le m w hm hw H hH

/-- A proper coset modulo a rough integer occupies at most a `1/(w+1)`
fraction of all residue classes. -/
theorem roughNumbersAt_proper_coset_card_bound {x w m : ℕ}
    (hm : m ∈ roughNumbersAt x w) (a : ZMod m)
    (H : AddSubgroup (ZMod m)) (hH : H ≠ ⊤) :
    (w + 1) * (a +ᵥ (H : Set (ZMod m))).ncard ≤ m := by
  have hmpos : 0 < m := by
    have hm' := mem_roughNumbersAt.mp hm
    omega
  have hm1 : 1 < m := by
    by_contra h
    have hmone : m = 1 := by omega
    subst m
    exact hH (Subsingleton.elim H ⊤)
  exact zmod_proper_addSubgroup_coset_scale_ncard_le m (w + 1) hm1
    (Nat.succ_le_iff.mpr (cutoff_lt_minFac_of_mem_roughNumbersAt hm hm1)) a H hH

end Erdos54
