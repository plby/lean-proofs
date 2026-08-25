import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-!
# Elementary collision estimates for Burgess averaging

The interval-collision and harmonic overcount arguments are extracted from
`Erdos587.NVDevelopment`. They are independent of its fixed fourth-moment
estimate and apply to every modulus with coprime denominators.
-/

namespace Pollack17.Burgess

open scoped BigOperators

lemma sum_Icc_inv_natCast_le_one_add_log (n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, ((r : ℝ)⁻¹)) ≤ 1 + Real.log n := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast] using harmonic_le_one_add_log n

/-- Scaled harmonic estimate in the exact form of the nonzero-residue term in
the quadratic Weyl bound. -/
lemma sum_Icc_natCast_div_le (q n : ℕ) :
    (∑ r ∈ Finset.Icc 1 n, (q : ℝ) / r) ≤
      q * (1 + Real.log n) := by
  simp_rw [div_eq_mul_inv]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (sum_Icc_inv_natCast_le_one_add_log n)
    (Nat.cast_nonneg q)

lemma card_le_div_add_one_of_pairwise_modEq {s : Finset ℕ} {X h : ℕ}
    (hsX : s ⊆ Finset.Icc 1 X) (_hh : 0 < h)
    (hmod : ∀ a ∈ s, ∀ b ∈ s, a ≡ b [MOD h]) :
    s.card ≤ X / h + 1 := by
  let f : ℕ → ℕ := fun a ↦ a / h
  have hinj : Set.InjOn f s := by
    intro a ha b hb hab
    have hrem : a % h = b % h := hmod a ha b hb
    have hda : h * (a / h) + a % h = a := Nat.div_add_mod a h
    have hdb : h * (b / h) + b % h = b := Nat.div_add_mod b h
    dsimp [f] at hab
    calc
      a = h * (a / h) + a % h := hda.symm
      _ = h * (b / h) + b % h := by rw [hab, hrem]
      _ = b := hdb
  have himage : s.image f ⊆ Finset.range (X / h + 1) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [Finset.mem_range]
    have haX : a ≤ X := (Finset.mem_Icc.mp (hsX ha)).2
    exact Nat.lt_succ_of_le (Nat.div_le_div_right haX)
  calc
    s.card = (s.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (X / h + 1)).card := Finset.card_le_card himage
    _ = X / h + 1 := Finset.card_range _

lemma card_le_div_add_one_of_fst_pairwise_modEq
    {s : Finset (ℕ × ℕ)} {H a : ℕ}
    (hsH : ∀ z ∈ s, z.1 < H) (ha : 0 < a)
    (hinj : Set.InjOn (fun z : ℕ × ℕ ↦ z.1) s)
    (hmod : ∀ z ∈ s, ∀ w ∈ s, z.1 ≡ w.1 [MOD a]) :
    s.card ≤ H / a + 1 := by
  let f : ℕ × ℕ → ℕ := fun z ↦ z.1 + 1
  have hfinj : Set.InjOn f s := by
    intro z hz w hw hzw
    apply hinj hz hw
    change z.1 + 1 = w.1 + 1 at hzw
    exact Nat.add_right_cancel hzw
  have hcard : s.card = (s.image f).card :=
    (Finset.card_image_of_injOn hfinj).symm
  rw [hcard]
  apply card_le_div_add_one_of_pairwise_modEq
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    simp only [Finset.mem_Icc]
    exact ⟨Nat.succ_pos _, Nat.succ_le_iff.mpr (hsH z hz)⟩
  · exact ha
  · intro x hx y hy
    rw [Finset.mem_image] at hx hy
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    exact (hmod z hz w hw).add_right 1

/-- Pairs of interval positions which give the same quotient after the two
fixed Burgess denominators are cross-multiplied modulo `p`. -/
def burgessIntervalCollision (p M H u₁ u₂ : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range H) ×ˢ (Finset.range H)).filter fun ij ↦
    (M + ij.1) * u₂ ≡ (M + ij.2) * u₁ [MOD p]
def positiveMultiplesUpTo (d U : ℕ) : Finset ℕ :=
  (Finset.Icc 1 U).filter fun u ↦ d ∣ u

lemma positiveMultiplesUpTo_card (d U : ℕ) :
    (positiveMultiplesUpTo d U).card = U / d := by
  have hset : Finset.Icc 1 U = Finset.Ioc 0 U := by
    ext x
    simp
    omega
  rw [positiveMultiplesUpTo, hset]
  exact Nat.Ioc_filter_dvd_card_eq_div U d

/-- Division by `d` bijects its positive multiples up to `U` with the
positive integers up to `U / d`. -/
lemma sum_positiveMultiplesUpTo_quotient
    {R : Type*} [AddCommMonoid R] (d U : ℕ) (hd : 0 < d)
    (f : ℕ → R) :
    (∑ u ∈ positiveMultiplesUpTo d U, f (u / d)) =
      ∑ a ∈ Finset.Icc 1 (U / d), f a := by
  apply Finset.sum_bij (fun u _ ↦ u / d)
  · intro u hu
    change u ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u) at hu
    rw [Finset.mem_filter] at hu
    rw [Finset.mem_Icc]
    exact ⟨Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp hu.1).1 hu.2) hd,
      Nat.div_le_div_right (Finset.mem_Icc.mp hu.1).2⟩
  · intro u₁ hu₁ u₂ hu₂ h
    change u₁ ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u) at hu₁
    change u₂ ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u) at hu₂
    have hd₁ := (Finset.mem_filter.mp hu₁).2
    have hd₂ := (Finset.mem_filter.mp hu₂).2
    calc
      u₁ = d * (u₁ / d) := (Nat.mul_div_cancel' hd₁).symm
      _ = d * (u₂ / d) := by rw [h]
      _ = u₂ := Nat.mul_div_cancel' hd₂
  · intro a ha
    refine ⟨d * a, ?_, ?_⟩
    · change d * a ∈ (Finset.Icc 1 U).filter (fun u ↦ d ∣ u)
      rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_Icc] at ha ⊢
        exact ⟨Nat.mul_pos hd ha.1,
          by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).mp ha.2⟩
      · exact dvd_mul_right d a
    · rw [Nat.mul_div_cancel_left]
      exact hd
  · intro u hu
    rfl

lemma sum_Icc_natDiv_add_one_cast_le (H n : ℕ) :
    (((∑ a ∈ Finset.Icc 1 n, (H / a + 1)) : ℕ) : ℝ) ≤
      H * (1 + Real.log n) + n := by
  rw [Nat.cast_sum]
  calc
    (∑ a ∈ Finset.Icc 1 n, (((H / a + 1) : ℕ) : ℝ)) ≤
        ∑ a ∈ Finset.Icc 1 n, ((H : ℝ) / a + 1) := by
      apply Finset.sum_le_sum
      intro a ha
      norm_num only [Nat.cast_add, Nat.cast_one]
      exact add_le_add (Nat.cast_div_le (α := ℝ) (m := H) (n := a)) le_rfl
    _ = (∑ a ∈ Finset.Icc 1 n, (H : ℝ) / a) + n := by
      rw [Finset.sum_add_distrib]
      simp
    _ ≤ H * (1 + Real.log n) + n := by
      gcongr
      exact sum_Icc_natCast_div_le H n

/-- The gcd itself is one of the common divisors, so the reduced-denominator
term is bounded by the sum over all common divisors. -/
lemma reduced_term_le_common_divisor_sum
    {H U u₁ u₂ : ℕ} (hu₁ : u₁ ∈ Finset.Icc 1 U) :
    H / (u₁ / u₁.gcd u₂) + 1 ≤
      ∑ d ∈ Finset.Icc 1 U,
        if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
  let d := u₁.gcd u₂
  have hu₁pos : 0 < u₁ := (Finset.mem_Icc.mp hu₁).1
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left u₂ hu₁pos
  have hdmem : d ∈ Finset.Icc 1 U := by
    rw [Finset.mem_Icc]
    exact ⟨hdpos, (Nat.gcd_le_left u₂ hu₁pos).trans
      (Finset.mem_Icc.mp hu₁).2⟩
  calc
    H / (u₁ / u₁.gcd u₂) + 1 =
        if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      simp [d, Nat.gcd_dvd_left, Nat.gcd_dvd_right]
    _ ≤ ∑ d ∈ Finset.Icc 1 U,
        if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      exact Finset.single_le_sum
        (s := Finset.Icc 1 U)
        (f := fun d ↦ if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0)
        (fun _ _ ↦ Nat.zero_le _) hdmem

def burgessDivisorOvercount (H U : ℕ) : ℕ :=
  ∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
    ∑ d ∈ Finset.Icc 1 U,
      if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0

lemma burgessDivisorSlice_eq (H U d : ℕ) (hd : 0 < d) :
    (∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
      if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0) =
      (U / d) * ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1) := by
  classical
  simp_rw [ite_and]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero]
  rw [← Finset.sum_filter]
  change (∑ u₁ ∈ positiveMultiplesUpTo d U,
      ∑ u₂ ∈ Finset.Icc 1 U,
        if d ∣ u₂ then H / (u₁ / d) + 1 else 0) = _
  calc
    (∑ u₁ ∈ positiveMultiplesUpTo d U,
        ∑ u₂ ∈ Finset.Icc 1 U,
          if d ∣ u₂ then H / (u₁ / d) + 1 else 0) =
      ∑ u₁ ∈ positiveMultiplesUpTo d U,
        ∑ _u₂ ∈ positiveMultiplesUpTo d U,
          (H / (u₁ / d) + 1) := by
      apply Finset.sum_congr rfl
      intro u₁ hu₁
      rw [← Finset.sum_filter]
      rfl
    _ = (U / d) * ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1) := by
      simp_rw [Finset.sum_const]
      rw [positiveMultiplesUpTo_card]
      simp_rw [Nat.nsmul_eq_mul]
      rw [← Finset.mul_sum]
      congr 1
      exact sum_positiveMultiplesUpTo_quotient d U hd
        (fun a ↦ H / a + 1)

lemma burgessDivisorOvercount_eq (H U : ℕ) :
    burgessDivisorOvercount H U =
      ∑ d ∈ Finset.Icc 1 U, (U / d) *
        ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1) := by
  rw [burgessDivisorOvercount]
  calc
    (∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
        ∑ d ∈ Finset.Icc 1 U,
          if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0) =
      ∑ u₁ ∈ Finset.Icc 1 U, ∑ d ∈ Finset.Icc 1 U,
        ∑ u₂ ∈ Finset.Icc 1 U,
          if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u₁ hu₁
      rw [Finset.sum_comm]
    _ = ∑ d ∈ Finset.Icc 1 U, ∑ u₁ ∈ Finset.Icc 1 U,
        ∑ u₂ ∈ Finset.Icc 1 U,
          if d ∣ u₁ ∧ d ∣ u₂ then H / (u₁ / d) + 1 else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hdmem
      exact burgessDivisorSlice_eq H U d (Finset.mem_Icc.mp hdmem).1

lemma burgessDivisorOvercount_cast_le (H U : ℕ) (hU : 0 < U) :
    (burgessDivisorOvercount H U : ℝ) ≤
      ((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U)) := by
  rw [burgessDivisorOvercount_eq, Nat.cast_sum]
  have hlogU : 0 ≤ 1 + Real.log U := by
    have : (1 : ℝ) ≤ U := by exact_mod_cast hU
    linarith [Real.log_nonneg this]
  calc
    (∑ d ∈ Finset.Icc 1 U,
        ((((U / d) * ∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1)) : ℕ) : ℝ)) ≤
      ∑ d ∈ Finset.Icc 1 U,
        ((U : ℝ) / d) * ((H : ℝ) * (1 + Real.log U) + U) := by
      apply Finset.sum_le_sum
      intro d hdmem
      have hdpos : 0 < d := (Finset.mem_Icc.mp hdmem).1
      have hdU : d ≤ U := (Finset.mem_Icc.mp hdmem).2
      have hnpos : 0 < U / d := Nat.div_pos hdU hdpos
      have hnU : U / d ≤ U := Nat.div_le_self U d
      have hlog : Real.log (((U / d : ℕ) : ℝ)) ≤ Real.log U := by
        apply Real.log_le_log
        · exact_mod_cast hnpos
        · exact_mod_cast hnU
      rw [Nat.cast_mul]
      apply mul_le_mul
      · exact Nat.cast_div_le
      · calc
          (((∑ a ∈ Finset.Icc 1 (U / d), (H / a + 1)) : ℕ) : ℝ) ≤
              (H : ℝ) * (1 + Real.log (((U / d : ℕ) : ℝ))) +
                (U / d : ℕ) :=
            sum_Icc_natDiv_add_one_cast_le H (U / d)
          _ ≤ (H : ℝ) * (1 + Real.log U) + U := by
            gcongr
      · positivity
      · positivity
    _ = ((H : ℝ) * (1 + Real.log U) + U) *
        ∑ d ∈ Finset.Icc 1 U, ((U : ℝ) / d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ ((H : ℝ) * (1 + Real.log U) + U) *
        ((U : ℝ) * (1 + Real.log U)) := by
      exact mul_le_mul_of_nonneg_left (sum_Icc_natCast_div_le U U)
        (add_nonneg (mul_nonneg (Nat.cast_nonneg H) hlogU) (Nat.cast_nonneg U))

lemma reduced_denominator_sum_cast_le
    (H U : ℕ) :
    ((∑ u₁ ∈ Finset.Icc 1 U, ∑ u₂ ∈ Finset.Icc 1 U,
      (H / (u₁ / u₁.gcd u₂) + 1) : ℕ) : ℝ) ≤
      (burgessDivisorOvercount H U : ℝ) := by
  exact_mod_cast Finset.sum_le_sum fun u₁ hu₁ ↦
    Finset.sum_le_sum fun u₂ hu₂ ↦
      reduced_term_le_common_divisor_sum hu₁
lemma burgessIntervalCollision_card_le_of_coprime
    {q M H U u₁ u₂ : ℕ}
    (hH : 0 < H) (hU : 0 < U)
    (hu₁ : u₁ ∈ Finset.Icc 1 U) (hu₂ : u₂ ∈ Finset.Icc 1 U)
    (hcop₁ : q.Coprime u₁)
    (hsmall : 2 * (U * H) < q) :
    (burgessIntervalCollision q M H u₁ u₂).card ≤
      H / (u₁ / u₁.gcd u₂) + 1 := by
  let d := u₁.gcd u₂
  let a := u₁ / d
  let b := u₂ / d
  have hu₁pos : 0 < u₁ := (Finset.mem_Icc.mp hu₁).1
  have hu₂pos : 0 < u₂ := (Finset.mem_Icc.mp hu₂).1
  have hu₁U : u₁ ≤ U := (Finset.mem_Icc.mp hu₁).2
  have hu₂U : u₂ ≤ U := (Finset.mem_Icc.mp hu₂).2
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left u₂ hu₁pos
  have hd₁ : d ∣ u₁ := Nat.gcd_dvd_left u₁ u₂
  have hd₂ : d ∣ u₂ := Nat.gcd_dvd_right u₁ u₂
  have hfac₁ : d * a = u₁ := Nat.mul_div_cancel' hd₁
  have hfac₂ : d * b = u₂ := Nat.mul_div_cancel' hd₂
  have hapos : 0 < a := Nat.div_pos (Nat.le_of_dvd hu₁pos hd₁) hdpos
  have hab : a.Coprime b := Nat.coprime_div_gcd_div_gcd hdpos
  apply card_le_div_add_one_of_fst_pairwise_modEq
  · intro z hz
    exact Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).1
  · exact hapos
  · intro z hz w hw hzw
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    apply Prod.ext hzw
    change z.1 = w.1 at hzw
    rw [hzw] at hz'
    have hjmodM : M + z.2 ≡ M + w.2 [MOD q] := by
      apply Nat.ModEq.cancel_right_of_coprime hcop₁.gcd_eq_one
      exact hz'.symm.trans hw'
    have hjmod : z.2 ≡ w.2 [MOD q] :=
      Nat.ModEq.add_left_cancel' M hjmodM
    have hHq : H < q := by
      have hUHpos : 0 < U * H := Nat.mul_pos hU hH
      have hHle : H ≤ U * H := by
        simpa [mul_comm] using Nat.le_mul_of_pos_right H hU
      omega
    exact hjmod.eq_of_lt_of_lt
      (lt_trans (Finset.mem_range.mp
        (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).2) hHq)
      (lt_trans (Finset.mem_range.mp
        (Finset.mem_product.mp (Finset.filter_subset _ _ hw)).2) hHq)
  · intro z hz w hw
    have hz' := (Finset.mem_filter.mp hz).2
    have hw' := (Finset.mem_filter.mp hw).2
    have hsum := hz'.add hw'.symm
    have hred : u₂ * z.1 + u₁ * w.2 ≡
        u₂ * w.1 + u₁ * z.2 [MOD q] := by
      apply Nat.ModEq.add_left_cancel' (M * (u₁ + u₂))
      simpa [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc,
        add_comm, add_left_comm, add_assoc] using hsum
    have hzH := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).1
    have hzH₂ := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hz)).2
    have hwH := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hw)).1
    have hwH₂ := Finset.mem_range.mp
      (Finset.mem_product.mp (Finset.filter_subset _ _ hw)).2
    have hterm₁ : u₂ * z.1 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₂U hzH hU
    have hterm₂ : u₁ * w.2 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₁U hwH₂ hU
    have hterm₃ : u₂ * w.1 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₂U hwH hU
    have hterm₄ : u₁ * z.2 < U * H :=
      Nat.mul_lt_mul_of_le_of_lt hu₁U hzH₂ hU
    have heq : u₂ * z.1 + u₁ * w.2 =
        u₂ * w.1 + u₁ * z.2 :=
      hred.eq_of_lt_of_lt (by omega) (by omega)
    have hdeq : d * (b * z.1 + a * w.2) =
        d * (b * w.1 + a * z.2) := by
      calc
        d * (b * z.1 + a * w.2) = u₂ * z.1 + u₁ * w.2 := by
          rw [mul_add, ← mul_assoc, ← mul_assoc, hfac₂, hfac₁]
        _ = u₂ * w.1 + u₁ * z.2 := heq
        _ = d * (b * w.1 + a * z.2) := by
          rw [mul_add, ← mul_assoc, ← mul_assoc, hfac₂, hfac₁]
    have hnorm : b * z.1 + a * w.2 = b * w.1 + a * z.2 :=
      Nat.eq_of_mul_eq_mul_left hdpos hdeq
    have haw : a * w.2 ≡ 0 [MOD a] :=
      (Nat.dvd_mul_right a w.2).modEq_zero_nat
    have haz : a * z.2 ≡ 0 [MOD a] :=
      (Nat.dvd_mul_right a z.2).modEq_zero_nat
    have hfull : b * z.1 + a * w.2 ≡ b * w.1 + a * z.2 [MOD a] := by
      rw [hnorm]
    have hba : b * z.1 ≡ b * w.1 [MOD a] :=
      ((Nat.ModEq.rfl.add haw.symm).trans hfull).trans
        (Nat.ModEq.rfl.add haz)
    exact Nat.ModEq.cancel_left_of_coprime hab.gcd_eq_one hba

end Pollack17.Burgess
