import ErdosProblems.Erdos1141.CharacterSums

/-!
# Complete quadratic character sums at squarefree moduli

Chinese remaindering turns complete sums for products of prime quadratic
characters into products of finite-field sums.
-/

open scoped BigOperators

namespace Erdos1141.CharacterSums

/-- At a prime dividing the root differences we use the trivial bound. -/
lemma prime_quartic_bound (q : ℕ) [Fact q.Prime] (hq : q ≠ 2) (a b c d : ℤ) :
    |((∑ x : ZMod q,
      quadraticChar (ZMod q) ((x - a) * (x - b) * (x - c) * (x - d)) : ℤ) : ℝ)| ≤
      3 * Real.sqrt q * Real.sqrt (if (q : ℤ) ∣ (a - b) * (a - c) * (a - d)
        then (q : ℝ) else 1) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hsqrt : (1 : ℝ) ≤ Real.sqrt q := Real.one_le_sqrt.mpr (by
    exact_mod_cast (Fact.out : q.Prime).one_le)
  by_cases hdiv : (q : ℤ) ∣ (a - b) * (a - c) * (a - d)
  · rw [if_pos hdiv]
    push_cast
    have htriv :
        |∑ x : ZMod q,
          (quadraticChar (ZMod q) ((x - a) * (x - b) * (x - c) * (x - d)) : ℝ)| ≤ q := by
      calc
        _ ≤ ∑ x : ZMod q,
            |(quadraticChar (ZMod q) ((x - a) * (x - b) * (x - c) * (x - d)) : ℝ)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _x : ZMod q, (1 : ℝ) :=
          Finset.sum_le_sum fun x _ ↦ abs_quadraticChar_le_one _
        _ = q := by simp
    have hsq := Real.sq_sqrt hqpos.le
    nlinarith
  · rw [if_neg hdiv, Real.sqrt_one, mul_one]
    have hab : (a : ZMod q) ≠ b := by
      intro h
      have hd : (q : ℤ) ∣ a - b := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by
        push_cast; exact sub_eq_zero.mpr h)
      exact hdiv (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _)
    have hac : (a : ZMod q) ≠ c := by
      intro h
      have hd : (q : ℤ) ∣ a - c := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by
        push_cast; exact sub_eq_zero.mpr h)
      exact hdiv (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _)
    have had : (a : ZMod q) ≠ d := by
      intro h
      have hd : (q : ℤ) ∣ a - d := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by
        push_cast; exact sub_eq_zero.mpr h)
      exact hdiv (dvd_mul_of_dvd_right hd _)
    have h := abs_sum_quadraticChar_prod_four_le
      (by simpa only [ZMod.ringChar_zmod_n] using hq : ringChar (ZMod q) ≠ 2)
      (a : ZMod q) b c d hab hac had
    simp only [ZMod.card] at h
    linarith

variable {ι : Type*} [Fintype ι] (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hc : Pairwise fun i j ↦ (p i).Coprime (p j))

instance primeProduct_neZero : NeZero (∏ i, p i) :=
  ⟨Finset.prod_ne_zero_iff.mpr fun i _ ↦ (Fact.out : (p i).Prime).ne_zero⟩

/-- The product of the prime quadratic characters, transported by the CRT. -/
noncomputable def primeProductCharacter (x : ZMod (∏ i, p i)) : ℤ :=
  ∏ i, quadraticChar (ZMod (p i)) (ZMod.prodEquivPi p hc x i)

omit [Fintype ι] in
lemma jacobiSym_prime_prod (a : ℤ) (s : Finset ι) :
    jacobiSym a (∏ i ∈ s, p i) = ∏ i ∈ s, jacobiSym a (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hprod : (∏ j ∈ s, p j) ≠ 0 := Finset.prod_ne_zero_iff.mpr
      (fun j _ ↦ (Fact.out : (p j).Prime).ne_zero)
    simp only [Finset.prod_insert hi,
      jacobiSym.mul_right' a (Fact.out : (p i).Prime).ne_zero hprod, ih]

/-- The product character agrees with the usual Jacobi symbol on integers. -/
lemma primeProductCharacter_intCast (n : ℤ) :
    primeProductCharacter p hc n = jacobiSym n (∏ i, p i) := by
  rw [jacobiSym_prime_prod]
  unfold primeProductCharacter
  apply Finset.prod_congr rfl
  intro i _
  simp only [ZMod.prodEquivPi_apply, map_intCast]
  exact jacobiSym.legendreSym.to_jacobiSym (p i) n

lemma primeProductCharacter_natCast (n : ℕ) :
    primeProductCharacter p hc n = ∏ i, quadraticChar (ZMod (p i)) (n : ZMod (p i)) := by
  simp [primeProductCharacter]

lemma primeProductCharacter_mul (x y : ZMod (∏ i, p i)) :
    primeProductCharacter p hc (x * y) =
      primeProductCharacter p hc x * primeProductCharacter p hc y := by
  simp [primeProductCharacter, map_mul, Finset.prod_mul_distrib]

include hc in
omit [Fintype ι] in
lemma primeProduct_injective : Function.Injective p := by
  intro i j hij
  by_contra hne
  have h : (p i).Coprime (p j) := hc hne
  rw [hij, Nat.coprime_self] at h
  exact (Fact.out : (p j).Prime).ne_one h

include hc in
lemma primeProduct_primeFactors_card :
    (∏ i, p i : ℕ).primeFactors.card = Fintype.card ι := by
  classical
  have hp : ∏ a ∈ Finset.univ.image p, a = ∏ i, p i := by
    rw [Finset.prod_image]
    intro i _ j _ hij
    exact primeProduct_injective p hc hij
  rw [← hp, Nat.primeFactors_prod]
  · exact Finset.card_image_of_injective _ (primeProduct_injective p hc)
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact Fact.out

/-- A complete quartic sum factors into its prime-modulus sums. -/
theorem sum_primeProductCharacter_quartic (a b c d : ℤ) :
    (∑ x : ZMod (∏ i, p i),
      primeProductCharacter p hc ((x - a) * (x - b) * (x - c) * (x - d))) =
    ∏ i, ∑ x : ZMod (p i),
      quadraticChar (ZMod (p i)) ((x - a) * (x - b) * (x - c) * (x - d)) := by
  classical
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv (ZMod.prodEquivPi p hc).toEquiv
  intro x
  simp only [primeProductCharacter, map_mul, map_sub, map_intCast,
    Pi.mul_apply, Pi.sub_apply, Pi.intCast_apply]
  rfl

include hc in
omit [∀ i, Fact (p i).Prime] in
lemma prod_bad_primes_le_natAbs (D : ℤ) (hD : D ≠ 0) :
    (∏ i, if (p i : ℤ) ∣ D then p i else 1) ≤ D.natAbs := by
  classical
  let w : ι → ℕ := fun i ↦ if (p i : ℤ) ∣ D then p i else 1
  have hcop : Pairwise fun i j ↦ IsCoprime (w i : ℤ) (w j : ℤ) := by
    intro i j hij
    dsimp [w]
    split_ifs
    · exact (hc hij).cast (R := ℤ)
    · exact isCoprime_one_right
    · exact isCoprime_one_left
    · exact isCoprime_one_left
  have hdvd : (∏ i, (w i : ℤ)) ∣ D := Fintype.prod_dvd_of_coprime hcop (by
    intro i
    dsimp [w]
    split_ifs with h
    · exact h
    · exact one_dvd D)
  have hdvd' : (∏ i, w i) ∣ D.natAbs := by
    apply Int.natCast_dvd.mp
    simpa only [Nat.cast_prod] using hdvd
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hD) hdvd'

/-- A deliberately coarse complete-sum bound, sufficient for a power saving below `q^(1/2)`.
Only the three differences from one simple root enter the loss. -/
theorem abs_sum_primeProductCharacter_quartic_le
    (hodd : ∀ i, p i ≠ 2) (a b c d : ℤ)
    (hD : (a - b) * (a - c) * (a - d) ≠ 0) :
    |((∑ x : ZMod (∏ i, p i),
      primeProductCharacter p hc ((x - a) * (x - b) * (x - c) * (x - d)) : ℤ) : ℝ)| ≤
      3 ^ Fintype.card ι * Real.sqrt (∏ i, p i : ℕ) *
        Real.sqrt ((a - b) * (a - c) * (a - d)).natAbs := by
  classical
  let D : ℤ := (a - b) * (a - c) * (a - d)
  let w : ι → ℕ := fun i ↦ if (p i : ℤ) ∣ D then p i else 1
  have hw : (∏ i, w i) ≤ D.natAbs := prod_bad_primes_le_natAbs p hc D hD
  rw [sum_primeProductCharacter_quartic, Int.cast_prod, Finset.abs_prod]
  calc
    _ ≤ ∏ i, (3 * Real.sqrt (p i : ℝ) * Real.sqrt (w i : ℝ)) := by
      apply Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _)
      intro i _
      simpa only [w, D, Nat.cast_ite, Nat.cast_one] using
        prime_quartic_bound (p i) (hodd i) a b c d
    _ = 3 ^ Fintype.card ι * Real.sqrt (∏ i, p i : ℕ) * Real.sqrt (∏ i, w i : ℕ) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      rw [← Real.sqrt_prod Finset.univ (fun i _ ↦ Nat.cast_nonneg (p i)),
        ← Real.sqrt_prod Finset.univ (fun i _ ↦ Nat.cast_nonneg (w i))]
      simp only [Finset.prod_const, Finset.card_univ, Nat.cast_prod]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hw))
      (by positivity)

lemma abs_primeProductCharacter_le_one (x : ZMod (∏ i, p i)) :
    |(primeProductCharacter p hc x : ℝ)| ≤ 1 := by
  classical
  rw [primeProductCharacter, Int.cast_prod, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ ↦ abs_nonneg _) (fun _ _ ↦ abs_quadraticChar_le_one _)

/-- The complete-sum estimate for shifts in a bounded interval of integers. -/
lemma abs_sum_primeProductCharacter_bounded_quartic_le
    (hodd : ∀ i, p i ≠ 2) {B a b c d : ℕ}
    (ha : a ≤ B) (hb : b ≤ B) (hc' : c ≤ B) (hd : d ≤ B)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    |((∑ x : ZMod (∏ i, p i),
      primeProductCharacter p hc ((x - a) * (x - b) * (x - c) * (x - d)) : ℤ) : ℝ)| ≤
      3 ^ Fintype.card ι * Real.sqrt (∏ i, p i : ℕ) * Real.sqrt ((B : ℝ) ^ 3) := by
  have hD : ((a : ℤ) - b) * ((a : ℤ) - c) * ((a : ℤ) - d) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast hab))
      (sub_ne_zero.mpr (by exact_mod_cast hac))) (sub_ne_zero.mpr (by exact_mod_cast had))
  have hsize : (((((a : ℤ) - b) * ((a : ℤ) - c) * ((a : ℤ) - d)).natAbs) : ℝ) ≤
      (B : ℝ) ^ 3 := by
    have hn : ((((a : ℤ) - b) * ((a : ℤ) - c) * ((a : ℤ) - d)).natAbs) ≤ B ^ 3 := by
      rw [Int.natAbs_mul, Int.natAbs_mul]
      calc
        _ ≤ B * B * B := Nat.mul_le_mul
          (Nat.mul_le_mul (Int.natAbs_coe_sub_coe_le_of_le ha hb)
            (Int.natAbs_coe_sub_coe_le_of_le ha hc'))
          (Int.natAbs_coe_sub_coe_le_of_le ha hd)
        _ = _ := by ring
    exact_mod_cast hn
  have h := abs_sum_primeProductCharacter_quartic_le p hc hodd a b c d hD
  simp only [Int.cast_natCast] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsize) (by positivity))

lemma abs_sum_primeProductCharacter_unpaired_le
    (hodd : ∀ i, p i ≠ 2) {B a b c d : ℕ}
    (ha : a ≤ B) (hb : b ≤ B) (hc' : c ≤ B) (hd : d ≤ B)
    (h : ¬ ((a = b ∧ c = d) ∨ (a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    |((∑ x : ZMod (∏ i, p i),
      primeProductCharacter p hc ((x - a) * (x - b) * (x - c) * (x - d)) : ℤ) : ℝ)| ≤
      3 ^ Fintype.card ι * Real.sqrt (∏ i, p i : ℕ) * Real.sqrt ((B : ℝ) ^ 3) := by
  rcases four_has_simple_entry a b c d h with h₁ | h₂ | h₃ | h₄
  · exact abs_sum_primeProductCharacter_bounded_quartic_le p hc hodd
      ha hb hc' hd h₁.1 h₁.2.1 h₁.2.2
  · simpa only [mul_comm, mul_left_comm, mul_assoc] using
      abs_sum_primeProductCharacter_bounded_quartic_le p hc hodd
        hb ha hc' hd h₂.1 h₂.2.1 h₂.2.2
  · simpa only [mul_comm, mul_left_comm, mul_assoc] using
      abs_sum_primeProductCharacter_bounded_quartic_le p hc hodd
        hc' ha hb hd h₃.1 h₃.2.1 h₃.2.2
  · simpa only [mul_comm, mul_left_comm, mul_assoc] using
      abs_sum_primeProductCharacter_bounded_quartic_le p hc hodd
        hd ha hb hc' h₄.1 h₄.2.1 h₄.2.2

lemma sum_primeProductCharacter_quartic_le_indicators
    (hodd : ∀ i, p i ≠ 2) {B a b c d : ℕ}
    (ha : a ≤ B) (hb : b ≤ B) (hc' : c ≤ B) (hd : d ≤ B) :
    (∑ x : ZMod (∏ i, p i),
      (primeProductCharacter p hc ((x - a) * (x - b) * (x - c) * (x - d)) : ℝ)) ≤
      (if a = b ∧ c = d then ((∏ i, p i : ℕ) : ℝ) else 0) +
      (if a = c ∧ b = d then ((∏ i, p i : ℕ) : ℝ) else 0) +
      (if a = d ∧ b = c then ((∏ i, p i : ℕ) : ℝ) else 0) +
      3 ^ Fintype.card ι * Real.sqrt (∏ i, p i : ℕ) * Real.sqrt ((B : ℝ) ^ 3) := by
  have htriv :
      (∑ x : ZMod (∏ i, p i),
        (primeProductCharacter p hc ((x - a) * (x - b) * (x - c) * (x - d)) : ℝ)) ≤
          (∏ i, p i : ℕ) := by
    calc
      _ ≤ ∑ _x : ZMod (∏ i, p i), (1 : ℝ) := Finset.sum_le_sum fun _ _ ↦
        (le_abs_self _).trans (abs_primeProductCharacter_le_one p hc _)
      _ = _ := by simp
  have hC : 0 ≤ 3 ^ Fintype.card ι * Real.sqrt (∏ i, p i : ℕ) *
      Real.sqrt ((B : ℝ) ^ 3) := by positivity
  have hq : (0 : ℝ) ≤ (∏ i, p i : ℕ) := Nat.cast_nonneg _
  split_ifs with h₁ h₂ h₃
  all_goals first
    | linarith
    | have hgood := abs_sum_primeProductCharacter_unpaired_le p hc hodd
        ha hb hc' hd (by tauto)
      push_cast at hgood
      simpa using (le_abs_self _).trans hgood

/-- A coarse composite-modulus fourth moment, avoiding sharp divisor-sum estimates. -/
theorem primeProductCharacter_fourth_moment_le {κ : Type*} [Fintype κ]
    (hodd : ∀ i, p i ≠ 2) (B : ℕ) (f : κ → ℕ) (hf : Function.Injective f)
    (hB : ∀ k, f k ≤ B) :
    (∑ x : ZMod (∏ i, p i), (∑ k : κ, (primeProductCharacter p hc (x - f k) : ℝ)) ^ 4) ≤
      3 * (Fintype.card κ : ℝ) ^ 2 * (∏ i, p i : ℕ) +
      (Fintype.card κ : ℝ) ^ 4 *
        (3 ^ Fintype.card ι * Real.sqrt (∏ i, p i : ℕ) * Real.sqrt ((B : ℝ) ^ 3)) := by
  classical
  have hexpand : ∀ x : ZMod (∏ i, p i),
      (∑ k : κ, (primeProductCharacter p hc (x - f k) : ℝ)) ^ 4 =
        ∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
          (primeProductCharacter p hc
            ((x - f a) * (x - f b) * (x - f c) * (x - f d)) : ℝ) := by
    intro x
    rw [show (∑ k : κ, (primeProductCharacter p hc (x - f k) : ℝ)) ^ 4 =
      (∑ k : κ, (primeProductCharacter p hc (x - f k) : ℝ)) *
      (∑ k : κ, (primeProductCharacter p hc (x - f k) : ℝ)) *
      (∑ k : κ, (primeProductCharacter p hc (x - f k) : ℝ)) *
      (∑ k : κ, (primeProductCharacter p hc (x - f k) : ℝ)) by ring]
    simp only [Finset.mul_sum, primeProductCharacter_mul, Int.cast_mul, mul_comm, mul_assoc]
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]; arg 2; ext b; rw [Finset.sum_comm]
  conv_lhs => arg 2; ext a; arg 2; ext b; arg 2; ext c; rw [Finset.sum_comm]
  calc
    _ ≤ ∑ a : κ, ∑ b : κ, ∑ c : κ, ∑ d : κ,
        ((if f a = f b ∧ f c = f d then ((∏ i, p i : ℕ) : ℝ) else 0) +
         (if f a = f c ∧ f b = f d then ((∏ i, p i : ℕ) : ℝ) else 0) +
         (if f a = f d ∧ f b = f c then ((∏ i, p i : ℕ) : ℝ) else 0) +
         3 ^ Fintype.card ι * Real.sqrt (∏ i, p i : ℕ) * Real.sqrt ((B : ℝ) ^ 3)) := by
      apply Finset.sum_le_sum; intro a _
      apply Finset.sum_le_sum; intro b _
      apply Finset.sum_le_sum; intro c _
      apply Finset.sum_le_sum; intro d _
      exact sum_primeProductCharacter_quartic_le_indicators p hc hodd (hB a) (hB b) (hB c) (hB d)
    _ = _ := by
      simp only [hf.eq_iff, ite_and, Finset.sum_add_distrib]
      simp [Finset.sum_ite_irrel, Finset.sum_const, nsmul_eq_mul]
      ring

lemma abs_primeProductCharacter_of_isUnit (x : ZMod (∏ i, p i)) (hx : IsUnit x) :
    |(primeProductCharacter p hc x : ℝ)| = 1 := by
  classical
  rw [primeProductCharacter, Int.cast_prod, Finset.abs_prod]
  apply Finset.prod_eq_one
  intro i _
  have hu : IsUnit (ZMod.prodEquivPi p hc x i) :=
    (hx.map (ZMod.prodEquivPi p hc).toMonoidHom).map (Pi.evalMonoidHom _ i)
  rcases quadraticChar_dichotomy hu.ne_zero with h | h <;> rw [h] <;> norm_num

lemma abs_primeProductCharacter_of_coprime (a : ℕ) (ha : a.Coprime (∏ i, p i)) :
    |(primeProductCharacter p hc (a : ZMod (∏ i, p i)) : ℝ)| = 1 :=
  abs_primeProductCharacter_of_isUnit p hc _ ((ZMod.isUnit_iff_coprime _ _).mpr ha)

/-- The fourth moment is unchanged by reversing every shift. -/
theorem primeProductCharacter_fourth_moment_Icc_le
    (hodd : ∀ i, p i ≠ 2) (B : ℕ) :
    (∑ x : ZMod (∏ i, p i),
      (∑ b ∈ Finset.Icc 1 B, (primeProductCharacter p hc (x + b) : ℝ)) ^ 4) ≤
      3 * (B : ℝ) ^ 2 * (∏ i, p i : ℕ) +
      (B : ℝ) ^ 4 *
        (3 ^ Fintype.card ι * Real.sqrt (∏ i, p i : ℕ) * Real.sqrt ((B : ℝ) ^ 3)) := by
  classical
  have hminus := primeProductCharacter_fourth_moment_le p hc
    (κ := ↥(Finset.Icc 1 B)) hodd B Subtype.val Subtype.val_injective
    (fun k ↦ (Finset.mem_Icc.mp k.property).2)
  simp only [Fintype.card_coe, Nat.card_Icc, Nat.add_sub_cancel] at hminus
  have hsubtype : ∀ x : ZMod (∏ i, p i),
      (∑ k : ↥(Finset.Icc 1 B), (primeProductCharacter p hc (x - (k.val : ℕ)) : ℝ)) =
        ∑ b ∈ Finset.Icc 1 B, (primeProductCharacter p hc (x - b) : ℝ) := by
    intro x
    exact Finset.sum_coe_sort (Finset.Icc 1 B)
      (fun b : ℕ ↦ (primeProductCharacter p hc (x - b) : ℝ))
  simp_rw [hsubtype] at hminus
  have hsign := abs_primeProductCharacter_of_isUnit p hc (-1) (isUnit_one.neg)
  have hsign4 : (primeProductCharacter p hc (-1) : ℝ) ^ 4 = 1 := by
    have h := congrArg (fun t : ℝ ↦ t ^ 4) hsign
    simpa only [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, one_pow] using h
  have hneg : ∀ x : ZMod (∏ i, p i),
      (∑ b ∈ Finset.Icc 1 B, (primeProductCharacter p hc ((-x) - b) : ℝ)) ^ 4 =
        (∑ b ∈ Finset.Icc 1 B, (primeProductCharacter p hc (x + b) : ℝ)) ^ 4 := by
    intro x
    have heq : ∀ b : ℕ, -x - (b : ZMod (∏ i, p i)) = -1 * (x + b) := by
      intro b; ring
    simp_rw [heq, primeProductCharacter_mul, Int.cast_mul]
    rw [← Finset.mul_sum, mul_pow, hsign4, one_mul]
  have hsum := Fintype.sum_equiv (Equiv.neg (ZMod (∏ i, p i)))
    (fun x ↦ (∑ b ∈ Finset.Icc 1 B, (primeProductCharacter p hc (x + b) : ℝ)) ^ 4)
    (fun x ↦ (∑ b ∈ Finset.Icc 1 B, (primeProductCharacter p hc (x - b) : ℝ)) ^ 4)
    (fun x ↦ (hneg x).symm)
  exact hsum.trans_le hminus

theorem primeProductCharacter_fourth_moment_short_le
    (hodd : ∀ i, p i ≠ 2) (B : ℕ) (hB : B ^ 7 ≤ ∏ i, p i) :
    (∑ x : ZMod (∏ i, p i),
      (∑ b ∈ Finset.Icc 1 B, (primeProductCharacter p hc (x + b) : ℝ)) ^ 4) ≤
      (3 + 3 ^ Fintype.card ι) * (B : ℝ) ^ 2 * (∏ i, p i : ℕ) := by
  have hsB := Real.sq_sqrt (show 0 ≤ (B : ℝ) ^ 3 by positivity)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ (∏ i, p i : ℕ) by positivity)
  have hBr : (B : ℝ) ^ 7 ≤ (∏ i, p i : ℕ) := by exact_mod_cast hB
  have hroot : (B : ℝ) ^ 2 * Real.sqrt ((B : ℝ) ^ 3) ≤
      Real.sqrt (∏ i, p i : ℕ) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, hsB, hsq]
    nlinarith [hBr]
  have hmain := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ 3 ^ Fintype.card ι * (B : ℝ) ^ 2 * Real.sqrt (∏ i, p i : ℕ) by positivity)
  have hid : Real.sqrt (∏ i, p i : ℕ) * Real.sqrt (∏ i, p i : ℕ) =
      (∏ i, p i : ℕ) := Real.mul_self_sqrt (by positivity)
  have hmain' : (B : ℝ) ^ 4 *
      (3 ^ Fintype.card ι * Real.sqrt (∏ i, p i : ℕ) * Real.sqrt ((B : ℝ) ^ 3)) ≤
        3 ^ Fintype.card ι * (B : ℝ) ^ 2 * (∏ i, p i : ℕ) := by
    calc
      _ = (3 ^ Fintype.card ι * (B : ℝ) ^ 2 * Real.sqrt (∏ i, p i : ℕ)) *
          ((B : ℝ) ^ 2 * Real.sqrt ((B : ℝ) ^ 3)) := by ring
      _ ≤ _ := by simpa only [mul_assoc, hid] using hmain
  have hmoment := primeProductCharacter_fourth_moment_Icc_le p hc hodd B
  nlinarith [hmoment, hmain']

end Erdos1141.CharacterSums
