import ErdosProblems.Erdos587.HooleyReflection

/-!
# Prime multiplication for Hooley moments

For a prime not dividing `n`, divisor windows split into the old window
and its translate by `log p`. Positive moments therefore at least double,
so the moment divided by the divisor count is nondecreasing.
-/

open MeasureTheory
open scoped BigOperators

namespace Erdos587

lemma deltaDivisors_prime_mul {p n : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    (u : ℝ) :
    deltaDivisors (p * n) u = deltaDivisors n u ∪
      (deltaDivisors n (u - Real.log p)).image (fun d => p * d) := by
  classical
  have hn : n ≠ 0 := by
    intro hn
    exact hpn (hn ▸ dvd_zero p)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  ext d
  constructor
  · intro hd
    obtain ⟨hdpn, _, hlow, hupp⟩ := mem_deltaDivisors.mp hd
    obtain ⟨e, f, hep, hfn, hef⟩ := exists_dvd_and_dvd_of_dvd_mul hdpn
    rcases (Nat.dvd_prime hp).mp hep with he | he
    · rw [he, one_mul] at hef
      rw [hef] at hlow hupp ⊢
      exact Finset.mem_union_left _ (mem_deltaDivisors.mpr ⟨hfn, hn, hlow, hupp⟩)
    · rw [he] at hef
      have hwindow := (exp_window_mul_iff hpR).mp
        (show Real.exp u < (p : ℝ) * f ∧
          (p : ℝ) * f ≤ Real.exp (u + 1) by
            simpa only [hef, Nat.cast_mul] using And.intro hlow hupp)
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨f, mem_deltaDivisors.mpr ⟨hfn, hn, hwindow.1, hwindow.2⟩, hef.symm⟩)
  · intro hd
    rcases Finset.mem_union.mp hd with hd | hd
    · obtain ⟨hdn, _, hlow, hupp⟩ := mem_deltaDivisors.mp hd
      exact mem_deltaDivisors.mpr
        ⟨hdn.trans (dvd_mul_left n p), mul_ne_zero hp.ne_zero hn, hlow, hupp⟩
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hd
      obtain ⟨hfn, _, hlow, hupp⟩ := mem_deltaDivisors.mp hf
      have hwindow := (exp_window_mul_iff hpR).mpr (And.intro hlow hupp)
      apply mem_deltaDivisors.mpr
      exact ⟨Nat.mul_dvd_mul_left p hfn, mul_ne_zero hp.ne_zero hn,
        by simpa only [Nat.cast_mul] using hwindow.1,
        by simpa only [Nat.cast_mul] using hwindow.2⟩

lemma deltaDivisors_prime_mul_disjoint {p n : ℕ} (hpn : ¬ p ∣ n) (u : ℝ) :
    Disjoint (deltaDivisors n u)
      ((deltaDivisors n (u - Real.log p)).image (fun d => p * d)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro d hd hpd
  obtain ⟨f, _, rfl⟩ := Finset.mem_image.mp hpd
  exact hpn ((dvd_mul_right p f).trans (mem_deltaDivisors.mp hd).1)

/-- The exact local recursion on adjoining a new prime factor. -/
theorem deltaCount_prime_mul {p n : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    (u : ℝ) :
    deltaCount (p * n) u = deltaCount n u + deltaCount n (u - Real.log p) := by
  classical
  unfold deltaCount
  rw [deltaDivisors_prime_mul hp hpn,
    Finset.card_union_of_disjoint (deltaDivisors_prime_mul_disjoint hpn u),
    Finset.card_image_of_injective _
      (fun _ _ h => mul_left_cancel₀ hp.ne_zero h), Nat.cast_add]

/-- Positive moments at least double when a new prime is adjoined. -/
theorem two_mul_deltaMoment_le_prime_mul {p n q : ℕ}
    (hp : p.Prime) (hpn : ¬ p ∣ n) (hq : q ≠ 0) :
    2 * deltaMoment n q ≤ deltaMoment (p * n) q := by
  have hi := integrable_deltaCount_pow (n := n) hq
  have his := hi.comp_sub_right (Real.log p)
  calc
    2 * deltaMoment n q =
        (∫ u : ℝ, deltaCount n u ^ q) +
          ∫ u : ℝ, deltaCount n (u - Real.log p) ^ q := by
      rw [integral_sub_right_eq_self (fun u : ℝ => deltaCount n u ^ q) (Real.log p)]
      simp only [deltaMoment, two_mul]
    _ = ∫ u : ℝ, deltaCount n u ^ q + deltaCount n (u - Real.log p) ^ q :=
      (integral_add hi his).symm
    _ ≤ deltaMoment (p * n) q := by
      apply integral_mono (hi.add his) (integrable_deltaCount_pow hq)
      intro u
      change deltaCount n u ^ q + deltaCount n (u - Real.log p) ^ q ≤
        deltaCount (p * n) u ^ q
      rw [deltaCount_prime_mul hp hpn]
      exact pow_add_pow_le (deltaCount_nonneg n u)
        (deltaCount_nonneg n (u - Real.log p)) hq

/-- The full binomial moment expansion on adjoining a new prime. -/
theorem deltaMoment_prime_mul {p n q : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n)
    (hq : q ≠ 0) :
    deltaMoment (p * n) q = ∑ a ∈ Finset.range (q + 1),
      (q.choose a : ℝ) * deltaMixedMoment n a (q - a) (Real.log p) := by
  have hi (a : ℕ) (ha : a ∈ Finset.range (q + 1)) :
      Integrable (fun u : ℝ =>
        deltaCount n u ^ a * deltaCount n (u - Real.log p) ^ (q - a) *
          (q.choose a : ℝ)) := by
    apply (integrable_deltaCount_mixed n a (q - a) (Real.log p) ?_).mul_const
    rw [Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp ha))]
    exact hq
  calc
    deltaMoment (p * n) q = ∫ u : ℝ, ∑ a ∈ Finset.range (q + 1),
        deltaCount n u ^ a * deltaCount n (u - Real.log p) ^ (q - a) *
          (q.choose a : ℝ) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      dsimp only
      rw [deltaCount_prime_mul hp hpn, add_pow]
    _ = ∑ a ∈ Finset.range (q + 1), ∫ u : ℝ,
        deltaCount n u ^ a * deltaCount n (u - Real.log p) ^ (q - a) *
          (q.choose a : ℝ) := integral_finsetSum _ hi
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [integral_mul_const]
      exact mul_comm _ _

/-- Separate the two extreme terms from the binomial expansion. -/
theorem deltaMoment_prime_mul_eq_two_mul_add {p n q : ℕ}
    (hp : p.Prime) (hpn : ¬ p ∣ n) (hq : q ≠ 0) :
    deltaMoment (p * n) q = 2 * deltaMoment n q +
      ∑ a ∈ Finset.Ico 1 q,
        (q.choose a : ℝ) * deltaMixedMoment n a (q - a) (Real.log p) := by
  rw [deltaMoment_prime_mul hp hpn hq, Finset.sum_range_succ,
    Finset.sum_range_eq_add_Ico _ (Nat.pos_of_ne_zero hq)]
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero,
    deltaMixedMoment_zero_left, one_mul, Nat.choose_self, Nat.sub_self,
    deltaMixedMoment_zero_right]
  ring

lemma card_divisors_prime_mul {p n : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    (p * n).divisors.card = 2 * n.divisors.card := by
  have h := deltaMoment_prime_mul (q := 1) hp hpn (by decide)
  norm_num [Finset.sum_range_succ, two_mul] at h
  rw [two_mul]
  exact_mod_cast h

/-- Dividing by the divisor count removes the doubling factor. -/
theorem normalized_deltaMoment_le_prime_mul {p n q : ℕ}
    (hp : p.Prime) (hpn : ¬ p ∣ n) (hq : q ≠ 0) :
    deltaMoment n q / n.divisors.card ≤
      deltaMoment (p * n) q / (p * n).divisors.card := by
  rw [card_divisors_prime_mul hp hpn, Nat.cast_mul, Nat.cast_ofNat]
  calc
    deltaMoment n q / (n.divisors.card : ℝ) =
        (2 * deltaMoment n q) / (2 * n.divisors.card) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (two_mul_deltaMoment_le_prime_mul hp hpn hq) (by positivity)

lemma sum_symmetric_Ico_le_twice {q : ℕ} (f : ℕ → ℝ)
    (hnonneg : ∀ a, 0 ≤ f a)
    (hsymm : ∀ a ∈ Finset.Ico 1 q, f a = f (q - a)) :
    (∑ a ∈ Finset.Ico 1 q, f a) ≤ 2 * ∑ a ∈ Finset.Icc 1 (q / 2), f a := by
  classical
  let S := (Finset.Ico 1 q).filter (fun a => ¬ a ≤ q / 2)
  have hlow : (Finset.Ico 1 q).filter (fun a => a ≤ q / 2) =
      Finset.Icc 1 (q / 2) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hinj : Set.InjOn (fun a => q - a) (S : Set ℕ) := by
    intro a ha b hb hab
    have ha' := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
    have hb' := Finset.mem_Ico.mp (Finset.mem_filter.mp hb).1
    change q - a = q - b at hab
    omega
  have hsub : S.image (fun a => q - a) ⊆ Finset.Icc 1 (q / 2) := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨ha, hhigh⟩ := Finset.mem_filter.mp ha
    have ha' := Finset.mem_Ico.mp ha
    apply Finset.mem_Icc.mpr
    omega
  have hhigh : (∑ a ∈ S, f a) ≤ ∑ a ∈ Finset.Icc 1 (q / 2), f a := by
    calc
      (∑ a ∈ S, f a) = ∑ a ∈ S, f (q - a) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hsymm a (Finset.mem_filter.mp ha).1
      _ = ∑ a ∈ S.image (fun a => q - a), f a := (Finset.sum_image hinj).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => hnonneg a)
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.Ico 1 q) (fun a => a ≤ q / 2) f
  rw [hlow] at hsplit
  change (∑ a ∈ Finset.Icc 1 (q / 2), f a) + (∑ a ∈ S, f a) = _ at hsplit
  linarith

/-- Reflection lets us use only the mixed terms with the smaller exponent
at most half the total order. -/
theorem deltaMoment_prime_mul_le_half_sum {p n q : ℕ}
    (hp : p.Prime) (hpn : ¬ p ∣ n) (hq : q ≠ 0) :
    deltaMoment (p * n) q ≤ 2 * deltaMoment n q +
      2 * ∑ b ∈ Finset.Icc 1 (q / 2),
        (q.choose b : ℝ) * deltaMixedMoment n (q - b) b (Real.log p) := by
  rw [deltaMoment_prime_mul_eq_two_mul_add hp hpn hq]
  apply add_le_add le_rfl
  have hs := sum_symmetric_Ico_le_twice (q := q)
    (fun a => (q.choose a : ℝ) * deltaMixedMoment n a (q - a) (Real.log p))
    (fun a => mul_nonneg (Nat.cast_nonneg _) (deltaMixedMoment_nonneg _ _ _ _))
    (by
      intro a ha
      have haq := (Finset.mem_Ico.mp ha).2.le
      rw [Nat.choose_symm haq, Nat.sub_sub_self haq, deltaMixedMoment_symm n a])
  apply hs.trans_eq
  apply congrArg (fun x : ℝ => 2 * x)
  apply Finset.sum_congr rfl
  intro b hb
  rw [deltaMixedMoment_symm n b]

/-- The normalized prime recursion used in the restricted moment sums. -/
theorem normalized_deltaMoment_prime_mul_le {p n q : ℕ}
    (hp : p.Prime) (hpn : ¬ p ∣ n) (hq : q ≠ 0) :
    deltaMoment (p * n) q / (p * n).divisors.card ≤
      deltaMoment n q / n.divisors.card +
        (∑ b ∈ Finset.Icc 1 (q / 2),
          (q.choose b : ℝ) * deltaMixedMoment n (q - b) b (Real.log p)) /
            n.divisors.card := by
  rw [card_divisors_prime_mul hp hpn, Nat.cast_mul, Nat.cast_ofNat]
  calc
    deltaMoment (p * n) q / (2 * n.divisors.card) ≤
        (2 * deltaMoment n q +
          2 * ∑ b ∈ Finset.Icc 1 (q / 2),
            (q.choose b : ℝ) * deltaMixedMoment n (q - b) b (Real.log p)) /
              (2 * n.divisors.card) :=
      div_le_div_of_nonneg_right (deltaMoment_prime_mul_le_half_sum hp hpn hq)
        (by positivity)
    _ = _ := by ring

lemma normalized_deltaMoment_le_mul_of_squarefree {a b q : ℕ}
    (hq : q ≠ 0) (hsf : Squarefree (a * b)) :
    deltaMoment a q / a.divisors.card ≤
      deltaMoment (a * b) q / (a * b).divisors.card := by
  induction b using induction_on_primes with
  | zero => simp at hsf
  | one => simp
  | prime_mul p b hp ih =>
    have hsf' : Squarefree (p * (a * b)) := by
      simpa only [mul_left_comm a p b] using hsf
    have hcop : p.Coprime (a * b) := Nat.coprime_of_squarefree_mul hsf'
    have hpn : ¬ p ∣ a * b := hp.coprime_iff_not_dvd.mp hcop
    have hle := (ih hsf'.of_mul_right).trans
      (normalized_deltaMoment_le_prime_mul hp hpn hq)
    simpa only [mul_left_comm a p b] using hle

/-- For squarefree integers, normalized moments increase under divisibility.
Consequently all lower-moment constraints are preserved by prime truncation. -/
theorem normalized_deltaMoment_le_of_dvd {m n q : ℕ}
    (hn : Squarefree n) (hmn : m ∣ n) (hq : q ≠ 0) :
    deltaMoment m q / m.divisors.card ≤ deltaMoment n q / n.divisors.card := by
  obtain ⟨b, rfl⟩ := hmn
  exact normalized_deltaMoment_le_mul_of_squarefree hq hn

end Erdos587
