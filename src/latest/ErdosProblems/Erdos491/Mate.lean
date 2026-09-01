import Mathlib

open scoped BigOperators

namespace Erdos491MateScratch

/-- Additivity on coprime positive integers (the value at zero is irrelevant). -/
def CoprimeAdditive (f : ℕ → ℝ) : Prop :=
  ∀ ⦃a b : ℕ⦄, 1 ≤ a → 1 ≤ b → a.Coprime b → f (a * b) = f a + f b

/-- The geometric sum `1 + n + ... + n^j`, in a recursion convenient for Máté's proof. -/
def geom (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | j + 1 => n * geom n j + 1

@[simp] lemma geom_zero (n : ℕ) : geom n 0 = 1 := rfl

@[simp] lemma geom_succ (n j : ℕ) : geom n (j + 1) = n * geom n j + 1 := rfl

lemma geom_pos (n j : ℕ) : 1 ≤ geom n j := by
  induction j with
  | zero => simp
  | succ j ih => simp only [geom_succ]; omega

lemma geom_modEq_succ (n j : ℕ) (hn : 1 ≤ n) :
    geom n j ≡ j + 1 [MOD n - 1] := by
  have hnmod : n ≡ 1 [MOD n - 1] := by
    exact ((Nat.modEq_iff_dvd' hn).2 dvd_rfl).symm
  induction j with
  | zero => exact Nat.ModEq.refl 1
  | succ j ih =>
      simpa [Nat.succ_eq_add_one, add_assoc] using
        (hnmod.mul ih).add (Nat.ModEq.refl 1)

lemma geom_coprime_left (n j : ℕ) : n.Coprime (geom n j) := by
  induction j with
  | zero => simp
  | succ j ih => simp [geom_succ]

lemma geom_mul_pred_add_one_aux (n j : ℕ) (hn : 1 ≤ n) :
    (n - 1) * geom n j + 1 = n ^ (j + 1) := by
  induction j with
  | zero => simp [geom, Nat.sub_add_cancel hn]
  | succ j ih =>
      simp only [geom_succ]
      rw [Nat.pow_succ, ← ih]
      have hn' : n - 1 + 1 = n := Nat.sub_add_cancel hn
      calc
        (n - 1) * (n * geom n j + 1) + 1 =
            (n - 1) * n * geom n j + ((n - 1) + 1) := by ring
        _ = (n - 1) * n * geom n j + n := by rw [hn']
        _ = ((n - 1) * geom n j + 1) * n := by ring

lemma geom_mul_pred_add_one (n s : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s) :
    (n - 1) * geom n (s - 1) + 1 = n ^ s := by
  simpa [Nat.sub_add_cancel hs] using geom_mul_pred_add_one_aux n (s - 1) hn

lemma geom_pred_mul (n s : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s) :
    (n - 1) * geom n (s - 1) = n ^ s - 1 := by
  have h := geom_mul_pred_add_one n s hn hs
  omega

lemma geom_coprime_pred (n s : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s)
    (hcop : s.Coprime (n - 1)) : (n - 1).Coprime (geom n (s - 1)) := by
  rw [Nat.Coprime, Nat.gcd_rec]
  have hmod := geom_modEq_succ n (s - 1) hn
  rw [Nat.sub_add_cancel hs] at hmod
  rw [hmod]
  rw [← Nat.gcd_rec]
  exact hcop.symm.gcd_eq_one

variable {f : ℕ → ℝ} {M : ℝ}

lemma value_one (hf : CoprimeAdditive f) : f 1 = 0 := by
  have h := hf (a := 1) (b := 1) (by omega) (by omega) (by simp)
  norm_num at h ⊢
  linarith

lemma gap_telescoping
    (hgap : ∀ n : ℕ, 1 ≤ n → |f (n + 1) - f n| ≤ M)
    (a d : ℕ) (ha : 1 ≤ a) :
    |f (a + d) - f a| ≤ (d : ℝ) * M := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hg := hgap (a + d) (by omega)
      have heq : f (a + (d + 1)) - f a =
          (f (a + d + 1) - f (a + d)) + (f (a + d) - f a) := by ring
      rw [heq]
      calc
        |(f (a + d + 1) - f (a + d)) + (f (a + d) - f a)|
            ≤ |f (a + d + 1) - f (a + d)| + |f (a + d) - f a| := abs_add_le _ _
        _ ≤ M + (d : ℝ) * M := add_le_add hg ih
        _ = ((d + 1 : ℕ) : ℝ) * M := by push_cast; ring

lemma geom_estimate
    (hf : CoprimeAdditive f)
    (hgap : ∀ n : ℕ, 1 ≤ n → |f (n + 1) - f n| ≤ M)
    (n j : ℕ) (hn : 1 ≤ n) :
    |f (geom n j) - (j : ℝ) * f n| ≤ (j : ℝ) * M := by
  induction j with
  | zero => simp [geom, value_one hf]
  | succ j ih =>
      have hcop := geom_coprime_left n j
      have hadd := hf hn (geom_pos n j) hcop
      have hg := hgap (n * geom n j) (Nat.mul_pos hn (geom_pos n j))
      have heq : f (geom n (j + 1)) - ((j + 1 : ℕ) : ℝ) * f n =
          (f (n * geom n j + 1) - f (n * geom n j)) +
            (f (geom n j) - (j : ℝ) * f n) := by
        rw [geom_succ, hadd]
        push_cast
        ring
      rw [heq]
      calc
        |(f (n * geom n j + 1) - f (n * geom n j)) +
            (f (geom n j) - (j : ℝ) * f n)|
            ≤ |f (n * geom n j + 1) - f (n * geom n j)| +
                |f (geom n j) - (j : ℝ) * f n| := abs_add_le _ _
        _ ≤ M + (j : ℝ) * M := add_le_add hg ih
        _ = ((j + 1 : ℕ) : ℝ) * M := by push_cast; ring

/-- Máté's first elementary estimate. -/
lemma mate1
    (hf : CoprimeAdditive f)
    (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, 1 ≤ n → |f (n + 1) - f n| ≤ M)
    (n s : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s) (hcop : s.Coprime (n - 1)) :
    |f (n ^ s) - (s : ℝ) * f n| ≤ 2 * (s : ℝ) * M := by
  by_cases hn1 : n = 1
  · subst n
    rw [one_pow, value_one hf]
    simp only [mul_zero, sub_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg s)) hM
  · have hn2 : 2 ≤ n := by omega
    let G := geom n (s - 1)
    have hGpos : 1 ≤ G := geom_pos n (s - 1)
    have hprepos : 1 ≤ n - 1 := by omega
    have hpowpos : 1 ≤ n ^ s - 1 := by
      have : 2 ≤ n ^ s := by
        exact (Nat.one_lt_pow_iff (by omega : s ≠ 0)).2 hn2
      omega
    have hmul : (n - 1) * G = n ^ s - 1 := geom_pred_mul n s hn hs
    have hGcop : (n - 1).Coprime G := geom_coprime_pred n s hn hs hcop
    have hadd : f (n ^ s - 1) = f (n - 1) + f G := by
      rw [← hmul]
      exact hf hprepos hGpos hGcop
    have htop := hgap (n ^ s - 1) hpowpos
    have hbot := hgap (n - 1) hprepos
    have hgeom := geom_estimate hf hgap n (s - 1) hn
    have heq : f (n ^ s) - (s : ℝ) * f n =
        (f (n ^ s) - f (n ^ s - 1)) + (f (n - 1) - f n) +
          (f G - ((s - 1 : ℕ) : ℝ) * f n) := by
      rw [hadd]
      push_cast [Nat.cast_sub hs]
      ring
    rw [heq]
    calc
      |(f (n ^ s) - f (n ^ s - 1)) + (f (n - 1) - f n) +
          (f G - ((s - 1 : ℕ) : ℝ) * f n)|
          ≤ |f (n ^ s) - f (n ^ s - 1)| + |f (n - 1) - f n| +
              |f G - ((s - 1 : ℕ) : ℝ) * f n| := by
            exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ M + M + ((s - 1 : ℕ) : ℝ) * M := by
        have htop' : |f (n ^ s) - f (n ^ s - 1)| ≤ M := by
          have hp : 1 ≤ n ^ s := Nat.pow_pos (by omega)
          rw [Nat.sub_add_cancel hp] at htop
          exact htop
        have hbot' : |f (n - 1) - f n| ≤ M := by
          rw [abs_sub_comm]
          simpa [Nat.sub_add_cancel hn] using hbot
        exact add_le_add (add_le_add htop' hbot') hgeom
      _ ≤ 2 * (s : ℝ) * M := by
        rw [Nat.cast_sub hs]
        push_cast
        nlinarith [show (1 : ℝ) ≤ s by exact_mod_cast hs]

lemma mate2_even
    (hf : CoprimeAdditive f)
    (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, 1 ≤ n → |f (n + 1) - f n| ≤ M)
    (n k : ℕ) (hn : 1 ≤ n) (heven : Even n) :
    |f (n ^ (2 ^ k)) - ((2 ^ k : ℕ) : ℝ) * f n| ≤
      2 * ((2 ^ k : ℕ) : ℝ) * M := by
  have hodd : Odd (n - 1) := by
    obtain ⟨r, hr⟩ := heven
    have hrpos : 1 ≤ r := by omega
    refine ⟨r - 1, ?_⟩
    omega
  have hcop2 : (2 : ℕ).Coprime (n - 1) := Nat.coprime_two_left.2 hodd
  have hcop : (2 ^ k).Coprime (n - 1) := hcop2.pow_left k
  exact mate1 hf hM hgap n (2 ^ k) hn (Nat.pow_pos (by omega)) hcop

/-- Máté's dyadic estimate. -/
lemma mate2
    (hf : CoprimeAdditive f)
    (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, 1 ≤ n → |f (n + 1) - f n| ≤ M)
    (n k : ℕ) (hn : 1 ≤ n) :
    |f (n ^ (2 ^ k)) - ((2 ^ k : ℕ) : ℝ) * f n| ≤
      4 * ((2 ^ k : ℕ) : ℝ) * M := by
  by_cases heven : Even n
  · apply (mate2_even hf hM hgap n k hn heven).trans
    have hk0 : (0 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by positivity
    nlinarith
  · have hodd : Odd n := Nat.not_even_iff_odd.mp heven
    have hcop : (2 : ℕ).Coprime n := Nat.coprime_two_left.2 hodd
    have hcopPow : (2 ^ (2 ^ k)).Coprime (n ^ (2 ^ k)) := hcop.pow _ _
    have h2n := mate2_even hf hM hgap (2 * n) k (by omega) (by simp)
    have h2 := mate2_even hf hM hgap 2 k (by omega) (by simp)
    have haddBase : f (2 * n) = f 2 + f n := hf (by omega) hn hcop
    have haddPow : f ((2 * n) ^ (2 ^ k)) =
        f (2 ^ (2 ^ k)) + f (n ^ (2 ^ k)) := by
      rw [mul_pow]
      exact hf (Nat.pow_pos (by omega)) (Nat.pow_pos hn) hcopPow
    have heq : f (n ^ (2 ^ k)) - ((2 ^ k : ℕ) : ℝ) * f n =
        (f ((2 * n) ^ (2 ^ k)) - ((2 ^ k : ℕ) : ℝ) * f (2 * n)) -
          (f (2 ^ (2 ^ k)) - ((2 ^ k : ℕ) : ℝ) * f 2) := by
      rw [haddBase, haddPow]
      ring
    rw [heq]
    calc
      |(f ((2 * n) ^ (2 ^ k)) - ((2 ^ k : ℕ) : ℝ) * f (2 * n)) -
          (f (2 ^ (2 ^ k)) - ((2 ^ k : ℕ) : ℝ) * f 2)|
          ≤ |f ((2 * n) ^ (2 ^ k)) - ((2 ^ k : ℕ) : ℝ) * f (2 * n)| +
              |f (2 ^ (2 ^ k)) - ((2 ^ k : ℕ) : ℝ) * f 2| := abs_sub _ _
      _ ≤ (2 * ((2 ^ k : ℕ) : ℝ) * M) + (2 * ((2 ^ k : ℕ) : ℝ) * M) :=
        add_le_add h2n h2
      _ = 4 * ((2 ^ k : ℕ) : ℝ) * M := by ring

lemma power_coprime_pred (n i : ℕ) (hn : 1 ≤ n) (hi : 1 ≤ i) :
    n.Coprime (n ^ i - 1) := by
  have hpow : 1 ≤ n ^ i := Nat.pow_pos hn
  have hadj : (n ^ i).Coprime (n ^ i - 1) := by
    have hadj' : (n ^ i - 1).Coprime (n ^ i) := by
      rw [← Nat.coprime_sub_self_right (m := n ^ i - 1) (n := n ^ i) (Nat.sub_le _ _)]
      simp [Nat.sub_sub_self hpow]
    exact hadj'.symm
  apply hadj.of_dvd_left
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hi
  simp

lemma value_bound
    (hf : CoprimeAdditive f)
    (hgap : ∀ n : ℕ, 1 ≤ n → |f (n + 1) - f n| ≤ M)
    (n : ℕ) (hn : 1 ≤ n) :
    |f n| ≤ ((n - 1 : ℕ) : ℝ) * M := by
  have h := gap_telescoping hgap 1 (n - 1) (by omega)
  simpa [Nat.add_sub_of_le hn, value_one hf] using h

lemma power_step
    (hf : CoprimeAdditive f)
    (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, 1 ≤ n → |f (n + 1) - f n| ≤ M)
    (n i : ℕ) (hn : 2 ≤ n) (hi : 1 ≤ i) :
    |f (n ^ (i + 1)) - f (n ^ i)| ≤ 4 * (n : ℝ) * M := by
  have hnpos : 1 ≤ n := by omega
  have hpowip : 1 ≤ n ^ i - 1 := by
    have : 2 ≤ n ^ i := (Nat.one_lt_pow_iff (by omega : i ≠ 0)).2 hn
    omega
  have hbig : 1 ≤ n ^ (i + 1) - n := by
    have hnle : n ≤ (n ^ i - 1) * n := Nat.le_mul_of_pos_left n hpowip
    have heq : (n ^ i - 1) * n = n ^ (i + 1) - n := by
      rw [Nat.sub_mul, Nat.pow_succ]
      simp
    rw [← heq]
    omega
  have hident : n * (n ^ i - 1) = n ^ (i + 1) - n := by
    rw [Nat.mul_sub, Nat.pow_succ]
    simp [mul_comm]
  have hadd : f (n ^ (i + 1) - n) = f n + f (n ^ i - 1) := by
    rw [← hident]
    exact hf hnpos hpowip (power_coprime_pred n i hnpos hi)
  have htop := gap_telescoping hgap (n ^ (i + 1) - n) n hbig
  have htop' : |f (n ^ (i + 1)) - f (n ^ (i + 1) - n)| ≤ (n : ℝ) * M := by
    have hle : n ≤ n ^ (i + 1) := Nat.le_pow (by omega)
    rw [Nat.sub_add_cancel hle] at htop
    exact htop
  have hbot := hgap (n ^ i - 1) hpowip
  have hbot' : |f (n ^ i - 1) - f (n ^ i)| ≤ M := by
    rw [abs_sub_comm]
    have hp : 1 ≤ n ^ i := Nat.pow_pos hnpos
    rw [Nat.sub_add_cancel hp] at hbot
    exact hbot
  have hnval := value_bound hf hgap n hnpos
  have heq : f (n ^ (i + 1)) - f (n ^ i) =
      (f (n ^ (i + 1)) - f (n ^ (i + 1) - n)) + f n +
        (f (n ^ i - 1) - f (n ^ i)) := by
    rw [hadd]
    ring
  rw [heq]
  calc
    |(f (n ^ (i + 1)) - f (n ^ (i + 1) - n)) + f n +
        (f (n ^ i - 1) - f (n ^ i))|
        ≤ |f (n ^ (i + 1)) - f (n ^ (i + 1) - n)| + |f n| +
            |f (n ^ i - 1) - f (n ^ i)| := by
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (n : ℝ) * M + ((n - 1 : ℕ) : ℝ) * M + M :=
      add_le_add (add_le_add htop' hnval) hbot'
    _ ≤ 4 * (n : ℝ) * M := by
      rw [Nat.cast_sub hnpos]
      push_cast
      nlinarith [show (2 : ℝ) ≤ n by exact_mod_cast hn]

lemma power_telescoping
    (hf : CoprimeAdditive f)
    (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, 1 ≤ n → |f (n + 1) - f n| ≤ M)
    (n s d : ℕ) (hn : 2 ≤ n) (hs : 1 ≤ s) :
    |f (n ^ (s + d)) - f (n ^ s)| ≤
      (d : ℝ) * (4 * (n : ℝ) * M) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hstep := power_step hf hM hgap n (s + d) hn (by omega)
      have heq : f (n ^ (s + (d + 1))) - f (n ^ s) =
          (f (n ^ ((s + d) + 1)) - f (n ^ (s + d))) +
            (f (n ^ (s + d)) - f (n ^ s)) := by ring
      rw [heq]
      calc
        |(f (n ^ (s + d + 1)) - f (n ^ (s + d))) +
            (f (n ^ (s + d)) - f (n ^ s))|
            ≤ |f (n ^ (s + d + 1)) - f (n ^ (s + d))| +
                |f (n ^ (s + d)) - f (n ^ s)| := abs_add_le _ _
        _ ≤ 4 * (n : ℝ) * M + (d : ℝ) * (4 * (n : ℝ) * M) :=
          add_le_add hstep ih
        _ = ((d + 1 : ℕ) : ℝ) * (4 * (n : ℝ) * M) := by push_cast; ring

/-- Máté's third elementary estimate. -/
lemma mate3
    (hf : CoprimeAdditive f)
    (hM : 0 ≤ M)
    (hgap : ∀ n : ℕ, 1 ≤ n → |f (n + 1) - f n| ≤ M)
    (n s t : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    |f (n ^ t) - f (n ^ s)| ≤
      4 * (Nat.dist t s : ℝ) * (n : ℝ) * M := by
  by_cases hn1 : n = 1
  · subst n
    simp only [one_pow, sub_self, abs_zero, Nat.cast_one, mul_one]
    positivity
  · have hn2 : 2 ≤ n := by omega
    rcases le_total s t with hst | hts
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
      have h := power_telescoping hf hM hgap n s d hn2 hs
      rw [Nat.dist_eq_sub_of_le_right (Nat.le_add_right s d), Nat.add_sub_cancel_left]
      convert h using 1
      all_goals ring
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hts
      have h := power_telescoping hf hM hgap n t d hn2 ht
      rw [abs_sub_comm]
      rw [Nat.dist_eq_sub_of_le (Nat.le_add_right t d), Nat.add_sub_cancel_left]
      convert h using 1
      all_goals ring

end Erdos491MateScratch
