import ErdosProblems.Erdos250.Erdos250RatFrac
import ErdosProblems.Erdos250.Erdos250Arithmetic

open scoped BigOperators

namespace ZV

lemma prod_range_reverse_Icc {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∏ i ∈ Finset.range n, f (n - i) = ∏ r ∈ Finset.Icc 1 n, f r := by
  apply Finset.prod_bij (fun i _ ↦ n - i)
  · intro i hi
    rw [Finset.mem_Icc]
    have hil : i < n := Finset.mem_range.mp hi
    omega
  · intro i₁ hi₁ i₂ hi₂ heq
    have h₁ : i₁ < n := Finset.mem_range.mp hi₁
    have h₂ : i₂ < n := Finset.mem_range.mp hi₂
    omega
  · intro r hr
    rw [Finset.mem_Icc] at hr
    refine ⟨n - r, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro i hi
    rfl

lemma numerator_prod_closed (n k : ℕ) :
    (∏ i ∈ Finset.range n,
      (1 - (2 : ℚ) ^ (n - 1 - i) * DoublePartialFraction.OldRational.root k)) =
      (-1 : ℚ) ^ n * (Erdos250Arithmetic.highProd k n : ℚ) := by
  calc
    _ = ∏ i ∈ Finset.range n,
        (-((Erdos250Arithmetic.oddFactor (k + (n - i)) : ℕ) : ℚ)) := by
          apply Finset.prod_congr rfl
          intro i hi
          have hin : i < n := Finset.mem_range.mp hi
          rw [DoublePartialFraction.OldRational.root, ← pow_add]
          have he : n - 1 - i + (k + 1) = k + (n - i) := by omega
          rw [he]
          simp only [Erdos250Arithmetic.oddFactor]
          have hp : 1 ≤ 2 ^ (k + (n - i)) := one_le_pow₀ (by omega)
          push_cast
          rw [Nat.cast_sub hp]
          norm_num only [Nat.cast_pow, Nat.cast_ofNat]
          ring
    _ = (-1 : ℚ) ^ n *
        ∏ i ∈ Finset.range n, (Erdos250Arithmetic.oddFactor (k + (n - i)) : ℚ) := by
          rw [Finset.prod_neg, Finset.card_range]
    _ = (-1 : ℚ) ^ n *
        ∏ r ∈ Finset.Icc 1 n, (Erdos250Arithmetic.oddFactor (k + r) : ℚ) := by
          rw [prod_range_reverse_Icc (fun r ↦ (Erdos250Arithmetic.oddFactor (k + r) : ℚ)) n]
    _ = _ := by simp only [Erdos250Arithmetic.highProd, Nat.cast_prod]

lemma denProd_add (a b : ℕ) :
    Erdos250Arithmetic.denProd (a + b) = Erdos250Arithmetic.denProd a * Erdos250Arithmetic.highProd a b := by
  induction b with
  | zero => simp [Erdos250Arithmetic.denProd, Erdos250Arithmetic.highProd]
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega, Erdos250Arithmetic.denProd_succ,
        Erdos250Arithmetic.highProd_succ_right, ih]
      ring

lemma denProd_pos (n : ℕ) : 0 < Erdos250Arithmetic.denProd n := by
  apply Finset.prod_pos
  intro d hd
  rw [Finset.mem_Icc] at hd
  exact Nat.sub_pos_of_lt (one_lt_pow' (by omega) (by omega))

lemma gauss2_cast_eq_ratio {n k : ℕ} (hk : k ≤ n) :
    (Erdos250Arithmetic.gauss2 n k : ℚ) =
      (Erdos250Arithmetic.denProd n : ℚ) /
        ((Erdos250Arithmetic.denProd (n - k) : ℚ) * (Erdos250Arithmetic.denProd k : ℚ)) := by
  have hp := Erdos250Arithmetic.gauss2_mul_denProd_eq_highProd (n - k) k
  have hadd : n - k + k = n := Nat.sub_add_cancel hk
  rw [hadd] at hp
  have hden := denProd_add (n - k) k
  rw [hadd] at hden
  have hdk : (Erdos250Arithmetic.denProd k : ℚ) ≠ 0 := by exact_mod_cast (denProd_pos k).ne'
  have hdsub : (Erdos250Arithmetic.denProd (n - k) : ℚ) ≠ 0 := by
    exact_mod_cast (denProd_pos (n - k)).ne'
  have hpq : (Erdos250Arithmetic.gauss2 n k : ℚ) * Erdos250Arithmetic.denProd k =
      Erdos250Arithmetic.highProd (n - k) k := by exact_mod_cast hp
  have hdenq : (Erdos250Arithmetic.denProd n : ℚ) =
      Erdos250Arithmetic.denProd (n - k) * Erdos250Arithmetic.highProd (n - k) k := by
    exact_mod_cast hden
  rw [hdenq]
  field_simp [hdk, hdsub]
  nlinarith

lemma gauss2_add_cast_eq_ratio (n k : ℕ) :
    (Erdos250Arithmetic.gauss2 (n + k) k : ℚ) =
      (Erdos250Arithmetic.denProd (n + k) : ℚ) /
        ((Erdos250Arithmetic.denProd n : ℚ) * (Erdos250Arithmetic.denProd k : ℚ)) := by
  simpa using gauss2_cast_eq_ratio (n := n + k) (k := k) (by omega)

/-- The odd-product part of the double-pole residue is the Gaussian product. -/
lemma gaussian_odd_identity {n k : ℕ} (hk : k ≤ n) :
    (Erdos250Arithmetic.denProd n : ℚ) * (Erdos250Arithmetic.highProd k n : ℚ) /
        ((Erdos250Arithmetic.denProd k : ℚ) ^ 2 * (Erdos250Arithmetic.denProd (n - k) : ℚ) ^ 2) =
      (Erdos250Arithmetic.gauss2 n k : ℚ) ^ 2 * Erdos250Arithmetic.gauss2 (n + k) k := by
  have hdk : (Erdos250Arithmetic.denProd k : ℚ) ≠ 0 := by exact_mod_cast (denProd_pos k).ne'
  have hdn : (Erdos250Arithmetic.denProd n : ℚ) ≠ 0 := by exact_mod_cast (denProd_pos n).ne'
  have hdsub : (Erdos250Arithmetic.denProd (n - k) : ℚ) ≠ 0 := by
    exact_mod_cast (denProd_pos (n - k)).ne'
  have hhigh : (Erdos250Arithmetic.highProd k n : ℚ) =
      Erdos250Arithmetic.denProd (k + n) / Erdos250Arithmetic.denProd k := by
    have h := denProd_add k n
    have hq : (Erdos250Arithmetic.denProd k : ℚ) *
        Erdos250Arithmetic.highProd k n = Erdos250Arithmetic.denProd (k + n) := by
      exact_mod_cast h.symm
    exact (eq_div_iff hdk).2 (by simpa [mul_comm] using hq)
  rw [hhigh, gauss2_cast_eq_ratio hk, gauss2_add_cast_eq_ratio]
  rw [show k + n = n + k by omega]
  field_simp

end ZV
