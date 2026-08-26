import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped BigOperators

namespace Erdos
namespace Problem520

lemma cast_choose_succ_right {n k : ℕ} :
    ((n.choose (k + 1) : ℕ) : ℝ) =
      (n.choose k : ℝ) * (n - k : ℕ) / (k + 1 : ℕ) := by
  have h := Nat.choose_succ_right_eq n k
  apply (eq_div_iff (by positivity : ((k + 1 : ℕ) : ℝ) ≠ 0)).2
  exact_mod_cast h

lemma choose_even_le (r k : ℕ) (hk : k ≤ r) :
    ((Nat.choose (2 * r) (2 * k) : ℕ) : ℝ) ≤
      (Nat.choose r k : ℝ) * (2 * r - 1 : ℕ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hkr : k ≤ r := le_trans (Nat.le_succ k) hk
      have hklt : k < r := Nat.lt_of_succ_le hk
      have h2k : 2 * k ≤ 2 * r := Nat.mul_le_mul_left 2 hkr
      have h2ks : 2 * k + 1 ≤ 2 * r := by omega
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega,
        cast_choose_succ_right (n := 2 * r) (k := 2 * k + 1),
        cast_choose_succ_right (n := 2 * r) (k := 2 * k),
        cast_choose_succ_right (n := r) (k := k),
        pow_succ]
      push_cast
      rw [Nat.cast_sub h2k, Nat.cast_sub h2ks, Nat.cast_sub hklt.le]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      have ih' := ih hkr
      have hdodd : 0 < (2 * (k : ℝ) + 1) := by positivity
      have hdeven : 0 < (2 * (k : ℝ) + 2) := by positivity
      have hdk : 0 < ((k : ℝ) + 1) := by positivity
      have hx : 0 ≤ (r : ℝ) - k := sub_nonneg.mpr (by exact_mod_cast hkr)
      have hy : 0 ≤ (2 * r : ℝ) - (2 * k + 1) :=
        sub_nonneg.mpr (by exact_mod_cast h2ks)
      have hx2 : 0 ≤ (2 * r : ℝ) - 2 * k := by nlinarith
      have hfac_nonneg :
          0 ≤ ((2 * r : ℝ) - 2 * k) / (2 * k + 1) *
              (((2 * r : ℝ) - (2 * k + 1)) / (2 * k + 2)) :=
        mul_nonneg (div_nonneg hx2 hdodd.le) (div_nonneg hy hdeven.le)
      have hfactor :
          ((2 * r : ℝ) - 2 * k) / (2 * k + 1) *
              (((2 * r : ℝ) - (2 * k + 1)) / (2 * k + 2)) =
            ((r : ℝ) - k) / (k + 1) *
              (((2 * r : ℝ) - (2 * k + 1)) / (2 * k + 1)) := by
        field_simp
      have hodd :
          ((2 * r : ℝ) - (2 * k + 1)) / (2 * k + 1) ≤
            ((2 * r - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * r)]
        apply (div_le_iff₀ hdodd).2
        push_cast
        nlinarith
      have hfac_le :
          ((2 * r : ℝ) - 2 * k) / (2 * k + 1) *
              (((2 * r : ℝ) - (2 * k + 1)) / (2 * k + 2)) ≤
            ((r : ℝ) - k) / (k + 1) * ((2 * r - 1 : ℕ) : ℝ) := by
        rw [hfactor]
        exact mul_le_mul_of_nonneg_left hodd (div_nonneg hx hdk.le)
      rw [show (2 * (k : ℝ) + 1 + 1) = 2 * k + 2 by ring]
      calc
        (Nat.choose (2 * r) (2 * k) : ℝ) * ((2 * r : ℝ) - 2 * k) /
              (2 * k + 1) * ((2 * r : ℝ) - (2 * k + 1)) / (2 * k + 2) =
            (Nat.choose (2 * r) (2 * k) : ℝ) *
              (((2 * r : ℝ) - 2 * k) / (2 * k + 1) *
                (((2 * r : ℝ) - (2 * k + 1)) / (2 * k + 2))) := by ring
        _ ≤ ((Nat.choose r k : ℝ) * ((2 * r - 1 : ℕ) : ℝ) ^ k) *
              (((2 * r : ℝ) - 2 * k) / (2 * k + 1) *
                (((2 * r : ℝ) - (2 * k + 1)) / (2 * k + 2))) :=
          mul_le_mul_of_nonneg_right ih' hfac_nonneg
        _ ≤ ((Nat.choose r k : ℝ) * ((2 * r - 1 : ℕ) : ℝ) ^ k) *
              (((r : ℝ) - k) / (k + 1) * ((2 * r - 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hfac_le (by positivity)
        _ = (Nat.choose r k : ℝ) * ((r : ℝ) - k) / (k + 1) *
              (((2 * r - 1 : ℕ) : ℝ) ^ k * ((2 * r - 1 : ℕ) : ℝ)) := by ring

lemma average_signed_binomial_term (a b : ℝ) (n m : ℕ) :
    (b ^ m * a ^ (n - m) * (n.choose m : ℝ) +
          (-b) ^ m * a ^ (n - m) * (n.choose m : ℝ)) / 2 =
      if Even m then b ^ m * a ^ (n - m) * (n.choose m : ℝ) else 0 := by
  by_cases hm : Even m
  · rw [if_pos hm, hm.neg_pow]
    ring
  · have hm' : Odd m := Nat.not_even_iff_odd.mp hm
    rw [if_neg hm, hm'.neg_pow]
    ring

lemma average_even_powers_eq_sum (a b : ℝ) (r : ℕ) :
    ((a + b) ^ (2 * r) + (a - b) ^ (2 * r)) / 2 =
      ∑ k ∈ Finset.range (r + 1),
        b ^ (2 * k) * a ^ (2 * r - 2 * k) * ((2 * r).choose (2 * k) : ℝ) := by
  rw [show a + b = b + a by ring, show a - b = -b + a by ring, add_pow, add_pow]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  calc
    (∑ m ∈ Finset.range (2 * r + 1),
        (b ^ m * a ^ (2 * r - m) * ((2 * r).choose m : ℝ) +
          (-b) ^ m * a ^ (2 * r - m) * ((2 * r).choose m : ℝ)) / 2) =
      ∑ m ∈ Finset.range (2 * r + 1),
        if Even m then
          b ^ m * a ^ (2 * r - m) * ((2 * r).choose m : ℝ)
        else 0 := by
          apply Finset.sum_congr rfl
          intro m hm
          exact average_signed_binomial_term a b (2 * r) m
    _ = ∑ m ∈ (Finset.range (2 * r + 1)).filter Even,
          b ^ m * a ^ (2 * r - m) * ((2 * r).choose m : ℝ) := by
      rw [Finset.sum_filter]
    _ = ∑ k ∈ Finset.range (r + 1),
          b ^ (2 * k) * a ^ (2 * r - 2 * k) * ((2 * r).choose (2 * k) : ℝ) := by
      symm
      refine Finset.sum_bij (fun k _hk => 2 * k) ?_ ?_ ?_ ?_
      · intro k hk
        simp only [Finset.mem_range] at hk
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · have : k ≤ r := by omega
          omega
        · exact even_two_mul k
      · intro k₁ hk₁ k₂ hk₂ h
        change 2 * k₁ = 2 * k₂ at h
        omega
      · intro m hm
        simp only [Finset.mem_filter, Finset.mem_range] at hm
        rcases hm.2 with ⟨k, hk⟩
        have hmk : m = 2 * k := by omega
        subst m
        refine ⟨k, ?_, ?_⟩
        · simp only [Finset.mem_range]
          omega
        · exact hmk.symm
      · intro k hk
        rfl

lemma two_point_bonami (a b : ℝ) (r : ℕ) :
    ((a + b) ^ (2 * r) + (a - b) ^ (2 * r)) / 2 ≤
      (a ^ 2 + (2 * r - 1 : ℕ) * b ^ 2) ^ r := by
  rw [average_even_powers_eq_sum]
  rw [show a ^ 2 + (2 * r - 1 : ℕ) * b ^ 2 =
      ((2 * r - 1 : ℕ) : ℝ) * b ^ 2 + a ^ 2 by ring, add_pow]
  apply Finset.sum_le_sum
  intro k hk
  simp only [Finset.mem_range] at hk
  have hkr : k ≤ r := by omega
  have hc := choose_even_le r k hkr
  have ha : 0 ≤ a ^ (2 * r - 2 * k) := by
    rw [show 2 * r - 2 * k = 2 * (r - k) by omega, pow_mul]
    positivity
  have hb : 0 ≤ b ^ (2 * k) := by rw [pow_mul]; positivity
  calc
    b ^ (2 * k) * a ^ (2 * r - 2 * k) * ((2 * r).choose (2 * k) : ℝ) ≤
        b ^ (2 * k) * a ^ (2 * r - 2 * k) *
          ((r.choose k : ℝ) * ((2 * r - 1 : ℕ) : ℝ) ^ k) := by
      gcongr
    _ = (((2 * r - 1 : ℕ) : ℝ) * b ^ 2) ^ k *
          (a ^ 2) ^ (r - k) * (r.choose k : ℝ) := by
      rw [show 2 * r - 2 * k = 2 * (r - k) by omega]
      simp only [mul_pow, pow_mul]
      ring

noncomputable def fintypeAverage {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ :=
  (∑ i, f i) / Fintype.card ι

noncomputable def fintypeLpNat {ι : Type*} [Fintype ι]
    (r : ℕ) (f : ι → ℝ) : ℝ :=
  (fintypeAverage fun i => |f i| ^ r) ^ (1 / (r : ℝ))

lemma fintypeLpNat_add_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (r : ℕ) (hr : 1 ≤ r) (f g : ι → ℝ) :
    fintypeLpNat r (f + g) ≤ fintypeLpNat r f + fintypeLpNat r g := by
  have hp : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h := Real.Lp_add_le Finset.univ f g hp
  simp only [Real.rpow_natCast] at h
  have hcard : 0 < (Fintype.card ι : ℝ) := by positivity
  have hsumfg : 0 ≤ ∑ i, |f i + g i| ^ r := Finset.sum_nonneg fun _ _ => by positivity
  have hsumf : 0 ≤ ∑ i, |f i| ^ r := Finset.sum_nonneg fun _ _ => by positivity
  have hsumg : 0 ≤ ∑ i, |g i| ^ r := Finset.sum_nonneg fun _ _ => by positivity
  unfold fintypeLpNat fintypeAverage
  simp only [Pi.add_apply]
  rw [Real.div_rpow hsumfg hcard.le, Real.div_rpow hsumf hcard.le,
    Real.div_rpow hsumg hcard.le]
  rw [← add_div]
  exact div_le_div_of_nonneg_right h (by positivity)

lemma fintypeAverage_fin_succ (n : ℕ) (f : (Fin (n + 1) → Bool) → ℝ) :
    fintypeAverage f =
      fintypeAverage (fun omega : Fin n → Bool =>
        (f (Fin.cons false omega) + f (Fin.cons true omega)) / 2) := by
  unfold fintypeAverage
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp f]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [pow_succ]
  have hcons (b : Bool) (omega : Fin n → Bool) :
      (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)) (b, omega) =
        Fin.cons b omega := rfl
  simp_rw [hcons]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  push_cast
  ring

lemma fintypeAverage_mono {ι : Type*} [Fintype ι] [Nonempty ι]
    {f g : ι → ℝ} (h : ∀ i, f i ≤ g i) :
    fintypeAverage f ≤ fintypeAverage g := by
  unfold fintypeAverage
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => h i) (by positivity)

lemma average_pow_add_root_le_of_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (r : ℕ) (hr : 1 ≤ r) (u v : ι → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    (fintypeAverage fun i => (u i + v i) ^ r) ^ (1 / (r : ℝ)) ≤
      (fintypeAverage fun i => u i ^ r) ^ (1 / (r : ℝ)) +
        (fintypeAverage fun i => v i ^ r) ^ (1 / (r : ℝ)) := by
  have h := fintypeLpNat_add_le r hr u v
  unfold fintypeLpNat at h
  simpa only [Pi.add_apply, abs_of_nonneg (hu _), abs_of_nonneg (hv _),
    abs_of_nonneg (add_nonneg (hu _) (hv _))] using! h

lemma average_const_mul_pow_root {ι : Type*} [Fintype ι] [Nonempty ι]
    (r : ℕ) (hr : 1 ≤ r) (c : ℝ) (hc : 0 ≤ c) (u : ι → ℝ)
    (hu : ∀ i, 0 ≤ u i) :
    (fintypeAverage fun i => (c * u i) ^ r) ^ (1 / (r : ℝ)) =
      c * (fintypeAverage fun i => u i ^ r) ^ (1 / (r : ℝ)) := by
  have hr0 : r ≠ 0 := by omega
  have havg_nonneg : 0 ≤ fintypeAverage (fun i => u i ^ r) := by
    unfold fintypeAverage
    exact div_nonneg (Finset.sum_nonneg fun i _ => pow_nonneg (hu i) _) (by positivity)
  have havg :
      fintypeAverage (fun i => (c * u i) ^ r) =
        c ^ r * fintypeAverage (fun i => u i ^ r) := by
    unfold fintypeAverage
    simp_rw [mul_pow, ← Finset.mul_sum]
    ring
  rw [havg, Real.mul_rpow (pow_nonneg hc _) havg_nonneg]
  rw [one_div, Real.pow_rpow_inv_natCast hc hr0]

def cubeSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] lemma cubeSign_false : cubeSign false = -1 := rfl
@[simp] lemma cubeSign_true : cubeSign true = 1 := rfl

inductive WalshCoeff : ℕ → Type
  | const (c : ℝ) : WalshCoeff 0
  | step {n : ℕ} (c0 c1 : WalshCoeff n) : WalshCoeff (n + 1)

def WalshCoeff.eval : {n : ℕ} → WalshCoeff n → (Fin n → Bool) → ℝ
  | 0, .const c, _omega => c
  | _n + 1, .step c0 c1, omega =>
      eval c0 (Fin.tail omega) + cubeSign (omega 0) * eval c1 (Fin.tail omega)

def WalshCoeff.energy (r : ℕ) : {n : ℕ} → WalshCoeff n → ℝ
  | 0, .const c => c ^ 2
  | _n + 1, .step c0 c1 => energy r c0 + (2 * r - 1 : ℕ) * energy r c1

@[simp] lemma WalshCoeff.eval_cons_false {n : ℕ} (c0 c1 : WalshCoeff n)
    (omega : Fin n → Bool) :
    (step c0 c1).eval (Fin.cons false omega) = c0.eval omega - c1.eval omega := by
  simp [WalshCoeff.eval]
  ring

@[simp] lemma WalshCoeff.eval_cons_true {n : ℕ} (c0 c1 : WalshCoeff n)
    (omega : Fin n → Bool) :
    (step c0 c1).eval (Fin.cons true omega) = c0.eval omega + c1.eval omega := by
  simp [WalshCoeff.eval]

noncomputable def evenNormSq {ι : Type*} [Fintype ι]
    (r : ℕ) (f : ι → ℝ) : ℝ :=
  (fintypeAverage fun i => |f i| ^ (2 * r)) ^ (1 / (r : ℝ))

lemma abs_pow_two_mul (x : ℝ) (r : ℕ) :
    |x| ^ (2 * r) = x ^ (2 * r) := by
  rw [← abs_pow]
  exact abs_of_nonneg ((even_two_mul r).pow_nonneg x)

lemma sq_pow_eq_abs_pow_two_mul (x : ℝ) (r : ℕ) :
    (x ^ 2) ^ r = |x| ^ (2 * r) := by
  rw [abs_pow_two_mul, pow_mul]

lemma fintypeAverage_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i) :
    0 ≤ fintypeAverage f := by
  unfold fintypeAverage
  exact div_nonneg (Finset.sum_nonneg fun i _ => hf i) (by positivity)

theorem WalshCoeff.bonami (r : ℕ) (hr : 1 ≤ r) :
    ∀ {n : ℕ} (c : WalshCoeff n), evenNormSq r c.eval ≤ c.energy r
  | 0, .const c => by
      have hr0 : r ≠ 0 := by omega
      unfold evenNormSq fintypeAverage
      simp only [WalshCoeff.eval, Fintype.card_unique, Nat.cast_one, div_one,
        WalshCoeff.energy]
      rw [Fintype.sum_unique]
      rw [show |c| ^ (2 * r) = (c ^ 2) ^ r by
        rw [pow_mul, sq_abs]]
      rw [one_div, Real.pow_rpow_inv_natCast (sq_nonneg c) hr0]
  | n + 1, .step c0 c1 => by
      rw [evenNormSq, fintypeAverage_fin_succ]
      simp_rw [WalshCoeff.eval_cons_false, WalshCoeff.eval_cons_true, abs_pow_two_mul]
      let w : ℝ := (2 * r - 1 : ℕ)
      have hw : 0 ≤ w := by positivity
      have hpoint (omega : Fin n → Bool) :
          ((c0.eval omega - c1.eval omega) ^ (2 * r) +
              (c0.eval omega + c1.eval omega) ^ (2 * r)) / 2 ≤
            (c0.eval omega ^ 2 + w * c1.eval omega ^ 2) ^ r := by
        simpa [w, add_comm] using!
          two_point_bonami (c0.eval omega) (c1.eval omega) r
      have havg :
          fintypeAverage (fun omega : Fin n → Bool =>
              ((c0.eval omega - c1.eval omega) ^ (2 * r) +
                (c0.eval omega + c1.eval omega) ^ (2 * r)) / 2) ≤
            fintypeAverage (fun omega : Fin n → Bool =>
              (c0.eval omega ^ 2 + w * c1.eval omega ^ 2) ^ r) :=
        fintypeAverage_mono hpoint
      have hleft_nonneg :
          0 ≤ fintypeAverage (fun omega : Fin n → Bool =>
              ((c0.eval omega - c1.eval omega) ^ (2 * r) +
                (c0.eval omega + c1.eval omega) ^ (2 * r)) / 2) :=
        fintypeAverage_nonneg fun omega =>
          div_nonneg
            (add_nonneg ((even_two_mul r).pow_nonneg _)
              ((even_two_mul r).pow_nonneg _)) (by norm_num)
      calc
        (fintypeAverage fun omega : Fin n → Bool =>
            ((c0.eval omega - c1.eval omega) ^ (2 * r) +
              (c0.eval omega + c1.eval omega) ^ (2 * r)) / 2) ^ (1 / (r : ℝ)) ≤
            (fintypeAverage fun omega : Fin n → Bool =>
              (c0.eval omega ^ 2 + w * c1.eval omega ^ 2) ^ r) ^
                (1 / (r : ℝ)) :=
          Real.rpow_le_rpow hleft_nonneg havg (by positivity)
        _ ≤ (fintypeAverage fun omega : Fin n → Bool =>
                (c0.eval omega ^ 2) ^ r) ^ (1 / (r : ℝ)) +
              (fintypeAverage fun omega : Fin n → Bool =>
                (w * c1.eval omega ^ 2) ^ r) ^ (1 / (r : ℝ)) :=
          average_pow_add_root_le_of_nonneg r hr
            (fun omega : Fin n → Bool => c0.eval omega ^ 2)
            (fun omega : Fin n → Bool => w * c1.eval omega ^ 2)
            (fun _ => sq_nonneg _) (fun _ => mul_nonneg hw (sq_nonneg _))
        _ = evenNormSq r c0.eval + w * evenNormSq r c1.eval := by
          rw [average_const_mul_pow_root r hr w hw
            (fun omega : Fin n → Bool => c1.eval omega ^ 2) (fun _ => sq_nonneg _)]
          simp_rw [sq_pow_eq_abs_pow_two_mul]
          rfl
        _ ≤ c0.energy r + w * c1.energy r :=
          add_le_add (bonami r hr c0)
            (mul_le_mul_of_nonneg_left (bonami r hr c1) hw)
        _ = (step c0 c1).energy r := by rfl

def maskDegree : {n : ℕ} → (Fin n → Bool) → ℕ
  | 0, _A => 0
  | _n + 1, A => (if A 0 then 1 else 0) + maskDegree (Fin.tail A)

def maskChar : {n : ℕ} → (Fin n → Bool) → (Fin n → Bool) → ℝ
  | 0, _A, _omega => 1
  | _n + 1, A, omega =>
      (if A 0 then cubeSign (omega 0) else 1) *
        maskChar (Fin.tail A) (Fin.tail omega)

noncomputable def maskEval {n : ℕ}
    (c : (Fin n → Bool) → ℝ) (omega : Fin n → Bool) : ℝ :=
  ∑ A, c A * maskChar A omega

noncomputable def maskEnergy {n : ℕ} (r : ℕ)
    (c : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ A, ((2 * r - 1 : ℕ) : ℝ) ^ maskDegree A * c A ^ 2

def WalshCoeff.ofMask : {n : ℕ} → ((Fin n → Bool) → ℝ) → WalshCoeff n
  | 0, c => .const (c default)
  | _n + 1, c =>
      .step (ofMask fun A => c (Fin.cons false A))
        (ofMask fun A => c (Fin.cons true A))

lemma sum_fin_succ_masks {M : Type*} [AddCommMonoid M]
    (n : ℕ) (f : (Fin (n + 1) → Bool) → M) :
    ∑ A, f A = ∑ A : Fin n → Bool, (f (Fin.cons false A) + f (Fin.cons true A)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp f]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  have hcons (b : Bool) (A : Fin n → Bool) :
      (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)) (b, A) =
        Fin.cons b A := rfl
  simp_rw [hcons]
  rw [Finset.sum_add_distrib]
  exact add_comm _ _

@[simp] lemma maskDegree_cons_false {n : ℕ} (A : Fin n → Bool) :
    maskDegree (Fin.cons false A) = maskDegree A := by
  simp [maskDegree]

@[simp] lemma maskDegree_cons_true {n : ℕ} (A : Fin n → Bool) :
    maskDegree (Fin.cons true A) = maskDegree A + 1 := by
  simp [maskDegree, Nat.add_comm]

@[simp] lemma maskChar_cons_false {n : ℕ} (A omega : Fin n → Bool) (b : Bool) :
    maskChar (Fin.cons false A) (Fin.cons b omega) = maskChar A omega := by
  simp [maskChar]

@[simp] lemma maskChar_cons_true {n : ℕ} (A omega : Fin n → Bool) (b : Bool) :
    maskChar (Fin.cons true A) (Fin.cons b omega) =
      cubeSign b * maskChar A omega := by
  simp [maskChar]

@[simp] lemma maskChar_cons_false' {n : ℕ} (A : Fin n → Bool)
    (omega : Fin (n + 1) → Bool) :
    maskChar (Fin.cons false A) omega = maskChar A (Fin.tail omega) := by
  simp [maskChar]

@[simp] lemma maskChar_cons_true' {n : ℕ} (A : Fin n → Bool)
    (omega : Fin (n + 1) → Bool) :
    maskChar (Fin.cons true A) omega =
      cubeSign (omega 0) * maskChar A (Fin.tail omega) := by
  simp [maskChar]

theorem WalshCoeff.eval_ofMask :
    ∀ {n : ℕ} (c : (Fin n → Bool) → ℝ) (omega : Fin n → Bool),
      (ofMask c).eval omega = maskEval c omega
  | 0, c, omega => by
      unfold ofMask maskEval
      rw [Fintype.sum_unique]
      simp only [WalshCoeff.eval, maskChar, mul_one, Pi.default_def, Bool.default_bool]
      rw [Subsingleton.elim (fun _ : Fin 0 => false) default]
      exact congrArg c (Subsingleton.elim _ _)
  | n + 1, c, omega => by
      unfold ofMask WalshCoeff.eval maskEval
      rw [sum_fin_succ_masks]
      simp only [maskChar_cons_false', maskChar_cons_true']
      rw [eval_ofMask (fun A => c (Fin.cons false A)) (Fin.tail omega),
        eval_ofMask (fun A => c (Fin.cons true A)) (Fin.tail omega)]
      unfold maskEval
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      apply congrArg₂ (· + ·) rfl
      apply Finset.sum_congr rfl
      intro A hA
      ring

theorem WalshCoeff.energy_ofMask (r : ℕ) :
    ∀ {n : ℕ} (c : (Fin n → Bool) → ℝ),
      (ofMask c).energy r = maskEnergy r c
  | 0, c => by
      unfold ofMask maskEnergy WalshCoeff.energy
      rw [Fintype.sum_unique]
      simp only [maskDegree, pow_zero, one_mul, Pi.default_def, Bool.default_bool]
      rw [Subsingleton.elim (fun _ : Fin 0 => false) default]
      exact congrArg (fun x : ℝ => x ^ 2) (congrArg c (Subsingleton.elim _ _))
  | n + 1, c => by
      unfold ofMask WalshCoeff.energy maskEnergy
      rw [sum_fin_succ_masks]
      simp_rw [maskDegree_cons_false, maskDegree_cons_true]
      rw [energy_ofMask r (fun A => c (Fin.cons false A)),
        energy_ofMask r (fun A => c (Fin.cons true A))]
      unfold maskEnergy
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      apply congrArg₂ (· + ·) rfl
      apply Finset.sum_congr rfl
      intro A hA
      rw [pow_succ]
      ring

theorem mask_bonami (r : ℕ) (hr : 1 ≤ r) {n : ℕ}
    (c : (Fin n → Bool) → ℝ) :
    evenNormSq r (maskEval c) ≤ maskEnergy r c := by
  have heval : (WalshCoeff.ofMask c).eval = maskEval c := by
    funext omega
    exact WalshCoeff.eval_ofMask c omega
  rw [← heval, ← WalshCoeff.energy_ofMask r c]
  exact WalshCoeff.bonami r hr (WalshCoeff.ofMask c)

end Problem520
end Erdos
