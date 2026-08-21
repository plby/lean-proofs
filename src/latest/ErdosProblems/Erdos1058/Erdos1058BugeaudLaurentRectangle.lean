import ErdosProblems.Erdos1058.Erdos1058BugeaudLaurentZero
import ErdosProblems.Erdos1058.Erdos1058BugeaudLaurentMod

open scoped BigOperators

noncomputable section

namespace Erdos1058.BugeaudLaurent

open Polynomial

def choosePolynomial (k : ℕ) : ℚ[X] :=
  Polynomial.C ((k.factorial : ℚ)⁻¹) * descPochhammer ℚ k

lemma choosePolynomial_eval_nat (x k : ℕ) :
    (choosePolynomial k).eval (x : ℚ) = (x.choose k : ℚ) := by
  rw [choosePolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    descPochhammer_eval_eq_descFactorial]
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hk : (k.factorial : ℚ) ≠ 0 := by positivity
  field_simp

lemma choosePolynomial_natDegree (k : ℕ) :
    (choosePolynomial k).natDegree = k := by
  rw [choosePolynomial, Polynomial.natDegree_mul]
  · rw [Polynomial.natDegree_C, descPochhammer_natDegree]
    omega
  · exact Polynomial.C_ne_zero.mpr (inv_ne_zero (by positivity))
  · exact (monic_descPochhammer ℚ k).ne_zero

lemma choosePolynomial_coeff_self (k : ℕ) :
    (choosePolynomial k).coeff k = (k.factorial : ℚ)⁻¹ := by
  calc
    (choosePolynomial k).coeff k =
        (choosePolynomial k).coeff (choosePolynomial k).natDegree := by
          rw [choosePolynomial_natDegree]
    _ = (choosePolynomial k).leadingCoeff := Polynomial.coeff_natDegree
    _ = (k.factorial : ℚ)⁻¹ := by
      rw [choosePolynomial, Polynomial.leadingCoeff_mul,
        Polynomial.leadingCoeff_C, (monic_descPochhammer ℚ k).leadingCoeff]
      simp

lemma choosePolynomial_coeff_of_lt {j k : ℕ} (hjk : j < k) :
    (choosePolynomial j).coeff k = 0 := by
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    ((choosePolynomial_natDegree j).symm ▸ hjk)

theorem sum_choosePolynomial_ne_zero {K : ℕ} (v : Fin K → ℚ)
    (hv : v ≠ 0) :
    (∑ k : Fin K, Polynomial.C (v k) * choosePolynomial k.val) ≠ 0 := by
  induction K with
  | zero =>
      exfalso
      apply hv
      funext k
      exact Fin.elim0 k
  | succ K ih =>
      by_cases hlast : v (Fin.last K) = 0
      · let v' : Fin K → ℚ := fun k => v k.castSucc
        have hv' : v' ≠ 0 := by
          intro hvzero
          apply hv
          funext k
          refine Fin.lastCases ?_ (fun j => ?_) k
          · exact hlast
          · exact congr_fun hvzero j
        have hi := ih v' hv'
        rw [Fin.sum_univ_castSucc, hlast]
        simp only [Polynomial.C_0, zero_mul, add_zero]
        exact hi
      · intro hsum
        have hc := congrArg (fun P : ℚ[X] => P.coeff K) hsum
        rw [Fin.sum_univ_castSucc] at hc
        simp only [Polynomial.coeff_add, Polynomial.coeff_zero] at hc
        have hprefix :
            ((∑ k : Fin K,
              Polynomial.C (v k.castSucc) * choosePolynomial k.castSucc.val) : ℚ[X]).coeff K = 0 := by
          rw [show (∑ k : Fin K,
              Polynomial.C (v k.castSucc) * choosePolynomial k.castSucc.val) =
              ∑ k ∈ (Finset.univ : Finset (Fin K)),
                Polynomial.C (v k.castSucc) * choosePolynomial k.castSucc.val by rfl]
          rw [Polynomial.finsetSum_coeff]
          apply Finset.sum_eq_zero
          intro k _
          rw [Polynomial.coeff_C_mul]
          have hkzero : (choosePolynomial k.castSucc.val).coeff K = 0 :=
            choosePolynomial_coeff_of_lt k.isLt
          rw [hkzero]
          simp
        have hlastCoeff :
            (choosePolynomial (Fin.last K).val).coeff K =
              (K.factorial : ℚ)⁻¹ := by
          simpa using choosePolynomial_coeff_self K
        rw [hprefix, zero_add, Polynomial.coeff_C_mul, hlastCoeff] at hc
        exact hlast (mul_eq_zero.mp hc |>.resolve_right (inv_ne_zero (by positivity)))

def chooseCoefficientPolynomial {K L : ℕ}
    (v : Fin K × Fin L → ℚ) (l : Fin L) : ℚ[X] :=
  ∑ k : Fin K, Polynomial.C (v (k, l)) * choosePolynomial k.val

lemma chooseCoefficientPolynomial_eval {K L : ℕ}
    (v : Fin K × Fin L → ℚ) (l : Fin L) (x : ℚ) :
    (chooseCoefficientPolynomial v l).eval x =
      ∑ k : Fin K, v (k, l) * (choosePolynomial k.val).eval x := by
  change (Polynomial.evalRingHom x)
      (∑ k : Fin K, Polynomial.C (v (k, l)) * choosePolynomial k.val) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp

lemma chooseCoefficientPolynomial_natDegree_le {K L : ℕ} (hK : 0 < K)
    (v : Fin K × Fin L → ℚ) (l : Fin L) :
    (chooseCoefficientPolynomial v l).natDegree ≤ K - 1 := by
  unfold chooseCoefficientPolynomial
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  constructor
  · omega
  · intro k _
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Polynomial.natDegree_C, choosePolynomial_natDegree]
    omega

theorem exists_nonsingular_bivariate_choose_minor {K L : ℕ}
    {C : Type*} [Fintype C] [DecidableEq C]
    (hK : 0 < K) (xcoord ycoord : C → ℚ)
    (b base : ℚ) (hbase : 1 < base)
    (points : Finset ℚ) (hpoints : (K - 1) * L < points.card)
    (y : ℚ → ℚ) (hy : ∀ x ∈ points, y x ≠ 0)
    (column : ℚ → Fin L → C)
    (hxcol : ∀ x ∈ points, ∀ r,
      xcoord (column x r) = x + b * r.val)
    (hycol : ∀ x ∈ points, ∀ r,
      ycoord (column x r) = y x * base ^ r.val) :
    ∃ f : Fin K × Fin L → C, Function.Injective f ∧
      (Matrix.of (fun row col =>
        (choosePolynomial row.1.val).eval (xcoord (f col)) *
          ycoord (f col) ^ row.2.val)).det ≠ 0 := by
  let M : Matrix (Fin K × Fin L) C ℚ := fun row col =>
    (choosePolynomial row.1.val).eval (xcoord col) * ycoord col ^ row.2.val
  apply exists_nonsingular_column_minor_general M
  intro v w hvw
  let z : Fin K × Fin L → ℚ := v - w
  have hzmul : M.transpose.mulVec z = 0 := by
    rw [show z = v - w by rfl, Matrix.mulVec_sub, hvw, sub_self]
  have hz : z = 0 := by
    by_contra hz
    have hQsome : ∃ l : Fin L, chooseCoefficientPolynomial z l ≠ 0 := by
      obtain ⟨⟨k, l⟩, hkl⟩ : ∃ row : Fin K × Fin L, z row ≠ 0 := by
        obtain ⟨row, hrow⟩ := Function.ne_iff.mp hz
        exact ⟨row, by simpa using hrow⟩
      refine ⟨l, ?_⟩
      apply sum_choosePolynomial_ne_zero (fun k => z (k, l))
      intro hzero
      exact hkl (congr_fun hzero k)
    refine translated_exponential_polynomial_zero_lemma b base hbase
      (chooseCoefficientPolynomial z) hQsome points ?_ y hy ?_
    · let s : Finset (Fin L) := Finset.univ.filter
          (fun l : Fin L => chooseCoefficientPolynomial z l ≠ 0)
      have hsCard : s.card ≤ L := by simpa using Finset.card_le_univ s
      have hsBound : (∑ l ∈ s, (chooseCoefficientPolynomial z l).natDegree) <
          points.card := by
        calc
          (∑ l ∈ s, (chooseCoefficientPolynomial z l).natDegree) ≤
              ∑ _l ∈ s, (K - 1) := by
                exact Finset.sum_le_sum (fun l _ =>
                  chooseCoefficientPolynomial_natDegree_le hK z l)
          _ = s.card * (K - 1) := by simp
          _ ≤ L * (K - 1) := Nat.mul_le_mul_right (K - 1) hsCard
          _ < points.card := by simpa [Nat.mul_comm] using hpoints
      simpa only [s] using hsBound
    · intro x hx r
      have hc := congr_fun hzmul (column x r)
      simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct,
        Pi.zero_apply] at hc
      rw [← show ∑ row : Fin K × Fin L, M row (column x r) * z row =
          ∑ l : Fin L, base ^ (l.val * r.val) *
            (chooseCoefficientPolynomial z l).eval (x + b * r.val) *
              y x ^ l.val by
        rw [Fintype.sum_prod_type]
        simp_rw [M, hxcol x hx r, hycol x hx r,
          chooseCoefficientPolynomial_eval]
        simp_rw [mul_pow, pow_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        have hp : (base ^ (r : ℕ)) ^ (l : ℕ) =
            (base ^ (l : ℕ)) ^ (r : ℕ) := by
          simp only [← pow_mul]
          rw [Nat.mul_comm]
        rw [hp]
        calc
          (∑ k : Fin K, (choosePolynomial k.val).eval (x + b * r.val) *
              (y x ^ l.val * (base ^ l.val) ^ r.val) * z (k, l)) =
              (∑ k : Fin K, (base ^ l.val) ^ r.val *
                (z (k, l) * (choosePolynomial k.val).eval (x + b * r.val))) *
                  y x ^ l.val := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _
            ring
          _ = ((base ^ l.val) ^ r.val *
                ∑ k : Fin K,
                  z (k, l) * (choosePolynomial k.val).eval (x + b * r.val)) *
                  y x ^ l.val := by
            apply congrArg (fun t : ℚ => t * y x ^ l.val)
            rw [Finset.mul_sum]]
      exact hc
  simpa [z, sub_eq_zero] using hz

theorem exists_nonsingular_interpolation_rectangle
    {K L R₂ S₂ a b p q : ℕ}
    (hK : 0 < K) (hL : 0 < L) (hR₂ : 0 < R₂) (hS₂ : 0 < S₂)
    (hp : 1 < p) (hq : 0 < q) (hb : 0 < b)
    (hsize : (K - 1) * L < R₂ * S₂)
    (hinj : Function.Injective (fun rs : Fin R₂ × Fin S₂ =>
      b * rs.1.val + a * rs.2.val)) :
    ∃ f : Fin K × Fin L → Fin (R₂ + L - 1) × Fin S₂,
      Function.Injective f ∧
      (Matrix.of (fun row col =>
        ((b * (f col).1.val + a * (f col).2.val : ℕ).choose row.1.val : ℚ) *
          (((p : ℚ) ^ (2 * (f col).1.val) /
            (q : ℚ) ^ (2 * (f col).2.val)) ^ row.2.val))).det ≠ 0 := by
  classical
  let C := Fin (R₂ + L - 1) × Fin S₂
  let source := Fin R₂ × Fin S₂
  let linear : source → ℕ := fun rs => b * rs.1.val + a * rs.2.val
  let points : Finset ℚ := Finset.univ.image fun rs : source => (linear rs : ℚ)
  let defaultSource : source := (⟨0, hR₂⟩, ⟨0, hS₂⟩)
  let rep : ℚ → source := fun x =>
    if hx : ∃ rs : source, (linear rs : ℚ) = x then Classical.choose hx
    else defaultSource
  have hrep {x : ℚ} (hx : x ∈ points) : (linear (rep x) : ℚ) = x := by
    have hex : ∃ rs : source, (linear rs : ℚ) = x := by
      rw [Finset.mem_image] at hx
      obtain ⟨rs, _, hrs⟩ := hx
      exact ⟨rs, hrs⟩
    simp only [rep, dif_pos hex]
    exact Classical.choose_spec hex
  have hR : 0 < R₂ + L - 1 := by omega
  let column : ℚ → Fin L → C := fun x r =>
    (⟨r.val + (rep x).1.val, by
      have hr := r.isLt
      have hs := (rep x).1.isLt
      omega⟩, (rep x).2)
  let xcoord : C → ℚ := fun rs =>
    (b * rs.1.val + a * rs.2.val : ℕ)
  let ycoord : C → ℚ := fun rs =>
    (p : ℚ) ^ (2 * rs.1.val) / (q : ℚ) ^ (2 * rs.2.val)
  let y : ℚ → ℚ := fun x =>
    (p : ℚ) ^ (2 * (rep x).1.val) / (q : ℚ) ^ (2 * (rep x).2.val)
  have hpointsCard : points.card = R₂ * S₂ := by
    dsimp only [points]
    rw [Finset.card_image_of_injective]
    · simp [source]
    · intro rs rs' hrs
      apply hinj
      change (linear rs : ℚ) = (linear rs' : ℚ) at hrs
      have hlin : linear rs = linear rs' := by exact_mod_cast hrs
      simpa only [linear] using hlin
  have hpoints : (K - 1) * L < points.card := by
    rw [hpointsCard]
    exact hsize
  have hy : ∀ x ∈ points, y x ≠ 0 := by
    intro x hx
    dsimp only [y]
    exact div_ne_zero (pow_ne_zero _ (by exact_mod_cast (show p ≠ 0 by omega)))
      (pow_ne_zero _ (by exact_mod_cast (show q ≠ 0 by omega)))
  have hxcol : ∀ x ∈ points, ∀ r,
      xcoord (column x r) = x + (b : ℚ) * r.val := by
    intro x hx r
    have hr := hrep hx
    dsimp only [xcoord, column]
    push_cast
    calc
      (b : ℚ) * (r.val + (rep x).1.val) + a * (rep x).2.val =
          ((linear (rep x) : ℕ) : ℚ) + b * r.val := by
            dsimp only [linear]
            push_cast
            ring
      _ = x + b * r.val := by rw [hr]
  have hycol : ∀ x ∈ points, ∀ r,
      ycoord (column x r) = y x * ((p : ℚ) ^ 2) ^ r.val := by
    intro x hx r
    dsimp only [ycoord, column, y]
    rw [show 2 * (r.val + (rep x).1.val) =
        2 * (rep x).1.val + 2 * r.val by omega, pow_add]
    rw [show (p : ℚ) ^ (2 * r.val) = ((p : ℚ) ^ 2) ^ r.val by
      rw [pow_mul]]
    ring
  obtain ⟨f, hf, hdet⟩ := exists_nonsingular_bivariate_choose_minor
    hK xcoord ycoord (b : ℚ) ((p : ℚ) ^ 2)
    (by nlinarith [show (1 : ℚ) < p by exact_mod_cast hp])
    points hpoints y hy column hxcol hycol
  refine ⟨f, hf, ?_⟩
  simpa only [xcoord, ycoord, C, choosePolynomial_eval_nat] using hdet

end Erdos1058.BugeaudLaurent
