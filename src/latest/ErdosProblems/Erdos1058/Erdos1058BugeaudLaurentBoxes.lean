import ErdosProblems.Erdos1058.Erdos1058BugeaudLaurentVandermonde

open scoped BigOperators
open Polynomial

noncomputable section

namespace Erdos1058.BugeaudLaurent

def shiftedExponentialMatrixGeneral {n : ℕ}
    (shift scale : Fin n → ℚ) (exponent : Fin n → ℕ)
    (Q : Fin n → ℚ[X]) :
    Matrix (Fin n) (Fin n) ℚ[X] := fun i j =>
  Polynomial.C (scale i ^ exponent j) *
    (Q j).comp (Polynomial.X + Polynomial.C (shift i))

theorem shiftedExponentialMatrixGeneral_coeff_det {n : ℕ}
    (shift scale : Fin n → ℚ) (exponent : Fin n → ℕ)
    (Q : Fin n → ℚ[X])
    (hscale : ∀ i, scale i ≠ 0) (hQ : ∀ j, Q j ≠ 0) :
    ((shiftedExponentialMatrixGeneral shift scale exponent Q).det).coeff
        (∑ j : Fin n, (Q j).natDegree) =
      (Matrix.of fun (i j : Fin n) => scale i ^ exponent j).det *
        ∏ j : Fin n, (Q j).leadingCoeff := by
  rw [Matrix.det_apply]
  change (Polynomial.lcoeff ℚ (∑ j : Fin n, (Q j).natDegree))
      (∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
        ∏ i, shiftedExponentialMatrixGeneral shift scale exponent Q (σ i) i) = _
  rw [map_sum]
  simp
  rw [Matrix.det_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  let F : Fin n → ℚ[X] := fun j =>
    shiftedExponentialMatrixGeneral shift scale exponent Q (σ j) j
  have hF : ∀ j, F j ≠ 0 := by
    intro j
    apply mul_ne_zero
    · exact Polynomial.C_ne_zero.mpr (pow_ne_zero _ (hscale (σ j)))
    · exact Polynomial.comp_X_add_C_ne_zero_iff.mpr (hQ j)
  have hdeg : ∀ j, (F j).natDegree = (Q j).natDegree := by
    intro j
    have hscalar : Polynomial.C (scale (σ j) ^ exponent j) ≠ (0 : ℚ[X]) :=
      Polynomial.C_ne_zero.mpr (pow_ne_zero _ (hscale (σ j)))
    have hcomp : (Q j).comp
        (Polynomial.X + Polynomial.C (shift (σ j))) ≠ 0 :=
      Polynomial.comp_X_add_C_ne_zero_iff.mpr (hQ j)
    dsimp only [F, shiftedExponentialMatrixGeneral]
    rw [Polynomial.natDegree_mul hscalar hcomp,
      Polynomial.natDegree_C, Polynomial.natDegree_comp,
      Polynomial.natDegree_X_add_C]
    omega
  have hproddeg : (∏ j : Fin n, F j).natDegree =
      ∑ j : Fin n, (Q j).natDegree := by
    rw [Polynomial.natDegree_prod]
    · exact Finset.sum_congr rfl (fun j _ => hdeg j)
    · intro j _
      exact hF j
  rw [← hproddeg, Polynomial.coeff_natDegree,
    Polynomial.leadingCoeff_prod]
  have hcompLC (i j : Fin n) :
      ((Q j).comp (Polynomial.X + Polynomial.C (shift i))).leadingCoeff =
        (Q j).leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp]
    · rw [(Polynomial.monic_X_add_C (shift i)).leadingCoeff]
      simp
    · rw [Polynomial.natDegree_X_add_C]
      omega
  have hentryLC (j : Fin n) : (F j).leadingCoeff =
      scale (σ j) ^ exponent j * (Q j).leadingCoeff := by
    dsimp only [F, shiftedExponentialMatrixGeneral]
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      hcompLC]
  rw [Finset.prod_congr rfl (fun j _ => hentryLC j),
    Finset.prod_mul_distrib]
  simp only [Matrix.of_apply]
  rw [smul_mul_assoc]

theorem shiftedExponentialMatrixGeneral_det_ne_zero {n : ℕ}
    (shift scale : Fin n → ℚ) (exponent : Fin n → ℕ)
    (Q : Fin n → ℚ[X])
    (hscalePos : ∀ i, 0 < scale i) (hscaleInj : Function.Injective scale)
    (hexponent : Function.Injective exponent) (hQ : ∀ j, Q j ≠ 0) :
    (shiftedExponentialMatrixGeneral shift scale exponent Q).det ≠ 0 := by
  intro hzero
  have hcoeff := shiftedExponentialMatrixGeneral_coeff_det
    shift scale exponent Q (fun i => ne_of_gt (hscalePos i)) hQ
  rw [hzero, Polynomial.coeff_zero] at hcoeff
  have hv : (Matrix.of fun (i j : Fin n) => scale i ^ exponent j).det ≠ 0 :=
    generalizedVandermonde_det_ne_zero scale hscalePos hscaleInj exponent hexponent
  have hlead : (∏ j : Fin n, (Q j).leadingCoeff) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact Polynomial.leadingCoeff_ne_zero.mpr (hQ j)
  exact (mul_ne_zero hv hlead) hcoeff.symm

theorem shiftedExponentialMatrixGeneral_root_bound {n : ℕ}
    (shift scale : Fin n → ℚ) (exponent : Fin n → ℕ)
    (Q : Fin n → ℚ[X])
    (hscalePos : ∀ i, 0 < scale i) (hscaleInj : Function.Injective scale)
    (hexponent : Function.Injective exponent) (hQ : ∀ j, Q j ≠ 0)
    (points : Finset ℚ)
    (hcard : (∑ j : Fin n, (Q j).natDegree) < points.card)
    (hkernel : ∀ x ∈ points, ∃ w : Fin n → ℚ, w ≠ 0 ∧
      Matrix.mulVec (Matrix.of fun (i j : Fin n) => scale i ^ exponent j *
        (Q j).eval (x + shift i)) w = 0) : False := by
  let Δ : ℚ[X] := (shiftedExponentialMatrixGeneral shift scale exponent Q).det
  have hΔne : Δ ≠ 0 :=
    shiftedExponentialMatrixGeneral_det_ne_zero shift scale exponent Q
      hscalePos hscaleInj hexponent hQ
  have heval : ∀ x ∈ points, Δ.eval x = 0 := by
    intro x hx
    obtain ⟨w, hw, hmul⟩ := hkernel x hx
    let A : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j =>
      scale i ^ exponent j * (Q j).eval (x + shift i)
    have hdet : A.det = 0 := by
      by_contra hdet
      exact hw (Matrix.eq_zero_of_mulVec_eq_zero hdet (by simpa [A] using hmul))
    have hmap : (shiftedExponentialMatrixGeneral shift scale exponent Q).map
        (Polynomial.evalRingHom x) = A := by
      ext i j
      simp [A, shiftedExponentialMatrixGeneral, Polynomial.eval_comp]
    change (Polynomial.evalRingHom x) Δ = 0
    rw [show (Polynomial.evalRingHom x) Δ =
        ((shiftedExponentialMatrixGeneral shift scale exponent Q).map
          (Polynomial.evalRingHom x)).det by
      simpa [Δ] using (RingHom.map_det (Polynomial.evalRingHom x)
        (shiftedExponentialMatrixGeneral shift scale exponent Q))]
    rw [hmap, hdet]
  have hz := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
    Δ points heval
  have hdeg : Δ.natDegree ≤ ∑ j : Fin n, (Q j).natDegree := by
    dsimp only [Δ]
    rw [Matrix.det_apply]
    refine (Polynomial.natDegree_sum_le _ _).trans ?_
    rw [Finset.fold_max_le]
    constructor
    · omega
    · intro σ _
      exact (Polynomial.natDegree_smul_le _ _).trans
        ((Polynomial.natDegree_prod_le _ _).trans
          (Finset.sum_le_sum fun j _ => by
            have hscalar : Polynomial.C (scale (σ j) ^ exponent j) ≠ (0 : ℚ[X]) :=
              Polynomial.C_ne_zero.mpr (pow_ne_zero _ (ne_of_gt (hscalePos (σ j))))
            have hcomp : (Q j).comp
                (Polynomial.X + Polynomial.C (shift (σ j))) ≠ 0 :=
              Polynomial.comp_X_add_C_ne_zero_iff.mpr (hQ j)
            dsimp only [shiftedExponentialMatrixGeneral]
            rw [Polynomial.natDegree_mul hscalar hcomp,
              Polynomial.natDegree_C, Polynomial.natDegree_comp,
              Polynomial.natDegree_X_add_C]
            omega))
  exact hΔne (hz (hdeg.trans_lt hcard))

theorem exponential_polynomial_zero_general {L : ℕ}
    (shift scale : Fin L → ℚ)
    (hscalePos : ∀ r, 0 < scale r) (hscaleInj : Function.Injective scale)
    (Q : Fin L → ℚ[X]) (hQsome : ∃ l, Q l ≠ 0)
    (points : Finset ℚ)
    (hcard : (∑ l ∈ Finset.univ.filter (fun l : Fin L => Q l ≠ 0),
      (Q l).natDegree) < points.card)
    (y : ℚ → ℚ) (hy : ∀ x ∈ points, y x ≠ 0)
    (hzero : ∀ x ∈ points, ∀ r : Fin L,
      ∑ l : Fin L, scale r ^ l.val *
        (Q l).eval (x + shift r) * y x ^ l.val = 0) : False := by
  classical
  let support : Finset (Fin L) :=
    Finset.univ.filter fun l : Fin L => Q l ≠ 0
  let e : Fin support.card → Fin L := fun i => (support.equivFin.symm i).val
  let Q' : Fin support.card → ℚ[X] := fun i => Q (e i)
  have hQ' : ∀ i, Q' i ≠ 0 := by
    intro i
    exact (Finset.mem_filter.mp (support.equivFin.symm i).property).2
  have heinj : Function.Injective e := by
    intro i j hij
    apply support.equivFin.symm.injective
    exact Subtype.ext hij
  have hsupportcard : support.card ≤ L := by
    simpa using Finset.card_le_univ support
  let row : Fin support.card → Fin L := fun i => Fin.castLE hsupportcard i
  let shift' : Fin support.card → ℚ := fun i => shift (row i)
  let scale' : Fin support.card → ℚ := fun i => scale (row i)
  have hscalePos' : ∀ i, 0 < scale' i := by
    intro i
    exact hscalePos (row i)
  have hrowinj : Function.Injective row := by
    intro i j hij
    apply Fin.ext
    simpa [row] using congrArg Fin.val hij
  have hscaleInj' : Function.Injective scale' := hscaleInj.comp hrowinj
  apply shiftedExponentialMatrixGeneral_root_bound
    shift' scale' (fun i => (e i).val) Q' hscalePos' hscaleInj'
      (fun i j hij => heinj (Fin.ext hij)) hQ' points
  · change (∑ i : Fin support.card, (Q (e i)).natDegree) < points.card
    rw [show (∑ i : Fin support.card, (Q (e i)).natDegree) =
        ∑ l ∈ support, (Q l).natDegree by
      calc
        (∑ i : Fin support.card, (Q (e i)).natDegree) =
            ∑ l : support, (Q l.val).natDegree := by
          simpa only [e] using support.equivFin.symm.sum_comp
            (fun l : support => (Q l.val).natDegree)
        _ = ∑ l ∈ support, (Q l).natDegree :=
          Finset.sum_attach support (fun l : Fin L => (Q l).natDegree)]
    exact hcard
  · intro x hx
    let w : Fin support.card → ℚ := fun i => y x ^ (e i).val
    have hw : w ≠ 0 := by
      intro hwzero
      obtain ⟨l, hl⟩ := hQsome
      have hls : l ∈ support := by simp [support, hl]
      let i : Fin support.card := support.equivFin ⟨l, hls⟩
      have hwi := congr_fun hwzero i
      simp only [Pi.zero_apply, w] at hwi
      exact (pow_ne_zero _ (hy x hx)) hwi
    refine ⟨w, hw, ?_⟩
    ext r
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    let term : Fin L → ℚ := fun l =>
      scale (row r) ^ l.val *
        (Q l).eval (x + shift (row r)) * y x ^ l.val
    calc
      ∑ i : Fin support.card,
          scale' r ^ (e i).val * (Q' i).eval (x + shift' r) * w i =
          ∑ i : Fin support.card, term (e i) := by
            apply Finset.sum_congr rfl
            intro i _
            simp [term, scale', shift', Q', w]
      _ = ∑ l : support, term l.val := by
        simpa only [e] using support.equivFin.symm.sum_comp
          (fun l : support => term l.val)
      _ = ∑ l ∈ support, term l := Finset.sum_attach support term
      _ = ∑ l : Fin L, term l := by
        apply Finset.sum_subset (by simp)
        intro l _ hl
        have hQl : Q l = 0 := by simpa [support] using hl
        simp [term, hQl]
      _ = 0 := hzero x hx (row r)

theorem exists_nonsingular_bivariate_choose_minor_general {K L : ℕ}
    {C : Type*} [Fintype C] [DecidableEq C]
    (hK : 0 < K) (xcoord ycoord : C → ℚ)
    (shift scale : Fin L → ℚ)
    (hscalePos : ∀ r, 0 < scale r) (hscaleInj : Function.Injective scale)
    (points : Finset ℚ) (hpoints : (K - 1) * L < points.card)
    (y : ℚ → ℚ) (hy : ∀ x ∈ points, y x ≠ 0)
    (column : ℚ → Fin L → C)
    (hxcol : ∀ x ∈ points, ∀ r,
      xcoord (column x r) = x + shift r)
    (hycol : ∀ x ∈ points, ∀ r,
      ycoord (column x r) = y x * scale r) :
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
    refine exponential_polynomial_zero_general shift scale hscalePos hscaleInj
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
          ∑ l : Fin L, scale r ^ l.val *
            (chooseCoefficientPolynomial z l).eval (x + shift r) *
              y x ^ l.val by
        rw [Fintype.sum_prod_type]
        simp_rw [M, hxcol x hx r, hycol x hx r,
          chooseCoefficientPolynomial_eval]
        simp_rw [mul_pow]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        calc
          (∑ k : Fin K, (choosePolynomial k.val).eval (x + shift r) *
              (y x ^ l.val * scale r ^ l.val) * z (k, l)) =
              (∑ k : Fin K, scale r ^ l.val *
                (z (k, l) * (choosePolynomial k.val).eval (x + shift r))) *
                  y x ^ l.val := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _
            ring
          _ = (scale r ^ l.val *
                ∑ k : Fin K,
                  z (k, l) * (choosePolynomial k.val).eval (x + shift r)) *
                  y x ^ l.val := by
            apply congrArg (fun t : ℚ => t * y x ^ l.val)
            rw [Finset.mul_sum]
        ]
      exact hc
  simpa [z, sub_eq_zero] using hz

theorem prime_power_product_exponents_injective {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Function.Injective (fun uv : ℕ × ℕ => p ^ uv.1 * q ^ uv.2) := by
  intro uv uv' huv
  have hp0 : p ≠ 0 := hp.ne_zero
  have hq0 : q ≠ 0 := hq.ne_zero
  have hpExp := congrArg (fun z : ℕ => z.factorization p) huv
  have hqExp := congrArg (fun z : ℕ => z.factorization q) huv
  simp [Nat.factorization_mul (pow_ne_zero _ hp0) (pow_ne_zero _ hq0),
    hp.factorization_pow, hq.factorization_pow, Finsupp.single_apply,
    hpq, hpq.symm] at hpExp hqExp
  exact Prod.ext hpExp hqExp

theorem balanced_scale_injective {R S p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Function.Injective (fun rs : Fin R × Fin S =>
      p ^ (2 * rs.1.val) * q ^ (2 * (S - rs.2.val))) := by
  intro rs rs' hrs
  have hpair : (2 * rs.1.val, 2 * (S - rs.2.val)) =
      (2 * rs'.1.val, 2 * (S - rs'.2.val)) := by
    apply prime_power_product_exponents_injective hp hq hpq
    exact hrs
  apply Prod.ext
  · apply Fin.ext
    have := congrArg Prod.fst hpair
    omega
  · apply Fin.ext
    have := congrArg Prod.snd hpair
    have hs := rs.2.isLt
    have hs' := rs'.2.isLt
    omega

theorem exists_nonsingular_interpolation_boxes
    {K L R₁ R₂ S₁ S₂ a b p q : ℕ}
    (hK : 0 < K) (hL : 0 < L)
    (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hS₁ : 0 < S₁) (hS₂ : 0 < S₂)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hb : 0 < b)
    (hsize₁ : L ≤ R₁ * S₁) (hsize₂ : (K - 1) * L < R₂ * S₂)
    (hinj : Function.Injective (fun rs : Fin R₂ × Fin S₂ =>
      b * rs.1.val + a * rs.2.val)) :
    ∃ f : Fin K × Fin L → Fin (R₁ + R₂ - 1) × Fin (S₁ + S₂ - 1),
      Function.Injective f ∧
      (Matrix.of (fun row col =>
        ((b * (f col).1.val + a * (f col).2.val : ℕ).choose row.1.val : ℚ) *
          (((p : ℚ) ^ (2 * (f col).1.val) /
            (q : ℚ) ^ (2 * (f col).2.val)) ^ row.2.val))).det ≠ 0 := by
  classical
  let C := Fin (R₁ + R₂ - 1) × Fin (S₁ + S₂ - 1)
  let source₁ := Fin R₁ × Fin S₁
  let source₂ := Fin R₂ × Fin S₂
  let first : Fin L → source₁ := fun i =>
    finProdFinEquiv.symm (Fin.castLE hsize₁ i)
  have hfirst : Function.Injective first :=
    finProdFinEquiv.symm.injective.comp (Fin.castLE_injective hsize₁)
  let linear : source₂ → ℕ := fun rs => b * rs.1.val + a * rs.2.val
  let points : Finset ℚ := Finset.univ.image fun rs : source₂ => (linear rs : ℚ)
  let defaultSource : source₂ := (⟨0, hR₂⟩, ⟨0, hS₂⟩)
  let rep : ℚ → source₂ := fun x =>
    if hx : ∃ rs : source₂, (linear rs : ℚ) = x then Classical.choose hx
    else defaultSource
  have hrep {x : ℚ} (hx : x ∈ points) : (linear (rep x) : ℚ) = x := by
    have hex : ∃ rs : source₂, (linear rs : ℚ) = x := by
      rw [Finset.mem_image] at hx
      obtain ⟨rs, _, hrs⟩ := hx
      exact ⟨rs, hrs⟩
    simp only [rep, dif_pos hex]
    exact Classical.choose_spec hex
  let column : ℚ → Fin L → C := fun x i =>
    (⟨(rep x).1.val + (first i).1.val, by
      have hr₂' := (rep x).1.isLt
      have hr₁' := (first i).1.isLt
      omega⟩,
     ⟨(rep x).2.val + (first i).2.val, by
      have hs₂' := (rep x).2.isLt
      have hs₁' := (first i).2.isLt
      omega⟩)
  let xcoord : C → ℚ := fun rs =>
    (b * rs.1.val + a * rs.2.val : ℕ)
  let ycoord : C → ℚ := fun rs =>
    (p : ℚ) ^ (2 * rs.1.val) / (q : ℚ) ^ (2 * rs.2.val)
  let shift : Fin L → ℚ := fun i =>
    (b * (first i).1.val + a * (first i).2.val : ℕ)
  let scale : Fin L → ℚ := fun i =>
    (p ^ (2 * (first i).1.val) *
      q ^ (2 * (S₁ - (first i).2.val)) : ℕ)
  let y : ℚ → ℚ := fun x =>
    (p : ℚ) ^ (2 * (rep x).1.val) /
      (q : ℚ) ^ (2 * ((rep x).2.val + S₁))
  have hpointsCard : points.card = R₂ * S₂ := by
    dsimp only [points]
    rw [Finset.card_image_of_injective]
    · simp [source₂]
    · intro rs rs' hrs
      apply hinj
      change (linear rs : ℚ) = (linear rs' : ℚ) at hrs
      have hlin : linear rs = linear rs' := by exact_mod_cast hrs
      simpa only [linear] using hlin
  have hpoints : (K - 1) * L < points.card := by
    rw [hpointsCard]
    exact hsize₂
  have hscalePos : ∀ i, 0 < scale i := by
    intro i
    dsimp only [scale]
    exact_mod_cast Nat.mul_pos (pow_pos hp.pos _) (pow_pos hq.pos _)
  have hscaleInj : Function.Injective scale := by
    intro i j hij
    apply hfirst
    apply balanced_scale_injective hp hq hpq
    dsimp only [scale] at hij
    exact_mod_cast hij
  have hy : ∀ x ∈ points, y x ≠ 0 := by
    intro x hx
    dsimp only [y]
    exact div_ne_zero
      (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
      (pow_ne_zero _ (by exact_mod_cast hq.ne_zero))
  have hxcol : ∀ x ∈ points, ∀ i,
      xcoord (column x i) = x + shift i := by
    intro x hx i
    have hr := hrep hx
    dsimp only [xcoord, column, shift]
    push_cast
    calc
      (b : ℚ) * ((rep x).1.val + (first i).1.val) +
          a * ((rep x).2.val + (first i).2.val) =
          ((linear (rep x) : ℕ) : ℚ) +
            (b * (first i).1.val + a * (first i).2.val : ℕ) := by
              dsimp only [linear]
              push_cast
              ring
      _ = x + ((b : ℚ) * (first i).1.val + a * (first i).2.val) := by
        rw [hr]
        push_cast
        rfl
  have hycol : ∀ x ∈ points, ∀ i,
      ycoord (column x i) = y x * scale i := by
    intro x hx i
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
    dsimp only [ycoord, column, y, scale]
    push_cast
    rw [show 2 * ((rep x).1.val + (first i).1.val) =
        2 * (rep x).1.val + 2 * (first i).1.val by omega, pow_add]
    have hs : (first i).2.val < S₁ := (first i).2.isLt
    have hexp : 2 * ((rep x).2.val + S₁) =
        2 * ((rep x).2.val + (first i).2.val) +
          2 * (S₁ - (first i).2.val) := by omega
    rw [hexp, pow_add]
    field_simp
  obtain ⟨f, hf, hdet⟩ := exists_nonsingular_bivariate_choose_minor_general
    hK xcoord ycoord shift scale hscalePos hscaleInj
    points hpoints y hy column hxcol hycol
  refine ⟨f, hf, ?_⟩
  simpa only [xcoord, ycoord, C, choosePolynomial_eval_nat] using hdet

end Erdos1058.BugeaudLaurent
