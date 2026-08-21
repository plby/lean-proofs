import ErdosProblems.Erdos1058.Erdos1058BugeaudLaurent

open scoped BigOperators
open Polynomial

noncomputable section

namespace Erdos1058.BugeaudLaurent

def shiftedExponentialMatrix {n : ℕ} (b : ℚ)
    (c : Fin n → ℚ) (Q : Fin n → ℚ[X]) :
    Matrix (Fin n) (Fin n) ℚ[X] := fun i j =>
  Polynomial.C (c j ^ i.val) *
    (Q j).comp (Polynomial.X + Polynomial.C (b * i.val))

theorem shiftedExponentialMatrix_coeff_det {n : ℕ} (b : ℚ)
    (c : Fin n → ℚ) (Q : Fin n → ℚ[X])
    (hc : ∀ j, c j ≠ 0) (hQ : ∀ j, Q j ≠ 0) :
    ((shiftedExponentialMatrix b c Q).det).coeff
        (∑ j : Fin n, (Q j).natDegree) =
      (Matrix.vandermonde c).det * ∏ j : Fin n, (Q j).leadingCoeff := by
  rw [Matrix.det_apply]
  change (Polynomial.lcoeff ℚ (∑ j : Fin n, (Q j).natDegree))
      (∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
        ∏ i, shiftedExponentialMatrix b c Q (σ i) i) = _
  rw [map_sum]
  simp
  rw [← Matrix.det_transpose (Matrix.vandermonde c),
    Matrix.det_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  let F : Fin n → ℚ[X] := fun j =>
    shiftedExponentialMatrix b c Q (σ j) j
  have hF : ∀ j, F j ≠ 0 := by
    intro j
    apply mul_ne_zero
    · simp [hc]
    · exact Polynomial.comp_X_add_C_ne_zero_iff.mpr (hQ j)
  have hdeg : ∀ j, (F j).natDegree = (Q j).natDegree := by
    intro j
    have hscalar : Polynomial.C (c j ^ (σ j).val) ≠ (0 : ℚ[X]) := by
      exact Polynomial.C_ne_zero.mpr (pow_ne_zero _ (hc j))
    have hcomp : (Q j).comp
        (Polynomial.X + Polynomial.C (b * (σ j).val)) ≠ 0 :=
      Polynomial.comp_X_add_C_ne_zero_iff.mpr (hQ j)
    dsimp only [F, shiftedExponentialMatrix]
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
      ((Q j).comp (Polynomial.X + Polynomial.C (b * i.val))).leadingCoeff =
        (Q j).leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp]
    · rw [(Polynomial.monic_X_add_C (b * i.val)).leadingCoeff]
      simp
    · rw [Polynomial.natDegree_X_add_C]
      omega
  have hentryLC (j : Fin n) : (F j).leadingCoeff =
      c j ^ (σ j).val * (Q j).leadingCoeff := by
    dsimp only [F, shiftedExponentialMatrix]
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      hcompLC]
  rw [Finset.prod_congr rfl (fun j _ => hentryLC j)]
  rw [Finset.prod_mul_distrib]
  simp only [Matrix.transpose_apply, Matrix.vandermonde_apply]
  rw [smul_mul_assoc]

theorem shiftedExponentialMatrix_det_ne_zero {n : ℕ} (b : ℚ)
    (c : Fin n → ℚ) (Q : Fin n → ℚ[X])
    (hc : ∀ j, c j ≠ 0) (hcinj : Function.Injective c)
    (hQ : ∀ j, Q j ≠ 0) :
    (shiftedExponentialMatrix b c Q).det ≠ 0 := by
  intro hzero
  have hcoeff := shiftedExponentialMatrix_coeff_det b c Q hc hQ
  rw [hzero, Polynomial.coeff_zero] at hcoeff
  have hv : (Matrix.vandermonde c).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hcinj
  have hlead : (∏ j : Fin n, (Q j).leadingCoeff) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact Polynomial.leadingCoeff_ne_zero.mpr (hQ j)
  exact (mul_ne_zero hv hlead) hcoeff.symm

theorem shiftedExponentialMatrix_root_bound {n : ℕ} (b : ℚ)
    (c : Fin n → ℚ) (Q : Fin n → ℚ[X])
    (hc : ∀ j, c j ≠ 0) (hcinj : Function.Injective c)
    (hQ : ∀ j, Q j ≠ 0) (points : Finset ℚ)
    (hcard : (∑ j : Fin n, (Q j).natDegree) < points.card)
    (hkernel : ∀ x ∈ points, ∃ w : Fin n → ℚ, w ≠ 0 ∧
      Matrix.mulVec (Matrix.of fun (i j : Fin n) => c j ^ i.val *
        (Q j).eval (x + b * i.val)) w = 0) : False := by
  let Δ : ℚ[X] := (shiftedExponentialMatrix b c Q).det
  have hΔne : Δ ≠ 0 := shiftedExponentialMatrix_det_ne_zero b c Q hc hcinj hQ
  have heval : ∀ x ∈ points, Δ.eval x = 0 := by
    intro x hx
    obtain ⟨w, hw, hmul⟩ := hkernel x hx
    let A : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j =>
      c j ^ i.val * (Q j).eval (x + b * i.val)
    have hdet : A.det = 0 := by
      by_contra hdet
      exact hw (Matrix.eq_zero_of_mulVec_eq_zero hdet (by simpa [A] using hmul))
    have hmap : (shiftedExponentialMatrix b c Q).map
        (Polynomial.evalRingHom x) = A := by
      ext i j
      simp [A, shiftedExponentialMatrix, Polynomial.eval_comp]
    change (Polynomial.evalRingHom x) Δ = 0
    rw [show (Polynomial.evalRingHom x) Δ =
        ((shiftedExponentialMatrix b c Q).map
          (Polynomial.evalRingHom x)).det by
      simpa [Δ] using (RingHom.map_det (Polynomial.evalRingHom x)
        (shiftedExponentialMatrix b c Q))]
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
            have hscalar : Polynomial.C (c j ^ (σ j).val) ≠ (0 : ℚ[X]) := by
              exact Polynomial.C_ne_zero.mpr (pow_ne_zero _ (hc j))
            have hcomp : (Q j).comp
                (Polynomial.X + Polynomial.C (b * (σ j).val)) ≠ 0 :=
              Polynomial.comp_X_add_C_ne_zero_iff.mpr (hQ j)
            dsimp only [shiftedExponentialMatrix]
            rw [Polynomial.natDegree_mul hscalar hcomp,
              Polynomial.natDegree_C, Polynomial.natDegree_comp,
              Polynomial.natDegree_X_add_C]
            omega))
  exact hΔne (hz (hdeg.trans_lt hcard))

theorem exists_nonsingular_column_minor {N : ℕ} {C : Type*}
    [Fintype C] [DecidableEq C] (M : Matrix (Fin N) C ℚ)
    (hinj : Function.Injective M.transpose.mulVec) :
    ∃ f : Fin N → C, Function.Injective f ∧
      (M.submatrix id f).det ≠ 0 := by
  let F : (Fin N → ℚ) →ₗ[ℚ] C → ℚ := Matrix.toLin' M.transpose
  have hFinj : Function.Injective F := by
    intro x y hxy
    apply hinj
    simpa [F] using hxy
  obtain ⟨G, hGF⟩ := F.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hFinj)
  let A : Matrix (Fin N) C ℚ := LinearMap.toMatrix' G
  have hmul : A * M.transpose = 1 := by
    calc
      A * M.transpose = LinearMap.toMatrix' (G ∘ₗ F) := by
        rw [LinearMap.toMatrix'_comp]
        simp [A, F]
      _ = LinearMap.toMatrix' LinearMap.id := by rw [hGF]
      _ = 1 := LinearMap.toMatrix'_id
  have hsum := det_mul_eq_sum_functions A M.transpose
  rw [hmul, Matrix.det_one] at hsum
  have hsumne : (∑ f : Fin N → C,
      (∏ i, A i (f i)) * (M.transpose.submatrix f id).det) ≠ 0 := by
    rw [← hsum]
    norm_num
  obtain ⟨f, _, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
  have hminorT : (M.transpose.submatrix f id).det ≠ 0 := by
    exact fun hz => hf (by rw [hz, mul_zero])
  have hminor : (M.submatrix id f).det ≠ 0 := by
    have hmat : (M.transpose.submatrix f id).transpose = M.submatrix id f := by
      ext i j
      simp
    rw [← hmat, Matrix.det_transpose]
    exact hminorT
  refine ⟨f, ?_, hminor⟩
  intro i j hij
  by_contra hne
  apply hminor
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp [hij]

theorem translated_exponential_polynomial_zero_lemma {L : ℕ}
    (b base : ℚ) (hbase : 1 < base) (Q : Fin L → ℚ[X])
    (hQsome : ∃ l, Q l ≠ 0) (points : Finset ℚ)
    (hcard : (∑ l ∈ Finset.univ.filter (fun l : Fin L => Q l ≠ 0),
      (Q l).natDegree) < points.card)
    (y : ℚ → ℚ) (hy : ∀ x ∈ points, y x ≠ 0)
    (hzero : ∀ x ∈ points, ∀ r : Fin L,
      ∑ l : Fin L, base ^ (l.val * r.val) *
        (Q l).eval (x + b * r.val) * y x ^ l.val = 0) : False := by
  classical
  let support : Finset (Fin L) :=
    Finset.univ.filter fun l : Fin L => Q l ≠ 0
  let e : Fin support.card → Fin L := fun i => (support.equivFin.symm i).val
  let Q' : Fin support.card → ℚ[X] := fun i => Q (e i)
  let c : Fin support.card → ℚ := fun i => base ^ (e i).val
  have hQ' : ∀ i, Q' i ≠ 0 := by
    intro i
    exact (Finset.mem_filter.mp (support.equivFin.symm i).property).2
  have heinj : Function.Injective e := by
    intro i j hij
    apply support.equivFin.symm.injective
    exact Subtype.ext hij
  have hcinj : Function.Injective c := by
    intro i j hij
    apply heinj
    apply Fin.ext
    exact (pow_right_strictMono₀ hbase).injective hij
  have hc : ∀ i, c i ≠ 0 := by
    intro i
    exact pow_ne_zero _ (ne_of_gt (lt_trans zero_lt_one hbase))
  apply shiftedExponentialMatrix_root_bound b c Q' hc hcinj hQ' points
  · change (∑ i : Fin support.card, (Q (e i)).natDegree) < points.card
    rw [show (∑ i : Fin support.card, (Q (e i)).natDegree) =
        ∑ l ∈ support, (Q l).natDegree by
      calc
        (∑ i : Fin support.card, (Q (e i)).natDegree) =
            ∑ l : support, (Q l.val).natDegree := by
          simpa only [e] using support.equivFin.symm.sum_comp
            (fun l : support => (Q l.val).natDegree)
        _ = ∑ l ∈ support, (Q l).natDegree := by
          exact Finset.sum_attach support (fun l : Fin L => (Q l).natDegree)]
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
    have hsupportcard : support.card ≤ L := by
      simpa using Finset.card_le_univ support
    have hrlt : r.val < L := lt_of_lt_of_le r.isLt hsupportcard
    let r' : Fin L := ⟨r.val, hrlt⟩
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    let term : Fin L → ℚ := fun l =>
      base ^ (l.val * r.val) *
        (Q l).eval (x + b * r.val) * y x ^ l.val
    calc
      ∑ i : Fin support.card,
          c i ^ r.val * (Q' i).eval (x + b * r.val) * w i =
          ∑ i : Fin support.card, term (e i) := by
            apply Finset.sum_congr rfl
            intro i _
            simp [term, c, Q', w, pow_mul]
      _ = ∑ l : support, term l.val := by
        simpa only [e] using support.equivFin.symm.sum_comp
          (fun l : support => term l.val)
      _ = ∑ l ∈ support, term l := by
        exact Finset.sum_attach support term
      _ = ∑ l : Fin L, term l := by
        apply Finset.sum_subset (by simp)
        intro l _ hl
        have hQl : Q l = 0 := by simpa [support] using hl
        simp [term, hQl]
      _ = 0 := by
        simpa only [term, r', Fin.val_mk] using hzero x hx r'

theorem exists_nonsingular_column_minor_general {I C : Type*}
    [Fintype I] [DecidableEq I] [Fintype C] [DecidableEq C]
    (M : Matrix I C ℚ) (hinj : Function.Injective M.transpose.mulVec) :
    ∃ f : I → C, Function.Injective f ∧ (M.submatrix id f).det ≠ 0 := by
  let F : (I → ℚ) →ₗ[ℚ] C → ℚ := Matrix.toLin' M.transpose
  have hFinj : Function.Injective F := by
    intro x y hxy
    apply hinj
    simpa [F] using hxy
  obtain ⟨G, hGF⟩ := F.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hFinj)
  let A : Matrix I C ℚ := LinearMap.toMatrix' G
  have hmul : A * M.transpose = 1 := by
    calc
      A * M.transpose = LinearMap.toMatrix' (G ∘ₗ F) := by
        rw [LinearMap.toMatrix'_comp]
        simp [A, F]
      _ = LinearMap.toMatrix' LinearMap.id := by rw [hGF]
      _ = 1 := LinearMap.toMatrix'_id
  have hsum := det_mul_eq_sum_functions A M.transpose
  rw [hmul, Matrix.det_one] at hsum
  have hsumne : (∑ f : I → C,
      (∏ i, A i (f i)) * (M.transpose.submatrix f id).det) ≠ 0 := by
    rw [← hsum]
    norm_num
  obtain ⟨f, _, hf⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsumne
  have hminorT : (M.transpose.submatrix f id).det ≠ 0 := by
    exact fun hz => hf (by rw [hz, mul_zero])
  have hminor : (M.submatrix id f).det ≠ 0 := by
    have hmat : (M.transpose.submatrix f id).transpose = M.submatrix id f := by
      ext i j
      simp
    rw [← hmat, Matrix.det_transpose]
    exact hminorT
  refine ⟨f, ?_, hminor⟩
  intro i j hij
  by_contra hne
  apply hminor
  apply Matrix.det_zero_of_column_eq hne
  intro r
  simp [hij]

def coefficientPolynomial {K L : ℕ}
    (v : Fin K × Fin L → ℚ) (l : Fin L) : ℚ[X] :=
  ∑ k : Fin K, Polynomial.monomial k.val (v (k, l))

lemma coefficientPolynomial_eval {K L : ℕ}
    (v : Fin K × Fin L → ℚ) (l : Fin L) (x : ℚ) :
    (coefficientPolynomial v l).eval x = ∑ k : Fin K, v (k, l) * x ^ k.val := by
  change (Polynomial.evalRingHom x)
      (∑ k : Fin K, Polynomial.monomial k.val (v (k, l))) = _
  rw [map_sum]
  simp [Polynomial.eval_monomial, mul_comm]

lemma coefficientPolynomial_coeff {K L : ℕ}
    (v : Fin K × Fin L → ℚ) (l : Fin L) (k : Fin K) :
    (coefficientPolynomial v l).coeff k.val = v (k, l) := by
  unfold coefficientPolynomial
  rw [show (∑ j : Fin K, Polynomial.monomial j.val (v (j, l))) =
      ∑ j ∈ (Finset.univ : Finset (Fin K)),
        Polynomial.monomial j.val (v (j, l)) by rfl]
  rw [Polynomial.finsetSum_coeff]
  calc
    (∑ j : Fin K, (Polynomial.monomial j.val (v (j, l))).coeff k.val) =
        ∑ j : Fin K, if j = k then v (j, l) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Polynomial.coeff_monomial]
      by_cases hj : j = k
      · simp [hj]
      · have hval : j.val ≠ k.val := fun h => hj (Fin.ext h)
        simp [hj, hval]
    _ = v (k, l) := by simp

lemma coefficientPolynomial_natDegree_le {K L : ℕ} (hK : 0 < K)
    (v : Fin K × Fin L → ℚ) (l : Fin L) :
    (coefficientPolynomial v l).natDegree ≤ K - 1 := by
  unfold coefficientPolynomial
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  constructor
  · omega
  · intro k _
    exact (Polynomial.natDegree_monomial_le _).trans (by omega)

theorem exists_nonsingular_bivariate_monomial_minor {K L : ℕ}
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
        xcoord (f col) ^ row.1.val * ycoord (f col) ^ row.2.val)).det ≠ 0 := by
  let M : Matrix (Fin K × Fin L) C ℚ := fun row col =>
    xcoord col ^ row.1.val * ycoord col ^ row.2.val
  apply exists_nonsingular_column_minor_general M
  intro v w hvw
  let z : Fin K × Fin L → ℚ := v - w
  have hzmul : M.transpose.mulVec z = 0 := by
    rw [show z = v - w by rfl, Matrix.mulVec_sub, hvw, sub_self]
  have hz : z = 0 := by
    by_contra hz
    have hQsome : ∃ l : Fin L, coefficientPolynomial z l ≠ 0 := by
      have hzpoint : ∃ row : Fin K × Fin L, z row ≠ 0 := by
        obtain ⟨row, hrow⟩ := Function.ne_iff.mp hz
        exact ⟨row, by simpa using hrow⟩
      obtain ⟨⟨k, l⟩, hkl⟩ := hzpoint
      refine ⟨l, ?_⟩
      intro hzero
      have := congrArg (fun P : ℚ[X] => P.coeff k.val) hzero
      apply hkl
      simpa only [coefficientPolynomial_coeff, Polynomial.coeff_zero] using this
    refine translated_exponential_polynomial_zero_lemma b base hbase
      (coefficientPolynomial z) hQsome points ?_ y hy ?_
    · let s : Finset (Fin L) := Finset.univ.filter
          (fun l : Fin L => coefficientPolynomial z l ≠ 0)
      have hsCard : s.card ≤ L := by
        simpa using Finset.card_le_univ s
      have hsBound : (∑ l ∈ s, (coefficientPolynomial z l).natDegree) <
          points.card := by
        calc
          (∑ l ∈ s, (coefficientPolynomial z l).natDegree) ≤
              ∑ _l ∈ s, (K - 1) := by
                exact Finset.sum_le_sum (fun l _ =>
                  coefficientPolynomial_natDegree_le hK z l)
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
            (coefficientPolynomial z l).eval (x + b * r.val) *
              y x ^ l.val by
        rw [Fintype.sum_prod_type]
        simp_rw [M, hxcol x hx r, hycol x hx r,
          coefficientPolynomial_eval]
        simp_rw [mul_pow, pow_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro l _
        calc
          (∑ k : Fin K, (x + b * (r : ℕ)) ^ (k : ℕ) *
              (y x ^ (l : ℕ) * (base ^ (r : ℕ)) ^ (l : ℕ)) * z (k, l)) =
              (∑ k : Fin K, (base ^ (l : ℕ)) ^ (r : ℕ) *
                (z (k, l) * (x + b * (r : ℕ)) ^ (k : ℕ))) *
                  y x ^ (l : ℕ) := by
            have hp : (base ^ (r : ℕ)) ^ (l : ℕ) =
                (base ^ (l : ℕ)) ^ (r : ℕ) := by
              simp only [← pow_mul]
              rw [Nat.mul_comm]
            rw [hp]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _
            ring
          _ = ((base ^ (l : ℕ)) ^ (r : ℕ) *
                ∑ k : Fin K, z (k, l) * (x + b * (r : ℕ)) ^ (k : ℕ)) *
                  y x ^ (l : ℕ) := by
            apply congrArg (fun t : ℚ => t * y x ^ (l : ℕ))
            rw [Finset.mul_sum]]
      exact hc
  simpa [z, sub_eq_zero] using hz

end Erdos1058.BugeaudLaurent
