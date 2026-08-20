/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos407.RothIndex

/-!
# Small integral nonvanishing points

This file proves the finite-grid nonvanishing lemma used in the last (nonvanishing)
step of the rational Subspace Theorem.  The derivative is the divided, or Hasse,
derivative: its value is a coefficient of the polynomial after translation.
-/

namespace Erdos407.SmallIntegerNonvanishing

open scoped BigOperators

noncomputable section

open Erdos407.RothIndex

/-! ## A univariate multiplicity lemma -/

/-- A nonzero polynomial whose degree is less than `(q+1) * #S` has, at one
point of `S`, a nonzero Hasse derivative of order at most `q`.

This is Hermite interpolation in the exact weak form needed below.  The proof
counts every point at which all these derivatives vanish with multiplicity at
least `q+1` in the multiset of roots. -/
theorem exists_hasseDeriv_eval_ne_zero_of_natDegree_lt
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (p : Polynomial R) (hp : p ≠ 0) (S : Finset R) (q : ℕ)
    (hdeg : p.natDegree < (q + 1) * S.card) :
    ∃ a ∈ S, ∃ k ≤ q, Polynomial.eval a (Polynomial.hasseDeriv k p) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hmult : ∀ a ∈ S, q + 1 ≤ p.roots.count a := by
    intro a ha
    rw [Polynomial.count_roots]
    apply Nat.succ_le_iff.mpr
    rw [Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative hp]
    intro k hk
    rw [Polynomial.IsRoot]
    have hfac := congrFun (Polynomial.factorial_smul_hasseDeriv (R := R) k) p
    simp only [LinearMap.smul_apply] at hfac
    rw [← hfac, Polynomial.eval_smul, h a ha k hk]
    simp
  have hsubset : S ⊆ p.roots.toFinset := by
    intro a ha
    rw [Multiset.mem_toFinset, ← Multiset.count_pos]
    exact (Nat.zero_lt_succ q).trans_le (hmult a ha)
  have hcount : (q + 1) * S.card ≤ p.roots.card := by
    calc
      (q + 1) * S.card = ∑ a ∈ S, (q + 1) := by simp [Nat.mul_comm]
      _ ≤ ∑ a ∈ S, p.roots.count a := by
        exact Finset.sum_le_sum fun a ha ↦ hmult a ha
      _ ≤ ∑ a ∈ p.roots.toFinset, p.roots.count a := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ ↦ Nat.zero_le _)
      _ = p.roots.card := Multiset.toFinset_sum_count_eq _
  exact (not_lt_of_ge (hcount.trans p.card_roots')) hdeg

/-! ## Translation and the first variable -/

/-- Translation of multivariate polynomials, as a rational algebra homomorphism. -/
def translateAlgHom {ι : Type*} (x : ι → ℚ) :
    MvPolynomial ι ℚ →ₐ[ℚ] MvPolynomial ι ℚ :=
  { MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i ↦ MvPolynomial.X i + MvPolynomial.C (x i)) with
    commutes' := fun r ↦ by simp }

@[simp] theorem translateAlgHom_apply {ι : Type*} (x : ι → ℚ)
    (P : MvPolynomial ι ℚ) :
    translateAlgHom x P = translate x P := by
  rfl

@[simp] theorem translateAlgHom_C {ι : Type*} (x : ι → ℚ) (a : ℚ) :
    translateAlgHom x (MvPolynomial.C a) = MvPolynomial.C a := by
  simp [translateAlgHom]

@[simp] theorem translateAlgHom_X {ι : Type*} (x : ι → ℚ) (i : ι) :
    translateAlgHom x (MvPolynomial.X i) =
      MvPolynomial.X i + MvPolynomial.C (x i) := by
  simp [translateAlgHom]

/-- Under `finSuccEquiv`, simultaneous translation is ordinary Taylor
translation in the first variable followed by translation of every
coefficient in the remaining variables. -/
theorem finSuccEquiv_translate {n : ℕ} (a : ℚ) (x : Fin n → ℚ)
    (P : MvPolynomial (Fin (n + 1)) ℚ) :
    MvPolynomial.finSuccEquiv ℚ n (translate (Fin.cons a x) P) =
      Polynomial.map (translateAlgHom x).toRingHom
        (Polynomial.taylor (MvPolynomial.C a)
          (MvPolynomial.finSuccEquiv ℚ n P)) := by
  let F : MvPolynomial (Fin (n + 1)) ℚ →ₐ[ℚ]
      Polynomial (MvPolynomial (Fin n) ℚ) :=
    (MvPolynomial.finSuccEquiv ℚ n).toAlgHom.comp
      (translateAlgHom (Fin.cons a x))
  let T : Polynomial (MvPolynomial (Fin n) ℚ) →ₐ[ℚ]
      Polynomial (MvPolynomial (Fin n) ℚ) :=
    (Polynomial.taylorAlgHom (MvPolynomial.C a)).restrictScalars ℚ
  let G : MvPolynomial (Fin (n + 1)) ℚ →ₐ[ℚ]
      Polynomial (MvPolynomial (Fin n) ℚ) :=
    (Polynomial.mapAlgHom (translateAlgHom x)).comp
      (T.comp (MvPolynomial.finSuccEquiv ℚ n).toAlgHom)
  have hFG : F = G := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [F, G, T, Polynomial.taylor_apply,
        MvPolynomial.finSuccEquiv_X_zero]
      exact (MvPolynomial.finSuccEquiv ℚ n).commutes a
    · simp [F, G, T, Polynomial.taylor_apply,
        MvPolynomial.finSuccEquiv_X_succ]
      exact (MvPolynomial.finSuccEquiv ℚ n).commutes (x j)
  exact DFunLike.congr_fun hFG P

/-- Coefficients after full translation split into the first-variable Hasse
derivative followed by translation in the remaining variables. -/
theorem coeff_finSuccEquiv_translate {n : ℕ} (a : ℚ) (x : Fin n → ℚ)
    (P : MvPolynomial (Fin (n + 1)) ℚ) (k : ℕ) :
    Polynomial.coeff
        (MvPolynomial.finSuccEquiv ℚ n (translate (Fin.cons a x) P)) k =
      translate x
        (Polynomial.eval (MvPolynomial.C a)
          (Polynomial.hasseDeriv k (MvPolynomial.finSuccEquiv ℚ n P))) := by
  rw [finSuccEquiv_translate, Polynomial.coeff_map, Polynomial.taylor_coeff]
  exact translateAlgHom_apply _ _

/-- The multivariate Hasse coefficient at a `Fin.cons` point is the tail
Hasse coefficient of the first-variable Hasse coefficient polynomial. -/
theorem hasseCoeff_cons {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℚ)
    (a : ℚ) (x : Fin n → ℚ) (k : ℕ) (I : Fin n →₀ ℕ) :
    hasseCoeff P (Fin.cons a x) (Finsupp.cons k I) =
      hasseCoeff
        (Polynomial.eval (MvPolynomial.C a)
          (Polynomial.hasseDeriv k (MvPolynomial.finSuccEquiv ℚ n P))) x I := by
  unfold hasseCoeff
  rw [← MvPolynomial.finSuccEquiv_coeff_coeff I (translate (Fin.cons a x) P) k]
  rw [coeff_finSuccEquiv_translate]

/-! ## Coordinatewise degree control -/

/-- Taking a Hasse derivative in the first variable and evaluating that
variable cannot increase the degree in any remaining variable. -/
theorem degreeOf_eval_hasseDeriv_finSucc_le {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℚ) (a : ℚ) (k : ℕ) (j : Fin n) :
    MvPolynomial.degreeOf j
        (Polynomial.eval (MvPolynomial.C a)
          (Polynomial.hasseDeriv k (MvPolynomial.finSuccEquiv ℚ n P))) ≤
      MvPolynomial.degreeOf j.succ P := by
  classical
  rw [Polynomial.hasseDeriv_apply, Polynomial.eval_sum, Polynomial.sum_def]
  refine (MvPolynomial.degreeOf_sum_le j _ _).trans ?_
  apply Finset.sup_le
  intro i hi
  simp only [Polynomial.eval_monomial]
  calc
    MvPolynomial.degreeOf j
        ((i.choose k : MvPolynomial (Fin n) ℚ) *
            (MvPolynomial.finSuccEquiv ℚ n P).coeff i *
          MvPolynomial.C a ^ (i - k)) ≤
        MvPolynomial.degreeOf j
            ((i.choose k : MvPolynomial (Fin n) ℚ) *
              (MvPolynomial.finSuccEquiv ℚ n P).coeff i) +
          MvPolynomial.degreeOf j (MvPolynomial.C a ^ (i - k)) :=
      MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ MvPolynomial.degreeOf j
        ((MvPolynomial.finSuccEquiv ℚ n P).coeff i) := by
      have hleft :
          MvPolynomial.degreeOf j
              ((i.choose k : MvPolynomial (Fin n) ℚ) *
                (MvPolynomial.finSuccEquiv ℚ n P).coeff i) ≤
            MvPolynomial.degreeOf j
              ((MvPolynomial.finSuccEquiv ℚ n P).coeff i) := by
        have hconst :
            MvPolynomial.degreeOf j
                (i.choose k : MvPolynomial (Fin n) ℚ) = 0 := by
          simpa only [map_natCast] using
            (MvPolynomial.degreeOf_C (σ := Fin n) (i.choose k : ℚ) j)
        refine (MvPolynomial.degreeOf_mul_le j _ _).trans ?_
        simp [hconst]
      have hright :
          MvPolynomial.degreeOf j (MvPolynomial.C a ^ (i - k)) = 0 := by
        apply Nat.eq_zero_of_le_zero
        simpa using
          (MvPolynomial.degreeOf_pow_le j (MvPolynomial.C a) (i - k))
      simpa [hright] using Nat.add_le_add_right hleft
    _ ≤ MvPolynomial.degreeOf j.succ P :=
      MvPolynomial.degreeOf_coeff_finSuccEquiv P j i

/-! ## The multivariate finite-grid lemma -/

/-- Multivariate Hermite interpolation on a Cartesian grid.  If the degree in
coordinate `i` is strictly less than `(q i + 1) * #S`, a nonzero polynomial
has a nonzero Hasse coefficient of coordinatewise order at most `q` at some
point of `S^n`.

The proof is a genuine induction over the variables.  At the first variable
the univariate multiplicity lemma selects a low Hasse derivative which is
still a nonzero polynomial in the remaining variables; the preceding degree
lemma supplies the induction bounds. -/
theorem exists_gridPoint_hasseCoeff_ne_zero {n : ℕ}
    (P : MvPolynomial (Fin n) ℚ) (hP : P ≠ 0)
    (S : Finset ℚ) (q : Fin n → ℕ)
    (hdeg : ∀ i, MvPolynomial.degreeOf i P < (q i + 1) * S.card) :
    ∃ x : Fin n → ℚ,
      (∀ i, x i ∈ S) ∧
      ∃ I : Fin n →₀ ℕ,
        (∀ i, I i ≤ q i) ∧ hasseCoeff P x I ≠ 0 := by
  induction n with
  | zero =>
      let x : Fin 0 → ℚ := fun i ↦ Fin.elim0 i
      obtain ⟨I, hI⟩ := exists_hasseCoeff_ne_zero hP x
      refine ⟨x, ?_, I, ?_, hI⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ n ih =>
      let p : Polynomial (MvPolynomial (Fin n) ℚ) :=
        MvPolynomial.finSuccEquiv ℚ n P
      have hp : p ≠ 0 := by
        intro hp0
        apply hP
        apply (MvPolynomial.finSuccEquiv ℚ n).injective
        simpa [p] using hp0
      let S' : Finset (MvPolynomial (Fin n) ℚ) :=
        S.image MvPolynomial.C
      have hcard : S'.card = S.card := by
        exact Finset.card_image_of_injective S
          (MvPolynomial.C_injective (Fin n) ℚ)
      have hpdeg : p.natDegree < (q 0 + 1) * S'.card := by
        rw [hcard, show p = MvPolynomial.finSuccEquiv ℚ n P from rfl,
          MvPolynomial.natDegree_finSuccEquiv]
        exact hdeg 0
      obtain ⟨A, hA, k, hk, hQ⟩ :=
        exists_hasseDeriv_eval_ne_zero_of_natDegree_lt p hp S' (q 0) hpdeg
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
      let Q : MvPolynomial (Fin n) ℚ :=
        Polynomial.eval (MvPolynomial.C a) (Polynomial.hasseDeriv k p)
      have hQ' : Q ≠ 0 := by
        simpa [Q] using hQ
      have hQdeg : ∀ j : Fin n,
          MvPolynomial.degreeOf j Q < (q j.succ + 1) * S.card := by
        intro j
        exact (degreeOf_eval_hasseDeriv_finSucc_le P a k j).trans_lt (hdeg j.succ)
      obtain ⟨x, hx, I, hI, hnonzero⟩ :=
        ih Q hQ' (fun j ↦ q j.succ) hQdeg
      refine ⟨Fin.cons a x, ?_, Finsupp.cons k I, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simpa using ha
        · simpa using hx j
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simpa using hk
        · simpa using hI j
      · rw [hasseCoeff_cons]
        simpa [Q, p] using hnonzero

/-! ## A bounded integral grid -/

/-- The rational images of the integers `0, ..., B`. -/
def nonnegativeIntegerGrid (B : ℕ) : Finset ℚ :=
  (Finset.range (B + 1)).image fun k : ℕ ↦ (k : ℚ)

@[simp] theorem card_nonnegativeIntegerGrid (B : ℕ) :
    (nonnegativeIntegerGrid B).card = B + 1 := by
  rw [nonnegativeIntegerGrid,
    Finset.card_image_of_injective _ (Nat.cast_injective :
      Function.Injective (fun k : ℕ ↦ (k : ℚ)))]
  simp

theorem mem_nonnegativeIntegerGrid {B : ℕ} {x : ℚ} :
    x ∈ nonnegativeIntegerGrid B ↔ ∃ k ≤ B, x = (k : ℚ) := by
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨k, Nat.le_of_lt_succ (Finset.mem_range.mp hk), rfl⟩
  · rintro ⟨k, hk, rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩

/-- **Small integer nonvanishing lemma (GLR Lemma 5.1, finite-grid
form).**  A nonzero rational polynomial admits a nonzero Hasse coefficient
at an integral point in the box `|z_i| ≤ B`.  In coordinate `i`, the Hasse
order is at most `degreeOf i P / (B+1)`.

The denominator `B+1` is slightly stronger than the usual displayed bound
`degreeOf i P / B` (for `B ≥ 1`), and comes from using all `B+1` integers in
the nonnegative half of the box. -/
theorem exists_smallInteger_hasseCoeff_ne_zero {n : ℕ}
    (P : MvPolynomial (Fin n) ℚ) (hP : P ≠ 0) (B : ℕ) :
    ∃ z : Fin n → ℤ,
      (∀ i, |z i| ≤ (B : ℤ)) ∧
      ∃ I : Fin n →₀ ℕ,
        (∀ i, I i ≤ MvPolynomial.degreeOf i P / (B + 1)) ∧
        hasseCoeff P (fun i ↦ (z i : ℚ)) I ≠ 0 := by
  let q : Fin n → ℕ := fun i ↦ MvPolynomial.degreeOf i P / (B + 1)
  have hdeg : ∀ i,
      MvPolynomial.degreeOf i P <
        (q i + 1) * (nonnegativeIntegerGrid B).card := by
    intro i
    rw [card_nonnegativeIntegerGrid]
    simpa [q, Nat.mul_comm] using
      (Nat.lt_mul_div_succ (MvPolynomial.degreeOf i P) (Nat.succ_pos B))
  obtain ⟨x, hx, I, hI, hnonzero⟩ :=
    exists_gridPoint_hasseCoeff_ne_zero P hP
      (nonnegativeIntegerGrid B) q hdeg
  choose k hk hxk using fun i ↦ mem_nonnegativeIntegerGrid.mp (hx i)
  let z : Fin n → ℤ := fun i ↦ (k i : ℤ)
  have hxz : x = fun i ↦ (z i : ℚ) := by
    funext i
    simpa [z] using hxk i
  refine ⟨z, ?_, I, ?_, ?_⟩
  · intro i
    have hkz : (k i : ℤ) ≤ (B : ℤ) := by
      exact_mod_cast hk i
    simpa [z, abs_of_nonneg] using hkz
  · intro i
    simpa [q] using hI i
  · simpa [hxz] using hnonzero

/-- The more customary `degree / B` bound, for a positive box radius. -/
theorem exists_smallInteger_hasseCoeff_ne_zero_div {n : ℕ}
    (P : MvPolynomial (Fin n) ℚ) (hP : P ≠ 0) {B : ℕ} (hB : 1 ≤ B) :
    ∃ z : Fin n → ℤ,
      (∀ i, |z i| ≤ (B : ℤ)) ∧
      ∃ I : Fin n →₀ ℕ,
        (∀ i, I i ≤ MvPolynomial.degreeOf i P / B) ∧
        hasseCoeff P (fun i ↦ (z i : ℚ)) I ≠ 0 := by
  obtain ⟨z, hz, I, hI, hnonzero⟩ :=
    exists_smallInteger_hasseCoeff_ne_zero P hP B
  refine ⟨z, hz, I, ?_, hnonzero⟩
  intro i
  exact (hI i).trans
    (Nat.div_le_div_left (Nat.le_add_right B 1) (by omega : 0 < B))

end

end Erdos407.SmallIntegerNonvanishing
