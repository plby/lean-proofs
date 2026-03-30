/-
  Formalization of results from MO509493a.tex

  Given real n×n orthogonal projection matrices P₁, P₂ (i.e., P² = P = Pᵀ)
  of the same rank (hence unitarily equivalent), define
    A := (P₁P₂) ∘ (P₂P₁)
  where ∘ denotes the Hadamard (entrywise) product.

  We formalize several results about the power-nonnegativity of A,
  an explicit counterexample for n=4, k=3, and minimality results.
-/

import Mathlib

namespace MO509493

open Matrix Finset BigOperators

/-! ## Definitions -/

/-- An orthogonal projection matrix: a real matrix satisfying P² = P = Pᵀ. -/
def IsOrthProj {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ) : Prop :=
  P * P = P ∧ Pᵀ = P

/-- Two real matrices are orthogonally equivalent if one can be obtained from the other
    by conjugation with an orthogonal matrix. -/
def IsOrthEquiv {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) : Prop :=
  ∃ Q : Matrix n n ℝ, Q * Qᵀ = 1 ∧ Qᵀ * Q = 1 ∧ B = Q * A * Qᵀ

/-- Two matrices over a star ring are unitarily equivalent if one can be obtained from
    the other by conjugation with a unitary matrix. -/
def IsUnitEquiv {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [CommSemiring 𝕜]
    [StarRing 𝕜] (A B : Matrix n n 𝕜) : Prop :=
  ∃ U : Matrix n n 𝕜, U * star U = 1 ∧ star U * U = 1 ∧ B = U * A * star U

/-- Over `ℝ`, orthogonal equivalence and unitary equivalence coincide. -/
lemma isOrthEquiv_iff_isUnitEquiv {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) : IsOrthEquiv A B ↔ IsUnitEquiv A B := by
  have key : ∀ (Q : Matrix n n ℝ), star Q = Qᵀ := by
    intro Q; ext; simp [star_apply, star_trivial]
  simp only [IsOrthEquiv, IsUnitEquiv, key]

/-- A matrix is power-nonnegative if tr(Xᵐ) ≥ 0 for every m ≥ 0. -/
def IsPowerNonneg {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℝ) : Prop :=
  ∀ m : ℕ, 0 ≤ (X ^ m).trace

/-- The Hadamard-square construction A = (P₁P₂) ∘ (P₂P₁). -/
noncomputable def hadamardSquare {n : Type*} [Fintype n] [DecidableEq n]
    (P₁ P₂ : Matrix n n ℝ) : Matrix n n ℝ :=
  (P₁ * P₂).hadamard (P₂ * P₁)

/-- A counterexample to power-nonnegativity of the Hadamard-square construction
    at dimension `n` and exponent `k` is a matrix `A` that arises as a Hadamard square
    of two unitarily equivalent orthogonal projections, with `tr(Aᵏ) < 0`. -/
def IsCounterexample (n : ℕ) (k : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ (P₁ P₂ : Matrix (Fin n) (Fin n) ℝ),
    IsOrthProj P₁ ∧ IsOrthProj P₂ ∧ IsUnitEquiv P₁ P₂ ∧
    A = hadamardSquare P₁ P₂ ∧ ¬ (0 ≤ (A ^ k).trace)

/-! ## Proposition 1: Orthogonal projections are unitarily equivalent iff same rank -/

/-
PROBLEM
Two orthogonal projection matrices of the same size are unitarily (in fact orthogonally)
    equivalent if and only if they have the same rank.

PROVIDED SOLUTION
Forward direction: If P₂ = Q P₁ Qᵀ with Q orthogonal, then rank(P₂) = rank(P₁) since Q is invertible. This uses LinearMap.rank_eq_of_mul_eq_one or similar.

Backward direction: If rank(P₁) = rank(P₂) = r, use the spectral theorem for real symmetric idempotent matrices. Since P is symmetric and P² = P, all eigenvalues are 0 or 1, and the eigenvalue 1 has multiplicity r. So there exist orthogonal Q₁, Q₂ with Q₁ᵀ P₁ Q₁ = diag(I_r, 0) = Q₂ᵀ P₂ Q₂. Then P₂ = (Q₂Q₁ᵀ) P₁ (Q₂Q₁ᵀ)ᵀ. This is very involved in Lean/Mathlib.
-/
set_option maxHeartbeats 800000 in
theorem orthProj_equiv_iff_rank {n : Type*} [Fintype n] [DecidableEq n]
    (P₁ P₂ : Matrix n n ℝ) (h₁ : IsOrthProj P₁) (h₂ : IsOrthProj P₂) :
    P₁.rank = P₂.rank ↔ IsOrthEquiv P₁ P₂ := by
  unfold IsOrthEquiv
  constructor;
  · -- If $P_1$ and $P_2$ are orthogonal projections with the same rank, then they are similar.
    intro h_rank
    have h_similar : ∃ Q : Matrix n n ℝ, Q * Qᵀ = 1 ∧ Qᵀ * Q = 1 ∧ P₂ = Q * P₁ * Qᵀ := by
      have h_unitary : ∃ R : Matrix n n ℝ, R * Rᵀ = 1 ∧ Rᵀ * R = 1 ∧ P₂ = R * P₁ * Rᵀ := by
        -- Since $P_1$ and $P_2$ are orthogonal projections, they are diagonalizable with eigenvalues $0$ or $1$.
        have h_diag : ∀ (P : Matrix n n ℝ), IsOrthProj P → ∃ D : Matrix n n ℝ, D * Dᵀ = 1 ∧ Dᵀ * D = 1 ∧ ∃ (d : n → ℝ), (∀ i, d i = 0 ∨ d i = 1) ∧ P = D * Matrix.diagonal d * Dᵀ := by
          intro P hP;
          -- Since $P$ is a real symmetric matrix, it is diagonalizable.
          have h_diag : ∃ D : Matrix n n ℝ, D * Dᵀ = 1 ∧ Dᵀ * D = 1 ∧ ∃ (d : n → ℝ), P = D * Matrix.diagonal d * Dᵀ := by
            have h_diag : Matrix.IsHermitian P := by
              exact hP.2;
            have := h_diag.spectral_theorem;
            refine' ⟨ _, _, _, _, this ⟩;
            · convert h_diag.eigenvectorUnitary.2.2 using 1;
            · simp +decide [ mul_eq_one_comm ];
              convert h_diag.eigenvectorUnitary.2.2 using 1;
          obtain ⟨ D, hD₁, hD₂, d, rfl ⟩ := h_diag;
          refine' ⟨ D, hD₁, hD₂, d, _, rfl ⟩;
          intro i
          have h_diag_eq : (D * Matrix.diagonal d * Dᵀ) * (D * Matrix.diagonal d * Dᵀ) = D * Matrix.diagonal d * Dᵀ := by
            exact hP.1;
          replace h_diag_eq := congr_arg ( fun m => Dᵀ * m * D ) h_diag_eq ; simp_all +decide [ Matrix.mul_assoc ];
          simp_all +decide [ ← Matrix.mul_assoc ];
          exact or_iff_not_imp_left.mpr fun hi => mul_left_cancel₀ hi <| by linarith [ h_diag_eq i ] ;
        obtain ⟨ D₁, hD₁₁, hD₁₂, d₁, hd₁, rfl ⟩ := h_diag P₁ h₁
        obtain ⟨ D₂, hD₂₁, hD₂₂, d₂, hd₂, rfl ⟩ := h_diag P₂ h₂
        have h_eigenvalues : (∑ i, if d₁ i = 1 then 1 else 0) = (∑ i, if d₂ i = 1 then 1 else 0) := by
          have h_eigenvalues : Matrix.rank (D₁ * Matrix.diagonal d₁ * D₁ᵀ) = ∑ i, if d₁ i = 1 then 1 else 0 := by
            have h_eigenvalues : Matrix.rank (D₁ * Matrix.diagonal d₁ * D₁ᵀ) = Matrix.rank (Matrix.diagonal d₁) := by
              have h_eigenvalues : Matrix.rank (D₁ * Matrix.diagonal d₁ * D₁ᵀ) = Matrix.rank (Matrix.diagonal d₁ * D₁ᵀ) := by
                have h_eigenvalues : ∀ (A : Matrix n n ℝ), Matrix.rank (D₁ * A) = Matrix.rank A := by
                  intro A
                  have h_eigenvalues : Matrix.rank (D₁ * A) ≤ Matrix.rank A := by
                    exact Matrix.rank_mul_le_right _ _
                  have h_eigenvalues' : Matrix.rank A ≤ Matrix.rank (D₁ * A) := by
                    have := Matrix.rank_mul_le ( D₁ᵀ ) ( D₁ * A ) ; simp_all +decide [ ← Matrix.mul_assoc ] ;
                  exact le_antisymm h_eigenvalues h_eigenvalues'
                generalize_proofs at *; (
                rw [ Matrix.mul_assoc, h_eigenvalues ]);
              rw [ h_eigenvalues ];
              refine' le_antisymm _ _;
              · exact Matrix.rank_mul_le_left _ _ |> le_trans <| by simp +decide
              · have := Matrix.rank_mul_le ( diagonal d₁ * D₁ᵀ ) D₁; simp_all +decide [ Matrix.mul_assoc ] ;
            rw [ h_eigenvalues, Matrix.rank_diagonal ];
            simp +decide [ Fintype.card_subtype ];
            exact congr_arg Finset.card ( Finset.ext fun x => by cases hd₁ x <;> simp +decide [ * ] )
          have h_eigenvalues' : Matrix.rank (D₂ * Matrix.diagonal d₂ * D₂ᵀ) = ∑ i, if d₂ i = 1 then 1 else 0 := by
            have h_eigenvalues' : Matrix.rank (D₂ * Matrix.diagonal d₂ * D₂ᵀ) = Matrix.rank (Matrix.diagonal d₂) := by
              have h_eigenvalues' : Matrix.rank (D₂ * Matrix.diagonal d₂ * D₂ᵀ) = Matrix.rank (Matrix.diagonal d₂ * D₂ᵀ) := by
                rw [ Matrix.mul_assoc ];
                refine' le_antisymm _ _ <;> simp_all +decide [ Matrix.rank_mul_le_right ];
                have := Matrix.rank_mul_le ( D₂ᵀ ) ( D₂ * ( diagonal d₂ * D₂ᵀ ) ) ; simp_all +decide [ Matrix.mul_assoc ] ;
                grind +splitImp;
              have := Matrix.rank_mul_le ( diagonal d₂ * D₂ᵀ ) D₂; simp_all +decide [ Matrix.mul_assoc ] ;
              exact le_antisymm ( Matrix.rank_mul_le_left _ _ ) this.1;
            simp_all +decide [ Matrix.rank_diagonal ];
            rw [ Fintype.card_subtype ];
            rw [ tsub_eq_of_eq_add_rev ] ; rw [ ← Finset.card_union_of_disjoint ( Finset.disjoint_filter.mpr fun _ _ _ => by aesop ) ] ; rw [ Finset.filter_union_right ] ; aesop;
          aesop
        have h_perm : ∃ σ : n ≃ n, ∀ i, d₂ (σ i) = d₁ i := by
          -- Since $d₁$ and $d₂$ are both diagonal matrices with entries $0$ or $1$, and their sums are equal, there must be a bijection between the indices where $d₁$ is $1$ and the indices where $d₂$ is $1$.
          have h_bij : ∃ σ : {i | d₁ i = 1} ≃ {i | d₂ i = 1}, True := by
            simp_all +decide
            exact ⟨ Fintype.equivOfCardEq <| by simpa [ Fintype.card_subtype ] using h_eigenvalues ⟩;
          obtain ⟨σ, hσ⟩ := h_bij
          have h_bij_compl : ∃ τ : {i | d₁ i = 0} ≃ {i | d₂ i = 0}, True := by
            have h_bij_compl : Finset.card (Finset.filter (fun i => d₁ i = 0) Finset.univ) = Finset.card (Finset.filter (fun i => d₂ i = 0) Finset.univ) := by
              have h_compl : Finset.card (Finset.filter (fun i => d₁ i = 0) Finset.univ) = Finset.card (Finset.univ : Finset n) - Finset.card (Finset.filter (fun i => d₁ i = 1) Finset.univ) ∧ Finset.card (Finset.filter (fun i => d₂ i = 0) Finset.univ) = Finset.card (Finset.univ : Finset n) - Finset.card (Finset.filter (fun i => d₂ i = 1) Finset.univ) := by
                exact ⟨ eq_tsub_of_add_eq <| by rw [ ← Finset.card_union_of_disjoint ( Finset.disjoint_filter.mpr fun _ _ _ => by aesop ) ] ; congr ; ext i ; cases hd₁ i <;> aesop, eq_tsub_of_add_eq <| by rw [ ← Finset.card_union_of_disjoint ( Finset.disjoint_filter.mpr fun _ _ _ => by aesop ) ] ; congr ; ext i ; cases hd₂ i <;> aesop ⟩;
              aesop;
            exact ⟨ Fintype.equivOfCardEq ( by simpa [ Fintype.card_subtype ] using h_bij_compl ), trivial ⟩
          obtain ⟨τ, hτ⟩ := h_bij_compl
          use Equiv.ofBijective (fun i => if hi : d₁ i = 1 then σ ⟨i, hi⟩ else τ ⟨i, by
            exact Or.resolve_right ( hd₁ i ) hi⟩) (by
          constructor;
          · intro i j hij; cases hd₁ i <;> cases hd₁ j <;> simp_all +decide ;
            · exact congr_arg Subtype.val ( τ.injective ( Subtype.ext hij ) );
            · grind;
            · grind +ring;
            · simpa [ Subtype.ext_iff ] using σ.injective ( Subtype.ext hij );
          · intro i
            by_cases hi : d₂ i = 1
            all_goals generalize_proofs at *;
            · obtain ⟨ j, hj ⟩ := σ.surjective ⟨ i, hi ⟩;
              grind;
            · use τ.symm ⟨i, by
                exact Or.resolve_right ( hd₂ i ) hi⟩
              generalize_proofs at *;
              grind +splitImp);
          grind
        obtain ⟨ σ, hσ ⟩ := h_perm
        use D₂ * (Matrix.of (fun i j => if σ j = i then 1 else 0)) * D₁ᵀ
        simp_all +decide [ Matrix.mul_assoc, mul_eq_one_comm ];
        simp_all +decide [ ← Matrix.mul_assoc, mul_eq_one_comm.mp hD₁₁, mul_eq_one_comm.mp hD₂₁ ];
        refine' ⟨ _, _, _ ⟩;
        · convert hD₂₁ using 1;
          ext i j; simp +decide [ Matrix.mul_apply, Matrix.transpose_apply ] ;
          rw [ ← Equiv.sum_comp σ ] ; simp +decide ;
          conv_rhs => rw [ ← Equiv.sum_comp σ ] ;
        · simp_all +decide [ ← Matrix.ext_iff ];
          simp_all +decide [ Matrix.mul_apply, Matrix.one_apply ];
        · ext i j; simp +decide [ Matrix.mul_apply ] ; ring_nf;
          simp +decide [ Matrix.diagonal, Finset.sum_ite ];
          simp +decide [ ← hσ, Finset.sum_filter ];
          exact Finset.sum_congr rfl fun x _ => by rw [ Finset.sum_eq_single ( σ.symm x ) ] <;> aesop;
      exact h_unitary;
    exact h_similar;
  · rintro ⟨ Q, hQ₁, hQ₂, rfl ⟩;
    simp +decide [ Matrix.mul_assoc ];
    refine' le_antisymm _ _;
    · have := Matrix.rank_mul_le ( Qᵀ ) ( Q * ( P₁ * Qᵀ ) ) ; simp_all +decide [ ← mul_assoc ] ;
      have := Matrix.rank_mul_le ( P₁ * Qᵀ ) Q; simp_all +decide
      grind +extAll;
    · exact Matrix.rank_mul_le_right _ _ |> le_trans <| Matrix.rank_mul_le_left _ _

set_option maxHeartbeats 800000 in
/-- Two orthogonal projections are unitarily equivalent if and only if they have
    the same rank. This is the unitary-equivalence version of `orthProj_equiv_iff_rank`. -/
theorem orthProj_unitEquiv_iff_rank {n : Type*} [Fintype n] [DecidableEq n]
    (P₁ P₂ : Matrix n n ℝ) (h₁ : IsOrthProj P₁) (h₂ : IsOrthProj P₂) :
    P₁.rank = P₂.rank ↔ IsUnitEquiv P₁ P₂ := by
  rw [orthProj_equiv_iff_rank P₁ P₂ h₁ h₂, isOrthEquiv_iff_isUnitEquiv]

/-! ## Proposition 5: tr(A) ≥ 0 -/

/-
PROBLEM
For any matrices P₁, P₂, the trace of A = (P₁P₂) ∘ (P₂P₁) is nonneg,
    since the diagonal entries of A are squares.

PROVIDED SOLUTION
Unfold hadamardSquare and trace. The trace of A = (P₁P₂) ∘ (P₂P₁) is ∑ᵢ (P₁P₂)ᵢᵢ · (P₂P₁)ᵢᵢ. Since P₁ᵀ = P₁ and P₂ᵀ = P₂, we have (P₂P₁)ᵢᵢ = (P₁P₂)ᵢᵢᵀ = (P₁P₂)ᵢᵢ. So the trace = ∑ᵢ (P₁P₂)ᵢᵢ², which is a sum of squares.
-/
theorem trace_hadamardSquare_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (P₁ P₂ : Matrix n n ℝ)
    (h₁ : IsOrthProj P₁) (h₂ : IsOrthProj P₂) :
    0 ≤ (hadamardSquare P₁ P₂).trace := by
  unfold hadamardSquare;
  norm_num [ Matrix.trace ];
  refine' Finset.sum_nonneg fun i _ => _;
  -- Since $P₁$ and $P₂$ are orthogonal projections, we have $(P₁P₂)^T = P₂P₁$.
  have h_transpose : (P₁ * P₂).transpose = P₂ * P₁ := by
    rw [ Matrix.transpose_mul, h₁.2, h₂.2 ];
  rw [ ← h_transpose, Matrix.transpose_apply ] ; exact mul_self_nonneg _;

/-! ## Theorem 3: tr(Aᵏ) ≥ 0 for real symmetric A and even k -/

/-
PROBLEM
For any real symmetric matrix A and even k ≥ 0, tr(Aᵏ) ≥ 0.
    Proof idea: if k = 2m, then Aᵏ = (Aᵐ)ᵀ(Aᵐ), so tr(Aᵏ) = ∑ᵢⱼ (Aᵐ)ᵢⱼ² ≥ 0.

PROVIDED SOLUTION
Write k = 2m. Then A^(2m) = (Aᵐ)ᵀ · (Aᵐ) since Aᵀ = A implies (Aᵐ)ᵀ = Aᵐ, so A^(2m) = Aᵐ · Aᵐ = (Aᵐ)ᵀ · Aᵐ. Then tr(A^(2m)) = tr((Aᵐ)ᵀ · Aᵐ) = ∑ᵢⱼ ((Aᵐ)ᵢⱼ)² ≥ 0. Key Mathlib facts: Matrix.IsSymm.transpose_pow (Aᵐ)ᵀ = Aᵐ, then rewrite the trace as a sum of squares using Finset.sum_nonneg.
-/
theorem trace_pow_nonneg_of_isSymm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsSymm) (k : ℕ) (hk : Even k) :
    0 ≤ (A ^ k).trace := by
  -- Since k is even, write k = 2m.
  obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m := even_iff_two_dvd.mp hk
  -- Then A^(2m) = (A^m)ᵀ(A^m).
  have h_even : A ^ (2 * m) = (A ^ m).transpose * (A ^ m) := by
    simp +decide [ pow_mul', hA.eq ];
    rw [ sq ]
  -- The trace is tr((A^m)ᵀ(A^m)) = ∑ᵢⱼ (A^m)ᵢⱼ².
  have h_trace : (A ^ (2 * m)).trace = ∑ i, ∑ j, ((A ^ m) i j) ^ 2 := by
    simp +decide [ h_even, Matrix.trace, pow_two ];
    simp +decide [ Matrix.mul_apply, mul_comm ];
    rw [ ← Finset.sum_comm ] ; congr ; ext ; congr ; ext ; rw [ ← Matrix.transpose_pow ] ; aesop;
  -- So tr(A^(2m)) is a sum of squares, hence nonnegative.
  have h_sum_nonneg : 0 ≤ ∑ i, ∑ j, ((A ^ m) i j) ^ 2 := by
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  -- Therefore, tr(A^(2m)) ≥ 0.
  exact h_sum_nonneg.trans_eq h_trace.symm

/-! ## Corollary 4: For admissible P₁, P₂ and even k, tr(Aᵏ) ≥ 0 -/

/-
PROBLEM
A = (P₁P₂) ∘ (P₂P₁) is always symmetric.

PROVIDED SOLUTION
Unfold hadamardSquare and IsSymm. We need to show ((P₁P₂) ∘ (P₂P₁))ᵀ = (P₁P₂) ∘ (P₂P₁). The (i,j) entry of the LHS is (P₁P₂)ⱼᵢ · (P₂P₁)ⱼᵢ. Since P₁ᵀ = P₁ and P₂ᵀ = P₂, we have (P₂P₁)ⱼᵢ = ((P₁P₂)ᵀ)ⱼᵢ = (P₁P₂)ᵢⱼ, and (P₁P₂)ⱼᵢ = ((P₁P₂)ᵀ)ᵢⱼ = (P₂P₁)ᵢⱼ. So the entry is (P₂P₁)ᵢⱼ · (P₁P₂)ᵢⱼ = (P₁P₂)ᵢⱼ · (P₂P₁)ᵢⱼ, which is the RHS. Use ext, simp with hadamard, transpose, mul_comm.
-/
theorem hadamardSquare_isSymm {n : Type*} [Fintype n] [DecidableEq n]
    (P₁ P₂ : Matrix n n ℝ) (h₁ : IsOrthProj P₁) (h₂ : IsOrthProj P₂) :
    (hadamardSquare P₁ P₂).IsSymm := by
  ext i j; ( unfold hadamardSquare; simp +decide [ Matrix.mul_apply, mul_comm ] ; );
  -- By the properties of orthogonal projections, we know that $P_1^T = P_1$ and $P_2^T = P_2$.
  have hP1T : P₁ᵀ = P₁ := by
    exact h₁.2
  have hP2T : P₂ᵀ = P₂ := by
    exact h₂.2;
  simp +decide [ ← Matrix.ext_iff ] at hP1T hP2T;
  simp +decide only [hP1T, hP2T, mul_comm]

/-- For admissible P₁, P₂ and even k, tr(Aᵏ) ≥ 0. -/
theorem trace_hadamardSquare_pow_nonneg_even {n : Type*} [Fintype n] [DecidableEq n]
    (P₁ P₂ : Matrix n n ℝ) (h₁ : IsOrthProj P₁) (h₂ : IsOrthProj P₂)
    (k : ℕ) (hk : Even k) :
    0 ≤ ((hadamardSquare P₁ P₂) ^ k).trace := by
  exact trace_pow_nonneg_of_isSymm _ (hadamardSquare_isSymm P₁ P₂ h₁ h₂) k hk

/-! ## Proposition 2: n ≤ 3 implies power-nonneg -/

/-
PROBLEM
Proposition 2 requires detailed case analysis involving eigenvalue bounds.
We decompose it into helper lemmas for each dimension.

Helper: for a 2×2 symmetric matrix with nonneg trace, tr(A^m) ≥ 0 for all m.
    Key insight: eigenvalues λ₁ ≥ λ₂ satisfy λ₁+λ₂ ≥ 0. For odd m with λ₂ < 0,
    λ₁ ≥ |λ₂| so λ₁^m ≥ |λ₂|^m.

PROVIDED SOLUTION
For a 2×2 real symmetric matrix A with eigenvalues λ₁ ≥ λ₂ and tr(A) = λ₁ + λ₂ ≥ 0:
- For even m: tr(A^m) = λ₁^m + λ₂^m ≥ 0 (sum of nonneg reals). Use trace_pow_nonneg_of_isSymm.
- For odd m ≥ 1: If λ₂ ≥ 0, done. If λ₂ < 0, then λ₁ ≥ |λ₂| (from λ₁ + λ₂ ≥ 0), so λ₁^m + λ₂^m = λ₁^m - |λ₂|^m ≥ 0.
- For m=0: trace(I₂) = 2 ≥ 0.

Use the spectral theorem for the 2×2 symmetric matrix: A = Q diag(λ₁, λ₂) Qᵀ. Then A^m = Q diag(λ₁^m, λ₂^m) Qᵀ, so tr(A^m) = λ₁^m + λ₂^m. Since λ₁ + λ₂ ≥ 0, for odd m we have λ₁^m + λ₂^m ≥ 0 because if λ₂ < 0 then λ₁ ≥ -λ₂ > 0 and λ₁^m ≥ (-λ₂)^m = -λ₂^m.
-/
lemma trace_pow_nonneg_of_isSymm_nonneg_trace_2x2
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.IsSymm) (htr : 0 ≤ A.trace)
    (m : ℕ) : 0 ≤ (A ^ m).trace := by
  -- By the spectral theorem, since A is symmetric, there exists an orthogonal matrix Q such that QᵀAQ is diagonal with eigenvalues λ₁ and λ₂.
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin 2) (Fin 2) ℝ, Q.transpose * Q = 1 ∧ Q * Q.transpose = 1 ∧ ∃ (eigenvalues : Fin 2 → ℝ), A = Q * Matrix.diagonal eigenvalues * Q.transpose := by
    have := Matrix.IsHermitian.spectral_theorem hA;
    refine' ⟨ _, _, _, _, this ⟩;
    · simp +decide [ ← Matrix.ext_iff, mul_eq_one_comm ];
      have := ( IsHermitian.eigenvectorUnitary hA ).2.2;
      exact ⟨ ⟨ by simpa [ Matrix.mul_apply ] using congr_fun ( congr_fun this 0 ) 0, by simpa [ Matrix.mul_apply ] using congr_fun ( congr_fun this 0 ) 1 ⟩, by simpa [ Matrix.mul_apply ] using congr_fun ( congr_fun this 1 ) 0, by simpa [ Matrix.mul_apply ] using congr_fun ( congr_fun this 1 ) 1 ⟩;
    · exact Units.mul_eq_one_iff_inv_eq.mpr rfl;
  rcases hQ with ⟨ hQ₁, hQ₂, eigenvalues, rfl ⟩;
  -- Since eigenvalues are real, we have eigenvalues 0 + eigenvalues 1 ≥ 0.
  have h_eigenvalues_nonneg : eigenvalues 0 + eigenvalues 1 ≥ 0 := by
    simp_all +decide [ Matrix.trace_mul_comm, Matrix.mul_assoc ];
  -- Since eigenvalues are real, we have eigenvalues 0 ^ m + eigenvalues 1 ^ m ≥ 0.
  have h_eigenvalues_pow_nonneg : eigenvalues 0 ^ m + eigenvalues 1 ^ m ≥ 0 := by
    rcases Nat.even_or_odd' m with ⟨ k, rfl | rfl ⟩ <;> norm_num [ pow_add, pow_mul ] at *;
    · positivity;
    · by_cases h₂ : eigenvalues 0 ≥ 0 <;> by_cases h₃ : eigenvalues 1 ≥ 0 <;> simp_all +decide
      · positivity;
      · nlinarith [ pow_le_pow_left₀ ( by positivity ) ( by nlinarith : eigenvalues 0 ^ 2 ≥ eigenvalues 1 ^ 2 ) k, pow_nonneg ( sq_nonneg ( eigenvalues 0 ) ) k, pow_nonneg ( sq_nonneg ( eigenvalues 1 ) ) k ];
      · nlinarith [ pow_le_pow_left₀ ( by nlinarith ) ( by nlinarith : eigenvalues 0 ^ 2 ≤ eigenvalues 1 ^ 2 ) k, pow_nonneg ( sq_nonneg ( eigenvalues 0 ) ) k, pow_nonneg ( sq_nonneg ( eigenvalues 1 ) ) k ];
      · linarith;
  -- Since $Q$ is orthogonal, we have $(Q * diagonal eigenvalues * Qᵀ)^m = Q * diagonal (eigenvalues^m) * Qᵀ$.
  have h_diag_pow : (Q * Matrix.diagonal eigenvalues * Qᵀ) ^ m = Q * Matrix.diagonal (fun i => eigenvalues i ^ m) * Qᵀ := by
    refine' Nat.recOn m _ _ <;> simp_all +decide [ pow_succ, ← mul_assoc ];
    simp +decide [ mul_assoc, hQ₁ ];
  simp_all +decide [ Matrix.trace_mul_comm, Matrix.mul_assoc ]

/-
PROBLEM
n=0 case: empty type, trace is 0.

PROVIDED SOLUTION
Fin 0 is empty. For any matrix over Fin 0, the trace is a sum over an empty Finset, hence 0. So (A^m).trace = 0 ≥ 0 for all m. Use Fintype.elim or show that any matrix over Fin 0 is unique/trivial.
-/
lemma power_nonneg_dim_zero
    (P₁ P₂ : Matrix (Fin 0) (Fin 0) ℝ) :
    IsPowerNonneg (hadamardSquare P₁ P₂) := by
  exact fun m => by cases m <;> norm_num [ Matrix.trace ] ;

/-
PROBLEM
n=1 case: 1×1 projections are 0 or 1.

PROVIDED SOLUTION
A 1×1 orthogonal projection P satisfies P²=P and Pᵀ=P. For a 1×1 matrix, P = !![a] where a² = a, so a ∈ {0,1}. Same rank means P₁ = P₂ (both 0 or both I₁). Then P₁P₂ = P₁² = P₁ and P₂P₁ = P₁. So A = P₁ ∘ P₁ = !![a²] where a ∈ {0,1}, so A = P₁. Then A^m = P₁ for m ≥ 1, A^0 = I₁. trace(A^m) ∈ {0,1} ≥ 0.
-/
lemma power_nonneg_dim_one
    (P₁ P₂ : Matrix (Fin 1) (Fin 1) ℝ)
    (h₁ : IsOrthProj P₁)
    (hrank : P₁.rank = P₂.rank) :
    IsPowerNonneg (hadamardSquare P₁ P₂) := by
  -- Since P₁ and P₂ are 1x1 matrices, they are either 0 or 1. We can consider the two cases.
  by_cases hP₁ : P₁ = 0 ∨ P₁ = 1;
  · cases hP₁ <;> simp_all +decide [ IsPowerNonneg, Matrix.trace ];
    · intro m; induction m <;> simp_all +decide [ pow_succ, Matrix.mul_apply, hadamardSquare ] ;
      norm_num [ ← hrank ];
    · intro m; induction m <;> simp_all +decide [ hadamardSquare ] ;
      simp_all +decide [ ← hrank, pow_add, Matrix.mul_apply ];
      exact mul_nonneg ‹_› ( mul_self_nonneg _ );
  · simp_all +decide [ ← Matrix.ext_iff, Fin.forall_fin_one, IsOrthProj ];
    simp_all +decide [ Matrix.mul_apply ]

/-
PROBLEM
n=2 case: A is power-nonneg by 2×2 eigenvalue argument.

PROVIDED SOLUTION
The hadamard square A = hadamardSquare P₁ P₂ is a 2×2 symmetric matrix (by hadamardSquare_isSymm) with nonneg trace (by trace_hadamardSquare_nonneg). So we can apply trace_pow_nonneg_of_isSymm_nonneg_trace_2x2 directly.
-/
lemma power_nonneg_dim_two
    (P₁ P₂ : Matrix (Fin 2) (Fin 2) ℝ)
    (h₁ : IsOrthProj P₁) (h₂ : IsOrthProj P₂) :
    IsPowerNonneg (hadamardSquare P₁ P₂) := by
  have hsymm : (hadamardSquare P₁ P₂).IsSymm := by
    exact hadamardSquare_isSymm P₁ P₂ h₁ h₂
  have htrace_nonneg : 0 ≤ (hadamardSquare P₁ P₂).trace := by
    exact trace_hadamardSquare_nonneg P₁ P₂ h₁ h₂
  exact fun m => trace_pow_nonneg_of_isSymm_nonneg_trace_2x2 _ hsymm htrace_nonneg m

/-
PROBLEM
For a PSD symmetric matrix, power-nonneg follows from eigenvalues ≥ 0.

PROVIDED SOLUTION
A PSD symmetric matrix has eigenvalues ≥ 0. By the spectral theorem, A = Q diag(λ₁,λ₂,λ₃) Qᵀ. Then A^m = Q diag(λ₁^m,λ₂^m,λ₃^m) Qᵀ and tr(A^m) = λ₁^m + λ₂^m + λ₃^m ≥ 0.

Alternative approach: For PSD A, we can show tr(A^m) ≥ 0 directly. For even m, already proved. For odd m: A is PSD so A^{(m-1)/2} exists and A^m = (A^{(m-1)/2})^T A (A^{(m-1)/2}). Then tr(A^m) = tr((A^{(m-1)/2})^T A (A^{(m-1)/2})) ≥ 0 since A is PSD. But this requires A^{1/2} to exist.

Simplest approach: Use hA.eigenvalues_nonneg and the spectral decomposition to express tr(A^m) as sum of nonneg eigenvalues to the m-th power.
-/
lemma isPowerNonneg_of_posSemidef
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.PosSemidef) :
    IsPowerNonneg A := by
  intro m; exact (by
  -- By the spectral theorem, since A is positive semidefinite, there exists an orthogonal matrix Q and a diagonal matrix D such that A = Q D Qᵀ.
  obtain ⟨Q, D, hQ, hD⟩ : ∃ Q : Matrix (Fin 3) (Fin 3) ℝ, ∃ D : Fin 3 → ℝ, A = Q * Matrix.diagonal D * Q.transpose ∧ (∀ i, 0 ≤ D i) ∧ Q.transpose * Q = 1 := by
    have := hA.1.spectral_theorem;
    refine' ⟨ _, _, this, _, _ ⟩ <;> norm_num [ ← Matrix.mul_assoc, ← Matrix.ext_iff ] at *;
    · exact fun i => hA.eigenvalues_nonneg i;
    · intro i j; erw [ Matrix.mul_apply ] ; simp +decide [ Matrix.one_apply, Matrix.transpose_apply ] ;
      have := hA.1.eigenvectorBasis.orthonormal; simp_all +decide [ orthonormal_iff_ite ] ;
      convert this i j using 1 ; simp +decide [ Fin.sum_univ_three, inner ] ; ring!;
  -- Then $A^m = (Q D Q^T)^m = Q D^m Q^T$.
  have hA_pow : A ^ m = Q * Matrix.diagonal (fun i => D i ^ m) * Q.transpose := by
    refine' Nat.recOn m _ _ <;> simp_all +decide [ pow_succ, mul_assoc ];
    · rw [ mul_eq_one_comm.mp hD.2 ];
    · simp +decide [ ← mul_assoc, hD.2 ]
  simp_all +decide [ Matrix.trace_mul_comm, Matrix.mul_assoc ] ; (
  exact Finset.sum_nonneg fun i _ => pow_nonneg ( hD.1 i ) _));

/-
PROBLEM
For full-rank projections on Fin 3, both are I and A = I.

PROVIDED SOLUTION
If P is an orthogonal projection (P² = P and Pᵀ = P) on Fin 3 with rank 3, then P = I. Rank 3 means the range of P (as a linear map) is all of ℝ³. Since P² = P, P is idempotent. For any x, there exists y with Py = x (since range = ℝ³). Then Px = P(Py) = P²y = Py = x. So P acts as the identity on every vector, hence P = I.
Use Submodule.eq_top_of_finrank_eq to show range = ⊤, then show P acts as identity.
-/
lemma orthProj_rank_full_eq_one
    (P : Matrix (Fin 3) (Fin 3) ℝ) (h : IsOrthProj P) (hr : P.rank = 3) : P = 1 := by
  -- Since P is a projection matrix with rank 3, its range is all of ℝ³. Therefore, for any vector x, there exists some y such that Py = x.
  have h_range : ∀ x : Fin 3 → ℝ, ∃ y : Fin 3 → ℝ, P.mulVec y = x := by
    intro x
    have h_range : LinearMap.range (Matrix.mulVecLin P) = ⊤ := by
      exact Submodule.eq_top_of_finrank_eq ( by aesop );
    exact LinearMap.range_eq_top.mp h_range x;
  -- Since P is a projection matrix with rank 3, its range is all of ℝ³. Therefore, for any vector x, we have Px = x.
  have h_diag : ∀ x : Fin 3 → ℝ, P.mulVec x = x := by
    intro x; obtain ⟨ y, rfl ⟩ := h_range x; simp_all +decide [ Matrix.mulVec_mulVec ] ;
    rw [ h.1 ];
  exact Matrix.toLin'.injective ( LinearMap.ext fun x => by simpa using h_diag x )

/-
PROBLEM
For rank ≤ 1 projections (or full rank), the hadamard square is PSD.

PROVIDED SOLUTION
Case on hcase:

Case P₁.rank = 3: By orthProj_rank_full_eq_one, P₁ = I. Since hrank: P₁.rank = P₂.rank, also P₂.rank = 3, so P₂ = I. Then hadamardSquare I I = (I*I).hadamard(I*I) = I.hadamard I = I (since I_{ij} * I_{ij} = I_{ij}). And I is PSD.

Case P₁.rank ≤ 1:
  Sub-case P₁.rank = 0: By orthProj_rank_zero_eq_zero, P₁ = 0 and P₂ = 0 (since P₂.rank = 0). Then A = 0, which is PSD.

  Sub-case P₁.rank = 1: Need to show A = (P₁P₂) ∘ (P₂P₁) is PSD. Since P₁ and P₂ are rank-1 projections, A has nonneg diagonal entries (since A_{ii} = M_{ii}² ≥ 0) and the off-diagonal entries satisfy A_{ij} = M_{ij}M_{ji}. The PSD property follows from the quadratic form: x^T A x = ∑_{ij} x_i x_j M_{ij} M_{ji} = tr(DMDM) where D = diag(x). For rank-1 projections P₁ = uu^T, P₂ = vv^T, M = (u·v)uv^T. Then DM = (u·v) D u v^T. DMDM = (u·v)² (Du)(v^T D u)(v^T). tr(DMDM) = (u·v)² (v^TDu)² ≥ 0. So A is PSD.

Use orthProj_rank_zero_eq_zero and orthProj_rank_full_eq_one as helpers.
-/
lemma hadamardSquare_posSemidef_rank_le_one_or_full
    (P₁ P₂ : Matrix (Fin 3) (Fin 3) ℝ)
    (h₁ : IsOrthProj P₁) (h₂ : IsOrthProj P₂)
    (hrank : P₁.rank = P₂.rank)
    (hcase : P₁.rank ≤ 1 ∨ P₁.rank = 3) :
    (hadamardSquare P₁ P₂).PosSemidef := by
  cases hcase <;> simp_all +decide [ IsOrthProj ];
  · -- Since $P₁$ and $P₂$ are rank-1 projections, we can write them as $P₁ = u e^T$ and $P₂ = v f^T$ for some vectors $u, e, v, f$.
    obtain ⟨u, e, hu⟩ : ∃ u e : Fin 3 → ℝ, P₁ = Matrix.of (fun i j => u i * e j) := by
      -- Since $P₁$ is a rank-1 projection, its range is one-dimensional. Let $u$ be a vector in the range of $P₁$.
      obtain ⟨u, hu⟩ : ∃ u : Fin 3 → ℝ, u ≠ 0 ∧ ∀ x : Fin 3 → ℝ, ∃ c : ℝ, P₁.mulVec x = c • u := by
        have h_range : Module.finrank ℝ (LinearMap.range (Matrix.mulVecLin P₁)) ≤ 1 := by
          linarith!;
        interval_cases _ : Module.finrank ℝ ( LinearMap.range ( Matrix.mulVecLin P₁ ) ) <;> simp_all +decide [ Submodule.eq_bot_iff ];
        · exact ⟨ fun _ => 1, fun h => by simpa using congr_fun h 0, 0, by norm_num ⟩;
        · have := finrank_eq_one_iff'.mp ‹_›;
          simp +zetaDelta at *;
          exact ⟨ _, this.choose_spec.1, fun x => by obtain ⟨ c, hc ⟩ := this.choose_spec.2 x; exact ⟨ c, hc.symm ⟩ ⟩;
      choose c hc using hu.2;
      exact ⟨ u, fun j => c ( Pi.single j 1 ), by ext i j; simpa [ mul_comm ] using congr_fun ( hc ( Pi.single j 1 ) ) i ⟩
    obtain ⟨v, f, hv⟩ : ∃ v f : Fin 3 → ℝ, P₂ = Matrix.of (fun i j => v i * f j) := by
      cases' ‹Module.finrank ℝ ( LinearMap.range P₂.mulVecLin ) ≤ 1›.eq_or_lt with h h <;> simp_all +decide [ Submodule.eq_bot_iff ];
      · obtain ⟨ v, hv ⟩ := finrank_eq_one_iff'.mp h;
        -- Since $v$ is a basis vector for the range of $P₂$, we can write $P₂$ as $P₂ = v f^T$ for some vector $f$.
        obtain ⟨f, hf⟩ : ∃ f : Fin 3 → ℝ, ∀ i, P₂.mulVecLin (Pi.single i 1) = f i • v := by
          choose f hf using fun i => hv.2 ⟨ P₂.mulVecLin ( Pi.single i 1 ), Set.mem_range_self _ ⟩ ; use f; aesop;
        use v.val, f;
        ext i j; specialize hf j; replace hf := congr_fun hf i; simp_all +decide [ mul_comm, Matrix.mulVec ] ;
      · exact ⟨ 0, 0, by ext i j; simpa using congr_fun ( h ( Pi.single j 1 ) ) i ⟩;
    unfold hadamardSquare; simp_all +decide [ ← Matrix.ext_iff ] ;
    constructor;
    · ext i j; simp +decide [ hu, hv, Matrix.mul_apply, mul_comm, mul_left_comm ] ;
      simp +decide [ ← mul_assoc, h₁.2, h₂.2 ] ; ring;
    · simp_all +decide [ Matrix.mul_apply, Fin.sum_univ_three ];
      intro x; simp_all +decide [ Finsupp.sum_fintype ] ; ring_nf;
      -- Factor out common terms and simplify the expression.
      suffices h_simp : 0 ≤ (∑ i, x i * u i * e 0 * v i * f 0 + ∑ i, x i * u i * e 1 * v i * f 1 + ∑ i, x i * u i * e 2 * v i * f 2) ^ 2 by
        convert h_simp using 1 ; norm_num [ Fin.sum_univ_three ] ; ring!;
      positivity;
  · -- Since P₁ and P₂ are both rank 3, they are both the identity matrix.
    have hP1 : P₁ = 1 := by
      apply orthProj_rank_full_eq_one; exact h₁; linarith;
    have hP2 : P₂ = 1 := by
      exact orthProj_rank_full_eq_one P₂ h₂ (id (Eq.symm hrank))
    simp [hP1, hP2] at *;
    constructor <;> norm_num [ hadamardSquare ];
    · ext i j ; fin_cases i <;> fin_cases j <;> rfl;
    · simp +decide [ Matrix.one_apply, Finsupp.sum ];
      exact fun x => Finset.sum_nonneg fun i hi => by split_ifs <;> nlinarith;

open Matrix BigOperators Finset

noncomputable section

/-!
# Power-nonnegativity for the Hadamard square in dimension 3, rank 2

We prove that if `P₁` and `P₂` are 3×3 real orthogonal projection matrices of rank 2,
then the matrix `A = (P₁ * P₂) ∘ (P₂ * P₁)` (Hadamard product) satisfies
`tr(A ^ k) ≥ 0` for every `k : ℕ`.
-/

/-! ## Numerical core lemma -/

/-- If `a ≥ 1/3` and `b, c ≥ -1/8`, then `a ^ k + b ^ k + c ^ k ≥ 0` for all `k : ℕ`. -/
lemma sum_pow_nonneg_of_bounds (a b c : ℝ) (ha : 1 / 3 ≤ a) (hb : -(1 / 8) ≤ b)
    (hc : -(1 / 8) ≤ c) (k : ℕ) : 0 ≤ a ^ k + b ^ k + c ^ k := by
  rcases Nat.even_or_odd' k with ⟨ k, rfl | rfl ⟩
  · exact add_nonneg (add_nonneg (pow_mul a 2 k ▸ by positivity) (pow_mul b 2 k ▸ by positivity))
      (pow_mul c 2 k ▸ by positivity)
  · have h_bounds : a ^ (2 * k + 1) ≥ (1 / 3) ^ (2 * k + 1) ∧
        b ^ (2 * k + 1) ≥ - (1 / 8) ^ (2 * k + 1) ∧
        c ^ (2 * k + 1) ≥ - (1 / 8) ^ (2 * k + 1) := by
      refine' ⟨_, _, _⟩ <;> norm_num [pow_add, pow_mul] at *
      · exact mul_le_mul (pow_le_pow_left₀ (by norm_num) (by nlinarith) _) ha
          (by positivity) (by positivity)
      · by_cases hb_nonneg : 0 ≤ b
        · exact le_trans (neg_nonpos_of_nonneg (by positivity)) (by positivity)
        · nlinarith [pow_le_pow_left₀ (by nlinarith)
            (show b ^ 2 ≤ (1 / 8) ^ 2 by nlinarith) k,
            pow_pos (by norm_num : (0 : ℝ) < 1 / 64) k]
      · by_cases hc_nonneg : 0 ≤ c
        · exact le_trans (neg_nonpos_of_nonneg (by positivity)) (by positivity)
        · nlinarith [pow_pos (by nlinarith : 0 < c ^ 2) k,
            pow_le_pow_left₀ (by nlinarith) (by nlinarith : c ^ 2 ≤ (1 / 8) ^ 2) k]
    norm_num [pow_add, pow_mul] at *
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 9) k,
      pow_le_pow_left₀ (by norm_num) (by norm_num : (1 / 64 : ℝ) ≤ 1 / 9) k]

/-- Bridge lemma: Fin 3 version of the numerical core. -/
lemma fin3_sum_pow_nonneg (f : Fin 3 → ℝ)
    (hmin : ∀ i, -(1 / 8) ≤ f i) (hmax : ∃ i, 1 / 3 ≤ f i) (k : ℕ) :
    0 ≤ ∑ i, f i ^ k := by
  obtain ⟨ i, hi ⟩ := hmax
  fin_cases i <;> simp_all +decide [ Fin.sum_univ_three ]
  · have := @sum_pow_nonneg_of_bounds ( f 0 ) ( f 1 ) ( f 2 ) ?_ ?_ ?_ k <;>
      norm_num at * <;> aesop
  · convert sum_pow_nonneg_of_bounds ( f 1 ) ( f 0 ) ( f 2 )
      ( by linarith ) ( by linarith [ hmin 0 ] ) ( by linarith [ hmin 2 ] ) k using 1 ; ring!
  · convert sum_pow_nonneg_of_bounds ( f 2 ) ( f 0 ) ( f 1 )
      ( by linarith ) ( by linarith [ hmin 0 ] ) ( by linarith [ hmin 1 ] ) k using 1 ; ring!

/-! ## Hadamard product of M and Mᵀ is symmetric -/

/-- The Hadamard product `M ∘ Mᵀ` is symmetric for any square matrix `M`. -/
lemma hadamard_transpose_isSymm {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) : (M.hadamard M.transpose).IsSymm := by
  ext i j; simp +decide [mul_comm]

/-- Conversion: a symmetric real matrix is Hermitian. -/
lemma isSymm_to_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (h : M.IsSymm) : M.IsHermitian := by
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]

/-- For symmetric P₁, P₂, we have `P₂ * P₁ = (P₁ * P₂)ᵀ`. -/
lemma transpose_prod_symm {n : Type*} [Fintype n] [DecidableEq n]
    (P₁ P₂ : Matrix n n ℝ) (h1 : P₁.transpose = P₁) (h2 : P₂.transpose = P₂) :
    P₂ * P₁ = (P₁ * P₂).transpose := by
  simp [Matrix.transpose_mul, h1, h2]

/-- The Hadamard product `(P₁P₂) ∘ (P₂P₁)` is symmetric when P₁, P₂ are symmetric. -/
lemma hadamard_prod_isSymm
    {n : Type*} [Fintype n] [DecidableEq n]
    (P₁ P₂ : Matrix n n ℝ) (h1 : P₁.transpose = P₁) (h2 : P₂.transpose = P₂) :
    (hadamard (P₁ * P₂) (P₂ * P₁)).IsSymm := by
  rw [transpose_prod_symm P₁ P₂ h1 h2]
  exact hadamard_transpose_isSymm (P₁ * P₂)

/-! ## Trace of A^k equals sum of eigenvalue powers -/

/-- For a Hermitian matrix, the trace of `A ^ k` equals the sum of the k-th powers of
its eigenvalues. -/
lemma IsHermitian.trace_pow_eq_sum_eigenvalues_pow {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (k : ℕ) :
    (A ^ k).trace = ∑ i, (hA.eigenvalues i) ^ k := by
  obtain ⟨U, D, hU, hD⟩ : ∃ U : Matrix n n ℝ, ∃ D : Matrix n n ℝ,
      U.transpose * U = 1 ∧ U * U.transpose = 1 ∧
      D = Matrix.diagonal (hA.eigenvalues) ∧ A = U * D * U.transpose := by
    have := hA.spectral_theorem
    refine' ⟨_, _, _, _, rfl, this⟩
    · simp +decide [mul_eq_one_comm]
      convert hA.eigenvectorUnitary.2.2 using 1
    · simp +decide
      have := hA.eigenvectorUnitary.2.2
      convert this using 1
  have hA_k : A ^ k = U * D ^ k * U.transpose := by
    induction' k with k ih <;> simp_all +decide [pow_succ, mul_assoc]
    simp +decide [← mul_assoc, hU]
  rw [hA_k, Matrix.trace_mul_comm]
  simp +decide [← mul_assoc, hU, hD.2.1, Matrix.trace]
  simp +decide [Matrix.diagonal_pow]

/-! ## Helper lemmas for eigenvalue bounds -/

/-
PROBLEM
If A + c • 1 is positive semidefinite (as a quadratic form), then all eigenvalues
of A are at least -c.

PROVIDED SOLUTION
Since A is Hermitian, let v_i be the eigenvector for eigenvalue λ_i = hA.eigenvalues i. Then v_i is nonzero (it's an element of an orthonormal basis).

By hypothesis, 0 ≤ v_i^T (A + c·I) v_i = v_i^T A v_i + c · v_i^T v_i = λ_i · ||v_i||² + c · ||v_i||².

Since ||v_i||² > 0, we get λ_i + c ≥ 0, so λ_i ≥ -c.

For the eigenvector, use `hA.eigenvectorBasis i` which gives an orthonormal basis. The eigenvector satisfies A.mulVec v_i = λ_i • v_i (use `hA.mulVec_eigenvectorBasis`). It's nonzero because it's part of an orthonormal set.

For the Rayleigh quotient: v_i^T A v_i = λ_i · v_i^T v_i. This follows from A v_i = λ_i v_i, so v_i^T A v_i = v_i^T (λ_i v_i) = λ_i ||v_i||².

Also v_i^T (c·I) v_i = c · ||v_i||².

Key Mathlib lemma: `hA.eigenvalues_eq i` relates eigenvalue to the Rayleigh quotient. Use this directly.
-/
lemma eigenvalue_ge_neg_of_psd_shift
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.IsHermitian) (c : ℝ)
    (hpsd : ∀ v : Fin 3 → ℝ, 0 ≤ dotProduct v ((A + (c : ℝ) • (1 : Matrix _ _ ℝ)).mulVec v))
    (i : Fin 3) :
    -c ≤ hA.eigenvalues i := by
  -- By hypothesis, $0 \leq v_i^T (A + cI) v_i = v_i^T A v_i + c \cdot v_i^T v_i = \lambda_i \cdot \|v_i\|^2 + c \cdot \|v_i\|^2$.
  have h_eigenvalue : ∀ (v : Fin 3 → ℝ), 0 ≤ v ⬝ᵥ A.mulVec v + c * ∑ i, v i ^ 2 := by
    convert hpsd using 3 ; simp +decide [ Matrix.add_mulVec, dotProduct_add ] ; ring_nf;
    simp +decide [ Matrix.mulVec, dotProduct, Fin.sum_univ_three ] ; ring;
  -- Let $v_i$ be the eigenvector corresponding to the eigenvalue $\lambda_i$.
  obtain ⟨v, hv⟩ : ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ A.mulVec v = hA.eigenvalues i • v := by
    have := hA.eigenvectorBasis.orthonormal;
    refine' ⟨ hA.eigenvectorBasis i, _, _ ⟩;
    · intro h; have := this.1 i; aesop;
    · convert hA.mulVec_eigenvectorBasis i using 1;
  -- Substitute $A.mulVec v = \lambda_i \cdot v$ into the inequality.
  have h_substitute : 0 ≤ hA.eigenvalues i * ∑ i, v i ^ 2 + c * ∑ i, v i ^ 2 := by
    convert h_eigenvalue v using 1 ; simp +decide [ hv.2, dotProduct, Finset.mul_sum _ _ _ ] ; ring_nf;
  nlinarith [ show 0 < ∑ i, v i ^ 2 from lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ( Ne.symm <| by intro H; exact hv.1 <| by ext i; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg ] ) ]

/-
PROBLEM
A rank-2 symmetric idempotent 3×3 real matrix equals I - nnᵀ for a unit vector n.

PROVIDED SOLUTION
Since P is symmetric, idempotent, and rank 2 in ℝ³, the kernel of P is 1-dimensional.

Step 1: Find a nonzero vector n in ker(P). Since rank P = 2 and P acts on ℝ³, the nullity = 3 - 2 = 1. By contradiction: if ker(P) = {0}, then P is injective as a linear map, so rank P = 3, contradicting rank P = 2.

Step 2: Normalize n to be a unit vector: replace n by n/||n||. Then ∑ i, n i ^ 2 = 1 and P.mulVec n = 0.

Step 3: Show P = I - of(n ⊗ n). For any vector w:
- If w ⊥ n (i.e., dotProduct n w = 0), then w ∈ range(P) (since ker(P) = span{n} and range(P) = ker(P)⊥ for symmetric P). So P w = w (since P is idempotent and w ∈ range(P)). Also, (I - nn^T)w = w - (n·w)n = w. So P w = (I - nn^T)w for w ⊥ n.
- If w = n, then P n = 0 and (I - nn^T)n = n - n = 0. So P w = (I - nn^T)w for w = n.
- By linearity, P = I - nn^T for all vectors.

Step 4: Convert from the operator equation to the matrix equation. Use ext to show P i j = (1 - of(n ⊗ n)) i j by applying the operator to standard basis vectors (Pi.single j 1).
-/
set_option maxHeartbeats 400000 in
lemma proj_rank_two_eq_id_sub_outer
    (P : Matrix (Fin 3) (Fin 3) ℝ)
    (hP_sym : P.transpose = P)
    (hP_idem : P * P = P)
    (hP_rank : P.rank = 2) :
    ∃ n : Fin 3 → ℝ, (∑ i, n i ^ 2 = 1) ∧
      P = 1 - Matrix.of (fun i j => n i * n j) := by
  -- Since P is symmetric and has rank 2, there exists a unit vector n such that P = I - nnᵀ.
  obtain ⟨n, hn⟩ : ∃ n : Fin 3 → ℝ, (∑ i, n i^2 = 1) ∧ P.mulVec n = 0 := by
    -- Since $P$ is a rank-2 symmetric matrix, it has a 1-dimensional null space.
    have h_null_space : ∃ n : Fin 3 → ℝ, n ≠ 0 ∧ P.mulVec n = 0 := by
      have h_det : Matrix.det P = 0 := by
        by_contra hP_det_nonzero;
        have := Matrix.rank_mul_le P ( P⁻¹ ) ; simp_all +decide [ isUnit_iff_ne_zero ] ;
      convert Matrix.exists_mulVec_eq_zero_iff.mpr h_det
    obtain ⟨ n, hn_ne_zero, hn_null ⟩ := h_null_space
    use (1 / Real.sqrt (∑ i, n i ^ 2)) • n
    simp
    simp_all +decide [ Fin.sum_univ_three, mul_pow, Matrix.mulVec_smul ];
    rw [ Real.sq_sqrt <| by positivity, ← mul_add, ← mul_add, inv_mul_cancel₀ <| by intro h; exact hn_ne_zero <| by ext i; fin_cases i <;> norm_num <;> nlinarith! ];
  -- Since P is symmetric and has rank 2, for any vector w orthogonal to n, we have Pw = w.
  have h_orthogonal : ∀ w : Fin 3 → ℝ, dotProduct n w = 0 → P.mulVec w = w := by
    -- Since P is symmetric and has rank 2, the range of P is the orthogonal complement of the kernel of P.
    have h_range : LinearMap.range (Matrix.mulVecLin P) = Submodule.span ℝ {w : Fin 3 → ℝ | dotProduct n w = 0} := by
      refine' Submodule.eq_of_le_of_finrank_le _ _;
      · intro x hx; obtain ⟨ y, rfl ⟩ := hx; simp_all +decide [ dotProduct ] ;
        -- Since $P$ is symmetric and idempotent, we have $P.mulVec y \cdot n = y \cdot P.mulVec n = 0$.
        have h_dot : dotProduct (P.mulVec y) n = dotProduct y (P.mulVec n) := by
          simp +decide [ Matrix.mulVec, dotProduct ];
          simp +decide only [mul_comm, Finset.mul_sum _ _ _, mul_left_comm];
          exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [ ← Matrix.ext_iff ] at hP_sym; aesop );
        simp_all +decide [ dotProduct, Fin.sum_univ_three ];
        exact Submodule.subset_span ( by simpa [ mul_comm ] using h_dot );
      · -- The orthogonal complement of a 1-dimensional subspace in a 3-dimensional space is 2-dimensional.
        have h_orthogonal_complement_dim : Module.finrank ℝ (Submodule.span ℝ {w : Fin 3 → ℝ | dotProduct n w = 0}) = 2 := by
          have h_orthogonal_complement : Submodule.span ℝ {w : Fin 3 → ℝ | dotProduct n w = 0} = LinearMap.ker (Matrix.mulVecLin (Matrix.of ![n])) := by
            refine' le_antisymm _ _ <;> intro x hx <;> simp_all +decide [ dotProduct ];
            · rw [ Submodule.mem_span ] at hx;
              specialize hx ( LinearMap.ker ( Matrix.mulVecLin ( Matrix.of ![n] ) ) ) ; simp_all +decide [ Set.subset_def ];
              exact hx fun x hx => by simpa [ dotProduct ] using hx;
            · exact Submodule.subset_span hx;
          rw [ h_orthogonal_complement ];
          have := LinearMap.finrank_range_add_finrank_ker ( Matrix.mulVecLin ( Matrix.of ![n] ) );
          rw [ show ( Matrix.mulVecLin ( Matrix.of ![n] ) ).range = ⊤ from _ ] at this;
          · norm_num at * ; linarith;
          · rw [ LinearMap.range_eq_top ];
            intro x; use fun i => x 0 * n i; ext i; fin_cases i ; simp +decide [ Matrix.mulVec, dotProduct ] ; ring_nf;
            rw [ ← Finset.sum_mul, hn.1, one_mul ];
        linarith!;
    intro w hw; replace h_range := SetLike.ext_iff.mp h_range w; simp_all +decide [ Submodule.mem_span ] ;
    obtain ⟨ y, rfl ⟩ := h_range.mpr ( fun p hp => hp hw ) ; simp_all +decide
  -- Let's choose any vector w and decompose it into a component parallel to n and a component orthogonal to n.
  have h_decomp : ∀ w : Fin 3 → ℝ, P.mulVec w = w - (dotProduct n w) • n := by
    intro w; specialize h_orthogonal ( w - ( n ⬝ᵥ w ) • n ) ; simp_all +decide [ Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_smul ] ;
    simp_all +decide [ dotProduct, Fin.sum_univ_three ];
    exact h_orthogonal ( by rw [ show n 0 * n 0 + n 1 * n 1 + n 2 * n 2 = 1 by linarith ] ; ring );
  refine' ⟨ n, hn.1, _ ⟩;
  ext i j;
  have := congr_fun ( h_decomp ( Pi.single j 1 ) ) i; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
  fin_cases i <;> fin_cases j <;> simp_all +decide [ Pi.single_apply ] <;> linarith!

/-! ## SOS decomposition in the rotated frame (from PsdShiftHelpers) -/

/-- The SOS identity: in the rotated frame, the quadratic form decomposes into a sum of
squares. This is the algebraic core of the proof. -/
lemma sos_identity (α β a_ b_ c_ d_ e_ f_ : ℝ) (hαβ : α ^ 2 + β ^ 2 = 1) :
    (a_ ^ 2 + 2 * α ^ 2 * b_ ^ 2 + 2 * α * β * b_ * c_ + α ^ 4 * d_ ^ 2 +
      2 * α ^ 3 * β * d_ * e_ + α ^ 2 * β ^ 2 * e_ ^ 2 +
      1 / 8 * (a_ ^ 2 + d_ ^ 2 + f_ ^ 2 + 2 * b_ ^ 2 + 2 * c_ ^ 2 + 2 * e_ ^ 2)) =
    (9 / 8 * a_ ^ 2 + 1 / 8 * f_ ^ 2 + 1 / 4 * (c_ + 4 * α * β * b_) ^ 2 +
      (2 * α ^ 2 - 1 / 2) ^ 2 * b_ ^ 2 + (α ^ 2 * d_ + α * β * e_) ^ 2 +
      1 / 8 * d_ ^ 2 + 1 / 4 * e_ ^ 2) := by
  linear_combination (-4 * α ^ 2 * b_ ^ 2) * hαβ

/-- The SOS expression is nonneg. -/
lemma sos_nonneg (α β a_ b_ c_ d_ e_ f_ : ℝ) :
    0 ≤ 9 / 8 * a_ ^ 2 + 1 / 8 * f_ ^ 2 + 1 / 4 * (c_ + 4 * α * β * b_) ^ 2 +
      (2 * α ^ 2 - 1 / 2) ^ 2 * b_ ^ 2 + (α ^ 2 * d_ + α * β * e_) ^ 2 +
      1 / 8 * d_ ^ 2 + 1 / 4 * e_ ^ 2 := by positivity

/-- Combined: the quadratic form in the rotated frame is nonneg. -/
lemma rotated_frame_nonneg (α β a_ b_ c_ d_ e_ f_ : ℝ) (hαβ : α ^ 2 + β ^ 2 = 1) :
    0 ≤ a_ ^ 2 + 2 * α ^ 2 * b_ ^ 2 + 2 * α * β * b_ * c_ + α ^ 4 * d_ ^ 2 +
      2 * α ^ 3 * β * d_ * e_ + α ^ 2 * β ^ 2 * e_ ^ 2 +
      1 / 8 * (a_ ^ 2 + d_ ^ 2 + f_ ^ 2 + 2 * b_ ^ 2 + 2 * c_ ^ 2 + 2 * e_ ^ 2) := by
  rw [sos_identity α β a_ b_ c_ d_ e_ f_ hαβ]
  exact sos_nonneg α β a_ b_ c_ d_ e_ f_

/-! ## Adapted basis approach for psd_poly_ineq_nonparallel -/

/-
PROBLEM
Lagrange identity: cross product squared = 1 - (dot product)² for unit vectors.

PROVIDED SOLUTION
Expand ∑ i, a i ^ 2, ∑ i, b i ^ 2, and (∑ i, a i * b i) ^ 2 using Fin.sum_univ_three, then the identity follows by ring (Lagrange identity for cross products).
-/
private lemma lagrange_cross_sq (a b : Fin 3 → ℝ) (ha : ∑ i, a i ^ 2 = 1)
    (hb : ∑ i, b i ^ 2 = 1) :
    (a 1 * b 2 - a 2 * b 1) ^ 2 + (a 2 * b 0 - a 0 * b 2) ^ 2 +
    (a 0 * b 1 - a 1 * b 0) ^ 2 = 1 - (∑ i, a i * b i) ^ 2 := by
  norm_num [ Fin.sum_univ_three ] at * ; nlinarith! only [ ha, hb ] ;

/-
PROBLEM
Matrix version of the SOS theorem: for any symmetric 3×3 matrix E and α²+β²=1,
    tr(E M₀ E M₀) + (1/8) tr(E²) ≥ 0 where M₀ = !![1,0,0;0,α²,αβ;0,0,0].

PROVIDED SOLUTION
Step 1: Extract entries of E. Since E is symmetric, E j i = E i j for all i,j. Denote a_ = E 0 0, b_ = E 0 1, c_ = E 0 2, d_ = E 1 1, e_ = E 1 2, f_ = E 2 2.

Step 2: Expand the matrix products E * M₀ * E * M₀ and E * E entry by entry using Fin.sum_univ_three, then compute their traces.

tr(E * M₀ * E * M₀) = a_² + 2α²b_² + 2αβ b_c_ + α⁴d_² + 2α³β d_e_ + α²β² e_²
tr(E * E) = a_² + d_² + f_² + 2b_² + 2c_² + 2e_²

Step 3: After the expansion, the goal becomes exactly the expression in rotated_frame_nonneg. Apply rotated_frame_nonneg with these entries and the hypothesis hαβ.

The key approach is: use ext with Fin 3 to convert IsSymm to equalities E 1 0 = E 0 1, E 2 0 = E 0 2, E 2 1 = E 1 2. Then expand the traces using simp with Fin.sum_univ_three, Matrix.mul_apply, Matrix.trace, Matrix.cons notation (!![...]), and Matrix.of. Then convert to rotated_frame_nonneg.
-/
private lemma matrix_psd_rotated (E : Matrix (Fin 3) (Fin 3) ℝ) (hE : E.IsSymm)
    (α β : ℝ) (hαβ : α ^ 2 + β ^ 2 = 1) :
    let M₀ : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, α ^ 2, α * β; 0, 0, 0]
    0 ≤ (E * M₀ * E * M₀).trace + (1 / 8) * (E * E).trace := by
  norm_num [ Matrix.trace ] at *;
  simp_all +decide [ Fin.sum_univ_three, Matrix.mul_apply ];
  convert rotated_frame_nonneg α β ( E 0 0 ) ( E 1 0 ) ( E 2 0 ) ( E 1 1 ) ( E 2 1 ) ( E 2 2 ) hαβ using 1 ; ring_nf! ; norm_num [ hE.apply ] ; ring!;

/-
PROBLEM
E = Q^T diag(v) Q is symmetric when Q is orthogonal.

PROVIDED SOLUTION
Show (Q^T * diag(v) * Q)^T = Q^T * diag(v)^T * Q = Q^T * diag(v) * Q, using that diagonal matrices are symmetric (diagonal_transpose) and the transpose rule (A*B*C)^T = C^T * B^T * A^T. Use Matrix.IsSymm, Matrix.transpose_mul, Matrix.transpose_transpose.
-/
private lemma conj_diagonal_symm (v : Fin 3 → ℝ) (Q : Matrix (Fin 3) (Fin 3) ℝ) :
    (Q.transpose * Matrix.diagonal v * Q).IsSymm := by
  simp +decide [ Matrix.IsSymm, Matrix.mul_assoc ]

/-
PROBLEM
Q^T M Q = M₀ given that Q is orthogonal and maps a → e₃, b → (0,-β,α).
    Here M is the matrix of P₁P₂ in the original frame and M₀ is the matrix
    in the adapted frame.

PROVIDED SOLUTION
The key idea: M = I - aa^T - bb^T + α·ab^T (the product of projections P₁P₂ where P₁ = I - aa^T, P₂ = I - bb^T and α = a·b).

So Q^T M Q = Q^T Q - (Q^T a)(Q^T a)^T - (Q^T b)(Q^T b)^T + α·(Q^T a)(Q^T b)^T

Since Q^T Q = I (hQortho), Q^T a = ![0,0,1] = e₃ (hQa), Q^T b = ![0,-β,α] (hQb):

Q^T M Q = I - e₃ e₃^T - ![0,-β,α]![0,-β,α]^T + α · e₃ · ![0,-β,α]^T

Computing entry by entry:
- e₃ e₃^T = !![0,0,0; 0,0,0; 0,0,1]
- ![0,-β,α]![0,-β,α]^T = !![0,0,0; 0,β²,-αβ; 0,-αβ,α²]
- α · e₃ · ![0,-β,α]^T = !![0,0,0; 0,0,0; 0,-αβ,α²]

So Q^T M Q = !![1,0,0; 0,1-β²,αβ; 0,αβ-αβ,-α²+α²] = !![1,0,0; 0,α²,αβ; 0,0,0]

using α²+β² = 1, so 1-β² = α².

Approach: prove entry by entry using ext (Fin 3). For each (i,j) entry, expand the matrix products using mul_apply and Fin.sum_univ_three, substitute the values from hQa and hQb (by extracting components: e.g., have hQa0 : (Q^T.mulVec a) 0 = 0 from congr_fun hQa 0), use hQortho for Q^T Q = I entries, and simplify with ha, hb, hαβ, and ring/nlinarith.
-/
private lemma QtMQ_eq_M0_of_basis (a b : Fin 3 → ℝ) (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (α β : ℝ)
    (hα : α = ∑ i, a i * b i)
    (hαβ : α ^ 2 + β ^ 2 = 1)
    (hQortho : Q.transpose * Q = 1)
    (hQa : Q.transpose.mulVec a = ![0, 0, 1])
    (hQb : Q.transpose.mulVec b = ![0, -β, α]) :
    Q.transpose * Matrix.of (fun i j =>
      (if i = j then (1 : ℝ) else 0) - a i * a j - b i * b j + α * a i * b j) * Q =
    !![1, 0, 0; 0, α ^ 2, α * β; 0, 0, 0] := by
  -- Let's simplify the expression for the matrix multiplication.
  have h_simp : (Q.transpose * (Matrix.of (fun i j => (if i = j then 1 else 0) - a i * a j - b i * b j + α * a i * b j)) * Q) = (Q.transpose * Q) - (Q.transpose * Matrix.of (fun i j => a i * a j) * Q) - (Q.transpose * Matrix.of (fun i j => b i * b j) * Q) + α • (Q.transpose * Matrix.of (fun i j => a i * b j) * Q) := by
    ext i j; simp +decide [ Matrix.mul_apply, Fin.sum_univ_three ] ; ring;
  -- Let's simplify the expression for the matrix multiplication using the given conditions.
  have h_simp : (Q.transpose * (Matrix.of (fun i j => a i * a j)) * Q) = Matrix.of (fun i j => (Q.transpose.mulVec a) i * (Q.transpose.mulVec a) j) ∧
                 (Q.transpose * (Matrix.of (fun i j => b i * b j)) * Q) = Matrix.of (fun i j => (Q.transpose.mulVec b) i * (Q.transpose.mulVec b) j) ∧
                 (Q.transpose * (Matrix.of (fun i j => a i * b j)) * Q) = Matrix.of (fun i j => (Q.transpose.mulVec a) i * (Q.transpose.mulVec b) j) := by
                   refine' ⟨ _, _, _ ⟩ <;> ext i j <;> simp +decide [ Matrix.mul_apply, Matrix.mulVec ] <;> ring_nf!;
                   · simp +decide [ dotProduct, Finset.mul_sum _ _ _, mul_comm, mul_left_comm ];
                   · simp +decide [ dotProduct, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ];
                   · simp +decide [ dotProduct, Finset.mul_sum _ _ _, mul_comm, mul_left_comm ];
  simp_all +decide [ ← Matrix.ext_iff, Fin.forall_fin_succ ];
  exact ⟨ by linarith, by ring ⟩

/-
PROBLEM
Existence of an adapted orthogonal basis for two non-parallel unit vectors.

PROVIDED SOLUTION
Construct Q explicitly. Set α = ∑ i, a i * b i, β = √(1 - α²).

Define:
- p_i = α * a_i - b_i (perpendicular to a, since a · p = α - α = 0)
- y_i = p_i / β (normalized, |y| = 1)
- x = a × y: x_0 = a_1*y_2 - a_2*y_1, x_1 = a_2*y_0 - a_0*y_2, x_2 = a_0*y_1 - a_1*y_0

Q has columns (x, y, a): Q i j = match j with | 0 => x i | 1 => y i | 2 => a i.

Verification:
1. Q^T Q = I: need x·x=1, y·y=1, a·a=1, x·y=0, x·a=0, y·a=0.
   - a·a = 1 (ha)
   - a·p = α(a·a) - a·b = α - α = 0, so a·y = 0
   - |p|² = α²(a·a) - 2α(a·b) + |b|² = α² - 2α² + 1 = 1-α² = β², so |y|² = 1
   - x = a × y ⊥ a and x ⊥ y automatically (cross product properties)
   - |x|² = |a|²|y|² - (a·y)² = 1 (Lagrange identity, finite verification for Fin 3)

2. Q Q^T = I: follows from Q^T Q = I for finite-dimensional square matrices. Use Matrix.nonsing_inv_eq_of_mul_eq_one or show it directly.

3. Q^T a = ![0, 0, 1]: (Q^T a)_j = ∑_i a_i Q_{ij} = ∑_i a_i (col_j)_i = a · col_j.
   For j=0: a·x = 0 (cross product ⊥ a)
   For j=1: a·y = 0 (shown above)
   For j=2: a·a = 1 (ha)

4. Q^T b = ![0, -β, α]:
   b = α*a - β*y (since y = p/β = (αa-b)/β, so b = αa - βy)
   For j=0: b·x = (αa - βy)·x = 0 (x ⊥ a, x ⊥ y)
   For j=1: b·y = (αa - βy)·y = α(a·y) - β(y·y) = 0 - β = -β
   For j=2: b·a = α (by definition)

Key issue: β = √(1-α²), all dot products involve sums over Fin 3. Use nlinarith to handle the algebraic identities. For Q Q^T = I, use the fact that for a square matrix, if Q^T Q = I then Q Q^T = I (use mul_right_eq_of_mul_eq_one or Matrix.mul_eq_one_comm).
-/
set_option maxHeartbeats 800000 in
private lemma adapted_basis_exists (a b : Fin 3 → ℝ)
    (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hcross : 0 < (a 1 * b 2 - a 2 * b 1) ^ 2 +
      (a 2 * b 0 - a 0 * b 2) ^ 2 + (a 0 * b 1 - a 1 * b 0) ^ 2) :
    let α := ∑ i, a i * b i
    let β := Real.sqrt (1 - α ^ 2)
    ∃ Q : Matrix (Fin 3) (Fin 3) ℝ,
      Q.transpose * Q = 1 ∧
      Q * Q.transpose = 1 ∧
      Q.transpose.mulVec a = ![0, 0, 1] ∧
      Q.transpose.mulVec b = ![0, -β, α] := by
  -- Define $p_i = \alpha a_i - b_i$, $y_i = \frac{p_i}{\beta}$, and $x = a \times y$.
  set α := ∑ i, a i * b i
  set β := Real.sqrt (1 - α^2)
  set p : Fin 3 → ℝ := fun i => α * a i - b i
  set y : Fin 3 → ℝ := fun i => p i / β
  set x : Fin 3 → ℝ := fun i => if i = 0 then a 1 * y 2 - a 2 * y 1 else if i = 1 then a 2 * y 0 - a 0 * y 2 else a 0 * y 1 - a 1 * y 0;
  -- Construct the matrix Q with columns x, y, and a.
  set Q : Matrix (Fin 3) (Fin 3) ℝ := ![![x 0, y 0, a 0], ![x 1, y 1, a 1], ![x 2, y 2, a 2]];
  -- Show that Q is orthogonal: Q^T * Q = I and Q * Q^T = I.
  have hQ_ortho : Q.transpose * Q = 1 ∧ Q * Q.transpose = 1 := by
    have hQ_ortho : Q.transpose * Q = 1 := by
      -- By definition of $x$, $y$, and $a$, we know that $x \cdot x = 1$, $y \cdot y = 1$, $a \cdot a = 1$, $x \cdot y = 0$, $x \cdot a = 0$, and $y \cdot a = 0$.
      have h_ortho : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 ∧ y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 = 1 ∧ a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 = 1 ∧ x 0 * y 0 + x 1 * y 1 + x 2 * y 2 = 0 ∧ x 0 * a 0 + x 1 * a 1 + x 2 * a 2 = 0 ∧ y 0 * a 0 + y 1 * a 1 + y 2 * a 2 = 0 := by
        simp +zetaDelta at *;
        refine' ⟨ _, _, _, _, _ ⟩;
        · norm_num [ Fin.sum_univ_three ] at *;
          field_simp;
          rw [ Real.sq_sqrt ( by nlinarith only [ sq_nonneg ( a 0 * b 1 - a 1 * b 0 ), sq_nonneg ( a 0 * b 2 - a 2 * b 0 ), sq_nonneg ( a 1 * b 2 - a 2 * b 1 ), ha, hb ] ), div_eq_iff ] <;> nlinarith only [ hcross, ha, hb ];
        · norm_num [ Fin.sum_univ_three ] at *;
          field_simp;
          rw [ Real.sq_sqrt, div_eq_iff ] <;> nlinarith only [ ha, hb, hcross ];
        · simpa only [ Fin.sum_univ_three ] using ha;
        · ring;
        · constructor <;> ring_nf!;
          rw [ Fin.sum_univ_three ] at *;
          rw [ show a 0 ^ 2 = 1 - a 1 ^ 2 - a 2 ^ 2 by linarith ] ; ring;
      ext i j; fin_cases i <;> fin_cases j <;> simp +decide [ *, Matrix.mul_apply, Fin.sum_univ_three ] ; ring_nf;
      all_goals simp +decide [ Q ] ; linarith!;
    exact ⟨ hQ_ortho, mul_eq_one_comm.mp hQ_ortho ⟩;
  refine' ⟨ Q, hQ_ortho.1, hQ_ortho.2, _, _ ⟩ <;> simp_all +decide [ ← List.ofFn_inj, Matrix.mulVec ];
  · simp +zetaDelta at *;
    simp_all +decide [ Fin.sum_univ_three, dotProduct, vecHead, vecTail ];
    grind;
  · simp +zetaDelta at *;
    norm_num [ Fin.sum_univ_three, vecHead, vecTail, dotProduct ] at *;
    grind +ring

/-
PROBLEM
The full trace-based reduction: connects the raw polynomial expression
    to the adapted-basis trace expression, using an orthogonal Q.

PROVIDED SOLUTION
The proof chains several equalities:

1. First, the double sum equals tr(D*M*D*M) where D = diagonal(v) and M_ij = (if i=j then 1 else 0) - a_i*a_j - b_i*b_j + s*a_i*b_j. Use double_sum_eq_trace_diag_M. Note: the second factor in the sum is M j i (up to commutativity of multiplication), which is needed for the trace identity.

2. Similarly, ∑ i, v_i² = tr(D²). Use sum_sq_eq_trace_diag_sq.

3. Show D*M*D*M = Q*(E*M₀*E*M₀)*Q^T:
   - M = Q*M₀*Q^T (from Q^T*M*Q = M₀, which follows from QtMQ_eq_M0_of_basis)
   - D = Q*E*Q^T (from E = Q^T*D*Q)
   - Substitute and cancel Q^T*Q = I:
     DMDM = QEQ^T * QM₀Q^T * QEQ^T * QM₀Q^T = Q*E*M₀*E*M₀*Q^T

4. Apply trace_ortho_conj: tr(Q*C*Q^T) = tr(C).

5. Similarly for D*D = Q*(E*E)*Q^T.

So LHS = tr(DMDM) + (1/8)*tr(D²) = tr(E*M₀*E*M₀) + (1/8)*tr(E²) = RHS.

Key technical detail: To match the second factor in the sum with M j i, note that M j i = (if j = i then 1 else 0) - a j * a i - b j * b i + s * a j * b i. The goal's second factor has (if i = j then 1 else 0) - a i * a j - b i * b j + s * a j * b i. These are equal because if i=j iff j=i, a_i*a_j = a_j*a_i, b_i*b_j = b_j*b_i. So show that the sum in the goal equals ∑ij v_i*v_j*M_ij*M_ji by congr and ring, then use double_sum_eq_trace_diag_M.

For the trace conjugation, use the approach:
- M = Q * M₀ * Q^T: calc M = Q*Q^T*M*Q*Q^T = Q*(Q^T*M*Q)*Q^T = Q*M₀*Q^T using hQ2 and hQtMQ.
- D = Q * E * Q^T: similarly.
- Then DMDM = Q*E*Q^T * Q*M₀*Q^T * Q*E*Q^T * Q*M₀*Q^T, cancel Q^T*Q=I repeatedly to get Q*(E*M₀*E*M₀)*Q^T.
- tr(Q*C*Q^T) = tr(C) by trace_ortho_conj.
-/
private lemma trace_reduction (a b v : Fin 3 → ℝ)
    (Q : Matrix (Fin 3) (Fin 3) ℝ) (s β : ℝ)
    (hs : s = ∑ i, a i * b i)
    (hαβ : s ^ 2 + β ^ 2 = 1)
    (hQ1 : Q.transpose * Q = 1) (hQ2 : Q * Q.transpose = 1)
    (hQa : Q.transpose.mulVec a = ![0, 0, 1])
    (hQb : Q.transpose.mulVec b = ![0, -β, s]) :
    let M₀ : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, s ^ 2, s * β; 0, 0, 0]
    let E := Q.transpose * Matrix.diagonal v * Q
    ∑ i : Fin 3, ∑ j : Fin 3, v i * v j *
      ((if i = j then (1 : ℝ) else 0) - a i * a j - b i * b j + s * a i * b j) *
      ((if i = j then (1 : ℝ) else 0) - a i * a j - b i * b j + s * a j * b i) +
    (1 / 8) * ∑ i, v i ^ 2 =
    (E * M₀ * E * M₀).trace + (1 / 8) * (E * E).trace := by
  -- By definition of $D$ and $M$, we know that $D = QEQ^T$ and $M = QM_0Q^T$.
  have hD : Matrix.diagonal v = Q * (Q.transpose * Matrix.diagonal v * Q) * Q.transpose := by
    grind +revert
  have hM : Matrix.of (fun i j => if i = j then (1 : ℝ) else 0) - Matrix.of (fun i j => a i * a j) - Matrix.of (fun i j => b i * b j) + Matrix.of (fun i j => s * a i * b j) = Q * !![1, 0, 0; 0, s ^ 2, s * β; 0, 0, 0] * Q.transpose := by
    have hM : Q.transpose * (Matrix.of (fun i j => if i = j then (1 : ℝ) else 0) - Matrix.of (fun i j => a i * a j) - Matrix.of (fun i j => b i * b j) + Matrix.of (fun i j => s * a i * b j)) * Q = !![1, 0, 0; 0, s ^ 2, s * β; 0, 0, 0] := by
      convert QtMQ_eq_M0_of_basis a b Q s β hs hαβ hQ1 hQa hQb using 1;
    simp +decide [ ← hM, ← mul_assoc, hQ2 ];
    rw [ mul_assoc, hQ2, mul_one ];
  -- Substitute $D = QEQ^T$ and $M = QM_0Q^T$ into the left-hand side.
  have h_subst : ∑ i, ∑ j, v i * v j * ((if i = j then (1 : ℝ) else 0) - a i * a j - b i * b j + s * a i * b j) * ((if i = j then (1 : ℝ) else 0) - a i * a j - b i * b j + s * a j * b i) + (1 / 8) * ∑ i, v i ^ 2 = (Matrix.diagonal v * (Matrix.of (fun i j => if i = j then (1 : ℝ) else 0) - Matrix.of (fun i j => a i * a j) - Matrix.of (fun i j => b i * b j) + Matrix.of (fun i j => s * a i * b j)) * Matrix.diagonal v * (Matrix.of (fun i j => if i = j then (1 : ℝ) else 0) - Matrix.of (fun i j => a i * a j) - Matrix.of (fun i j => b i * b j) + Matrix.of (fun i j => s * a i * b j))).trace + (1 / 8) * (Matrix.diagonal v * Matrix.diagonal v).trace := by
    norm_num [ Matrix.trace, Matrix.mul_apply ] at *;
    simp +decide [ Matrix.diagonal, Fin.sum_univ_three ] ; ring!;
  nontriviality;
  rw [ h_subst, hM ];
  norm_num [ ← mul_assoc, ← hD ];
  norm_num [ Matrix.mul_assoc, hQ1, hQ2 ];
  norm_num [ Matrix.trace_mul_comm ( Qᵀ ), Matrix.trace_mul_comm ( Q ) ];
  norm_num [ Matrix.mul_assoc, hQ1, hQ2 ]

set_option maxHeartbeats 800000 in
/-- The core polynomial inequality for the non-parallel case: when `a` and `b` are unit
vectors with nonzero cross product, the Hadamard-square quadratic form plus `(1/8)I` is
positive semi-definite. -/
lemma psd_poly_ineq_nonparallel
    (a b v : Fin 3 → ℝ) (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1)
    (hcross : 0 < (a 1 * b 2 - a 2 * b 1) ^ 2 +
      (a 2 * b 0 - a 0 * b 2) ^ 2 + (a 0 * b 1 - a 1 * b 0) ^ 2) :
    let s := ∑ i, a i * b i
    0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, v i * v j *
      ((if i = j then (1 : ℝ) else 0) - a i * a j - b i * b j + s * a i * b j) *
      ((if i = j then (1 : ℝ) else 0) - a i * a j - b i * b j + s * a j * b i) +
    (1 / 8) * ∑ i, v i ^ 2 := by
  intro s
  -- Step 1: Key quantities
  have hcross_eq := lagrange_cross_sq a b ha hb
  have hs2 : s ^ 2 < 1 := by nlinarith
  set β := Real.sqrt (1 - s ^ 2) with hβ_def
  have hβ_pos : 0 < β := Real.sqrt_pos_of_pos (by linarith)
  have hβ_sq : β ^ 2 = 1 - s ^ 2 := Real.sq_sqrt (by linarith)
  have hαβ : s ^ 2 + β ^ 2 = 1 := by linarith
  -- Step 2: Get adapted orthogonal basis
  obtain ⟨Q, hQ1, hQ2, hQa, hQb⟩ := adapted_basis_exists a b ha hb hcross
  -- Step 3: Define key matrices
  set E := Q.transpose * Matrix.diagonal v * Q with hE_def
  set M₀ : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, s ^ 2, s * β; 0, 0, 0] with hM₀_def
  have hE_symm : E.IsSymm := conj_diagonal_symm v Q
  -- Step 4: Reduce to adapted-basis trace expression
  rw [trace_reduction a b v Q s β rfl hαβ hQ1 hQ2 hQa hQb]
  -- Step 5: Apply the SOS theorem
  exact matrix_psd_rotated E hE_symm s β hαβ

set_option maxHeartbeats 6400000 in
/-- The core polynomial inequality: this is the algebraic content of psd_shift_from_normals. -/
lemma psd_poly_ineq
    (a b v : Fin 3 → ℝ) (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1) :
    let s := ∑ i, a i * b i
    0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, v i * v j *
      ((if i = j then (1 : ℝ) else 0) - a i * a j - b i * b j + s * a i * b j) *
      ((if i = j then (1 : ℝ) else 0) - a i * a j - b i * b j + s * a j * b i) +
    (1 / 8) * ∑ i, v i ^ 2 := by
  intro s
  by_cases hpar : a 0 * b 1 = a 1 * b 0 ∧ a 0 * b 2 = a 2 * b 0 ∧ a 1 * b 2 = a 2 * b 1
  · -- Case 1: a ∥ b (cross product = 0)
    simp only [Fin.sum_univ_three, Fin.isValue]
    simp +decide only []
    simp only [Fin.sum_univ_three] at ha hb
    obtain ⟨h01, h02, h12⟩ := hpar
    have hs : s = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
      simp [s, Fin.sum_univ_three];
    have hb_sub : ∀ i, b i = s * a i := by
      intro i
      fin_cases i <;> simp [hs];
      · grind +ring;
      · grind +ring;
      · grind +ring;
    norm_num [ hb_sub 0, hb_sub 1, hb_sub 2 ] at *;
    rw [ show ( 1 - a 0 * a 0 ) = a 1 * a 1 + a 2 * a 2 by linarith, show ( 1 - a 1 * a 1 ) = a 0 * a 0 + a 2 * a 2 by linarith, show ( 1 - a 2 * a 2 ) = a 0 * a 0 + a 1 * a 1 by linarith ] ; ring_nf ; norm_num;
    nlinarith only [ sq_nonneg ( v 0 * a 1 ^ 2 + v 1 * a 0 ^ 2 ), sq_nonneg ( v 0 * a 2 ^ 2 + v 2 * a 0 ^ 2 ), sq_nonneg ( v 1 * a 2 ^ 2 + v 2 * a 1 ^ 2 ), sq_nonneg ( a 0 * a 1 ), sq_nonneg ( a 0 * a 2 ), sq_nonneg ( a 1 * a 2 ), ha ]
  · -- Case 2: a and b are not parallel — use the extracted lemma
    push_neg at hpar
    have hcross : 0 < (a 1 * b 2 - a 2 * b 1) ^ 2 +
        (a 2 * b 0 - a 0 * b 2) ^ 2 + (a 0 * b 1 - a 1 * b 0) ^ 2 := by
      by_contra hle; push_neg at hle
      have hd0 : a 1 * b 2 = a 2 * b 1 := by nlinarith [sq_nonneg (a 1*b 2-a 2*b 1), sq_nonneg (a 2*b 0-a 0*b 2), sq_nonneg (a 0*b 1-a 1*b 0)]
      have hd1 : a 2 * b 0 = a 0 * b 2 := by nlinarith [sq_nonneg (a 1*b 2-a 2*b 1), sq_nonneg (a 2*b 0-a 0*b 2), sq_nonneg (a 0*b 1-a 1*b 0)]
      have hd2 : a 0 * b 1 = a 1 * b 0 := by nlinarith [sq_nonneg (a 1*b 2-a 2*b 1), sq_nonneg (a 2*b 0-a 0*b 2), sq_nonneg (a 0*b 1-a 1*b 0)]
      exact absurd hd0 (hpar hd2 hd1.symm)
    exact psd_poly_ineq_nonparallel a b v ha hb hcross

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 2048 in
lemma psd_shift_from_normals
    (a b v : Fin 3 → ℝ) (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1) :
    let P₁ := (1 : Matrix (Fin 3) (Fin 3) ℝ) - Matrix.of (fun i j => a i * a j)
    let P₂ := (1 : Matrix (Fin 3) (Fin 3) ℝ) - Matrix.of (fun i j => b i * b j)
    0 ≤ dotProduct v ((hadamard (P₁ * P₂) (P₂ * P₁) +
        (1 / 8 : ℝ) • (1 : Matrix _ _ ℝ)).mulVec v) := by
  intro P₁ P₂
  -- Reduce to pure polynomial inequality
  suffices h : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, v i * v j *
      ((if i = j then (1 : ℝ) else 0) - a i * a j - b i * b j + (∑ k, a k * b k) * a i * b j) *
      ((if i = j then (1 : ℝ) else 0) - a i * a j - b i * b j + (∑ k, a k * b k) * a j * b i) +
      (1 / 8) * ∑ i, v i ^ 2 by
    have heq : dotProduct v ((hadamard (P₁ * P₂) (P₂ * P₁) +
        (1 / 8 : ℝ) • (1 : Matrix _ _ ℝ)).mulVec v) =
      ∑ i : Fin 3, ∑ j : Fin 3, v i * v j *
        ((if i = j then (1 : ℝ) else 0) - a i * a j - b i * b j + (∑ k, a k * b k) * a i * b j) *
        ((if i = j then (1 : ℝ) else 0) - a i * a j - b i * b j + (∑ k, a k * b k) * a j * b i) +
      (1 / 8) * ∑ i, v i ^ 2 := by
      simp only [dotProduct, mulVec, hadamard, of_apply,
        one_apply, mul_apply, smul_apply, sub_apply, add_apply,
        Fin.sum_univ_three, Fin.isValue, smul_eq_mul, P₁, P₂]
      simp +decide only []
      norm_num
      ring
    linarith
  exact psd_poly_ineq a b v ha hb

lemma hadamard_square_psd_shift
    (P₁ P₂ : Matrix (Fin 3) (Fin 3) ℝ)
    (hP₁_sym : P₁.transpose = P₁)
    (hP₂_sym : P₂.transpose = P₂)
    (hP₁_idem : P₁ * P₁ = P₁)
    (hP₂_idem : P₂ * P₂ = P₂)
    (hP₁_rank : P₁.rank = 2)
    (hP₂_rank : P₂.rank = 2)
    (v : Fin 3 → ℝ) :
    0 ≤ dotProduct v ((hadamard (P₁ * P₂) (P₂ * P₁) +
        (1 / 8 : ℝ) • (1 : Matrix _ _ ℝ)).mulVec v) := by
  obtain ⟨n₁, hn₁, rfl⟩ := proj_rank_two_eq_id_sub_outer P₁ hP₁_sym hP₁_idem hP₁_rank
  obtain ⟨n₂, hn₂, rfl⟩ := proj_rank_two_eq_id_sub_outer P₂ hP₂_sym hP₂_idem hP₂_rank
  exact psd_shift_from_normals n₁ n₂ v hn₁ hn₂

/-
PROBLEM
For rank-2 projections in ℝ³, the images intersect nontrivially.

PROVIDED SOLUTION
Since P₁ and P₂ are rank-2 projections in ℝ³, the ranges (images) of P₁ and P₂ as linear maps are 2-dimensional subspaces of ℝ³. By the dimension formula:

dim(im P₁ ∩ im P₂) = dim(im P₁) + dim(im P₂) - dim(im P₁ + im P₂) ≥ 2 + 2 - 3 = 1.

So im P₁ ∩ im P₂ has dimension ≥ 1, meaning there exists a nonzero vector x in the intersection.

For x in im P₁, P₁ x = x (since P₁ is an idempotent and x is in its range). Similarly P₂ x = x.

Use `LinearMap.range (Matrix.mulVecLin P₁)` for the range. The rank is `Matrix.rank P₁ = Module.finrank ℝ (LinearMap.range (Matrix.mulVecLin P₁))`. The dimension formula is `Submodule.finrank_sup_add_finrank_inf_eq`.

For x in range P₁, there exists y with P₁ y = x. Then P₁ x = P₁ (P₁ y) = (P₁ * P₁) y = P₁ y = x (using idempotency). So P₁ x = x for all x in range P₁. Similarly for P₂. Use `Matrix.mulVec_mulVec` to relate P₁.mulVec (P₁.mulVec y) to (P₁ * P₁).mulVec y = P₁.mulVec y.
-/
lemma rank_two_proj_intersection_nonempty
    (P₁ P₂ : Matrix (Fin 3) (Fin 3) ℝ)
    (hP₁_idem : P₁ * P₁ = P₁)
    (hP₂_idem : P₂ * P₂ = P₂)
    (hP₁_rank : P₁.rank = 2)
    (hP₂_rank : P₂.rank = 2) :
    ∃ x : Fin 3 → ℝ, x ≠ 0 ∧ P₁.mulVec x = x ∧ P₂.mulVec x = x := by
  -- Since $P₁$ and $P₂$ are projections, their images are 2-dimensional subspaces of $\mathbb{R}^3$. The intersection of two 2-dimensional subspaces in $\mathbb{R}^3$ is at least 1-dimensional.
  have h_inter : Module.finrank ℝ (↥(LinearMap.range (Matrix.mulVecLin P₁) ⊓ LinearMap.range (Matrix.mulVecLin P₂))) ≥ 1 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq ( LinearMap.range ( Matrix.mulVecLin P₁ ) ) ( LinearMap.range ( Matrix.mulVecLin P₂ ) );
    linarith! [ show Module.finrank ℝ ( ↥ ( P₁.mulVecLin.range ⊔ P₂.mulVecLin.range ) ) ≤ 3 by exact le_trans ( Submodule.finrank_le _ ) ( by norm_num ) ];
  -- Since the intersection of the images of $P₁$ and $P₂$ is at least 1-dimensional, there exists a nonzero vector $x$ in this intersection.
  obtain ⟨x, hx_ne_zero, hx_inter⟩ : ∃ x : Fin 3 → ℝ, x ≠ 0 ∧ x ∈ LinearMap.range (Matrix.mulVecLin P₁) ⊓ LinearMap.range (Matrix.mulVecLin P₂) := by
    contrapose! h_inter;
    rw [ show ( P₁.mulVecLin.range ⊓ P₂.mulVecLin.range ) = ⊥ by exact eq_bot_iff.mpr fun x hx => Classical.not_not.1 fun hx' => h_inter x hx' hx ] ; norm_num;
  -- Since $x$ is in the image of $P₁$, there exists some $y$ such that $P₁.mulVec y = x$. Similarly, there exists some $z$ such that $P₂.mulVec z = x$.
  obtain ⟨y, hy⟩ : ∃ y : Fin 3 → ℝ, P₁.mulVec y = x := by
    aesop
  obtain ⟨z, hz⟩ : ∃ z : Fin 3 → ℝ, P₂.mulVec z = x := by
    aesop;
  -- Since $P₁$ and $P₂$ are projections, we have $P₁.mulVec x = x$ and $P₂.mulVec x = x$.
  have hP₁x : P₁.mulVec x = x := by
    simp +decide [ ← hy, hP₁_idem ]
  have hP₂x : P₂.mulVec x = x := by
    simp +decide [ ← hz, hP₂_idem ]
  use x, hx_ne_zero, hP₁x, hP₂x

/-
PROBLEM
For Hermitian A, if the sum of all entries is at least S, then some eigenvalue
is at least S / (Fintype.card n). Here we use the trace-eigenvalue identity
and the Rayleigh quotient with the all-ones vector.

PROVIDED SOLUTION
By `hA.trace_eq_sum_eigenvalues`, the trace of A equals the sum of eigenvalues: tr(A) = ∑ i, eigenvalue i. But the trace is also ∑ i, A i i.

We need a different approach since the sum of ALL entries (not just diagonal) is ≥ S.

Actually, ∑ i j, A i j = v^T A v where v = (1,1,1). And v^T A v = ∑ i, eigenvalue_i * (eigenvector_i · v)². Since eigenvectors form an orthonormal basis, ∑ i, (eigenvector_i · v)² = ||v||² = 3.

So ∑ i j, A i j = ∑ i, eigenvalue_i * w_i where w_i = (eigenvector_i · v)² ≥ 0 and ∑ w_i = 3.

If all eigenvalues < S/3, then ∑ eigenvalue_i * w_i < (S/3) * ∑ w_i = (S/3) * 3 = S. But ∑ eigenvalue_i * w_i = ∑ i j, A i j ≥ S, contradiction. So some eigenvalue ≥ S/3.

More precisely: by_contra h, push_neg at h to get ∀ i, eigenvalue i < S/3. Then ∑ i j, A i j = ∑ eigenvalue_i * w_i < (S/3) * 3 = S, contradicting hS.

To express ∑ i j, A i j = v^T A v for v = 1: use `Fin.sum_univ_three` and matrix multiplication.

For the spectral decomposition of v^T A v: use the spectral theorem A = U D U^T, then v^T A v = v^T U D U^T v = (U^T v)^T D (U^T v) = ∑ eigenvalue_i * (U^T v)_i². And ∑ (U^T v)_i² = ||U^T v||² = ||v||² = 3 (since U is orthogonal).
-/
lemma exists_eigenvalue_ge_of_entry_sum
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.IsHermitian) (S : ℝ)
    (hS : S ≤ ∑ i, ∑ j, A i j) :
    ∃ i : Fin 3, S / 3 ≤ hA.eigenvalues i := by
  -- By the properties of the trace and the sum of the entries, we know that $\sum_{i,j} A_{ij} = \sum_{i} \lambda_i$ where $\lambda_i$ are the eigenvalues of $A$.
  have h_trace_sum : ∑ i, ∑ j, A i j = ∑ i, hA.eigenvalues i * (hA.eigenvectorBasis i 0 + hA.eigenvectorBasis i 1 + hA.eigenvectorBasis i 2)^2 := by
    have := hA.spectral_theorem;
    conv_lhs => rw [ this ] ; norm_num [ Matrix.mul_apply ] ; ring_nf;
    simp +decide [ Fin.sum_univ_three, Matrix.diagonal ] ; ring;
  by_cases h_all_lt : ∀ i, hA.eigenvalues i < S / 3;
  · -- Since the sum of the squares of the eigenvector components is 3, we can simplify the inequality.
    have h_sum_squares : ∑ i, ((hA.eigenvectorBasis i).ofLp 0 + (hA.eigenvectorBasis i).ofLp 1 + (hA.eigenvectorBasis i).ofLp 2) ^ 2 = 3 := by
      have := hA.eigenvectorBasis.orthonormal;
      rw [ orthonormal_iff_ite ] at this;
      simp_all +decide [ Fin.sum_univ_three, inner ];
      grind +locals;
    have h_contradiction : ∑ i, hA.eigenvalues i * ((hA.eigenvectorBasis i).ofLp 0 + (hA.eigenvectorBasis i).ofLp 1 + (hA.eigenvectorBasis i).ofLp 2) ^ 2 < ∑ i, (S / 3) * ((hA.eigenvectorBasis i).ofLp 0 + (hA.eigenvectorBasis i).ofLp 1 + (hA.eigenvectorBasis i).ofLp 2) ^ 2 := by
      apply Finset.sum_lt_sum;
      · exact fun i _ => mul_le_mul_of_nonneg_right ( le_of_lt ( h_all_lt i ) ) ( sq_nonneg _ );
      · contrapose! h_sum_squares;
        exact ne_of_lt <| lt_of_le_of_lt ( Finset.sum_nonpos fun i _ => le_of_not_gt fun hi => by nlinarith only [ hi, h_all_lt i, h_sum_squares i <| Finset.mem_univ i ] ) <| by norm_num;
    simp_all +decide [ ← Finset.mul_sum _ _ _ ];
    linarith;
  · aesop

/-! ## Eigenvalue bounds -/

/-- For rank-2 orthogonal projections P₁, P₂ in ℝ³, all eigenvalues of the
Hadamard square `A = (P₁P₂) ∘ (P₂P₁)` are at least `-1/8`. -/
lemma eigenvalue_lower_bound
    (P₁ P₂ : Matrix (Fin 3) (Fin 3) ℝ)
    (hP₁_sym : P₁.transpose = P₁)
    (hP₂_sym : P₂.transpose = P₂)
    (hP₁_idem : P₁ * P₁ = P₁)
    (hP₂_idem : P₂ * P₂ = P₂)
    (hP₁_rank : P₁.rank = 2)
    (hP₂_rank : P₂.rank = 2)
    (hA_herm : (hadamard (P₁ * P₂) (P₂ * P₁)).IsHermitian) (i : Fin 3) :
    -(1 / 8) ≤ hA_herm.eigenvalues i := by
  apply eigenvalue_ge_neg_of_psd_shift _ hA_herm (1 / 8)
  exact hadamard_square_psd_shift P₁ P₂ hP₁_sym hP₂_sym hP₁_idem hP₂_idem hP₁_rank hP₂_rank

/-
PROBLEM
tr((P₁P₂)²) ≥ 1 for rank-2 symmetric idempotent P₁, P₂ with intersecting images.

PROVIDED SOLUTION
Use Cayley-Hamilton theorem and the fixed vector from rank_two_proj_intersection_nonempty.

Step 1: Get a nonzero x with P₁ x = x and P₂ x = x via rank_two_proj_intersection_nonempty.

Step 2: Let M = P₁ * P₂. Then Mx = x (since P₂x = x, P₁x = x, so Mx = P₁(P₂x) = P₁x = x).

Step 3: rank(M) ≤ 2 (since rank(P₁P₂) ≤ min(rank P₁, rank P₂) = 2, or use rank_mul_le). Therefore det(M) = 0 (a 3×3 matrix with rank ≤ 2 has zero determinant).

Step 4: By the Cayley-Hamilton theorem (Matrix.aeval_self_charpoly), M satisfies its characteristic polynomial. The characteristic polynomial of a 3×3 matrix M is:
χ(t) = t³ - (tr M)t² + s₂t - det(M)
where s₂ = ((tr M)² - tr(M²))/2.
With det(M) = 0: M³ = (tr M)·M² - s₂·M.

Step 5: Apply M³x = (tr M)M²x - s₂Mx. Since Mx = M²x = M³x = x:
x = (tr M)x - s₂x, so (tr M - s₂ - 1)x = 0.
Since x ≠ 0: s₂ = tr M - 1.

Step 6: tr(M²) = (tr M)² - 2s₂ = (tr M)² - 2(tr M) + 2 = (tr M - 1)² + 1 ≥ 1.

And ((P₁ * P₂) * (P₁ * P₂)).trace = tr(M²), so the result follows.
-/
lemma trace_sq_ge_one
    (P₁ P₂ : Matrix (Fin 3) (Fin 3) ℝ)
    (hP₁_idem : P₁ * P₁ = P₁)
    (hP₂_idem : P₂ * P₂ = P₂)
    (hP₁_rank : P₁.rank = 2)
    (hP₂_rank : P₂.rank = 2) :
    1 ≤ ((P₁ * P₂) * (P₁ * P₂)).trace := by
  -- By the Cayley-Hamilton theorem, we know that $M^3 = (\operatorname{tr} M)M^2 - s₂M$, where $s₂ = \frac{(\operatorname{tr} M)^2 - \operatorname{tr}(M^2)}{2}$.
  set M : Matrix (Fin 3) (Fin 3) ℝ := P₁ * P₂
  set trM : ℝ := M.trace
  set s₂ : ℝ := ((trM)^2 - (M^2).trace) / 2
  have h_cayley_hamilton : M^3 = (trM) • M^2 - s₂ • M := by
    -- By the Cayley-Hamilton theorem, we know that $M^3 = (\operatorname{tr} M)M^2 - s₂M$, where $s₂ = \frac{(\operatorname{tr} M)^2 - \operatorname{tr}(M^2)}{2}$. This follows from the characteristic polynomial of $M$.
    have h_char_poly : Matrix.charpoly M = Polynomial.X^3 - Polynomial.C trM * Polynomial.X^2 + Polynomial.C s₂ * Polynomial.X - Polynomial.C (Matrix.det M) := by
      simp +zetaDelta at *;
      simp +decide [ Matrix.charpoly, Matrix.det_fin_three, Matrix.trace_fin_three, pow_succ ];
      refine' Polynomial.funext fun x => _ ; norm_num [ Matrix.mul_apply, Fin.sum_univ_three ] ; ring;
    have h_cayley_hamilton : M^3 - (trM) • M^2 + s₂ • M - (Matrix.det M) • 1 = 0 := by
      rw [ ← Matrix.aeval_self_charpoly M, h_char_poly ];
      norm_num [ Algebra.smul_def ];
    -- Since $M$ is a $3 \times 3$ matrix with rank at most 2, its determinant is zero.
    have h_det_zero : Matrix.det M = 0 := by
      have h_det_zero : Matrix.rank M ≤ 2 := by
        exact le_trans ( Matrix.rank_mul_le_left _ _ ) ( by norm_num [ hP₁_rank ] );
      contrapose! h_det_zero;
      have := Matrix.rank_mul_le ( M⁻¹ ) M; simp_all +decide [ isUnit_iff_ne_zero ] ;
      linarith;
    simp_all +decide
    exact eq_of_sub_eq_zero ( by rw [ ← h_cayley_hamilton ] ; abel1 );
  -- Since $x \in \operatorname{im}(P₁) \cap \operatorname{im}(P₂)$, we have $Mx = x$.
  obtain ⟨x, hx_ne_zero, hx_P₁, hx_P₂⟩ : ∃ x : Fin 3 → ℝ, x ≠ 0 ∧ P₁.mulVec x = x ∧ P₂.mulVec x = x :=
    rank_two_proj_intersection_nonempty P₁ P₂ hP₁_idem hP₂_idem hP₁_rank hP₂_rank
  have hMx : M.mulVec x = x := by
    rw [ ← Matrix.mulVec_mulVec, hx_P₂, hx_P₁ ];
  -- Since $Mx = x$, we have $M^2x = M(Mx) = Mx = x$ and $M^3x = M(M^2x) = Mx = x$.
  have hM2x : M.mulVec (M.mulVec x) = x := by
    aesop
  have hM3x : M.mulVec (M.mulVec (M.mulVec x)) = x := by
    aesop;
  -- Substitute $Mx = x$, $M^2x = x$, and $M^3x = x$ into the Cayley-Hamilton equation.
  have h_subst : x = (trM) • x - s₂ • x := by
    have h_subst : M.mulVec (M.mulVec (M.mulVec x)) = (trM) • M.mulVec (M.mulVec x) - s₂ • M.mulVec x := by
      convert congr_arg ( fun m => m.mulVec x ) h_cayley_hamilton using 1 <;> norm_num [ pow_succ, Matrix.mul_assoc ];
      ext i; simp +decide [ Matrix.sub_mulVec, Matrix.smul_eq_diagonal_mul ] ;
      simp +decide [ Matrix.mulVec, dotProduct ];
      simp +decide only [Finset.mul_sum _ _ _, mul_assoc];
    grind;
  -- Since $x \neq 0$, we can divide both sides of the equation $x = (trM) • x - s₂ • x$ by $x$ to get $1 = trM - s₂$.
  have h_div : 1 = trM - s₂ := by
    exact Classical.not_not.1 fun h => hx_ne_zero <| by ext i; have := congr_fun h_subst i; norm_num at *; cases lt_or_gt_of_ne h <;> nlinarith;
  norm_num +zetaDelta at *;
  norm_num [ sq, Matrix.mul_assoc ] at * ; nlinarith [ sq_nonneg ( Matrix.trace ( P₁ * P₂ ) - 1 ) ]

/-
PROBLEM
The sum of all entries of the Hadamard square equals tr(M²).

PROVIDED SOLUTION
The sum ∑ i, ∑ j, hadamard (P₁ * P₂) (P₂ * P₁) i j equals ∑ i, ∑ j, (P₁ * P₂) i j * (P₂ * P₁) i j.

Since P₂ * P₁ = (P₁ * P₂)ᵀ (by `transpose_prod_symm`), we have (P₂ * P₁) i j = (P₁ * P₂) j i.

So the sum equals ∑ i, ∑ j, (P₁ * P₂) i j * (P₁ * P₂) j i = ∑ i, ((P₁ * P₂) * (P₁ * P₂)) i i = ((P₁ * P₂) * (P₁ * P₂)).trace.

This is just expanding the definitions of hadamard, matrix multiplication, and trace: hadamard A B i j = A i j * B i j, (A * B) i j = ∑ k, A i k * B k j, and trace M = ∑ i, M i i.
-/
lemma hadamard_entry_sum_eq
    (P₁ P₂ : Matrix (Fin 3) (Fin 3) ℝ)
    (hP₁_sym : P₁.transpose = P₁)
    (hP₂_sym : P₂.transpose = P₂) :
    ∑ i, ∑ j, hadamard (P₁ * P₂) (P₂ * P₁) i j = ((P₁ * P₂) * (P₁ * P₂)).trace := by
  simp +decide only [hadamard, mul_apply, trace];
  simp +decide only [Matrix.diag, mul_apply];
  simp_all +decide [ ← Matrix.ext_iff, Fin.sum_univ_three ];
  ring

lemma max_eigenvalue_lower_bound
    (P₁ P₂ : Matrix (Fin 3) (Fin 3) ℝ)
    (hP₁_sym : P₁.transpose = P₁)
    (hP₂_sym : P₂.transpose = P₂)
    (hP₁_idem : P₁ * P₁ = P₁)
    (hP₂_idem : P₂ * P₂ = P₂)
    (hP₁_rank : P₁.rank = 2)
    (hP₂_rank : P₂.rank = 2)
    (hA_herm : (hadamard (P₁ * P₂) (P₂ * P₁)).IsHermitian) :
    ∃ i : Fin 3, 1 / 3 ≤ hA_herm.eigenvalues i := by
  apply exists_eigenvalue_ge_of_entry_sum _ hA_herm 1
  rw [hadamard_entry_sum_eq P₁ P₂ hP₁_sym hP₂_sym]
  exact trace_sq_ge_one P₁ P₂ hP₁_idem hP₂_idem hP₁_rank hP₂_rank

/-! ## Main theorem -/

/-- For 3×3 real orthogonal projection matrices P₁, P₂ of rank 2, the Hadamard product
`A = (P₁P₂) ∘ (P₂P₁)` satisfies `tr(A^k) ≥ 0` for every `k : ℕ`. -/
theorem power_nonneg_dim_three_rank_two_core
    (P₁ P₂ : Matrix (Fin 3) (Fin 3) ℝ)
    (hP₁_sym : P₁.transpose = P₁)
    (hP₂_sym : P₂.transpose = P₂)
    (hP₁_idem : P₁ * P₁ = P₁)
    (hP₂_idem : P₂ * P₂ = P₂)
    (hP₁_rank : P₁.rank = 2)
    (hP₂_rank : P₂.rank = 2)
    (k : ℕ) :
    0 ≤ (hadamard (P₁ * P₂) (P₂ * P₁) ^ k).trace := by
  set A := hadamard (P₁ * P₂) (P₂ * P₁) with hA_def
  have hA_symm : A.IsSymm := hadamard_prod_isSymm P₁ P₂ hP₁_sym hP₂_sym
  have hA_herm : A.IsHermitian := isSymm_to_isHermitian A hA_symm
  rw [IsHermitian.trace_pow_eq_sum_eigenvalues_pow A hA_herm k]
  exact fin3_sum_pow_nonneg (fun i => hA_herm.eigenvalues i)
    (eigenvalue_lower_bound P₁ P₂ hP₁_sym hP₂_sym hP₁_idem hP₂_idem hP₁_rank hP₂_rank hA_herm)
    (max_eigenvalue_lower_bound P₁ P₂ hP₁_sym hP₂_sym hP₁_idem hP₂_idem hP₁_rank hP₂_rank hA_herm)
    k

end

/-- The hard case: rank 2 projections in dimension 3.
    The proof in the paper uses eigenvalue bounds:
    all eigenvalues ≥ -1/8 and max eigenvalue ≥ 1/3,
    from which power-nonnegativity follows since (1/3)^m > 2·(1/8)^m for all m ≥ 1. -/
lemma power_nonneg_dim_three_rank_two
    (P₁ P₂ : Matrix (Fin 3) (Fin 3) ℝ)
    (h₁ : IsOrthProj P₁) (h₂ : IsOrthProj P₂)
    (hrank : P₁.rank = P₂.rank)
    (hrank2 : P₁.rank = 2) :
    IsPowerNonneg (hadamardSquare P₁ P₂) := by
  intro m
  exact power_nonneg_dim_three_rank_two_core P₁ P₂ h₁.2 h₂.2 h₁.1 h₂.1 hrank2
    (hrank.symm.trans hrank2) m

/-- n=3 case: power-nonneg via eigenvalue bounds. -/
lemma power_nonneg_dim_three
    (P₁ P₂ : Matrix (Fin 3) (Fin 3) ℝ)
    (h₁ : IsOrthProj P₁) (h₂ : IsOrthProj P₂)
    (hrank : P₁.rank = P₂.rank) :
    IsPowerNonneg (hadamardSquare P₁ P₂) := by
  -- Case split on rank of P₁ (which equals rank of P₂)
  have h_rank_le : P₁.rank ≤ 3 := by
    have := P₁.rank_le_card_height; simp [Fintype.card_fin] at this; exact this
  by_cases h0 : P₁.rank ≤ 1
  · exact isPowerNonneg_of_posSemidef _ (hadamardSquare_posSemidef_rank_le_one_or_full P₁ P₂ h₁ h₂ hrank (Or.inl h0))
  · by_cases h2 : P₁.rank = 2
    · exact power_nonneg_dim_three_rank_two P₁ P₂ h₁ h₂ hrank h2
    · exact isPowerNonneg_of_posSemidef _ (hadamardSquare_posSemidef_rank_le_one_or_full P₁ P₂ h₁ h₂ hrank (Or.inr (by omega)))

/-- For n ≤ 3, A = (P₁P₂) ∘ (P₂P₁) is always power-nonnegative,
    for any admissible pair P₁, P₂. -/
theorem power_nonneg_dim_le_three (n : ℕ) (hn : n ≤ 3)
    (P₁ P₂ : Matrix (Fin n) (Fin n) ℝ)
    (h₁ : IsOrthProj P₁) (h₂ : IsOrthProj P₂)
    (hrank : P₁.rank = P₂.rank) :
    IsPowerNonneg (hadamardSquare P₁ P₂) := by
  interval_cases n
  · exact power_nonneg_dim_zero P₁ P₂
  · exact power_nonneg_dim_one P₁ P₂ h₁ hrank
  · exact power_nonneg_dim_two P₁ P₂ h₁ h₂
  · exact power_nonneg_dim_three P₁ P₂ h₁ h₂ hrank

/-! ## Theorem 7: Minimality -/

/-
PROBLEM
For any admissible pair P₁, P₂ and k ≤ 2, tr(Aᵏ) ≥ 0.
    k=0: trace of identity; k=1: Proposition 5; k=2: even case.

PROVIDED SOLUTION
Do interval_cases on k (k can be 0, 1, or 2):
- k = 0: (hadamardSquare P₁ P₂)^0 = 1, trace of 1 = Fintype.card n, which is ≥ 0 (cast to ℝ).
- k = 1: simp [pow_one], then use trace_hadamardSquare_nonneg P₁ P₂ h₁ h₂.
- k = 2: use trace_hadamardSquare_pow_nonneg_even with ⟨1, rfl⟩ for Even 2.
-/
theorem trace_hadamardSquare_pow_nonneg_le2 {n : Type*} [Fintype n] [DecidableEq n]
    (P₁ P₂ : Matrix n n ℝ)
    (h₁ : IsOrthProj P₁) (h₂ : IsOrthProj P₂)
    (k : ℕ) (hk : k ≤ 2) :
    0 ≤ ((hadamardSquare P₁ P₂) ^ k).trace := by
  interval_cases k <;> simp +decide [ *, sq ];
  · exact trace_hadamardSquare_nonneg P₁ P₂ h₁ h₂;
  · convert trace_hadamardSquare_pow_nonneg_even P₁ P₂ h₁ h₂ 2 ( by decide ) using 1;
    rw [ pow_two ]

/-! ## Theorem 6: Explicit counterexample for n=4, k=3 -/

/-- The explicit P₁ from Theorem 6, as a rational matrix over Fin 4. -/
def P₁_example : Matrix (Fin 4) (Fin 4) ℚ :=
  !![3/5, -1/5, 1/5, -2/5;
     -1/5, 2/5, -2/5, -1/5;
     1/5, -2/5, 2/5, 1/5;
     -2/5, -1/5, 1/5, 3/5]

/-- The explicit P₂ from Theorem 6, as a rational matrix over Fin 4. -/
def P₂_example : Matrix (Fin 4) (Fin 4) ℚ :=
  !![7/20, 9/20, -1/20, 3/20;
     9/20, 13/20, 3/20, 1/20;
     -1/20, 3/20, 13/20, -9/20;
     3/20, 1/20, -9/20, 7/20]

/-
PROBLEM
The smallest dimension admitting a counterexample to power-nonnegativity is n = 4.

The smallest dimension admitting a counterexample to power-nonnegativity is n = 4.
    Note: this depends on `power_nonneg_dim_le_three` (Proposition 2).

PROVIDED SOLUTION
Split into ⟨part1, part2⟩.

Part 1: Same counterexample as in min_counterexample_exp. Use n=4, the same real-valued matrices from P₁_example and P₂_example. Show ¬ IsPowerNonneg by showing tr(A³) < 0 (witness m = 3). The construction is the same as in min_counterexample_exp.

Part 2: Use power_nonneg_dim_le_three directly.

For the first conjunct, use the same matrices as in min_counterexample_exp: use Matrix.of (fun i j => (P₁_example i j : ℝ)) and Matrix.of (fun i j => (P₂_example i j : ℝ)). Prove IsOrthProj by ext/fin_cases/norm_num as in min_counterexample_exp. Prove rank equality using the rank_eq_trace argument from min_counterexample_exp. For ¬ IsPowerNonneg, introduce h and apply h 3 to get 0 ≤ tr(A³), then compute the trace using norm_num/norm_cast/native_decide to derive a contradiction (since tr(A³) < 0 by counterexample_trace_cube_neg).
-/
set_option maxHeartbeats 1600000 in
theorem min_counterexample_dim :
    (∃ (P₁ P₂ : Matrix (Fin 4) (Fin 4) ℝ),
      IsOrthProj P₁ ∧ IsOrthProj P₂ ∧ P₁.rank = P₂.rank ∧
      ¬ IsPowerNonneg (hadamardSquare P₁ P₂)) ∧
    (∀ (n : ℕ) (_ : n ≤ 3) (P₁ P₂ : Matrix (Fin n) (Fin n) ℝ),
      IsOrthProj P₁ → IsOrthProj P₂ → P₁.rank = P₂.rank →
      IsPowerNonneg (hadamardSquare P₁ P₂)) := by
  constructor
  · -- Counterexample for n=4
    unfold IsOrthProj hadamardSquare IsPowerNonneg;
    simp +zetaDelta at *;
    refine' ⟨ Matrix.of fun i j => ( P₁_example i j : ℝ ), _, Matrix.of fun i j => ( P₂_example i j : ℝ ), _, _, _ ⟩ <;> norm_cast;
    · norm_num [ ← Matrix.ext_iff, Fin.forall_fin_succ ];
      norm_num [ Fin.sum_univ_succ, Matrix.mul_apply, P₁_example ];
      repeat erw [ Matrix.cons_val_succ' ] ; norm_num;
    · constructor <;> ext i j <;> norm_num [ Matrix.mul_apply, P₂_example ];
      · fin_cases i <;> fin_cases j <;> norm_num [ Fin.sum_univ_succ ];
      · fin_cases i <;> fin_cases j <;> rfl;
    · rw [ Matrix.rank, Matrix.rank ];
      -- Since these are orthogonal projections, their ranks are equal to their traces.
      have h_rank_eq_trace : ∀ (P : Matrix (Fin 4) (Fin 4) ℝ), P * P = P ∧ P.transpose = P → Matrix.rank P = Matrix.trace P := by
        intro P hP;
        -- Since P is symmetric and idempotent, it is diagonalizable with eigenvalues 0 or 1.
        have h_diag : ∃ D : Matrix (Fin 4) (Fin 4) ℝ, D.transpose * D = 1 ∧ D * D.transpose = 1 ∧ ∃ d : Fin 4 → ℝ, (∀ i, d i = 0 ∨ d i = 1) ∧ P = D * Matrix.diagonal d * D.transpose := by
          have h_diag : ∃ D : Matrix (Fin 4) (Fin 4) ℝ, D.transpose * D = 1 ∧ D * D.transpose = 1 ∧ ∃ d : Fin 4 → ℝ, P = D * Matrix.diagonal d * D.transpose := by
            have h_diag : ∃ D : Matrix (Fin 4) (Fin 4) ℝ, D.transpose * D = 1 ∧ D * D.transpose = 1 ∧ ∃ d : Fin 4 → ℝ, P = D * Matrix.diagonal d * D.transpose := by
              have h_symm : Matrix.IsHermitian P := by
                exact hP.2
              have := h_symm.spectral_theorem;
              refine' ⟨ _, _, _, _, this ⟩;
              · simp +decide [ mul_eq_one_comm ];
                convert h_symm.eigenvectorUnitary.2.2 using 1;
              · simp +decide
                have := h_symm.eigenvectorUnitary.2.2;
                convert this using 1;
            exact h_diag;
          obtain ⟨ D, hD₁, hD₂, d, rfl ⟩ := h_diag;
          refine' ⟨ D, hD₁, hD₂, d, _, rfl ⟩;
          intro i; replace hP := congr_arg ( fun m => Dᵀ * m * D ) hP.1; simp_all +decide [ Matrix.mul_assoc ] ;
          simp_all +decide [ ← Matrix.mul_assoc ];
          exact or_iff_not_imp_left.mpr fun hi => mul_left_cancel₀ hi <| by linarith [ hP i ] ;
        obtain ⟨ D, hD₁, hD₂, d, hd₁, rfl ⟩ := h_diag;
        -- Since $D$ is orthogonal, the rank of $D * \text{diagonal } d * Dᵀ$ is equal to the rank of $\text{diagonal } d$.
        have h_rank_diag : Matrix.rank (D * Matrix.diagonal d * Dᵀ) = Matrix.rank (Matrix.diagonal d) := by
          have h_rank_diag : Matrix.rank (D * Matrix.diagonal d * Dᵀ) ≤ Matrix.rank (Matrix.diagonal d) := by
            have h_rank_diag : Matrix.rank (D * Matrix.diagonal d * Dᵀ) ≤ Matrix.rank (D * Matrix.diagonal d) := by
              exact Matrix.rank_mul_le_left _ _;
            exact h_rank_diag.trans ( Matrix.rank_mul_le_right _ _ );
          refine' le_antisymm h_rank_diag _;
          have h_rank_diag : Matrix.rank (Dᵀ * (D * Matrix.diagonal d * Dᵀ) * D) ≤ Matrix.rank (D * Matrix.diagonal d * Dᵀ) := by
            exact Matrix.rank_mul_le_left _ _ |> le_trans <| Matrix.rank_mul_le_right _ _;
          simp_all +decide [ ← mul_assoc ];
          simp_all +decide [ Matrix.mul_assoc ];
        rw [ h_rank_diag, Matrix.rank_diagonal ];
        simp_all +decide [ Matrix.trace_mul_comm, Matrix.mul_assoc ];
        rw [ Fintype.card_subtype ];
        rw [ Finset.sum_congr rfl fun i hi => show d i = if d i = 0 then 0 else 1 by cases hd₁ i <;> split_ifs <;> linarith ] ; norm_num [ Finset.sum_ite ];
        rw [ Finset.filter_not, Finset.card_sdiff ] ; norm_num [ Finset.card_univ ];
      have h_trace_eq : Matrix.trace (Matrix.of (fun i j => (P₁_example i j : ℝ))) = Matrix.trace (Matrix.of (fun i j => (P₂_example i j : ℝ))) := by
        norm_num [ Matrix.trace, P₁_example, P₂_example ];
        norm_num [ Fin.sum_univ_succ ];
      have h_rank_eq_trace : Matrix.rank (Matrix.of (fun i j => (P₁_example i j : ℝ))) = Matrix.trace (Matrix.of (fun i j => (P₁_example i j : ℝ))) ∧ Matrix.rank (Matrix.of (fun i j => (P₂_example i j : ℝ))) = Matrix.trace (Matrix.of (fun i j => (P₂_example i j : ℝ))) := by
        apply And.intro;
        · apply h_rank_eq_trace;
          norm_num [ ← Matrix.ext_iff, Fin.forall_fin_succ ];
          norm_num [ Fin.sum_univ_succ, Matrix.mul_apply, P₁_example ] at *;
          repeat erw [ Matrix.cons_val_succ' ] ; norm_num;
        · apply h_rank_eq_trace;
          constructor <;> ext i j <;> norm_num [ Matrix.mul_apply, P₂_example ];
          · fin_cases i <;> fin_cases j <;> norm_num [ Fin.sum_univ_succ ];
          · fin_cases i <;> fin_cases j <;> rfl;
      exact_mod_cast h_rank_eq_trace.1.trans h_trace_eq |> Eq.trans <| h_rank_eq_trace.2.symm;
    · use 3
      norm_num [Matrix.trace, Matrix.mul_apply, pow_three, hadamardSquare]
      norm_num [P₁_example, P₂_example, Matrix.hadamard, Fin.sum_univ_succ]
  · exact fun n hn P₁ P₂ h₁ h₂ h₃ => power_nonneg_dim_le_three n hn P₁ P₂ h₁ h₂ h₃

/-
PROBLEM
The smallest exponent admitting a counterexample is k = 3.
    For k = 0, 1, 2, tr(Aᵏ) ≥ 0 always holds.

PROVIDED SOLUTION
Split into ⟨part1, part2⟩.

Part 2 is easy: intro n P₁ P₂ h₁ h₂, then use trace_hadamardSquare_pow_nonneg_le2.

Part 1: We need to produce real matrices. Use P₁_example.map (algebraMap ℚ ℝ) and P₂_example.map (algebraMap ℚ ℝ). We know:
- P₁_example * P₁_example = P₁_example and P₁_example.transpose = P₁_example (from P₁_example_isOrthProj)
- Same for P₂
- counterexample_trace_cube_neg : (A_example ^ 3).trace < 0

The key insight is that Matrix.map preserves multiplication (via RingHom.map_matrix_mul or Matrix.map_mul for ring homs), transpose, and trace. So the real versions satisfy the same properties.

Use algebraMap ℚ ℝ as a ring homomorphism. Then:
- Matrix.map (P * P) f = Matrix.map P f * Matrix.map P f (by map_mul)
- Matrix.map Pᵀ f = (Matrix.map P f)ᵀ
- Similarly for hadamard and trace

For rank equality: both have rank 2. Since P₁_example and P₂_example have equal traces (both = 2), and for orthogonal projections rank = trace, the real versions have equal rank.

This may be complex. An alternative: directly define P₁_real and P₂_real with the same entries as ℝ values and use norm_num / native_decide to verify them.
-/
set_option maxHeartbeats 1600000 in
theorem min_counterexample_exp :
    (∃ (n : ℕ) (P₁ P₂ : Matrix (Fin n) (Fin n) ℝ),
      IsOrthProj P₁ ∧ IsOrthProj P₂ ∧ P₁.rank = P₂.rank ∧
      ¬ (0 ≤ ((hadamardSquare P₁ P₂) ^ 3).trace)) ∧
    (∀ (n : ℕ) (P₁ P₂ : Matrix (Fin n) (Fin n) ℝ),
      IsOrthProj P₁ → IsOrthProj P₂ →
      (∀ k : ℕ, k ≤ 2 → 0 ≤ ((hadamardSquare P₁ P₂) ^ k).trace)) := by
  refine' ⟨ _, fun n P₁ P₂ h₁ h₂ k hk => _ ⟩;
  · use 4, Matrix.of ( fun i j => ( P₁_example i j : ℝ ) ), Matrix.of ( fun i j => ( P₂_example i j : ℝ ) );
    refine' ⟨ _, _, _, _ ⟩;
    · constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [ P₁_example ];
      all_goals norm_num [ Fin.sum_univ_succ, Matrix.mul_apply ] ;
    · constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [ P₂_example ];
      all_goals norm_num [ Fin.sum_univ_succ, Matrix.mul_apply ] ;
    · -- Since these matrices are orthogonal projections, their ranks are equal to their traces.
      have h_rank_eq_trace : ∀ (P : Matrix (Fin 4) (Fin 4) ℝ), P * P = P → P.transpose = P → Matrix.rank P = Matrix.trace P := by
        intro P hP hP';
        -- Since $P$ is an orthogonal projection, we have $P^2 = P$ and $P^T = P$. Therefore, $P$ is diagonalizable with eigenvalues $0$ or $1$.
        have h_diag : ∃ D : Matrix (Fin 4) (Fin 4) ℝ, D.transpose * D = 1 ∧ D * D.transpose = 1 ∧ ∃ d : Fin 4 → ℝ, (∀ i, d i = 0 ∨ d i = 1) ∧ P = D * Matrix.diagonal d * D.transpose := by
          have h_diag : ∃ D : Matrix (Fin 4) (Fin 4) ℝ, D.transpose * D = 1 ∧ D * D.transpose = 1 ∧ ∃ d : Fin 4 → ℝ, P = D * Matrix.diagonal d * D.transpose := by
            have h_diag : ∃ D : Matrix (Fin 4) (Fin 4) ℝ, D.transpose * D = 1 ∧ D * D.transpose = 1 ∧ ∃ d : Fin 4 → ℝ, P = D * Matrix.diagonal d * D.transpose := by
              have h_symm : Matrix.IsHermitian P := by
                finiteness
              have := h_symm.spectral_theorem;
              refine' ⟨ _, _, _, _, this ⟩;
              · simp +decide [ mul_eq_one_comm ];
                convert h_symm.eigenvectorUnitary.2.2 using 1;
              · convert h_symm.eigenvectorUnitary.2.2 using 1;
            exact h_diag;
          obtain ⟨ D, hD₁, hD₂, d, rfl ⟩ := h_diag;
          refine' ⟨ D, hD₁, hD₂, d, _, rfl ⟩;
          intro i; replace hP := congr_arg ( fun m => Dᵀ * m * D ) hP; simp_all +decide [ Matrix.mul_assoc ] ;
          simp_all +decide [ ← Matrix.mul_assoc, mul_eq_one_comm.mp hD₁ ];
          exact or_iff_not_imp_left.mpr fun hi => mul_left_cancel₀ hi <| by linarith [ hP i ] ;
        obtain ⟨ D, hD₁, hD₂, d, hd₁, rfl ⟩ := h_diag; simp_all +decide [ Matrix.trace_mul_comm, Matrix.mul_assoc ] ;
        -- Since $D$ is orthogonal, we have $\text{rank}(D * \text{diagonal}(d) * D^T) = \text{rank}(\text{diagonal}(d))$.
        have h_rank_diag : Matrix.rank (D * Matrix.diagonal d * D.transpose) = Matrix.rank (Matrix.diagonal d) := by
          have h_rank_diag : Matrix.rank (D * Matrix.diagonal d * D.transpose) ≤ Matrix.rank (Matrix.diagonal d) := by
            have h_rank_diag : Matrix.rank (D * Matrix.diagonal d * D.transpose) ≤ Matrix.rank (D * Matrix.diagonal d) := by
              exact Matrix.rank_mul_le_left _ _;
            exact h_rank_diag.trans ( Matrix.rank_mul_le_right _ _ );
          have h_rank_diag : Matrix.rank (D * Matrix.diagonal d * D.transpose) ≥ Matrix.rank (D.transpose * (D * Matrix.diagonal d * D.transpose) * D) := by
            exact Matrix.rank_mul_le_left _ _ |> le_trans <| Matrix.rank_mul_le_right _ _ |> le_trans <| by norm_num;
          grind +locals;
        simp_all +decide [ ← Matrix.mul_assoc, Matrix.rank_diagonal ];
        rw [ Fintype.card_subtype ];
        rw [ Finset.sum_congr rfl fun i hi => show d i = if d i = 0 then 0 else 1 by cases hd₁ i <;> split_ifs <;> linarith ] ; norm_num [ Finset.sum_ite ] ; ring_nf;
        rw [ Finset.filter_not, Finset.card_sdiff ] ; norm_num [ Finset.card_univ ];
      have h_trace_eq : Matrix.trace (Matrix.of (fun i j => (P₁_example i j : ℝ))) = Matrix.trace (Matrix.of (fun i j => (P₂_example i j : ℝ))) := by
        norm_num [ Matrix.trace, P₁_example, P₂_example ];
        norm_num [ Fin.sum_univ_succ ];
      have h_rank_eq_trace_P1 : Matrix.rank (Matrix.of (fun i j => (P₁_example i j : ℝ))) = Matrix.trace (Matrix.of (fun i j => (P₁_example i j : ℝ))) := by
        apply h_rank_eq_trace;
        · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, P₁_example, Fin.sum_univ_succ];
        · ext i j; fin_cases i <;> fin_cases j <;> rfl;
      have h_rank_eq_trace_P2 : Matrix.rank (Matrix.of (fun i j => (P₂_example i j : ℝ))) = Matrix.trace (Matrix.of (fun i j => (P₂_example i j : ℝ))) := by
        apply h_rank_eq_trace;
        · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, P₂_example, Fin.sum_univ_succ];
        · ext i j; fin_cases i <;> fin_cases j <;> rfl;
      exact_mod_cast h_rank_eq_trace_P1.trans h_trace_eq |> Eq.trans <| h_rank_eq_trace_P2.symm;
    · unfold hadamardSquare; norm_num [Matrix.trace, Matrix.mul_apply, pow_three, P₁_example, P₂_example, Matrix.hadamard, Fin.sum_univ_succ];
  · convert trace_hadamardSquare_pow_nonneg_le2 P₁ P₂ h₁ h₂ k hk using 1

/-! ## Counterexample theorems using IsCounterexample -/

section counterexample_CE
set_option maxHeartbeats 3200000

/-
PROBLEM
`A_example` (cast to ℝ) is a counterexample to power-nonnegativity at dimension 4
    and exponent 3.

PROVIDED SOLUTION
Unfold IsCounterexample and provide P₁ = Matrix.of (fun i j => (P₁_example i j : ℝ)) and P₂ = Matrix.of (fun i j => (P₂_example i j : ℝ)) as the witnesses.

For IsOrthProj: prove by ext/fin_cases/norm_num (same approach as min_counterexample_exp proof). P₁_example and P₂_example are defined as specific 4x4 rational matrices.

For rank equality: use the same rank_eq_trace argument from min_counterexample_dim proof — orthogonal projections satisfy rank P = trace P, and both traces are equal.

For A = hadamardSquare P₁ P₂: use rfl.

For ¬ (0 ≤ (A ^ 3).trace): unfold hadamardSquare, then norm_num/norm_cast/native_decide to show the trace is negative.

The proof structure should be: refine ⟨_, _, ?_, ?_, ?_, rfl, ?_⟩ then prove each goal. Use the same proof approach that min_counterexample_exp uses for the IsOrthProj, rank equality, and trace negativity parts.
-/
theorem A_example_isCounterexample :
    IsCounterexample 4 3 (hadamardSquare
      (Matrix.of (fun i j => (P₁_example i j : ℝ)))
      (Matrix.of (fun i j => (P₂_example i j : ℝ)))) := by
  have hP₁ : IsOrthProj (Matrix.of (fun i j => (P₁_example i j : ℝ))) := by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, P₁_example ];
    all_goals norm_num [ Fin.sum_univ_succ, Fin.sum_univ_zero ] at *
  have hP₂ : IsOrthProj (Matrix.of (fun i j => (P₂_example i j : ℝ))) := by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> norm_num [ Matrix.mul_apply, P₂_example ];
    all_goals norm_num [ Fin.sum_univ_succ, Fin.sum_univ_zero ] ;
  refine' ⟨ _, _, hP₁, hP₂, (orthProj_unitEquiv_iff_rank _ _ hP₁ hP₂).mp ?_, rfl, ?_ ⟩;
  · -- Since these matrices are orthogonal projections, their ranks are equal to the number of independent rows or columns.
    have h_rank_eq : ∀ (P : Matrix (Fin 4) (Fin 4) ℝ), P * P = P → P.transpose = P → P.rank = P.trace := by
      intro P hP hP_symm
      have h_diag : ∃ Q : Matrix (Fin 4) (Fin 4) ℝ, Q.transpose * Q = 1 ∧ ∃ D : Matrix (Fin 4) (Fin 4) ℝ, D.IsDiag ∧ P = Q * D * Q.transpose := by
        have := Matrix.IsHermitian.spectral_theorem hP_symm
        generalize_proofs at *; (
        refine' ⟨ _, _, _, _, this ⟩ <;> norm_num [ Matrix.mul_assoc, mul_eq_one_comm ] at *; (
        have := IsHermitian.eigenvectorUnitary hP_symm |>.2.2
        generalize_proofs at *; (
        convert this using 1)))
      generalize_proofs at *;
      obtain ⟨ Q, hQ₁, D, hD₁, rfl ⟩ := h_diag
      have h_diag_trace : D.trace = D.rank := by
        have h_diag_trace : ∀ i, D i i = 0 ∨ D i i = 1 := by
          have h_diag_trace : ∀ i, D i i ^ 2 = D i i := by
            have h_diag_trace : D * D = D := by
              grind +qlia
            generalize_proofs at *; (
            intro i; replace h_diag_trace := congr_fun ( congr_fun h_diag_trace i ) i; simp_all +decide [ sq, Matrix.mul_apply ] ;
            rw [ Finset.sum_eq_single i ] at h_diag_trace <;> aesop)
          generalize_proofs at *; (
          exact fun i => or_iff_not_imp_left.mpr fun hi => mul_left_cancel₀ hi <| by linarith [ h_diag_trace i ] ;)
        generalize_proofs at *; (
        have h_diag_trace : D.rank = ∑ i, if D i i = 1 then 1 else 0 := by
          have h_diag_trace : D = Matrix.diagonal (fun i => D i i) := by
            ext i j; by_cases hi : i = j <;> aesop;
          generalize_proofs at *; (
          rw [ h_diag_trace, Matrix.rank_diagonal ] ; norm_num [ Finset.sum_ite ] ; ring_nf;
          rw [ Fintype.card_subtype ] ; rw [ Finset.card_filter ] ; rw [ tsub_eq_of_eq_add ] ; ring_nf;
          rw [ Finset.sum_congr rfl fun i hi => show ( if D i i = 0 then 1 else 0 ) = 1 - ( if D i i = 1 then 1 else 0 ) by rcases ‹∀ i, D i i = 0 ∨ D i i = 1› i with h | h <;> norm_num [ h ] ] ; ring_nf;
          rw [ Finset.sum_congr rfl fun i hi => show ( 1 - if D i i = 1 then 1 else 0 ) = if D i i = 1 then 0 else 1 by rcases ‹∀ i, D i i = 0 ∨ D i i = 1› i with h | h <;> norm_num [ h ] ] ; norm_num [ Finset.sum_ite ] ; ring_nf;
          rw [ Finset.card_filter_add_card_filter_not, Finset.card_fin ])
        generalize_proofs at *; (
        simp_all +decide [ Matrix.trace ];
        rw [ Finset.sum_congr rfl fun i hi => show D i i = if D i i = 1 then 1 else 0 by cases ‹∀ i, D i i = 0 ∨ D i i = 1› i <;> aesop ] ; aesop;))
      generalize_proofs at *; (
      have h_diag_trace : (Q * D * Qᵀ).trace = D.trace := by
        rw [ Matrix.trace_mul_comm ];
        rw [ ← Matrix.mul_assoc, hQ₁, Matrix.one_mul ]
      generalize_proofs at *; (
      have h_diag_trace : Matrix.rank (Q * D * Qᵀ) = Matrix.rank D := by
        have h_diag_trace : (Q * D * Qᵀ).rank ≤ D.rank := by
          exact Matrix.rank_mul_le_left _ _ |> le_trans <| Matrix.rank_mul_le_right _ _ |> le_trans <| by norm_num;
        generalize_proofs at *; (
        have h_diag_trace : Matrix.rank D ≤ Matrix.rank (Q * D * Qᵀ) := by
          have h_diag_trace : Matrix.rank D ≤ Matrix.rank (Qᵀ * (Q * D * Qᵀ) * Q) := by
            simp +decide [ ← Matrix.mul_assoc, hQ₁ ];
            simp +decide [ Matrix.mul_assoc, hQ₁ ]
          exact h_diag_trace.trans ( Matrix.rank_mul_le_left _ _ |> le_trans <| Matrix.rank_mul_le_right _ _ ) |> le_trans <| by simp +decide
        generalize_proofs at *; (
        linarith))
      generalize_proofs at *; aesop;))
    generalize_proofs at *; (
    convert congr_arg ( fun x : ℝ => Int.floor x ) ( congr_arg₂ ( · - · ) ( h_rank_eq ( Matrix.of fun i j => ( P₁_example i j : ℝ ) ) ?_ ?_ ) ( h_rank_eq ( Matrix.of fun i j => ( P₂_example i j : ℝ ) ) ?_ ?_ ) ) using 1 <;> norm_num [ Matrix.trace ];
    · unfold P₁_example P₂_example; norm_num [ Fin.sum_univ_succ ] ;
      norm_num [ sub_eq_zero ];
    · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, P₁_example, Fin.sum_univ_succ];
    · ext i j; fin_cases i <;> fin_cases j <;> rfl;
    · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, P₂_example, Fin.sum_univ_succ];
    · ext i j; fin_cases i <;> fin_cases j <;> rfl;);
  · unfold hadamardSquare; norm_num [Matrix.trace, Matrix.mul_apply, pow_three, P₁_example, P₂_example, Matrix.hadamard, Fin.sum_univ_succ]

/-- The smallest dimension admitting a counterexample to power-nonnegativity is n = 4.
    Rephrased using `IsCounterexample`. -/
theorem min_counterexample_dim_CE :
    (∃ A, IsCounterexample 4 3 A) ∧
    (∀ n (_ : n ≤ 3) k (A : Matrix (Fin n) (Fin n) ℝ), ¬ IsCounterexample n k A) := by
  exact ⟨⟨_, A_example_isCounterexample⟩, fun n hn k A ⟨P₁, P₂, h₁, h₂, hequiv, hA, htr⟩ =>
    htr (hA ▸ min_counterexample_dim.2 n hn P₁ P₂ h₁ h₂
      ((orthProj_unitEquiv_iff_rank _ _ h₁ h₂).mpr hequiv) k)⟩

/-- The smallest exponent admitting a counterexample is k = 3.
    Rephrased using `IsCounterexample`. -/
theorem min_counterexample_exp_CE :
    (∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), IsCounterexample n 3 A) ∧
    (∀ (n k : ℕ), k ≤ 2 → ∀ (A : Matrix (Fin n) (Fin n) ℝ), ¬ IsCounterexample n k A) := by
  refine ⟨⟨4, _, A_example_isCounterexample⟩, fun n k hk A ⟨P₁, P₂, h₁, h₂, _, hA, htr⟩ =>
    htr (hA ▸ min_counterexample_exp.2 n P₁ P₂ h₁ h₂ k hk)⟩

end counterexample_CE

#print axioms min_counterexample_dim_CE
-- 'MO509493.min_counterexample_dim_CE' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms min_counterexample_exp_CE
-- 'MO509493.min_counterexample_exp_CE' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms A_example_isCounterexample
-- 'MO509493.A_example_isCounterexample' depends on axioms: [propext, Classical.choice, Quot.sound]

end MO509493
