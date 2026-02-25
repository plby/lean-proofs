import Mathlib

set_option linter.dupNamespace false
set_option linter.mathlibStandardSet false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option linter.unusedRCasesPattern false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
Redefining Tensor, unfolding, mlrank, and mode_product with cleaner index handling.
-/
open Matrix BigOperators Fintype

section TensorDefs

variable {d : ℕ}
variable (I : Fin d → ℕ)

def Tensor := (∀ k, Fin (I k)) → ℝ

def combine_indices (t : Fin d) (i : Fin (I t)) (j : ∀ k : {k // k ≠ t}, Fin (I k)) : ∀ k, Fin (I k) :=
  fun k =>
    if h : k = t then
      cast (by rw [h]) i
    else
      j ⟨k, h⟩

def unfolding (t : Fin d) (T : Tensor I) : Matrix (Fin (I t)) (∀ k : {k // k ≠ t}, Fin (I k)) ℝ :=
  fun i j => T (combine_indices I t i j)

noncomputable def mlrank (T : Tensor I) : Fin d → ℕ :=
  fun t => (unfolding I t T).rank

variable {r : Fin d → ℕ}

def mode_product_shape (t : Fin d) (I_t : ℕ) (r : Fin d → ℕ) : Fin d → ℕ :=
  fun k => if k = t then I_t else r k

def mode_product_index_G (t : Fin d) (p : Fin (r t)) (idx : ∀ k, Fin (mode_product_shape t (I t) r k)) : ∀ k, Fin (r k) :=
  fun k =>
    if h : k = t then
      cast (by rw [h]) p
    else
      let val := idx k
      cast (by
        have : mode_product_shape t (I t) r k = r k := by
          simp [mode_product_shape, h]
        rw [this]) val

def mode_product (G : Tensor r) (t : Fin d) (U : Matrix (Fin (I t)) (Fin (r t)) ℝ) :
    Tensor (mode_product_shape t (I t) r) :=
  fun idx =>
    ∑ p : Fin (r t),
      G (mode_product_index_G I t p idx) * U (cast (by simp [mode_product_shape]) (idx t)) p

end TensorDefs

/-
Definition of Tucker reconstruction and Tucker rank bound.
-/
section Tucker

variable {d : ℕ}
variable {I : Fin d → ℕ}
variable {r : Fin d → ℕ}

def tucker_reconstruction (G : Tensor r) (U : ∀ t, Matrix (Fin (I t)) (Fin (r t)) ℝ) : Tensor I :=
  fun idx =>
    ∑ p : ∀ k, Fin (r k), G p * ∏ k, U k (idx k) (p k)

def has_tucker_rank_at_most (T : Tensor I) (r : Fin d → ℕ) : Prop :=
  ∃ (G : Tensor r) (U : ∀ t, Matrix (Fin (I t)) (Fin (r t)) ℝ), T = tucker_reconstruction G U

lemma tucker_reconstruction_apply (G : Tensor r) (U : ∀ t, Matrix (Fin (I t)) (Fin (r t)) ℝ) (idx : ∀ k, Fin (I k)) :
    tucker_reconstruction G U idx = ∑ p : ∀ k, Fin (r k), G p * ∏ k, U k (idx k) (p k) := rfl

end Tucker

/-
Definition of iota mapping (alpha, i) to a linear index.
-/
open Matrix BigOperators Fintype

section BlockTensors

variable {n : ℕ}

def iota (α : Fin n) (i : Fin 3) : Fin (3 * n) :=
  ⟨3 * α.val + i.val, by
    grind⟩

end BlockTensors

/-
Definition of inv_iota_alpha, mapping a linear index to the block index alpha.
-/
open Matrix BigOperators Fintype

section BlockTensors

variable {n : ℕ}

def inv_iota_alpha (x : Fin (3 * n)) : Fin n :=
  ⟨x.val / 3, by
    exact Nat.div_lt_of_lt_mul <| by linarith [ Fin.is_lt x ] ;⟩

end BlockTensors

/-
Definition of inv_iota_i, mapping a linear index to the inner index i.
-/
open Matrix BigOperators Fintype

section BlockTensors

variable {n : ℕ}

def inv_iota_i (x : Fin (3 * n)) : Fin 3 :=
  ⟨x.val % 3, Nat.mod_lt _ (by norm_num)⟩

end BlockTensors

/-
Definition of Asm, assembling block tensors into a larger tensor.
-/
open Matrix BigOperators Fintype

section BlockTensors

variable {n : ℕ}

def Asm (T : Fin n → Fin n → Fin n → Fin n → Tensor (fun _ : Fin 4 => 3)) :
    Tensor (fun _ : Fin 4 => 3 * n) :=
  fun idx =>
    let α := fun k => inv_iota_alpha (idx k)
    let i := fun k => inv_iota_i (idx k)
    T (α 0) (α 1) (α 2) (α 3) i

end BlockTensors

/-
Definition of block scaling (corrected variable name).
-/
open Matrix BigOperators Fintype

section BlockTensors

variable {n : ℕ}

def block_scaling (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (T : Fin n → Fin n → Fin n → Fin n → Tensor (fun _ : Fin 4 => 3)) :
    Fin n → Fin n → Fin n → Fin n → Tensor (fun _ : Fin 4 => 3) :=
  fun α β γ δ =>
    fun idx => lam α β γ δ * T α β γ δ idx

end BlockTensors

/-
Definition of the Levi-Civita tensor.
-/
open Matrix BigOperators Fintype

section BlockTensors

variable {n : ℕ}

def LeviCivita : Tensor (fun _ : Fin 4 => 4) :=
  fun idx =>
    let M : Matrix (Fin 4) (Fin 4) ℝ := fun i j => if idx i = j then 1 else 0
    M.det

end BlockTensors

/-
Definition of Q_block, the determinantal blocks.
-/
open Matrix BigOperators Fintype

section BlockTensors

variable {n : ℕ}

def Q_block (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (α β γ δ : Fin n) : Tensor (fun _ : Fin 4 => 3) :=
  fun idx =>
    let M : Matrix (Fin 4) (Fin 4) ℝ := fun r c =>
      match r with
      | 0 => A α (idx 0) c
      | 1 => A β (idx 1) c
      | 2 => A γ (idx 2) c
      | 3 => A δ (idx 3) c
    M.det

end BlockTensors

/-
Definition of StackedMatrix.
-/
open Matrix BigOperators Fintype

section BlockTensors

variable {n : ℕ}

def StackedMatrix (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ) : Matrix (Fin (3 * n)) (Fin 4) ℝ :=
  fun r c =>
    let α := inv_iota_alpha r
    let i := inv_iota_i r
    A α i c

end BlockTensors

/-
Definitions of N(n), MinorIndices, F_n, and mathbf_F_n with Lex wrapper for columns.
-/
open Matrix BigOperators Fintype

section Fn

variable {n : ℕ}

def I_3n (n : ℕ) : Fin 4 → ℕ := fun _ => 3 * n

def N (n : ℕ) : ℕ := 4 * (Nat.choose (3 * n) 5) * (Nat.choose ((3 * n) ^ 3) 5)

structure MinorIndices (n : ℕ) where
  t : Fin 4
  rows : Finset (Fin (3 * n))
  cols : Finset (Lex ({k // k ≠ t} → Fin (3 * n)))
  h_rows : rows.card = 5
  h_cols : cols.card = 5

noncomputable def F_n (T : Tensor (I_3n n)) (idx : MinorIndices n) : ℝ :=
  let U := unfolding (I_3n n) idx.t T
  let row_map := idx.rows.orderEmbOfFin idx.h_rows
  let col_map := idx.cols.orderEmbOfFin idx.h_cols
  let sub := Matrix.submatrix U row_map col_map
  sub.det

def BlockTensorFamily (n : ℕ) := Fin n → Fin n → Fin n → Fin n → Tensor (fun _ : Fin 4 => 3)

noncomputable def mathbf_F_n (T_fam : BlockTensorFamily n) (idx : MinorIndices n) : ℝ :=
  F_n (Asm T_fam) idx

end Fn

/-
Definitions of cofactor_vector, P_matrix, and Generic condition (corrected).
-/
open Matrix BigOperators Fintype

section Aux

variable {n : ℕ}

def cofactor_vector (r s t : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i =>
    let subM : Matrix (Fin 3) (Fin 3) ℝ := fun a b =>
      let col := (finSuccAboveEquiv i).toEmbedding b
      match a with
      | 0 => r col
      | 1 => s col
      | 2 => t col
    (-1 : ℝ)^(i : ℕ) * subM.det

def P_matrix (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ) (β γ δ : Fin n) :
    Matrix (Fin 4) (Fin 3 × Fin 3 × Fin 3) ℝ :=
  fun i idx =>
    let (j, k, l) := idx
    let r := A β j
    let s := A γ k
    let t := A δ l
    cofactor_vector r s t i

def Generic (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ) : Prop :=
  (StackedMatrix A).rank = 4 ∧
  ∀ β γ δ : Fin n, ¬(β = γ ∧ γ = δ) → (P_matrix A β γ δ).rank = 4

end Aux

/-
Definitions of not_all_identical and separable_scaling.
-/
open Matrix BigOperators Fintype

section MainDefs

variable {n : ℕ}

def not_all_identical (α β γ δ : Fin n) : Prop :=
  ¬(α = β ∧ β = γ ∧ γ = δ)

def separable_scaling (lam : Fin n → Fin n → Fin n → Fin n → ℝ) : Prop :=
  ∃ (u v w x : Fin n → ℝ),
    (∀ i, u i ≠ 0) ∧ (∀ i, v i ≠ 0) ∧ (∀ i, w i ≠ 0) ∧ (∀ i, x i ≠ 0) ∧
    ∀ α β γ δ, not_all_identical α β γ δ →
      lam α β γ δ = u α * v β * w γ * x δ

end MainDefs

/-
Lemma: If the multilinear rank is at most (4,4,4,4), then all 5x5 minors vanish.
-/
open Matrix BigOperators Fintype

section RankLemmas

variable {n : ℕ}

def rank_le_four (T : Tensor (I_3n n)) : Prop :=
  ∀ t : Fin 4, (unfolding (I_3n n) t T).rank ≤ 4

theorem rank_le_four_implies_F_n_zero (T : Tensor (I_3n n)) (h : rank_le_four T) :
    ∀ idx : MinorIndices n, F_n T idx = 0 := by
  intro idx
  unfold F_n
  let U := unfolding (I_3n n) idx.t T
  have h_rank : U.rank ≤ 4 := h idx.t
  -- The minor of a matrix with rank <= 4 is 0 if size > 4.
  -- idx.rows and idx.cols have card 5.
  -- Since the rank of U is at most 4, any 5x5 submatrix of U must have a determinant of zero.
  have h_submatrix_zero : ∀ (sub : Matrix (Fin 5) (Fin 5) ℝ), Matrix.rank sub ≤ 4 → sub.det = 0 := by
    intro sub h_sub_rank
    by_contra h_det_nonzero;
    have := Matrix.rank_mul_le_left sub ( sub⁻¹ ) ; simp_all +decide [ isUnit_iff_ne_zero ] ;
    grind;
  apply h_submatrix_zero;
  refine' le_trans _ h_rank;
  -- The rank of a submatrix is less than or equal to the rank of the original matrix.
  have h_submatrix_rank : ∀ (A : Matrix (Fin (I_3n n idx.t)) ((k : {k : Fin 4 // k ≠ idx.t}) → Fin (I_3n n k)) ℝ) (row_map : Fin 5 → Fin (I_3n n idx.t)) (col_map : Fin 5 → (k : {k : Fin 4 // k ≠ idx.t}) → Fin (I_3n n k)), Matrix.rank (Matrix.submatrix A row_map col_map) ≤ Matrix.rank A := by
    intros A row_map col_map
    set B : Matrix (Fin 5) (Fin (I_3n n idx.t)) ℝ := fun i j => if j = row_map i then 1 else 0
    set C : Matrix ((k : {k : Fin 4 // k ≠ idx.t}) → Fin (I_3n n k)) (Fin 5) ℝ := fun j i => if j = col_map i then 1 else 0
    have h_submatrix : A.submatrix row_map col_map = B * A * C := by
      ext i j; simp +decide [ Matrix.mul_apply, B, C ] ;
    rw [ h_submatrix ];
    refine' le_trans ( Matrix.rank_mul_le_left _ _ ) _;
    exact Matrix.rank_mul_le_right _ _;
  convert h_submatrix_rank U _ _

end RankLemmas

/-
Lemma: The Levi-Civita tensor has multilinear rank at most (4,4,4,4).
-/
open Matrix BigOperators Fintype

section RankLemmas

variable {n : ℕ}

lemma LeviCivita_rank_le_four :
    ∀ t : Fin 4, (unfolding (fun _ => 4) t LeviCivita).rank ≤ 4 := by
  intro t
  apply le_trans (Matrix.rank_le_card_height _)
  simp

end RankLemmas

/-
Proof that Asm Q has multilinear rank at most 4 by factoring the unfolding.
-/
open Matrix BigOperators Fintype

section RankProof

variable {n : ℕ}

def cofactor_matrix_t (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ) (t : Fin 4) :
    Matrix (Fin 4) ({k // k ≠ t} → Fin (3 * n)) ℝ :=
  fun k idx =>
    let others : Fin 3 → Fin 4 → ℝ := fun i =>
      StackedMatrix A (idx ((finSuccAboveEquiv t) i))
    ((-1 : ℝ) ^ (t : ℕ)) * cofactor_vector (others 0) (others 1) (others 2) k

lemma unfolding_Q_eq_mul (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ) (t : Fin 4) :
    unfolding (I_3n n) t (Asm (fun α β γ δ => Q_block A α β γ δ)) =
    StackedMatrix A * cofactor_matrix_t A t := by
  ext i j
  simp [Matrix.mul_apply, unfolding, Asm, Q_block, StackedMatrix, cofactor_matrix_t, cofactor_vector]
  -- We need to show that the dot product matches the determinant.
  -- LHS is Q_block ... which is det(rows).
  -- RHS is sum_k A_{i,k} * (-1)^t * cof(others)_k.
  -- This is (-1)^t * (A_i . cof(others)).
  -- A_i . cof(others) = det(A_i, others).
  -- (-1)^t * det(A_i, others) = det(others_before, A_i, others_after).
  -- We need to verify the order of rows in Q_block matches (others_before, A_i, others_after).
  -- Q_block uses indices (idx 0, idx 1, idx 2, idx 3).
  -- unfolding at t uses i for idx t, and j for others.
  -- So the rows are A(idx 0), A(idx 1), A(idx 2), A(idx 3).
  -- i is A(idx t).
  -- others are A(idx k) for k != t, in order.
  -- So indeed, we are moving A(idx t) to the front, which gives (-1)^t sign.
  convert Matrix.det_succ_row _ t using 1;
  fin_cases t <;> simp +decide [ Matrix.submatrix ];
  · unfold combine_indices; simp +decide [ Finset.prod ] ; ring_nf!;
    congr! 2;
  · rw [ ← Finset.sum_neg_distrib ] ; congr ; ext x ; ring!;
  · simp +decide [ Fin.sum_univ_succ, Matrix.det_fin_three ];
    ring!;
  · rw [ ← Finset.sum_neg_distrib ] ; congr ; ext x ; ring!

lemma rank_Q_le_four (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ) :
    rank_le_four (Asm (fun α β γ δ => Q_block A α β γ δ)) := by
  intro t
  rw [unfolding_Q_eq_mul]
  apply le_trans (Matrix.rank_mul_le_left _ _)
  -- rank(StackedMatrix A) <= 4
  apply le_trans (Matrix.rank_le_card_width (StackedMatrix A))
  simp

end RankProof

/-
Definition of mode_product_square with explicit cast proof.
-/
open Matrix BigOperators Fintype

section ModeProductSquare

variable {n : ℕ}

lemma mode_product_shape_eq_I_3n (t : Fin 4) :
    mode_product_shape t (I_3n n t) (I_3n n) = I_3n n := by
      exact funext fun x => by unfold mode_product_shape I_3n; aesop;

def mode_product_square (T : Tensor (I_3n n)) (t : Fin 4) (M : Matrix (Fin (3 * n)) (Fin (3 * n)) ℝ) : Tensor (I_3n n) :=
  cast (congrArg Tensor (mode_product_shape_eq_I_3n t)) (mode_product (I_3n n) T t M)

end ModeProductSquare

/-
Extensionality lemma for Tensor.
-/
open Matrix BigOperators Fintype

section TensorExt

variable {d : ℕ}
variable {I : Fin d → ℕ}

@[ext]
lemma Tensor.ext {T1 T2 : Tensor I} (h : ∀ idx, T1 idx = T2 idx) : T1 = T2 := by
  funext idx
  exact h idx

end TensorExt

/-
Definition of scaling_matrix.
-/
open Matrix BigOperators Fintype

section ScalingMatrix

variable {n : ℕ}

def scaling_matrix (u : Fin n → ℝ) : Matrix (Fin (3 * n)) (Fin (3 * n)) ℝ :=
  Matrix.diagonal (fun i => u (inv_iota_alpha i))

end ScalingMatrix

/-
Lemma: Casting a tensor and applying it is equivalent to applying the tensor to the casted index.
-/
open Matrix BigOperators Fintype

section CastLemma

variable {d : ℕ}

lemma cast_tensor_apply {I J : Fin d → ℕ} (h : I = J) (T : Tensor I) (idx : ∀ k, Fin (J k)) :
    cast (congrArg Tensor h) T idx = T (cast (congrArg (fun K => ∀ k, Fin (K k)) h.symm) idx) := by
  subst h
  simp

end CastLemma

/-
Helper lemma: Mode product with a diagonal matrix simplifies to a single term. Explicit casts included.
-/
open Matrix BigOperators Fintype

section ScalingHelper

variable {n : ℕ}

lemma mode_product_diagonal_simp (T : Tensor (I_3n n)) (t : Fin 4) (u : Fin n → ℝ)
    (idx : ∀ k, Fin (mode_product_shape t (I_3n n t) (I_3n n) k)) :
    mode_product (I_3n n) T t (scaling_matrix u) idx =
    T (mode_product_index_G (I_3n n) t (cast (by simp [mode_product_shape, I_3n]) (idx t)) idx) *
    u (inv_iota_alpha (cast (by simp [mode_product_shape, I_3n]) (idx t))) := by
      unfold mode_product;
      unfold scaling_matrix;
      rw [ Finset.sum_eq_single ( cast ( by simp [ mode_product_shape ] ) ( idx t ) ) ] <;> simp +decide [ Matrix.diagonal ];
      tauto

end ScalingHelper

/-
The column space of the specified submatrix of the unfolding of Q is the image of the column space of P under the linear map defined by C.
-/
section GroupSpan

variable {n : ℕ}

def unfolding_column_submatrix (T : Tensor (I_3n n)) (β γ δ : Fin n) :
    Matrix (Fin (3 * n)) (Fin 3 × Fin 3 × Fin 3) ℝ :=
  fun r idx =>
    let col_idx : {k : Fin 4 // k ≠ 0} → Fin (3 * n) := fun k =>
      if h1 : k.val = 1 then iota β idx.1
      else if h2 : k.val = 2 then iota γ idx.2.1
      else iota δ idx.2.2
    unfolding (I_3n n) 0 T r col_idx

lemma group_span (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ) (β γ δ : Fin n)
    (hC : (StackedMatrix A).rank = 4) :
    Submodule.span ℝ (Set.range (unfolding_column_submatrix (Asm (fun α β γ δ => Q_block A α β γ δ)) β γ δ)ᵀ) =
    Submodule.map (Matrix.mulVecLin (StackedMatrix A))
      (Submodule.span ℝ (Set.range (P_matrix A β γ δ)ᵀ)) := by
        -- By definition of unfolding and mode product, we can show that the two subspaces are equal.
        have h_eq : Submodule.span ℝ (Set.range (unfolding_column_submatrix (Asm (fun α β γ δ => Q_block A α β γ δ)) β γ δ)ᵀ) = Submodule.span ℝ (Set.range (Matrix.transpose (StackedMatrix A * P_matrix A β γ δ)) : Set (Fin (3 * n) → ℝ)) := by
          congr! 3;
          convert unfolding_Q_eq_mul A 0 using 1;
          constructor <;> intro h;
          · exact unfolding_Q_eq_mul A 0;
          · ext i j; simp [unfolding_column_submatrix, P_matrix];
            convert congr_fun ( congr_fun h i ) _ using 1;
            unfold cofactor_matrix_t; simp +decide [ Matrix.mul_apply ] ;
            unfold StackedMatrix; simp +decide [ iota ] ;
            unfold inv_iota_alpha inv_iota_i; simp +decide [ Nat.add_div ] ;
            fin_cases j <;> rfl;
        rw [ h_eq ];
        refine' le_antisymm _ _;
        · rw [ Submodule.span_le, Set.range_subset_iff ];
          intro y;
          refine' Submodule.mem_map.mpr ⟨ _, Submodule.subset_span <| Set.mem_range_self _, _ ⟩;
          exact y;
          ext; simp +decide [ Matrix.mulVec, dotProduct ] ;
          rw [ Matrix.mul_apply ];
        · rw [ Submodule.map_le_iff_le_comap ];
          rw [ Submodule.span_le ];
          rintro _ ⟨ i, rfl ⟩;
          exact Submodule.subset_span ⟨ i, rfl ⟩

end GroupSpan

/-
Definition of the example matrices A used to prove generic rank.
-/
section ExampleDef

variable {n : ℕ}

def example_A (β γ δ : Fin n) : Fin n → Matrix (Fin 3) (Fin 4) ℝ :=
  fun α =>
    if β ≠ γ ∧ γ ≠ δ ∧ β ≠ δ then
      if α = β then !![1,0,0,0; 0,1,0,0; 0,0,0,1]
      else if α = γ then !![1,0,0,0; 0,1,0,0; 0,0,1,0]
      else if α = δ then !![0,0,1,0; 0,0,0,1; 1,0,0,0]
      else 0
    else
      let (u, v) :=
        if β = γ then (β, δ)
        else if β = δ then (β, γ)
        else (γ, β)
      if α = u then !![1,0,0,0; 0,1,0,0; 0,0,1,0]
      else if α = v then !![0,1,0,0; 0,0,1,0; 0,0,0,1]
      else 0

end ExampleDef

/-
The rank of the triple-cofactor matrix P for the example choice of A is 4.
-/
section ExampleRank

variable {n : ℕ}

def not_constant_triple (β γ δ : Fin n) : Prop := ¬(β = γ ∧ γ = δ)

lemma example_P_rank_eq_four (β γ δ : Fin n) (h : not_constant_triple β γ δ) :
    (P_matrix (example_A β γ δ) β γ δ).rank = 4 := by
      revert h;
      -- By definition of `example_A`, we know that the column space of `P` contains the standard basis vectors `e_1, e_2, e_3, e_4`.
      have h_basis : ∀ (β γ δ : Fin n), ¬(β = γ ∧ γ = δ) → Submodule.span ℝ (Set.range (P_matrix (example_A β γ δ) β γ δ)ᵀ) = ⊤ := by
        intros β γ δ h_not_const
        have h_basis : ∀ (i : Fin 4), ∃ (j k l : Fin 3), cofactor_vector (example_A β γ δ β j) (example_A β γ δ γ k) (example_A β γ δ δ l) = fun x => if x = i then 1 else 0 := by
          by_cases h : β = γ ∧ γ = δ <;> simp_all +decide [ example_A ];
          by_cases hβγ : β = γ <;> by_cases hγδ : γ = δ <;> by_cases hβδ : β = δ <;> simp +decide [ hβγ, hγδ, hβδ ] at h ⊢;
          · aesop;
          · split_ifs <;> simp_all +decide [ funext_iff, Fin.forall_fin_succ ];
            unfold cofactor_vector; simp +decide [ Matrix.det_fin_three ] ;
            simp +decide [ finSuccAboveEquiv ] at *;
            simp +decide [ Fin.exists_fin_succ, Fin.forall_fin_succ, Fin.succAbove ] at *;
          · intro i; fin_cases i <;> simp +decide [ funext_iff, Fin.forall_fin_succ ] ;
            · unfold cofactor_vector; simp +decide [ Matrix.det_fin_three ] ;
              simp +decide [ Fin.exists_fin_succ, finSuccAboveEquiv ] at *;
            · unfold cofactor_vector; simp +decide [ Matrix.det_fin_three ] ;
              simp +decide [ Fin.exists_fin_succ, Fin.forall_fin_succ, finSuccAboveEquiv ] at *;
              simp +decide [ Fin.succAbove ] at *;
            · unfold cofactor_vector; simp +decide [ Matrix.det_fin_three ] ;
              simp +decide [ Fin.exists_fin_succ, finSuccAboveEquiv ] at *;
              simp +decide [ Fin.succAbove ] at *;
            · unfold cofactor_vector; simp +decide [ Matrix.det_fin_three ] ;
              simp +decide [ Fin.exists_fin_succ, finSuccAboveEquiv ] at *;
              simp +decide [ Fin.succAbove ] at *;
          · simp_all +decide [ Fin.forall_fin_succ ];
            simp +decide [ funext_iff, Fin.forall_fin_succ, cofactor_vector ];
            simp +decide [ Matrix.det_fin_three ];
            simp +decide [ finSuccAboveEquiv ] at *;
            simp +decide [ Fin.exists_fin_succ, Fin.forall_fin_succ, Fin.succAbove ] at *;
          · simp +decide [ Fin.forall_fin_succ, funext_iff, hβγ, hγδ, hβδ ];
            split_ifs <;> simp_all +decide [ Matrix.det_fin_three ];
            unfold cofactor_vector; simp +decide [ Matrix.det_fin_three ] ;
            simp +decide [ finSuccAboveEquiv ] at *;
            simp +decide [ Fin.exists_fin_succ, Fin.forall_fin_succ, Fin.succAbove ] at *;
        refine' eq_top_iff.mpr fun x hx => _;
        choose j k l h using h_basis;
        -- By definition of $P$, we know that each column of $P$ is a linear combination of the standard basis vectors.
        have h_comb : ∀ i : Fin 4, (fun x => if x = i then 1 else 0) ∈ Submodule.span ℝ (Set.range (P_matrix (example_A β γ δ) β γ δ)ᵀ) := by
          intro i; specialize h i; rw [ ← h ] ; exact Submodule.subset_span ⟨ ( j i, k i, l i ), rfl ⟩ ;
        convert Submodule.sum_mem _ fun i ( hi : i ∈ Finset.univ ) => Submodule.smul_mem _ ( x i ) ( h_comb i ) using 1 ; ext i ; simp +decide [ Finset.sum_ite_eq' ];
      intro h;
      rw [ Matrix.rank ];
      rw [ show LinearMap.range ( P_matrix ( example_A β γ δ ) β γ δ |> Matrix.mulVecLin ) = ⊤ from ?_ ];
      · norm_num;
      · convert h_basis β γ δ h using 1;
        ext; simp [Matrix.mulVecLin];
        simp +decide [ Submodule.mem_span_range_iff_exists_fun, Matrix.mulVec, dotProduct ];
        simp +decide [ funext_iff, Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_comm ]

end ExampleRank

/-
Definition of Zariski generic property for properties of the matrix tuple A.
-/
section ZariskiDefs

variable {n : ℕ}

def Vars (n : ℕ) := Fin n × Fin 3 × Fin 4

def to_vec (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ) : Vars n → ℝ :=
  fun (α, i, j) => A α i j

def ZariskiGeneric (P : (Fin n → Matrix (Fin 3) (Fin 4) ℝ) → Prop) : Prop :=
  ∃ p : MvPolynomial (Vars n) ℝ, p ≠ 0 ∧ ∀ A, MvPolynomial.eval (to_vec A) p ≠ 0 → P A

end ZariskiDefs

/-
Lemmas calculating the cofactor vector of standard basis vectors.
-/
section CofactorLemmas

variable {n : ℕ}

def e (i : Fin 4) : Fin 4 → ℝ := fun j => if j = i then 1 else 0

lemma cofactor_e2_e3_e4 : cofactor_vector (e 1) (e 2) (e 3) = e 0 := by
  unfold cofactor_vector;
  simp +decide [ funext_iff, Matrix.det_fin_three ];
  simp +decide [ Fin.forall_fin_succ, e ]
lemma cofactor_e1_e3_e4 : cofactor_vector (e 0) (e 2) (e 3) = -e 1 := by
  unfold cofactor_vector e; ext i; fin_cases i <;> norm_num [ Matrix.det_fin_three ] ;
  · simp +decide [ finSuccAboveEquiv ];
  · simp +decide [ finSuccAboveEquiv ];
  · simp +decide [ finSuccAboveEquiv ];
  · simp +decide [ finSuccAboveEquiv ]
lemma cofactor_e1_e2_e4 : cofactor_vector (e 0) (e 1) (e 3) = e 2 := by
  ext i;
  fin_cases i <;> unfold cofactor_vector <;> norm_num [ Matrix.det_fin_three ];
  · simp +decide [ Fin.ext_iff, e ];
  · simp +decide [ e ];
  · simp +decide [ e ];
  · simp +decide [ Fin.ext_iff, e ]
lemma cofactor_e1_e2_e3 : cofactor_vector (e 0) (e 1) (e 2) = -e 3 := by
  unfold cofactor_vector;
  simp +decide [ funext_iff, Matrix.det_fin_three ];
  simp +decide [ Fin.forall_fin_succ, e ]

end CofactorLemmas

/-
Helper lemmas for cofactor calculations of standard basis vectors.
-/
section CofactorHelper

variable {n : ℕ}

def vec_e (i : Fin 4) : Fin 4 → ℝ := fun j => if j = i then 1 else 0

lemma vec_e_cofactor_1 : cofactor_vector (vec_e 1) (vec_e 2) (vec_e 3) = vec_e 0 := by
  convert cofactor_e2_e3_e4 using 1

lemma vec_e_cofactor_2 : cofactor_vector (vec_e 0) (vec_e 2) (vec_e 3) = -vec_e 1 := by
  unfold vec_e cofactor_vector; norm_num [ Matrix.det_fin_three ] ;
  ext i; fin_cases i <;> simp +decide [ finSuccAboveEquiv ] ;

lemma vec_e_cofactor_3 : cofactor_vector (vec_e 0) (vec_e 1) (vec_e 3) = vec_e 2 := by
  convert cofactor_e1_e2_e4 using 1

lemma vec_e_cofactor_4 : cofactor_vector (vec_e 0) (vec_e 1) (vec_e 2) = -vec_e 3 := by
  -- Apply the lemma that states the cofactor vector of the standard basis vectors.
  apply cofactor_e1_e2_e3

end CofactorHelper

/-
The rank of the triple-cofactor matrix P for the example choice of A is 4.
-/
section ExampleRankProofFinalV2

variable {n : ℕ}

lemma example_P_rank_eq_four_final (β γ δ : Fin n) (h : not_constant_triple β γ δ) :
    (P_matrix (example_A β γ δ) β γ δ).rank = 4 := by
      exact example_P_rank_eq_four β γ δ h

end ExampleRankProofFinalV2

/-
The rank of the triple-cofactor matrix P for the example choice of A is 4.
-/
section ExampleRankProofFinalV3

variable {n : ℕ}

lemma example_P_rank_eq_four_final_v3 (β γ δ : Fin n) (h : not_constant_triple β γ δ) :
    (P_matrix (example_A β γ δ) β γ δ).rank = 4 := by
      exact example_P_rank_eq_four β γ δ h

end ExampleRankProofFinalV3

/-
The rank of the triple-cofactor matrix P for the example choice of A is 4.
-/
section ExampleRankProofFixed

variable {n : ℕ}

lemma example_P_rank_eq_four_fixed (β γ δ : Fin n) (h : not_constant_triple β γ δ) :
    (P_matrix (example_A β γ δ) β γ δ).rank = 4 := by
      convert example_P_rank_eq_four_final_v3 β γ δ h using 1

end ExampleRankProofFixed

/-
The rank of the triple-cofactor matrix P for the example choice of A is 4.
-/
section ExampleRankProofFinalV4

variable {n : ℕ}

lemma example_P_rank_eq_four_final_v4 (β γ δ : Fin n) (h : not_constant_triple β γ δ) :
    (P_matrix (example_A β γ δ) β γ δ).rank = 4 := by
      convert example_P_rank_eq_four_fixed β γ δ h using 1

end ExampleRankProofFinalV4

/-
Polynomial definitions for A and P, and their evaluation property.
-/
section Polynomials

variable {n : ℕ}

open MvPolynomial

def cofactor_vector_generic {R : Type*} [CommRing R] (r s t : Fin 4 → R) : Fin 4 → R :=
  fun i =>
    let subM : Matrix (Fin 3) (Fin 3) R := fun a b =>
      let col := (finSuccAboveEquiv i).toEmbedding b
      match a with
      | 0 => r col
      | 1 => s col
      | 2 => t col
    (-1 : R)^(i : ℕ) * subM.det

def A_poly (n : ℕ) : Fin n → Matrix (Fin 3) (Fin 4) (MvPolynomial (Vars n) ℝ) :=
  fun α i j => X (α, i, j)

def P_matrix_poly (β γ δ : Fin n) : Matrix (Fin 4) (Fin 3 × Fin 3 × Fin 3) (MvPolynomial (Vars n) ℝ) :=
  fun i idx =>
    let (j, k, l) := idx
    let r := A_poly n β j
    let s := A_poly n γ k
    let t := A_poly n δ l
    cofactor_vector_generic r s t i

lemma eval_P_matrix_poly (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ) (β γ δ : Fin n) :
    (P_matrix_poly β γ δ).map (eval (to_vec A)) = P_matrix A β γ δ := by
      -- By definition of `P_matrix`, we know that its entries are the evaluations of the cofactor vector polynomials.
      ext i j; simp [P_matrix, P_matrix_poly];
      unfold cofactor_vector_generic cofactor_vector; simp +decide [ Matrix.det_fin_three ] ;
      unfold A_poly; simp +decide [ to_vec ] ;

end Polynomials

/-
Definition of the witness polynomial and its evaluation property.
-/
section WitnessPoly

variable {n : ℕ}

open MvPolynomial

noncomputable def witness_poly (β γ δ : Fin n) : MvPolynomial (Vars n) ℝ :=
  let P := P_matrix_poly β γ δ
  let cols := @Finset.univ (Fin 4 → Fin 3 × Fin 3 × Fin 3) _
  ∑ c ∈ cols, (Matrix.det (P.submatrix id c))^2

lemma witness_poly_eval (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ) (β γ δ : Fin n) :
    eval (to_vec A) (witness_poly β γ δ) =
    let P := P_matrix A β γ δ
    let cols := @Finset.univ (Fin 4 → Fin 3 × Fin 3 × Fin 3) _
    ∑ c ∈ cols, (Matrix.det (P.submatrix id c))^2 := by
      have h_eval_P : (P_matrix_poly β γ δ).map (eval (to_vec A)) = P_matrix A β γ δ := by
        exact eval_P_matrix_poly A β γ δ;
      convert congr_arg ( fun m : Matrix ( Fin 4 ) ( Fin 3 × Fin 3 × Fin 3 ) ℝ => ∑ c ∈ Finset.univ, ( m.submatrix id c ).det ^ 2 ) h_eval_P using 1;
      unfold witness_poly;
      simp +decide [ Matrix.det_apply' ]

end WitnessPoly

/-
If a 4xM matrix has rank 4, there exists a 4x4 submatrix with non-zero determinant.
-/
section RankHelper

variable {m : Type*} [Fintype m] [DecidableEq m]

lemma exists_det_ne_zero_of_rank_eq_four (A : Matrix (Fin 4) m ℝ) (h : A.rank = 4) :
    ∃ c : Fin 4 → m, (A.submatrix id c).det ≠ 0 := by
      -- Since the rank of A is 4, the columns of A span ℝ^4. Therefore, there must be 4 linearly independent columns.
      obtain ⟨c, hc⟩ : ∃ c : Fin 4 → m, LinearIndependent ℝ (fun i => A.mulVec (Pi.single (c i) 1)) := by
        have h_span : Submodule.span ℝ (Set.range (fun i : m => A.mulVec (Pi.single i 1))) = ⊤ := by
          refine' Submodule.eq_top_of_finrank_eq _;
          convert h using 1;
          · congr;
            · simp +decide [ funext_iff, Matrix.mulVec, Submodule.mem_span_range_iff_exists_fun ];
              simp +decide [ dotProduct, mul_comm ];
            · ext; simp [Matrix.mulVecLin];
              simp +decide [ Submodule.mem_span_range_iff_exists_fun, Matrix.mulVec, funext_iff ];
              simp +decide [ dotProduct, mul_comm ];
            · ext; simp [Matrix.mulVecLin];
              simp +decide [ Submodule.mem_span_range_iff_exists_fun, Matrix.mulVec, funext_iff ];
              simp +decide only [mul_comm, dotProduct];
          · norm_num;
        have := exists_linearIndependent ℝ ( Set.range fun i : m => A *ᵥ Pi.single i 1 );
        obtain ⟨ b, hb₁, hb₂, hb₃ ⟩ := this;
        have h_card : Set.ncard b = 4 := by
          have h_card : Module.finrank ℝ (Submodule.span ℝ b) = 4 := by
            rw [ hb₂, h_span, finrank_top ] ; aesop;
          have h_card : Set.ncard b = Module.finrank ℝ (Submodule.span ℝ b) := by
            have h_card : Set.ncard b = Module.finrank ℝ (Submodule.span ℝ (Set.range (fun x : b => x.val))) := by
              have h_card : Set.ncard b = Module.finrank ℝ (Submodule.span ℝ (Set.range (fun x : b => x.val))) := by
                have h_finite : Set.Finite b := by
                  exact Set.Finite.subset ( Set.toFinite ( Set.range fun i : m => A *ᵥ Pi.single i 1 ) ) hb₁
                have := h_finite.fintype;
                rw [ Set.ncard_eq_toFinset_card' ];
                rw [ finrank_span_eq_card ] ; aesop;
                grind;
              exact h_card;
            convert h_card using 1;
            rw [ show Submodule.span ℝ b = Submodule.span ℝ ( Set.range fun x : b => x.val ) from ?_ ];
            exact congr_arg _ ( by ext; aesop );
          grind;
        have h_card : ∃ c : Fin 4 → m, ∀ i, A.mulVec (Pi.single (c i) 1) ∈ b ∧ ∀ i j, i ≠ j → A.mulVec (Pi.single (c i) 1) ≠ A.mulVec (Pi.single (c j) 1) := by
          have h_card : ∃ c : Fin 4 → (Fin 4 → ℝ), (∀ i, c i ∈ b) ∧ (∀ i j, i ≠ j → c i ≠ c j) := by
            have h_card : ∃ c : Finset (Fin 4 → ℝ), c.card = 4 ∧ ∀ x ∈ c, x ∈ b := by
              obtain ⟨ c, hc ⟩ := Set.Finite.exists_finset_coe ( show Set.Finite b from Set.finite_of_ncard_pos ( by linarith ) ) ; use c; aesop;
            obtain ⟨ c, hc₁, hc₂ ⟩ := h_card;
            have h_card : Nonempty (Fin 4 ≃ c) := by
              exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ hc₁ ] ⟩;
            exact ⟨ fun i => h_card.some i |>.1, fun i => hc₂ _ ( h_card.some i |>.2 ), fun i j hij => fun h => hij ( h_card.some.injective <| Subtype.ext h ) ⟩;
          obtain ⟨ c, hc₁, hc₂ ⟩ := h_card;
          choose f hf using fun i => hb₁ ( hc₁ i );
          exact ⟨ f, fun i => ⟨ by simpa [ hf ] using hc₁ i, fun i j hij => by simpa [ hf ] using hc₂ i j hij ⟩ ⟩;
        obtain ⟨ c, hc ⟩ := h_card;
        use c;
        convert hb₃.comp _ _;
        rotate_left;
        use fun i => ⟨ A *ᵥ Pi.single ( c i ) 1, hc i |>.1 ⟩;
        · exact fun i j hij => Classical.not_not.1 fun hi => hc i |>.2 i j hi <| by simpa using congr_arg Subtype.val hij;
        · rfl;
      refine' ⟨ c, _ ⟩;
      rw [ Fintype.linearIndependent_iff ] at hc;
      contrapose! hc;
      obtain ⟨ g, hg ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hc;
      refine' ⟨ g, _, _ ⟩ <;> simp_all +decide [ funext_iff, Matrix.mulVec, dotProduct ];
      simpa only [ mul_comm ] using hg.2

end RankHelper

/-
The witness polynomial is not the zero polynomial.
-/
section WitnessNonZeroFinal

variable {n : ℕ}

open MvPolynomial

lemma witness_poly_ne_zero (β γ δ : Fin n) (h : not_constant_triple β γ δ) :
    witness_poly β γ δ ≠ 0 := by
      -- By definition of `witness_poly`, if it were zero, then for `example_A`, the sum of squares of minors would be zero, implying all minors are zero.
      by_contra h_contra
      have h_all_minors_zero : ∀ c : Fin 4 → Fin 3 × Fin 3 × Fin 3, (Matrix.det (P_matrix (example_A β γ δ) β γ δ |>.submatrix id c)) = 0 := by
        have h_all_minors_zero : ∑ c ∈ Finset.univ, (Matrix.det (P_matrix (example_A β γ δ) β γ δ |>.submatrix id c))^2 = 0 := by
          have := witness_poly_eval ( example_A β γ δ ) β γ δ; aesop;
        rw [ Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _ ] at h_all_minors_zero ; aesop;
      -- By Lemma `exists_det_ne_zero_of_rank_eq_four`, there exists a $4 \times 4$ submatrix with non-zero determinant.
      obtain ⟨c, hc⟩ : ∃ c : Fin 4 → Fin 3 × Fin 3 × Fin 3, (Matrix.det (P_matrix (example_A β γ δ) β γ δ |>.submatrix id c)) ≠ 0 := by
        apply exists_det_ne_zero_of_rank_eq_four;
        exact example_P_rank_eq_four β γ δ h;
      exact hc <| h_all_minors_zero c

end WitnessNonZeroFinal

/-
If a 4xM matrix has rank 4, the sum of squares of its 4x4 minors is non-zero.
-/
section SumSqMinors

variable {m : Type*} [Fintype m] [DecidableEq m]

lemma sum_sq_minors_ne_zero (A : Matrix (Fin 4) m ℝ) (h : A.rank = 4) :
    ∑ c : Fin 4 → m, (A.submatrix id c).det ^ 2 ≠ 0 := by
      -- By `exists_det_ne_zero_of_rank_eq_four`, there exists a 4x4 submatrix with non-zero determinant.
      obtain ⟨c, hc⟩ : ∃ c : Fin 4 → m, (A.submatrix id c).det ≠ 0 := by
        exact exists_det_ne_zero_of_rank_eq_four A h;
      exact ne_of_gt ( lt_of_lt_of_le ( by positivity ) ( Finset.single_le_sum ( fun x _ => sq_nonneg ( Matrix.det ( A.submatrix id x ) ) ) ( Finset.mem_univ c ) ) )

end SumSqMinors

/-
The rank of the triple-cofactor matrix P is 4 Zariski-generically.
-/
section GenericRankProofFinal

variable {n : ℕ}

open MvPolynomial

lemma P_rank_generic (β γ δ : Fin n) (h : not_constant_triple β γ δ) :
    ZariskiGeneric (fun A => (P_matrix A β γ δ).rank = 4) := by
      refine' ⟨ witness_poly β γ δ, _, _ ⟩;
      · exact witness_poly_ne_zero β γ δ h;
      · unfold witness_poly at *;
        intro A hA;
        -- If the sum of squares of minors is non-zero, then at least one minor is non-zero.
        obtain ⟨c, hc⟩ : ∃ c : Fin 4 → Fin 3 × Fin 3 × Fin 3, (Matrix.det ((P_matrix A β γ δ).submatrix id c)) ≠ 0 := by
          contrapose! hA; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg ] ;
          convert hA using 1;
          rw [ ← eval_P_matrix_poly ];
          simp +decide [ Matrix.det_apply' ];
        -- Since $\det(M) \neq 0$, $\rank(M) = 4$.
        have h_rank_M : (Matrix.submatrix (P_matrix A β γ δ) id c).rank = 4 := by
          have := Matrix.rank_mul_le ( ( P_matrix A β γ δ |> Matrix.submatrix ) id c ) ( ( P_matrix A β γ δ |> Matrix.submatrix ) id c ) ⁻¹ ; simp_all +decide [ isUnit_iff_ne_zero ] ;
          exact le_antisymm ( le_trans ( Matrix.rank_le_card_width _ ) ( by norm_num ) ) this.1;
        refine' le_antisymm _ _;
        · exact le_trans ( Matrix.rank_le_card_height _ ) ( by norm_num );
        · have h_rank_P : (Matrix.submatrix (P_matrix A β γ δ) id c).rank ≤ (P_matrix A β γ δ).rank := by
            have h_submatrix : ∃ (f : Fin 4 → Fin 4) (g : Fin 4 → Fin 3 × Fin 3 × Fin 3), (Matrix.submatrix (P_matrix A β γ δ) id c) = (P_matrix A β γ δ).submatrix f g := by
              exact ⟨ id, c, rfl ⟩
            obtain ⟨ f, g, hfg ⟩ := h_submatrix;
            rw [ hfg ];
            have h_submatrix : ∃ (F : Matrix (Fin 4) (Fin 4) ℝ) (G : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 4) ℝ), (P_matrix A β γ δ).submatrix f g = F * (P_matrix A β γ δ) * G := by
              use Matrix.of (fun i j => if j = f i then 1 else 0), Matrix.of (fun i j => if i = g j then 1 else 0);
              ext i j; simp +decide [ Matrix.mul_apply ] ;
            obtain ⟨ F, G, hfg ⟩ := h_submatrix; rw [ hfg ] ; exact Matrix.rank_mul_le_left _ _ |> le_trans <| Matrix.rank_mul_le_right _ _;
          linarith

end GenericRankProofFinal

/-
The rank of the triple-cofactor matrix P is 4 Zariski-generically.
-/
section GenericRankProofFinalCorrect

variable {n : ℕ}

open MvPolynomial

lemma P_rank_generic_final (β γ δ : Fin n) (h : not_constant_triple β γ δ) :
    ZariskiGeneric (fun A => (P_matrix A β γ δ).rank = 4) := by
      convert P_rank_generic β γ δ h using 1

end GenericRankProofFinalCorrect

/-
The rank of the stacked matrix C is 4 Zariski-generically, provided n is at least 2.
-/
section CRankGeneric

variable {n : ℕ}

open MvPolynomial

lemma C_rank_generic (h_n : n ≥ 2) :
    ZariskiGeneric (fun (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ) => (StackedMatrix A).rank = 4) := by
  -- We need to show that the set of A where rank(C) = 4 is Zariski open and non-empty.
  -- The condition rank(C) < 4 is Zariski closed (defined by vanishing of 4x4 minors).
  -- So rank(C) >= 4 is Zariski open.
  -- Since C has 4 columns, rank(C) <= 4 always.
  -- So rank(C) = 4 is equivalent to rank(C) >= 4.
  -- We just need to show there exists an A with rank(C) = 4.
  -- Since n >= 2, C has at least 6 rows.
  -- We can choose A such that C contains I_4 as a submatrix.
  -- For example, let A 0 = [e_0, e_1, e_2] and A 1 = [e_3, 0, 0].
  -- Then C has rows e_0, e_1, e_2, e_3, ...
  -- These are linearly independent, so rank is 4.
  -- Let $C$ be the stacked matrix.
  set C : (Fin n → Matrix (Fin 3) (Fin 4) ℝ) → Matrix (Fin (3 * n)) (Fin 4) ℝ := fun A => StackedMatrix A;
  -- The set of matrices $A$ where $C$ has rank 4 is Zariski-open.
  have h_open : ∀ A : Fin n → Matrix (Fin 3) (Fin 4) ℝ, Matrix.rank (C A) = 4 → ∃ p : MvPolynomial (Vars n) ℝ, p ≠ 0 ∧ ∀ A' : Fin n → Matrix (Fin 3) (Fin 4) ℝ, MvPolynomial.eval (to_vec A') p ≠ 0 → Matrix.rank (C A') = 4 := by
    intro A hA
    obtain ⟨c, hc⟩ : ∃ c : Fin 4 → Fin (3 * n), Matrix.det (Matrix.submatrix (C A) c id) ≠ 0 := by
      have := exists_det_ne_zero_of_rank_eq_four ( Matrix.transpose ( C A ) ) ?_;
      · obtain ⟨ c, hc ⟩ := this; use c; simp_all +decide [ Matrix.det_transpose ] ;
        rw [ ← Matrix.det_transpose ];
        congr! 1;
      · rw [ Matrix.rank_transpose, hA ];
    -- The determinant of the submatrix is a polynomial in the entries of A.
    obtain ⟨p, hp⟩ : ∃ p : MvPolynomial (Vars n) ℝ, ∀ A' : Fin n → Matrix (Fin 3) (Fin 4) ℝ, MvPolynomial.eval (to_vec A') p = Matrix.det (Matrix.submatrix (C A') c id) := by
      use Matrix.det (Matrix.of (fun i j => MvPolynomial.X (inv_iota_alpha (c i), inv_iota_i (c i), j)));
      simp +decide [ Matrix.det_apply', Matrix.submatrix ];
      exact fun A' ↦ rfl;
    refine' ⟨ p, _, _ ⟩;
    · intro h; simp_all +decide [ MvPolynomial.eval_eq' ] ;
      exact hc ( hp A ▸ rfl );
    · intro A' hA'
      have h_rank : Matrix.rank (C A') ≥ 4 := by
        have h_rank : Matrix.rank (Matrix.submatrix (C A') c id) ≥ 4 := by
          have := Matrix.rank_mul_le ( Matrix.submatrix ( C A' ) c id ) ( Matrix.submatrix ( C A' ) c id ) ⁻¹; simp_all +decide [ isUnit_iff_ne_zero ] ;
        refine' le_trans h_rank _;
        -- The rank of a submatrix is less than or equal to the rank of the original matrix.
        have h_submatrix_rank : ∀ (A : Matrix (Fin (3 * n)) (Fin 4) ℝ) (c : Fin 4 → Fin (3 * n)), Matrix.rank (Matrix.submatrix A c id) ≤ Matrix.rank A := by
          intros A c; exact (by
          have h_submatrix_rank : ∀ (A : Matrix (Fin (3 * n)) (Fin 4) ℝ) (c : Fin 4 → Fin (3 * n)), Matrix.rank (Matrix.submatrix A c id) ≤ Matrix.rank A := by
            intros A c
            have h_submatrix : ∃ (B : Matrix (Fin 4) (Fin (3 * n)) ℝ), Matrix.submatrix A c id = B * A := by
              use Matrix.of (fun i j => if j = c i then 1 else 0);
              ext i j; simp +decide [ Matrix.mul_apply ] ;
            obtain ⟨ B, hB ⟩ := h_submatrix; rw [ hB ] ; exact Matrix.rank_mul_le_right _ _;
          exact h_submatrix_rank A c);
        exact h_submatrix_rank _ _;
      exact le_antisymm ( le_trans ( Matrix.rank_le_card_width _ ) ( by norm_num ) ) h_rank;
  -- Let's choose any $A$ such that $C$ has rank 4.
  obtain ⟨A, hA⟩ : ∃ A : Fin n → Matrix (Fin 3) (Fin 4) ℝ, Matrix.rank (C A) = 4 := by
    -- Let's choose any $A$ such that $C$ has rank 4. We can construct such an $A$ by choosing $A^{(0)}$ to have rows $e_1, e_2, e_3$ and $A^{(1)}$ to have row $e_4$ (and zeros).
    use fun α => if α.val = 0 then !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] else if α.val = 1 then !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0] else 0;
    refine' le_antisymm _ _;
    · refine' le_trans ( Matrix.rank_le_card_width _ ) _ ; norm_num;
    · refine' le_trans _ ( Submodule.finrank_mono <| show LinearMap.range ( Matrix.mulVecLin ( StackedMatrix ( fun α : Fin n => if α.val = 0 then !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] else if α.val = 1 then !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0] else 0 ) ) ) ≥ Submodule.span ℝ ( Set.range ( fun i : Fin 4 => Matrix.mulVec ( StackedMatrix ( fun α : Fin n => if α.val = 0 then !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0] else if α.val = 1 then !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0] else 0 ) ) ( Pi.single i 1 ) ) ) from _ );
      · rw [ @finrank_span_eq_card ];
        · norm_num;
        · rw [ Fintype.linearIndependent_iff ] ; norm_num;
          simp +decide [ Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ ];
          intro g hg; have := hg ⟨ 0, by linarith ⟩ ; have := hg ⟨ 1, by linarith ⟩ ; have := hg ⟨ 2, by linarith ⟩ ; have := hg ⟨ 3, by linarith ⟩ ; simp_all +decide [ Fin.forall_fin_succ, StackedMatrix ] ;
          have := hg ⟨ 0, by linarith ⟩ ; have := hg ⟨ 1, by linarith ⟩ ; have := hg ⟨ 2, by linarith ⟩ ; have := hg ⟨ 3, by linarith ⟩ ; simp_all +decide [ inv_iota_alpha, inv_iota_i ] ;
      · exact Submodule.span_le.mpr ( Set.range_subset_iff.mpr fun i => LinearMap.mem_range_self _ _ );
  exact Exists.elim ( h_open A hA ) fun p hp => ⟨ p, hp.1, hp.2 ⟩

end CRankGeneric

/-
Lemma 5.5 (Matrix version): If D C = C G, and C has rank 4 with rank-3 blocks, then D is scalar.
-/
section StabilizerMatrix

open Matrix BigOperators Fintype

variable {n : ℕ}

lemma stabilizer_lemma_matrix (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (hC : (StackedMatrix A).rank = 4)
    (h_blocks : ∀ α, (A α).rank = 3)
    (s : Fin n → ℝ) (hs : ∀ α, s α ≠ 0)
    (h_stab : ∃ G : Matrix (Fin 4) (Fin 4) ℝ, scaling_matrix s * StackedMatrix A = StackedMatrix A * G) :
    ∀ α β, s α = s β := by
      intro α β;
      -- By assumption, $D C = C G$ for some matrix $G$.
      obtain ⟨G, hG⟩ := h_stab;
      -- This implies for each block $\alpha$: $s_\alpha A^{(\alpha)} = A^{(\alpha)} G$.
      have h_block_eq : ∀ α, s α • A α = A α * G := by
        intro α; ext i j; replace hG := congr_fun ( congr_fun hG ( iota α i ) ) j; simp_all +decide [ Matrix.mul_apply, StackedMatrix ] ;
        unfold scaling_matrix at hG; simp_all +decide [ Finset.sum_ite, Finset.filter_ne', Finset.filter_eq', inv_iota_alpha, inv_iota_i ] ;
        simp_all +decide [ Finset.sum_apply, Matrix.diagonal_apply, iota ];
        convert hG using 1;
        · fin_cases i <;> norm_num [ Nat.add_div ];
        · norm_num [ Nat.add_div, Nat.mod_eq_of_lt ];
          fin_cases i <;> trivial;
      -- Since $A^{(\alpha)}$ has rank 3, the geometric multiplicity of $s_\alpha$ (for $G^\top$) is at least 3.
      have h_geom_mult : ∀ α, 3 ≤ Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (G.transpose - Matrix.diagonal (fun _ => s α)))) := by
        intro α
        have h_geom_mult_alpha : LinearMap.range (Matrix.mulVecLin (A α).transpose) ≤ LinearMap.ker (Matrix.mulVecLin (G.transpose - Matrix.diagonal (fun _ => s α))) := by
          intro x hx
          obtain ⟨y, hy⟩ := hx
          have h_eq : s α • (A α).transpose.mulVec y = G.transpose.mulVec ((A α).transpose.mulVec y) := by
            convert congr_arg ( fun m => m.transpose.mulVec y ) ( h_block_eq α ) using 1 <;> simp +decide [ Matrix.mul_assoc, Matrix.transpose_mul ];
            exact Eq.symm (smul_mulVec (s α) (A α)ᵀ y);
          simp_all +decide [ ← Matrix.mulVec_transpose, ← Matrix.mulVec_smul, ← Matrix.mulVec_mulVec ];
        refine' le_trans _ ( Submodule.finrank_mono h_geom_mult_alpha );
        rw [ ← Matrix.rank, Matrix.rank_transpose ] ; aesop;
      -- If there are two distinct eigenvalues $s_\alpha, s_\beta$, then we have two eigenspaces of dimension $\ge 3$ in $\mathbb{R}^4$.
      by_contra h_contra
      have h_eigenvalues : s α ≠ s β := by
        assumption;
      have h_sum_geom_mult : Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (G.transpose - Matrix.diagonal (fun _ => s α)))) + Module.finrank ℝ (LinearMap.ker (Matrix.mulVecLin (G.transpose - Matrix.diagonal (fun _ => s β)))) ≤ 4 := by
        have h_sum_geom_mult : ∀ (V W : Submodule ℝ (Fin 4 → ℝ)), V ⊓ W = ⊥ → Module.finrank ℝ V + Module.finrank ℝ W ≤ 4 := by
          intros V W h_inter; have := Submodule.finrank_sup_add_finrank_inf_eq V W; simp_all +decide ;
          rw [ ← this, h_inter, finrank_bot ] ; norm_num;
          exact le_trans ( Submodule.finrank_le _ ) ( by norm_num );
        apply h_sum_geom_mult;
        simp +decide [ Submodule.eq_bot_iff ];
        intro x hx₁ hx₂; ext i; simp_all +decide [ sub_eq_iff_eq_add, funext_iff ] ;
      linarith [ h_geom_mult α, h_geom_mult β ]

end StabilizerMatrix

/-
Lemma 5.5: Block-diagonal stabilizer. If a block-diagonal matrix D stabilizes the column space of C, and C has rank 4 with rank-3 blocks, then D is a scalar multiple of identity.
-/
section StabilizerFinal

open Matrix BigOperators Fintype

variable {n : ℕ}

lemma stabilizer_lemma (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (hC : (StackedMatrix A).rank = 4)
    (h_blocks : ∀ α, (A α).rank = 3)
    (s : Fin n → ℝ) (hs : ∀ α, s α ≠ 0)
    (h_stab : Submodule.map (Matrix.mulVecLin (scaling_matrix s)) (LinearMap.range (Matrix.mulVecLin (StackedMatrix A))) =
              LinearMap.range (Matrix.mulVecLin (StackedMatrix A))) :
    ∀ α β, s α = s β := by
      intros α β
      have h_subspace : ∃ G : Matrix (Fin 4) (Fin 4) ℝ, scaling_matrix s * StackedMatrix A = StackedMatrix A * G := by
        have h_subspace : ∀ j : Fin 4, ∃ g : Fin 4 → ℝ, (scaling_matrix s).mulVec (StackedMatrix A |> Matrix.mulVecLin <| Pi.single j 1) = (StackedMatrix A).mulVecLin g := by
          intro j
          have h_subspace : (scaling_matrix s).mulVec (StackedMatrix A |> Matrix.mulVecLin <| Pi.single j 1) ∈ LinearMap.range (StackedMatrix A).mulVecLin := by
            exact h_stab ▸ Submodule.mem_map_of_mem ( LinearMap.mem_range_self _ _ );
          exact h_subspace.imp fun x hx => hx.symm;
        choose g hg using h_subspace;
        use Matrix.of (fun i j => g j i);
        ext i j; specialize hg j; replace hg := congr_fun hg i; aesop;
      exact stabilizer_lemma_matrix A hC h_blocks s hs h_subspace α β

end StabilizerFinal

/-
Lemma 6.2: Column-group scaling identity. The submatrix of the unfolding of the scaled tensor is the scaled submatrix of the unfolding of the original tensor.
-/
section ColGroupScaling

open Matrix BigOperators Fintype

variable {n : ℕ}

lemma colgroup_scaling (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (β γ δ : Fin n) :
    let Q_fam := fun α β γ δ => Q_block A α β γ δ
    let T_fam := block_scaling lam Q_fam
    let mathcal_Q := Asm Q_fam
    let mathcal_T := Asm T_fam
    let s := fun α => lam α β γ δ
    unfolding_column_submatrix mathcal_T β γ δ =
    scaling_matrix s * unfolding_column_submatrix mathcal_Q β γ δ := by
      unfold unfolding_column_submatrix scaling_matrix;
      unfold unfolding Asm block_scaling;
      ext r idx; simp +decide [ combine_indices ] ; ring_nf;
      unfold inv_iota_alpha iota; simp +decide ;
      norm_num [ Nat.add_div ];
      exact Or.inl ( by congr <;> fin_cases idx <;> trivial )

end ColGroupScaling

/-
Helper lemma: If a subspace W is contained in U, dim(W)=4, and dim(U)<=4, then W=U (assuming ambient space is finite dimensional).
-/
section HelperLemmas1Fixed

open Matrix BigOperators Fintype

variable {n : ℕ}

lemma submodule_equality_of_rank {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
    [FiniteDimensional R M]
    {W U : Submodule R M} (hWU : W ≤ U)
    (hW : Module.finrank R W = 4)
    (hU : Module.finrank R U ≤ 4) : W = U := by
      exact Submodule.eq_of_le_of_finrank_eq hWU ( by linarith [ show Module.finrank R U ≥ 4 by exact hW ▸ Submodule.finrank_mono hWU ] )

end HelperLemmas1Fixed

/-
Helper lemma: The range of A*B is the image of the range of B under A (if A is invertible/surjective).
-/
section HelperLemmas2

open Matrix BigOperators Fintype

variable {n : ℕ}

lemma range_scaling_submatrix (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin 4) ℝ)
    (hA : IsUnit A) :
    LinearMap.range (Matrix.mulVecLin (A * B)) =
    Submodule.map (Matrix.mulVecLin A) (LinearMap.range (Matrix.mulVecLin B)) := by
      ext; simp [Matrix.mulVecLin]

end HelperLemmas2

/-
Lemma: The rank of the submatrix of the unfolding of Q is 4.
-/
section RankQSub

open Matrix BigOperators Fintype

variable {n : ℕ}

lemma rank_unfolding_submatrix_Q (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (β γ δ : Fin n)
    (hC : (StackedMatrix A).rank = 4)
    (hP : (P_matrix A β γ δ).rank = 4) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (unfolding_column_submatrix (Asm (fun α β γ δ => Q_block A α β γ δ)) β γ δ)ᵀ)) = 4 := by
      rw [ group_span ];
      · rw [ show Submodule.span ℝ ( Set.range ( P_matrix A β γ δ ) ᵀ ) = LinearMap.range ( Matrix.mulVecLin ( P_matrix A β γ δ ) ) from ?_ ];
        · rw [ LinearMap.range_eq_top.mpr ];
          · rw [ show Submodule.map ( Matrix.mulVecLin ( StackedMatrix A ) ) ⊤ = LinearMap.range ( Matrix.mulVecLin ( StackedMatrix A ) ) by ext; aesop ] ; aesop;
          · exact LinearMap.range_eq_top.mp ( Submodule.eq_top_of_finrank_eq <| by aesop );
        · ext; simp [Matrix.mulVecLin];
          simp +decide [ Submodule.mem_span_range_iff_exists_fun, Matrix.mulVec, funext_iff ];
          simp +decide only [dotProduct, mul_comm];
      · exact hC

end RankQSub

/-
Lemma: The column space of the unfolding submatrix for a non-constant triple is equal to the column space of the full unfolding.
-/
section ColSpaceConstant

open Matrix BigOperators Fintype

variable {n : ℕ}

lemma col_space_eq_global (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hC : (StackedMatrix A).rank = 4)
    (hP : ∀ β γ δ, not_constant_triple β γ δ → (P_matrix A β γ δ).rank = 4)
    (h_lam_supp : ∀ α β γ δ, not_all_identical α β γ δ ↔ lam α β γ δ ≠ 0)
    (hT : (unfolding (I_3n n) 0 (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ)))).rank ≤ 4)
    (β γ δ : Fin n) (h_triple : not_constant_triple β γ δ) :
    LinearMap.range (Matrix.mulVecLin (unfolding_column_submatrix (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))) β γ δ)) =
    LinearMap.range (Matrix.mulVecLin (unfolding (I_3n n) 0 (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))))) := by
      have h_dim_T_submatrix : Module.finrank ℝ (LinearMap.range (Matrix.mulVecLin (unfolding_column_submatrix (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))) β γ δ))) = 4 := by
        have h_submatrix_range : LinearMap.range (Matrix.mulVecLin (unfolding_column_submatrix (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))) β γ δ)) = Submodule.map (Matrix.mulVecLin (scaling_matrix (fun α => lam α β γ δ))) (LinearMap.range (Matrix.mulVecLin (unfolding_column_submatrix (Asm (fun α β γ δ => Q_block A α β γ δ)) β γ δ))) := by
          have h_submatrix_range : unfolding_column_submatrix (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))) β γ δ = scaling_matrix (fun α => lam α β γ δ) * unfolding_column_submatrix (Asm (fun α β γ δ => Q_block A α β γ δ)) β γ δ := by
            apply colgroup_scaling;
          simp +decide [ h_submatrix_range, LinearMap.range_comp ];
        have h_submatrix_range_dim : Module.finrank ℝ (LinearMap.range (Matrix.mulVecLin (unfolding_column_submatrix (Asm (fun α β γ δ => Q_block A α β γ δ)) β γ δ))) = 4 := by
          convert rank_unfolding_submatrix_Q A β γ δ hC ( hP β γ δ h_triple ) using 1;
          rw [ show LinearMap.range ( Matrix.mulVecLin _ ) = Submodule.span ℝ ( Set.range ( Matrix.transpose _ ) ) from ?_ ];
          ext; simp [Matrix.mulVecLin];
          simp +decide [ Submodule.mem_span_range_iff_exists_fun, Matrix.mulVec, funext_iff ];
          simp +decide [ dotProduct, mul_comm ];
        rw [ h_submatrix_range, ← h_submatrix_range_dim ];
        have h_submatrix_range_dim : LinearMap.ker (Matrix.mulVecLin (scaling_matrix (fun α => lam α β γ δ))) = ⊥ := by
          have h_submatrix_range_dim : ∀ α, lam α β γ δ ≠ 0 := by
            intro α; specialize h_lam_supp α β γ δ; unfold not_all_identical at h_lam_supp; aesop;
          rw [ LinearMap.ker_eq_bot' ];
          intro m hm; ext i; replace hm := congr_fun hm i; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
          simp_all +decide [ scaling_matrix, Matrix.diagonal ];
        -- Since the scaling matrix is invertible, the image of the range under this map should have the same dimension as the original range.
        have h_submatrix_range_dim : Function.Injective (Matrix.mulVecLin (scaling_matrix (fun α => lam α β γ δ))) := by
          exact LinearMap.ker_eq_bot.mp h_submatrix_range_dim;
        have h_submatrix_range_dim : ∀ (V : Submodule ℝ (Fin (3 * n) → ℝ)), Module.finrank ℝ (Submodule.map (Matrix.mulVecLin (scaling_matrix (fun α => lam α β γ δ))) V) = Module.finrank ℝ V := by
          intro V; exact (by
          have h_submatrix_range_dim : ∀ (V : Submodule ℝ (Fin (3 * n) → ℝ)), Module.finrank ℝ (Submodule.map (Matrix.mulVecLin (scaling_matrix (fun α => lam α β γ δ))) V) = Module.finrank ℝ V := by
            intro V
            have h_inj : Function.Injective (Matrix.mulVecLin (scaling_matrix (fun α => lam α β γ δ))) := by
              exact h_submatrix_range_dim
            exact (by
              have h_iso : V ≃ₗ[ℝ] Submodule.map (Matrix.mulVecLin (scaling_matrix (fun α => lam α β γ δ))) V := by
                exact
                  Submodule.equivMapOfInjective (scaling_matrix fun α ↦ lam α β γ δ).mulVecLin
                    h_submatrix_range_dim V
              exact (by
              exact LinearEquiv.finrank_eq h_iso |> Eq.symm));
          exact h_submatrix_range_dim V);
        exact h_submatrix_range_dim _;
      have h_dim_T : Module.finrank ℝ (LinearMap.range (Matrix.mulVecLin (unfolding (I_3n n) 0 (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))))) ) ≤ 4 := by
        convert hT using 1;
      apply_rules [ Submodule.eq_of_le_of_finrank_eq ];
      · intro x hx; obtain ⟨ y, rfl ⟩ := hx; exact (by
        use Matrix.mulVec (Matrix.of (fun (i : {k : Fin 4 // k ≠ 0} → Fin (3 * n)) (j : Fin 3 × Fin 3 × Fin 3) => if i = (fun k => if k.val = 1 then iota β j.1 else if k.val = 2 then iota γ j.2.1 else iota δ j.2.2) then 1 else 0)) y;
        ext i; simp +decide [ Matrix.mulVec, dotProduct ] ;
        simp +decide [ Finset.sum_filter, unfolding_column_submatrix ];
        simp +decide [ Finset.sum_mul _ _ _, Finset.mul_sum ];
        rw [ Finset.sum_comm ];
        simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ]);
      · refine' le_antisymm _ _;
        · refine' Submodule.finrank_mono _;
          rintro x ⟨ y, rfl ⟩;
          use Matrix.mulVec (Matrix.of (fun (idx : {k : Fin 4 // k ≠ 0} → Fin (3 * n)) (j : Fin 3 × Fin 3 × Fin 3) => if idx = (fun k => if h1 : k.val = 1 then iota β j.1 else if h2 : k.val = 2 then iota γ j.2.1 else iota δ j.2.2) then 1 else 0)) y;
          ext i; simp +decide [ Matrix.mulVec, dotProduct ] ;
          simp +decide [ Finset.sum_filter, unfolding_column_submatrix ];
          simp +decide [ Finset.sum_mul _ _ _, Finset.mul_sum ];
          rw [ Finset.sum_comm ];
          simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ];
        · grind

end ColSpaceConstant

/-
Lemma: The ratio of lambda values for two non-constant triples is constant in alpha.
-/
section RatioConstant

open Matrix BigOperators Fintype

variable {n : ℕ}

lemma ratio_is_constant (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hC : (StackedMatrix A).rank = 4)
    (h_blocks : ∀ α, (A α).rank = 3)
    (hP : ∀ β γ δ, not_constant_triple β γ δ → (P_matrix A β γ δ).rank = 4)
    (h_lam_supp : ∀ α β γ δ, not_all_identical α β γ δ ↔ lam α β γ δ ≠ 0)
    (hT : (unfolding (I_3n n) 0 (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ)))).rank ≤ 4)
    (β γ δ β' γ' δ' : Fin n)
    (h_triple : not_constant_triple β γ δ)
    (h_triple' : not_constant_triple β' γ' δ') :
    ∀ α α', lam α β γ δ / lam α β' γ' δ' = lam α' β γ δ / lam α' β' γ' δ' := by
      -- By `col_space_eq_global`, $\col(\mathcal{T}_{(1)}^{(\beta\gamma\delta)}) = \col(\mathcal{T}_{(1)})$ and $\col(\mathcal{T}_{(1)}^{(\beta'\gamma'\delta')}) = \col(\mathcal{T}_{(1)})$.
      have h_col_space_eq_global : LinearMap.range (Matrix.mulVecLin (unfolding_column_submatrix (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))) β γ δ)) = LinearMap.range (Matrix.mulVecLin (unfolding (I_3n n) 0 (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))))) ∧ LinearMap.range (Matrix.mulVecLin (unfolding_column_submatrix (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))) β' γ' δ')) = LinearMap.range (Matrix.mulVecLin (unfolding (I_3n n) 0 (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))))) := by
        apply And.intro;
        · apply col_space_eq_global A lam hC hP h_lam_supp hT β γ δ h_triple;
        · apply col_space_eq_global A lam hC hP h_lam_supp hT β' γ' δ' h_triple';
      -- By Lemma `colgroup_scaling`, $\col(\mathcal{T}_{(1)}^{(\beta\gamma\delta)}) = D^{(\beta\gamma\delta)} \col(\mathcal{Q}_{(1)}^{(\beta\gamma\delta)})$.
      have h_colgroup_scaling : LinearMap.range (Matrix.mulVecLin (scaling_matrix (fun α => lam α β γ δ) * unfolding_column_submatrix (Asm (fun α β γ δ => Q_block A α β γ δ)) β γ δ)) = LinearMap.range (Matrix.mulVecLin (unfolding (I_3n n) 0 (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))))) ∧ LinearMap.range (Matrix.mulVecLin (scaling_matrix (fun α => lam α β' γ' δ') * unfolding_column_submatrix (Asm (fun α β γ δ => Q_block A α β γ δ)) β' γ' δ')) = LinearMap.range (Matrix.mulVecLin (unfolding (I_3n n) 0 (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))))) := by
        have h_colgroup_scaling : unfolding_column_submatrix (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))) β γ δ = scaling_matrix (fun α => lam α β γ δ) * unfolding_column_submatrix (Asm (fun α β γ δ => Q_block A α β γ δ)) β γ δ ∧ unfolding_column_submatrix (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))) β' γ' δ' = scaling_matrix (fun α => lam α β' γ' δ') * unfolding_column_submatrix (Asm (fun α β γ δ => Q_block A α β γ δ)) β' γ' δ' := by
          exact ⟨ colgroup_scaling A lam β γ δ, colgroup_scaling A lam β' γ' δ' ⟩;
        aesop;
      -- By Lemma `group_span`, $\col(\mathcal{Q}_{(1)}^{(\beta\gamma\delta)}) = \col(C)$ and $\col(\mathcal{Q}_{(1)}^{(\beta'\gamma'\delta')}) = \col(C)$.
      have h_group_span : LinearMap.range (Matrix.mulVecLin (unfolding_column_submatrix (Asm (fun α β γ δ => Q_block A α β γ δ)) β γ δ)) = LinearMap.range (Matrix.mulVecLin (StackedMatrix A)) ∧ LinearMap.range (Matrix.mulVecLin (unfolding_column_submatrix (Asm (fun α β γ δ => Q_block A α β γ δ)) β' γ' δ')) = LinearMap.range (Matrix.mulVecLin (StackedMatrix A)) := by
        have := group_span A β γ δ hC; have := group_span A β' γ' δ' hC; simp_all +decide [ Submodule.map_comap_eq, Submodule.comap_map_eq ] ;
        have h_group_span : Submodule.span ℝ (Set.range (P_matrix A β γ δ)ᵀ) = ⊤ ∧ Submodule.span ℝ (Set.range (P_matrix A β' γ' δ')ᵀ) = ⊤ := by
          have h_group_span : ∀ (M : Matrix (Fin 4) (Fin 3 × Fin 3 × Fin 3) ℝ), Matrix.rank M = 4 → Submodule.span ℝ (Set.range Mᵀ) = ⊤ := by
            intros M hM_rank
            have hM_span : Submodule.span ℝ (Set.range Mᵀ) = ⊤ := by
              have hM_dim : Module.finrank ℝ (Submodule.span ℝ (Set.range Mᵀ)) = 4 := by
                convert hM_rank using 1;
                rw [ Matrix.rank ];
                rw [ show LinearMap.range M.mulVecLin = Submodule.span ℝ ( Set.range Mᵀ ) from ?_ ];
                ext; simp [Matrix.mulVecLin];
                simp +decide [ Submodule.mem_span_range_iff_exists_fun, Matrix.mulVec, funext_iff ];
                simp +decide [ dotProduct, mul_comm ]
              exact Submodule.eq_top_of_finrank_eq ( by simpa [ hM_dim ] );
            exact hM_span;
          exact ⟨ h_group_span _ ( hP _ _ _ h_triple ), h_group_span _ ( hP _ _ _ h_triple' ) ⟩;
        simp_all +decide [ Submodule.map_top ];
        convert And.intro ‹Submodule.span ℝ ( Set.range ( unfolding_column_submatrix ( Asm fun α β γ δ => Q_block A α β γ δ ) β γ δ ) ᵀ ) = LinearMap.range ( StackedMatrix A |> Matrix.mulVecLin ) › ‹Submodule.span ℝ ( Set.range ( unfolding_column_submatrix ( Asm fun α β γ δ => Q_block A α β γ δ ) β' γ' δ' ) ᵀ ) = LinearMap.range ( StackedMatrix A |> Matrix.mulVecLin ) › using 1;
        · rw [ ← ‹Submodule.span ℝ ( Set.range ( unfolding_column_submatrix ( Asm fun α β γ δ => Q_block A α β γ δ ) β γ δ ) ᵀ ) = LinearMap.range ( StackedMatrix A |> Matrix.mulVecLin ) › ];
          simp +decide [ Submodule.ext_iff, SetLike.ext_iff ];
          simp +decide [ Submodule.mem_span_range_iff_exists_fun ];
          simp +decide [ funext_iff, Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _ ];
          exact fun x => ⟨ fun ⟨ y, hy ⟩ => ⟨ y, fun i => by simpa only [ mul_comm ] using hy i ⟩, fun ⟨ y, hy ⟩ => ⟨ y, fun i => by simpa only [ mul_comm ] using hy i ⟩ ⟩;
        · simp +decide [ ← this, LinearMap.range_eq_top ];
          ext; simp [Matrix.mulVecLin];
          simp +decide [ Submodule.mem_span_range_iff_exists_fun, Matrix.mulVec, dotProduct ];
          simp +decide [ funext_iff, Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_comm ];
      -- By Lemma `stabilizer_lemma`, $D^{(\beta'\gamma'\delta')})^{-1} D^{(\beta\gamma\delta)}$ is a scalar multiple of identity.
      have h_stabilizer : ∀ (s : Fin n → ℝ), (∀ α, s α ≠ 0) → (Submodule.map (Matrix.mulVecLin (scaling_matrix s)) (LinearMap.range (Matrix.mulVecLin (StackedMatrix A)))) = LinearMap.range (Matrix.mulVecLin (StackedMatrix A)) → ∀ α β, s α = s β := by
        exact fun s a a_1 α β ↦ stabilizer_lemma A hC h_blocks s a a_1 α β;
      contrapose! h_stabilizer;
      refine' ⟨ fun α => lam α β γ δ / lam α β' γ' δ', _, _, _ ⟩ <;> simp_all +decide [ division_def ];
      · intro α; have := h_lam_supp α β γ δ; have := h_lam_supp α β' γ' δ'; simp_all +decide [ not_all_identical ] ;
        exact ⟨ by specialize h_lam_supp α β γ δ; aesop_cat, by specialize h_lam_supp α β' γ' δ'; aesop_cat ⟩;
      · convert congr_arg ( fun x => Submodule.map ( Matrix.mulVecLin ( scaling_matrix ( fun α => ( lam α β' γ' δ' ) ⁻¹ ) ) ) x ) h_colgroup_scaling.1 using 1;
        · simp +decide [ ← h_group_span.1, ← h_group_span.2, Submodule.map_comp ];
          ext; simp [Matrix.mulVecLin];
          simp +decide [ ← Matrix.mul_assoc, scaling_matrix ];
          simp +decide only [mul_comm];
        · rw [ ← h_colgroup_scaling.2, ← h_group_span.2 ];
          ext; simp [Matrix.mulVecLin];
          congr! 2;
          congr! 2;
          ext i j; simp +decide [ Matrix.mul_apply, scaling_matrix ] ; ring_nf;
          simp +decide [ Matrix.diagonal, Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ];
          rw [ ← mul_assoc, inv_mul_cancel₀ ( h_lam_supp _ _ _ _ |>.1 <| by
            exact fun h => h_triple' <| by aesop; ), one_mul ]

end RatioConstant

/-
Proposition 6.3: Mode-1 factorization of lambda. If the mode-1 unfolding has rank at most 4, then lambda factors as u_alpha * mu_{beta,gamma,delta} for non-constant triples.
-/
section Mode1FactorFinal

open Matrix BigOperators Fintype

variable {n : ℕ}

lemma mode1_factor (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (h_n : n ≥ 5)
    (hC : (StackedMatrix A).rank = 4)
    (h_blocks : ∀ α, (A α).rank = 3)
    (hP : ∀ β γ δ, not_constant_triple β γ δ → (P_matrix A β γ δ).rank = 4)
    (h_lam_supp : ∀ α β γ δ, not_all_identical α β γ δ ↔ lam α β γ δ ≠ 0)
    (hT : (unfolding (I_3n n) 0 (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ)))).rank ≤ 4) :
    ∃ (u : Fin n → ℝ) (mu : Fin n → Fin n → Fin n → ℝ),
      (∀ α, u α ≠ 0) ∧
      ∀ α β γ δ, not_constant_triple β γ δ → lam α β γ δ = u α * mu β γ δ := by
        use fun α => lam α ⟨ 0, by linarith ⟩ ⟨ 1, by linarith ⟩ ⟨ 2, by linarith ⟩;
        use fun β γ δ => lam ⟨ 0, by linarith ⟩ β γ δ / lam ⟨ 0, by linarith ⟩ ⟨ 0, by linarith ⟩ ⟨ 1, by linarith ⟩ ⟨ 2, by linarith ⟩;
        have h_ratio : ∀ α β γ δ, not_constant_triple β γ δ → lam α β γ δ / lam α ⟨ 0, by linarith ⟩ ⟨ 1, by linarith ⟩ ⟨ 2, by linarith ⟩ = lam ⟨ 0, by linarith ⟩ β γ δ / lam ⟨ 0, by linarith ⟩ ⟨ 0, by linarith ⟩ ⟨ 1, by linarith ⟩ ⟨ 2, by linarith ⟩ := by
          intros α β γ δ h_triple
          have h_ratio : lam α β γ δ / lam α ⟨ 0, by linarith ⟩ ⟨ 1, by linarith ⟩ ⟨ 2, by linarith ⟩ = lam ⟨ 0, by linarith ⟩ β γ δ / lam ⟨ 0, by linarith ⟩ ⟨ 0, by linarith ⟩ ⟨ 1, by linarith ⟩ ⟨ 2, by linarith ⟩ := by
            have h_ratio : lam α β γ δ / lam α ⟨ 0, by linarith ⟩ ⟨ 1, by linarith ⟩ ⟨ 2, by linarith ⟩ = lam ⟨ 0, by linarith ⟩ β γ δ / lam ⟨ 0, by linarith ⟩ ⟨ 0, by linarith ⟩ ⟨ 1, by linarith ⟩ ⟨ 2, by linarith ⟩ := by
              have := ratio_is_constant A lam hC h_blocks hP h_lam_supp hT
              convert this β γ δ ⟨ 0, by linarith ⟩ ⟨ 1, by linarith ⟩ ⟨ 2, by linarith ⟩ h_triple ( by unfold not_constant_triple; simp +decide ) α ⟨ 0, by linarith ⟩ using 1
            exact h_ratio;
          exact h_ratio;
        have h_nonzero : ∀ α, lam α ⟨ 0, by linarith ⟩ ⟨ 1, by linarith ⟩ ⟨ 2, by linarith ⟩ ≠ 0 := by
          intro α; specialize h_lam_supp α ⟨ 0, by linarith ⟩ ⟨ 1, by linarith ⟩ ⟨ 2, by linarith ⟩ ; simp_all +decide [ not_all_identical ] ;
        grind

end Mode1FactorFinal

/-
Swapping the first two block indices and the first two tensor indices negates the Q-block value.
-/
lemma Q_block_swap_12 {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (α β γ δ : Fin n) (idx : Fin 4 → Fin 3) :
    Q_block A β α γ δ (fun k => if k = 0 then idx 1 else if k = 1 then idx 0 else idx k) =
    - Q_block A α β γ δ idx := by
      unfold Q_block; norm_num [ Matrix.det_succ_row_zero ] ; ring_nf;
      simp +decide [ Fin.forall_fin_succ, Fin.sum_univ_succ ] at *;
      simp +decide [ Fin.succAbove ] ; ring!;

/-
The swapped tensor T' evaluated at an index is equal to the original tensor T evaluated at the swapped index.
-/
lemma T_prime_apply {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (idx : Fin 4 → Fin (3 * n)) :
    let lam' := fun β α γ δ => - lam α β γ δ
    let T := Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))
    let T' := Asm (block_scaling lam' (fun α β γ δ => Q_block A α β γ δ))
    T' idx = T (idx ∘ (Equiv.swap 0 1)) := by
      -- By definition of Asm and block_scaling, we can expand both T' and T.
      simp [Asm, block_scaling];
      -- By definition of $Q_block$, we know that $Q_block A β α γ δ (fun k => if k = 0 then idx 1 else if k = 1 then idx 0 else idx k) = - Q_block A α β γ δ idx$.
      have hQ : ∀ (α β γ δ : Fin n) (idx : Fin 4 → Fin 3), Q_block A β α γ δ (fun k => if k = 0 then idx 1 else if k = 1 then idx 0 else idx k) = - Q_block A α β γ δ idx := by
        field_simp;
        exact fun α β γ δ idx ↦ Q_block_swap_12 A α β γ δ idx;
      simp +decide [ Equiv.swap_apply_def ];
      grind

/-
Equivalence between column indices for mode 1 and mode 0.
-/
def col_index_swap_equiv (n : ℕ) :
    ({k : Fin 4 // k ≠ 1} → Fin (3 * n)) ≃ ({k : Fin 4 // k ≠ 0} → Fin (3 * n)) :=
  Equiv.arrowCongr
    (Equiv.subtypeEquiv (Equiv.swap 0 1) (by
      intro x
      simp [Equiv.swap_apply_def]
      constructor <;> intro h
      · split_ifs <;> simp_all
      · split_ifs at h <;> simp_all
    ))
    (Equiv.refl _)

/-
Helper lemma: swapping indices in combine_indices corresponds to swapping the column index function.
-/
lemma combine_indices_swap_eq {n : ℕ} (i : Fin (3 * n)) (j : {k : Fin 4 // k ≠ 0} → Fin (3 * n)) :
    (fun k => combine_indices (I_3n n) 0 i j (Equiv.swap (0 : Fin 4) (1 : Fin 4) k)) =
    combine_indices (I_3n n) 1 i ((col_index_swap_equiv n).symm j) := by
      funext k;
      fin_cases k <;> simp +decide [ Equiv.swap_apply_def ];
      · unfold combine_indices col_index_swap_equiv; aesop;
      · unfold combine_indices; aesop;
      · unfold combine_indices; aesop;
      · exact rfl

/-
The rank of the mode-1 unfolding of the swapped tensor equals the rank of the mode-2 unfolding of the original tensor.
-/
lemma rank_mode_swap_eq {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ) :
    let lam' := fun β α γ δ => - lam α β γ δ
    let T := Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))
    let T' := Asm (block_scaling lam' (fun α β γ δ => Q_block A α β γ δ))
    (unfolding (I_3n n) 0 T').rank = (unfolding (I_3n n) 1 T).rank := by
      refine' le_antisymm _ _;
      · -- By definition of unfolding, we can rewrite the left-hand side using the fact that swapping the first two modes corresponds to permuting the columns.
        have h_unfolding_swap : (unfolding (I_3n n) 0 (Asm (block_scaling (fun β α γ δ => -lam α β γ δ) (fun α β γ δ => Q_block A α β γ δ)))) =
          (unfolding (I_3n n) 1 (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ)))).submatrix id (col_index_swap_equiv n).symm := by
            ext i j; simp +decide [ T_prime_apply ] ;
            convert T_prime_apply A lam ( combine_indices ( I_3n n ) 0 i j ) using 1;
        rw [ h_unfolding_swap ];
        exact
          rank_submatrix_le id (col_index_swap_equiv n).symm
            (unfolding (I_3n n) 1 (Asm (block_scaling lam fun α β γ δ ↦ Q_block A α β γ δ)));
      · refine' Submodule.finrank_mono _;
        intro x;
        rintro ⟨ y, rfl ⟩;
        use fun j => y ( ( col_index_swap_equiv n ).symm j );
        ext i; simp +decide [ Matrix.mulVec, dotProduct ] ;
        refine' Finset.sum_bij ( fun x _ => ( col_index_swap_equiv n ).symm x ) _ _ _ _ <;> simp +decide [ Finset.mem_univ, Finset.mem_filter ];
        · exact fun a₁ a₂ h => by simpa using congr_arg ( col_index_swap_equiv n ) h;
        · exact fun b => ⟨ _, Equiv.apply_symm_apply _ _ ⟩;
        · intro a; exact Or.inl ( by
            convert T_prime_apply A lam ( combine_indices ( I_3n n ) 0 i a ) using 1 ) ;

/-
Factorization for mode 2.
-/
lemma mode2_factor {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (h_n : n ≥ 5)
    (hC : (StackedMatrix A).rank = 4)
    (h_blocks : ∀ α, (A α).rank = 3)
    (hP : ∀ β γ δ, not_constant_triple β γ δ → (P_matrix A β γ δ).rank = 4)
    (h_lam_supp : ∀ α β γ δ, not_all_identical α β γ δ ↔ lam α β γ δ ≠ 0)
    (hT : (unfolding (I_3n n) 1 (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ)))).rank ≤ 4) :
    ∃ (v : Fin n → ℝ) (nu : Fin n → Fin n → Fin n → ℝ),
      (∀ β, v β ≠ 0) ∧
      ∀ α β γ δ, not_constant_triple α γ δ → lam α β γ δ = v β * nu α γ δ := by
        have := rank_mode_swap_eq A lam;
        -- Apply `mode1_factor` to the permuted scaling `lam' β α γ δ := - lam α β γ δ`.
        obtain ⟨u', mu', hu', hmu'⟩ := mode1_factor A (fun β α γ δ => -lam α β γ δ) h_n hC h_blocks (by
        exact hP) (by
        simp_all +decide [ not_all_identical ];
        grind) (by
        convert this.le.trans hT using 1);
        use fun α => -u' α, fun α γ δ => mu' α γ δ;
        exact ⟨ fun α => neg_ne_zero.mpr ( hu' α ), fun α β γ δ h => by have := hmu' β α γ δ h; norm_num at *; linarith ⟩

/-
Swapping the first and third block indices and tensor indices negates the Q-block value.
-/
lemma Q_block_swap_13 {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (α β γ δ : Fin n) (idx : Fin 4 → Fin 3) :
    Q_block A γ β α δ (fun k => if k = 0 then idx 2 else if k = 2 then idx 0 else idx k) =
    - Q_block A α β γ δ idx := by
      unfold Q_block; simp +decide [ Matrix.det_succ_row_zero ] ; ring_nf;
      simp +decide [ Fin.sum_univ_succ, Fin.succAbove ] ; ring!

/-
The swapped tensor T' (modes 0 and 2) evaluated at an index is equal to the original tensor T evaluated at the swapped index.
-/
lemma T_prime_apply_13 {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (idx : Fin 4 → Fin (3 * n)) :
    let lam' := fun γ β α δ => - lam α β γ δ
    let T := Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))
    let T' := Asm (block_scaling lam' (fun α β γ δ => Q_block A α β γ δ))
    T' idx = T (idx ∘ (Equiv.swap 0 2)) := by
      unfold block_scaling Asm; simp +decide [ Fin.sum_univ_four ] ; ring_nf;
      unfold Q_block; simp +decide [ Fin.sum_univ_succ, Matrix.det_succ_row_zero ] ; ring_nf;
      simp +decide [ Fin.succAbove ] ; ring!

/-
Equivalence between column indices for mode 2 and mode 0.
-/
def col_index_swap_equiv_02 (n : ℕ) :
    ({k : Fin 4 // k ≠ 2} → Fin (3 * n)) ≃ ({k : Fin 4 // k ≠ 0} → Fin (3 * n)) :=
  Equiv.arrowCongr
    (Equiv.subtypeEquiv (Equiv.swap 0 2) (by
      intro x
      simp [Equiv.swap_apply_def]
      constructor <;> intro h
      · split_ifs <;> simp_all
      · split_ifs at h <;> simp_all
    ))
    (Equiv.refl _)

/-
Helper lemma: swapping indices 0 and 2 in combine_indices corresponds to swapping the column index function.
-/
lemma combine_indices_swap_eq_02 {n : ℕ} (i : Fin (3 * n)) (j : {k : Fin 4 // k ≠ 0} → Fin (3 * n)) :
    (fun k => combine_indices (I_3n n) 0 i j (Equiv.swap (0 : Fin 4) (2 : Fin 4) k)) =
    combine_indices (I_3n n) 2 i ((col_index_swap_equiv_02 n).symm j) := by
      funext k; simp +decide [combine_indices, col_index_swap_equiv_02];
      fin_cases k <;> simp +decide [ Equiv.swap_apply_def ]

/-
The rank of the mode-1 unfolding of the swapped tensor (modes 1 and 3) equals the rank of the mode-3 unfolding of the original tensor.
-/
lemma rank_mode_swap_eq_02 {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ) :
    let lam' := fun γ β α δ => - lam α β γ δ
    let T := Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))
    let T' := Asm (block_scaling lam' (fun α β γ δ => Q_block A α β γ δ))
    (unfolding (I_3n n) 0 T').rank = (unfolding (I_3n n) 2 T).rank := by
      refine' le_antisymm _ _;
      · convert Submodule.finrank_mono _ using 1;
        · infer_instance;
        · infer_instance;
        · intro x hx;
          obtain ⟨ y, rfl ⟩ := hx;
          use ( y ∘ ( col_index_swap_equiv_02 n ) );
          ext i; simp +decide [ Matrix.mulVec, dotProduct ] ;
          refine' Finset.sum_bij ( fun x _ => ( col_index_swap_equiv_02 n ) x ) _ _ _ _ <;> simp +decide [ Finset.mem_univ ];
          · exact fun a₁ a₂ h => by simpa using congr_arg ( fun f => ( col_index_swap_equiv_02 n ).symm f ) h;
          · exact fun b => ⟨ ( col_index_swap_equiv_02 n ).symm b, by simp +decide ⟩;
          · intro a; left; unfold unfolding; simp +decide [ Asm, block_scaling ] ;
            unfold Q_block; simp +decide [ Fin.sum_univ_succ, Matrix.det_succ_row_zero ] ; ring_nf;
            unfold combine_indices; simp +decide [ Fin.succAbove ] ; ring_nf;
            unfold col_index_swap_equiv_02; simp +decide [ Fin.succAbove ] ; ring_nf;
            simp +decide [ Equiv.swap_apply_def ] ; ring;
      · refine' Submodule.finrank_mono _;
        intro x hx;
        obtain ⟨ y, rfl ⟩ := hx;
        refine' ⟨ fun j => y ( ( col_index_swap_equiv_02 n ).symm j ), _ ⟩;
        ext i; simp +decide [ Matrix.mulVec, dotProduct ] ;
        refine' Finset.sum_bij ( fun x _ => ( col_index_swap_equiv_02 n ).symm x ) _ _ _ _ <;> simp +decide [ Finset.mem_univ, Finset.mem_filter ];
        · exact fun a₁ a₂ h => by simpa using congr_arg ( col_index_swap_equiv_02 n ) h;
        · exact fun b => ⟨ _, Equiv.apply_symm_apply _ _ ⟩;
        · intro a; left; exact (by
          convert T_prime_apply_13 A lam _ using 1);

/-
Factorization for mode 3.
-/
lemma mode3_factor {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (h_n : n ≥ 5)
    (hC : (StackedMatrix A).rank = 4)
    (h_blocks : ∀ α, (A α).rank = 3)
    (hP : ∀ β γ δ, not_constant_triple β γ δ → (P_matrix A β γ δ).rank = 4)
    (h_lam_supp : ∀ α β γ δ, not_all_identical α β γ δ ↔ lam α β γ δ ≠ 0)
    (hT : (unfolding (I_3n n) 2 (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ)))).rank ≤ 4) :
    ∃ (w : Fin n → ℝ) (xi : Fin n → Fin n → Fin n → ℝ),
      (∀ γ, w γ ≠ 0) ∧
      ∀ α β γ δ, not_constant_triple α β δ → lam α β γ δ = w γ * xi α β δ := by
        have := @mode1_factor ( n := n ) ( A := A ) ( lam := fun γ β α δ => -lam α β γ δ ) ( h_n := h_n ) ( hC := hC ) ( h_blocks := h_blocks ) ( hP := fun β γ δ h => ?_ ) ( h_lam_supp := fun α β γ δ => ?_ ) ( hT := ?_ ) <;> norm_num at *;
        · obtain ⟨ u, hu, x, hx ⟩ := this; use fun γ => -u γ; simp_all +decide [ not_all_identical ] ;
          use fun α β δ => x β α δ; intros α β γ δ h; specialize hx γ β α δ; simp_all +decide [ not_constant_triple ] ;
          rw [ ← hx ( by contrapose! h; aesop ), neg_neg ];
        · exact hP β γ δ ( by simpa [ not_constant_triple ] using h );
        · rw [ ← h_lam_supp ] ; unfold not_all_identical; aesop;
        · convert hT using 1;
          convert rank_mode_swap_eq_02 A lam using 1

/-
Swapping the first and fourth block indices and tensor indices negates the Q-block value.
-/
lemma Q_block_swap_14 {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (α β γ δ : Fin n) (idx : Fin 4 → Fin 3) :
    Q_block A δ β γ α (fun k => if k = 0 then idx 3 else if k = 3 then idx 0 else idx k) =
    - Q_block A α β γ δ idx := by
      unfold Q_block;
      rw [ Matrix.det_succ_row _ 3 ] ; norm_num [ Fin.sum_univ_succ, Matrix.det_succ_row _ 2 ] ; ring!;

/-
The swapped tensor T' (modes 0 and 3) evaluated at an index is equal to the original tensor T evaluated at the swapped index.
-/
lemma T_prime_apply_14 {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (idx : Fin 4 → Fin (3 * n)) :
    let lam' := fun δ β γ α => - lam α β γ δ
    let T := Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))
    let T' := Asm (block_scaling lam' (fun α β γ δ => Q_block A α β γ δ))
    T' idx = T (idx ∘ (Equiv.swap 0 3)) := by
      unfold Asm; unfold block_scaling; simp +decide [ Fin.sum_univ_succ, Equiv.swap_apply_def ] ; ring_nf!;
      unfold Q_block; simp +decide [ Fin.sum_univ_succ, Matrix.det_succ_row_zero ] ; ring!;

/-
Equivalence between column indices for mode 3 and mode 0.
-/
def col_index_swap_equiv_03 (n : ℕ) :
    ({k : Fin 4 // k ≠ 3} → Fin (3 * n)) ≃ ({k : Fin 4 // k ≠ 0} → Fin (3 * n)) :=
  Equiv.arrowCongr
    (Equiv.subtypeEquiv (Equiv.swap 0 3) (by
      intro x
      simp [Equiv.swap_apply_def]
      constructor <;> intro h
      · split_ifs <;> simp_all
      · split_ifs at h <;> simp_all
    ))
    (Equiv.refl _)

/-
Helper lemma: swapping indices 0 and 3 in combine_indices corresponds to swapping the column index function.
-/
lemma combine_indices_swap_eq_03 {n : ℕ} (i : Fin (3 * n)) (j : {k : Fin 4 // k ≠ 0} → Fin (3 * n)) :
    (fun k => combine_indices (I_3n n) 0 i j (Equiv.swap (0 : Fin 4) (3 : Fin 4) k)) =
    combine_indices (I_3n n) 3 i ((col_index_swap_equiv_03 n).symm j) := by
      -- By definition of combine_indices, we can expand both sides.
      funext k; simp [combine_indices, col_index_swap_equiv_03];
      fin_cases k <;> simp +decide [ Equiv.swap_apply_def ]

/-
The rank of the mode-1 unfolding of the swapped tensor (modes 1 and 4) equals the rank of the mode-4 unfolding of the original tensor.
-/
lemma rank_mode_swap_eq_03 {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ) :
    let lam' := fun δ β γ α => - lam α β γ δ
    let T := Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))
    let T' := Asm (block_scaling lam' (fun α β γ δ => Q_block A α β γ δ))
    (unfolding (I_3n n) 0 T').rank = (unfolding (I_3n n) 3 T).rank := by
      refine' le_antisymm _ _;
      · refine' Submodule.finrank_mono _;
        rintro x ⟨ y, rfl ⟩;
        refine' ⟨ _, _ ⟩;
        exact fun x => y ( fun k => x ( ⟨ Equiv.swap 0 3 k, by
          native_decide +revert ⟩ ) );
        ext; simp +decide [ Matrix.mulVec, dotProduct ] ;
        refine' Finset.sum_bij ( fun x _ => fun k => x ⟨ Equiv.swap 0 3 k, _ ⟩ ) _ _ _ _ <;> simp +decide [ Equiv.swap_apply_def ];
        all_goals norm_num [ funext_iff, Fin.forall_fin_succ ];
        grind;
        · tauto;
        · exact fun b => ⟨ fun k => b ⟨ Equiv.swap 0 3 k, by
            decide +revert ⟩, rfl, rfl, rfl ⟩;
        · unfold unfolding; simp +decide [ Asm, block_scaling ] ;
          unfold combine_indices; simp +decide [ Fin.sum_univ_succ, Matrix.mulVec, dotProduct ] ;
          unfold Q_block; simp +decide [ Fin.sum_univ_succ, Matrix.det_succ_row_zero ] ;
          simp +decide [ Fin.succAbove ] ; ring_nf ; aesop ( simp_config := { decide := true } ) ;
      · refine' Submodule.finrank_mono _;
        intro x;
        rintro ⟨ y, rfl ⟩;
        refine' ⟨ fun i => y ( ( col_index_swap_equiv_03 n ).symm i ), _ ⟩;
        ext i j; simp +decide [ Matrix.mulVec, dotProduct ] ;
        apply Finset.sum_bij (fun x _ => (col_index_swap_equiv_03 n).symm x) _ _ _ <;> simp +decide [ col_index_swap_equiv_03 ];
        · intro a; exact Or.inl (by
          convert T_prime_apply_14 A lam _ using 1);
        · exact fun b => ⟨ _, Equiv.apply_symm_apply _ _ ⟩

/-
Factorization for mode 4.
-/
lemma mode4_factor {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (h_n : n ≥ 5)
    (hC : (StackedMatrix A).rank = 4)
    (h_blocks : ∀ α, (A α).rank = 3)
    (hP : ∀ β γ δ, not_constant_triple β γ δ → (P_matrix A β γ δ).rank = 4)
    (h_lam_supp : ∀ α β γ δ, not_all_identical α β γ δ ↔ lam α β γ δ ≠ 0)
    (hT : (unfolding (I_3n n) 3 (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ)))).rank ≤ 4) :
    ∃ (x : Fin n → ℝ) (zeta : Fin n → Fin n → Fin n → ℝ),
      (∀ δ, x δ ≠ 0) ∧
      ∀ α β γ δ, not_constant_triple α β γ → lam α β γ δ = x δ * zeta α β γ := by
        -- Apply `mode1_factor` to the permuted scaling `lam' δ β γ α := - lam α β γ δ`.
        obtain ⟨u', mu', hu', hmu'⟩ : ∃ (u' : Fin n → ℝ) (mu' : Fin n → Fin n → Fin n → ℝ),
          (∀ δ, u' δ ≠ 0) ∧
          ∀ δ β γ α, not_constant_triple β γ α → - lam α β γ δ = u' δ * mu' β γ α := by
            have h_perm : (unfolding (I_3n n) 0 (Asm (block_scaling (fun δ β γ α => -lam α β γ δ) (fun α β γ δ => Q_block A α β γ δ)))).rank ≤ 4 := by
              convert hT using 1;
              apply rank_mode_swap_eq_03;
            -- Apply `mode1_factor` to the permuted scaling `lam' δ β γ α := - lam α β γ δ` with the given hypotheses.
            apply mode1_factor A (fun δ β γ α => -lam α β γ δ) h_n hC h_blocks (by
            assumption) (by
            simp_all +decide [ not_all_identical ];
            grind) h_perm;
        use fun δ => -u' δ, fun α β γ => mu' β γ α;
        -- For the second part, we can use the fact that if the triple is not constant, then by hmu', we have -lam α β γ δ = u' δ * mu' β γ α. Rearranging gives lam α β γ δ = -u' δ * mu' β γ α.
        apply And.intro;
        · exact fun δ => neg_ne_zero.mpr ( hu' δ );
        · intro α β γ δ h; specialize hmu' δ β γ α; simp_all +decide [ not_constant_triple ] ;
          rw [ ← hmu' ( by rintro rfl; tauto ), neg_neg ]

/-
Corollary 6.4: If the tensor has multilinear rank at most (4,4,4,4), then lambda has a factorization for each mode.
-/
lemma all_modes_factor {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (h_n : n ≥ 5)
    (hC : (StackedMatrix A).rank = 4)
    (h_blocks : ∀ α, (A α).rank = 3)
    (hP : ∀ β γ δ, not_constant_triple β γ δ → (P_matrix A β γ δ).rank = 4)
    (h_lam_supp : ∀ α β γ δ, not_all_identical α β γ δ ↔ lam α β γ δ ≠ 0)
    (hT : rank_le_four (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ)))) :
    ∃ (u v w x : Fin n → ℝ)
      (mu : Fin n → Fin n → Fin n → ℝ)
      (nu : Fin n → Fin n → Fin n → ℝ)
      (xi : Fin n → Fin n → Fin n → ℝ)
      (zeta : Fin n → Fin n → Fin n → ℝ),
      (∀ i, u i ≠ 0) ∧ (∀ i, v i ≠ 0) ∧ (∀ i, w i ≠ 0) ∧ (∀ i, x i ≠ 0) ∧
      (∀ α β γ δ, not_constant_triple β γ δ → lam α β γ δ = u α * mu β γ δ) ∧
      (∀ α β γ δ, not_constant_triple α γ δ → lam α β γ δ = v β * nu α γ δ) ∧
      (∀ α β γ δ, not_constant_triple α β δ → lam α β γ δ = w γ * xi α β δ) ∧
      (∀ α β γ δ, not_constant_triple α β γ → lam α β γ δ = x δ * zeta α β γ) := by
        -- Apply the results from mode1_factor, mode2_factor, mode3_factor, and mode4_factor to obtain the required factorizations.
        obtain ⟨u, mu, hu⟩ := mode1_factor A lam h_n hC h_blocks hP h_lam_supp (hT 0)
        obtain ⟨v, nu, hv⟩ := mode2_factor A lam h_n hC h_blocks hP h_lam_supp (hT 1)
        obtain ⟨w, xi, hw⟩ := mode3_factor A lam h_n hC h_blocks hP h_lam_supp (hT 2)
        obtain ⟨x, zeta, hx⟩ := mode4_factor A lam h_n hC h_blocks hP h_lam_supp (hT 3);
        exact ⟨ u, v, w, x, mu, nu, xi, zeta, hu.1, hv.1, hw.1, hx.1, hu.2, hv.2, hw.2, hx.2 ⟩

/-
Step 1 of separable lambda: factor out u and v for gamma != delta.
-/
lemma separable_lambda_step1 {n : ℕ}
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (u v : Fin n → ℝ)
    (mu : Fin n → Fin n → Fin n → ℝ)
    (nu : Fin n → Fin n → Fin n → ℝ)
    (h_n : n ≥ 1)
    (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0)
    (h_mode1 : ∀ α β γ δ, not_constant_triple β γ δ → lam α β γ δ = u α * mu β γ δ)
    (h_mode2 : ∀ α β γ δ, not_constant_triple α γ δ → lam α β γ δ = v β * nu α γ δ) :
    ∃ (rho : Fin n → Fin n → ℝ),
      ∀ α β γ δ, γ ≠ δ → lam α β γ δ = u α * v β * rho γ δ := by
        -- Fix $\alpha_0 = 0$. Define $\rho_{\gamma\delta} = \nu_{0\gamma\delta} / u_0$.
        set rho : Fin n → Fin n → ℝ := fun γ δ => nu ⟨0, h_n⟩ γ δ / u ⟨0, h_n⟩;
        use rho;
        intros α β γ δ hγδ
        have h_mu : mu β γ δ = v β * rho γ δ := by
          have h_mu : u ⟨0, h_n⟩ * mu β γ δ = v β * nu ⟨0, h_n⟩ γ δ := by
            rw [ ← h_mode1 ⟨ 0, h_n ⟩ β γ δ ( by unfold not_constant_triple; aesop ), ← h_mode2 ⟨ 0, h_n ⟩ β γ δ ( by unfold not_constant_triple; aesop ) ]
          generalize_proofs at *; (
          grind)
        rw [h_mode1 α β γ δ (by
        exact fun h => hγδ <| by aesop;), h_mu]
        ring

/-
Step 2 of separable lambda: factor rho into w and x.
-/
lemma separable_lambda_step2 {n : ℕ}
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (u v w : Fin n → ℝ)
    (xi : Fin n → Fin n → Fin n → ℝ)
    (rho : Fin n → Fin n → ℝ)
    (h_n : n ≥ 5)
    (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0)
    (h_lam_supp : ∀ α β γ δ, not_all_identical α β γ δ ↔ lam α β γ δ ≠ 0)
    (h_rho : ∀ α β γ δ, γ ≠ δ → lam α β γ δ = u α * v β * rho γ δ)
    (h_mode3 : ∀ α β γ δ, not_constant_triple α β δ → lam α β γ δ = w γ * xi α β δ) :
    ∃ (x : Fin n → ℝ),
      (∀ δ, x δ ≠ 0) ∧
      ∀ γ δ, γ ≠ δ → rho γ δ = w γ * x δ := by
        -- Fix $\alpha_1 \neq \beta_1$ (exists since $n \ge 5$).
        obtain ⟨α1, β1, hαβ⟩ : ∃ α1 β1 : Fin n, α1 ≠ β1 := by
          exact ⟨ ⟨ 0, by linarith ⟩, ⟨ 1, by linarith ⟩, by norm_num ⟩;
        -- By definition of $x$, we have $x δ = xi α1 β1 δ / (u α1 * v β1)$.
        use fun δ => xi α1 β1 δ / (u α1 * v β1);
        constructor;
        · intro δ hδ; specialize h_lam_supp α1 β1 α1 δ; simp_all +decide [ not_all_identical ] ;
          specialize h_mode3 α1 β1 α1 δ ; simp_all +decide [ not_constant_triple ];
        · intro γ δ hγδ; specialize h_mode3 α1 β1 γ δ; specialize h_rho α1 β1 γ δ hγδ; simp_all +decide [ mul_assoc, mul_div_cancel₀ ] ;
          rw [ ← mul_div_assoc, eq_div_iff ( mul_ne_zero ( hu α1 ) ( hv β1 ) ) ] ; specialize h_mode3 ( by unfold not_constant_triple; aesop ) ; linarith;

/-
Step 3 of separable lambda: handle the case where the last two indices are equal.
-/
lemma separable_lambda_step3 {n : ℕ}
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (u v w x : Fin n → ℝ)
    (zeta : Fin n → Fin n → Fin n → ℝ)
    (h_n : n ≥ 5)
    (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0) (hx : ∀ i, x i ≠ 0)
    (h_lam_supp : ∀ α β γ δ, not_all_identical α β γ δ ↔ lam α β γ δ ≠ 0)
    (h_neq : ∀ α β γ δ, γ ≠ δ → lam α β γ δ = u α * v β * w γ * x δ)
    (h_mode4 : ∀ α β γ δ, not_constant_triple α β γ → lam α β γ δ = x δ * zeta α β γ) :
    ∀ α β σ, not_all_identical α β σ σ → lam α β σ σ = u α * v β * w σ * x σ := by
      intro α β σ h_not_all_identical
      obtain ⟨τ, hτ⟩ : ∃ τ, τ ≠ σ := by
        exact ⟨ if σ = ⟨ 0, by linarith ⟩ then ⟨ 1, by linarith ⟩ else ⟨ 0, by linarith ⟩, by aesop ⟩
      have h_eq : lam α β σ τ = u α * v β * w σ * x τ := by
        exact h_neq α β σ τ hτ.symm ▸ rfl
        skip
      have h_eq' : lam α β σ τ = x τ * zeta α β σ := by
        exact h_mode4 α β σ τ (by
        exact fun h => h_not_all_identical <| by aesop;)
      have h_eq'' : zeta α β σ = u α * v β * w σ := by
        exact mul_left_cancel₀ ( hx τ ) ( by linarith )
      have h_eq''' : lam α β σ σ = x σ * zeta α β σ := by
        convert h_mode4 α β σ σ _ using 1;
        exact fun h => h_not_all_identical <| by aesop;
      rw [h_eq''', h_eq'']
      ring

/-
Helper lemma: x' is proportional to x.
-/
lemma proportionality {n : ℕ}
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (u v w x x' : Fin n → ℝ)
    (zeta : Fin n → Fin n → Fin n → ℝ)
    (h_n : n ≥ 5)
    (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0) (hx : ∀ i, x i ≠ 0) (hx' : ∀ i, x' i ≠ 0)
    (h_neq : ∀ α β γ δ, γ ≠ δ → lam α β γ δ = u α * v β * w γ * x' δ)
    (h_mode4 : ∀ α β γ δ, not_constant_triple α β γ → lam α β γ δ = x δ * zeta α β γ) :
    ∃ c : ℝ, c ≠ 0 ∧ ∀ δ, x' δ = c * x δ := by
      -- Fix $\alpha=0, \beta=1$. Since $n \ge 5$, $\alpha \neq \beta$.
      obtain ⟨α, β, hαβ⟩ : ∃ α β : Fin n, α ≠ β := by
        exact ⟨ ⟨ 0, by linarith ⟩, ⟨ 1, by linarith ⟩, by norm_num ⟩
      generalize_proofs at *;
      -- Fix γ = 2. Then for any δ ≠ 2, we have x' δ / x δ = zeta α β 2 / (u α * v β * w 2).
      set c := zeta α β ⟨2, by linarith⟩ / (u α * v β * w ⟨2, by linarith⟩)
      have hc : ∀ δ, δ ≠ ⟨2, by linarith⟩ → x' δ = c * x δ := by
        intro δ hδ
        have h_eq : u α * v β * w ⟨2, by linarith⟩ * x' δ = x δ * zeta α β ⟨2, by linarith⟩ := by
          rw [ ← h_neq α β ⟨ 2, by linarith ⟩ δ ( by tauto ), h_mode4 α β ⟨ 2, by linarith ⟩ δ ( by tauto ) ]
        generalize_proofs at *;
        field_simp [h_eq] at *;
        generalize_proofs at *;
        (generalize_proofs at *; (
        grind););
      -- Fix γ = 3. Then for any δ ≠ 3, we have x' δ / x δ = zeta α β 3 / (u α * v β * w 3).
      set d := zeta α β ⟨3, by linarith⟩ / (u α * v β * w ⟨3, by linarith⟩)
      have hd : ∀ δ, δ ≠ ⟨3, by linarith⟩ → x' δ = d * x δ := by
        intro δ hδ_3
        have h_eq : u α * v β * w ⟨3, by linarith⟩ * x' δ = x δ * zeta α β ⟨3, by linarith⟩ := by
          rw [ ← h_neq α β ⟨ 3, by linarith ⟩ δ ( by tauto ), h_mode4 α β ⟨ 3, by linarith ⟩ δ ( by unfold not_constant_triple; aesop ) ]
        generalize_proofs at *; (
        rw [ div_mul_eq_mul_div, eq_div_iff ] <;> first | linarith | simp +decide [ * ] ;);
      -- Since $c = d$, we can conclude that $x' δ = c * x δ$ for all $δ$.
      have hcd : c = d := by
        specialize hc ⟨ 4, by linarith ⟩ ; specialize hd ⟨ 4, by linarith ⟩ ; aesop;
      refine' ⟨ c, _, _ ⟩ <;> simp_all +decide [ div_eq_iff ];
      · intro h; specialize hd ⟨ 2, by linarith ⟩ ; simp_all +decide ;
      · intro δ; by_cases hδ : δ = ⟨ 2, by linarith ⟩ <;> by_cases hδ' : δ = ⟨ 3, by linarith ⟩ <;> simp_all +decide ;

/-
Proposition 6.5: From mode-wise factorizations to a separable scaling.
-/
lemma separable_lambda {n : ℕ}
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (h_n : n ≥ 5)
    (h_lam_supp : ∀ α β γ δ, not_all_identical α β γ δ ↔ lam α β γ δ ≠ 0)
    (u v w x : Fin n → ℝ)
    (mu : Fin n → Fin n → Fin n → ℝ)
    (nu : Fin n → Fin n → Fin n → ℝ)
    (xi : Fin n → Fin n → Fin n → ℝ)
    (zeta : Fin n → Fin n → Fin n → ℝ)
    (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0) (hx : ∀ i, x i ≠ 0)
    (h_mode1 : ∀ α β γ δ, not_constant_triple β γ δ → lam α β γ δ = u α * mu β γ δ)
    (h_mode2 : ∀ α β γ δ, not_constant_triple α γ δ → lam α β γ δ = v β * nu α γ δ)
    (h_mode3 : ∀ α β γ δ, not_constant_triple α β δ → lam α β γ δ = w γ * xi α β δ)
    (h_mode4 : ∀ α β γ δ, not_constant_triple α β γ → lam α β γ δ = x δ * zeta α β γ) :
    separable_scaling lam := by
      -- By Lemma `separable_lambda_step1`, we can factor out u and v for gamma != delta.
      obtain ⟨rho, h_rho⟩ : ∃ (rho : Fin n → Fin n → ℝ), ∀ α β γ δ, γ ≠ δ → lam α β γ δ = u α * v β * rho γ δ := by
        -- Apply the lemma separable_lambda_step1 with the given hypotheses.
        apply separable_lambda_step1 lam u v mu nu (by linarith) hu hv h_mode1 h_mode2;
      -- By Lemma `separable_lambda_step2`, we can factor rho into w and x.
      obtain ⟨x', hx', h_lam_eq⟩ : ∃ (x' : Fin n → ℝ), (∀ δ, x' δ ≠ 0) ∧ ∀ α β γ δ, γ ≠ δ → lam α β γ δ = u α * v β * w γ * x' δ := by
        have := separable_lambda_step2 lam u v w xi rho h_n hu hv hw h_lam_supp h_rho h_mode3;
        exact ⟨ this.choose, this.choose_spec.1, fun α β γ δ h => by rw [ h_rho α β γ δ h, this.choose_spec.2 γ δ h ] ; ring ⟩;
      -- By Lemma `proportionality`, we can find a constant `c` such that `x' = c * x`.
      obtain ⟨c, hc⟩ : ∃ c : ℝ, c ≠ 0 ∧ ∀ δ, x' δ = c * x δ := by
        apply proportionality lam u v w x x' zeta h_n hu hv hw hx hx' h_lam_eq h_mode4;
      -- By Lemma `separable_lambda_step3`, we can handle the case where the last two indices are equal.
      have h_lam_eq_eq : ∀ α β σ, not_all_identical α β σ σ → lam α β σ σ = u α * v β * w σ * x' σ := by
        intros α β σ hσ
        apply separable_lambda_step3;
        grind;
        grind;
        exact hv;
        exact hw;
        exact hx';
        exact h_lam_supp;
        exact h_lam_eq;
        rotate_right;
        use fun α β γ => zeta α β γ / c;
        · grind;
        · exact hσ;
      refine' ⟨ u, v, w, fun δ => x' δ, _ ⟩;
      grind

/-
The diagonal blocks Q(alpha, alpha, alpha, alpha) are zero.
-/
lemma Q_block_diagonal_zero {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ) (α : Fin n) :
    Q_block A α α α α = fun _ => 0 := by
      funext idx;
      -- By definition of $idx$, we know that $idx 0 = idx 1$ or $idx 0 = idx 2$ or $idx 0 = idx 3$ or $idx 1 = idx 2$ or $idx 1 = idx 3$ or $idx 2 = idx 3$.
      obtain ⟨i, j, hij, h_eq⟩ : ∃ i j : Fin 4, i ≠ j ∧ idx i = idx j := by
        native_decide +revert;
      convert Matrix.det_zero_of_row_eq hij _ ; aesop

/-
The diagonal blocks Q(alpha, alpha, alpha, alpha) are zero.
-/
lemma Q_block_diagonal_zero_v2 {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ) (α : Fin n) :
    Q_block A α α α α = fun _ => 0 := by
      -- Since the rows of A α are identical, any four rows chosen will have at least one duplicate, making the determinant zero.
      apply Q_block_diagonal_zero A α

/-
The diagonal blocks Q(alpha, alpha, alpha, alpha) are zero.
-/
lemma Q_block_diagonal_zero_v3 {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ) (α : Fin n) :
    Q_block A α α α α = fun _ => 0 := by
      -- Apply the lemma that states Q_block A α α α α is the zero tensor.
      apply Q_block_diagonal_zero_v2

/-
If rank is at most 4, then all 5x5 minors are zero.
-/
lemma rank_le_four_imp_minors_zero {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (M : Matrix m n ℝ)
    (h : M.rank ≤ 4) :
    ∀ (r : Fin 5 → m) (c : Fin 5 → n), (M.submatrix r c).det = 0 := by
      intro r c;
      by_contra h_det_nonzero;
      have h_rank_le : Matrix.rank (Matrix.submatrix M r c) ≤ 4 := by
        refine' le_trans _ h;
        have h_submatrix_rank : Matrix.rank (Matrix.submatrix M r c) ≤ Matrix.rank M := by
          have h_submatrix : ∃ (R : Matrix (Fin 5) m ℝ) (C : Matrix n (Fin 5) ℝ), Matrix.submatrix M r c = R * M * C := by
            use Matrix.of (fun i j => if j = r i then 1 else 0), Matrix.of (fun i j => if i = c j then 1 else 0);
            ext i j; simp +decide [ Matrix.mul_apply ] ;
          obtain ⟨ R, C, hR ⟩ := h_submatrix; rw [ hR ] ; exact le_trans ( Matrix.rank_mul_le_left _ _ ) ( Matrix.rank_mul_le_right _ _ ) ;
        exact h_submatrix_rank;
      have := Matrix.rank_mul_le_left ( Matrix.submatrix M r c ) ( Matrix.submatrix M r c ) ⁻¹; simp_all +decide [ isUnit_iff_ne_zero ] ;
      linarith

/-
If rank is at least 5, there exists a non-zero 5x5 minor.
-/
lemma rank_ge_five_imp_exists_minor {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (M : Matrix m n ℝ)
    (h : M.rank ≥ 5) :
    ∃ (r : Fin 5 → m) (c : Fin 5 → n), (M.submatrix r c).det ≠ 0 := by
      -- Since $\rank(M) \ge 5$, there exists a subset of 5 linearly independent columns of $M$.
      obtain ⟨c, hc⟩ : ∃ (c : Fin 5 → n), LinearIndependent ℝ (fun i => (M.col (c i))) := by
        have := ( exists_linearIndependent ℝ ( Set.range ( Matrix.col M ) ) );
        obtain ⟨ b, hb₁, hb₂, hb₃ ⟩ := this;
        have h_card : Cardinal.mk b ≥ 5 := by
          have h_card : Module.finrank ℝ (Submodule.span ℝ b) ≥ 5 := by
            rw [ hb₂ ];
            convert h using 1;
            exact Eq.symm (rank_eq_finrank_span_cols M);
          have h_card : Module.finrank ℝ (Submodule.span ℝ b) ≤ Cardinal.mk b := by
            simp_all +decide [ Cardinal.lift_le ];
            rw [ rank_span_set ] ; aesop;
          exact le_trans ( mod_cast by assumption ) h_card;
        have h_card : ∃ c : Fin 5 → (m → ℝ), Function.Injective c ∧ ∀ i, c i ∈ b := by
          have := Cardinal.le_mk_iff_exists_subset.mp h_card;
          obtain ⟨ p, hp₁, hp₂ ⟩ := this;
          have := Cardinal.eq.1 hp₂;
          obtain ⟨ e ⟩ := this;
          exact ⟨ fun i => e.symm ( ULift.up i ) |>.1, fun i j hij => by simpa using e.symm.injective <| Subtype.ext hij, fun i => hp₁ <| e.symm ( ULift.up i ) |>.2 ⟩;
        obtain ⟨ c, hc₁, hc₂ ⟩ := h_card;
        choose f hf using fun i => hb₁ ( hc₂ i );
        refine' ⟨ f, _ ⟩;
        convert hb₃.comp _ _;
        rotate_left;
        exacts [ fun i => ⟨ c i, hc₂ i ⟩, fun i j hij => hc₁ <| by simpa using hij, by simp +decide [ hf ] ];
      -- The submatrix $M'$ formed by these columns has rank 5.
      have hM'_rank : (Matrix.transpose (Matrix.submatrix M (fun x => x) c)).rank = 5 := by
        convert finrank_span_eq_card hc using 1;
        convert Matrix.rank_transpose _;
        rw [ Matrix.rank ];
        rw [ show LinearMap.range ( Matrix.mulVecLin ( Matrix.submatrix M ( fun x => x ) c ) ) = Submodule.span ℝ ( Set.range fun i => M.col ( c i ) ) from ?_ ];
        ext; simp [Matrix.mulVecLin];
        simp +decide [ funext_iff, Matrix.mulVec, Submodule.mem_span_range_iff_exists_fun ];
        simp +decide only [dotProduct, mul_comm];
      -- Since row rank equals column rank, $M'$ has 5 linearly independent rows. Let their indices be given by $r: \text{Fin } 5 \to m$.
      obtain ⟨r, hr⟩ : ∃ r : Fin 5 → m, LinearIndependent ℝ (fun i => (Matrix.submatrix M (fun x => x) c).row (r i)) := by
        have hM'_rows : ∃ (r : Fin 5 → m), LinearIndependent ℝ (fun i => (Matrix.submatrix M (fun x => x) c).row (r i)) := by
          have hM'_rows : Module.finrank ℝ (Submodule.span ℝ (Set.range (Matrix.row (Matrix.submatrix M (fun x => x) c)))) = 5 := by
            convert hM'_rank using 1;
            rw [ Matrix.rank ];
            rw [ show LinearMap.range ( Matrix.mulVecLin ( Matrix.transpose ( Matrix.submatrix M ( fun x => x ) c ) ) ) = Submodule.span ℝ ( Set.range ( Matrix.row ( Matrix.submatrix M ( fun x => x ) c ) ) ) from ?_ ];
            ext; simp [Matrix.mulVecLin];
            simp +decide [ funext_iff, Matrix.mulVec, dotProduct, Submodule.mem_span_range_iff_exists_fun ];
            simp +decide only [mul_comm]
          have := ( exists_linearIndependent ℝ ( Set.range ( Matrix.row ( Matrix.submatrix M ( fun x => x ) c ) ) ) );
          obtain ⟨ b, hb₁, hb₂, hb₃ ⟩ := this;
          have h_card : b.Finite := by
            exact Set.Finite.subset ( Set.toFinite ( Set.range ( Matrix.row ( Matrix.submatrix M ( fun x => x ) c ) ) ) ) hb₁;
          have := h_card.fintype;
          have h_card : Fintype.card b = 5 := by
            have h_card : Module.finrank ℝ (Submodule.span ℝ b) = 5 := by
              rw [ hb₂, hM'_rows ];
            rw [ finrank_span_set_eq_card ] at h_card <;> aesop;
          have h_card : Nonempty (Fin 5 ≃ b) := by
            exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ h_card ] ⟩;
          obtain ⟨ r ⟩ := h_card;
          have h_card : LinearIndependent ℝ (fun i => (r i : Fin 5 → ℝ)) := by
            convert hb₃.comp _ _;
            exact r.injective;
          choose f hf using fun i => hb₁ ( r i |>.2 );
          exact ⟨ f, by simpa only [ hf ] using h_card ⟩;
        exact hM'_rows;
      -- The $5 \times 5$ submatrix formed by $r$ and $c$ has rank 5, so its determinant is non-zero.
      use r, c;
      rw [ Fintype.linearIndependent_iff ] at hr;
      contrapose! hr;
      obtain ⟨ g, hg ⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hr;
      exact ⟨ g, by simpa [ funext_iff, Matrix.vecMul, dotProduct, mul_comm ] using hg.2, Function.ne_iff.mp hg.1 ⟩

/-
A matrix has rank at most 4 if and only if all 5x5 minors vanish.
-/
lemma matrix_rank_le_four_iff {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (M : Matrix m n ℝ) :
    M.rank ≤ 4 ↔ ∀ (r : Fin 5 → m) (c : Fin 5 → n), (M.submatrix r c).det = 0 := by
      refine' ⟨ fun h r c => _, fun h => _ ⟩;
      · exact rank_le_four_imp_minors_zero M h r c;
      · contrapose! h with h_pos;
        obtain ⟨ r, c, hrc ⟩ := rank_ge_five_imp_exists_minor M h_pos;
        exact ⟨ r, c, hrc ⟩

/-
Condition (6.1) on lambda: lambda is non-zero if and only if indices are not all identical.
-/
def valid_lambda {n : ℕ} (lam : Fin n → Fin n → Fin n → Fin n → ℝ) : Prop :=
  ∀ α β γ δ, not_all_identical α β γ δ ↔ lam α β γ δ ≠ 0

/-
The equivalence statement of the main theorem: F_n vanishes iff lambda is separable.
-/
def main_theorem_equivalence {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ) : Prop :=
  ∀ lam : Fin n → Fin n → Fin n → Fin n → ℝ,
    valid_lambda lam →
    ((∀ idx : MinorIndices n, mathbf_F_n (block_scaling lam (fun α β γ δ => Q_block A α β γ δ)) idx = 0) ↔
     separable_scaling lam)

/-
Definition of GoodA: A satisfies all the rank conditions required for the theorem.
-/
def GoodA {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ) : Prop :=
  (StackedMatrix A).rank = 4 ∧
  (∀ α, (A α).rank = 3) ∧
  (∀ β γ δ, not_constant_triple β γ δ → (P_matrix A β γ δ).rank = 4)

/-
If lambda agrees with a separable scaling on non-diagonal blocks, the assembled tensors are equal (since diagonal blocks are zero).
-/
lemma separable_congr {n : ℕ} (A : Fin n → Matrix (Fin 3) (Fin 4) ℝ)
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (u v w x : Fin n → ℝ)
    (h_sep : ∀ α β γ δ, not_all_identical α β γ δ → lam α β γ δ = u α * v β * w γ * x δ) :
    Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ)) =
    Asm (block_scaling (fun α β γ δ => u α * v β * w γ * x δ) (fun α β γ δ => Q_block A α β γ δ)) := by
      have h_diag_zero : ∀ α β γ δ, α = β ∧ β = γ ∧ γ = δ → Q_block A α β γ δ = fun _ => 0 := by
        -- Apply the lemma that states Q_block A α α α α is zero.
        intros α β γ δ h_eq
        have h_diag : Q_block A α α α α = fun _ => 0 := by
          exact Q_block_diagonal_zero_v3 A α
        aesop;
      unfold not_all_identical at *;
      ext i j k l;
      unfold Asm block_scaling; simp +decide [ h_sep, h_diag_zero ] ;
      by_cases h : inv_iota_alpha ( i 0 ) = inv_iota_alpha ( i 1 ) ∧ inv_iota_alpha ( i 1 ) = inv_iota_alpha ( i 2 ) ∧ inv_iota_alpha ( i 2 ) = inv_iota_alpha ( i 3 ) <;> simp_all +decide [ funext_iff ]

/-- Convenience alias for the ambient camera-parameter type used throughout. -/
abbrev CamTuple (n : ℕ) := Fin n → Matrix (Fin 3) (Fin 4) ℝ

/-- Convenience alias for the big tensor shape `I_3n n`. -/
abbrev BigI (n : ℕ) : Fin 4 → ℕ := fun _ => 3 * n

/-- Convenience alias for a `4`-mode tensor of shape `(3n,3n,3n,3n)` in your encoding. -/
abbrev BigTensor (n : ℕ) := Tensor (BigI n)

/-- Convenience alias for a block tensor family of `3×3×3×3` tensors. -/
abbrev BlockFam (n : ℕ) := Fin n → Fin n → Fin n → Fin n → Tensor (fun _ : Fin 4 => 3)

/-! --------------------------------------------------------------------------
  1) Indexing lemmas for `iota`, `inv_iota_alpha`, `inv_iota_i`.
---------------------------------------------------------------------------- -/

section Iota

variable {n : ℕ}

lemma inv_iota_alpha_iota (α : Fin n) (i : Fin 3) :
    inv_iota_alpha (n := n) (iota (n := n) α i) = α := by
  -- By definition of `iota` and `inv_iota_alpha`, we have `iota α i = (α, i)` and `inv_iota_alpha (α, i) = α`.
  simp [iota, inv_iota_alpha];
  -- Since $i$ is a `Fin 3`, its value is between 0 and 2. Therefore, $3 * \alpha + i$ divided by 3 is just $\alpha$.
  have h_div : (3 * α.val + i.val) / 3 = α.val := by
    grind;
  -- Since the first component of the pair is equal to α.val and the second component is i.val, which is irrelevant for the equality of Fin elements, we can conclude that the pairs are equal.
  ext; simp [h_div]

lemma inv_iota_i_iota (α : Fin n) (i : Fin 3) :
    inv_iota_i (n := n) (iota (n := n) α i) = i := by
  -- By definition of `iota` and `inv_iota_i`, we know that `inv_iota_i (iota α i) = (α, i)` and `concat (inv_iota_i (iota α i)) = iota α i`. Therefore, `inv_iota_i (iota α i) = i`.
  simp [iota, inv_iota_i];
  -- Since $i$ is a `Fin 3`, its value is between 0 and 2. The modulo operation here is just taking the remainder when divided by 3, which for numbers 0, 1, 2 is just the number itself. So, $(i : ℕ) % 3$ is equal to $i$.
  ext; simp [Fin.ext_iff]

lemma iota_inv (x : Fin (3 * n)) :
    iota (n := n) (inv_iota_alpha (n := n) x) (inv_iota_i (n := n) x) = x := by
  -- By definition of `iota` and `inv_iota_alpha`, we have `iota (inv_iota_alpha x) (inv_iota_i x) = x`.
  simp [iota, inv_iota_alpha, inv_iota_i];
  -- By the division algorithm, we know that $x.val = 3 * (x.val / 3) + (x.val % 3)$.
  have h_div_alg : x.val = 3 * (x.val / 3) + (x.val % 3) := by
    -- By the division algorithm, we know that $x = 3 * (x / 3) + (x % 3)$ for any natural number $x$.
    apply Eq.symm; exact Nat.div_add_mod x 3
  generalize_proofs at *;
  exact Fin.ext (by linarith)

lemma iota_injective (α β : Fin n) (i j : Fin 3) :
    iota (n := n) α i = iota (n := n) β j ↔ α = β ∧ i = j := by
  -- By definition of `iota`, we know that `iota α i = alpha * 3 + i` and `iota β j = beta * 3 + j`.
  simp [iota];
  grind

lemma inv_iota_alpha_eq_iff {x y : Fin (3 * n)} :
    inv_iota_alpha (n := n) x = inv_iota_alpha (n := n) y ↔ x.val / 3 = y.val / 3 := by
  -- By definition of `inv_iota_alpha`, we know that `inv_iota_alpha x = x / 3`.
  simp [inv_iota_alpha]

lemma inv_iota_i_eq_iff {x y : Fin (3 * n)} :
    inv_iota_i (n := n) x = inv_iota_i (n := n) y ↔ x.val % 3 = y.val % 3 := by
  -- By definition of `inv_iota_i`, we know that `inv_iota_i x = x % 3`.
  simp [inv_iota_i]

end Iota

/-! --------------------------------------------------------------------------
  2) Assembly lemmas for `Asm` and interaction with `block_scaling`.
---------------------------------------------------------------------------- -/

section AsmLemmas

variable {n : ℕ}

-- Useful explicit “index constructors” for readability
def idx4 (α β γ δ : Fin n) (i j k ℓ : Fin 3) : Fin 4 → Fin (3 * n)
  | 0 => iota (n := n) α i
  | 1 => iota (n := n) β j
  | 2 => iota (n := n) γ k
  | 3 => iota (n := n) δ ℓ

def inner4 (i j k ℓ : Fin 3) : Fin 4 → Fin 3
  | 0 => i
  | 1 => j
  | 2 => k
  | 3 => ℓ

lemma Asm_apply_iota (T : BlockFam n) (α β γ δ : Fin n) (i j k ℓ : Fin 3) :
    Asm (n := n) T (idx4 (n := n) α β γ δ i j k ℓ)
      = T α β γ δ (inner4 i j k ℓ) := by
  -- By definition of `Asm`, we know that `Asm T (idx4 α β γ δ i j k ℓ)` is equal to `T α β γ δ (inner4 i j k ℓ)` because `idx4` and `inner4` are inverses in the sense that they provide the necessary components to apply `T`.
  simp [Asm, idx4, inner4];
  congr! 1;
  · exact inv_iota_alpha_iota α i;
  · exact inv_iota_alpha_iota β j;
  · exact inv_iota_alpha_iota γ k;
  · exact inv_iota_alpha_iota δ ℓ;
  · -- By definition of `inv_iota_i` and `iota`, we can simplify each component of the function.
    funext k; fin_cases k <;> simp [inv_iota_i, iota];
    · fin_cases i <;> rfl;
    · exact Fin.ext ( Nat.mod_eq_of_lt ( Fin.is_lt j ) );
    · fin_cases k <;> rfl;
    · fin_cases ℓ <;> rfl

lemma Asm_block_scaling_apply
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ) (T : BlockFam n) (idx : Fin 4 → Fin (3 * n)) :
    Asm (n := n) (block_scaling (n := n) lam T) idx
      =
    (lam (inv_iota_alpha (n := n) (idx 0))
         (inv_iota_alpha (n := n) (idx 1))
         (inv_iota_alpha (n := n) (idx 2))
         (inv_iota_alpha (n := n) (idx 3)))
      * Asm (n := n) T idx := by
  -- By definition of Asm and block_scaling, we can expand the expression for the scaled tensor and show that it equals the original tensor scaled by the lambda values. Specifically, we have:
  simp [Asm, block_scaling]

lemma Asm_block_scaling_apply_iota
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ) (T : BlockFam n)
    (α β γ δ : Fin n) (i j k ℓ : Fin 3) :
    Asm (n := n) (block_scaling (n := n) lam T) (idx4 (n := n) α β γ δ i j k ℓ)
      =
    lam α β γ δ * T α β γ δ (inner4 i j k ℓ) := by
  exact Asm_apply_iota (block_scaling lam T) α β γ δ i j k ℓ

lemma Asm_ext_blocks
    (T₁ T₂ : BlockFam n)
    (h : ∀ α β γ δ (idx : Fin 4 → Fin 3), T₁ α β γ δ idx = T₂ α β γ δ idx) :
    Asm (n := n) T₁ = Asm (n := n) T₂ := by
  -- Since T₁ and T₂ are equal in their block scaling, for every index, the assembled tensors will have the same value.
  funext x; simp [Asm, h]

end AsmLemmas

/-! --------------------------------------------------------------------------
  3) Tensor/minor correctness: “all 5×5 minors vanish” ↔ “rank ≤ 4”.
---------------------------------------------------------------------------- -/

section MinorRank

variable {n : ℕ}

-- Matrix-level packaging (you already have stubs for some of these)
lemma matrix_rank_le_four_iff_all_5x5_minors
    {m p : Type*} [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p]
    (M : Matrix m p ℝ) :
    M.rank ≤ 4 ↔ ∀ (r : Fin 5 → m) (c : Fin 5 → p), (M.submatrix r c).det = 0 := by
  convert matrix_rank_le_four_iff M using 1

-- Key missing tensor-level equivalence for your `F_n`
noncomputable section AristotleLemmas

lemma minor_eq_zero_of_F_n_zero {n : ℕ} (T : Tensor (I_3n n))
    (h : ∀ idx : MinorIndices n, F_n T idx = 0)
    (t : Fin 4)
    (r : Fin 5 → Fin (3 * n))
    (c : Fin 5 → Lex ({k // k ≠ t} → Fin (3 * n))) :
    (Matrix.submatrix (unfolding (I_3n n) t T) r c).det = 0 := by
      by_cases hr : Function.Injective r <;> by_cases hc : Function.Injective c <;> simp_all +decide [ Matrix.det_zero_of_row_eq ];
      · -- Let `rows` be the image of `r` and `cols` be the image of `c`. Since `r, c` are injective from `Fin 5`, `rows` and `cols` have cardinality 5.
        set rows : Finset (Fin (3 * n)) := Finset.image r Finset.univ
        set cols : Finset (Lex ({ k : Fin 4 // k ≠ t } → Fin (3 * n))) := Finset.image c Finset.univ
        have h_rows_card : rows.card = 5 := by
          rw [ Finset.card_image_of_injective _ hr, Finset.card_fin ]
        have h_cols_card : cols.card = 5 := by
          rw [ Finset.card_image_of_injective _ hc, Finset.card_fin ];
        -- By assumption `h`, `F_n T (⟨t, rows, cols, h_rows_card, h_cols_card⟩) = 0`.
        have h_det_zero : Matrix.det (Matrix.submatrix (unfolding (I_3n n) t T) (rows.orderEmbOfFin h_rows_card) (cols.orderEmbOfFin h_cols_card)) = 0 := by
          convert h ⟨ t, rows, cols, h_rows_card, h_cols_card ⟩ using 1;
        -- The matrix `submatrix ... r c` is obtained from `submatrix ... (sorted rows) (sorted cols)` by permuting rows and columns.
        have h_perm : ∃ (σ : Equiv.Perm (Fin 5)) (τ : Equiv.Perm (Fin 5)), Matrix.submatrix (unfolding (I_3n n) t T) r c = Matrix.submatrix (Matrix.submatrix (unfolding (I_3n n) t T) (rows.orderEmbOfFin h_rows_card) (cols.orderEmbOfFin h_cols_card)) (fun i => σ i) (fun i => τ i) := by
          have h_perm : ∃ (σ : Equiv.Perm (Fin 5)), ∀ i, r i = rows.orderEmbOfFin h_rows_card (σ i) := by
            have h_perm : ∀ i, ∃ j : Fin 5, r i = rows.orderEmbOfFin h_rows_card j := by
              intro i
              have h_mem : r i ∈ rows := by
                exact Finset.mem_image_of_mem _ ( Finset.mem_univ _ );
              have h_perm : Finset.image (fun j => rows.orderEmbOfFin h_rows_card j) (Finset.univ : Finset (Fin 5)) = rows := by
                exact Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun j _ => Finset.orderEmbOfFin_mem _ _ _ ) ( by simp +decide [ Finset.card_image_of_injective _ ( show Function.Injective ( fun j => rows.orderEmbOfFin h_rows_card j ) from fun i j hij => by simpa [ Fin.ext_iff ] using hij ), h_rows_card ] );
              exact Exists.elim ( Finset.mem_image.mp ( h_perm.symm ▸ h_mem ) ) fun j hj => ⟨ j, hj.2.symm ⟩;
            choose σ hσ using h_perm;
            exact ⟨ Equiv.ofBijective σ ( Finite.injective_iff_bijective.mp ( fun i j hij => by have := hr ( by rw [ hσ i, hσ j, hij ] : r i = r j ) ; aesop ) ), hσ ⟩
          have h_perm' : ∃ (τ : Equiv.Perm (Fin 5)), ∀ i, c i = cols.orderEmbOfFin h_cols_card (τ i) := by
            have h_perm' : ∀ i, ∃ j, c i = cols.orderEmbOfFin h_cols_card j := by
              intro i
              have h_mem : c i ∈ cols := by
                exact Finset.mem_image_of_mem _ ( Finset.mem_univ _ );
              have h_perm' : ∀ x ∈ cols, ∃ j : Fin 5, x = cols.orderEmbOfFin h_cols_card j := by
                intro x hx
                have h_mem : x ∈ cols := hx
                have h_perm' : ∃ j : Fin 5, x = cols.orderEmbOfFin h_cols_card j := by
                  have h_image : cols = Finset.image (fun j => cols.orderEmbOfFin h_cols_card j) Finset.univ := by
                    exact Eq.symm ( Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => Finset.orderEmbOfFin_mem _ _ _ ) ( by simp +decide [ Finset.card_image_of_injective _ ( show Function.Injective ( fun j : Fin 5 => cols.orderEmbOfFin h_cols_card j ) from fun i j hij => by simpa [ Fin.ext_iff ] using hij ), h_cols_card ] ) )
                  rw [h_image] at h_mem; exact Finset.mem_image.mp h_mem |> fun ⟨j, _, hj⟩ => ⟨j, hj.symm⟩;
                exact h_perm';
              exact h_perm' _ h_mem;
            choose τ hτ using h_perm';
            exact ⟨ Equiv.ofBijective τ ( Finite.injective_iff_bijective.mp ( fun i j hij => by have := hc ( by aesop : c i = c j ) ; aesop ) ), hτ ⟩
          obtain ⟨σ, hσ⟩ := h_perm
          obtain ⟨τ, hτ⟩ := h_perm';
          exact ⟨ σ, τ, by ext i j; simp +decide [ hσ, hτ ] ⟩;
        obtain ⟨ σ, τ, h ⟩ := h_perm;
        -- Apply the fact that the determinant is invariant under permutation of rows and columns.
        have h_det_perm : Matrix.det (Matrix.submatrix (Matrix.submatrix (unfolding (I_3n n) t T) (rows.orderEmbOfFin h_rows_card) (cols.orderEmbOfFin h_cols_card)) (fun i => σ i) (fun i => τ i)) = σ.sign * τ.sign * Matrix.det (Matrix.submatrix (unfolding (I_3n n) t T) (rows.orderEmbOfFin h_rows_card) (cols.orderEmbOfFin h_cols_card)) := by
          have h_det_perm : ∀ (M : Matrix (Fin 5) (Fin 5) ℝ) (σ τ : Equiv.Perm (Fin 5)), Matrix.det (Matrix.submatrix M (fun i => σ i) (fun i => τ i)) = σ.sign * τ.sign * Matrix.det M := by
            intro M σ τ; rw [ Matrix.det_apply', Matrix.det_apply' ] ; simp +decide [ Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const, Finset.card_univ ] ;
            rw [ Finset.mul_sum _ _ _ ];
            refine' Finset.sum_bij ( fun x _ => σ * x * τ⁻¹ ) _ _ _ _ <;> simp +decide [ mul_assoc, Equiv.Perm.sign_mul ];
            · exact fun b => ⟨ σ⁻¹ * b * τ, by group ⟩;
            · intro a; rw [ ← Equiv.prod_comp ( τ⁻¹ ) ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
              cases' Int.units_eq_one_or ( Equiv.Perm.sign σ ) with h h <;> cases' Int.units_eq_one_or ( Equiv.Perm.sign τ ) with j j <;> simp +decide [ h, j ];
          convert h_det_perm _ σ τ using 1;
        aesop;
      · -- Since $c$ is not injective, there exist $i \ne j$ such that $c i = c j$.
        obtain ⟨i, j, hij, hc_eq⟩ : ∃ i j : Fin 5, i ≠ j ∧ c i = c j := by
          simpa [ Function.Injective, and_comm ] using hc;
        rw [ Matrix.det_zero_of_column_eq hij ] ; aesop
        skip;
      · -- Since $r$ is not injective, there exist $i \ne j$ such that $r i = r j$.
        obtain ⟨i, j, hij, hr_eq⟩ : ∃ i j : Fin 5, i ≠ j ∧ r i = r j := by
          simpa [ Function.Injective, and_comm ] using hr;
        rw [ Matrix.det_zero_of_row_eq hij ] ; aesop;
      · -- Since $r$ is not injective, there exist $i \ne j$ such that $r i = r j$.
        obtain ⟨i, j, hij, h_eq⟩ : ∃ i j : Fin 5, i ≠ j ∧ r i = r j := by
          simpa [ Function.Injective, and_comm ] using hr;
        exact Matrix.det_zero_of_row_eq hij ( by aesop )

end AristotleLemmas

theorem rank_le_four_iff_F_n_zero (T : BigTensor n) :
    rank_le_four (n := n) T ↔ ∀ idx : MinorIndices n, F_n (n := n) T idx = 0 := by
  constructor;
  · exact fun a idx ↦ rank_le_four_implies_F_n_zero T a idx;
  · intro hF_n_zero t
    have h_rank_le_four : (unfolding (I_3n n) t T).rank ≤ 4 := by
      apply (matrix_rank_le_four_iff (unfolding (I_3n n) t T)).mpr;
      convert minor_eq_zero_of_F_n_zero T hF_n_zero t using 1
    exact h_rank_le_four

-- Immediate corollary for `mathbf_F_n`
theorem rank_le_four_iff_mathbf_F_n_zero (T_fam : BlockFam n) :
    rank_le_four (n := n) (Asm (n := n) T_fam) ↔
      ∀ idx : MinorIndices n, mathbf_F_n (n := n) T_fam idx = 0 := by
  convert rank_le_four_iff_F_n_zero ( Asm T_fam ) using 1

-- Often useful: one direction explicitly
theorem mathbf_F_n_zero_implies_rank_le_four (T_fam : BlockFam n)
    (h : ∀ idx : MinorIndices n, mathbf_F_n (n := n) T_fam idx = 0) :
    rank_le_four (n := n) (Asm (n := n) T_fam) := by
  convert rank_le_four_iff_mathbf_F_n_zero T_fam |>.2 h

theorem rank_le_four_implies_mathbf_F_n_zero (T_fam : BlockFam n)
    (h : rank_le_four (n := n) (Asm (n := n) T_fam)) :
    ∀ idx : MinorIndices n, mathbf_F_n (n := n) T_fam idx = 0 := by
  -- Apply the theorem that states the equivalence between the rank condition and the vanishing of all 5x5 minors.
  apply (rank_le_four_iff_F_n_zero (Asm T_fam)).mp h

end MinorRank

/-! --------------------------------------------------------------------------
  4) Basic logical lemmas about `not_all_identical` / `not_constant_triple`.
---------------------------------------------------------------------------- -/

section NotIdentical

variable {n : ℕ}

lemma not_constant_triple_of_not_all_identical_left
    {α β γ δ : Fin n} (h : not_all_identical α β γ δ) :
    not_constant_triple β γ δ ∨ not_constant_triple α γ δ ∨ not_constant_triple α β δ ∨ not_constant_triple α β γ := by
  -- If not_all_identical α β γ δ, then at least one of the triples β γ δ, α γ δ, α β δ, or α β γ is not_constant_triple.
  have h_triple : ¬(α = β ∧ β = γ ∧ γ = δ) → ¬(β = γ ∧ γ = δ) ∨ ¬(α = γ ∧ γ = δ) ∨ ¬(α = β ∧ β = δ) ∨ ¬(α = β ∧ β = γ) := by
    -- By definition of not_all_identical, there exist three indices i, j, k such that idx i ≠ idx j.
    intro h_not_all_identical
    by_contra h_contra
    push_neg at h_contra;
    -- By combining the equalities from h_contra, we can derive that α = β = γ = δ, which contradicts h_not_all_identical.
    obtain ⟨hβγ, hαγ, hαβ, hαβγ⟩ := h_contra;
    aesop;
  -- Apply the hypothesis `h_triple` to the negation of the equality of all four elements.
  apply h_triple h

lemma not_constant_triple_implies_not_all_identical
    (α β γ δ : Fin n) (h : not_constant_triple β γ δ) :
    not_all_identical α β γ δ := by
  -- If β, γ, δ are not all identical, then there must be at least two of them that are different. Therefore, α, β, γ, δ can't all be the same because β and γ are different.
  by_contra h_contra
  have h_eq : α = β ∧ β = γ ∧ γ = δ := by
    -- By definition of `not_all_identical`, if `not_all_identical α β γ δ` is false, then `α`, `β`, `γ`, and `δ` must all be equal.
    simp [not_all_identical] at h_contra
    exact h_contra;
  -- If β = γ and γ = δ, then β, γ, δ are all identical, which contradicts the assumption that not_constant_triple β γ δ holds.
  simp [h_eq, not_constant_triple] at h

lemma valid_lambda_nonzero_of_not_constant_triple
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (h_lam : valid_lambda lam)
    (α β γ δ : Fin n) (h : not_constant_triple β γ δ) :
    lam α β γ δ ≠ 0 := by
  -- By definition of `valid_lambda`, if `not_constant_triple β γ δ` holds, then `lam α β γ δ` must be non-zero.
  apply (h_lam α β γ δ).mp; exact not_constant_triple_implies_not_all_identical α β γ δ h

end NotIdentical

/-! --------------------------------------------------------------------------
  5) Scaling matrices: invertibility, isUnit, and rank monotonicity.
---------------------------------------------------------------------------- -/

section Scaling

variable {n : ℕ}

lemma scaling_matrix_diagonal (u : Fin n → ℝ) (i : Fin (3 * n)) :
    scaling_matrix (n := n) u i i = u (inv_iota_alpha (n := n) i) := by
  -- By definition of `scaling_matrix`, we know that the diagonal entries are exactly the values of `u`s. Therefore, we can simplify the expression.
  simp [scaling_matrix]

lemma scaling_matrix_offdiag (u : Fin n → ℝ) (i j : Fin (3 * n)) (h : i ≠ j) :
    scaling_matrix (n := n) u i j = 0 := by
  -- By definition of scaling matrix, if i ≠ j, then scaling_matrix u i j = 0.
  simp [scaling_matrix, h]

lemma scaling_matrix_isUnit (u : Fin n → ℝ) (hu : ∀ α, u α ≠ 0) :
    IsUnit (scaling_matrix (n := n) u) := by
  -- Since the scaling matrix is diagonal with non-zero entries, its determinant is the product of its diagonal entries, which are all non-zero.
  have h_det : Matrix.det (scaling_matrix (n := n) u) ≠ 0 := by
    erw [ Matrix.det_of_upperTriangular ];
    · exact Finset.prod_ne_zero_iff.mpr fun i _ => by unfold scaling_matrix; aesop;
    · -- Since the scaling matrix is diagonal, it is block triangular with respect to the identity function.
      intros i j hij
      simp [scaling_matrix, hij];
      exact if_neg ( ne_of_gt hij );
  exact Matrix.isUnit_iff_isUnit_det _ |>.2 <| isUnit_iff_ne_zero.2 h_det

lemma rank_mul_left_le (A : Matrix (Fin (3 * n)) (Fin (3 * n)) ℝ)
    (B : Matrix (Fin (3 * n)) (Fin 4) ℝ) :
    (A * B).rank ≤ B.rank := by
  -- The rank of a product of matrices is less than or equal to the minimum of the ranks of the individual matrices. This follows from the fact that the image of the product is contained in the image of the second matrix.
  apply Matrix.rank_mul_le_right

lemma rank_mul_right_le {m p q : Type*} [Fintype m] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq p] [DecidableEq q]
    (A : Matrix m p ℝ) (B : Matrix p q ℝ) :
    (A * B).rank ≤ A.rank := by
  -- The rank of the product of two matrices is less than or equal to the rank of the first matrix by the properties of linear maps.
  apply Matrix.rank_mul_le_left

end Scaling

/-! --------------------------------------------------------------------------
  6) Q-block and assembly facts.
---------------------------------------------------------------------------- -/

section QFacts

variable {n : ℕ}

lemma Q_block_diagonal_zero' (A : CamTuple n) (α : Fin n) :
    Q_block A α α α α = fun _ => 0 := by
  -- By definition of $Q_block$, we know that $Q_block A α α α α$ is the zero matrix because all the determinants are zero.
  apply Q_block_diagonal_zero_v3

-- Optional: explicit Tucker/LeviCivita factorization statement (if you want it)
-- (May require additional definitions of mode products for tensors of varying shape.)
theorem Asm_Q_eq_LeviCivita_modeProducts
    (A : CamTuple n) :
    True := by
  -- Placeholder: replace `True` by your intended formal statement relating `Asm Q` to LeviCivita ×_t C.
  -- The goal is trivially true since True is always true.
  apply trivial

end QFacts

/-! --------------------------------------------------------------------------
  7) Rank monotonicity for mode products (needed for the ⇒ direction).
---------------------------------------------------------------------------- -/

section ModeProductRank

variable {n : ℕ}

-- A general “mode-product does not increase ranks of unfoldings” statement.
-- Replace by the exact statement you decide to use.
noncomputable section AristotleLemmas

/-
The rank of the unfolding of the mode product at the active mode is equal to the rank of the product of the transformation matrix and the unfolding of the original tensor.
-/
def col_equiv_t {d : ℕ} (t : Fin d) (I : Fin d → ℕ) (r : Fin d → ℕ) :
    (∀ k : {k // k ≠ t}, Fin (mode_product_shape t (I t) r k)) ≃ (∀ k : {k // k ≠ t}, Fin (r k)) where
  toFun f k := cast (by rw [mode_product_shape]; simp [k.prop]) (f k)
  invFun g k := cast (by rw [mode_product_shape]; simp [k.prop]) (g k)
  left_inv f := by ext k; simp
  right_inv g := by ext k; simp

lemma rank_mode_product_t_eq {d : ℕ} (I : Fin d → ℕ) {r : Fin d → ℕ} (G : Tensor r) (t : Fin d) (U : Matrix (Fin (I t)) (Fin (r t)) ℝ) :
    (unfolding (mode_product_shape t (I t) r) t (mode_product I G t U)).rank = (U * unfolding r t G).rank := by
      convert Matrix.rank_reindex _ _ _;
      rotate_left;
      exact inferInstance;
      exact Equiv.cast ( by simp +decide [ mode_product_shape ] );
      exact (col_equiv_t t I r).symm;
      ext i j; simp +decide [ mode_product, unfolding ] ;
      simp +decide [ Matrix.mul_apply, mode_product_index_G, combine_indices ];
      rw [ Finset.sum_congr rfl ] ; intros ; ring_nf!;
      rw [ mul_comm ];
      unfold mode_product_index_G combine_indices col_equiv_t; aesop;

/-
If every column of matrix A is in the span of the columns of matrix B, then the rank of A is at most the rank of B.
-/
lemma rank_le_of_cols_in_span {m n1 n2 : Type*} [Fintype m] [Fintype n1] [Fintype n2] [DecidableEq m] [DecidableEq n1] [DecidableEq n2] (A : Matrix m n1 ℝ) (B : Matrix m n2 ℝ) (h : ∀ j, Aᵀ j ∈ Submodule.span ℝ (Set.range Bᵀ)) : A.rank ≤ B.rank := by
  -- The column space of A is contained in the column space of B, so the rank of A is less than or equal to the rank of B.
  have h_col_space : LinearMap.range (Matrix.mulVecLin A) ≤ Submodule.span ℝ (Set.range (Matrix.mulVecLin B)) := by
    intro x hx
    obtain ⟨y, hy⟩ := hx
    have h_col : ∀ j : n1, A.mulVecLin (Pi.single j 1) ∈ Submodule.span ℝ (Set.range (Matrix.mulVecLin B)) := by
      intro j
      specialize h j
      simp [Matrix.mulVecLin] at *;
      rw [ Submodule.mem_span ] at h ⊢;
      intro p hp; specialize h p; simp_all +decide [ Set.range_subset_iff, Matrix.mulVec ] ;
      exact h fun y => by simpa [ Matrix.mulVec, dotProduct ] using hp ( Pi.single y 1 ) ;
    convert Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ ( y j ) ( h_col j ) using 1;
    swap;
    exacts [ Finset.univ, by ext i; simpa [ Matrix.mulVec, dotProduct, mul_comm ] using congr_fun hy.symm i ];
  refine' le_trans ( Submodule.finrank_mono h_col_space ) _;
  refine' Submodule.finrank_mono _;
  exact Submodule.span_le.mpr ( Set.range_subset_iff.mpr fun x => LinearMap.mem_range_self _ _ )

/-
Mapping from column indices of the mode product unfolding to column indices of the original tensor unfolding, for a fixed summation index p.
-/
def col_map_ne_t {d : ℕ} {I : Fin d → ℕ} {r : Fin d → ℕ} {t k : Fin d} (h : k ≠ t)
    (j : ∀ l : {l // l ≠ k}, Fin (mode_product_shape t (I t) r l)) (p : Fin (r t)) :
    ∀ l : {l // l ≠ k}, Fin (r l) :=
  fun l =>
    if h_lt : l.val = t then
      cast (by rw [h_lt]) p
    else
      cast (by
        have : mode_product_shape t (I t) r l = r l := by
          simp [mode_product_shape]; intro h_eq; rw [h_eq] at h_lt; contradiction
        rw [this]) (j l)

/-
Equivalence between row indices of the unfolded mode product and the original tensor for a non-active mode.
-/
def row_equiv_ne_t {d : ℕ} {I : Fin d → ℕ} {r : Fin d → ℕ} {t k : Fin d} (h : k ≠ t) :
    Fin (mode_product_shape t (I t) r k) ≃ Fin (r k) :=
  Equiv.cast (by rw [mode_product_shape]; simp [h])

/-
Entry-wise formula for the reindexed unfolding of a mode product at a non-active mode.
-/
lemma unfolding_mode_product_ne_t_apply {d : ℕ} (I : Fin d → ℕ) {r : Fin d → ℕ} (G : Tensor r) (t : Fin d) (U : Matrix (Fin (I t)) (Fin (r t)) ℝ) (k : Fin d) (h : k ≠ t)
    (i : Fin (r k)) (j : ∀ l : {l // l ≠ k}, Fin (mode_product_shape t (I t) r l)) :
    (unfolding (mode_product_shape t (I t) r) k (mode_product I G t U)).reindex (row_equiv_ne_t h) (Equiv.refl _) i j =
    ∑ p : Fin (r t), U (cast (by simp [mode_product_shape]) (j ⟨t, h.symm⟩)) p * (unfolding r k G) i (col_map_ne_t h j p) := by
      unfold mode_product unfolding;
      simp +decide [ row_equiv_ne_t, mode_product_index_G, combine_indices ];
      unfold mode_product_index_G col_map_ne_t; simp +decide [ h.symm, mul_comm ] ;
      congr! 3;
      ext l; by_cases hl : l = k <;> simp +decide [ hl, combine_indices ] ;
      aesop

/-
The rank of the unfolding of a mode product at a non-active mode is at most the rank of the unfolding of the original tensor at that mode.
-/
lemma rank_mode_product_ne_t_le {d : ℕ} (I : Fin d → ℕ) {r : Fin d → ℕ} (G : Tensor r) (t : Fin d) (U : Matrix (Fin (I t)) (Fin (r t)) ℝ) (k : Fin d) (h : k ≠ t) :
    (unfolding (mode_product_shape t (I t) r) k (mode_product I G t U)).rank ≤ (unfolding r k G).rank := by
      -- By Lemma 2, the rank of the Reindexed Matrix of a Mode Product is the same as the Rank of the Original Matrix.
      set M' := (unfolding (mode_product_shape t (I t) r) k (mode_product I G t U)).reindex (row_equiv_ne_t h) (Equiv.refl _) with hM';
      -- By Lemma 2, the rank of the reindexed matrix `M'` is the same as the rank of the original matrix.
      have h_rank_M' : M'.rank ≤ (unfolding r k G).rank := by
        apply rank_le_of_cols_in_span;
        intro j
        have h_sum : M'ᵀ j = ∑ p : Fin (r t), (U (cast (by simp [mode_product_shape]) (j ⟨t, h.symm⟩)) p) • (unfolding r k G)ᵀ (fun i => col_map_ne_t h j p i) := by
          ext i; simp [hM', unfolding_mode_product_ne_t_apply];
          convert unfolding_mode_product_ne_t_apply I G t U k h i j using 1;
        exact h_sum.symm ▸ Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ ( Submodule.subset_span <| Set.mem_range_self _ );
      convert h_rank_M' using 1;
      convert Matrix.rank_reindex _ _ _;
      rotate_left;
      exact inferInstance;
      exact (row_equiv_ne_t h).symm;
      exact Equiv.refl _;
      ext i j; simp +decide [ M' ] ;

/-
The rank of the unfolding of a casted tensor is equal to the rank of the unfolding of the original tensor.
-/
lemma rank_unfolding_cast {d : ℕ} {I J : Fin d → ℕ} (h : I = J) (T : Tensor I) (k : Fin d) :
    (unfolding J k (cast (congrArg Tensor h) T)).rank = (unfolding I k T).rank := by
      subst h; rfl;

end AristotleLemmas

theorem rank_le_four_mode_product_square
    (T : BigTensor n) (t : Fin 4)
    (M : Matrix (Fin (3 * n)) (Fin (3 * n)) ℝ)
    (h : rank_le_four (n := n) T) :
    rank_le_four (n := n) (mode_product_square (n := n) T t M) := by
  intro k;
  -- Apply the rank inequality for mode products
  have h_rank : (unfolding (mode_product_shape t (I_3n n t) (I_3n n)) k (mode_product (I_3n n) T t M)).rank ≤ (unfolding (I_3n n) k T).rank := by
    by_cases hk : k = t;
    · rw [ hk, rank_mode_product_t_eq ];
      exact Matrix.rank_mul_le_right _ _;
    · convert rank_mode_product_ne_t_le ( I_3n n ) T t M k hk using 1;
  convert h_rank.trans ( h k ) using 1;
  convert rank_unfolding_cast _ _ _ using 1;
  exact mode_product_shape_eq_I_3n t

-- Sequential version: apply to four modes.
theorem rank_le_four_mode_product_square4
    (T : BigTensor n)
    (M0 M1 M2 M3 : Matrix (Fin (3 * n)) (Fin (3 * n)) ℝ)
    (h : rank_le_four (n := n) T) :
    rank_le_four (n := n)
      (mode_product_square (n := n)
        (mode_product_square (n := n)
          (mode_product_square (n := n)
            (mode_product_square (n := n) T 0 M0) 1 M1) 2 M2) 3 M3) := by
  -- Apply the rank_le_four_mode_product_square lemma four times, once for each mode.
  have h1 : rank_le_four (mode_product_square T 0 M0) := by
    apply rank_le_four_mode_product_square; assumption
  have h2 : rank_le_four (mode_product_square (mode_product_square T 0 M0) 1 M1) := by
    convert rank_le_four_mode_product_square ( mode_product_square T 0 M0 ) 1 M1 h1 using 1
  have h3 : rank_le_four (mode_product_square (mode_product_square (mode_product_square T 0 M0) 1 M1) 2 M2) := by
    convert rank_le_four_mode_product_square _ _ _ h2 using 1
  have h4 : rank_le_four (mode_product_square (mode_product_square (mode_product_square (mode_product_square T 0 M0) 1 M1) 2 M2) 3 M3) := by
    convert rank_le_four_mode_product_square _ _ _ h3 using 1;
  exact h4

end ModeProductRank

/-! --------------------------------------------------------------------------
  8) Separable scaling → minors vanish (the easy direction).
---------------------------------------------------------------------------- -/

section ForwardDirection

variable {n : ℕ}

-- Forward implication in the main theorem: separable_scaling → all minors vanish
noncomputable section AristotleLemmas

/-
Helper lemma: casting an index vector between equal shapes preserves the values of the components.
-/
lemma mode_product_cast_idx_val {n : ℕ} (t : Fin 4) (idx : Fin 4 → Fin (3 * n)) :
    let h := (mode_product_shape_eq_I_3n t).symm
    let idx_cast := cast (congrArg (fun I => (k : Fin 4) → Fin (I k)) h) idx
    ∀ k, (idx_cast k).val = (idx k).val := by
      convert cast_eq_iff_heq.mpr _;
      rotate_left;
      exact Π k : Fin 4, Fin ( I_3n n k );
      exact ( k : Fin 4 ) → Fin ( mode_product_shape t ( I_3n n t ) ( I_3n n ) k );
      rotate_left;
      exact fun k => ⟨ idx k, by fin_cases k <;> simp +decide [ I_3n ] ⟩;
      exact fun k => ⟨ idx k, by fin_cases k <;> simp +decide [ I_3n, mode_product_shape ] ⟩;
      congr! 1;
      rotate_left 1;
      rotate_left;
      congr! 1;
      all_goals norm_num [ funext_iff, Fin.ext_iff, mode_product_shape ];
      · grind;
      · congr! 1;
        · unfold mode_product_shape; aesop;
        · aesop

/-
Helper lemma: mode_product_index_G simplifies to the identity index when the shapes are equal.
-/
lemma mode_product_index_G_simp_I3n {n : ℕ} (t : Fin 4) (idx : Fin 4 → Fin (3 * n)) :
    let h := (mode_product_shape_eq_I_3n t).symm
    let idx_cast := cast (congrArg (fun I => (k : Fin 4) → Fin (I k)) h) idx
    mode_product_index_G (I_3n n) t (cast (by simp [mode_product_shape, I_3n]) (idx_cast t)) idx_cast =
    idx := by
      unfold mode_product_index_G; simp +decide [ *, Fin.ext_iff ] ;
      ext k; by_cases h : ( k : ℕ ) = t <;> simp +decide [ h ] ;
      · convert mode_product_cast_idx_val t idx k;
        · fin_cases k <;> fin_cases t <;> trivial;
        · grind;
      · convert mode_product_cast_idx_val t idx k using 1
        generalize_proofs at *;
        congr! 1;
        · unfold mode_product_shape; aesop;
        · grind

/-
Applying a mode product with a scaling matrix (diagonal) to a tensor is equivalent to multiplying the tensor element-wise by the scaling factor corresponding to the index in that mode.
-/
lemma mode_product_square_apply_scaling {n : ℕ} (T : Tensor (I_3n n)) (t : Fin 4) (u : Fin n → ℝ)
    (idx : Fin 4 → Fin (3 * n)) :
    mode_product_square (n := n) T t (scaling_matrix u) idx =
    T idx * u (inv_iota_alpha (idx t)) := by
      convert mode_product_diagonal_simp T t u _ using 1;
      convert cast_tensor_apply _ _ _;
      convert mode_product_shape_eq_I_3n t;
      congr! 2;
      · convert mode_product_index_G_simp_I3n t idx |> Eq.symm;
      · congr! 2;
        convert rfl using 1;
        convert mode_product_cast_idx_val t idx t using 1;
        simp +decide [ Fin.ext_iff, cast ];
        fin_cases t <;> rfl ;

/-
The assembly of a separably scaled block tensor family is equal to the sequential mode product of the assembled unscaled tensor with the corresponding scaling matrices.
-/
lemma Asm_separable_eq_mode_product {n : ℕ} (T_fam : Fin n → Fin n → Fin n → Fin n → Tensor (fun _ : Fin 4 => 3))
    (u v w x : Fin n → ℝ) :
    Asm (block_scaling (fun α β γ δ => u α * v β * w γ * x δ) T_fam) =
    mode_product_square (n := n)
      (mode_product_square (n := n)
        (mode_product_square (n := n)
          (mode_product_square (n := n) (Asm T_fam) 0 (scaling_matrix u))
        1 (scaling_matrix v))
      2 (scaling_matrix w))
    3 (scaling_matrix x) := by
      apply Tensor.ext; intro idx; simp [mode_product_square_apply_scaling, Asm_block_scaling_apply];
      ring

end AristotleLemmas

theorem separable_scaling_implies_mathbf_F_n_zero
    (A : CamTuple n) (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hsep : separable_scaling (n := n) lam) :
    ∀ idx : MinorIndices n,
      mathbf_F_n (n := n)
        (block_scaling (n := n) lam (fun α β γ δ => Q_block A α β γ δ)) idx = 0 := by
  -- Apply the main theorem's hypothesis that if all minors vanish, then the assembled tensor has rank ≤ 4.
  have h_rank_le_four : rank_le_four (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))) := by
    obtain ⟨ u, v, w, x, h_nonzero, h_sep ⟩ := hsep;
    convert rank_le_four_mode_product_square4 _ _ _ _ _ _ using 1;
    convert separable_congr A lam u v w x _;
    rw [ Asm_separable_eq_mode_product ];
    · exact h_sep.2.2.2;
    · exact rank_Q_le_four A;
  convert rank_le_four_implies_mathbf_F_n_zero _ h_rank_le_four using 1

end ForwardDirection

/-! --------------------------------------------------------------------------
  9) Minors vanish → separable scaling (the hard direction).
---------------------------------------------------------------------------- -/

section BackwardDirection

variable {n : ℕ}

-- Main “hard” implication packaged as a single lemma (under GoodA + valid_lambda).
theorem mathbf_F_n_zero_implies_separable_scaling
    (A : CamTuple n) (h_n : n ≥ 5) (hA : GoodA (n := n) A)
    (lam : Fin n → Fin n → Fin n → Fin n → ℝ) (h_lam : valid_lambda (n := n) lam)
    (hF : ∀ idx : MinorIndices n,
      mathbf_F_n (n := n)
        (block_scaling (n := n) lam (fun α β γ δ => Q_block A α β γ δ)) idx = 0) :
    separable_scaling (n := n) lam := by
  -- Apply the assumption that the tensor has multilinear rank at most (4,4,4,4) to obtain the factorization.
  have h_factor : ∃ (u v w x : Fin n → ℝ) (mu nu xi zeta : Fin n → Fin n → Fin n → ℝ),
    (∀ i, u i ≠ 0) ∧ (∀ i, v i ≠ 0) ∧ (∀ i, w i ≠ 0) ∧ (∀ i, x i ≠ 0) ∧
    (∀ α β γ δ, not_constant_triple β γ δ → lam α β γ δ = u α * mu β γ δ) ∧
    (∀ α β γ δ, not_constant_triple α γ δ → lam α β γ δ = v β * nu α γ δ) ∧
    (∀ α β γ δ, not_constant_triple α β δ → lam α β γ δ = w γ * xi α β δ) ∧
    (∀ α β γ δ, not_constant_triple α β γ → lam α β γ δ = x δ * zeta α β γ) := by
      apply all_modes_factor A lam h_n hA.1 hA.2.1 hA.2.2 h_lam (rank_le_four_iff_F_n_zero (n := n) (Asm (block_scaling lam (fun α β γ δ => Q_block A α β γ δ))) |>.2 hF);
  exact separable_lambda lam h_n h_lam _ _ _ _ _ _ _ _ h_factor.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1 h_factor.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1 h_factor.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.1 h_factor.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1 h_factor.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.1 h_factor.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.2.1 h_factor.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.1 h_factor.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.2

-- If you prefer to expose the intermediate step: minors vanish ⇒ rank_le_four of assembled scaled tensor.
theorem mathbf_F_n_zero_implies_rank_le_four_scaled
    (A : CamTuple n) (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (hF : ∀ idx : MinorIndices n,
      mathbf_F_n (n := n)
        (block_scaling (n := n) lam (fun α β γ δ => Q_block A α β γ δ)) idx = 0) :
    rank_le_four (n := n)
      (Asm (n := n)
        (block_scaling (n := n) lam (fun α β γ δ => Q_block A α β γ δ))) := by
  convert rank_le_four_iff_F_n_zero _ |>.2 _;
  convert hF using 1

-- If you want the full “all modes factor” + “separable_lambda” chain packaged:
theorem rank_le_four_scaled_implies_separable_scaling
    (A : CamTuple n) (lam : Fin n → Fin n → Fin n → Fin n → ℝ)
    (h_n : n ≥ 5) (hA : GoodA (n := n) A) (h_lam : valid_lambda (n := n) lam)
    (hT : rank_le_four (n := n)
      (Asm (n := n)
        (block_scaling (n := n) lam (fun α β γ δ => Q_block A α β γ δ)))) :
    separable_scaling (n := n) lam := by
  by_contra h_contra;
  -- Apply the lemma that states if the tensor has multilinear rank at most (4,4,4,4), then lambda has a factorization for each mode.
  obtain ⟨u, v, w, x, mu, nu, xi, zeta, hu, hv, hw, hx, h_mode1, h_mode2, h_mode3, h_mode4⟩ := all_modes_factor A lam h_n hA.1 hA.2.1 hA.2.2 h_lam hT;
  exact h_contra <| separable_lambda lam h_n h_lam u v w x mu nu xi zeta hu hv hw hx h_mode1 h_mode2 h_mode3 h_mode4

end BackwardDirection

/-! --------------------------------------------------------------------------
  10) Main equivalence theorem and packaging into your `main_theorem_equivalence`.
---------------------------------------------------------------------------- -/

section MainEquivalence

variable {n : ℕ}

theorem main_theorem_equivalence_of_GoodA
    (A : CamTuple n) (h_n : n ≥ 5) (hA : GoodA (n := n) A) :
    main_theorem_equivalence (n := n) A := by
  intro lam h_lam
  constructor
  · intro hF
    -- minors vanish → separable
    exact mathbf_F_n_zero_implies_separable_scaling (n := n) A h_n hA lam h_lam hF
  · intro hsep idx
    -- separable → minors vanish
    -- (Use the forward-direction lemma)
    exact separable_scaling_implies_mathbf_F_n_zero (n := n) A lam hsep idx

end MainEquivalence

/-! --------------------------------------------------------------------------
  11) Zariski-genericity combinators + GoodA is generic.
---------------------------------------------------------------------------- -/

section ZariskiGenericCombinators

variable {n : ℕ}

-- Conjunction closure
theorem ZariskiGeneric.and
    (P Q : CamTuple n → Prop)
    (hP : ZariskiGeneric (n := n) P)
    (hQ : ZariskiGeneric (n := n) Q) :
    ZariskiGeneric (n := n) (fun A => P A ∧ Q A) := by
  obtain ⟨ fP, hfP ⟩ := hP;
  obtain ⟨ fQ, hfQ ⟩ := hQ;
  exact ⟨ fP * fQ, mul_ne_zero hfP.1 hfQ.1, fun A hA => ⟨ hfP.2 A ( by contrapose! hA; simp +decide [ hA ] ), hfQ.2 A ( by contrapose! hA; simp +decide [ hA ] ) ⟩ ⟩

-- Finite universal quantification closure
theorem ZariskiGeneric.forall_finset
    {ι : Type*} [Fintype ι]
    (P : ι → CamTuple n → Prop)
    (h : ∀ i, ZariskiGeneric (n := n) (P i)) :
    ZariskiGeneric (n := n) (fun A => ∀ i, P i A) := by
  choose p hp hp' using h;
  refine' ⟨ ∏ i, p i, _, _ ⟩;
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => hp i;
  · simp_all +decide [ Finset.prod_eq_zero_iff, MvPolynomial.eval_prod ]

-- Zariski-genericity of rank-3 blocks: ∀ α, rank(A α)=3
theorem block_rank_three_generic (α : Fin n) :
    ZariskiGeneric (n := n) (fun A : CamTuple n => (A α).rank = 3) := by
  -- By definition of $p$, we know that $p(A) \neq 0$ if and only if at least one of the $3 \times 3$ minors of $A_\alpha$ is non-zero.
  have h_poly_nonzero : ∀ A : CamTuple n, (∃ C : Fin 3 → Fin 4, Matrix.det (Matrix.of (fun i j => A α i (C j))) ≠ 0) ↔ (A α).rank = 3 := by
    intro A
    constructor
    intro h_det_nonzero
    obtain ⟨C, hC⟩ := h_det_nonzero
    have h_rank_ge_3 : (A α).rank ≥ 3 := by
      have h_rank_ge_3 : LinearMap.range (Matrix.mulVecLin (A α)) ≥ Submodule.span ℝ (Set.range (fun i : Fin 3 => Matrix.mulVec (A α) (Pi.single (C i) 1))) := by
        exact Submodule.span_le.mpr ( Set.range_subset_iff.mpr fun i => LinearMap.mem_range_self _ _ )
      generalize_proofs at *; (
      have h_lin_indep : LinearIndependent ℝ (fun i : Fin 3 => Matrix.mulVec (A α) (Pi.single (C i) 1)) := by
        convert Matrix.linearIndependent_cols_of_det_ne_zero hC using 1
        generalize_proofs at *; (
        ext i j; simp +decide [ Matrix.mulVec, dotProduct ] ;
        rw [ Finset.sum_eq_single ( C i ) ] <;> aesop
        skip)
      generalize_proofs at *; (
      have h_dim_ge_3 : Module.finrank ℝ (Submodule.span ℝ (Set.range (fun i : Fin 3 => Matrix.mulVec (A α) (Pi.single (C i) 1)))) = 3 := by
        rw [ finrank_span_eq_card ] <;> aesop
        skip
      generalize_proofs at *; (
      exact h_dim_ge_3 ▸ Submodule.finrank_mono h_rank_ge_3 |> le_trans <| by simp +decide [ Matrix.rank ] ;)))
    have h_rank_le_3 : (A α).rank ≤ 3 := by
      exact rank_le_height (A α)
    exact le_antisymm h_rank_le_3 h_rank_ge_3
    intro h_rank_eq_3
    have h_det_nonzero : ∃ C : Fin 3 → Fin 4, Matrix.det (Matrix.of (fun i j => A α i (C j))) ≠ 0 := by
      have := Matrix.rank_eq_finrank_span_cols ( A α ) ; simp_all +decide [ Matrix.rank ] ;
      -- Since the rank of $A_\alpha$ is 3, the range of $A_\alpha$ spans a 3-dimensional subspace of $\mathbb{R}^3$.
      have h_span : ∃ (v : Fin 3 → Fin 4), LinearIndependent ℝ (fun i => (A α).col (v i)) := by
        have := ( exists_linearIndependent ℝ ( Set.range ( A α |> Matrix.col ) ) );
        obtain ⟨ b, hb₁, hb₂, hb₃ ⟩ := this; have := hb₃; simp_all +decide [ Set.subset_def ] ;
        have h_card : b.Finite ∧ Set.ncard b = 3 := by
          have h_card : b.Finite ∧ Module.finrank ℝ (Submodule.span ℝ b) = 3 := by
            exact ⟨ Set.Finite.subset ( Set.toFinite ( Set.range ( A α |> Matrix.col ) ) ) fun x hx => by aesop, by rw [ hb₂, ‹3 = Module.finrank ℝ ( Submodule.span ℝ ( Set.range ( A α |> Matrix.col ) ) ) ›.symm ] ⟩
            skip
          generalize_proofs at *; (
          have := h_card.1.fintype; simp_all +decide [ Set.ncard_eq_toFinset_card' ] ;
          rw [ ← h_card.2, finrank_span_set_eq_card ] ; aesop
          skip;
          (expose_names; exact this_2))
        generalize_proofs at *; (
        -- Since $b$ is finite and has cardinality 3, we can obtain a bijection between $Fin 3$ and $b$.
        obtain ⟨v, hv⟩ : ∃ v : Fin 3 ≃ b, True := by
          have := h_card.1.fintype; exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ Set.ncard_eq_toFinset_card' ] at h_card ⊢; linarith, trivial ⟩ ;
        generalize_proofs at *; (
        choose f hf using fun i => hb₁ _ ( v i |>.2 ) ; use f; convert this.comp _ _ ; aesop;
        exact v.injective))
      generalize_proofs at *; (
      obtain ⟨ v, hv ⟩ := h_span; use v; rw [ Fintype.linearIndependent_iff ] at hv; simp_all +decide [ Matrix.det_fin_three ] ;
      contrapose! hv
      generalize_proofs at *; (
      -- Since the determinant is zero, the columns are linearly dependent.
      have h_lin_dep : ∃ (g : Fin 3 → ℝ), g ≠ 0 ∧ ∑ i, g i • (A α).col (v i) = 0 := by
        have h_det_zero : Matrix.det (Matrix.of (fun i j => A α i (v j))) = 0 := by
          simp +decide [ Matrix.det_fin_three, hv ]
        have := Matrix.exists_mulVec_eq_zero_iff.mpr h_det_zero; obtain ⟨ g, hg ⟩ := this; use g; simp_all +decide [ funext_iff, Fin.sum_univ_three ] ;
        simp_all +decide [ Fin.sum_univ_three, Matrix.mulVec, dotProduct ];
        exact fun x => by linear_combination' hg.2 x;
      generalize_proofs at *; (
      exact ⟨ h_lin_dep.choose, h_lin_dep.choose_spec.2, Function.ne_iff.mp h_lin_dep.choose_spec.1 ⟩
      skip)))
    exact h_det_nonzero
    skip
  generalize_proofs at *;
  -- By definition of $p$, we know that $p(A) \neq 0$ if and only if at least one of the $3 \times 3$ minors of $A_\alpha$ is non-zero. Hence, $p$ is non-zero.
  have h_poly_nonzero : ∃ p : MvPolynomial (Fin n × Fin 3 × Fin 4) ℝ, p ≠ 0 ∧ ∀ A : CamTuple n, (∃ C : Fin 3 → Fin 4, Matrix.det (Matrix.of (fun i j => A α i (C j))) ≠ 0) ↔ MvPolynomial.eval (fun v => (A v.1 v.2.1 v.2.2)) p ≠ 0 := by
    -- Define the polynomial p as the sum of squares of the determinants of all 3x3 submatrices of A α.
    use Finset.sum (Finset.univ : Finset (Fin 3 → Fin 4)) (fun C => MvPolynomial.C (1 : ℝ) * (MvPolynomial.X (α, 0, C 0) * MvPolynomial.X (α, 1, C 1) * MvPolynomial.X (α, 2, C 2) - MvPolynomial.X (α, 0, C 1) * MvPolynomial.X (α, 1, C 0) * MvPolynomial.X (α, 2, C 2) + MvPolynomial.X (α, 0, C 1) * MvPolynomial.X (α, 1, C 2) * MvPolynomial.X (α, 2, C 0) - MvPolynomial.X (α, 0, C 2) * MvPolynomial.X (α, 1, C 1) * MvPolynomial.X (α, 2, C 0) + MvPolynomial.X (α, 0, C 2) * MvPolynomial.X (α, 1, C 0) * MvPolynomial.X (α, 2, C 1) - MvPolynomial.X (α, 0, C 0) * MvPolynomial.X (α, 1, C 2) * MvPolynomial.X (α, 2, C 1))^2);
    constructor;
    · refine' ne_of_apply_ne ( MvPolynomial.eval ( fun v => if v = ( α, 0, 0 ) then 1 else if v = ( α, 1, 1 ) then 1 else if v = ( α, 2, 2 ) then 1 else 0 ) ) _ ; simp +decide [ Fin.sum_univ_three ] ; ring_nf ; norm_num;
      norm_cast at * <;> simp_all +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ] <;> ring_nf <;> norm_num <;> first | linarith | aesop | assumption;
    · intro A; simp +decide [ Finset.sum_ite, Matrix.det_fin_three ] ;
      constructor <;> intro h <;> contrapose! h <;> simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg ] ;
      · exact fun x => by linear_combination' h x;
      · exact fun i => by linear_combination' h i;
  generalize_proofs at *;
  rename_i h; obtain ⟨ p, hp₁, hp₂ ⟩ := h_poly_nonzero; simp_all +decide [ ZariskiGeneric ] ;
  refine' ⟨ p, hp₁, fun A hA => h A |>.1 hA ⟩
  skip -- This is a placeholder to make the code compile. The actual proof will be filled in later.

theorem all_blocks_rank_three_generic :
    ZariskiGeneric (n := n) (fun A : CamTuple n => ∀ α, (A α).rank = 3) := by
  -- Apply the ZariskiGeneric.and lemma to combine the genericity of each individual rank condition.
  have h_rank3 : ∀ α : Fin n, ZariskiGeneric (fun A : CamTuple n => (A α).rank = 3) := by
    -- Apply the lemma `block_rank_three_generic` to each α.
    intro α
    apply block_rank_three_generic;
  -- Apply the ZariskiGeneric.forall_finset lemma to combine the genericity of each individual rank condition.
  apply ZariskiGeneric.forall_finset; intro α; exact h_rank3 α

-- Zariski-genericity of the P-matrix rank condition, uniformly over all non-constant triples.
theorem all_P_rank_generic :
    ZariskiGeneric (n := n)
      (fun A : CamTuple n => ∀ β γ δ, not_constant_triple β γ δ → (P_matrix A β γ δ).rank = 4) := by
  -- By Theorem `rank_P_matrix المستخدم`, each rank-4 condition is Zariski-generic; we Just Need Finite Intersections.
  have hP_generic : ∀ (β γ δ : Fin n), not_constant_triple β γ δ → ZariskiGeneric (fun A : CamTuple n => Matrix.rank (P_matrix A β γ δ) = 4) := by
    exact fun β γ δ a ↦ P_rank_generic_final β γ δ a;
  have hP_generic : ZariskiGeneric (fun A : CamTuple n => ∀ β γ δ : Fin n, not_constant_triple β γ δ → Matrix.rank (P_matrix A β γ δ) = 4) := by
    have hP_generic : ∀ (s : Finset (Fin n × Fin n × Fin n)), (∀ (β γ δ : Fin n), (β, γ, δ) ∈ s → not_constant_triple β γ δ) → ZariskiGeneric (fun A : CamTuple n => ∀ (β γ δ : Fin n), (β, γ, δ) ∈ s → Matrix.rank (P_matrix A β γ δ) = 4) := by
      intros s hsconst
      induction' s using Finset.induction with βγδ s ih;
      · simp [ZariskiGeneric];
        exact ⟨ 1, one_ne_zero ⟩;
      · rename_i h;
        convert ZariskiGeneric.and _ _ ( h fun β γ δ h => hsconst β γ δ ( Finset.mem_insert_of_mem h ) ) ( hP_generic βγδ.1 βγδ.2.1 βγδ.2.2 ( hsconst _ _ _ ( Finset.mem_insert_self _ _ ) ) ) using 1;
        grind
    convert hP_generic ( Finset.univ.filter fun x => not_constant_triple x.1 x.2.1 x.2.2 ) _ using 1;
    · grind;
    · simp +contextual;
  convert hP_generic using 1

-- Finally, GoodA is Zariski-generic (requires `n ≥ 2` for C-rank condition).
theorem GoodA_generic (h_n : n ≥ 2) :
    ZariskiGeneric (n := n) (fun A : CamTuple n => GoodA (n := n) A) := by
  -- Apply the ZariskiGeneric.and lemma to combine the genericity of the conditions.
  have h_combined : ZariskiGeneric (fun A : CamTuple n => (StackedMatrix A).rank = 4) ∧ ZariskiGeneric (fun A : CamTuple n => ∀ α, (A α).rank = 3) ∧ ZariskiGeneric (fun A : CamTuple n => ∀ β γ δ, not_constant_triple β γ δ → (P_matrix A β γ δ).rank = 4) := by
    refine' ⟨ _, _, _ ⟩;
    · exact C_rank_generic h_n;
    · exact all_blocks_rank_three_generic;
    · exact all_P_rank_generic;
  convert ZariskiGeneric.and _ _ h_combined.1 ( ZariskiGeneric.and _ _ h_combined.2.1 h_combined.2.2 ) using 1

end ZariskiGenericCombinators

/-! --------------------------------------------------------------------------
  12) “Global” main theorem: generic A implies the equivalence statement.
---------------------------------------------------------------------------- -/

section GenericMain

variable {n : ℕ}

-- Version: on the Zariski-open set `GoodA`, the equivalence holds.
theorem main_on_GoodA :
    ∀ A : CamTuple n, GoodA (n := n) A → (n ≥ 5 → main_theorem_equivalence (n := n) A) := by
  intro A hA h_n
  exact main_theorem_equivalence_of_GoodA (n := n) A h_n hA

-- Version: Zariski-generic A satisfy the equivalence.
theorem main_Zariski_generic (h_n5 : n ≥ 5) (h_n2 : n ≥ 2) :
    ZariskiGeneric (n := n) (fun A : CamTuple n => main_theorem_equivalence (n := n) A) := by
  -- Intended proof strategy: use `GoodA_generic` and show `GoodA A → main_theorem_equivalence A`.
  have := GoodA_generic h_n2;
  exact ⟨ this.choose, this.choose_spec.1, fun A hA => main_on_GoodA A ( this.choose_spec.2 A hA ) h_n5 ⟩

end GenericMain

/-
  ============================================================================
  PACKAGING LAYER:
  From `BlockFam n` / `MinorIndices n` to an explicit map
  `ℝ^(81*n^4) → ℝ^N`, plus final theorems matching the original goal.
  ============================================================================
-/

namespace Packaging

/-- The raw “coordinate index” for a block family:
    choose (α,β,γ,δ) and an internal tensor index (i,j,k,ℓ). -/
abbrev DomIdx (n : ℕ) :=
  Fin n × Fin n × Fin n × Fin n × (Fin 4 → Fin 3)

/-- The input space `ℝ^(81*n^4)` as a function on `Fin (81*n^4)`. -/
abbrev RVec (m : ℕ) := Fin m → ℝ

/-- The “uncurried” view of a block tensor family as a single function on `DomIdx n`. -/
def uncurryBlockFam {n : ℕ} (T : BlockFam n) : DomIdx n → ℝ
  | ⟨α, β, γ, δ, idx⟩ => T α β γ δ idx

/-- The “curried” view: turn a function on `DomIdx n` into a block family. -/
def curryBlockFam {n : ℕ} (f : DomIdx n → ℝ) : BlockFam n :=
  fun α β γ δ idx => f ⟨α, β, γ, δ, idx⟩

/-- `BlockFam n` is equivalent to functions on `DomIdx n`. -/
def blockFamEquivFun (n : ℕ) : BlockFam n ≃ (DomIdx n → ℝ) where
  toFun := uncurryBlockFam
  invFun := curryBlockFam
  left_inv := by
    intro T
    rfl
  right_inv := by
    intro f
    rfl

/-- The cardinality of the domain index type is `81 * n^4`. -/
lemma card_DomIdx (n : ℕ) :
    Fintype.card (DomIdx n) = 81 * n^4 := by
  simp +arith +decide [ Fintype.card_pi ] ; ring;

theorem nonempty_DomIdx_equiv_fin (n : ℕ) : Nonempty (DomIdx n ≃ Fin (81 * n^4)) := by
  -- Since the cardinality of `DomIdx n` is `81 * n^4`, we can use the fact that there exists an equivalence between `DomIdx n` and `Fin (81 * n^4)` by the definition of `Fintype.card`.
  apply Nonempty.intro; exact Fintype.equivFinOfCardEq (by
  -- Apply the lemma that states the cardinality of `DomIdx n` is `81 * n^4`.
  apply card_DomIdx)

/-- Choose a concrete equivalence between `DomIdx n` and `Fin (81*n^4)`. -/
noncomputable def DomIdx_equiv_fin (n : ℕ) : DomIdx n ≃ Fin (81 * n^4) := by
  classical
  exact Classical.choice (nonempty_DomIdx_equiv_fin n)

/-- Turn a function on `DomIdx n` into an `ℝ^(81*n^4)` vector using the chosen equivalence. -/
def funDom_to_RVec {n : ℕ} (f : DomIdx n → ℝ) : RVec (81 * n^4) :=
  fun i => f ((DomIdx_equiv_fin n).symm i)

/-- Inverse map: turn an `ℝ^(81*n^4)` vector into a function on `DomIdx n`. -/
def RVec_to_funDom {n : ℕ} (v : RVec (81 * n^4)) : DomIdx n → ℝ :=
  fun x => v ((DomIdx_equiv_fin n) x)

/-- Equivalence: `(DomIdx n → ℝ)` is `ℝ^(81*n^4)`. -/
noncomputable def funDomEquivRVec (n : ℕ) : (DomIdx n → ℝ) ≃ RVec (81 * n^4) where
  toFun := funDom_to_RVec
  invFun := RVec_to_funDom
  left_inv := by
    intro f
    ext x
    simp [funDom_to_RVec, RVec_to_funDom]
  right_inv := by
    intro v
    ext i
    simp [funDom_to_RVec, RVec_to_funDom]

/-- Equivalence: `BlockFam n` is (definitionally) the same as `ℝ^(81*n^4)`. -/
noncomputable def blockFamEquivRVec (n : ℕ) : BlockFam n ≃ RVec (81 * n^4) :=
  (blockFamEquivFun n).trans (funDomEquivRVec n)

/-! --------------------------------------------------------------------------
  Output packaging: `MinorIndices n → ℝ` as `ℝ^N` where `N = card (MinorIndices n)`.
---------------------------------------------------------------------------- -/

noncomputable section AristotleLemmas

lemma MinorIndices.finite_aux (n : ℕ) : Finite (MinorIndices n) := by
  -- To prove the equivalence, we can construct an injective function from `MinorIndices n` to the sigma type.
  have h_injective : Function.Injective (fun m : MinorIndices n => ⟨m.t, m.rows, m.cols⟩ : MinorIndices n → Σ t : Fin 4, Finset (Fin (3 * n)) × Finset (Lex ({k // k ≠ t} → Fin (3 * n)))) := by
    intro m₁ m₂ h; cases m₁; cases m₂; aesop;
  generalize_proofs at *; (
  exact Finite.of_injective _ h_injective)

end AristotleLemmas

theorem minorIndices_finite (n : ℕ) : Finite (MinorIndices n) := by
  -- prove finiteness
  convert MinorIndices.finite_aux n

noncomputable instance (n : ℕ) : Fintype (MinorIndices n) := by
  classical
  haveI : Finite (MinorIndices n) := minorIndices_finite n
  exact Fintype.ofFinite (MinorIndices n)

/-- We will use `N_out n := card (MinorIndices n)` as the output dimension. -/
noncomputable def N_out (n : ℕ) : ℕ := Fintype.card (MinorIndices n)

theorem finite_MinorIndices (n : ℕ) :
    Finite (MinorIndices n) := by
  -- The type `MinorIndices n` is finite because it is defined as a product of finite types.
  apply minorIndices_finite

/-- `MinorIndices n` is finite (hence has a `Fintype` instance). -/
instance (n : ℕ) : Fintype (MinorIndices n) := by
  exact Fintype.ofFinite (MinorIndices n)

theorem nonempty_outEquivRVec (n : ℕ) : Nonempty ((MinorIndices n → ℝ) ≃ RVec (N_out n)) := by
  -- Since `MinorIndices n` is finite, we can use the fact that any function from a finite set to `ℝ` can be represented as a vector in `ℝ^N`, where `N` is the cardinal �ity� of `MinorIndices n`. This follows from the fact that the type `MinorIndices n` is equivalent to `Fin (Fintype.card (MinorIndices n))`.
  have h_equiv : Nonempty (MinorIndices n ≃ Fin (Fintype.card (MinorIndices n))) := by
    -- Since `MinorIndices n` is finite, � we� can use the fact that any finite set is equivalent to `Fin (Fintype.card (MinorIndices n))`.
    apply Nonempty.intro; exact Fintype.equivFin (MinorIndices n);
  -- Apply the fact that if two types are equivalent, then the function spaces between them � are� also equivalent.
  apply Nonempty.intro; exact Equiv.arrowCongr h_equiv.some (Equiv.refl ℝ)

/-- Equivalence: `(MinorIndices n → ℝ)` is `ℝ^(N_out n)`. -/
noncomputable def outEquivRVec (n : ℕ) : (MinorIndices n → ℝ) ≃ RVec (N_out n) := by
  classical
  exact Classical.choice (nonempty_outEquivRVec n)

/-! --------------------------------------------------------------------------
  Define the packaged map `F_packed : ℝ^(81*n^4) → ℝ^(N_out n)`.

  This is your map `mathbf_F_n` but with explicit Euclidean-type domain/codomain.
---------------------------------------------------------------------------- -/

/-- The “raw” map before turning it into `Fin (N_out n) → ℝ`. -/
def F_raw (n : ℕ) : BlockFam n → (MinorIndices n → ℝ) :=
  fun T_fam idx => mathbf_F_n (n := n) T_fam idx

/-- The fully packaged map: `ℝ^(81*n^4) → ℝ^(N_out n)`. -/
noncomputable def F_packed (n : ℕ) : RVec (81 * n^4) → RVec (N_out n) :=
  fun v =>
    -- unpack ℝ^(81*n^4) to BlockFam n
    let T_fam : BlockFam n := (blockFamEquivRVec n).symm v
    -- apply raw minors map (MinorIndices n → ℝ)
    let outFun : MinorIndices n → ℝ := F_raw n T_fam
    -- repack as ℝ^(N_out n)
    (outEquivRVec n) outFun

/-- Convenience: “`F_packed n v = 0`” means all coordinates vanish. -/
def F_packed_vanishes {n : ℕ} (v : RVec (81 * n^4)) : Prop :=
  ∀ i : Fin (N_out n), F_packed n v i = 0

/-- Convenience: “raw output vanishes” in the original `MinorIndices` indexing. -/
def F_raw_vanishes {n : ℕ} (T_fam : BlockFam n) : Prop :=
  ∀ idx : MinorIndices n, F_raw n T_fam idx = 0

namespace Packaging

/-! --------------------------------------------------------------------------
  0) "Simp" lemmas for the equivalences you defined.
---------------------------------------------------------------------------- -/

@[simp] lemma blockFamEquivRVec_symm_apply_apply {n : ℕ} (T_fam : BlockFam n) :
    (blockFamEquivRVec n).symm ((blockFamEquivRVec n) T_fam) = T_fam := by
  -- By definition of `blockFamEquivRVec`, applying it and then its inverse returns the original `BlockFam n`.
  apply Equiv.symm_apply_apply

@[simp] lemma blockFamEquivRVec_apply_symm_apply {n : ℕ} (v : RVec (81 * n^4)) :
    (blockFamEquivRVec n) ((blockFamEquivRVec n).symm v) = v := by
  -- By definition of equivalence, the inverse of the equivalence is the same as the original function.
  apply Equiv.apply_symm_apply

@[simp] lemma outEquivRVec_symm_apply_apply {n : ℕ} (f : MinorIndices n → ℝ) :
    (outEquivRVec n).symm ((outEquivRVec n) f) = f := by
  -- By definition of equivalence, the composition of the equivalence and its inverse is the identity function.
  apply Equiv.symm_apply_apply

@[simp] lemma outEquivRVec_apply_symm_apply {n : ℕ} (g : RVec (N_out n)) :
    (outEquivRVec n) ((outEquivRVec n).symm g) = g := by
  grind

/-! --------------------------------------------------------------------------
  1) Expand / rewrite `F_packed` in a form that's easy to use.
---------------------------------------------------------------------------- -/

/-- A convenient "composition" form of `F_packed`. -/
lemma F_packed_eq_outEquivRVec_F_raw {n : ℕ} (v : RVec (81 * n^4)) :
    F_packed n v =
      (outEquivRVec n) (F_raw n ((blockFamEquivRVec n).symm v)) := by
  exact rfl

/-- Specialization of the previous lemma to an encoded block family. -/
lemma F_packed_apply_encode {n : ℕ} (T_fam : BlockFam n) :
    F_packed n ((blockFamEquivRVec n) T_fam) =
      (outEquivRVec n) (F_raw n T_fam) := by
  unfold Packaging.F_packed Packaging.F_raw Packaging.blockFamEquivRVec Packaging.outEquivRVec; aesop;

/-! --------------------------------------------------------------------------
  2) Unfold the "vanishing" predicates (purely definitional helpers).
---------------------------------------------------------------------------- -/

lemma F_raw_vanishes_iff_forall {n : ℕ} (T_fam : BlockFam n) :
    F_raw_vanishes (n := n) T_fam ↔
      (∀ idx : MinorIndices n, F_raw n T_fam idx = 0) := by
  -- By definition of `F_raw_vanishes`, we have that `F_raw_vanishes T_fam` is equivalent to `∀ idx, F_raw n T_fam idx = 0` by definition.
  simp [Packaging.F_raw_vanishes]

lemma F_packed_vanishes_iff_forall {n : ℕ} (v : RVec (81 * n^4)) :
    F_packed_vanishes (n := n) v ↔
      (∀ i : Fin (N_out n), F_packed n v i = 0) := by
  -- By definition of `F_packed_vanishes`, we have that `F_packed_vanishes v` is equivalent to `∀ i, F_packed n v i = 0` by definition.
  simp [Packaging.F_packed_vanishes]

/-! --------------------------------------------------------------------------
  3) The key “vanishing is invariant under reindexing” lemma for the output equiv.
---------------------------------------------------------------------------- -/

/--
Core reindexing fact: a function on a finite type vanishes everywhere iff its
reindexed/packed version vanishes everywhere.
-/
theorem outEquivRVec_forall_eq_zero_iff' {n : ℕ} (f : MinorIndices n → ℝ)
    (h0 : (outEquivRVec n (0 : MinorIndices n → ℝ)) = (0 : RVec (N_out n))) :
    (∀ i : Fin (N_out n), (outEquivRVec n f) i = 0) ↔
      (∀ idx : MinorIndices n, f idx = 0) := by
  classical
  -- Helper: a function into ℝ is identically zero iff it is equal to 0
  have forall_eq_zero_iff_eq_zero {α : Type} (g : α → ℝ) : (∀ a : α, g a = 0) ↔ g = 0 := by
    constructor
    · intro hg
      funext a
      exact hg a
    · intro hg a
      rw [hg]
      rfl
  -- First show that the inverse equivalence also sends 0 to 0
  have hsymm0 : (outEquivRVec n).symm (0 : RVec (N_out n)) = (0 : MinorIndices n → ℝ) := by
    have h := congrArg (outEquivRVec n).symm h0
    -- `simp` turns the left-hand side into `0`
    have h' : (0 : MinorIndices n → ℝ) = (outEquivRVec n).symm (0 : RVec (N_out n)) := by
      simpa using h
    exact h'.symm
  -- Equality with 0 is preserved/reflected by the equivalence, using `h0`
  have heq0 : (outEquivRVec n f = (0 : RVec (N_out n))) ↔ f = 0 := by
    constructor
    · intro hf
      have h := congrArg (outEquivRVec n).symm hf
      have h' : f = (outEquivRVec n).symm (0 : RVec (N_out n)) := by
        simpa using h
      simpa [hsymm0] using h'
    · intro hf
      subst hf
      exact h0
  -- Convert pointwise statements to equalities, then use `heq0`.
  have hout : (∀ i : Fin (N_out n), (outEquivRVec n f) i = 0) ↔ outEquivRVec n f = 0 := by
    simpa using (forall_eq_zero_iff_eq_zero (g := (outEquivRVec n f)))
  have hf : (∀ idx : MinorIndices n, f idx = 0) ↔ f = 0 := by
    simpa using (forall_eq_zero_iff_eq_zero (g := f))
  calc
    (∀ i : Fin (N_out n), (outEquivRVec n f) i = 0) ↔ outEquivRVec n f = 0 := hout
    _ ↔ f = 0 := heq0
    _ ↔ (∀ idx : MinorIndices n, f idx = 0) := by
      simpa using hf.symm

/-! --------------------------------------------------------------------------
  4) A “bridge lemma” combining (1) + (3): packed-vanish on encoded input
     ↔ raw-vanish.
---------------------------------------------------------------------------- -/

/--
This is often the single most useful intermediate lemma for the final equivalence:
`F_packed` vanishes on the encoded family iff `F_raw` vanishes.
-/
lemma F_packed_vanishes_encode_iff_F_raw_vanishes {n : ℕ} (T_fam : BlockFam n) :
    (∀ i : Fin (N_out n), F_packed n ((blockFamEquivRVec n) T_fam) i = 0) ↔
      (∀ idx : MinorIndices n, F_raw n T_fam idx = 0) := by
  sorry

/--
If you prefer it stated using your predicate abbreviations
`F_packed_vanishes` / `F_raw_vanishes`.
-/
lemma F_packed_vanishes_encode_iff_F_raw_vanishes' {n : ℕ} (T_fam : BlockFam n) :
    F_packed_vanishes (n := n) ((blockFamEquivRVec n) T_fam) ↔
      F_raw_vanishes (n := n) T_fam := by
  convert F_packed_vanishes_encode_iff_F_raw_vanishes T_fam using 1

end Packaging

/-- Lemma: vanishing is preserved by the output equivalence. -/
lemma F_raw_vanishes_iff_F_packed_vanishes {n : ℕ} (T_fam : BlockFam n) :
    F_raw_vanishes (n := n) T_fam ↔
      F_packed_vanishes (n := n) ((blockFamEquivRVec n) T_fam) := by
  convert Packaging.F_packed_vanishes_encode_iff_F_raw_vanishes' T_fam |> Iff.symm

/-! --------------------------------------------------------------------------
  Final theorems matching the original goal statement.
---------------------------------------------------------------------------- -/

/--
**Final theorem on a fixed generic `A`:** restates your main equivalence using `F_packed`.

This is the direct “if and only if” asked in the problem, but expressed as an explicit
map `ℝ^(81*n^4) → ℝ^N` with `N = N_out n`.
-/
theorem main_equivalence_packed_of_GoodA
    {n : ℕ} (A : CamTuple n) (h_n : n ≥ 5) (hA : GoodA (n := n) A) :
    ∀ lam : Fin n → Fin n → Fin n → Fin n → ℝ,
      valid_lambda (n := n) lam →
      let T_fam : BlockFam n :=
        block_scaling (n := n) lam (fun α β γ δ => Q_block A α β γ δ)
      -- packaged input vector
      let v_in : RVec (81 * n^4) := (blockFamEquivRVec n) T_fam
      (F_packed_vanishes (n := n) v_in ↔ separable_scaling (n := n) lam) := by
  intros lam h_lam
  apply Iff.intro;
  · convert mathbf_F_n_zero_implies_separable_scaling A h_n hA lam h_lam using 1;
    convert F_raw_vanishes_iff_F_packed_vanishes _ |> Iff.symm;
  · intro hsep
    apply F_raw_vanishes_iff_F_packed_vanishes (block_scaling lam (fun α β γ δ => Q_block A α β γ δ)) |>.mp;
    apply separable_scaling_implies_mathbf_F_n_zero A lam hsep

/--
**Zariski-generic version:** for `n ≥ 5`, Zariski-generic `A` satisfy the packaged equivalence.
This is the Lean statement that most closely matches the original “generic A” hypothesis.
-/
theorem main_equivalence_packed_Zariski_generic
    {n : ℕ} (h_n5 : n ≥ 5) :
    ZariskiGeneric (n := n) (fun A : CamTuple n =>
      ∀ lam : Fin n → Fin n → Fin n → Fin n → ℝ,
        valid_lambda (n := n) lam →
        let T_fam : BlockFam n :=
          block_scaling (n := n) lam (fun α β γ δ => Q_block A α β γ δ)
        let v_in : RVec (81 * n^4) := (blockFamEquivRVec n) T_fam
        (F_packed_vanishes (n := n) v_in ↔ separable_scaling (n := n) lam)
    ) := by
  convert main_Zariski_generic h_n5 ( by linarith ) using 1;
  funext A; simp [main_theorem_equivalence];
  congr! 3;
  convert F_raw_vanishes_iff_F_packed_vanishes _ |> Iff.symm

/--
**Existence statement phrased like the problem:**
There exists a map `F_packed n : ℝ^(81*n^4) → ℝ^N` (here `N = N_out n`) that is
independent of `A`, with the desired “vanish iff separable scaling” property
holding Zariski-generically in `A`.

This is the closest direct analogue of:

> “Does there exist a polynomial map `F : ℝ^(81n^4) → ℝ^N` … ?”
-/
theorem exists_F_packed_satisfying_goal
    {n : ℕ} (h_n5 : n ≥ 5) :
    ∃ (F : RVec (81 * n^4) → RVec (N_out n)),
      (F = F_packed n) ∧
      ZariskiGeneric (n := n) (fun A : CamTuple n =>
        ∀ lam : Fin n → Fin n → Fin n → Fin n → ℝ,
          valid_lambda (n := n) lam →
          let T_fam : BlockFam n :=
            block_scaling (n := n) lam (fun α β γ δ => Q_block A α β γ δ)
          let v_in : RVec (81 * n^4) := (blockFamEquivRVec n) T_fam
          ( (∀ i : Fin (N_out n), F v_in i = 0) ↔ separable_scaling (n := n) lam )
      ) := by
  refine' ⟨ _, rfl, _ ⟩;
  convert main_equivalence_packed_Zariski_generic h_n5 using 1

/-
Optional (if you want to explicitly advertise degree independence):

You can state: each coordinate is a polynomial of degree 5 in the input entries.

This requires a chosen notion of “polynomial map” in Lean. One convenient representation is:
`Fin N → MvPolynomial (Fin m) ℝ`, i.e. a tuple of coordinate polynomials in `m` variables.
I’m only stating the lemma skeleton here.
-/

/-- A skeleton notion: a polynomial map `ℝ^m → ℝ^N` encoded by coordinate polynomials. -/
def PolyMap (m N : ℕ) := Fin N → MvPolynomial (Fin m) ℝ

/-- Evaluate a polynomial map at a point. -/
noncomputable def PolyMap.eval {m N : ℕ} (P : PolyMap m N) (x : RVec m) : RVec N :=
  fun i => (P i).eval x

theorem det_totalDegree_le_five {σ : Type*} (M : Matrix (Fin 5) (Fin 5) (MvPolynomial σ ℝ)) (h : ∀ i j, (M i j).totalDegree ≤ 1) : (Matrix.det M).totalDegree ≤ 5 := by
  classical
  -- expand determinant using the Leibniz formula
  rw [Matrix.det_apply']
  -- bound totalDegree of the sum by the supremum of the totalDegrees of its terms
  refine le_trans
    (MvPolynomial.totalDegree_finset_sum (s := (Finset.univ : Finset (Equiv.Perm (Fin 5))))
      (f := fun τ : Equiv.Perm (Fin 5) =>
        (↑↑(Equiv.Perm.sign τ) : MvPolynomial σ ℝ) * ∏ i : Fin 5, M (τ i) i)) ?_
  -- it suffices to bound each summand by 5
  refine (Finset.sup_le_iff).2 ?_
  intro τ hτ
  -- totalDegree of a product is subadditive
  have hmul :
      ((↑↑(Equiv.Perm.sign τ) : MvPolynomial σ ℝ) * ∏ i : Fin 5, M (τ i) i).totalDegree
        ≤ (↑↑(Equiv.Perm.sign τ) : MvPolynomial σ ℝ).totalDegree
            + (∏ i : Fin 5, M (τ i) i).totalDegree := by
    simpa using
      (MvPolynomial.totalDegree_mul
        (a := (↑↑(Equiv.Perm.sign τ) : MvPolynomial σ ℝ))
        (b := ∏ i : Fin 5, M (τ i) i))
  -- the sign is a constant polynomial, hence has totalDegree 0
  have hconst : (↑↑(Equiv.Perm.sign τ) : MvPolynomial σ ℝ).totalDegree = 0 := by
    simpa using
      (MvPolynomial.totalDegree_C (σ := σ) (R := ℝ)
        (a := (↑↑(Equiv.Perm.sign τ) : ℝ)))
  -- bound the totalDegree of the product term
  have hprod : (∏ i : Fin 5, M (τ i) i).totalDegree ≤ 5 := by
    refine le_trans
      (MvPolynomial.totalDegree_finset_prod (s := (Finset.univ : Finset (Fin 5)))
        (f := fun i : Fin 5 => M (τ i) i)) ?_
    -- rewrite the RHS as a plain sum over `Fin 5`
    have hsum' : (∑ i : Fin 5, (M (τ i) i).totalDegree) ≤ 5 := by
      have hsum : (∑ i : Fin 5, (M (τ i) i).totalDegree) ≤ ∑ _i : Fin 5, (1 : ℕ) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        simpa using h (τ i) i
      have hones : (∑ _i : Fin 5, (1 : ℕ)) = 5 := by
        simpa using (Fin.sum_const (n := 5) (b := (1 : ℕ)))
      exact le_trans hsum (by simpa [hones])
    simpa using hsum'
  -- conclude using `hconst` and `hprod`
  have hsumdeg :
      (↑↑(Equiv.Perm.sign τ) : MvPolynomial σ ℝ).totalDegree + (∏ i : Fin 5, M (τ i) i).totalDegree ≤ 5 := by
    simpa [hconst] using hprod
  exact le_trans hmul hsumdeg

noncomputable def entryVarIndex (n : ℕ) (idx : MinorIndices n) (r c : Fin 5) : Fin (81 * n ^ 4) :=
  let rowMap := idx.rows.orderEmbOfFin idx.h_rows
  let colMap := idx.cols.orderEmbOfFin idx.h_cols
  let i : Fin (3 * n) := rowMap r
  let j : {k // k ≠ idx.t} → Fin (3 * n) := colMap c
  let bigIdx := combine_indices (I_3n n) idx.t i j
  let α : Fin 4 → Fin n := fun k => inv_iota_alpha (n := n) (bigIdx k)
  let inner : Fin 4 → Fin 3 := fun k => inv_iota_i (n := n) (bigIdx k)
  DomIdx_equiv_fin n ⟨α 0, α 1, α 2, α 3, inner⟩

noncomputable def F_raw_coord_poly (n : ℕ) (idx : MinorIndices n) : MvPolynomial (Fin (81 * n ^ 4)) ℝ :=
  Matrix.det (fun r c : Fin 5 => MvPolynomial.X (entryVarIndex n idx r c))

theorem F_raw_coord_poly_eval (n : ℕ) (idx : MinorIndices n) : ∀ x, (F_raw_coord_poly n idx).eval x = F_raw n ((blockFamEquivRVec n).symm x) idx := by
  intro x
  classical
  have hL : (F_raw_coord_poly n idx).eval x =
      Matrix.det (fun r c : Fin 5 => x (entryVarIndex n idx r c)) := by
    unfold F_raw_coord_poly
    -- push evaluation through determinant
    simpa [Matrix.map, MvPolynomial.eval_X] using
      (RingHom.map_det (MvPolynomial.eval x)
        (fun r c : Fin 5 => MvPolynomial.X (entryVarIndex n idx r c)))
  unfold F_raw mathbf_F_n F_n
  rw [hL]
  rfl

theorem F_raw_coord_poly_totalDegree_le_five (n : ℕ) (idx : MinorIndices n) : (F_raw_coord_poly n idx).totalDegree ≤ 5 := by
  classical
  unfold F_raw_coord_poly
  refine det_totalDegree_le_five (M := fun r c : Fin 5 => MvPolynomial.X (entryVarIndex n idx r c)) ?_
  intro i j
  simpa using (show (MvPolynomial.X (entryVarIndex n idx i j) : MvPolynomial (Fin (81 * n ^ 4)) ℝ).totalDegree ≤ 1 from by
    simpa [MvPolynomial.totalDegree_X] )

noncomputable def outEquivRVec_canonical (n : ℕ) : (MinorIndices n → ℝ) ≃ RVec (N_out n) :=
  Equiv.arrowCongr (Fintype.equivFin (MinorIndices n)) (Equiv.refl ℝ)

noncomputable def F_packed_canonical (n : ℕ) : RVec (81 * n^4) → RVec (N_out n) :=
  fun v =>
    let T_fam : BlockFam n := (blockFamEquivRVec n).symm v
    let outFun : MinorIndices n → ℝ := F_raw n T_fam
    (outEquivRVec_canonical n) outFun

theorem outEquivRVec_canonical_apply (n : ℕ) (outFun : MinorIndices n → ℝ) (i : Fin (N_out n)) :
  (outEquivRVec_canonical n) outFun i = outFun ((Fintype.equivFin (MinorIndices n)).symm i) := by
  classical
  simp [outEquivRVec_canonical, Equiv.arrowCongr_apply]
  rfl

theorem F_packed_canonical_is_polynomial_degree_le_five (n : ℕ) :
    ∃ (P : PolyMap (81 * n^4) (N_out n)),
      (∀ x, PolyMap.eval P x = F_packed_canonical n x) ∧
      (∀ i, (P i).totalDegree ≤ 5) := by
  classical
  let P : PolyMap (81 * n^4) (N_out n) :=
    fun i => F_raw_coord_poly n ((Fintype.equivFin (MinorIndices n)).symm i)
  refine ⟨P, ?_, ?_⟩
  · intro x
    ext i
    simp [PolyMap.eval, P]
    rw [F_raw_coord_poly_eval (n := n) (idx := (Fintype.equivFin (MinorIndices n)).symm i) x]
    simp [F_packed_canonical, outEquivRVec_canonical_apply]
  · intro i
    simpa [P] using
      (F_raw_coord_poly_totalDegree_le_five (n := n)
        (idx := (Fintype.equivFin (MinorIndices n)).symm i))
