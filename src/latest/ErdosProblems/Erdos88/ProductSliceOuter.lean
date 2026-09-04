import ErdosProblems.Erdos88.GaussianFourierComparison
import ErdosProblems.Erdos88.GaussianRobustRank
import ErdosProblems.Erdos88.BoundedWindowAnalytic

open scoped BigOperators

namespace Erdos88.GaussianQuadratic

lemma norm_expect_finTuple_le_of_head
    {K : ℕ} {Omega : Fin (K + 1) → Type*}
    [∀ k, Fintype (Omega k)] [∀ k, Nonempty (Omega k)]
    (g : (∀ k, Omega k) → ℂ) {B : ℝ}
    (h : ∀ tail : ∀ k : Fin K, Omega k.succ,
      ‖𝔼 x0 : Omega 0, g (Fin.cons x0 tail)‖ ≤ B) :
    ‖𝔼 x : ∀ k, Omega k, g x‖ ≤ B := by
  let e := Fin.consEquiv Omega
  have hsplit :
      (𝔼 x : ∀ k, Omega k, g x) =
        𝔼 p : Omega 0 × (∀ k : Fin K, Omega k.succ),
          g (Fin.cons p.1 p.2) := by
    apply Fintype.expect_equiv e.symm
    intro x
    simp [e]
  rw [hsplit, ← Finset.univ_product_univ, Finset.expect_product,
    Finset.expect_comm]
  calc
    ‖𝔼 tail : ∀ k : Fin K, Omega k.succ,
        𝔼 x0 : Omega 0, g (Fin.cons x0 tail)‖ ≤
        𝔼 tail : ∀ k : Fin K, Omega k.succ,
          ‖𝔼 x0 : Omega 0, g (Fin.cons x0 tail)‖ :=
      RCLike.norm_expect_le (K := ℂ) (E := ℂ)
    _ ≤ 𝔼 _tail : ∀ k : Fin K, Omega k.succ, B := by
      apply Finset.expect_le_expect
      intro tail _
      exact h tail
    _ = B := Fintype.expect_const B

lemma norm_finiteCharacteristic_productSlice_le_of_head
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K : ℕ} (P : Erdos88.BooleanSlices.BucketPartition alpha (Fin (K + 1)))
    (ell : Fin (K + 1) → ℕ)
    [Nonempty (Erdos88.BooleanSlices.ProductSlicePoint P ell)]
    [∀ k, Nonempty (Erdos88.BooleanSlices.BooleanSlicePoint (P.fiber k) (ell k))]
    (X : Erdos88.BooleanSlices.ProductSlicePoint P ell → ℝ)
    (t B : ℝ)
    (h : ∀ tail : ∀ k : Fin K,
        Erdos88.BooleanSlices.BooleanSlicePoint (P.fiber k.succ) (ell k.succ),
      ‖Erdos88.BooleanSlices.finiteCharacteristic
          (fun S0 : Erdos88.BooleanSlices.BooleanSlicePoint (P.fiber 0) (ell 0) ↦
            X ((Erdos88.BooleanSlices.productSliceEquiv P ell).symm
              (Fin.cons S0 tail))) t‖ ≤ B) :
    ‖Erdos88.BooleanSlices.finiteCharacteristic X t‖ ≤ B := by
  rw [Erdos88.BooleanSlices.finiteCharacteristic,
    Erdos88.BooleanSlices.productSlice_expect_equiv]
  apply norm_expect_finTuple_le_of_head
  intro tail
  simpa only [Erdos88.BooleanSlices.finiteCharacteristic] using h tail

lemma sum_signOfSet_eq {q : ℕ} (S : Finset (Fin q)) :
    (∑ i, Erdos88.BooleanSlices.signOfSet S i) =
      2 * (S.card : ℝ) - q := by
  classical
  simp only [Erdos88.BooleanSlices.signOfSet]
  rw [Finset.sum_ite]
  simp
  have hcardNat :
      S.card + ((Finset.univ : Finset (Fin q)).filter fun i ↦ i ∉ S).card = q := by
    simpa using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin q))) (p := fun i ↦ i ∈ S)
  have hcardReal :
      (S.card : ℝ) +
          (((Finset.univ : Finset (Fin q)).filter fun i ↦ i ∉ S).card : ℝ) = q := by
    exact_mod_cast hcardNat
  linarith

lemma sliceQuadratic_eq_of_matrix_add_row_col
    {q ell : ℕ} (H : SimpleGraph (Fin q))
    (f0 : ℝ) (f : Fin q → ℝ) (F : Matrix (Fin q) (Fin q) ℝ)
    (r c : Fin q → ℝ) (S : Finset (Fin q)) (hS : S.card = ell)
    (hF : ∀ i j, F i j = Erdos88.GraphQuadratic.graphSliceMatrix H i j + r i + c j) :
    Erdos88.BooleanSlices.sliceQuadratic f0 f F S =
      Erdos88.BooleanSlices.sliceQuadratic f0
        (fun i ↦ f i + (((2 * ell : ℕ) : ℝ) - (q : ℝ)) * (r i + c i))
        (Erdos88.GraphQuadratic.graphSliceMatrix H) S := by
  classical
  let x := Erdos88.BooleanSlices.signOfSet S
  let z : ℝ := ((2 * ell : ℕ) : ℝ) - (q : ℝ)
  have hx : (∑ i, x i) = z := by
    dsimp only [x, z]
    rw [sum_signOfSet_eq, hS]
    push_cast
    ring
  have hquad :
      Erdos88.BooleanSlices.quadraticPart F x =
        Erdos88.BooleanSlices.quadraticPart
            (Erdos88.GraphQuadratic.graphSliceMatrix H) x +
          z * (∑ i, (r i + c i) * x i) := by
    have hr :
        (∑ i, ∑ j, x i * r i * x j) =
          (∑ i, r i * x i) * (∑ j, x j) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hc :
        (∑ i, ∑ j, x i * c j * x j) =
          (∑ i, x i) * (∑ j, c j * x j) := by
      calc
        (∑ i, ∑ j, x i * c j * x j) =
            ∑ i, ∑ j, x i * (c j * x j) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              ring
        _ = ∑ i, x i * (∑ j, c j * x j) := by
              simp_rw [Finset.mul_sum]
        _ = (∑ i, x i) * (∑ j, c j * x j) := by
              rw [Finset.sum_mul]
    simp only [Erdos88.BooleanSlices.quadraticPart]
    simp_rw [hF]
    calc
      (∑ i, ∑ j,
          (x i * (Erdos88.GraphQuadratic.graphSliceMatrix H i j + r i + c j)) * x j) =
          (∑ i, ∑ j,
            (x i * Erdos88.GraphQuadratic.graphSliceMatrix H i j) * x j) +
            (∑ i, r i * x i) * (∑ j, x j) +
            (∑ i, x i) * (∑ j, c j * x j) := by
              simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
              rw [hr, hc]
      _ = (∑ i, ∑ j,
            (x i * Erdos88.GraphQuadratic.graphSliceMatrix H i j) * x j) +
          z * (∑ i, (r i + c i) * x i) := by
            rw [hx]
            simp_rw [add_mul, Finset.sum_add_distrib]
            ring
  simp only [Erdos88.BooleanSlices.sliceQuadratic,
    Erdos88.BooleanSlices.quadraticPolynomial,
    Erdos88.BooleanSlices.linearPart]
  change f0 + (∑ i, f i * x i) +
      Erdos88.BooleanSlices.quadraticPart F x =
    f0 + (∑ i, (f i + z * (r i + c i)) * x i) +
      Erdos88.BooleanSlices.quadraticPart
        (Erdos88.GraphQuadratic.graphSliceMatrix H) x
  rw [hquad]
  simp_rw [add_mul, Finset.sum_add_distrib]
  have hzsum :
      (∑ i, z * (r i + c i) * x i) =
        z * (∑ i, r i * x i) + z * (∑ i, c i * x i) := by
    calc
      (∑ i, z * (r i + c i) * x i) =
          ∑ i, (z * r i * x i + z * c i * x i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = (∑ i, z * r i * x i) + (∑ i, z * c i * x i) :=
        Finset.sum_add_distrib
      _ = z * (∑ i, r i * x i) + z * (∑ i, c i * x i) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        simp only [mul_assoc]
  rw [hzsum]
  ring

lemma exists_bucketCenteredAdjacency_add_row_col_on_bucket
    {n m s : ℕ} (bucket : Fin n → Fin m) (G : SimpleGraph (Fin n))
    (k : Fin m) (hne : ∃ a, bucket a = k) :
    ∃ r c : Fin n → ℝ, ∀ i j, bucket i = k → bucket j = k →
      bucketCenteredAdjacency bucket s G i j =
        Erdos88.GraphQuadratic.graphSliceMatrix G i j + r i + c j := by
  classical
  obtain ⟨a, ha⟩ := hne
  let M := Erdos88.RobustRank.graphAdjacencyMatrix G
  let Q := bucketProjectionMatrix bucket s
  let r : Fin n → ℝ := fun i ↦
    -(1 / 8 : ℝ) * (M * Q) i a +
      (1 / 8 : ℝ) * (Q * M * Q) a a
  let c : Fin n → ℝ := fun j ↦
    -(1 / 8 : ℝ) * (Q * M) a j
  refine ⟨r, c, ?_⟩
  intro i j hi hj
  have hja : bucket j = bucket a := hj.trans ha.symm
  have hia : bucket i = bucket a := hi.trans ha.symm
  have hMQ := mul_bucketProjectionMatrix_col_eq
    (s := s) bucket M hja i
  have hQM := bucketProjectionMatrix_mul_row_eq
    (s := s) bucket M hia j
  have hQMQ : (Q * M * Q) i j = (Q * M * Q) a a :=
    (bucketProjectionMatrix_mul_mul_row_eq
      (s := s) bucket M hia j).trans
      (bucketProjectionMatrix_mul_mul_col_eq
        (s := s) bucket M hja a)
  rw [bucketCenteredAdjacency]
  simp only [bucketLowRankPart, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.add_apply]
  change (1 / 8 : ℝ) *
      (M i j - ((M * Q) i j + (Q * M) i j - (Q * M * Q) i j)) =
    Erdos88.GraphQuadratic.graphSliceMatrix G i j + r i + c j
  rw [hMQ, hQM, hQMQ]
  dsimp only [r, c, M]
  rw [Erdos88.GraphQuadratic.graphSliceMatrix]
  ring

noncomputable def splitQuadraticConstant
    {n q : ℕ} {R : Type*} [Fintype R]
    (e : Fin n ≃ Fin q ⊕ R) (f0 : ℝ) (f : Fin n → ℝ)
    (F : Matrix (Fin n) (Fin n) ℝ) (d : R → ℝ) : ℝ :=
  f0 + (∑ b, f (e.symm (Sum.inr b)) * d b) +
    ∑ b, ∑ c,
      (d b * F (e.symm (Sum.inr b)) (e.symm (Sum.inr c))) * d c

noncomputable def splitQuadraticLinear
    {n q : ℕ} {R : Type*} [Fintype R]
    (e : Fin n ≃ Fin q ⊕ R) (f : Fin n → ℝ)
    (F : Matrix (Fin n) (Fin n) ℝ) (d : R → ℝ) (a : Fin q) : ℝ :=
  f (e.symm (Sum.inl a)) +
    (∑ b, F (e.symm (Sum.inl a)) (e.symm (Sum.inr b)) * d b) +
    ∑ b, d b * F (e.symm (Sum.inr b)) (e.symm (Sum.inl a))

noncomputable def splitQuadraticMatrix
    {n q : ℕ} {R : Type*}
    (e : Fin n ≃ Fin q ⊕ R) (F : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin q) (Fin q) ℝ :=
  fun a b ↦ F (e.symm (Sum.inl a)) (e.symm (Sum.inl b))

lemma quadraticPolynomial_split_equiv
    {n q : ℕ} {R : Type*} [Fintype R]
    (e : Fin n ≃ Fin q ⊕ R) (f0 : ℝ) (f : Fin n → ℝ)
    (F : Matrix (Fin n) (Fin n) ℝ) (d : R → ℝ) (x : Fin q → ℝ) :
    Erdos88.BooleanSlices.quadraticPolynomial f0 f F
        (fun i ↦ Sum.elim x d (e i)) =
      Erdos88.BooleanSlices.quadraticPolynomial
        (splitQuadraticConstant e f0 f F d)
        (splitQuadraticLinear e f F d)
        (splitQuadraticMatrix e F) x := by
  classical
  have hlin :
      (∑ i : Fin n, f i * Sum.elim x d (e i)) =
        (∑ a : Fin q, f (e.symm (Sum.inl a)) * x a) +
          ∑ b : R, f (e.symm (Sum.inr b)) * d b := by
    calc
      (∑ i : Fin n, f i * Sum.elim x d (e i)) =
          ∑ z : Fin q ⊕ R, f (e.symm z) * Sum.elim x d z := by
            simpa only [e.symm_apply_apply] using
              e.sum_comp (fun z : Fin q ⊕ R ↦
                f (e.symm z) * Sum.elim x d z)
      _ = _ := by
        rw [Fintype.sum_sum_type]
        rfl
  have hquad :
      (∑ i : Fin n, ∑ j : Fin n,
          (Sum.elim x d (e i) * F i j) * Sum.elim x d (e j)) =
        (∑ a : Fin q, ∑ b : Fin q,
            (x a * F (e.symm (Sum.inl a)) (e.symm (Sum.inl b))) * x b) +
          (∑ a : Fin q, ∑ b : R,
            (x a * F (e.symm (Sum.inl a)) (e.symm (Sum.inr b))) * d b) +
          (∑ a : R, ∑ b : Fin q,
            (d a * F (e.symm (Sum.inr a)) (e.symm (Sum.inl b))) * x b) +
          (∑ a : R, ∑ b : R,
            (d a * F (e.symm (Sum.inr a)) (e.symm (Sum.inr b))) * d b) := by
    calc
      (∑ i : Fin n, ∑ j : Fin n,
          (Sum.elim x d (e i) * F i j) * Sum.elim x d (e j)) =
          ∑ z : Fin q ⊕ R, ∑ w : Fin q ⊕ R,
            (Sum.elim x d z * F (e.symm z) (e.symm w)) * Sum.elim x d w := by
              calc
                _ = ∑ i : Fin n, ∑ w : Fin q ⊕ R,
                    (Sum.elim x d (e i) * F i (e.symm w)) * Sum.elim x d w := by
                      apply Finset.sum_congr rfl
                      intro i _
                      simpa only [e.symm_apply_apply] using
                        e.sum_comp (fun w : Fin q ⊕ R ↦
                          (Sum.elim x d (e i) * F i (e.symm w)) *
                            Sum.elim x d w)
                _ = _ := by
                      simpa only [e.symm_apply_apply] using
                        e.sum_comp (fun z : Fin q ⊕ R ↦
                          ∑ w : Fin q ⊕ R,
                            (Sum.elim x d z * F (e.symm z) (e.symm w)) *
                              Sum.elim x d w)
      _ = _ := by
        rw [Fintype.sum_sum_type]
        simp_rw [Fintype.sum_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        ring
  have hcrossLR :
      (∑ a : Fin q, ∑ b : R,
          (x a * F (e.symm (Sum.inl a)) (e.symm (Sum.inr b))) * d b) =
        ∑ a : Fin q,
          (∑ b : R, F (e.symm (Sum.inl a)) (e.symm (Sum.inr b)) * d b) * x a := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hcrossRL :
      (∑ a : R, ∑ b : Fin q,
          (d a * F (e.symm (Sum.inr a)) (e.symm (Sum.inl b))) * x b) =
        ∑ b : Fin q,
          (∑ a : R, d a * F (e.symm (Sum.inr a)) (e.symm (Sum.inl b))) * x b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.sum_mul]
  simp only [Erdos88.BooleanSlices.quadraticPolynomial,
    Erdos88.BooleanSlices.linearPart, Erdos88.BooleanSlices.quadraticPart]
  rw [hlin, hquad]
  simp only [splitQuadraticConstant, splitQuadraticLinear, splitQuadraticMatrix]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [hcrossLR, hcrossRL]
  ring

noncomputable def booleanSlicePointSubsetEquiv
    {alpha beta : Type*} [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (I : Finset alpha) (ell : ℕ) (e : (I : Set alpha) ≃ beta) :
    Erdos88.BooleanSlices.BooleanSlicePoint I ell ≃
      Erdos88.BooleanSlices.BooleanSlicePoint (Finset.univ : Finset beta) ell where
  toFun S :=
    ⟨(Erdos88.BooleanSlices.finsetLift I S.1).map e.toEmbedding,
      Erdos88.BooleanSlices.mem_booleanSlice.mpr ⟨Finset.subset_univ _, by
        rw [Finset.card_map,
          Erdos88.BooleanSlices.card_finsetLift I S.1
            (Erdos88.BooleanSlices.mem_booleanSlice.mp S.2).1,
          (Erdos88.BooleanSlices.mem_booleanSlice.mp S.2).2]⟩⟩
  invFun T :=
    ⟨(T.1.map e.symm.toEmbedding).map
        (Function.Embedding.subtype fun i : alpha ↦ i ∈ I),
      Erdos88.BooleanSlices.mem_booleanSlice.mpr ⟨by
        intro i hi
        rw [Finset.mem_map] at hi
        obtain ⟨j, _hj, rfl⟩ := hi
        exact j.property, by
        rw [Finset.card_map, Finset.card_map,
          (Erdos88.BooleanSlices.mem_booleanSlice.mp T.2).2]⟩⟩
  left_inv S := by
    apply Subtype.ext
    have hSI := (Erdos88.BooleanSlices.mem_booleanSlice.mp S.2).1
    ext i
    simp only [SetLike.coe_sort_coe, Finset.mem_map, Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_map_mk,
    Function.Embedding.subtype_apply, Subtype.exists, exists_and_right, exists_eq_right]
    intro hi
    exact hSI hi
  right_inv T := by
    apply Subtype.ext
    ext b
    simp [Erdos88.BooleanSlices.finsetLift]

lemma mem_booleanSlicePointSubsetEquiv_symm
    {alpha beta : Type*} [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (I : Finset alpha) (ell : ℕ) (e : (I : Set alpha) ≃ beta)
    (S : Erdos88.BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset beta) ell) (i : (I : Set alpha)) :
    i.1 ∈ ((booleanSlicePointSubsetEquiv I ell e).symm S).1 ↔ e i ∈ S.1 := by
  let S0 := (booleanSlicePointSubsetEquiv I ell e).symm S
  have hmap := congrArg Subtype.val
    ((booleanSlicePointSubsetEquiv I ell e).apply_symm_apply S)
  change (Erdos88.BooleanSlices.finsetLift I S0.1).map e.toEmbedding = S.1 at hmap
  rw [← hmap, Finset.mem_map]
  constructor
  · intro hi
    exact ⟨i, by
      simp [Erdos88.BooleanSlices.finsetLift, S0, hi], rfl⟩
  · rintro ⟨j, hj, hji⟩
    have : j = i := e.injective hji
    subst j
    exact (Finset.mem_filter.mp hj).2

lemma mem_booleanSlicePointSubsetEquiv
    {alpha beta : Type*} [Fintype alpha] [DecidableEq alpha]
    [Fintype beta] [DecidableEq beta]
    (I : Finset alpha) (ell : ℕ) (e : (I : Set alpha) ≃ beta)
    (S : Erdos88.BooleanSlices.BooleanSlicePoint I ell)
    (i : (I : Set alpha)) :
    e i ∈ (booleanSlicePointSubsetEquiv I ell e S).1 ↔ i.1 ∈ S.1 := by
  change e i ∈ (Erdos88.BooleanSlices.finsetLift I S.1).map e.toEmbedding ↔ _
  rw [Finset.mem_map]
  constructor
  · rintro ⟨j, hj, hji⟩
    have : j = i := e.injective hji
    subst j
    exact (Finset.mem_filter.mp hj).2
  · intro hi
    exact ⟨i, by
      simp [Erdos88.BooleanSlices.finsetLift, hi], rfl⟩

lemma exists_split_bucketCenteredMatrix_add_row_col
    {n m q s : ℕ} {R : Type*}
    (bucket : Fin n → Fin m) (G : SimpleGraph (Fin n)) (k : Fin m)
    (e : Fin n ≃ Fin q ⊕ R) (H : SimpleGraph (Fin q))
    (a0 : Fin q)
    (hleft : ∀ a, bucket (e.symm (Sum.inl a)) = k)
    (hgraph : ∀ a b,
      G.Adj (e.symm (Sum.inl a)) (e.symm (Sum.inl b)) ↔ H.Adj a b) :
    ∃ r c : Fin q → ℝ, ∀ a b,
      splitQuadraticMatrix e (bucketCenteredAdjacency bucket s G) a b =
        Erdos88.GraphQuadratic.graphSliceMatrix H a b + r a + c b := by
  classical
  obtain ⟨r0, c0, hlocal⟩ :=
    exists_bucketCenteredAdjacency_add_row_col_on_bucket
      (s := s) bucket G k ⟨e.symm (Sum.inl a0), hleft a0⟩
  refine ⟨fun a ↦ r0 (e.symm (Sum.inl a)),
    fun b ↦ c0 (e.symm (Sum.inl b)), ?_⟩
  intro a b
  rw [splitQuadraticMatrix,
    hlocal _ _ (hleft a) (hleft b)]
  congr 2
  rw [Erdos88.GraphQuadratic.graphSliceMatrix_apply,
    Erdos88.GraphQuadratic.graphSliceMatrix_apply]
  exact if_congr (hgraph a b) rfl rfl

noncomputable def inducedOverFin {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) :
    SimpleGraph (Fin I.card) :=
  (G.induce (I : Set (Fin n))).overFin
    (Erdos88.card_subtype_coe_finset I)

noncomputable def inducedOverFinIso {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) :
    G.induce (I : Set (Fin n)) ≃g inducedOverFin G I :=
  (G.induce (I : Set (Fin n))).overFinIso
    (Erdos88.card_subtype_coe_finset I)

noncomputable def graphFinsetSplitEquiv {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) :
    Fin n ≃ Fin I.card ⊕ ((I : Set (Fin n))ᶜ : Set (Fin n)) :=
  (Equiv.Set.sumCompl (I : Set (Fin n))).symm.trans
    ((inducedOverFinIso G I).toEquiv.sumCongr (Equiv.refl _))

lemma graphFinsetSplitEquiv_symm_inl {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) (a : Fin I.card) :
    (graphFinsetSplitEquiv G I).symm (Sum.inl a) =
      (inducedOverFinIso G I).symm a := by
  change (Equiv.Set.sumCompl (I : Set (Fin n)))
      (Sum.inl ((inducedOverFinIso G I).symm a)) = _
  exact Equiv.Set.sumCompl_apply_inl _ _

lemma graphFinsetSplitEquiv_left_mem {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) (a : Fin I.card) :
    (graphFinsetSplitEquiv G I).symm (Sum.inl a) ∈ I := by
  rw [graphFinsetSplitEquiv_symm_inl]
  exact ((inducedOverFinIso G I).symm a).property

lemma graphFinsetSplitEquiv_left_adj {n : ℕ}
    (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) (a b : Fin I.card) :
    G.Adj ((graphFinsetSplitEquiv G I).symm (Sum.inl a))
        ((graphFinsetSplitEquiv G I).symm (Sum.inl b)) ↔
      (inducedOverFin G I).Adj a b := by
  rw [graphFinsetSplitEquiv_symm_inl,
    graphFinsetSplitEquiv_symm_inl]
  exact (inducedOverFinIso G I).symm.map_rel_iff

lemma exists_perturbedEdgePolynomial_of_graphSlice
    {q : ℕ} (H : SimpleGraph (Fin q)) (f0 : ℝ) (f : Fin q → ℝ) :
    letI : DecidableRel H.Adj := fun _ _ ↦ Classical.propDecidable _
    ∃ e0 : ℝ, ∃ coeff : Fin q → ℝ, ∀ S : Finset (Fin q),
      Erdos88.BooleanSlices.sliceQuadratic f0 f
          (Erdos88.GraphQuadratic.graphSliceMatrix H) S =
        Erdos88.Probability.perturbedEdgePolynomial H e0 coeff S := by
  classical
  let coeff : Fin q → ℝ := fun i ↦ 2 * f i - (H.degree i : ℝ) / 2
  let e0 : ℝ := f0 - (H.edgeFinset.card : ℝ) / 4 - (∑ i, coeff i) / 2
  refine ⟨e0, coeff, ?_⟩
  intro S
  have hlin : Erdos88.GraphQuadratic.graphSliceLinear H coeff = f := by
    funext i
    simp only [Erdos88.GraphQuadratic.graphSliceLinear, coeff]
    ring
  have hconst : Erdos88.GraphQuadratic.graphSliceConstant H e0 coeff = f0 := by
    simp only [Erdos88.GraphQuadratic.graphSliceConstant, e0]
    ring
  rw [← hlin, ← hconst]
  exact Erdos88.GraphQuadratic.sliceQuadratic_graph_coefficients H e0 coeff S

lemma exists_perturbedEdgePolynomial_of_splitQuadratic
    {n q ell : ℕ} {R : Type*} [Fintype R]
    (e : Fin n ≃ Fin q ⊕ R) (H : SimpleGraph (Fin q))
    (f0 : ℝ) (f : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ)
    (d : R → ℝ) (r c : Fin q → ℝ)
    (hF : ∀ a b, splitQuadraticMatrix e F a b =
      Erdos88.GraphQuadratic.graphSliceMatrix H a b + r a + c b) :
    letI : DecidableRel H.Adj := fun _ _ ↦ Classical.propDecidable _
    ∃ e0 : ℝ, ∃ coeff : Fin q → ℝ,
      ∀ S : Erdos88.BooleanSlices.BooleanSlicePoint
          (Finset.univ : Finset (Fin q)) ell,
        Erdos88.BooleanSlices.quadraticPolynomial f0 f F
            (fun i ↦ Sum.elim
              (Erdos88.BooleanSlices.signOfSet S.1) d (e i)) =
          Erdos88.Probability.perturbedEdgePolynomial H e0 coeff S.1 := by
  classical
  let f0' := splitQuadraticConstant e f0 f F d
  let f' := splitQuadraticLinear e f F d
  let F' := splitQuadraticMatrix e F
  let z : ℝ := ((2 * ell : ℕ) : ℝ) - (q : ℝ)
  let f'' : Fin q → ℝ := fun a ↦ f' a + z * (r a + c a)
  obtain ⟨e0, coeff, hpert⟩ :=
    exists_perturbedEdgePolynomial_of_graphSlice H f0' f''
  refine ⟨e0, coeff, ?_⟩
  intro S
  rw [quadraticPolynomial_split_equiv]
  change Erdos88.BooleanSlices.sliceQuadratic f0' f' F' S.1 = _
  rw [sliceQuadratic_eq_of_matrix_add_row_col H f0' f' F' r c S.1
    (Erdos88.BooleanSlices.mem_booleanSlice.mp S.2).2 hF]
  change Erdos88.BooleanSlices.sliceQuadratic f0' f''
      (Erdos88.GraphQuadratic.graphSliceMatrix H) S.1 = _
  exact hpert S.1

noncomputable def productSliceTailUnion
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K : ℕ} (P : Erdos88.BooleanSlices.BucketPartition alpha (Fin (K + 1)))
    (ell : Fin (K + 1) → ℕ)
    (tail : ∀ k : Fin K,
      Erdos88.BooleanSlices.BooleanSlicePoint (P.fiber k.succ) (ell k.succ)) :
    Finset alpha :=
  Finset.univ.biUnion fun k : Fin K ↦ (tail k).1

lemma productSliceEquiv_symm_cons_val
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {K : ℕ} (P : Erdos88.BooleanSlices.BucketPartition alpha (Fin (K + 1)))
    (ell : Fin (K + 1) → ℕ)
    (S0 : Erdos88.BooleanSlices.BooleanSlicePoint (P.fiber 0) (ell 0))
    (tail : ∀ k : Fin K,
      Erdos88.BooleanSlices.BooleanSlicePoint (P.fiber k.succ) (ell k.succ)) :
    ((Erdos88.BooleanSlices.productSliceEquiv P ell).symm
        (Fin.cons S0 tail)).1 =
      S0.1 ∪ productSliceTailUnion P ell tail := by
  classical
  change (Finset.univ.biUnion fun k : Fin (K + 1) ↦
      ((Fin.cons S0 tail : ∀ h,
        Erdos88.BooleanSlices.BooleanSlicePoint (P.fiber h) (ell h)) k).1) =
    S0.1 ∪ productSliceTailUnion P ell tail
  ext i
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_union, productSliceTailUnion]
  constructor
  · rintro ⟨k, hik⟩
    cases k using Fin.cases with
    | zero => exact Or.inl hik
    | succ k => exact Or.inr ⟨k, hik⟩
  · rintro (hi | ⟨k, hik⟩)
    · exact ⟨0, hi⟩
    · exact ⟨k.succ, hik⟩

lemma exists_productSliceConditional_perturbed
    {n K s : ℕ}
    (P : Erdos88.BooleanSlices.BucketPartition (Fin n) (Fin (K + 1)))
    (ell : Fin (K + 1) → ℕ) (G : SimpleGraph (Fin n))
    (f0 : ℝ) (f : Fin n → ℝ)
    (tail : ∀ k : Fin K,
      Erdos88.BooleanSlices.BooleanSlicePoint (P.fiber k.succ) (ell k.succ))
    (hIpos : 0 < (P.fiber 0).card) :
    let H := inducedOverFin G (P.fiber 0)
    letI : DecidableRel H.Adj := fun _ _ ↦ Classical.propDecidable _
    ∃ e0 : ℝ, ∃ coeff : Fin (P.fiber 0).card → ℝ,
      ∀ S0 : Erdos88.BooleanSlices.BooleanSlicePoint (P.fiber 0) (ell 0),
        Erdos88.BooleanSlices.sliceQuadratic f0 f
            (bucketCenteredAdjacency P.bucket s G)
            ((Erdos88.BooleanSlices.productSliceEquiv P ell).symm
              (Fin.cons S0 tail)).1 =
          Erdos88.Probability.perturbedEdgePolynomial H e0 coeff
            (booleanSlicePointSubsetEquiv (P.fiber 0) (ell 0)
              (inducedOverFinIso G (P.fiber 0)).toEquiv S0).1 := by
  classical
  let I := P.fiber 0
  let H := inducedOverFin G I
  let eL := (inducedOverFinIso G I).toEquiv
  let e := graphFinsetSplitEquiv G I
  let E := booleanSlicePointSubsetEquiv I (ell 0) eL
  let T := productSliceTailUnion P ell tail
  let d : ((I : Set (Fin n))ᶜ : Set (Fin n)) → ℝ :=
    fun i ↦ Erdos88.BooleanSlices.signOfSet T i.1
  let a0 : Fin I.card := ⟨0, by simpa only [I] using hIpos⟩
  have hleft : ∀ a, P.bucket (e.symm (Sum.inl a)) = 0 := by
    intro a
    apply (P.mem_fiber 0 _).mp
    simpa only [I, e] using graphFinsetSplitEquiv_left_mem G I a
  have hgraph : ∀ a b,
      G.Adj (e.symm (Sum.inl a)) (e.symm (Sum.inl b)) ↔ H.Adj a b := by
    intro a b
    simpa only [H, e] using graphFinsetSplitEquiv_left_adj G I a b
  obtain ⟨r, c, hmatrix⟩ :=
    exists_split_bucketCenteredMatrix_add_row_col
      P.bucket G 0 e H a0 hleft hgraph
  obtain ⟨e0, coeff, hrep⟩ :=
    exists_perturbedEdgePolynomial_of_splitQuadratic
      (ell := ell 0) e H f0 f
        (bucketCenteredAdjacency P.bucket s G) d r c hmatrix
  refine ⟨e0, coeff, ?_⟩
  intro S0
  let S := E S0
  let W := (Erdos88.BooleanSlices.productSliceEquiv P ell).symm
    (Fin.cons S0 tail)
  have hW : W.1 = S0.1 ∪ T := by
    simpa only [W, T] using productSliceEquiv_symm_cons_val P ell S0 tail
  have hTnot : ∀ i, i ∈ I → i ∉ T := by
    intro i hiI hiT
    obtain ⟨k, _hk, hik⟩ := Finset.mem_biUnion.mp hiT
    have hikFiber : i ∈ P.fiber k.succ :=
      (Erdos88.BooleanSlices.mem_booleanSlice.mp (tail k).2).1 hik
    have hiBucket : P.bucket i = 0 := by
      exact (P.mem_fiber 0 i).mp (by simpa only [I] using hiI)
    have hikBucket : P.bucket i = k.succ := (P.mem_fiber k.succ i).mp hikFiber
    exact Fin.succ_ne_zero k (hikBucket.symm.trans hiBucket)
  have hS0sub : S0.1 ⊆ I := by
    simpa only [I] using
      (Erdos88.BooleanSlices.mem_booleanSlice.mp S0.2).1
  have hsign : ∀ i,
      Erdos88.BooleanSlices.signOfSet W.1 i =
        Sum.elim (Erdos88.BooleanSlices.signOfSet S.1) d (e i) := by
    intro i
    rw [hW]
    by_cases hiI : i ∈ I
    · have he : e i = Sum.inl (eL ⟨i, hiI⟩) := by
        change (graphFinsetSplitEquiv G I) i = _
        change ((inducedOverFinIso G I).toEquiv.sumCongr (Equiv.refl _))
          ((Equiv.Set.sumCompl (I : Set (Fin n))).symm i) = _
        rw [Equiv.Set.sumCompl_symm_apply_of_mem hiI]
        rfl
      rw [he]
      simp only [Sum.elim_inl]
      have hiT : i ∉ T := hTnot i hiI
      have hmem : eL ⟨i, hiI⟩ ∈ S.1 ↔ i ∈ S0.1 := by
        simpa only [S, E, eL] using
          mem_booleanSlicePointSubsetEquiv I (ell 0) eL S0 ⟨i, hiI⟩
      simp only [Erdos88.BooleanSlices.signOfSet, Finset.mem_union,
        hiT, or_false]
      exact if_congr hmem.symm rfl rfl
    · have he : e i = Sum.inr ⟨i, hiI⟩ := by
        change (graphFinsetSplitEquiv G I) i = _
        change ((inducedOverFinIso G I).toEquiv.sumCongr (Equiv.refl _))
          ((Equiv.Set.sumCompl (I : Set (Fin n))).symm i) = _
        rw [Equiv.Set.sumCompl_symm_apply_of_notMem hiI]
        rfl
      rw [he]
      simp only [Sum.elim_inr, d, Erdos88.BooleanSlices.signOfSet,
        Finset.mem_union]
      have hiS0 : i ∉ S0.1 := fun hi ↦ hiI (hS0sub hi)
      simp only [hiS0, false_or]
  change Erdos88.BooleanSlices.quadraticPolynomial f0 f
      (bucketCenteredAdjacency P.bucket s G)
      (Erdos88.BooleanSlices.signOfSet W.1) = _
  convert hrep S using 1
  apply congrArg
  funext i
  exact hsign i

/-- A uniform bound for all perturbed induced-edge polynomials on the first
bucket transfers verbatim to every conditional characteristic function of
the corresponding product-slice quadratic. -/
lemma norm_productSliceConditional_le_of_perturbed
    {n K s : ℕ}
    (P : Erdos88.BooleanSlices.BucketPartition (Fin n) (Fin (K + 1)))
    (ell : Fin (K + 1) → ℕ) (G : SimpleGraph (Fin n))
    (f0 : ℝ) (f : Fin n → ℝ)
    (tail : ∀ k : Fin K,
      Erdos88.BooleanSlices.BooleanSlicePoint (P.fiber k.succ) (ell k.succ))
    [Nonempty (Erdos88.BooleanSlices.BooleanSlicePoint (P.fiber 0) (ell 0))]
    (hIpos : 0 < (P.fiber 0).card) (t B : ℝ)
    (hbound : ∀ (e0 : ℝ) (coeff : Fin (P.fiber 0).card → ℝ),
      let E := booleanSlicePointSubsetEquiv (P.fiber 0) (ell 0)
        (inducedOverFinIso G (P.fiber 0)).toEquiv
      letI : Nonempty (Erdos88.BooleanSlices.BooleanSlicePoint
          (Finset.univ : Finset (Fin (P.fiber 0).card)) (ell 0)) :=
        Nonempty.map E inferInstance
      let H := inducedOverFin G (P.fiber 0)
      letI : DecidableRel H.Adj := fun _ _ ↦ Classical.propDecidable _
      ‖Erdos88.Fourier.finCharFun
          (Erdos88.BooleanSlices.BooleanSlicePoint
            (Finset.univ : Finset (Fin (P.fiber 0).card)) (ell 0))
          (fun S ↦ Erdos88.Probability.perturbedEdgePolynomial
            H e0 coeff S.1) t‖ ≤ B) :
    ‖Erdos88.BooleanSlices.finiteCharacteristic
        (fun S0 : Erdos88.BooleanSlices.BooleanSlicePoint
            (P.fiber 0) (ell 0) ↦
          Erdos88.BooleanSlices.sliceQuadratic f0 f
            (bucketCenteredAdjacency P.bucket s G)
            ((Erdos88.BooleanSlices.productSliceEquiv P ell).symm
              (Fin.cons S0 tail)).1) t‖ ≤ B := by
  classical
  let H := inducedOverFin G (P.fiber 0)
  let : DecidableRel H.Adj := fun _ _ ↦ Classical.propDecidable _
  let E := booleanSlicePointSubsetEquiv (P.fiber 0) (ell 0)
    (inducedOverFinIso G (P.fiber 0)).toEquiv
  let X : Erdos88.BooleanSlices.BooleanSlicePoint (P.fiber 0) (ell 0) → ℝ :=
    fun S0 ↦ Erdos88.BooleanSlices.sliceQuadratic f0 f
      (bucketCenteredAdjacency P.bucket s G)
      ((Erdos88.BooleanSlices.productSliceEquiv P ell).symm
        (Fin.cons S0 tail)).1
  obtain ⟨e0, coeff, hpoly⟩ :=
    exists_productSliceConditional_perturbed P ell G f0 f tail hIpos
  let Y : Erdos88.BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset (Fin (P.fiber 0).card)) (ell 0) → ℝ :=
    fun S ↦ Erdos88.Probability.perturbedEdgePolynomial H e0 coeff S.1
  let : Nonempty (Erdos88.BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset (Fin (P.fiber 0).card)) (ell 0)) :=
    Nonempty.map E inferInstance
  have hchar : Erdos88.BooleanSlices.finiteCharacteristic X t =
      Erdos88.BooleanSlices.finiteCharacteristic Y t := by
    unfold Erdos88.BooleanSlices.finiteCharacteristic
    apply Fintype.expect_equiv E
    intro S0
    simp only [X, Y]
    rw [hpoly S0]
  change ‖Erdos88.BooleanSlices.finiteCharacteristic X t‖ ≤ B
  rw [hchar,
    Erdos88.BoundedWindowAnalytic.booleanFiniteCharacteristic_eq_finCharFun]
  exact hbound e0 coeff

/-- Lemma 8.1 applied to a fixed first-bucket conditional of the centered
product-slice quadratic.  The decay scale is the size of that bucket. -/
theorem exists_productSliceConditional_lemma81_bound
    (C eta : ℝ) (hC : 0 < C) (heta : 0 < eta)
    (hetaHalf : eta < 1 / 2) :
    ∃ nu : ℝ, 0 < nu ∧ ∃ N : ℕ,
      ∀ {n K s : ℕ}
        (P : Erdos88.BooleanSlices.BucketPartition (Fin n) (Fin (K + 1)))
        (ell : Fin (K + 1) → ℕ) (G : SimpleGraph (Fin n))
        (f0 : ℝ) (f : Fin n → ℝ)
        (tail : ∀ k : Fin K,
          Erdos88.BooleanSlices.BooleanSlicePoint
            (P.fiber k.succ) (ell k.succ))
        [Nonempty (Erdos88.BooleanSlices.BooleanSlicePoint
          (P.fiber 0) (ell 0))],
        0 < (P.fiber 0).card →
        N ≤ (P.fiber 0).card →
        RamseyFree C (inducedOverFin G (P.fiber 0)) →
        eta * (P.fiber 0).card ≤ ell 0 →
        (ell 0 : ℝ) ≤ (1 - eta) * (P.fiber 0).card →
        ∀ t : ℝ,
          ((P.fiber 0).card : ℝ) ^ (-1 + eta) ≤ |t| →
          |t| ≤ nu →
          ‖Erdos88.BooleanSlices.finiteCharacteristic
              (fun S0 : Erdos88.BooleanSlices.BooleanSlicePoint
                  (P.fiber 0) (ell 0) ↦
                Erdos88.BooleanSlices.sliceQuadratic f0 f
                  (bucketCenteredAdjacency P.bucket s G)
                  ((Erdos88.BooleanSlices.productSliceEquiv P ell).symm
                    (Fin.cons S0 tail)).1) t‖ ≤
            ((P.fiber 0).card : ℝ) ^ (-5 : ℝ) := by
  obtain ⟨nu, hnu, N, hlemma81⟩ :=
    Erdos88.QuadraticCancellation.ksssLemma81 C eta hC heta hetaHalf
  refine ⟨nu, hnu, N, ?_⟩
  intro n K s P ell G f0 f tail _ hIpos hN hRamsey
    hellLower hellUpper t htLower htUpper
  apply norm_productSliceConditional_le_of_perturbed
    P ell G f0 f tail hIpos t
  intro e0 coeff
  let E := booleanSlicePointSubsetEquiv (P.fiber 0) (ell 0)
    (inducedOverFinIso G (P.fiber 0)).toEquiv
  let : Nonempty (Erdos88.BooleanSlices.BooleanSlicePoint
      (Finset.univ : Finset (Fin (P.fiber 0).card)) (ell 0)) :=
    Nonempty.map E inferInstance
  let : DecidableRel (inducedOverFin G (P.fiber 0)).Adj :=
    fun _ _ ↦ Classical.propDecidable _
  exact hlemma81 (P.fiber 0).card hN
    (inducedOverFin G (P.fiber 0)) hRamsey
    (ell 0) e0 coeff t hellLower hellUpper htLower htUpper

/-- Lemma 8.1 averaged over all the remaining buckets.  Conditioning on
the tail leaves a perturbed induced-edge polynomial on the first bucket,
and the bound is uniform in that tail. -/
theorem exists_productSlice_lemma81_bound
    (C eta : ℝ) (hC : 0 < C) (heta : 0 < eta)
    (hetaHalf : eta < 1 / 2) :
    ∃ nu : ℝ, 0 < nu ∧ ∃ N : ℕ,
      ∀ {n K s : ℕ}
        (P : Erdos88.BooleanSlices.BucketPartition (Fin n) (Fin (K + 1)))
        (ell : Fin (K + 1) → ℕ) (G : SimpleGraph (Fin n))
        (f0 : ℝ) (f : Fin n → ℝ)
        [Nonempty (Erdos88.BooleanSlices.ProductSlicePoint P ell)]
        [∀ k, Nonempty (Erdos88.BooleanSlices.BooleanSlicePoint
          (P.fiber k) (ell k))],
        0 < (P.fiber 0).card →
        N ≤ (P.fiber 0).card →
        RamseyFree C (inducedOverFin G (P.fiber 0)) →
        eta * (P.fiber 0).card ≤ ell 0 →
        (ell 0 : ℝ) ≤ (1 - eta) * (P.fiber 0).card →
        ∀ t : ℝ,
          ((P.fiber 0).card : ℝ) ^ (-1 + eta) ≤ |t| →
          |t| ≤ nu →
          ‖Erdos88.BooleanSlices.finiteCharacteristic
              (fun W : Erdos88.BooleanSlices.ProductSlicePoint P ell ↦
                Erdos88.BooleanSlices.sliceQuadratic f0 f
                  (bucketCenteredAdjacency P.bucket s G) W.1) t‖ ≤
            ((P.fiber 0).card : ℝ) ^ (-5 : ℝ) := by
  obtain ⟨nu, hnu, N, hconditional⟩ :=
    exists_productSliceConditional_lemma81_bound C eta hC heta hetaHalf
  refine ⟨nu, hnu, N, ?_⟩
  intro n K s P ell G f0 f _ _ hIpos hN hRamsey
    hellLower hellUpper t htLower htUpper
  apply norm_finiteCharacteristic_productSlice_le_of_head P ell
  intro tail
  exact hconditional P ell G f0 f tail hIpos hN hRamsey
    hellLower hellUpper t htLower htUpper

lemma bucket_rpow_neg_five_le_ambient_neg_two
    {n q : ℕ} (hn : 1 ≤ n)
    (hq : (n : ℝ) ^ (2 / 5 : ℝ) ≤ q) :
    (q : ℝ) ^ (-5 : ℝ) ≤ (n : ℝ) ^ (-2 : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbase : 0 < (n : ℝ) ^ (2 / 5 : ℝ) :=
    Real.rpow_pos_of_pos hnpos _
  calc
    (q : ℝ) ^ (-5 : ℝ) ≤
        ((n : ℝ) ^ (2 / 5 : ℝ)) ^ (-5 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hbase hq (by norm_num)
    _ = (n : ℝ) ^ (-2 : ℝ) := by
      rw [← Real.rpow_mul hnpos.le]
      congr 1
      norm_num

/-- Ambient-scale consequence of the product-slice Lemma 8.1 bound.  A
bucket of size at least `n^(2/5)` turns its local fifth-power decay into the
`n⁻²` outer estimate needed by the three-band Fourier argument. -/
theorem exists_productSlice_lemma81_outer_two_bound
    (C eta : ℝ) (hC : 0 < C) (heta : 0 < eta)
    (hetaHalf : eta < 1 / 2) :
    ∃ nu : ℝ, 0 < nu ∧ ∃ N : ℕ,
      ∀ {n K s : ℕ}
        (P : Erdos88.BooleanSlices.BucketPartition (Fin n) (Fin (K + 1)))
        (ell : Fin (K + 1) → ℕ) (G : SimpleGraph (Fin n))
        (f0 : ℝ) (f : Fin n → ℝ)
        [Nonempty (Erdos88.BooleanSlices.ProductSlicePoint P ell)]
        [∀ k, Nonempty (Erdos88.BooleanSlices.BooleanSlicePoint
          (P.fiber k) (ell k))],
        1 ≤ n →
        (n : ℝ) ^ (2 / 5 : ℝ) ≤ (P.fiber 0).card →
        0 < (P.fiber 0).card →
        N ≤ (P.fiber 0).card →
        RamseyFree C (inducedOverFin G (P.fiber 0)) →
        eta * (P.fiber 0).card ≤ ell 0 →
        (ell 0 : ℝ) ≤ (1 - eta) * (P.fiber 0).card →
        ∀ t : ℝ,
          ((P.fiber 0).card : ℝ) ^ (-1 + eta) ≤ |t| →
          |t| ≤ nu →
          ‖Erdos88.BooleanSlices.finiteCharacteristic
              (fun W : Erdos88.BooleanSlices.ProductSlicePoint P ell ↦
                Erdos88.BooleanSlices.sliceQuadratic f0 f
                  (bucketCenteredAdjacency P.bucket s G) W.1) t‖ ≤
            (n : ℝ) ^ (-2 : ℝ) := by
  obtain ⟨nu, hnu, N, hproduct⟩ :=
    exists_productSlice_lemma81_bound C eta hC heta hetaHalf
  refine ⟨nu, hnu, N, ?_⟩
  intro n K s P ell G f0 f _ _ hn hbucket hIpos hN hRamsey
    hellLower hellUpper t htLower htUpper
  exact (hproduct P ell G f0 f hIpos hN hRamsey hellLower hellUpper
    t htLower htUpper).trans
      (bucket_rpow_neg_five_le_ambient_neg_two hn hbucket)

end Erdos88.GaussianQuadratic
