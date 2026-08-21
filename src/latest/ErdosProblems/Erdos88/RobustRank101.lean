/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos88.RobustRank
import ErdosProblems.Erdos88.AKSGraph

open scoped BigOperators
open SimpleGraph

namespace Erdos88.RobustRank

noncomputable section

lemma bucketBlock_graphAdjacency_isBinary {n m : ℕ}
    (bucket : Fin n → Fin m) (G : SimpleGraph (Fin n)) (a b : Fin m) :
    IsBinary (bucketBlock bucket (graphAdjacencyMatrix G) a b) := by
  intro i j
  exact graphAdjacencyMatrix_isBinary G i.1 j.1

lemma bucketBlock_sub {n m : ℕ} (bucket : Fin n → Fin m)
    (A B : Matrix (Fin n) (Fin n) ℝ) (a b : Fin m) :
    bucketBlock bucket (A - B) a b =
      bucketBlock bucket A a b - bucketBlock bucket B a b := by
  rfl

/-- Relabel the square `Fin q` conclusion of Proposition 10.2 to arbitrary
finite row and column types without changing its uniform constant. -/
lemma proposition102_equalCard_with_constant
    (r : ℕ) (Cr : ℝ)
    (hround : ∀ (q : ℕ) (ε : ℝ)
      (A B : Matrix (Fin q) (Fin q) ℝ),
      0 ≤ ε → IsBinary A → B.rank ≤ r →
      frobeniusSq (A - B) ≤ ε * (q : ℝ) ^ 2 →
        ∃ Q : Matrix (Fin q) (Fin q) ℝ,
          IsBinary Q ∧ Q.rank ≤ r ∧
            frobeniusSq (A - Q) ≤ Cr * Real.sqrt ε * (q : ℝ) ^ 2) :
    ∀ {ι κ : Type} [Fintype ι] [Fintype κ],
      ∀ (q : ℕ), Fintype.card ι = q → Fintype.card κ = q →
        ∀ (ε : ℝ) (A B : Matrix ι κ ℝ),
          0 ≤ ε → IsBinary A → B.rank ≤ r →
          frobeniusSq (A - B) ≤ ε * (q : ℝ) ^ 2 →
            ∃ Q : Matrix ι κ ℝ,
              IsBinary Q ∧ Q.rank ≤ r ∧
                frobeniusSq (A - Q) ≤
                  Cr * Real.sqrt ε * (q : ℝ) ^ 2 := by
  intro ι κ _ _ q hι hκ ε A B hε hA hBrank hclose
  let eι : ι ≃ Fin q := Fintype.equivFinOfCardEq hι
  let eκ : κ ≃ Fin q := Fintype.equivFinOfCardEq hκ
  let A₀ : Matrix (Fin q) (Fin q) ℝ := A.reindex eι eκ
  let B₀ : Matrix (Fin q) (Fin q) ℝ := B.reindex eι eκ
  have hA₀ : IsBinary A₀ := by
    intro i j
    simpa [A₀, Matrix.reindex_apply] using hA (eι.symm i) (eκ.symm j)
  have hB₀rank : B₀.rank ≤ r := by
    rw [show B₀.rank = B.rank by
      simpa [B₀] using Matrix.rank_reindex eι eκ B]
    exact hBrank
  have hclose₀ : frobeniusSq (A₀ - B₀) ≤ ε * (q : ℝ) ^ 2 := by
    have hsub : A₀ - B₀ = (A - B).submatrix eι.symm eκ.symm := by rfl
    rw [hsub, frobeniusSq_submatrix_equiv]
    exact hclose
  obtain ⟨Q₀, hQ₀, hQ₀rank, hQ₀close⟩ :=
    hround q ε A₀ B₀ hε hA₀ hB₀rank hclose₀
  let Q : Matrix ι κ ℝ := Q₀.submatrix eι eκ
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro i j
    simpa [Q] using hQ₀ (eι i) (eκ j)
  · rw [show Q.rank = Q₀.rank by
      simpa [Q] using Matrix.rank_submatrix Q₀ eι eκ]
    exact hQ₀rank
  · have hsub : A - Q = (A₀ - Q₀).submatrix eι eκ := by
      ext i j
      simp [A₀, Q, Matrix.reindex_apply]
    rw [hsub, frobeniusSq_submatrix_equiv]
    exact hQ₀close

theorem exists_roundedBucketSystem_of_lowError
    {n m D r s : ℕ} (bucket : Fin n → Fin m)
    (G : SimpleGraph (Fin n)) (B : Matrix (Fin n) (Fin n) ℝ)
    (sel : Fin D → Fin m) (hs : ∀ a, (bucketFiber bucket (sel a)).card = s)
    (hBrank : BlockRankAtMost r bucket B)
    {alpha Cr : ℝ} (halpha : 0 ≤ alpha)
    (hround : ∀ {ι : Type} {κ : Type} [Fintype ι] [Fintype κ],
      ∀ (q : ℕ), Fintype.card ι = q → Fintype.card κ = q →
        ∀ (ε : ℝ) (A B : Matrix ι κ ℝ),
          0 ≤ ε → IsBinary A → B.rank ≤ r →
          frobeniusSq (A - B) ≤ ε * (q : ℝ) ^ 2 →
            ∃ Q : Matrix ι κ ℝ,
              IsBinary Q ∧ Q.rank ≤ r ∧
                frobeniusSq (A - Q) ≤ Cr * Real.sqrt ε * (q : ℝ) ^ 2)
    (hpair : ∀ a b : Fin D, a ≠ b →
      bucketError bucket (graphAdjacencyMatrix G - B) (sel a) (sel b) ≤
        alpha * (s : ℝ) ^ 2) :
    ∃ sys : RoundedBucketSystem (r := r) bucket sel,
      ∀ a b, a ≠ b →
        frobeniusSq
            (bucketBlock bucket (graphAdjacencyMatrix G) (sel a) (sel b) -
              sys.Q a b) ≤
          Cr * Real.sqrt alpha * (s : ℝ) ^ 2 := by
  classical
  let A := graphAdjacencyMatrix G
  have hex : ∀ a b : Fin D,
      ∃ Q : Matrix (bucketFiber bucket (sel a))
          (bucketFiber bucket (sel b)) ℝ,
        IsBinary Q ∧ Q.rank ≤ r ∧
          (a ≠ b → frobeniusSq
              (bucketBlock bucket A (sel a) (sel b) - Q) ≤
            Cr * Real.sqrt alpha * (s : ℝ) ^ 2) := by
    intro a b
    by_cases hab : a = b
    · refine ⟨0, ?_, by simp, ?_⟩
      · intro i j
        exact Or.inl rfl
      · exact fun h ↦ (h hab).elim
    · have hcardA : Fintype.card (bucketFiber bucket (sel a)) = s := by
        rw [Fintype.card_coe]
        exact hs a
      have hcardB : Fintype.card (bucketFiber bucket (sel b)) = s := by
        rw [Fintype.card_coe]
        exact hs b
      have hclose : frobeniusSq
          (bucketBlock bucket A (sel a) (sel b) -
            bucketBlock bucket B (sel a) (sel b)) ≤ alpha * (s : ℝ) ^ 2 := by
        rw [← bucketBlock_sub]
        exact hpair a b hab
      obtain ⟨Q, hQ, hQrank, hQclose⟩ :=
        hround s hcardA hcardB alpha
          (bucketBlock bucket A (sel a) (sel b))
          (bucketBlock bucket B (sel a) (sel b)) halpha
          (bucketBlock_graphAdjacency_isBinary bucket G (sel a) (sel b))
          (hBrank (sel a) (sel b)) hclose
      exact ⟨Q, hQ, hQrank, fun _ ↦ hQclose⟩
  let sys : RoundedBucketSystem (r := r) bucket sel :=
    { Q := fun a b ↦ Classical.choose (hex a b)
      binary := fun a b ↦ (Classical.choose_spec (hex a b)).1
      rank_le := fun a b ↦ (Classical.choose_spec (hex a b)).2.1 }
  refine ⟨sys, ?_⟩
  intro a b hab
  exact (Classical.choose_spec (hex a b)).2.2 hab

noncomputable def refinedBucketVertices
    {n m D : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a))) (a : Fin D) :
    Finset (Fin n) :=
  (J a).image Subtype.val

lemma card_refinedBucketVertices
    {n m D : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a))) (a : Fin D) :
    (refinedBucketVertices J a).card = (J a).card := by
  classical
  exact Finset.card_image_iff.mpr Subtype.val_injective.injOn

lemma refinedBucketVertices_subset
    {n m D : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a))) (a : Fin D) :
    refinedBucketVertices J a ⊆ bucketFiber bucket (sel a) := by
  classical
  intro x hx
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hx
  exact i.property

lemma refinedBucketVertices_disjoint
    {n m D : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (hsel : Function.Injective sel)
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    {a b : Fin D} (hab : a ≠ b) :
    Disjoint (refinedBucketVertices J a) (refinedBucketVertices J b) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxa hxb
  have hxa' := refinedBucketVertices_subset J a hxa
  have hxb' := refinedBucketVertices_subset J b hxb
  have ha : bucket x = sel a := (mem_bucketFiber _ _ _).mp hxa'
  have hb : bucket x = sel b := (mem_bucketFiber _ _ _).mp hxb'
  exact hab (hsel (ha.symm.trans hb))

noncomputable def refinedVertexUnion
    {n m D : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    (H : Finset (Fin D)) : Finset (Fin n) :=
  H.biUnion (refinedBucketVertices J)

lemma card_refinedVertexUnion
    {n m D q : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (hsel : Function.Injective sel)
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    (hJcard : ∀ a, (J a).card = q) (H : Finset (Fin D)) :
    (refinedVertexUnion J H).card = H.card * q := by
  classical
  rw [refinedVertexUnion, Finset.card_biUnion]
  · simp_rw [card_refinedBucketVertices, hJcard]
    simp
  · intro a ha b hb hab
    exact refinedBucketVertices_disjoint hsel J hab

theorem exists_commonRefinement_div
    {n m D r s : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (sys : RoundedBucketSystem (r := r) bucket sel)
    (hs : ∀ a, (bucketFiber bucket (sel a)).card = s) :
    ∃ J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)),
      (∀ a, (J a).card = s /
        Fintype.card (Fin D → (Fin (2 ^ r) × Fin (2 ^ r)))) ∧
      ∀ a ⦃i i'⦄, i ∈ J a → i' ∈ J a →
        roundedVertexCode sys a i = roundedVertexCode sys a i' := by
  let codeCount := Fintype.card (Fin D → (Fin (2 ^ r) × Fin (2 ^ r)))
  have hfit : codeCount * (s / codeCount) ≤ s := Nat.mul_div_le s codeCount
  simpa only [codeCount] using
    exists_commonRefinement_of_roundedBucketSystem sys hs hfit

noncomputable def refinementRepresentative
    {n m D : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    (hJ : ∀ a, (J a).Nonempty) (a : Fin D) :
    bucketFiber bucket (sel a) :=
  Classical.choose (hJ a)

lemma refinementRepresentative_mem
    {n m D : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    (hJ : ∀ a, (J a).Nonempty) (a : Fin D) :
    refinementRepresentative J hJ a ∈ J a :=
  Classical.choose_spec (hJ a)

noncomputable def roundedIndexGraph
    {n m D r : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (sys : RoundedBucketSystem (r := r) bucket sel)
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    (hJ : ∀ a, (J a).Nonempty) : SimpleGraph (Fin D) :=
  SimpleGraph.fromRel fun a b ↦ a < b ∧
    sys.Q a b (refinementRepresentative J hJ a)
      (refinementRepresentative J hJ b) = 1

lemma roundedIndexGraph_adj_iff_of_lt
    {n m D r : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (sys : RoundedBucketSystem (r := r) bucket sel)
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    (hJ : ∀ a, (J a).Nonempty) {a b : Fin D} (hab : a < b) :
    (roundedIndexGraph sys J hJ).Adj a b ↔
      sys.Q a b (refinementRepresentative J hJ a)
        (refinementRepresentative J hJ b) = 1 := by
  rw [roundedIndexGraph, SimpleGraph.fromRel_adj]
  simp only [hab, true_and, ne_eq, ne_of_lt hab, not_false_eq_true]
  constructor
  · intro h
    rcases h with h | h
    · exact h
    · exact (not_lt_of_ge hab.le h.1).elim
  · exact fun h ↦ Or.inl h

lemma roundedBlock_eq_indexValue
    {n m D r : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (sys : RoundedBucketSystem (r := r) bucket sel)
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    (hcode : ∀ a ⦃i i'⦄, i ∈ J a → i' ∈ J a →
      roundedVertexCode sys a i = roundedVertexCode sys a i')
    (hJ : ∀ a, (J a).Nonempty) (a b : Fin D)
    {i : bucketFiber bucket (sel a)} {j : bucketFiber bucket (sel b)}
    (hi : i ∈ J a) (hj : j ∈ J b) :
    sys.Q a b i j =
      sys.Q a b (refinementRepresentative J hJ a)
        (refinementRepresentative J hJ b) := by
  exact roundedBlock_constant_on_commonRefinement sys J hcode a b
    hi (refinementRepresentative_mem J hJ a)
    hj (refinementRepresentative_mem J hJ b)

lemma roundedBlock_eq_zero_of_independent
    {n m D r : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (sys : RoundedBucketSystem (r := r) bucket sel)
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    (hcode : ∀ a ⦃i i'⦄, i ∈ J a → i' ∈ J a →
      roundedVertexCode sys a i = roundedVertexCode sys a i')
    (hJ : ∀ a, (J a).Nonempty) {H : Finset (Fin D)}
    (hH : (roundedIndexGraph sys J hJ).IsIndepSet (H : Set (Fin D)))
    {a b : Fin D} (ha : a ∈ H) (hb : b ∈ H) (hab : a < b)
    {i : bucketFiber bucket (sel a)} {j : bucketFiber bucket (sel b)}
    (hi : i ∈ J a) (hj : j ∈ J b) :
    sys.Q a b i j = 0 := by
  have hnot : ¬(roundedIndexGraph sys J hJ).Adj a b :=
    hH ha hb (ne_of_lt hab)
  have hnotOne : sys.Q a b (refinementRepresentative J hJ a)
      (refinementRepresentative J hJ b) ≠ 1 := by
    intro hone
    exact hnot ((roundedIndexGraph_adj_iff_of_lt sys J hJ hab).2 hone)
  have hbinary := sys.binary a b
    (refinementRepresentative J hJ a) (refinementRepresentative J hJ b)
  have hrep : sys.Q a b (refinementRepresentative J hJ a)
      (refinementRepresentative J hJ b) = 0 := by
    rcases hbinary with hzero | hone
    · exact hzero
    · exact (hnotOne hone).elim
  exact (roundedBlock_eq_indexValue sys J hcode hJ a b hi hj).trans hrep

lemma roundedBlock_eq_one_of_clique
    {n m D r : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (sys : RoundedBucketSystem (r := r) bucket sel)
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    (hcode : ∀ a ⦃i i'⦄, i ∈ J a → i' ∈ J a →
      roundedVertexCode sys a i = roundedVertexCode sys a i')
    (hJ : ∀ a, (J a).Nonempty) {H : Finset (Fin D)}
    (hH : (roundedIndexGraph sys J hJ).IsClique (H : Set (Fin D)))
    {a b : Fin D} (ha : a ∈ H) (hb : b ∈ H) (hab : a < b)
    {i : bucketFiber bucket (sel a)} {j : bucketFiber bucket (sel b)}
    (hi : i ∈ J a) (hj : j ∈ J b) :
    sys.Q a b i j = 1 := by
  have hadj := hH ha hb (ne_of_lt hab)
  have hrep := (roundedIndexGraph_adj_iff_of_lt sys J hJ hab).1 hadj
  exact (roundedBlock_eq_indexValue sys J hcode hJ a b hi hj).trans hrep

theorem exists_homogeneous_refinement_indices
    {n m D r t : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (sys : RoundedBucketSystem (r := r) bucket sel)
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    (hJ : ∀ a, (J a).Nonempty)
    (hD : Ramsey.ramseyNumber t t ≤ D) :
    (∃ H : Finset (Fin D), H.card = t ∧
      (roundedIndexGraph sys J hJ).IsClique (H : Set (Fin D))) ∨
    (∃ H : Finset (Fin D), H.card = t ∧
      (roundedIndexGraph sys J hJ).IsIndepSet (H : Set (Fin D))) := by
  rcases FiniteES.clique_or_independent_subset_of_ramseyNumber_le
      (roundedIndexGraph sys J hJ) Finset.univ (by simpa using hD) with
    hclique | hindep
  · obtain ⟨H, _hsub, hH⟩ := hclique
    exact Or.inl ⟨H, hH.card_eq, hH.isClique⟩
  · obtain ⟨H, _hsub, hH⟩ := hindep
    exact Or.inr ⟨H, hH.card_eq, hH.isIndepSet⟩

lemma sum_refinedVertexUnion
    {n m D : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (hsel : Function.Injective sel)
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    (H : Finset (Fin D)) (f : Fin n → ℝ) :
    (∑ x ∈ refinedVertexUnion J H, f x) =
      ∑ a ∈ H, ∑ i ∈ J a, f i.1 := by
  classical
  rw [refinedVertexUnion, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [refinedBucketVertices]
    exact Finset.sum_image (fun i _hi j _hj hij ↦ Subtype.val_injective hij)
  · intro a ha b hb hab
    exact refinedBucketVertices_disjoint hsel J hab

lemma sum_graphAdjacencyMatrix_eq_twice_edgeCount
    {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n)) :
    (∑ i ∈ U, ∑ j ∈ U, graphAdjacencyMatrix G i j) =
      2 * (AKSGraph.edgeCount G U : ℝ) := by
  classical
  have hrow (i : Fin n) :
      (∑ j ∈ U, graphAdjacencyMatrix G i j) =
        (AKSGraph.degreeInto G i U : ℝ) := by
    rw [AKSGraph.degreeInto_eq_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : G.Adj i j <;> simp [graphAdjacencyMatrix, hij]
  simp_rw [hrow]
  exact_mod_cast AKSGraph.sum_degreeInto G U

lemma refined_vertices_ne
    {n m D : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (hsel : Function.Injective sel)
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    {a b : Fin D} (hab : a ≠ b)
    {i : bucketFiber bucket (sel a)} {j : bucketFiber bucket (sel b)} :
    i.1 ≠ j.1 := by
  intro hij
  have hi : bucket i.1 = sel a := (mem_bucketFiber _ _ _).mp i.property
  have hj : bucket j.1 = sel b := (mem_bucketFiber _ _ _).mp j.property
  apply hab
  apply hsel
  exact hi.symm.trans (hij ▸ hj)

lemma cross_sum_le_frobenius_of_zero
    {n m D r : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (G : SimpleGraph (Fin n))
    (sys : RoundedBucketSystem (r := r) bucket sel)
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    (a b : Fin D)
    (hzero : ∀ {i : bucketFiber bucket (sel a)}
      {j : bucketFiber bucket (sel b)}, i ∈ J a → j ∈ J b →
        sys.Q a b i j = 0) :
    (∑ i ∈ J a, ∑ j ∈ J b, graphAdjacencyMatrix G i.1 j.1) ≤
      frobeniusSq
        (bucketBlock bucket (graphAdjacencyMatrix G) (sel a) (sel b) -
          sys.Q a b) := by
  classical
  let E := bucketBlock bucket (graphAdjacencyMatrix G) (sel a) (sel b) -
    sys.Q a b
  have hpoint : ∀ i ∈ J a, ∀ j ∈ J b,
      graphAdjacencyMatrix G i.1 j.1 = E i j ^ 2 := by
    intro i hi j hj
    have hz := hzero hi hj
    rcases graphAdjacencyMatrix_isBinary G i.1 j.1 with hA | hA
    · simp [E, bucketBlock, hz, hA]
    · simp [E, bucketBlock, hz, hA]
  calc
    (∑ i ∈ J a, ∑ j ∈ J b, graphAdjacencyMatrix G i.1 j.1) =
        ∑ i ∈ J a, ∑ j ∈ J b, E i j ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hpoint i hi j hj
    _ ≤ ∑ i ∈ J a, ∑ j : bucketFiber bucket (sel b), E i j ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_univ_sum_of_nonneg fun j ↦ sq_nonneg (E i j)
    _ ≤ ∑ i : bucketFiber bucket (sel a),
        ∑ j : bucketFiber bucket (sel b), E i j ^ 2 := by
      exact Finset.sum_le_univ_sum_of_nonneg fun i ↦
        Finset.sum_nonneg fun j _ ↦ sq_nonneg (E i j)
    _ = frobeniusSq
        (bucketBlock bucket (graphAdjacencyMatrix G) (sel a) (sel b) -
          sys.Q a b) := rfl

lemma cross_sum_compl_le_frobenius_of_one
    {n m D r : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (hsel : Function.Injective sel) (G : SimpleGraph (Fin n))
    (sys : RoundedBucketSystem (r := r) bucket sel)
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    {a b : Fin D} (hab : a ≠ b)
    (hone : ∀ {i : bucketFiber bucket (sel a)}
      {j : bucketFiber bucket (sel b)}, i ∈ J a → j ∈ J b →
        sys.Q a b i j = 1) :
    (∑ i ∈ J a, ∑ j ∈ J b, graphAdjacencyMatrix Gᶜ i.1 j.1) ≤
      frobeniusSq
        (bucketBlock bucket (graphAdjacencyMatrix G) (sel a) (sel b) -
          sys.Q a b) := by
  classical
  let E := bucketBlock bucket (graphAdjacencyMatrix G) (sel a) (sel b) -
    sys.Q a b
  have hpoint : ∀ i ∈ J a, ∀ j ∈ J b,
      graphAdjacencyMatrix Gᶜ i.1 j.1 = E i j ^ 2 := by
    intro i hi j hj
    have hne : i.1 ≠ j.1 := refined_vertices_ne hsel J hab
    have ho := hone hi hj
    by_cases hA : G.Adj i.1 j.1
    · simp [E, bucketBlock, graphAdjacencyMatrix, hA, hne, ho]
    · simp [E, bucketBlock, graphAdjacencyMatrix, hA, hne, ho]
  calc
    (∑ i ∈ J a, ∑ j ∈ J b, graphAdjacencyMatrix Gᶜ i.1 j.1) =
        ∑ i ∈ J a, ∑ j ∈ J b, E i j ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hpoint i hi j hj
    _ ≤ ∑ i ∈ J a, ∑ j : bucketFiber bucket (sel b), E i j ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.sum_le_univ_sum_of_nonneg fun j ↦ sq_nonneg (E i j)
    _ ≤ ∑ i : bucketFiber bucket (sel a),
        ∑ j : bucketFiber bucket (sel b), E i j ^ 2 := by
      exact Finset.sum_le_univ_sum_of_nonneg fun i ↦
        Finset.sum_nonneg fun j _ ↦ sq_nonneg (E i j)
    _ = frobeniusSq
        (bucketBlock bucket (graphAdjacencyMatrix G) (sel a) (sel b) -
          sys.Q a b) := rfl

lemma double_sum_refinedVertexUnion
    {n m D : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (hsel : Function.Injective sel)
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    (H : Finset (Fin D)) (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i ∈ refinedVertexUnion J H,
        ∑ j ∈ refinedVertexUnion J H, M i j) =
      ∑ a ∈ H, ∑ i ∈ J a, ∑ b ∈ H, ∑ j ∈ J b, M i.1 j.1 := by
  rw [sum_refinedVertexUnion hsel J H]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro i hi
  exact sum_refinedVertexUnion hsel J H (fun j ↦ M i.1 j)

lemma cross_sum_graph_comm
    {n m D : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (G : SimpleGraph (Fin n))
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a))) (a b : Fin D) :
    (∑ i ∈ J a, ∑ j ∈ J b, graphAdjacencyMatrix G i.1 j.1) =
      ∑ j ∈ J b, ∑ i ∈ J a, graphAdjacencyMatrix G j.1 i.1 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hij : G.Adj i.1 j.1
  · have hji := G.symm.symm _ _ hij
    simp [graphAdjacencyMatrix, hij, hji]
  · have hji : ¬G.Adj j.1 i.1 := fun h ↦ hij (G.symm.symm _ _ h)
    simp [graphAdjacencyMatrix, hij, hji]

lemma block_sum_graph_le_card_sq
    {n m D q : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (G : SimpleGraph (Fin n))
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    (hJcard : ∀ a, (J a).card = q) (a b : Fin D) :
    (∑ i ∈ J a, ∑ j ∈ J b, graphAdjacencyMatrix G i.1 j.1) ≤
      (q : ℝ) ^ 2 := by
  calc
    (∑ i ∈ J a, ∑ j ∈ J b, graphAdjacencyMatrix G i.1 j.1) ≤
        ∑ _i ∈ J a, ∑ _j ∈ J b, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rcases graphAdjacencyMatrix_isBinary G i.1 j.1 with h | h <;>
        rw [h] <;> norm_num
    _ = (q : ℝ) ^ 2 := by simp [hJcard, pow_two]

lemma sum_block_bounds
    {D q : ℕ} {H : Finset (Fin D)} {E0 : ℝ}
    (hE0 : 0 ≤ E0) (hblock : ∀ a ∈ H, ∀ b ∈ H,
      (if a = b then (q : ℝ) ^ 2 else E0) ≥ 0) :
    (∑ a ∈ H, ∑ b ∈ H,
        (if a = b then (q : ℝ) ^ 2 else E0)) ≤
      (H.card : ℝ) * ((q : ℝ) ^ 2 + H.card * E0) := by
  calc
    (∑ a ∈ H, ∑ b ∈ H,
        (if a = b then (q : ℝ) ^ 2 else E0)) ≤
        ∑ a ∈ H, ((q : ℝ) ^ 2 + H.card * E0) := by
      apply Finset.sum_le_sum
      intro a ha
      calc
        (∑ b ∈ H, if a = b then (q : ℝ) ^ 2 else E0) ≤
            ∑ b ∈ H, ((if a = b then (q : ℝ) ^ 2 else 0) + E0) := by
          apply Finset.sum_le_sum
          intro b hb
          by_cases hab : a = b
          · simp [hab, hE0]
          · simp [hab]
        _ = (q : ℝ) ^ 2 + H.card * E0 := by
          rw [Finset.sum_add_distrib]
          simp [ha]
    _ = (H.card : ℝ) * ((q : ℝ) ^ 2 + H.card * E0) := by
      simp
      ring

theorem edgeCount_refined_independent_le
    {n m D r q : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (hsel : Function.Injective sel) (G : SimpleGraph (Fin n))
    (sys : RoundedBucketSystem (r := r) bucket sel)
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    (hJcard : ∀ a, (J a).card = q)
    (hcode : ∀ a ⦃i i'⦄, i ∈ J a → i' ∈ J a →
      roundedVertexCode sys a i = roundedVertexCode sys a i')
    (hq : 0 < q) {H : Finset (Fin D)}
    (hH : (roundedIndexGraph sys J
      (fun a ↦ Finset.card_pos.mp (by rw [hJcard a]; exact hq))).IsIndepSet
        (H : Set (Fin D)))
    {E0 : ℝ} (hE0 : 0 ≤ E0)
    (hclose : ∀ a b, a ≠ b → frobeniusSq
        (bucketBlock bucket (graphAdjacencyMatrix G) (sel a) (sel b) -
          sys.Q a b) ≤ E0) :
    (AKSGraph.edgeCount G (refinedVertexUnion J H) : ℝ) ≤
      (H.card : ℝ) * ((q : ℝ) ^ 2 + H.card * E0) := by
  let hJ : ∀ a, (J a).Nonempty :=
    fun a ↦ Finset.card_pos.mp (by rw [hJcard a]; exact hq)
  have hdouble := sum_graphAdjacencyMatrix_eq_twice_edgeCount G
    (refinedVertexUnion J H)
  rw [double_sum_refinedVertexUnion hsel J H] at hdouble
  have hblocks : (∑ a ∈ H, ∑ i ∈ J a, ∑ b ∈ H, ∑ j ∈ J b,
      graphAdjacencyMatrix G i.1 j.1) ≤
      ∑ a ∈ H, ∑ b ∈ H,
        (if a = b then (q : ℝ) ^ 2 else E0) := by
    simp_rw [Finset.sum_comm (s := J _) (t := H)]
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    by_cases hab : a = b
    · rw [if_pos hab]
      exact block_sum_graph_le_card_sq G J hJcard a b
    · rw [if_neg hab]
      rcases lt_or_gt_of_ne hab with halt | hblt
      · exact (cross_sum_le_frobenius_of_zero G sys J a b
          (fun {i} {j} hi hj ↦ roundedBlock_eq_zero_of_independent
            sys J hcode hJ hH ha hb halt hi hj)).trans (hclose a b hab)
      · rw [cross_sum_graph_comm G J a b]
        exact (cross_sum_le_frobenius_of_zero G sys J b a
          (fun {i} {j} hi hj ↦ roundedBlock_eq_zero_of_independent
            sys J hcode hJ hH hb ha hblt hi hj)).trans
          (hclose b a (Ne.symm hab))
  have hsumBound := sum_block_bounds (H := H) (q := q) hE0
    (fun a ha b hb ↦ by
      by_cases hab : a = b
      · simp [hab]
      · simp [hab, hE0])
  have htwo : 2 * (AKSGraph.edgeCount G (refinedVertexUnion J H) : ℝ) ≤
      (H.card : ℝ) * ((q : ℝ) ^ 2 + H.card * E0) := by
    rw [← hdouble]
    exact hblocks.trans hsumBound
  have hedge0 : (0 : ℝ) ≤
      (AKSGraph.edgeCount G (refinedVertexUnion J H) : ℝ) := by positivity
  nlinarith

theorem edgeCount_refined_clique_compl_le
    {n m D r q : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (hsel : Function.Injective sel) (G : SimpleGraph (Fin n))
    (sys : RoundedBucketSystem (r := r) bucket sel)
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    (hJcard : ∀ a, (J a).card = q)
    (hcode : ∀ a ⦃i i'⦄, i ∈ J a → i' ∈ J a →
      roundedVertexCode sys a i = roundedVertexCode sys a i')
    (hq : 0 < q) {H : Finset (Fin D)}
    (hH : (roundedIndexGraph sys J
      (fun a ↦ Finset.card_pos.mp (by rw [hJcard a]; exact hq))).IsClique
        (H : Set (Fin D)))
    {E0 : ℝ} (hE0 : 0 ≤ E0)
    (hclose : ∀ a b, a ≠ b → frobeniusSq
        (bucketBlock bucket (graphAdjacencyMatrix G) (sel a) (sel b) -
          sys.Q a b) ≤ E0) :
    (AKSGraph.edgeCount Gᶜ (refinedVertexUnion J H) : ℝ) ≤
      (H.card : ℝ) * ((q : ℝ) ^ 2 + H.card * E0) := by
  let hJ : ∀ a, (J a).Nonempty :=
    fun a ↦ Finset.card_pos.mp (by rw [hJcard a]; exact hq)
  have hdouble := sum_graphAdjacencyMatrix_eq_twice_edgeCount Gᶜ
    (refinedVertexUnion J H)
  rw [double_sum_refinedVertexUnion hsel J H] at hdouble
  have hblocks : (∑ a ∈ H, ∑ i ∈ J a, ∑ b ∈ H, ∑ j ∈ J b,
      graphAdjacencyMatrix Gᶜ i.1 j.1) ≤
      ∑ a ∈ H, ∑ b ∈ H,
        (if a = b then (q : ℝ) ^ 2 else E0) := by
    simp_rw [Finset.sum_comm (s := J _) (t := H)]
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    by_cases hab : a = b
    · rw [if_pos hab]
      exact block_sum_graph_le_card_sq Gᶜ J hJcard a b
    · rw [if_neg hab]
      rcases lt_or_gt_of_ne hab with halt | hblt
      · exact (cross_sum_compl_le_frobenius_of_one hsel G sys J hab
          (fun {i} {j} hi hj ↦ roundedBlock_eq_one_of_clique
            sys J hcode hJ hH ha hb halt hi hj)).trans (hclose a b hab)
      · rw [cross_sum_graph_comm Gᶜ J a b]
        exact (cross_sum_compl_le_frobenius_of_one hsel G sys J (Ne.symm hab)
          (fun {i} {j} hi hj ↦ roundedBlock_eq_one_of_clique
            sys J hcode hJ hH hb ha hblt hi hj)).trans
          (hclose b a (Ne.symm hab))
  have hsumBound := sum_block_bounds (H := H) (q := q) hE0
    (fun a ha b hb ↦ by
      by_cases hab : a = b
      · simp [hab]
      · simp [hab, hE0])
  have htwo : 2 * (AKSGraph.edgeCount Gᶜ (refinedVertexUnion J H) : ℝ) ≤
      (H.card : ℝ) * ((q : ℝ) ^ 2 + H.card * E0) := by
    rw [← hdouble]
    exact hblocks.trans hsumBound
  have hedge0 : (0 : ℝ) ≤
      (AKSGraph.edgeCount Gᶜ (refinedVertexUnion J H) : ℝ) := by positivity
  nlinarith

/-- Transfer the unconditional finite Erdős--Szemerédi density theorem to
an induced vertex set once the logarithmic Ramsey threshold is verified. -/
lemma ramseyFree_induced_edgeCount_lower
    {n : ℕ} (G : SimpleGraph (Fin n)) (U : Finset (Fin n))
    {C D a : ℝ} {N : ℕ} (hG : RamseyFree C G)
    (hthreshold : C * Real.logb 2 n ≤ D * Real.logb 2 U.card)
    (hN : N ≤ U.card)
    (hdensity : ∀ s : ℕ, N ≤ s → ∀ H : SimpleGraph (Fin s),
      RamseyFree D H → a * (s : ℝ) ^ 2 ≤ (FiniteES.edgeCount H : ℝ)) :
    a * (U.card : ℝ) ^ 2 ≤ (AKSGraph.edgeCount G U : ℝ) := by
  classical
  let H := G.induce (U : Set (Fin n))
  let HF := H.overFin (card_subtype_coe_finset U)
  have hramsey : RamseyFree D HF := by
    exact ramseyFree_induce_overFin G U hG hthreshold
  have hlower := hdensity U.card hN HF hramsey
  have hcount : FiniteES.edgeCount HF = FiniteES.edgeCount H :=
    edgeCount_overFin H (card_subtype_coe_finset U)
  rw [hcount] at hlower
  have hedge : FiniteES.edgeCount H = AKSGraph.edgeCount G U := by
    calc
      FiniteES.edgeCount H = H.edgeFinset.card := rfl
      _ = AKSGraph.edgeCount G U := by
        symm
        simpa only [AKSGraph.edgeCount] using
          G.card_filter_edgeFinset_toFinset_subset U
  rwa [hedge] at hlower

/-- The finite contradiction at the end of the robust-rank argument.  Once
the rounded index graph has a homogeneous `t`-set, the corresponding union
of refined buckets is too sparse in either the graph or its complement to
remain Ramsey-free at the induced density scale. -/
theorem rounded_refinement_density_contradiction
    {n m D r t q : ℕ} {bucket : Fin n → Fin m} {sel : Fin D → Fin m}
    (hsel : Function.Injective sel) (G : SimpleGraph (Fin n))
    (sys : RoundedBucketSystem (r := r) bucket sel)
    (J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a)))
    (hJcard : ∀ a, (J a).card = q)
    (hcode : ∀ a ⦃i i'⦄, i ∈ J a → i' ∈ J a →
      roundedVertexCode sys a i = roundedVertexCode sys a i')
    (hq : 0 < q) {H : Finset (Fin D)} (hHcard : H.card = t)
    (hhom : (roundedIndexGraph sys J
      (fun a ↦ Finset.card_pos.mp (by rw [hJcard a]; exact hq))).IsClique
        (H : Set (Fin D)) ∨
      (roundedIndexGraph sys J
      (fun a ↦ Finset.card_pos.mp (by rw [hJcard a]; exact hq))).IsIndepSet
        (H : Set (Fin D)))
    {E0 C Dens a : ℝ} {N : ℕ} (hE0 : 0 ≤ E0)
    (hclose : ∀ x y, x ≠ y → frobeniusSq
        (bucketBlock bucket (graphAdjacencyMatrix G) (sel x) (sel y) -
          sys.Q x y) ≤ E0)
    (hG : RamseyFree C G)
    (hthreshold : C * Real.logb 2 n ≤
      Dens * Real.logb 2 ((t * q : ℕ) : ℝ))
    (hN : N ≤ t * q)
    (hdensity : ∀ s : ℕ, N ≤ s → ∀ K : SimpleGraph (Fin s),
      RamseyFree Dens K → a * (s : ℝ) ^ 2 ≤ (FiniteES.edgeCount K : ℝ))
    (hgap : (t : ℝ) * ((q : ℝ) ^ 2 + t * E0) <
      a * (t * q : ℕ) ^ 2) : False := by
  let U := refinedVertexUnion J H
  have hUcard : U.card = t * q := by
    simpa [U, hHcard] using card_refinedVertexUnion hsel J hJcard H
  have hthresholdU : C * Real.logb 2 n ≤ Dens * Real.logb 2 U.card := by
    simpa [hUcard] using hthreshold
  have hNU : N ≤ U.card := by simpa [hUcard] using hN
  rcases hhom with hclique | hindep
  · have hlower := ramseyFree_induced_edgeCount_lower Gᶜ U
      ((ramseyFree_compl G).2 hG) hthresholdU hNU hdensity
    have hupper := edgeCount_refined_clique_compl_le hsel G sys J hJcard
      hcode hq hclique hE0 hclose
    rw [hUcard] at hlower
    rw [hHcard] at hupper
    exact (not_lt_of_ge (hlower.trans hupper)) hgap
  · have hlower := ramseyFree_induced_edgeCount_lower G U hG
      hthresholdU hNU hdensity
    have hupper := edgeCount_refined_independent_le hsel G sys J hJcard
      hcode hq hindep hE0 hclose
    rw [hUcard] at hlower
    rw [hHcard] at hupper
    exact (not_lt_of_ge (hlower.trans hupper)) hgap

/-- Elementary supply bounds for the greedy low-error bucket selection. -/
lemma lowError_selection_parameters {D m : ℕ} (hD : 0 < D)
    (hm : 8 * D ≤ m) :
    let q := m / (4 * D)
    let L := m / 2
    0 < q ∧ 0 < L ∧ L + D * q ≤ m ∧
      (m : ℝ) ^ 2 ≤ 32 * D * (q * L : ℕ) := by
  let q := m / (4 * D)
  let L := m / 2
  have hd : 0 < 4 * D := by positivity
  have hdle : 4 * D ≤ m := by omega
  have hq : 0 < q := Nat.div_pos hdle hd
  have hmpos : 0 < m := lt_of_lt_of_le (by positivity : 0 < 8 * D) hm
  have hL : 0 < L := Nat.div_pos (by omega) (by omega)
  have hqUpper : 4 * D * q ≤ m := by
    simpa [q] using Nat.mul_div_le m (4 * D)
  have hLUpper : 2 * L ≤ m := by
    simpa [L] using Nat.mul_div_le m 2
  have hqUpper' : 4 * (D * q) ≤ m := by
    simpa [mul_assoc] using hqUpper
  have hsize : L + D * q ≤ m := by omega
  have hmod : m % (4 * D) < 4 * D := Nat.mod_lt _ hd
  have hdecomp : 4 * D * q + m % (4 * D) = m := by
    simpa [q] using Nat.div_add_mod m (4 * D)
  have hdq : 4 * D ≤ 4 * D * q := by
    simpa using Nat.mul_le_mul_left (4 * D) hq
  have hmqNat : m ≤ 8 * D * q := by
    have hmqNat' : m ≤ 2 * (4 * D * q) := by omega
    calc
      m ≤ 2 * (4 * D * q) := hmqNat'
      _ = 8 * D * q := by ring
  have hmLNat : m ≤ 4 * L := by
    have hLone : 1 ≤ L := hL
    have hmod2 : m % 2 < 2 := Nat.mod_lt _ (by omega)
    have hdecomp2 : 2 * L + m % 2 = m := by
      simpa [L] using Nat.div_add_mod m 2
    omega
  have hmq : (m : ℝ) ≤ 8 * D * q := by exact_mod_cast hmqNat
  have hmL : (m : ℝ) ≤ 4 * L := by exact_mod_cast hmLNat
  have hnonneg : (0 : ℝ) ≤ m := by positivity
  refine ⟨hq, hL, hsize, ?_⟩
  calc
    (m : ℝ) ^ 2 = (m : ℝ) * m := by ring
    _ ≤ (8 * D * q : ℝ) * (4 * L : ℝ) :=
      mul_le_mul hmq hmL hnonneg (by positivity)
    _ = 32 * D * (q * L : ℕ) := by push_cast; ring

/-- Once a positive divisor fits twice, its natural quotient is at least
half of the corresponding real quotient. -/
lemma nat_div_real_lower_half {K s : ℕ} (hK : 0 < K) (hfit : 2 * K ≤ s) :
    (s : ℝ) / (2 * K) ≤ (s / K : ℕ) := by
  let q := s / K
  have hq : 0 < q := Nat.div_pos (by omega) hK
  have hmod : s % K < K := Nat.mod_lt _ hK
  have hdecomp : K * q + s % K = s := by
    simpa [q] using Nat.div_add_mod s K
  have hKq : K ≤ K * q := by
    simpa using Nat.mul_le_mul_left K hq
  have hs : s ≤ 2 * K * q := by
    have hs' : s ≤ 2 * (K * q) := by omega
    calc
      s ≤ 2 * (K * q) := hs'
      _ = 2 * K * q := by ring
  have hKreal : (0 : ℝ) < 2 * K := by positivity
  apply (div_le_iff₀ hKreal).2
  have hsreal : (s : ℝ) ≤ (2 * K * q : ℕ) := by exact_mod_cast hs
  have heq : ((2 * K * q : ℕ) : ℝ) =
      ((s / K : ℕ) : ℝ) * (2 * (K : ℝ)) := by
    dsimp [q]
    push_cast
    ring
  exact hsreal.trans_eq heq

/-- Equal buckets have the expected `n^(1-δ)` lower scale when the number
of buckets is at most `2 n^δ`. -/
lemma equal_bucket_size_rpow_lower {n m s : ℕ} {delta : ℝ}
    (hnpos : 0 < n) (hn : n = m * s)
    (hm : (m : ℝ) ≤ 2 * Real.rpow (n : ℝ) delta) :
    Real.rpow (n : ℝ) (1 - delta) ≤ 2 * (s : ℝ) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hpow : 0 < Real.rpow (n : ℝ) delta := Real.rpow_pos_of_pos hnreal _
  have hncast : (n : ℝ) = (m : ℝ) * s := by exact_mod_cast hn
  apply (mul_le_mul_iff_right₀ hpow).mp
  have hexp : delta + (1 - delta) = 1 := by ring
  calc
    Real.rpow (n : ℝ) delta * Real.rpow (n : ℝ) (1 - delta) =
        Real.rpow (n : ℝ) (delta + (1 - delta)) :=
      (Real.rpow_add hnreal delta (1 - delta)).symm
    _ = (n : ℝ) := by
      rw [hexp]
      exact Real.rpow_one (n : ℝ)
    _ = (m : ℝ) * s := hncast
    _ ≤ Real.rpow (n : ℝ) delta * (2 * (s : ℝ)) := by
      calc
        (m : ℝ) * s ≤ (2 * Real.rpow (n : ℝ) delta) * s :=
          mul_le_mul_of_nonneg_right hm (by positivity)
        _ = Real.rpow (n : ℝ) delta * (2 * (s : ℝ)) := by ring

/-- A bucket of order `n^(1-δ)` still contains `n^((1-δ)/2)` vertices
after division by any fixed positive code-space size, once `n` is large. -/
lemma refined_quotient_rpow_bounds {n s K : ℕ} {delta : ℝ}
    (hnpos : 0 < n) (hK : 0 < K)
    (hsLower : Real.rpow (n : ℝ) (1 - delta) ≤ 2 * (s : ℝ))
    (hgrowth : (4 * K : ℕ) ≤
      Real.rpow (n : ℝ) ((1 - delta) / 2)) :
    2 * K ≤ s ∧
      Real.rpow (n : ℝ) ((1 - delta) / 2) ≤ (s / K : ℕ) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  let x := Real.rpow (n : ℝ) ((1 - delta) / 2)
  have hxpos : 0 < x := Real.rpow_pos_of_pos hnreal _
  have hxSq : x ^ 2 = Real.rpow (n : ℝ) (1 - delta) := by
    dsimp only [x]
    calc
      Real.rpow (n : ℝ) ((1 - delta) / 2) ^ 2 =
          Real.rpow (n : ℝ) ((1 - delta) / 2) *
            Real.rpow (n : ℝ) ((1 - delta) / 2) := by ring
      _ = Real.rpow (n : ℝ)
          (((1 - delta) / 2) + ((1 - delta) / 2)) :=
        (Real.rpow_add hnreal _ _).symm
      _ = Real.rpow (n : ℝ) (1 - delta) := by congr 1 <;> ring
  have hgrowthReal : (4 * (K : ℝ)) ≤ x := by
    exact_mod_cast hgrowth
  have hfitReal : (2 : ℝ) * (K : ℝ) ≤ (s : ℝ) := by
    rw [← hxSq] at hsLower
    have hKone : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hxSqLower : (4 * (K : ℝ)) ^ 2 ≤ x ^ 2 :=
      (sq_le_sq₀ (by positivity) hxpos.le).2 hgrowthReal
    have hKK : (K : ℝ) ≤ (K : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hKone) (by positivity : (0 : ℝ) ≤ K)]
    nlinarith
  have hfit : 2 * K ≤ s := by exact_mod_cast hfitReal
  have hdiv := nat_div_real_lower_half hK hfit
  have hxDiv : x ≤ (s : ℝ) / (2 * K) := by
    rw [← hxSq] at hsLower
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * K)).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hgrowthReal) hxpos.le]
  exact ⟨hfit, hxDiv.trans hdiv⟩

/-- Numerical gap between the homogeneous refined-block upper bound and the
Erdős--Szemerédi density lower bound. -/
lemma homogeneous_refinement_edge_gap {a E0 : ℝ} {t q : ℕ}
    (hat : 4 < a * (t : ℝ)) (hq : 0 < q)
    (hE0 : E0 ≤ (a / 8) * (q : ℝ) ^ 2) :
    (t : ℝ) * ((q : ℝ) ^ 2 + t * E0) <
      a * (t * q : ℕ) ^ 2 := by
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have htReal : (0 : ℝ) < t := by
    have htne : t ≠ 0 := by
      intro htzero
      subst t
      norm_num at hat
    exact_mod_cast Nat.pos_of_ne_zero htne
  have hscalar : 1 + (t : ℝ) * a / 8 < a * t := by
    nlinarith [hat]
  calc
    (t : ℝ) * ((q : ℝ) ^ 2 + t * E0) ≤
        (t : ℝ) * ((q : ℝ) ^ 2 + t * ((a / 8) * (q : ℝ) ^ 2)) := by
      gcongr
    _ = ((t : ℝ) * (q : ℝ) ^ 2) *
          (1 + (t : ℝ) * a / 8) := by ring
    _ < ((t : ℝ) * (q : ℝ) ^ 2) * (a * t) :=
      mul_lt_mul_of_pos_left hscalar (mul_pos htReal (sq_pos_of_pos hqreal))
    _ = a * (t * q : ℕ) ^ 2 := by push_cast; ring

/-- The finite data produced from a globally small Frobenius error: selected
buckets, a binary rounded block system, a common code refinement, and a
homogeneous set in the rounded index graph. -/
structure HomogeneousRoundedRefinement
    {n m : ℕ} (bucket : Fin n → Fin m) (G : SimpleGraph (Fin n))
    (r D t : ℕ) (E0 : ℝ) where
  sel : Fin D → Fin m
  sel_injective : Function.Injective sel
  sys : RoundedBucketSystem (r := r) bucket sel
  q : ℕ
  J : ∀ a : Fin D, Finset (bucketFiber bucket (sel a))
  card_J : ∀ a, (J a).card = q
  code_constant : ∀ a ⦃i i'⦄, i ∈ J a → i' ∈ J a →
    roundedVertexCode sys a i = roundedVertexCode sys a i'
  q_pos : 0 < q
  H : Finset (Fin D)
  card_H : H.card = t
  homogeneous :
    (roundedIndexGraph sys J
      (fun a ↦ Finset.card_pos.mp (by rw [card_J a]; exact q_pos))).IsClique
        (H : Set (Fin D)) ∨
    (roundedIndexGraph sys J
      (fun a ↦ Finset.card_pos.mp (by rw [card_J a]; exact q_pos))).IsIndepSet
        (H : Set (Fin D))
  close : ∀ a b, a ≠ b → frobeniusSq
      (bucketBlock bucket (graphAdjacencyMatrix G) (sel a) (sel b) -
        sys.Q a b) ≤ E0

/-- All finite selection, rounding, refinement, and Ramsey steps in Lemma
10.1, with the asymptotic scalar inequalities left as explicit hypotheses. -/
theorem exists_homogeneousRoundedRefinement_of_small_error
    {n m D r t s : ℕ} (bucket : Fin n → Fin m)
    (G : SimpleGraph (Fin n)) (B : Matrix (Fin n) (Fin n) ℝ)
    (hD : 0 < D) (hm : 8 * D ≤ m) (hspos : 0 < s)
    (hs : ∀ a, (bucketFiber bucket a).card = s)
    (hn : n = m * s) (hBrank : BlockRankAtMost r bucket B)
    {c alpha Cr : ℝ} (hc : 0 < c) (halpha : 0 < alpha)
    (hscale : 64 * D * c < alpha)
    (hsmall : frobeniusSq (graphAdjacencyMatrix G - B) < c * (n : ℝ) ^ 2)
    (hround : ∀ (q : ℕ) (ε : ℝ)
      (A B : Matrix (Fin q) (Fin q) ℝ),
      0 ≤ ε → IsBinary A → B.rank ≤ r →
      frobeniusSq (A - B) ≤ ε * (q : ℝ) ^ 2 →
        ∃ Q : Matrix (Fin q) (Fin q) ℝ,
          IsBinary Q ∧ Q.rank ≤ r ∧
            frobeniusSq (A - Q) ≤ Cr * Real.sqrt ε * (q : ℝ) ^ 2)
    (hcodefit : Fintype.card
      (Fin D → (Fin (2 ^ r) × Fin (2 ^ r))) ≤ s)
    (hRamsey : Ramsey.ramseyNumber t t ≤ D) :
    ∃ R : HomogeneousRoundedRefinement bucket G r D t
      (Cr * Real.sqrt alpha * (s : ℝ) ^ 2),
      R.q = s / Fintype.card
        (Fin D → (Fin (2 ^ r) × Fin (2 ^ r))) := by
  classical
  let M := graphAdjacencyMatrix G - B
  let qSel := m / (4 * D)
  let L := m / 2
  obtain ⟨hqSel, hL, hsize, hmSq⟩ := lowError_selection_parameters hD hm
  have hnreal : (n : ℝ) = (m : ℝ) * s := by exact_mod_cast hn
  have hqLpos : (0 : ℝ) < (qSel * L : ℕ) := by positivity
  have hsreal : (0 : ℝ) < s := by exact_mod_cast hspos
  have hbudget : 2 * frobeniusSq M <
      (qSel * L : ℕ) * (alpha * (s : ℝ) ^ 2) := by
    calc
      2 * frobeniusSq M < 2 * (c * (n : ℝ) ^ 2) := by
        exact mul_lt_mul_of_pos_left hsmall (by norm_num)
      _ = 2 * c * (m : ℝ) ^ 2 * (s : ℝ) ^ 2 := by
        rw [hnreal]
        ring
      _ ≤ (64 * D * c) * (qSel * L : ℕ) * (s : ℝ) ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left hmSq (mul_nonneg (by positivity)
          (sq_nonneg (s : ℝ)))
        nlinarith
      _ < alpha * (qSel * L : ℕ) * (s : ℝ) ^ 2 := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_right hscale hqLpos) (sq_pos_of_pos hsreal)
      _ = (qSel * L : ℕ) * (alpha * (s : ℝ) ^ 2) := by ring
  have htheta : 0 < alpha * (s : ℝ) ^ 2 :=
    mul_pos halpha (sq_pos_of_pos hsreal)
  obtain ⟨T, hTcard, hTpair⟩ := exists_lowError_bucket_subset bucket M
    htheta hL hsize hbudget
  let e : Fin D ≃ T := (Finset.equivFinOfCardEq hTcard).symm
  let sel : Fin D → Fin m := fun a ↦ (e a).1
  have hsel : Function.Injective sel := by
    intro a b hab
    apply e.injective
    exact Subtype.ext hab
  have hpair : ∀ a b : Fin D, a ≠ b →
      bucketError bucket M (sel a) (sel b) ≤ alpha * (s : ℝ) ^ 2 := by
    intro a b hab
    have heab : e a ≠ e b := fun h ↦ hab (e.injective h)
    have hval : (e a).1 ≠ (e b).1 := fun h ↦ heab (Subtype.ext h)
    have hp := hTpair (e a).property (e b).property hval
    have hnonneg := bucketError_nonneg bucket M (sel b) (sel a)
    dsimp only [sel] at hp ⊢
    linarith
  have hsSel : ∀ a, (bucketFiber bucket (sel a)).card = s := fun a ↦ hs _
  obtain ⟨sys, hclose⟩ := exists_roundedBucketSystem_of_lowError
    bucket G B sel hsSel hBrank halpha.le
      (proposition102_equalCard_with_constant r Cr hround) hpair
  obtain ⟨J, hJcard, hcode⟩ := exists_commonRefinement_div sys hsSel
  let codeCount := Fintype.card (Fin D → (Fin (2 ^ r) × Fin (2 ^ r)))
  have hcodepos : 0 < codeCount := Fintype.card_pos
  have hq : 0 < s / codeCount := Nat.div_pos hcodefit hcodepos
  have hJnonempty : ∀ a, (J a).Nonempty :=
    fun a ↦ Finset.card_pos.mp (by rw [hJcard a]; exact hq)
  rcases exists_homogeneous_refinement_indices sys J hJnonempty hRamsey with
    ⟨H, hHcard, hhom⟩ | ⟨H, hHcard, hhom⟩
  · let R : HomogeneousRoundedRefinement bucket G r D t
        (Cr * Real.sqrt alpha * (s : ℝ) ^ 2) :=
      { sel := sel
        sel_injective := hsel
        sys := sys
        q := s / codeCount
        J := J
        card_J := hJcard
        code_constant := hcode
        q_pos := hq
        H := H
        card_H := hHcard
        homogeneous := Or.inl hhom
        close := hclose }
    exact ⟨R, rfl⟩
  · let R : HomogeneousRoundedRefinement bucket G r D t
        (Cr * Real.sqrt alpha * (s : ℝ) ^ 2) :=
      { sel := sel
        sel_injective := hsel
        sys := sys
        q := s / codeCount
        J := J
        card_J := hJcard
        code_constant := hcode
        q_pos := hq
        H := H
        card_H := hHcard
        homogeneous := Or.inr hhom
        close := hclose }
    exact ⟨R, rfl⟩

/-- Kwan--Sah--Sauermann--Sawhney, Lemma 10.1. -/
theorem ksssLemma101 : KSSSLemma101 := by
  intro C delta r hC hdelta hdelta1
  let p : ℝ := (1 - delta) / 2
  have hp : 0 < p := by dsimp [p]; linarith
  let Dens : ℝ := 2 * C / (1 - delta)
  have hDens : 0 < Dens := by
    dsimp [Dens]
    exact div_pos (mul_pos (by norm_num) hC) (sub_pos.mpr hdelta1)
  obtain ⟨a, ha, Ndensity, hdensity⟩ :=
    FiniteES.ramseyFree_edgeCount_density_lower Dens hDens
  let t : ℕ := ⌈4 / a⌉₊ + 1
  have ht : 0 < t := by simp [t]
  have hat : 4 < a * (t : ℝ) := by
    have hceil : 4 / a ≤ (⌈4 / a⌉₊ : ℕ) := Nat.le_ceil _
    have hsucc : ((⌈4 / a⌉₊ : ℕ) : ℝ) < (t : ℝ) := by
      exact_mod_cast (Nat.lt_succ_self ⌈4 / a⌉₊)
    have hdiv : 4 / a < (t : ℝ) := hceil.trans_lt hsucc
    simpa [mul_comm] using (div_lt_iff₀ ha).mp hdiv
  let D : ℕ := Ramsey.ramseyNumber t t + 1
  have hD : 0 < D := by simp [D]
  have hRamsey : Ramsey.ramseyNumber t t ≤ D := by simp [D]
  let codeCount := Fintype.card (Fin D → (Fin (2 ^ r) × Fin (2 ^ r)))
  have hcodeCount : 0 < codeCount := Fintype.card_pos
  obtain ⟨Cr, hCr, hround⟩ := ksssProposition102 r
  let beta : ℝ := a / (32 * Cr * (codeCount : ℝ) ^ 2)
  have hbeta : 0 < beta := by
    dsimp [beta]
    positivity
  let alpha : ℝ := beta ^ 2
  have halpha : 0 < alpha := sq_pos_of_pos hbeta
  have hsqrtAlpha : Real.sqrt alpha = beta := by
    dsimp [alpha]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hbeta]
  let c : ℝ := alpha / (128 * (D : ℝ))
  have hc : 0 < c := div_pos halpha (by positivity)
  have hscale : 64 * (D : ℝ) * c < alpha := by
    have heq : 64 * (D : ℝ) * c = alpha / 2 := by
      dsimp [c]
      field_simp [ne_of_gt (show (0 : ℝ) < D by positivity)]
      <;> ring
    rw [heq]
    linarith
  obtain ⟨Ndelta, hNdelta⟩ := exists_nat_rpow_ge delta (16 * D) hdelta
  obtain ⟨Np, hNp⟩ := exists_nat_rpow_ge p
    (max (4 * codeCount : ℝ) (Ndensity : ℝ)) hp
  let N := max 1 (max Ndelta Np)
  refine ⟨c, hc, N, ?_⟩
  intro n hn m bucket G B hmpos hmlower hmupper hequal hG hBrank
  have hn1 : 1 ≤ n := by dsimp [N] at hn; omega
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hnNdelta : Ndelta ≤ n := by dsimp [N] at hn; omega
  have hnNp : Np ≤ n := by dsimp [N] at hn; omega
  have hpowDelta := hNdelta n hnNdelta
  have hpowP := hNp n hnNp
  have hmSupplyReal : (8 * D : ℕ) ≤ (m : ℝ) := by
    have hpowDelta' : (16 * (D : ℝ)) ≤ Real.rpow (n : ℝ) delta := by
      simpa only [Real.rpow_eq_pow] using hpowDelta
    have h8 : (8 * (D : ℝ)) ≤ Real.rpow (n : ℝ) delta / 2 := by
      linarith
    have h8m : (8 * (D : ℝ)) ≤ (m : ℝ) := h8.trans hmlower
    exact_mod_cast h8m
  have hmSupply : 8 * D ≤ m := by exact_mod_cast hmSupplyReal
  obtain ⟨s, hspos, hs⟩ := hequal
  have hns : n = m * s := card_eq_bucketCount_mul_bucketSize bucket hs
  have hsLower := equal_bucket_size_rpow_lower hnpos hns hmupper
  have hfourCodeReal : (4 : ℝ) * codeCount ≤ Real.rpow (n : ℝ) p := by
    simpa only [Real.rpow_eq_pow] using
      (le_max_left (4 * codeCount : ℝ) (Ndensity : ℝ)).trans hpowP
  have hfourCode : (4 * codeCount : ℕ) ≤ Real.rpow (n : ℝ) p := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hfourCodeReal
  have hfourCode' : (4 * codeCount : ℕ) ≤
      Real.rpow (n : ℝ) ((1 - delta) / 2) := by simpa [p] using hfourCode
  obtain ⟨hcodefit2, hqGrowth⟩ := refined_quotient_rpow_bounds
    hnpos hcodeCount hsLower hfourCode'
  have hcodefit : codeCount ≤ s := by omega
  by_contra hnot
  have hsmall : frobeniusSq (graphAdjacencyMatrix G - B) < c * (n : ℝ) ^ 2 :=
    lt_of_not_ge hnot
  obtain ⟨R, hRq⟩ := exists_homogeneousRoundedRefinement_of_small_error
    bucket G B hD hmSupply hspos hs hns hBrank hc halpha hscale hsmall
    hround hcodefit hRamsey
  have hRq' : R.q = s / codeCount := by simpa [codeCount] using hRq
  have hRqGrowth : Real.rpow (n : ℝ) p ≤ (R.q : ℝ) := by
    rw [hRq']
    simpa [p] using hqGrowth
  have hNdensityPow : (Ndensity : ℝ) ≤ Real.rpow (n : ℝ) p :=
    by simpa only [Real.rpow_eq_pow] using
      (le_max_right (4 * codeCount : ℝ) (Ndensity : ℝ)).trans hpowP
  have hNdensityQ : Ndensity ≤ R.q := by
    exact_mod_cast hNdensityPow.trans hRqGrowth
  have hNdensityUnion : Ndensity ≤ t * R.q := by
    exact hNdensityQ.trans (Nat.le_mul_of_pos_left R.q ht)
  have hqUnion : Real.rpow (n : ℝ) p ≤ (t * R.q : ℕ) := by
    calc
      Real.rpow (n : ℝ) p ≤ (R.q : ℝ) := hRqGrowth
      _ ≤ (t * R.q : ℕ) := by
        exact_mod_cast Nat.le_mul_of_pos_left R.q ht
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hlogMono : Real.logb 2 (Real.rpow (n : ℝ) p) ≤
      Real.logb 2 (t * R.q : ℕ) :=
    Real.logb_le_logb_of_le (by norm_num)
      (Real.rpow_pos_of_pos hnreal p) hqUnion
  have hlogLower : p * Real.logb 2 n ≤
      Real.logb 2 (t * R.q : ℕ) := by
    simpa [Real.logb_rpow_eq_mul_logb_of_pos hnreal] using hlogMono
  have hthreshold : C * Real.logb 2 n ≤
      Dens * Real.logb 2 ((t * R.q : ℕ) : ℝ) := by
    calc
      C * Real.logb 2 n = Dens * (p * Real.logb 2 n) := by
        dsimp [Dens, p]
        field_simp [ne_of_gt (sub_pos.mpr hdelta1)]
        <;> ring
      _ ≤ Dens * Real.logb 2 (t * R.q : ℕ) :=
        mul_le_mul_of_nonneg_left hlogLower hDens.le
  have hdivLower := nat_div_real_lower_half hcodeCount hcodefit2
  rw [← hRq'] at hdivLower
  have hsRq : (s : ℝ) ≤ 2 * (codeCount : ℝ) * R.q := by
    have hden : (0 : ℝ) < 2 * codeCount := by positivity
    have := (div_le_iff₀ hden).mp hdivLower
    nlinarith
  have hsSq : (s : ℝ) ^ 2 ≤
      (2 * (codeCount : ℝ) * R.q) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hsRq
  have hE0 : Cr * Real.sqrt alpha * (s : ℝ) ^ 2 ≤
      (a / 8) * (R.q : ℝ) ^ 2 := by
    calc
      Cr * Real.sqrt alpha * (s : ℝ) ^ 2 =
          Cr * beta * (s : ℝ) ^ 2 := by rw [hsqrtAlpha]
      _ ≤
          Cr * beta * (2 * (codeCount : ℝ) * R.q) ^ 2 :=
        mul_le_mul_of_nonneg_left hsSq (mul_nonneg hCr.le hbeta.le)
      _ = (a / 8) * (R.q : ℝ) ^ 2 := by
        dsimp [beta]
        field_simp [ne_of_gt hCr, ne_of_gt (show (0 : ℝ) < codeCount by positivity)]
        <;> ring
  have hgap : (t : ℝ) * ((R.q : ℝ) ^ 2 +
      t * (Cr * Real.sqrt alpha * (s : ℝ) ^ 2)) <
      a * (t * R.q : ℕ) ^ 2 := by
    exact homogeneous_refinement_edge_gap hat R.q_pos hE0
  exact rounded_refinement_density_contradiction R.sel_injective G R.sys R.J
    R.card_J R.code_constant R.q_pos R.card_H R.homogeneous
    (mul_nonneg (mul_nonneg hCr.le (Real.sqrt_nonneg _)) (sq_nonneg _))
    R.close hG hthreshold hNdensityUnion hdensity hgap

end

end Erdos88.RobustRank
