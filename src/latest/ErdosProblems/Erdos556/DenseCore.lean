import ErdosProblems.Erdos556.Pruning

/-!
# Minimal dense cores with a quadratic margin

A quadratic density margin allows the separator argument to use a single
minimal dense subset instead of a sequence of cuts. This file establishes
the minimality, minimum-degree, and numerical parts of that argument.
-/

namespace Erdos556

open SimpleGraph Finset

/-- Flatten two finite induced subgraphs without changing their edges. -/
noncomputable def induceFinsetMapIso {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (T : Finset S) :
    (G.induce (S : Set V)).induce (T : Set S) ≃g
      G.induce (T.map (Function.Embedding.subtype (fun v => v ∈ S)) : Set V) := by
  let f : ↥(T : Set S) → ↥(T.map (Function.Embedding.subtype (fun v => v ∈ S)) : Set V) :=
    fun x => ⟨x.val.val, mem_map.mpr ⟨x.val, x.property, rfl⟩⟩
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    change (f x).val = (f y).val
    exact congrArg Subtype.val h
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx, hxy⟩ := mem_map.mp y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact { toEquiv := Equiv.ofBijective f ⟨hinj, hsurj⟩, map_rel_iff' := Iff.rfl }

theorem exists_minimal_quadratic_dense_core_of_subset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k η : ℝ) (hη : 0 ≤ η)
    (A : Finset V)
    (he : k * A.card + η * (A.card : ℝ) ^ 2 < ((G.induce (A : Set V)).edgeFinset.card : ℝ)) :
    ∃ S : Finset V, S.Nonempty ∧
      k * S.card + η * (S.card : ℝ) ^ 2 < ((G.induce (S : Set V)).edgeFinset.card : ℝ) ∧
      (∀ v : S, k < (G.induce (S : Set V)).degree v) ∧
      ∀ T : Finset V, T.card < S.card →
        ((G.induce (T : Set V)).edgeFinset.card : ℝ) ≤ k * T.card + η * (T.card : ℝ) ^ 2 := by
  classical
  let good : Finset (Finset V) := univ.filter fun S =>
    k * S.card + η * (S.card : ℝ) ^ 2 < ((G.induce (S : Set V)).edgeFinset.card : ℝ)
  have hA : A ∈ good := mem_filter.mpr ⟨mem_univ _, he⟩
  obtain ⟨S, hS, hminimal⟩ := good.exists_min_image Finset.card ⟨_, hA⟩
  have hgood := (mem_filter.mp hS).2
  have hsmall (T : Finset V) (hT : T.card < S.card) :
      ((G.induce (T : Set V)).edgeFinset.card : ℝ) ≤ k * T.card + η * (T.card : ℝ) ^ 2 := by
    by_contra hn
    have hTgood : T ∈ good := mem_filter.mpr ⟨mem_univ _, lt_of_not_ge hn⟩
    exact (Nat.not_le_of_gt hT) (hminimal T hTgood)
  have hdegree (v : S) : k < (G.induce (S : Set V)).degree v := by
    by_contra hdeg
    have hdeg' := le_of_not_gt hdeg
    let T := S.erase v.val
    have hcard : T.card + 1 = S.card := card_erase_add_one v.property
    have hcardR : (T.card : ℝ) + 1 = S.card := by exact_mod_cast hcard
    have hedge := induced_edges_erase_add_degree G S v
    have hedgeR : ((G.induce (T : Set V)).edgeFinset.card : ℝ) +
        (G.induce (S : Set V)).degree v = (G.induce (S : Set V)).edgeFinset.card := by
      exact_mod_cast hedge
    have hT := hsmall T (by omega)
    have hnonneg := mul_nonneg hη (by positivity : (0 : ℝ) ≤ 2 * (T.card : ℝ) + 1)
    rw [← hcardR] at hgood
    nlinarith
  have hnonempty : S.Nonempty := by
    by_contra h
    have hzero : S.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h)
    have hScard : Fintype.card (S : Set V) = S.card := by
      calc
        Fintype.card (S : Set V) = (S : Set V).ncard := Nat.card_eq_fintype_card.symm
        _ = S.card := Set.ncard_coe_finset S
    have hb := (G.induce (S : Set V)).card_edgeFinset_le_card_choose_two
    rw [hScard, hzero] at hb
    norm_num only [Nat.choose_zero_succ] at hb
    have hezero : (G.induce (S : Set V)).edgeFinset.card = 0 := Nat.eq_zero_of_le_zero hb
    simp [hzero, hezero] at hgood
  exact ⟨S, hnonempty, hgood, hdegree, hsmall⟩

theorem exists_minimal_quadratic_dense_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k η : ℝ) (hη : 0 ≤ η)
    (he : k * Fintype.card V + η * (Fintype.card V : ℝ) ^ 2 < (G.edgeFinset.card : ℝ)) :
    ∃ S : Finset V, S.Nonempty ∧
      k * S.card + η * (S.card : ℝ) ^ 2 < ((G.induce (S : Set V)).edgeFinset.card : ℝ) ∧
      (∀ v : S, k < (G.induce (S : Set V)).degree v) ∧
      ∀ T : Finset V, T.card < S.card →
        ((G.induce (T : Set V)).edgeFinset.card : ℝ) ≤ k * T.card + η * (T.card : ℝ) ^ 2 := by
  have heq : (G.induce ((univ : Finset V) : Set V)).edgeFinset.card = G.edgeFinset.card := by
    rw [← G.card_filter_edgeFinset_toFinset_subset univ]
    simp
  apply exists_minimal_quadratic_dense_core_of_subset G k η hη univ
  simpa only [card_univ, heq] using he

theorem exists_minimal_quadratic_dense_core_internal_of_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k η : ℝ) (hη : 0 ≤ η) (A : Finset V)
    (he : k * A.card + η * (A.card : ℝ) ^ 2 < ((G.induce (A : Set V)).edgeFinset.card : ℝ)) :
    ∃ S : Finset V, S.Nonempty ∧
      k * S.card + η * (S.card : ℝ) ^ 2 < ((G.induce (S : Set V)).edgeFinset.card : ℝ) ∧
      (∀ v : S, k < (G.induce (S : Set V)).degree v) ∧
      ∀ T : Finset S, T.card < S.card →
        (((G.induce (S : Set V)).induce (T : Set S)).edgeFinset.card : ℝ) ≤
          k * T.card + η * (T.card : ℝ) ^ 2 := by
  obtain ⟨S, hS, hdense, hdeg, hsmall⟩ :=
    exists_minimal_quadratic_dense_core_of_subset G k η hη A he
  refine ⟨S, hS, hdense, hdeg, ?_⟩
  intro T hT
  have h := hsmall (T.map (Function.Embedding.subtype (fun v => v ∈ S)))
    (by simpa only [card_map] using hT)
  rw [← (induceFinsetMapIso G S T).card_edgeFinset_eq, card_map] at h
  exact h

theorem exists_minimal_quadratic_dense_core_internal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k η : ℝ) (hη : 0 ≤ η)
    (he : k * Fintype.card V + η * (Fintype.card V : ℝ) ^ 2 < (G.edgeFinset.card : ℝ)) :
    ∃ S : Finset V, S.Nonempty ∧
      k * S.card + η * (S.card : ℝ) ^ 2 < ((G.induce (S : Set V)).edgeFinset.card : ℝ) ∧
      (∀ v : S, k < (G.induce (S : Set V)).degree v) ∧
      ∀ T : Finset S, T.card < S.card →
        (((G.induce (S : Set V)).induce (T : Set S)).edgeFinset.card : ℝ) ≤
          k * T.card + η * (T.card : ℝ) ^ 2 := by
  obtain ⟨S, hS, hdense, hdeg, hsmall⟩ := exists_minimal_quadratic_dense_core G k η hη he
  refine ⟨S, hS, hdense, hdeg, ?_⟩
  intro T hT
  have h := hsmall (T.map (Function.Embedding.subtype (fun v => v ∈ S)))
    (by simpa only [card_map] using hT)
  rw [← (induceFinsetMapIso G S T).card_edgeFinset_eq, card_map] at h
  exact h

/-- The numerical contradiction supplied by a small vertex separator in a
minimal quadratically dense core. -/
theorem quadratic_separator_bound (a b t N k β η e : ℝ)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ht0 : 0 ≤ t) (hk0 : 0 ≤ k) (hη : 0 ≤ η)
    (hN : N = a + b + t) (ht : t ≤ β) (hβ : β ≤ k)
    (ha : k - β ≤ a) (hb : k - β ≤ b)
    (hbudget : β * N ≤ 2 * η * (k - β) ^ 2)
    (he : e ≤ k * (a + b) + η * (a ^ 2 + b ^ 2) + t * N) :
    e ≤ k * N + η * N ^ 2 := by
  have hr0 : 0 ≤ k - β := sub_nonneg.mpr hβ
  have hab : (k - β) ^ 2 ≤ a * b := by
    simpa only [pow_two] using mul_le_mul ha hb hr0 ha0
  have hprod := mul_le_mul_of_nonneg_left hab (by positivity : 0 ≤ 2 * η)
  have hN0 : 0 ≤ N := by linarith
  have htN := mul_le_mul_of_nonneg_right ht hN0
  have hkt := mul_nonneg hk0 ht0
  have hquad := mul_nonneg hη (mul_nonneg ht0 (by linarith : 0 ≤ 2 * N - t))
  have hid : k * N + η * N ^ 2 -
      (k * (a + b) + η * (a ^ 2 + b ^ 2) + t * N) =
      k * t + η * t * (2 * N - t) + 2 * η * (a * b) - t * N := by
    rw [hN]
    ring
  nlinarith

#print axioms exists_minimal_quadratic_dense_core
#print axioms exists_minimal_quadratic_dense_core_internal
#print axioms quadratic_separator_bound

end Erdos556
