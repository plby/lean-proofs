-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.E5Obstructions

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A two-dimensional array of disjoint finite obstructions toward E5

The one-dimensional obstruction sequence can be reindexed so that every finite
chromatic threshold occurs infinitely often, while all supports remain pairwise
disjoint.  This is useful for infinitary thinning arguments: discarding
arbitrarily many previously selected finite blocks never exhausts the supply at
any fixed threshold.
-/

open Cardinal

namespace Erdos1177

universe u

variable {W : Type u}

/-
Every uncountably chromatic triple system contains a pairwise
vertex-disjoint grid of finite edge systems.  The block in row `k` cannot be
weakly coloured with `k+1` colours, and the whole grid avoids any prescribed
countable vertex set.
-/
theorem exists_disjoint_finite_obstruction_grid
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable) :
    ∃ D : ℕ → ℕ → Finset (Set W),
      (∀ k r e, e ∈ D k r → e ∈ H.edges ∧ e ⊆ Sᶜ) ∧
      (∀ ⦃k r l s⦄, (k, r) ≠ (l, s) →
        Disjoint (finiteEdgeSupport (D k r)) (finiteEdgeSupport (D l s))) ∧
      (∀ k r, ¬ ∃ c : W → Fin (k + 1),
        (⟨(D k r : Set (Set W))⟩ : Hypergraph W).ProperColoring c) := by
  -- Apply `exists_disjoint_finite_obstruction_sequence` to obtain `E : ℕ → Finset (Set W)`.
  obtain ⟨E, hE⟩ := exists_disjoint_finite_obstruction_sequence H htri huc hS;
  refine' ⟨ fun k r => E ( Nat.pair k r ), _, _, _ ⟩ <;> simp_all +decide;
  · exact fun k r e he => hE.1 _ _ he;
  · intro k r x hx; specialize hE; have := hE.2.2 ( Nat.pair k r ) ( fun w => Fin.castLE ( by linarith [ Nat.left_le_pair k r ] ) ( x w ) ) ; simp_all +decide [ Hypergraph.ProperColoring ] ;

/-
The union of each row of the obstruction grid is a countable host-edge
family, supported away from the forbidden set, and still fails the row's finite
palette.
-/
theorem exists_disjoint_countable_obstruction_rows
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable) :
    ∃ A : ℕ → Set (Set W),
      (∀ k, (A k).Countable ∧ A k ⊆ H.edges ∧ ∀ e ∈ A k, e ⊆ Sᶜ) ∧
      (∀ ⦃k l⦄, k ≠ l →
        Disjoint (⋃ e ∈ A k, e) (⋃ e ∈ A l, e)) ∧
      (∀ k, ¬ ∃ c : W → Fin (k + 1),
        (⟨A k⟩ : Hypergraph W).ProperColoring c) := by
  obtain ⟨ D, hD₁, hD₂, hD₃ ⟩ := exists_disjoint_finite_obstruction_grid H htri huc hS;
  refine' ⟨ fun k => ⋃ r, ( D k r : Set ( Set W ) ), _, _, _ ⟩;
  · simp +zetaDelta at *;
    exact fun k => ⟨ fun i => Set.to_countable _, fun i => fun e he => hD₁ k i e he |>.1, fun e i he => hD₁ k i e he |>.2 ⟩;
  · intro k l hkl; simp_all +decide [ Set.disjoint_left ] ;
    intro a e r he ha f s hf; specialize hD₂ ( show k = l → ¬r = s from by tauto ) ; simp_all +decide [ finiteEdgeSupport ] ;
    exact hD₂ _ he ha _ hf;
  · intro k hk
    obtain ⟨c, hc⟩ := hk;
    exact hD₃ k 0 ⟨ c, fun e he => hc e <| Set.mem_iUnion_of_mem _ he ⟩

/-
There are countably many pairwise vertex-disjoint, countable edge
subhypergraphs with unbounded finite weak chromatic number.
-/
theorem exists_disjoint_countable_unbounded_chromatic_family
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable) :
    ∃ A : ℕ → Set (Set W),
      (∀ r, (A r).Countable ∧ A r ⊆ H.edges ∧ ∀ e ∈ A r, e ⊆ Sᶜ) ∧
      (∀ ⦃r s⦄, r ≠ s →
        Disjoint (⋃ e ∈ A r, e) (⋃ e ∈ A s, e)) ∧
      (∀ r k, 0 < k → ¬ ∃ c : W → Fin k,
        (⟨A r⟩ : Hypergraph W).ProperColoring c) := by
  obtain ⟨ D, hD₁, hD₂, hD₃ ⟩ := exists_disjoint_finite_obstruction_grid H htri huc hS;
  refine' ⟨ fun r ↦ ⋃ k, ( D k r : Set ( Set W ) ), _, _, _ ⟩ <;> simp_all +decide [ Set.subset_def ];
  · exact fun r => ⟨ fun i => Set.to_countable _, fun e k he => hD₁ k r e he |>.1, fun e k he x hx => hD₁ k r e he |>.2 x hx ⟩;
  · intro r s hrs i k hi j l hj; specialize @hD₂ l r k s; simp_all +decide [ Set.disjoint_left ] ;
    exact fun x hx₁ hx₂ => hD₂ ( Set.mem_iUnion₂.mpr ⟨ j, hj, hx₁ ⟩ ) ( Set.mem_iUnion₂.mpr ⟨ i, hi, hx₂ ⟩ );
  · intro r k hk x hx;
    contrapose! hD₃;
    refine' ⟨ k - 1, r, fun w => Fin.castLE ( by omega ) ( x w ), _ ⟩;
    intro e he; specialize hx e; simp_all +decide;
    exact hx _ he

/-
In a linear host, each member of the preceding disjoint family remains a
linear triple system, is countably colourable, and is not colourable by any
finite positive palette.
-/
theorem exists_disjoint_linear_exactly_countably_chromatic_family
    (H : Hypergraph W) (htri : H.IsTripleSystem) (hlin : H.Linear)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable) :
    ∃ A : ℕ → Set (Set W),
      (∀ r, (A r).Countable ∧ A r ⊆ H.edges ∧ (∀ e ∈ A r, e ⊆ Sᶜ) ∧
        (⟨A r⟩ : Hypergraph W).IsTripleSystem ∧
        (⟨A r⟩ : Hypergraph W).Linear ∧
        (⟨A r⟩ : Hypergraph W).ColorableBy ℵ₀ ∧
        ∀ k, 0 < k → ¬ ∃ c : W → Fin k,
          (⟨A r⟩ : Hypergraph W).ProperColoring c) ∧
      (∀ ⦃r s⦄, r ≠ s →
        Disjoint (⋃ e ∈ A r, e) (⋃ e ∈ A s, e)) := by
  obtain ⟨A, hA⟩ := exists_disjoint_countable_unbounded_chromatic_family H htri huc hS;
  refine' ⟨ A, _, _ ⟩;
  · intro r
    obtain ⟨hA_countable, hA_subset, hA_avoid⟩ := hA.left r
    have hA_linear : (⟨A r⟩ : Hypergraph W).Linear := by
      exact fun e he f hf hef => hlin e ( hA_subset he ) f ( hA_subset hf ) hef
    have hA_colorable : (⟨A r⟩ : Hypergraph W).ColorableBy ℵ₀ := by
      exact colorable_of_countable_edges _ ( show ( ⟨ A r ⟩ : Hypergraph W ).IsTripleSystem from fun e he => htri e ( hA_subset he ) ) hA_countable
    exact ⟨hA_countable, hA_subset, hA_avoid, by
      exact fun e he => htri e ( hA_subset he ), hA_linear, hA_colorable, hA.right.right r⟩;
  · exact hA.2.1

/-
The obstruction grid can simultaneously avoid a prescribed countable
family of host edges.
-/
theorem exists_disjoint_finite_obstruction_grid_avoid_edges
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable)
    {B : Set (Set W)} (hB : B.Countable) :
    ∃ D : ℕ → ℕ → Finset (Set W),
      (∀ k r e, e ∈ D k r → e ∈ H.edges ∧ e ∉ B ∧ e ⊆ Sᶜ) ∧
      (∀ ⦃k r l s⦄, (k, r) ≠ (l, s) →
        Disjoint (finiteEdgeSupport (D k r)) (finiteEdgeSupport (D l s))) ∧
      (∀ k r, ¬ ∃ c : W → Fin (k + 1),
        (⟨(D k r : Set (Set W))⟩ : Hypergraph W).ProperColoring c) := by
  obtain ⟨H', hH'⟩ : ∃ H' : Hypergraph W, H'.edges = {e ∈ H.edges | e ∉ B} ∧ H'.IsTripleSystem ∧ H'.UncountablyChromatic := by
    refine' ⟨ ⟨ { e | e ∈ H.edges ∧ e ∉ B } ⟩, rfl, _, _ ⟩;
    · exact fun e he => htri e he.1;
    · exact uncountablyChromatic_delete_countable_edges H htri huc hB;
  convert! exists_disjoint_finite_obstruction_grid H' hH'.2.1 hH'.2.2 hS using 1;
  simp +decide [ hH'.1, and_assoc ]

/-
Even after forbidding countably many vertices and countably many edges,
there remain countably many mutually vertex-disjoint countable subhypergraphs,
each of unbounded finite weak chromatic number.
-/
theorem exists_disjoint_countable_unbounded_chromatic_family_avoid
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable)
    {B : Set (Set W)} (hB : B.Countable) :
    ∃ A : ℕ → Set (Set W),
      (∀ r, (A r).Countable ∧ A r ⊆ H.edges ∧
        (∀ e ∈ A r, e ∉ B ∧ e ⊆ Sᶜ)) ∧
      (∀ ⦃r s⦄, r ≠ s →
        Disjoint (⋃ e ∈ A r, e) (⋃ e ∈ A s, e)) ∧
      (∀ r k, 0 < k → ¬ ∃ c : W → Fin k,
        (⟨A r⟩ : Hypergraph W).ProperColoring c) := by
  -- Use the edge-avoiding grid to define the family A.
  obtain ⟨D, hD⟩ := exists_disjoint_finite_obstruction_grid_avoid_edges H htri huc hS hB;
  refine' ⟨ fun r => ⋃ k, D k r, _, _, _ ⟩;
  · exact fun r => ⟨ Set.countable_iUnion fun k => Finset.countable_toSet _, Set.iUnion_subset fun k => fun e he => hD.1 k r e he |>.1, fun e he => by obtain ⟨ k, hk ⟩ := Set.mem_iUnion.mp he; exact hD.1 k r e hk |>.2 ⟩;
  · simp +contextual [ Set.disjoint_left, finiteEdgeSupport ] at hD ⊢;
    grind;
  · intro r k hk;
    rintro ⟨ c, hc ⟩;
    refine' hD.2.2 ( k - 1 ) r ⟨ fun x => Fin.castLE ( by omega ) ( c x ), _ ⟩;
    intro e he; specialize hc e; aesop;

/-
In a linear host the preceding edge-avoiding family consists of linear,
exactly countably chromatic triple systems.
-/
theorem exists_disjoint_linear_exactly_countably_chromatic_family_avoid
    (H : Hypergraph W) (htri : H.IsTripleSystem) (hlin : H.Linear)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable)
    {B : Set (Set W)} (hB : B.Countable) :
    ∃ A : ℕ → Set (Set W),
      (∀ r, (A r).Countable ∧ A r ⊆ H.edges ∧
        (∀ e ∈ A r, e ∉ B ∧ e ⊆ Sᶜ) ∧
        (⟨A r⟩ : Hypergraph W).IsTripleSystem ∧
        (⟨A r⟩ : Hypergraph W).Linear ∧
        (⟨A r⟩ : Hypergraph W).ColorableBy ℵ₀ ∧
        ∀ k, 0 < k → ¬ ∃ c : W → Fin k,
          (⟨A r⟩ : Hypergraph W).ProperColoring c) ∧
      (∀ ⦃r s⦄, r ≠ s →
        Disjoint (⋃ e ∈ A r, e) (⋃ e ∈ A s, e)) := by
  have h_linear : ∀ (A : Set (Set W)), A ⊆ H.edges → (⟨A⟩ : Hypergraph W).Linear := by
    intro A hA; intro e₁ he₁ e₂ he₂ hne; exact (by
    exact hlin _ ( hA he₁ ) _ ( hA he₂ ) hne);
  obtain ⟨A, hA⟩ := exists_disjoint_countable_unbounded_chromatic_family_avoid H htri huc hS hB;
  refine' ⟨ A, _, _ ⟩;
  · intro r
    obtain ⟨hA_countable, hA_subset, hA_avoid⟩ := hA.left r
    exact ⟨hA_countable, hA_subset, hA_avoid, by
      exact fun e he => htri e ( hA_subset he ), by
      exact h_linear _ hA_subset, by
      exact colorable_of_countable_edges ⟨ A r ⟩ ( fun e he => htri e ( hA_subset he ) ) hA_countable, by
      exact hA.2.2 r⟩;
  · exact hA.2.1

end Erdos1177
