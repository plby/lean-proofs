-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.E5Proof

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Disjoint finite chromatic obstructions toward E5

This file strengthens the compactness infrastructure in `E5Proof`.  Inside an
uncountably chromatic triple system one can recursively place finite weak-
chromatic obstructions of every finite order on pairwise disjoint vertex sets,
even while avoiding an arbitrary countable forbidden set.  Thus a countable
edge subhypergraph can retain unbounded finite weak chromatic number.
-/

open Cardinal

namespace Erdos1177

universe u

variable {W : Type u}

/-- The vertex support of a finite family of hyperedges. -/
def finiteEdgeSupport (D : Finset (Set W)) : Set W := ⋃ e ∈ D, e

/-
A finite family of edges in a triple system has finite vertex support.
-/
theorem finite_finiteEdgeSupport (H : Hypergraph W) (htri : H.IsTripleSystem)
    (D : Finset (Set W)) (hD : ∀ e ∈ D, e ∈ H.edges) :
    (finiteEdgeSupport D).Finite := by
      have h_finite_edges : ∀ e ∈ D, Set.Finite e := by
        exact fun e he => Set.finite_of_ncard_ne_zero ( by rw [ htri e ( hD e he ) ] ; norm_num )
      exact Set.Finite.biUnion ( Finset.finite_toSet D ) h_finite_edges

/-
In particular, the support of a finite edge family is countable.
-/
theorem countable_finiteEdgeSupport (H : Hypergraph W) (htri : H.IsTripleSystem)
    (D : Finset (Set W)) (hD : ∀ e ∈ D, e ∈ H.edges) :
    (finiteEdgeSupport D).Countable := by
      exact Set.Finite.countable ( finite_finiteEdgeSupport H htri D hD )

/-
A finite obstruction can be packaged together with a finite vertex support,
chosen outside any prescribed countable set.
-/
theorem exists_supported_finite_obstruction_avoid_countable
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable)
    (k : ℕ) [NeZero k] :
    ∃ D : Finset (Set W), ∃ V : Finset W,
      (∀ e ∈ D, e ∈ H.edges ∧ e ⊆ (V : Set W)) ∧
      (∀ x ∈ V, x ∉ S) ∧
      ¬ ∃ c : W → Fin k,
        (⟨(D : Set (Set W))⟩ : Hypergraph W).ProperColoring c := by
          convert! exists_finite_edge_coloring_obstruction_avoid_countable H htri huc hS k using 1;
          ext D;
          constructor <;> intro h;
          · grind;
          · use Set.Finite.toFinset (finite_finiteEdgeSupport H htri D (fun e he => h.left e he |>.1));
            simp_all +decide only [Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, not_exists];
            exact ⟨ fun e he x hx => Set.mem_iUnion₂.2 ⟨ e, he, hx ⟩, fun x hx => by rcases Set.mem_iUnion₂.1 hx with ⟨ e, he, hx ⟩ ; exact h.1 e he |>.2 hx ⟩

/-
There is a sequence of pairwise vertex-disjoint finite edge subhypergraphs,
where the `n`th member cannot be weakly coloured with `n+1` colours.  All their
vertices may simultaneously be required to avoid a fixed countable set.
-/
theorem exists_disjoint_finite_obstruction_sequence
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable) :
    ∃ D : ℕ → Finset (Set W),
      (∀ n e, e ∈ D n → e ∈ H.edges ∧ e ⊆ Sᶜ) ∧
      (∀ ⦃m n⦄, m ≠ n →
        Disjoint (finiteEdgeSupport (D m)) (finiteEdgeSupport (D n))) ∧
      (∀ n, ¬ ∃ c : W → Fin (n + 1),
        (⟨(D n : Set (Set W))⟩ : Hypergraph W).ProperColoring c) := by
          -- By induction, we construct a sequence of finite edge sets $D_n$ along with vertex sets $E_n$ such that:
          -- - $D_n$ supports $E_n$, all vertices in $E_n$ are not in $S$ or the union of prior $E_m$ for $m < n$.
          -- - $D_n$ cannot be $(n+1)$-coloured.
          have h_seq : ∃ (E : ℕ → Finset W) (D : ℕ → Finset (Set W)),
            (∀ n, (∀ e ∈ D n, e ∈ H.edges ∧ e ⊆ (E n : Set W))) ∧
            (∀ n, (∀ x ∈ E n, x ∉ S) ∧ (∀ m < n, Disjoint (E m : Set W) (E n : Set W))) ∧
            (∀ n, ¬∃ c : W → Fin (n + 1), (⟨(D n : Set (Set W))⟩ : Hypergraph W).ProperColoring c) := by
              have h_seq : ∀ (n : ℕ) (U : Set W) (hU : U.Countable), ∃ (E : Finset W) (D : Finset (Set W)),
                (∀ e ∈ D, e ∈ H.edges ∧ e ⊆ (E : Set W)) ∧
                (∀ x ∈ E, x ∉ S) ∧
                Disjoint (E : Set W) U ∧
                ¬∃ c : W → Fin (n + 1), (⟨(D : Set (Set W))⟩ : Hypergraph W).ProperColoring c := by
                  intro n U hU
                  obtain ⟨D, V, hD, hV, hob⟩ := exists_supported_finite_obstruction_avoid_countable H htri huc (hS.union hU) (n + 1);
                  exact ⟨ V, D, hD, fun x hx => by specialize hV x hx; aesop, Set.disjoint_left.mpr fun x hxV hxU => by specialize hV x hxV; aesop, hob ⟩;
              choose! E D hED using h_seq;
              -- Define the sequence of vertex sets $U_n$ and edge sets $D_n$.
              obtain ⟨U, hU⟩ : ∃ U : ℕ → Set W, (∀ n, (U n).Countable) ∧ (∀ n, U (n + 1) = U n ∪ (E n (U n) : Set W)) ∧ U 0 = ∅ := by
                refine' ⟨ fun n => Nat.recOn n ∅ fun n ih => ih ∪ ( E n ih : Set W ), _, _, _ ⟩ <;> simp +decide;
                intro n; induction n <;> simp_all +decide [ Set.countable_empty, Set.countable_union ] ;
                exact Set.to_countable _;
              refine' ⟨ fun n => E n ( U n ), fun n => D n ( U n ), _, _, _ ⟩ <;> simp_all +decide only [Finset.disjoint_coe];
              · exact fun n e he => hED n ( U n ) ( hU.1 n ) |>.1 e he |>.1;
              · refine' fun n => ⟨ hED n ( U n ) ( hU.1 n ) |>.2.1, fun m mn => _ ⟩;
                intro x hx₁ hx₂; have := hED n ( U n ) ( hU.1 n ) |>.2.2.1 hx₂; simp_all +decide [ Set.subset_def ] ;
                exact this ( by exact Nat.le_induction ( by aesop ) ( fun k hk ih => by aesop ) n mn );
          obtain ⟨ E, D, hE, hD, hD' ⟩ := h_seq;
          refine' ⟨ D, _, _, hD' ⟩;
          · exact fun n e he => ⟨ hE n e he |>.1, fun x hx => hD n |>.1 x ( hE n e he |>.2 hx ) ⟩;
          · intro m n mn; cases lt_or_gt_of_ne mn <;> simp_all +decide [ Set.disjoint_left ] ;
            · simp_all +decide [ finiteEdgeSupport ];
              exact fun a e he ha f hf => fun ha' => hD n |>.2 m ‹_› ( hE m e he |>.2 ha ) ( hE n f hf |>.2 ha' );
            · simp_all +decide [ finiteEdgeSupport ];
              intro a x hx hx' y hy hy'; have := hE m x hx; have := hE n y hy; simp_all +decide [ Set.subset_def ] ;
              exact hD m |>.2 n ‹_› ( this.2 a hy' ) ( ‹x ∈ H.edges ∧ ∀ x_1 ∈ x, x_1 ∈ E m›.2 a hx' )

/-
The union of the disjoint obstruction sequence is a countable family of
host edges and has no proper colouring by any positive finite palette.
-/
theorem exists_countable_edge_subhypergraph_unbounded_finite_chromatic
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable) :
    ∃ A : Set (Set W),
      A.Countable ∧ A ⊆ H.edges ∧ (∀ e ∈ A, e ⊆ Sᶜ) ∧
      ∀ k : ℕ, 0 < k →
        ¬ ∃ c : W → Fin k, (⟨A⟩ : Hypergraph W).ProperColoring c := by
          obtain ⟨D, hD⟩ := exists_disjoint_finite_obstruction_sequence H htri huc hS;
          refine' ⟨ ⋃ n, D n, Set.countable_iUnion fun n => Finset.countable_toSet _, _, _, _ ⟩ <;> simp_all +decide only [Set.iUnion_subset_iff, Set.mem_iUnion, SetLike.mem_coe, forall_exists_index,
    not_exists];
          · exact fun e n he => hD.1 n e he |>.1;
          · exact fun e n he x hx => hD.1 n e he |>.2 x hx;
          · intro k hk x hx; specialize hD; have := hD.2.2 ( k - 1 ) ( fun w => Fin.castLE ( by omega ) ( x w ) ) ; simp_all +decide [ Hypergraph.ProperColoring ] ;
            grind

/-
The disjoint obstruction sequence can simultaneously avoid a countable set
of vertices and a countable family of forbidden edges.
-/
theorem exists_disjoint_finite_obstruction_sequence_avoid_edges
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable)
    {B : Set (Set W)} (hB : B.Countable) :
    ∃ D : ℕ → Finset (Set W),
      (∀ n e, e ∈ D n → e ∈ H.edges ∧ e ∉ B ∧ e ⊆ Sᶜ) ∧
      (∀ ⦃m n⦄, m ≠ n →
        Disjoint (finiteEdgeSupport (D m)) (finiteEdgeSupport (D n))) ∧
      (∀ n, ¬ ∃ c : W → Fin (n + 1),
        (⟨(D n : Set (Set W))⟩ : Hypergraph W).ProperColoring c) := by
          obtain ⟨D, hD⟩ := exists_disjoint_finite_obstruction_sequence (⟨{e | e ∈ H.edges ∧ e ∉ B}⟩ : Hypergraph W) (by
          exact fun e he => htri e he.1) (by
          apply uncountablyChromatic_delete_countable_edges H htri huc hB) hS;
          exact ⟨ D, fun n e he => ⟨ hD.1 n e he |>.1.1, hD.1 n e he |>.1.2, hD.1 n e he |>.2 ⟩, hD.2.1, hD.2.2 ⟩

/-
There is a countable vertex-supported subhypergraph, wholly outside any
prescribed countable vertex and edge sets, whose finite weak chromatic numbers
are unbounded.
-/
theorem exists_countable_supported_unbounded_chromatic_avoid
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable)
    {B : Set (Set W)} (hB : B.Countable) :
    ∃ A : Set (Set W), ∃ V : Set W,
      A.Countable ∧ V.Countable ∧ A ⊆ H.edges ∧
      (∀ e ∈ A, e ∉ B ∧ e ⊆ V) ∧ V ⊆ Sᶜ ∧
      ∀ k : ℕ, 0 < k →
        ¬ ∃ c : W → Fin k, (⟨A⟩ : Hypergraph W).ProperColoring c := by
          obtain ⟨ D, hD₁, hD₂, hD₃ ⟩ := exists_disjoint_finite_obstruction_sequence_avoid_edges H htri huc hS hB;
          refine' ⟨ ⋃ n, D n, ⋃ n, finiteEdgeSupport ( D n ), _, _, _, _, _ ⟩ <;> simp_all +decide only [Set.countable_iUnion_iff, Set.iUnion_subset_iff, not_exists, Set.mem_iUnion,
    SetLike.mem_coe, forall_exists_index];
          · exact fun n => Set.to_countable _;
          · exact fun n => countable_finiteEdgeSupport H htri ( D n ) fun e he => hD₁ n e he |>.1;
          · exact fun e n he => hD₁ n e he |>.1;
          · exact fun e n he => ⟨ hD₁ n e he |>.2.1, fun x hx => ⟨ n, Set.mem_iUnion₂.2 ⟨ e, he, hx ⟩ ⟩ ⟩;
          · refine' ⟨ _, _ ⟩;
            · intro x n hx; obtain ⟨ e, he, hx ⟩ := Set.mem_iUnion₂.mp hx; specialize hD₁ n e he; aesop;
            · intro k hk x hx; specialize hD₃ ( k - 1 ) ( fun w => Fin.castLE ( by omega ) ( x w ) ) ; simp_all +decide [ Hypergraph.ProperColoring ] ;
              grind

/-
Consequently, every uncountably chromatic triple system contains, away
from arbitrary countable forbidden vertex and edge sets, a countably
colourable subhypergraph which is not colourable by any finite palette.
-/
theorem exists_exactly_countably_chromatic_subhypergraph_avoid
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable)
    {B : Set (Set W)} (hB : B.Countable) :
    ∃ A : Set (Set W),
      A.Countable ∧ A ⊆ H.edges ∧ (∀ e ∈ A, e ∉ B ∧ e ⊆ Sᶜ) ∧
      (⟨A⟩ : Hypergraph W).ColorableBy ℵ₀ ∧
      ∀ k : ℕ, 0 < k →
        ¬ ∃ c : W → Fin k, (⟨A⟩ : Hypergraph W).ProperColoring c := by
          obtain ⟨ A, V, hA, hV, hA_sub, hA_prop, hV_sub, hA_unbounded ⟩ := exists_countable_supported_unbounded_chromatic_avoid H htri huc hS hB;
          refine' ⟨ A, hA, hA_sub, fun e he => ⟨ hA_prop e he |>.1, hA_prop e he |>.2.trans hV_sub ⟩, _, hA_unbounded ⟩;
          convert! colorable_of_countable_edges ⟨ A ⟩ _ hA using 1;
          exact fun e he => htri e ( hA_sub he )

/-
In a linear host, the exactly countably chromatic subhypergraph supplied
above remains a linear triple system.
-/
theorem exists_linear_exactly_countably_chromatic_subhypergraph_avoid
    (H : Hypergraph W) (htri : H.IsTripleSystem) (hlin : H.Linear)
    (huc : H.UncountablyChromatic) {S : Set W} (hS : S.Countable)
    {B : Set (Set W)} (hB : B.Countable) :
    ∃ A : Set (Set W),
      A.Countable ∧ A ⊆ H.edges ∧ (∀ e ∈ A, e ∉ B ∧ e ⊆ Sᶜ) ∧
      (⟨A⟩ : Hypergraph W).IsTripleSystem ∧
      (⟨A⟩ : Hypergraph W).Linear ∧
      (⟨A⟩ : Hypergraph W).ColorableBy ℵ₀ ∧
      ∀ k : ℕ, 0 < k →
        ¬ ∃ c : W → Fin k, (⟨A⟩ : Hypergraph W).ProperColoring c := by
          obtain ⟨ A, hA₁, hA₂, hA₃, hA₄, hA₅ ⟩ := exists_exactly_countably_chromatic_subhypergraph_avoid H htri huc hS hB;
          refine' ⟨ A, hA₁, hA₂, hA₃, _, _, hA₄, hA₅ ⟩;
          · exact fun e he => htri e ( hA₂ he );
          · exact fun e₁ he₁ e₂ he₂ hne => hlin e₁ ( hA₂ he₁ ) e₂ ( hA₂ he₂ ) hne

end Erdos1177
