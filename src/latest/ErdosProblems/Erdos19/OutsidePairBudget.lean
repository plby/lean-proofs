import ErdosProblems.Erdos19.PairCompression

/-! # Pair budgets outside a fixed edge

An edge with many vertices reduces the number of almost-projective edges
which can coexist with it. The count uses ordered pairs outside that edge.
-/

namespace Erdos19.SetHypergraph

variable {X : Type*} [Fintype X]

theorem sum_outside_pair_weight_le (H : SetHypergraph X)
    (hlinear : H.IsLinear) (U : Set X) :
    (∑ e : H, (e.1 \ U).ncard * ((e.1 \ U).ncard - 1)) ≤
      Uᶜ.ncard * (Uᶜ.ncard - 1) := by
  classical
  let Fiber (e : H) := OrderedPairsInSet (e.1 \ U)
  let code (p : Σ e : H, Fiber e) : OrderedPairsInSet Uᶜ :=
    ⟨p.2.1, p.2.2.1.2, p.2.2.2.1.2, p.2.2.2.2⟩
  have hinj : Function.Injective code := by
    intro p q hpq
    have hpairs : p.2.1 = q.2.1 := congrArg Subtype.val hpq
    have hedge : p.1 = q.1 := by
      apply Subtype.ext
      by_contra hne
      have hsub := hlinear p.1.2 q.1.2 hne
      have hx : p.2.1.1 ∈ p.1.1 ∩ q.1.1 := by
        refine ⟨p.2.2.1.1, ?_⟩
        rw [congrArg Prod.fst hpairs]
        exact q.2.2.1.1
      have hy : p.2.1.2 ∈ p.1.1 ∩ q.1.1 := by
        refine ⟨p.2.2.2.1.1, ?_⟩
        rw [congrArg Prod.snd hpairs]
        exact q.2.2.2.1.1
      exact p.2.2.2.2 (hsub hx hy)
    apply Sigma.ext hedge
    exact (Subtype.heq_iff_coe_eq (fun z ↦ by rw [hedge])).2 hpairs
  calc
    (∑ e : H, (e.1 \ U).ncard * ((e.1 \ U).ncard - 1)) =
        ∑ e : H, Fintype.card (Fiber e) := by
      apply Finset.sum_congr rfl
      intro e _
      exact (card_orderedPairsInSet (e.1 \ U)).symm
    _ = Fintype.card (Σ e : H, Fiber e) := Fintype.card_sigma.symm
    _ ≤ Fintype.card (OrderedPairsInSet Uᶜ) := Fintype.card_le_of_injective code hinj
    _ = Uᶜ.ncard * (Uᶜ.ncard - 1) := card_orderedPairsInSet Uᶜ

theorem edge_family_count_mul_le_outside_pair_budget (H : SetHypergraph X)
    (hlinear : H.IsLinear) (S : Finset H) (e₀ : H) (r : ℕ)
    (hmin : ∀ e ∈ S, r ≤ e.1.ncard) :
    (S.card - 1) * ((r - 1) * (r - 2)) ≤
      (Fintype.card X - e₀.1.ncard) * (Fintype.card X - e₀.1.ncard - 1) := by
  classical
  let T := S.erase e₀
  have hT : S.card - 1 ≤ T.card := by
    dsimp only [T]
    rw [Finset.card_erase_eq_ite]
    split <;> omega
  have hout (e : H) (he : e ∈ T) : r - 1 ≤ (e.1 \ e₀.1).ncard := by
    have hne : e.1 ≠ e₀.1 := fun h ↦ (Finset.mem_erase.mp he).1 (Subtype.ext h)
    have hmeet : (e.1 ∩ e₀.1).ncard ≤ 1 :=
      Set.ncard_le_one_iff_subsingleton.mpr (hlinear e.2 e₀.2 hne)
    have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard e.1 e₀.1
    have hsize := hmin e (Finset.mem_erase.mp he).2
    omega
  have hlower : (S.card - 1) * ((r - 1) * (r - 2)) ≤
      ∑ e : H, (e.1 \ e₀.1).ncard * ((e.1 \ e₀.1).ncard - 1) := by
    calc
      (S.card - 1) * ((r - 1) * (r - 2)) ≤
          T.card * ((r - 1) * (r - 2)) := Nat.mul_le_mul_right _ hT
      _ = ∑ _e ∈ T, (r - 1) * (r - 2) := by simp
      _ ≤ ∑ e ∈ T, (e.1 \ e₀.1).ncard * ((e.1 \ e₀.1).ncard - 1) := by
        apply Finset.sum_le_sum
        intro e he
        have h := hout e he
        exact Nat.mul_le_mul h (by omega)
      _ ≤ ∑ e : H, (e.1 \ e₀.1).ncard * ((e.1 \ e₀.1).ncard - 1) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have htotal := H.sum_outside_pair_weight_le hlinear e₀.1
  rw [Set.ncard_compl, Nat.card_eq_fintype_card] at htotal
  exact hlower.trans htotal


theorem edge_count_mul_le_outside_pair_budget (H : SetHypergraph X)
    (hlinear : H.IsLinear) (e₀ : H) (r : ℕ)
    (hmin : ∀ e : H, r ≤ e.1.ncard) :
    (Fintype.card H - 1) * ((r - 1) * (r - 2)) ≤
      (Fintype.card X - e₀.1.ncard) * (Fintype.card X - e₀.1.ncard - 1) := by
  classical
  let S : Finset H := Finset.univ.erase e₀
  have hS : S.card = Fintype.card H - 1 := by simp [S]
  have hout (e : H) (he : e ∈ S) : r - 1 ≤ (e.1 \ e₀.1).ncard := by
    have hne : e.1 ≠ e₀.1 := fun h ↦ (Finset.mem_erase.mp he).1 (Subtype.ext h)
    have hmeet : (e.1 ∩ e₀.1).ncard ≤ 1 :=
      Set.ncard_le_one_iff_subsingleton.mpr (hlinear e.2 e₀.2 hne)
    have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard e.1 e₀.1
    have hsize := hmin e
    omega
  have hlower : (Fintype.card H - 1) * ((r - 1) * (r - 2)) ≤
      ∑ e : H, (e.1 \ e₀.1).ncard * ((e.1 \ e₀.1).ncard - 1) := by
    calc
      (Fintype.card H - 1) * ((r - 1) * (r - 2)) =
          ∑ _e ∈ S, (r - 1) * (r - 2) := by simp [hS]
      _ ≤ ∑ e ∈ S, (e.1 \ e₀.1).ncard * ((e.1 \ e₀.1).ncard - 1) := by
        apply Finset.sum_le_sum
        intro e he
        have h := hout e he
        exact Nat.mul_le_mul h (by omega)
      _ ≤ ∑ e : H, (e.1 \ e₀.1).ncard * ((e.1 \ e₀.1).ncard - 1) :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have htotal := H.sum_outside_pair_weight_le hlinear e₀.1
  rw [Set.ncard_compl, Nat.card_eq_fintype_card] at htotal
  exact hlower.trans htotal

/-- If one edge leaves too few pairs outside it to support `n` other
minimum-size edges, the whole family has at most `n` edges. -/
theorem card_le_of_large_edge (H : SetHypergraph X) (hlinear : H.IsLinear)
    (n r R : ℕ) (hvertices : Fintype.card X = n)
    (hmin : ∀ e : H, r ≤ e.1.ncard)
    (hbudget : (n - R) * (n - R - 1) < n * ((r - 1) * (r - 2)))
    (e₀ : H) (hlarge : R ≤ e₀.1.ncard) : Fintype.card H ≤ n := by
  have hcount := H.edge_count_mul_le_outside_pair_budget hlinear e₀ r hmin
  rw [hvertices] at hcount
  have hout : (n - e₀.1.ncard) * (n - e₀.1.ncard - 1) ≤
      (n - R) * (n - R - 1) :=
    Nat.mul_le_mul (Nat.sub_le_sub_left hlarge n)
      (Nat.sub_le_sub_right (Nat.sub_le_sub_left hlarge n) 1)
  by_contra hnot
  have hn : n ≤ Fintype.card H - 1 := by omega
  have := Nat.mul_le_mul_right ((r - 1) * (r - 2)) hn
  omega

end Erdos19.SetHypergraph

#print axioms Erdos19.SetHypergraph.card_le_of_large_edge
