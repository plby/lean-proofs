import ErdosProblems.Erdos19.SmallSupportRound
import ErdosProblems.Erdos19.RoundRobinEmbedding
import ErdosProblems.Erdos19.PackingSequence

/-! # Packing with an independent set of parity defects -/

namespace Erdos19

open _root_.SimpleGraph

theorem exists_matching_packing_with_auxiliary_clique {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) (B : Set V) (t : ℕ)
    (C : Fin (2 * t + 1) → Set V) (hCB : ∀ i, C i ⊆ B)
    (hcomplete : ∀ x y, x ≠ y → y ∉ B → G.Adj x y)
    (hsize : 2 * B.ncard + 3 * (2 * t + 1) + 1 ≤ Fintype.card V) :
    ∃ f : Fin (2 * t + 1) ↪ V, (∀ i, f i ∉ B) ∧
      ∃ M : Fin (2 * t + 1) → G.Subgraph,
        (∀ i, (M i).IsMatching ∧ (M i).verts = auxiliaryTarget (C i) (f i)) ∧
        Pairwise (fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe) ∧
        (∀ x ∈ Set.range f, ∀ y ∈ Set.range f, x ≠ y → (⨆ i, (M i).spanningCoe).Adj x y) := by
  classical
  let q := 2 * t + 1
  have hBcompl : q ≤ Bᶜ.ncard := by
    have hcard := Set.ncard_add_ncard_compl B
    rw [Nat.card_eq_fintype_card] at hcard
    dsimp only [q]
    omega
  have hcards : Fintype.card (Fin q) ≤ Fintype.card ↥(Bᶜ) := by
    simpa only [Fintype.card_fin, Set.fintypeCard_eq_ncard] using hBcompl
  obtain ⟨f₀ : Fin q ↪ ↥(Bᶜ)⟩ := Function.Embedding.nonempty_of_card_le hcards
  let f : Fin q ↪ V := f₀.trans (Function.Embedding.subtype _)
  have hfB : ∀ i, f i ∉ B := fun i ↦ (f₀ i).2
  let S := Set.range f
  have hBS : Disjoint B S := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨i, rfl⟩
    exact hfB i hx
  have hScard : S.ncard = q := by
    rw [Set.ncard_range_of_injective f.injective]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨P, hP, hPdis, hPcover⟩ := exists_roundRobin_family G t f (fun i j hij ↦
    hcomplete (f i) (f j) (fun h ↦ hij (f.injective h)) (hfB j))
  let A : ℕ → Set V := fun i ↦ if hi : i < q then auxiliaryTarget (C ⟨i, hi⟩) (f ⟨i, hi⟩) else ∅
  have hA : ∀ i : Fin q, A i = auxiliaryTarget (C i) (f i) := fun i ↦ dif_pos i.isLt
  have aux : ∀ i ≤ q, ∃ U : _root_.SimpleGraph V,
      IsMatchingPacking G A i U ∧
      (∀ j : Fin q, j.1 < i → (P j).spanningCoe ≤ U) ∧
      (∀ j : Fin q, i ≤ j.1 → Disjoint U (P j).spanningCoe) := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨⊥, IsMatchingPacking.nil, (by intro j hj; omega), (by intro j _; simp)⟩
    | succ i ih =>
      intro hi
      have hiq : i < q := by omega
      let j : Fin q := ⟨i, hiq⟩
      obtain ⟨U, hpack, hpast, hfuture⟩ := ih (by omega)
      have hdegree : ∀ v, (U.neighborSet v).ncard ≤ i := by
        intro v
        have h := hpack.degree_add_absences v
        omega
      have hroom : 2 * B.ncard + S.ncard + 2 * (i + 1) + 1 ≤ Fintype.card V := by
        rw [hScard]
        dsimp only [q] at hiq ⊢
        omega
      obtain ⟨N, hN, hNA, hPN, hUN, hextra⟩ := exists_small_support_matching_round G U B S
        (C j) (f j) hBS ⟨j, rfl⟩ (hCB j) hcomplete (P j) (hP j).1 (hP j).2
        (hfuture j le_rfl) i hdegree hroom
      have hNA' : N.verts = A i := hNA.trans (hA j).symm
      refine ⟨U ⊔ N.spanningCoe, hpack.snoc N hN hNA' hUN, ?_, ?_⟩
      · intro k hk
        by_cases hki : k.1 < i
        · exact (hpast k hki).trans le_sup_left
        · have hkj : k = j := Fin.ext (by dsimp only [j]; omega)
          rw [hkj]
          exact (Subgraph.spanningCoe_le_of_le hPN).trans le_sup_right
      · intro k hk
        apply disjoint_sup_left.mpr
        refine ⟨hfuture k (by omega), ?_⟩
        apply _root_.SimpleGraph.disjoint_left.mpr
        intro x y hNxy hPxy
        have hxS : x ∈ S := by
          have hx := (show (P k).Adj x y from hPxy).fst_mem
          rw [(hP k).2] at hx
          exact hx.1
        have hyS : y ∈ S := by
          have hy := (show (P k).Adj x y from hPxy).snd_mem
          rw [(hP k).2] at hy
          exact hy.1
        rcases hextra x y hNxy with hPj | hxW | hyW
        · have hjk : j ≠ k := by
            intro h
            have hval := congrArg Fin.val h
            dsimp only [j] at hval
            omega
          exact _root_.SimpleGraph.disjoint_left.mp (hPdis hjk) x y hPj hPxy
        · exact hxW (Or.inr hxS)
        · exact hyW (Or.inr hyS)
  obtain ⟨U, hpack, hpast, _⟩ := aux q le_rfl
  obtain ⟨M, hM, hdis, hunion⟩ := hpack.exists_family_exact
  refine ⟨f, hfB, M, fun i ↦ ⟨(hM i).1, (hM i).2.1.trans (hA i)⟩, hdis, ?_⟩
  intro x hx y hy hxy
  obtain ⟨i, hi⟩ := hPcover x hx y hy hxy
  rw [hunion]
  exact hpast i i.isLt hi

theorem exists_small_support_matching_packing {V : Type*} [Fintype V]
    (G : _root_.SimpleGraph V) (B : Set V)
    (C : Fin (2 * B.ncard + 1) → Set V) (hCB : ∀ i, C i ⊆ B)
    (hcomplete : ∀ x y, x ≠ y → y ∉ B → G.Adj x y)
    (hsize : 8 * B.ncard + 4 ≤ Fintype.card V) :
    ∃ f : Fin (2 * B.ncard + 1) ↪ V, (∀ i, f i ∉ B) ∧
      ∃ M : Fin (2 * B.ncard + 1) → G.Subgraph,
        (∀ i, (M i).IsMatching ∧ (M i).verts = auxiliaryTarget (C i) (f i)) ∧
        Pairwise (fun i j ↦ Disjoint (M i).spanningCoe (M j).spanningCoe) ∧
        (∀ x ∈ Set.range f, ∀ y ∈ Set.range f, x ≠ y → (⨆ i, (M i).spanningCoe).Adj x y) := by
  exact exists_matching_packing_with_auxiliary_clique G B B.ncard C hCB hcomplete (by omega)

#print axioms exists_matching_packing_with_auxiliary_clique
#print axioms exists_small_support_matching_packing

end Erdos19
