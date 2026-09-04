import ErdosProblems.Erdos19.ActiveNearPerfectMatching
import ErdosProblems.Erdos19.ActiveReservoirCompletion
import ErdosProblems.Erdos19.SubgraphLift
import ErdosProblems.Erdos19.GraphLoadStep

/-! # One round of prescribed matching packing

The base matching avoids the reservoir. Its repair avoids a prescribed set of
vertices, so that the same round can be used with the load-balancing invariant.
-/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_matching_packing_round
    (G U R Q : _root_.SimpleGraph V) (hRG : R ≤ G)
    (hQ : Q ≤ G \ (R ⊔ U)) (A : Set V) (heven : Even A.ncard)
    (hsupport : Q.support ⊆ A) (B : Finset V) (d D u q : ℕ)
    (hmin : ∀ v ∈ A, d ≤ Q.degree v) (hmax : ∀ v, Q.degree v ≤ D)
    (hB : B.card ≤ d)
    (huncovered : A.ncard * (D + 1 - d) ≤ u * (D + 1))
    (hdegree : ∀ v ∈ A,
      2 * q + 2 * B.card + 7 * u + Aᶜ.ncard + 1 ≤ (R \ U).degree v)
    (hcut : ∀ X Y : Finset V, Disjoint X Y → X.card = q → Y.card = q →
      q < ((R \ U).between (X : Set V) (Y : Set V)).edgeFinset.card) :
    ∃ N : G.Subgraph, ∃ T : Finset V,
      N.IsMatching ∧ N.verts = A ∧ Disjoint U N.spanningCoe ∧
      T.card ≤ 3 * u ∧ Disjoint T B ∧
      (N.spanningCoe ⊓ R).support ⊆ (T : Set V) := by
  classical
  let Z := B.filter (· ∈ A)
  have hZcard : Z.card ≤ B.card := card_filter_le _ _
  have hZdegree : ∀ z ∈ (Z : Set V), (Z : Set V).ncard ≤ (Q.neighborSet z).ncard := by
    intro z hz
    have hzA := (mem_filter.mp hz).2
    have hd := (hZcard.trans hB).trans (hmin z hzA)
    simpa only [Set.ncard_coe_finset, ← card_neighborSet_eq_degree,
      Set.fintypeCard_eq_ncard] using hd
  obtain ⟨M, hM, hMA, hZM, hMbound⟩ :=
    exists_near_perfect_matching_on_set_covering Q A Z hsupport hZdegree d D hmin hmax
  have hu : (A \ M.verts).ncard ≤ u := by
    exact Nat.le_of_mul_le_mul_right (hMbound.trans huncovered) (by omega)
  let H := G \ U
  have hQH : Q ≤ H := fun _ _ h ↦ ⟨(hQ h).1, fun hU ↦ (hQ h).2 (Or.inr hU)⟩
  have hRH : R \ U ≤ H := fun _ _ h ↦ ⟨hRG h.1, h.2⟩
  let M₀ := liftSubgraph hQH M
  have hM₀ : M₀.IsMatching := hM
  have hM₀A : M₀.verts ⊆ A := hMA
  have hZM₀ : (Z : Set V) ⊆ M₀.verts := hZM
  have hd : ∀ v ∈ A,
      2 * q + 2 * Z.card + 7 * (A \ M₀.verts).ncard + Aᶜ.ncard + 1 ≤ (R \ U).degree v := by
    intro v hv
    have hdv := hdegree v hv
    change 2 * q + 2 * Z.card + 7 * (A \ M.verts).ncard + Aᶜ.ncard + 1 ≤ _
    omega
  let R₀ := R \ U
  let : DecidableRel R₀.Adj := fun x y ↦ Classical.propDecidable (R₀.Adj x y)
  have hd₀ : ∀ v ∈ A,
      2 * q + 2 * Z.card + 7 * (A \ M₀.verts).ncard + Aᶜ.ncard + 1 ≤ R₀.degree v := by
    intro v hv
    simpa only [← card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] using hd v hv
  have hc₀ : ∀ X Y : Finset V, Disjoint X Y → X.card = q → Y.card = q →
      q < (R₀.between (X : Set V) (Y : Set V)).edgeFinset.card := by
    intro X Y hXY hX hY
    simpa only [edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard] using hcut X Y hXY hX hY
  obtain ⟨N, T, hN, hNA, hTcard, hTZ, hnew⟩ :=
    exists_matching_on_set_using_reservoir H R₀ hRH A heven q hc₀ M₀ hM₀ hM₀A Z hZM₀ hd₀
  have hdis : Disjoint M₀.edgeSet R.edgeSet := by
    apply Set.disjoint_left.mpr
    intro e heM heR
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hadj : M.Adj x y := Subgraph.mem_edgeSet.mp heM
      have hR : R.Adj x y := by simpa only [mem_edgeSet] using heR
      exact (hQ hadj.adj_sub).2 (Or.inl hR)
  have hsupp : (N.spanningCoe ⊓ R).support ⊆ (T : Set V) :=
    reservoir_inter_support_subset R M₀ N T hdis (fun e he ↦ (hnew e he).2)
  let T₀ := T.filter (· ∈ A)
  have hT₀card : T₀.card ≤ 3 * u :=
    (card_filter_le _ _).trans (hTcard.trans (Nat.mul_le_mul_left 3 hu))
  have hT₀B : Disjoint T₀ B := by
    apply Finset.disjoint_left.mpr
    intro v hv hvB
    have hv' := mem_filter.mp hv
    exact Finset.disjoint_left.mp hTZ hv'.1 (mem_filter.mpr ⟨hvB, hv'.2⟩)
  have hsupp₀ : (N.spanningCoe ⊓ R).support ⊆ (T₀ : Set V) := by
    intro v hv
    have hvA : v ∈ A := by
      obtain ⟨w, hw⟩ := hv
      rw [← hNA]
      exact (show N.Adj v w from hw.1).fst_mem
    exact mem_filter.mpr ⟨hsupp hv, hvA⟩
  have hHG : H ≤ G := fun _ _ h ↦ h.1
  refine ⟨liftSubgraph hHG N, T₀, hN, hNA, ?_, hT₀card, hT₀B, hsupp₀⟩
  apply _root_.SimpleGraph.disjoint_left.mpr
  intro x y hU hNxy
  exact (show H.Adj x y from (show N.Adj x y from hNxy).adj_sub).2 hU

#print axioms exists_matching_packing_round

end Erdos19
