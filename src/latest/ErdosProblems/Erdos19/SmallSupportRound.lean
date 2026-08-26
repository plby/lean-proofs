import ErdosProblems.Erdos19.ProtectedMatchingExtension
import ErdosProblems.Erdos19.AuxiliaryTargets

/-! # One small-support packing round with an auxiliary matching -/

namespace Erdos19

open _root_.SimpleGraph

variable {V : Type*} [Fintype V]

theorem exists_small_support_matching_round
    (G U : _root_.SimpleGraph V) (B S C : Set V) (z : V)
    (hBS : Disjoint B S) (hzS : z ∈ S) (hCB : C ⊆ B)
    (hcomplete : ∀ x y, x ≠ y → y ∉ B → G.Adj x y)
    (P : G.Subgraph) (hP : P.IsMatching) (hPv : P.verts = S \ {z})
    (hdis : Disjoint U P.spanningCoe) (d : ℕ)
    (hdegree : ∀ v, (U.neighborSet v).ncard ≤ d)
    (hroom : 2 * B.ncard + S.ncard + 2 * (d + 1) + 1 ≤ Fintype.card V) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.verts = auxiliaryTarget C z ∧ P ≤ M ∧
      Disjoint U M.spanningCoe ∧
      ∀ x y, M.Adj x y → P.Adj x y ∨ x ∈ (B ∪ S)ᶜ ∨ y ∈ (B ∪ S)ᶜ := by
  classical
  let R := G \ U
  let W := (B ∪ S)ᶜ
  let A := auxiliaryTarget C z
  have hzC : z ∉ C := fun h ↦ Set.disjoint_left.mp hBS (hCB h) hzS
  let P₀ : R.Subgraph :=
    { verts := P.verts
      Adj := P.Adj
      adj_sub := fun {x y} h ↦ ⟨h.adj_sub,
        fun hU ↦ _root_.SimpleGraph.disjoint_left.mp hdis x y hU h⟩
      edge_vert := P.edge_vert
      symm := P.symm }
  have hP₀ : P₀.IsMatching := hP
  have hP₀A : P₀.verts ⊆ A := by
    intro x hx
    rw [show P₀.verts = S \ {z} from hPv] at hx
    exact subset_auxiliaryTarget C z ⟨fun h ↦ Set.disjoint_left.mp hBS (hCB h) hx.1, hx.2⟩
  have hWA : W ⊆ A := by
    intro x hx
    apply subset_auxiliaryTarget C z
    refine ⟨fun h ↦ hx (Or.inl (hCB h)), ?_⟩
    intro hxz
    exact hx (Or.inr (hxz ▸ hzS))
  have hWP : Disjoint W P₀.verts := by
    apply Set.disjoint_left.mpr
    intro x hxW hxP
    rw [show P₀.verts = S \ {z} from hPv] at hxP
    exact hxW (Or.inr hxP.1)
  have hboundary : A \ (P₀.verts ∪ W) ⊆ B ∪ {z} := by
    intro x hx
    by_cases hxB : x ∈ B
    · exact Or.inl hxB
    · have hxW : x ∉ W := fun h ↦ hx.2 (Or.inr h)
      have hxS : x ∈ S := by
        by_contra hxS
        exact hxW (fun h ↦ h.elim hxB hxS)
      right
      by_contra hxz
      have hxP : x ∈ P₀.verts := by rw [show P₀.verts = S \ {z} from hPv]; exact ⟨hxS, hxz⟩
      exact hx.2 (Or.inl hxP)
  have hboundcard : (A \ (P₀.verts ∪ W)).ncard ≤ B.ncard + 1 :=
    (Set.ncard_le_ncard hboundary).trans (by
      simpa only [Set.ncard_singleton] using (Set.ncard_union_le B {z}))
  have hWcard : B.ncard + S.ncard + W.ncard = Fintype.card V := by
    have h := Set.ncard_add_ncard_compl (B ∪ S)
    rw [Set.ncard_union_eq hBS] at h
    simpa only [Nat.card_eq_fintype_card] using h
  have hroom' : 2 * (d + 1) + (A \ (P₀.verts ∪ W)).ncard ≤ W.ncard := by omega
  have hmissing : ∀ x ∈ A \ P₀.verts, (W \ R.neighborSet x).ncard ≤ d + 1 := by
    intro x _
    have hsub : W \ R.neighborSet x ⊆ {x} ∪ U.neighborSet x := by
      intro y hy
      by_cases hyx : y = x
      · exact Or.inl hyx
      · by_cases hU : U.Adj x y
        · exact Or.inr hU
        · have hG : G.Adj x y := hcomplete x y (fun h ↦ hyx h.symm)
            (fun hyB ↦ hy.1 (Or.inl hyB))
          exact (hy.2 ⟨hG, hU⟩).elim
    have h := (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le {x} (U.neighborSet x))
    rw [Set.ncard_singleton] at h
    have hd := hdegree x
    omega
  obtain ⟨M₀, hM₀, hMA, hPM, hextra⟩ := exists_matching_extension_with_buffer R P₀ hP₀ A W
    (auxiliaryTarget_even C z hzC) hP₀A hWA hWP (d + 1) hroom' hmissing
  let M := liftSubgraph (show R ≤ G from fun _ _ h ↦ h.1) M₀
  refine ⟨M, hM₀, hMA, hPM, ?_, hextra⟩
  apply _root_.SimpleGraph.disjoint_left.mpr
  intro x y hU hM
  exact (show R.Adj x y from (show M₀.Adj x y from hM).adj_sub).2 hU

#print axioms exists_small_support_matching_round

end Erdos19
