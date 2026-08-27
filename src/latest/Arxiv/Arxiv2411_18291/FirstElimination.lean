import Arxiv.Arxiv2411_18291.NearCancellationPairs
import Arxiv.Arxiv2411_18291.EliminationNegativeGeometry

/-!
# The first elimination stage and its further-elimination partners

Apply the simultaneous placement theorem to all opposite-sign near
pairs. Its negative cliques avoid the original graph. Every bad negative
clique has a unique positive far splitting partner through its old edge,
and the two cliques intersect in exactly that edge's vertices.
-/

open Finset Filter

noncomputable section

namespace Arxiv2411_18291

variable {W U V : Type*} [Fintype W] [Fintype U] [Fintype V]
variable [DecidableEq W] [DecidableEq U] [DecidableEq V] {q r C : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {θ θ' : ℝ}
variable {T : ExchangeSystem U q (r + 1)} {N : Block U q} {e₀ : Block U (r + 1)}

def SplittingFamily.graph (F : SplittingFamily S D B C θ) : Hypergraph V (r + 1) :=
  B ∪ univ.biUnion fun i => mapGraph (F.embedding i) (newEdges S.base.val S.graph)

omit [Fintype V] [DecidableEq V] in
theorem eventually_exists_first_elimination (S : ExchangeSystem W q (r + 1))
    {A₀ : Finset (Block W q)} (hA₀ : IsExchangeFamily S A₀)
    (T : ExchangeSystem U q (r + 1)) (N : Block U q) (e₀ : Block U (r + 1))
    (hpair : IsEliminationPair T N e₀) (hqr : r + 1 ≤ q) (C M : ℕ) {A ρ : ℝ}
    (hA : 1 ≤ A) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    let K : ℕ := 2 * C * M + 2
    ∀ᶠ n : ℕ in atTop, ∀ D : Finset (Block (Fin n) q),
      ∀ B : Hypergraph (Fin n) (r + 1),
      ∀ F : SplittingFamily S D B C (A * (n : ℝ) ^ (-ρ)),
      (∀ f : Block (Fin n) (r + 1), (D.filter fun Q => f.val ⊆ Q.val).card ≤ M) →
      Nonempty (EliminationFamily T N F.graph F.pairPositive F.pairNegative
        ((K : ℝ) * A * (n : ℝ) ^ (-ρ) + T.graph.card *
          (8 * (r + 1).factorial * (((q.choose (r + 1) * K : ℕ) : ℝ) *
            ((K : ℝ) * A) * (n : ℝ) ^ (-ρ))))) := by
  dsimp only
  let K : ℕ := 2 * C * M + 2
  have hK : 0 < K := by dsimp only [K]; omega
  have hKreal : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hAnonneg : 0 ≤ A := by linarith
  have hAK : A ≤ (K : ℝ) * A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hKreal hAnonneg
  have hKA : 1 ≤ (K : ℝ) * A := hA.trans hAK
  filter_upwards [eventually_exists_elimination_family T N e₀ hpair hqr K hK hKA hρ hρ1]
    with n hplace
  intro D B F hmult
  have hD' : IsCliqueFamilyBounded r F.cliques ((K : ℝ) * A * (n : ℝ) ^ (-ρ)) := by
    simpa only [K, mul_assoc] using F.cliques_bounded hmult
  have hB' : IsGraphBounded F.graph ((K : ℝ) * A * (n : ℝ) ^ (-ρ)) :=
    F.bounded.mono (mul_le_mul_of_nonneg_right hAK (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  exact hplace F.cliques F.graph hD' hB' F.cliques_support (F.clique_multiplicity hmult)
    F.NearPairs F.pairPositive F.pairNegative F.pairPositive_mem F.pairNegative_mem
    F.near_pair_injective (F.near_pair_inter hA₀)

theorem first_elimination_negative_avoids_original (F : SplittingFamily S D B C θ)
    {A₀ : Finset (Block W q)} (hA₀ : IsExchangeFamily S A₀)
    (E : EliminationFamily T N F.graph F.pairPositive F.pairNegative θ')
    (hpair : IsEliminationPair T N e₀) {R : Block V q} (hR : R ∈ E.negativeCliques) :
    Disjoint (cliqueEdges (r + 1) R) B :=
  E.negative_disjoint_previous hpair subset_union_left (F.near_pair_old_inter hA₀) hR

theorem first_good_negative_disjoint_splitting (F : SplittingFamily S D B C θ)
    (E : EliminationFamily T N F.graph F.pairPositive F.pairNegative θ')
    {R Q : Block V q} (hR : R ∈ E.goodNegative) (hQ : Q ∈ F.cliques) :
    Disjoint (cliqueEdges (r + 1) R) (cliqueEdges (r + 1) Q) := by
  apply Disjoint.mono_right _ (mem_filter.mp hR).2
  intro e he
  exact F.cliques_support (mem_biUnion.mpr ⟨Q, hQ, he⟩)

theorem first_bad_negative_partner (F : SplittingFamily S D B C θ)
    {A₀ : Finset (Block W q)} (hA₀ : IsExchangeFamily S A₀)
    (E : EliminationFamily T N F.graph F.pairPositive F.pairNegative θ')
    (hpair : IsEliminationPair T N e₀) {R : Block V q} (hR : R ∈ E.badNegative) :
    ∃ e : Block V (r + 1), ∃ Q ∈ F.positiveFar,
      cliqueEdges (r + 1) R ∩ F.graph = {e} ∧ e ∈ cliqueEdges (r + 1) Q ∧
      R.val ∩ Q.val = e.val ∧
      ∀ Q' ∈ F.positiveCliques, e ∈ cliqueEdges (r + 1) Q' → Q' = Q := by
  obtain ⟨e, heG, hRe⟩ := E.badNegative_inter_singleton hpair hR
  have heR : e ∈ cliqueEdges (r + 1) R :=
    (mem_inter.mp (hRe ▸ mem_singleton_self e)).1
  have heB : e ∉ B := fun h =>
    disjoint_left.mp (first_elimination_negative_avoids_original F hA₀ E hpair
      (mem_sdiff.mp hR).1) heR h
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp (mem_sdiff.mp hR).1
  obtain ⟨R₀, hR₀, hmap⟩ := (mem_mapGraph _ _ _).mp hi
  have heN : e ∈ cliqueEdges (r + 1) (F.pairNegative i) := by
    have heI := mem_inter.mpr ⟨heR, heG⟩
    rw [← hmap, E.negative_copy_inter_original hpair i hR₀] at heI
    exact (mem_inter.mp heI).2
  obtain ⟨Q, hQ, heQ, huniq⟩ := F.negativeNear_positiveFar_partner i.val.1.property heN heB
  have hQall : Q ∈ F.cliques := by
    rw [F.cliques_eq_signs]
    exact mem_union_left _ (mem_sdiff.mp hQ).1
  have hQG : cliqueEdges (r + 1) Q ⊆ F.graph := by
    intro f hf
    exact F.cliques_support (mem_biUnion.mpr ⟨Q, hQall, hf⟩)
  exact ⟨e, Q, hQ, hRe, heQ,
    vertices_inter_eq_of_graph_inter_singleton (Nat.succ_pos r) R Q F.graph e hRe hQG heQ,
    huniq⟩

end Arxiv2411_18291
