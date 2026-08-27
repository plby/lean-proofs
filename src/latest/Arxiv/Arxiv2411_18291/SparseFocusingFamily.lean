import Arxiv.Arxiv2411_18291.SparseCliqueCover
import Arxiv.Arxiv2411_18291.Focusing
import Arxiv.Arxiv2411_18291.CliqueFamilyBoundedness

/-!
# One sparse family focusing every vector on the input graph

Only input edges outside the target graph require focusing cliques. A sparse
cover of those edges gives a single bounded family that works for every
signed input vector, while preserving integral decomposability.
-/

open Finset Filter

noncomputable section

namespace Arxiv2411_18291

theorem exists_focusing_family_of_clique_cover_with_cap {q r n : ℕ}
    (B E : Hypergraph (Fin n) (r + 1)) {θ : ℝ}
    (Q : ↥(B \ E) → Block (Fin n) q) (hQ : IsCliqueCover E (fun e => e.val) Q)
    (hbnd : IsGraphBounded (cliqueCoverGraph (r := r) Q) θ) :
    ∃ F : Finset (Block (Fin n) q), IsCliqueFamilyBounded r F θ ∧
      (∀ e : Block (Fin n) (r + 1), (F.filter fun Q => e.val ⊆ Q.val).card ≤ 1) ∧
      ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
        IntegrallyDecomposable q J →
        ∃ K : Block (Fin n) (r + 1) → ℤ, GeneratedBy F (J - K) ∧
          (∀ e, e ∉ E → K e = 0) ∧ IntegrallyDecomposable q K := by
  let F := univ.image Q
  have hmem (e : ↥(B \ E)) : Q e ∈ F := mem_image.mpr ⟨e, mem_univ _, rfl⟩
  have hroot (e : ↥(B \ E)) : e.val ∈ cliqueEdges (r + 1) (Q e) :=
    (mem_cliqueEdges _ _).mpr (hQ.punctured e).1
  have hrest (e : ↥(B \ E)) : (cliqueEdges (r + 1) (Q e)).erase e.val ⊆ E :=
    ((isPuncturedClique_iff _ _ _).mp (hQ.punctured e)).2
  have hcap (e : Block (Fin n) (r + 1)) :
      (F.filter fun Q => e.val ⊆ Q.val).card ≤ 1 := by
    change ((univ.image Q).filter fun P => e.val ⊆ P.val).card ≤ 1
    rw [(isDecomposition_iff _ _).mp hQ.decomposition e]
    split_ifs <;> omega
  refine ⟨F, ?_, hcap, fun J hJ hInt => ?_⟩
  · intro T
    change ((degree (boundary (r + 1) (indicator (univ.image Q))) T.val : ℤ) : ℝ) < _
    rw [hQ.decomposition, degree_indicator]
    exact hbnd T
  · apply exists_focused_integral_vector (B \ E) E F Q hmem hroot hrest J _ hInt
    intro e he heE
    exact hJ e (fun heB => he (mem_sdiff.mpr ⟨heB, heE⟩))

theorem exists_focusing_family_of_clique_cover {q r n : ℕ}
    (B E : Hypergraph (Fin n) (r + 1)) {θ : ℝ}
    (Q : ↥(B \ E) → Block (Fin n) q) (hQ : IsCliqueCover E (fun e => e.val) Q)
    (hbnd : IsGraphBounded (cliqueCoverGraph (r := r) Q) θ) :
    ∃ F : Finset (Block (Fin n) q), IsCliqueFamilyBounded r F θ ∧
      ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
        IntegrallyDecomposable q J →
        ∃ K : Block (Fin n) (r + 1) → ℤ, GeneratedBy F (J - K) ∧
          (∀ e, e ∉ E → K e = 0) ∧ IntegrallyDecomposable q K := by
  obtain ⟨F, hF, _, hfocus⟩ := exists_focusing_family_of_clique_cover_with_cap B E Q hQ hbnd
  exact ⟨F, hF, hfocus⟩

theorem eventually_exists_sparse_focusing_family (q r : ℕ) (hq : r + 1 ≤ q)
    {a b : ℝ} (ha : 0 ≤ a) (hba : 2 * a < b) (hb1 : b - a < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ B E : Hypergraph (Fin n) (r + 1),
      IsGraphBounded B ((n : ℝ) ^ (-b)) →
      (∀ e ∈ B \ E, (n : ℝ) ^ (-a) * (n : ℝ) ^ (q - (r + 1)) ≤
        (puncturedCliques E e q).card) →
      ∃ F : Finset (Block (Fin n) q),
        IsCliqueFamilyBounded r F ((n : ℝ) ^ (-b) + q.choose (r + 1) *
          (4 * (r + 1).factorial * (n : ℝ) ^ (-(b - a)))) ∧
        ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
          IntegrallyDecomposable q J →
          ∃ K : Block (Fin n) (r + 1) → ℤ, GeneratedBy F (J - K) ∧
            (∀ e, e ∉ E → K e = 0) ∧ IntegrallyDecomposable q K := by
  filter_upwards [eventually_exists_sparse_clique_cover hq ha hba hb1] with n hn
  intro B E hB hcount
  have hd : Disjoint (B \ E) E :=
    disjoint_left.mpr (fun _ he hE => (mem_sdiff.mp he).2 hE)
  obtain ⟨Q, hQ, hbnd⟩ := hn E (B \ E) hd (hB.subgraph sdiff_subset) hcount
  exact exists_focusing_family_of_clique_cover B E Q hQ hbnd

end Arxiv2411_18291
