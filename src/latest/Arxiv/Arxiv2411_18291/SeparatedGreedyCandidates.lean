import Arxiv.Arxiv2411_18291.VertexAvoidingExtensions
import Arxiv.Arxiv2411_18291.PrescribedGreedyExistence

/-!
# History-dependent candidates with separated free vertices

At each step, forbid the free vertices of earlier related embeddings.
If at most `d` earlier steps are related, the forbidden set has at most
`d*w` vertices. The candidate count holds on every history, including
stopped histories. A resulting trajectory therefore gives the intended
separation between every related pair of successful placements.
-/

open Finset Preorder
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r t : ℕ}

def stateFreeVertices (F : Finset W) (a : EmbeddingState W V) : Finset V :=
  match a with
  | none => ∅
  | some f => (univ \ F).map f

omit [Fintype V] [DecidableEq V] in
@[simp] theorem stateFreeVertices_chosen (F : Finset W) (f : W ↪ V) :
    stateFreeVertices F (chosenEmbedding f) = (univ \ F).map f := rfl

omit [Fintype V] [DecidableEq V] in
theorem stateFreeVertices_card_le (F : Finset W) (a : EmbeddingState W V) :
    (stateFreeVertices F a).card ≤ Fintype.card W := by
  cases a with
  | none => exact Nat.zero_le _
  | some f =>
    change ((univ \ F).map f).card ≤ _
    rw [card_map]
    exact (card_le_card sdiff_subset).trans_eq card_univ

open Classical in
def priorRelated (Rel : ℕ → ℕ → Prop) (n : ℕ) : Finset ℕ :=
  (range n).filter fun j => Rel j n

@[simp] theorem mem_priorRelated (Rel : ℕ → ℕ → Prop) (n j : ℕ) :
    j ∈ priorRelated Rel n ↔ j < n ∧ Rel j n := by
  classical
  simp only [priorRelated, mem_filter, mem_range]

def historyAvoidVertices (F : Finset W) (Rel : ℕ → ℕ → Prop) {n : ℕ}
    (h : FiniteHistoryProcess.History (EmbeddingState W V) n) : Finset V :=
  (priorRelated Rel n).biUnion fun j => stateFreeVertices F (historyAt h j)

omit [Fintype V] in
theorem historyAvoidVertices_card_le (F : Finset W) (Rel : ℕ → ℕ → Prop) {n d : ℕ}
    (h : FiniteHistoryProcess.History (EmbeddingState W V) n)
    (hrel : (priorRelated Rel n).card ≤ d) :
    (historyAvoidVertices F Rel h).card ≤ d * Fintype.card W := by
  calc
    _ ≤ ∑ j ∈ priorRelated Rel n, (stateFreeVertices F (historyAt h j)).card := card_biUnion_le
    _ ≤ ∑ _j ∈ priorRelated Rel n, Fintype.card W :=
      sum_le_sum fun _ _ => stateFreeVertices_card_le F _
    _ = (priorRelated Rel n).card * Fintype.card W := by simp only [sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hrel

def separatedCandidates (Φ : ℕ → F ↪ V) (Rel : ℕ → ℕ → Prop) : CandidateFamilies Φ :=
  fun i h => vertexAvoidingExtensions (Φ i) (historyAvoidVertices F Rel h)

theorem separatedCandidates_lower_bound (Φ : ℕ → F ↪ V) (Rel : ℕ → ℕ → Prop)
    (H : Hypergraph W (r + 1)) (L : ℝ) {d t : ℕ}
    (hrel : ∀ i < t, (priorRelated Rel i).card ≤ d)
    (hn : 4 * Fintype.card W ^ 2 ≤ Fintype.card V)
    (hsize : 4 * Fintype.card W * (d * Fintype.card W) ≤ Fintype.card V) :
    HasCandidateLowerBound Φ (separatedCandidates Φ Rel) H L (1 / 2) t := by
  intro i hi h _ _
  apply vertexAvoidingExtensions_card_half (Φ i) _ hn
  exact (Nat.mul_le_mul_left (4 * Fintype.card W)
    (historyAvoidVertices_card_le F Rel h (hrel i hi))).trans hsize

theorem separatedCandidates_disjoint (Φ : ℕ → F ↪ V) (Rel : ℕ → ℕ → Prop)
    (ω : ℕ → EmbeddingState W V) (Ψ : (i : Fin t) → EmbeddingExtension (Φ i))
    (hmem : ∀ i : Fin t, Ψ i ∈ separatedCandidates Φ Rel i (frestrictLe (i : ℕ) ω))
    (hmatch : ∀ i : Fin t, ω (i + 1) = chosenEmbedding (Ψ i).val)
    (i j : Fin t) (hij : i < j) (hrel : Rel i j) :
    Disjoint ((univ \ F).map (Ψ i).val) ((univ \ F).map (Ψ j).val) := by
  classical
  have havoid := (mem_vertexAvoidingExtensions (Φ j)
    (historyAvoidVertices F Rel (frestrictLe (j : ℕ) ω)) (Ψ j)).mp (hmem j)
  have hsub : (univ \ F).map (Ψ i).val ⊆
      historyAvoidVertices F Rel (frestrictLe (j : ℕ) ω) := by
    intro v hv
    apply mem_biUnion.mpr
    refine ⟨i, (mem_priorRelated Rel j i).mpr ⟨hij, hrel⟩, ?_⟩
    rw [historyAt_prefix ω j i hij, hmatch i, stateFreeVertices_chosen]
    exact hv
  exact (Disjoint.mono_right hsub havoid).symm

end Arxiv2411_18291
