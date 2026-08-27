import Arxiv.Arxiv2411_18291.RootFiberBounds

/-! # Intersecting prescribed root sets with uniformly small edge degrees -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_intersecting_balanced_roots
    (A : Type*) [Fintype A] [AddGroup A] (L n t : ℕ) {θ : ℝ}
    (hcarrier : Fintype.card (Block (Option A) 2) ≤ n)
    (hindex : Fintype.card (Option A × A × Fin L) = t)
    (hdegree : (4 * L : ℝ) < θ * n) :
    ∃ Φ : Fin t → greedyStarRoots A ↪ Fin n,
      (∀ i j, (usedVertices (Φ i) ∩ usedVertices (Φ j)).Nonempty) ∧
      (∀ e : Block (greedyStarRoots A) 2,
        IsEdgeFamilyBounded (fun i => mapBlock (Φ i) e) θ) := by
  classical
  obtain ⟨g⟩ : Nonempty (Block (Option A) 2 ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa only [Fintype.card_fin] using hcarrier)
  let enum : Fin t ≃ Option A × A × Fin L :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, hindex])
  let Φ₀ : Option A × A × Fin L → greedyStarRoots A ↪ Block (Option A) 2 :=
    fun z => greedyRotatedRoot A z.1 z.2.1
  let Φ : Fin t → greedyStarRoots A ↪ Fin n := fun i => (Φ₀ (enum i)).trans g
  have hf (x : greedyStarRoots A) (v : Fin n) :
      (univ.filter fun i => Φ i x = v).card ≤ 2 * L :=
    embedding_fiber_card_le enum g Φ₀ (2 * L) (greedyRotatedRoot_fiber_card_le A L) x v
  refine ⟨Φ, ?_, ?_⟩
  · intro i j
    exact usedVertices_intersect_trans (Φ₀ (enum i)) (Φ₀ (enum j)) g
      (greedyRotatedRoots_intersect A _ _ _ _)
  · intro e S
    have h := mapBlock_familyDegree_le_of_fibers Φ e (2 * L) hf S
    have hr : (familyDegree (fun i => mapBlock (Φ i) e) S.val : ℝ) ≤ 4 * L := by
      have h' : (familyDegree (fun i => mapBlock (Φ i) e) S.val : ℝ) ≤
          2 * (2 * L) := by exact_mod_cast h
      nlinarith only [h']
    exact hr.trans_lt (by simpa only [Fintype.card_fin] using hdegree)

def finiteRootSequence {W V : Type*} {F : Finset W} {t : ℕ}
    (Φ : Fin t → F ↪ V) (φ : F ↪ V) (i : ℕ) : F ↪ V :=
  if hi : i < t then Φ ⟨i, hi⟩ else φ

theorem finiteRootSequence_apply {W V : Type*} {F : Finset W} {t : ℕ}
    (Φ : Fin t → F ↪ V) (φ : F ↪ V) (i : Fin t) : finiteRootSequence Φ φ i = Φ i := by
  simp only [finiteRootSequence, dif_pos i.isLt]

end Arxiv2411_18291
