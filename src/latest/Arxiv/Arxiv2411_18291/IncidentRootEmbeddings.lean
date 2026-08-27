import Arxiv.Arxiv2411_18291.IntersectingGreedyStars
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Data.Finset.Prod

/-! # Roots indexed by stars of a complete graph -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable (A : Type*) [Fintype A] [DecidableEq A]

def greedyNeighborEquiv (i : Option A) : A ≃ {j : Option A // j ≠ i} :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_option]
    omega)

def greedyIncidentEmbedding (i : Option A) : A ↪ Block (Option A) 2 where
  toFun x := ⟨{i, (greedyNeighborEquiv A i x).val}, by
    rw [card_pair (greedyNeighborEquiv A i x).property.symm]⟩
  inj' := by
    intro x y h
    have hval := congrArg Subtype.val h
    change ({i, (greedyNeighborEquiv A i x).val} : Finset (Option A)) =
      {i, (greedyNeighborEquiv A i y).val} at hval
    have hx : (greedyNeighborEquiv A i x).val ∈
        ({i, (greedyNeighborEquiv A i y).val} : Finset (Option A)) := by
      rw [← hval]
      exact mem_insert_of_mem (mem_singleton_self _)
    rcases mem_insert.mp hx with hi | hxy
    · exact ((greedyNeighborEquiv A i x).property hi).elim
    · exact (greedyNeighborEquiv A i).injective (Subtype.ext (mem_singleton.mp hxy))

theorem greedyIncidentEmbedding_base_mem (i : Option A) (x : A) :
    i ∈ (greedyIncidentEmbedding A i x).val := mem_insert_self _ _

theorem greedyIncidentEmbedding_hits (i j : Option A) (hij : i ≠ j) :
    ∃ x : A, (greedyIncidentEmbedding A i x).val = {i, j} := by
  refine ⟨(greedyNeighborEquiv A i).symm ⟨j, hij.symm⟩, ?_⟩
  change ({i, (greedyNeighborEquiv A i
    ((greedyNeighborEquiv A i).symm ⟨j, hij.symm⟩)).val} : Finset (Option A)) = _
  rw [Equiv.apply_symm_apply]

variable [AddGroup A]

def greedyRotatedRoot (i : Option A) (s : A) : greedyStarRoots A ↪ Block (Option A) 2 :=
  (greedyStarRootEquiv A).symm.toEmbedding.trans
    ((Equiv.addRight s).toEmbedding.trans (greedyIncidentEmbedding A i))

theorem greedyRotatedRoot_apply (i : Option A) (s x : A) :
    greedyRotatedRoot A i s (greedyStarRootEquiv A x) =
      greedyIncidentEmbedding A i (x + s) := by
  simp only [greedyRotatedRoot, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
    Equiv.symm_apply_apply]
  rfl

theorem greedyRotatedRoots_intersect (i j : Option A) (s t : A) :
    (usedVertices (greedyRotatedRoot A i s) ∩
      usedVertices (greedyRotatedRoot A j t)).Nonempty := by
  by_cases hij : i = j
  · subst j
    refine ⟨greedyIncidentEmbedding A i 0, mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact (mem_usedVertices _ _).mpr ⟨greedyStarRootEquiv A (-s), by
        rw [greedyRotatedRoot_apply, neg_add_cancel]⟩
    · exact (mem_usedVertices _ _).mpr ⟨greedyStarRootEquiv A (-t), by
        rw [greedyRotatedRoot_apply, neg_add_cancel]⟩
  · obtain ⟨x, hx⟩ := greedyIncidentEmbedding_hits A i j hij
    obtain ⟨y, hy⟩ := greedyIncidentEmbedding_hits A j i (Ne.symm hij)
    have heq : greedyIncidentEmbedding A j y = greedyIncidentEmbedding A i x := by
      apply Subtype.ext
      rw [hx, hy, pair_comm]
    refine ⟨greedyIncidentEmbedding A i x, mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact (mem_usedVertices _ _).mpr ⟨greedyStarRootEquiv A (x - s), by
        rw [greedyRotatedRoot_apply, sub_add_cancel]⟩
    · exact (mem_usedVertices _ _).mpr ⟨greedyStarRootEquiv A (y - t), by
        rw [greedyRotatedRoot_apply, sub_add_cancel, heq]⟩

theorem greedyRotatedRoot_fiber_card_le (L : ℕ) (x : greedyStarRoots A)
    (P : Block (Option A) 2) :
    (univ.filter fun z : Option A × A × Fin L => greedyRotatedRoot A z.1 z.2.1 x = P).card ≤
      2 * L := by
  classical
  have hle :
      (univ.filter fun z : Option A × A × Fin L => greedyRotatedRoot A z.1 z.2.1 x = P).card ≤
        (Finset.product P.val (univ : Finset (Fin L))).card := by
    apply card_le_card_of_injOn (fun z : Option A × A × Fin L => (z.1, z.2.2))
    · intro z hz
      have heq := (mem_filter.mp hz).2
      have hm := greedyIncidentEmbedding_base_mem A z.1
        ((greedyStarRootEquiv A).symm x + z.2.1)
      change z.1 ∈ (greedyRotatedRoot A z.1 z.2.1 x).val at hm
      rw [heq] at hm
      exact mem_product.mpr ⟨hm, mem_univ _⟩
    · rintro ⟨i, s, k⟩ hi ⟨j, t, l⟩ hj heq
      obtain ⟨hij, hkl⟩ := Prod.mk.inj heq
      change i = j at hij
      change k = l at hkl
      subst j
      subst l
      have h := (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm
      change greedyIncidentEmbedding A i ((greedyStarRootEquiv A).symm x + s) =
        greedyIncidentEmbedding A i ((greedyStarRootEquiv A).symm x + t) at h
      have hst := add_left_cancel ((greedyIncidentEmbedding A i).injective h)
      subst t
      rfl
  rw [product_eq_sprod, Finset.card_product, P.property, card_univ, Fintype.card_fin] at hle
  exact hle

end Arxiv2411_18291
