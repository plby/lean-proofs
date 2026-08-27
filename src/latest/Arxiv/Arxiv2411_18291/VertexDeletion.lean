import Arxiv.Arxiv2411_18291.CoefficientRelabeling
import Mathlib.Data.Finset.Option
import Mathlib.Logic.Equiv.Option

/-!
# Links and deletion of a vertex for signed hypergraphs

Represent the distinguished vertex by `none`. Blocks through it are obtained
by adjoining `none`; blocks avoiding it are images under `some`. These two
operations provide the incidence identities for the induction in `rem:div`.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} {q r : ℕ}

/-- Adjoin one new vertex to a block. -/
def coneBlock (e : Block V r) : Block (Option V) (r + 1) :=
  ⟨insertNone e.val, by simp [e.property]⟩

theorem coneBlock_injective : Function.Injective (coneBlock (V := V) (r := r)) := by
  intro e f h
  exact Subtype.ext (insertNone.injective (congrArg Subtype.val h))

@[simp] theorem coneBlock_subset_coneBlock (e : Block V r) (Q : Block V q) :
    (coneBlock e).val ⊆ (coneBlock Q).val ↔ e.val ⊆ Q.val :=
  insertNone.le_iff_le

@[simp] theorem none_mem_coneBlock (e : Block V r) : none ∈ (coneBlock e).val := by
  simp [coneBlock]

@[simp] theorem none_notMem_someBlock (e : Block V r) :
    none ∉ (mapBlock Function.Embedding.some e).val := by
  simp [mapBlock]

theorem exists_coneBlock {e : Block (Option V) (r + 1)} (he : none ∈ e.val) :
    ∃ e' : Block V r, coneBlock e' = e := by
  classical
  refine ⟨⟨e.val.eraseNone, ?_⟩, ?_⟩
  · rw [card_eraseNone_of_mem he, e.property]
    omega
  · apply Subtype.ext
    exact (insertNone_eraseNone e.val).trans (insert_eq_of_mem he)

theorem exists_someBlock {e : Block (Option V) r} (he : none ∉ e.val) :
    ∃ e' : Block V r, mapBlock Function.Embedding.some e' = e := by
  classical
  refine ⟨⟨e.val.eraseNone, by rw [card_eraseNone_of_not_mem he, e.property]⟩, ?_⟩
  apply Subtype.ext
  exact (map_some_eraseNone e.val).trans (erase_eq_of_notMem he)

/-- Signed link at the new vertex. -/
def linkVector (J : Block (Option V) (r + 1) → ℤ) (e : Block V r) : ℤ :=
  J (coneBlock e)

/-- Restrict to the vertices other than the distinguished vertex. -/
def restrictVector (J : Block (Option V) r → ℤ) (e : Block V r) : ℤ :=
  J (mapBlock Function.Embedding.some e)

variable [Fintype V] [DecidableEq V]

/-- Degrees in the link are degrees at sets containing the distinguished vertex. -/
theorem degree_linkVector (J : Block (Option V) (r + 1) → ℤ) (I : Finset V) :
    degree (linkVector J) I = degree J (insertNone I) := by
  apply Fintype.sum_of_injective coneBlock coneBlock_injective
  · intro e he
    have hnone : none ∉ e.val := by
      intro h
      exact he (exists_coneBlock h)
    have hsub : ¬insertNone I ⊆ e.val := fun h => hnone (h (by simp))
    exact if_neg hsub
  · intro e
    simp only [linkVector, coneBlock, insertNone.le_iff_le]

/-- If the link is zero, restriction preserves every remaining degree. -/
theorem degree_restrictVector (J : Block (Option V) r → ℤ)
    (hzero : ∀ e, none ∈ e.val → J e = 0) (I : Finset V) :
    degree (restrictVector J) I = degree J (I.map Function.Embedding.some) := by
  apply Fintype.sum_of_injective (mapBlock Function.Embedding.some)
    (mapBlock_injective Function.Embedding.some)
  · intro e he
    have hnone : none ∈ e.val := by
      by_contra h
      exact he (exists_someBlock h)
    simp only [hzero e hnone, ite_self]
  · intro e
    simp only [restrictVector, mapBlock, map_subset_map]

theorem DegreeDivisible.link {J : Block (Option V) (r + 1) → ℤ}
    (hJ : DegreeDivisible (q + 1) J) : DegreeDivisible q (linkVector J) := by
  intro I hI
  rw [degree_linkVector]
  simpa only [card_insertNone, Nat.add_sub_add_right] using
    hJ (insertNone I) (by simpa using Nat.add_le_add_right hI 1)

theorem DegreeDivisible.restrict {J : Block (Option V) r → ℤ}
    (hJ : DegreeDivisible q J) (hzero : ∀ e, none ∈ e.val → J e = 0) :
    DegreeDivisible q (restrictVector J) := by
  intro I hI
  rw [degree_restrictVector J hzero]
  simpa only [card_map] using
    hJ (I.map Function.Embedding.some) (by simpa using hI)

/-- Extending every clique by the new vertex realizes a prescribed link. -/
theorem boundary_coneVector (Φ : Block V q → ℤ) (e : Block V r) :
    boundary (r + 1) (liftVector coneBlock Φ) (coneBlock e) = boundary r Φ e := by
  rw [boundary_liftVector]
  simp only [coneBlock_subset_coneBlock, boundary]

/-- Extending the coefficient vector by zero preserves incidences on old edges. -/
theorem boundary_extendVector (Φ : Block V q → ℤ) (e : Block V r) :
    boundary r (liftVector (mapBlock Function.Embedding.some) Φ)
      (mapBlock Function.Embedding.some e) = boundary r Φ e := by
  rw [boundary_liftVector]
  simp only [mapBlock_subset_mapBlock, boundary]

/-- No old clique contains an edge through the new vertex. -/
theorem boundary_extendVector_of_none (Φ : Block V q → ℤ)
    (e : Block (Option V) r) (he : none ∈ e.val) :
    boundary r (liftVector (mapBlock Function.Embedding.some) Φ) e = 0 := by
  rw [boundary_liftVector]
  apply sum_eq_zero
  intro Q _
  exact if_neg (fun h => none_notMem_someBlock Q (h he))

end Arxiv2411_18291
