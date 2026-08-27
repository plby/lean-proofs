import Arxiv.Arxiv2411_18291.Divisibility
import Arxiv.Arxiv2411_18291.Relabeling

/-! # Transport of signed incidence vectors -/

open scoped BigOperators
open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V W : Type*} {q r p : ℕ}

/-- A vertex equivalence induces an equivalence on blocks. -/
def blockEquiv (f : V ≃ W) : Block V r ≃ Block W r where
  toFun := mapBlock f.toEmbedding
  invFun := mapBlock f.symm.toEmbedding
  left_inv s := by
    apply Subtype.ext
    ext x
    simp [mapBlock]
  right_inv s := by
    apply Subtype.ext
    ext x
    simp [mapBlock]

variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem degree_relabel (f : V ≃ W) (J : Block W r → ℤ) (I : Finset V) :
    degree (fun e => J (mapBlock f.toEmbedding e)) I =
      degree J (I.map f.toEmbedding) := by
  apply Fintype.sum_equiv (blockEquiv f)
  intro e
  simp only [blockEquiv, Equiv.coe_fn_mk, mapBlock, map_subset_map]

theorem boundary_relabel (f : V ≃ W) (Φ : Block W q → ℤ) (e : Block V r) :
    boundary r (fun Q => Φ (mapBlock f.toEmbedding Q)) e =
      boundary r Φ (mapBlock f.toEmbedding e) := by
  exact degree_relabel f Φ e.val

theorem DegreeDivisible.relabel (f : V ≃ W) {J : Block W r → ℤ}
    (hJ : DegreeDivisible q J) :
    DegreeDivisible q (fun e => J (mapBlock f.toEmbedding e)) := by
  intro I hI
  rw [degree_relabel]
  simpa only [card_map] using hJ (I.map f.toEmbedding) (by simpa using hI)

theorem IntegrallyDecomposable.relabel (f : V ≃ W) {J : Block W r → ℤ}
    (hJ : IntegrallyDecomposable q J) :
    IntegrallyDecomposable q (fun e => J (mapBlock f.toEmbedding e)) := by
  obtain ⟨Φ, hΦ⟩ := hJ
  refine ⟨fun Q => Φ (mapBlock f.toEmbedding Q), ?_⟩
  funext e
  rw [boundary_relabel, hΦ]

/-- Push coefficients forward, adding all coefficients in each fibre. The
source and target uniformities may differ, as in adjoining a new vertex. -/
def liftVector (f : Block V q → Block W p) (Φ : Block V q → ℤ)
    (Q : Block W p) : ℤ :=
  ∑ P, if f P = Q then Φ P else 0

omit [DecidableEq V] in
theorem degree_liftVector (f : Block V q → Block W p) (Φ : Block V q → ℤ)
    (I : Finset W) :
    degree (liftVector f Φ) I = ∑ Q, if I ⊆ (f Q).val then Φ Q else 0 := by
  unfold degree liftVector
  simp only [ite_sum_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro Q _
  have h : (fun P : Block W p =>
      if I ⊆ P.val then if f Q = P then Φ Q else 0 else 0) =
      (fun P => if f Q = P then (if I ⊆ (f Q).val then Φ Q else 0) else 0) := by
    funext P
    by_cases hP : f Q = P
    · subst P
      simp
    · simp [hP]
  rw [h]
  simp

omit [DecidableEq V] in
theorem boundary_liftVector (f : Block V q → Block W p) (Φ : Block V q → ℤ)
    (e : Block W r) :
    boundary r (liftVector f Φ) e = ∑ Q, if e.val ⊆ (f Q).val then Φ Q else 0 :=
  degree_liftVector f Φ e.val

theorem DegreeDivisible.sub {J K : Block V r → ℤ}
    (hJ : DegreeDivisible q J) (hK : DegreeDivisible q K) : DegreeDivisible q (J - K) := by
  intro I hI
  have h : degree (J - K) I = degree J I - degree K I := by
    unfold degree
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro e _
    split_ifs <;> simp
  rw [h]
  exact dvd_sub (hJ I hI) (hK I hI)

end Arxiv2411_18291
