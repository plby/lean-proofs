/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos73.Pregrill
import ErdosProblems.Erdos73.FiniteAveraging

/-!
# Selecting a full pregrill

The selected rows all meet the selected columns, whose original common
row order is retained. This is the averaging step before minor normalization.
-/

namespace Erdos73Infrastructure.SimpleGraph
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V : Type*} {G : _root_.SimpleGraph V}

/-- A full pregrill has disjoint rows and connected disjoint columns,
all row--column intersections nonempty, and common column order. -/
structure FullPregrill (G : _root_.SimpleGraph V) (m n : ℕ) where
  row : Fin m → GraphPath G
  row_disjoint : Pairwise fun r s ↦ Disjoint (row r).vertexSet (row s).vertexSet
  column : Fin n → Finset V
  connected : ∀ j, (G.induce (column j : Set V)).Connected
  column_disjoint : Pairwise fun i j ↦ Disjoint (column i) (column j)
  meets : ∀ r j, ((row r).vertexSet ∩ column j).Nonempty
  ordered : ∀ i j, i < j → ∀ r,
    ∀ x ∈ column i, x ∈ (row r).vertexSet →
    ∀ y ∈ column j, y ∈ (row r).vertexSet → (row r).Before x y

/-- Integral averaging retains any requested number of full columns
up to half the original number. No row or column is duplicated. -/
theorem Pregrill.exists_fullPregrill_with_columns
    {m n d : ℕ} (P : Pregrill G m n d) (M L : ℕ)
    (hMpos : 0 < M) (hM : M ≤ m) (hd : 2 * M * d ≤ m) (hL : 2 * L ≤ n) :
    ∃ F : FullPregrill G M L, ∃ c : Fin L ↪o Fin n,
      ∀ j, F.column j = P.column (c j) := by
  let miss (r : P.rows.Index) (j : Fin n) : Prop :=
    Disjoint (P.rows.path r).vertexSet (P.column j)
  have hcard : Fintype.card P.rows.Index = m := P.card_rows
  have hM' : M ≤ Fintype.card P.rows.Index := by rw [hcard]; exact hM
  have hmiss (j : Fin n) :
      2 * M * (Finset.univ.filter fun r ↦ miss r j).card ≤ Fintype.card P.rows.Index := by
    rw [hcard]
    exact (Nat.mul_le_mul_left _ (P.misses_le j)).trans hd
  obtain ⟨J, C, hJ, hC, hmeet⟩ := Erdos73.exists_rows_common_half_columns
    miss M hMpos hM' (by
      intro j
      convert hmiss j using 1
      apply congrArg (fun S : Finset P.rows.Index ↦ 2 * M * S.card)
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and])
  have hLC : L ≤ C.card := by
    have hn : n ≤ 2 * C.card := by simpa using hC
    omega
  let e : Fin M ≃ {r // r ∈ J} :=
    (Fintype.equivFinOfCardEq (show Fintype.card {r // r ∈ J} = M by simpa using hJ)).symm
  let c : Fin L ↪o Fin n := C.orderEmbOfCardLe hLC
  refine ⟨{
    row := fun r ↦ P.rows.path (e r).1
    row_disjoint := ?_
    column := fun j ↦ P.column (c j)
    connected := fun j ↦ P.connected (c j)
    column_disjoint := fun _ _ hij ↦ P.disjoint (c.injective.ne hij)
    meets := ?_
    ordered := ?_ }, c, fun _ => rfl⟩
  · intro r s hrs
    exact P.rows.node_disjoint (fun heq ↦ hrs (e.injective (Subtype.ext heq)))
  · intro r j
    have h := hmeet (e r).1 (e r).2 (c j) (C.orderEmbOfCardLe_mem hLC j)
    obtain ⟨v, hvrow, hvcol⟩ := Finset.not_disjoint_iff.mp h
    exact ⟨v, Finset.mem_inter.mpr ⟨hvrow, hvcol⟩⟩
  · intro i j hij r x hx hxP y hy hyP
    exact P.ordered (c i) (c j) (c.strictMono hij) (e r).1 x hx hxP y hy hyP

/-- Forget only the column labels after the stronger selection theorem. -/
theorem Pregrill.exists_fullPregrill
    {m n d : ℕ} (P : Pregrill G m n d) (M L : ℕ)
    (hMpos : 0 < M) (hM : M ≤ m) (hd : 2 * M * d ≤ m) (hL : 2 * L ≤ n) :
    Nonempty (FullPregrill G M L) := by
  obtain ⟨F, _, _⟩ := P.exists_fullPregrill_with_columns M L hMpos hM hd hL
  exact ⟨F⟩

end
end Erdos73Infrastructure.SimpleGraph
