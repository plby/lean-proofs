import Mathlib.Data.Fintype.EquivFin

/-!
# Matching finite families with prescribed colors

An inequality between the sizes of every pair of color fibers gives an
injection preserving colors. For near splitting cliques the color is their
unique edge in the original graph.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem card_filter_subtype {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (univ.filter fun x : s => p x.val).card = (s.filter p).card := by
  classical
  have h : (univ.filter fun x : s => p x.val).map (Function.Embedding.subtype _) =
      s.filter p := by
    ext x
    simp [and_comm]
  rw [← h, card_map]

theorem exists_color_preserving_embedding {N P C : Type*} [Fintype N] [Fintype P]
    [DecidableEq C]
    (negative : N → C) (positive : P → C)
    (hcard : ∀ c, (univ.filter fun x => negative x = c).card ≤
      (univ.filter fun y => positive y = c).card) :
    ∃ f : N ↪ P, ∀ x, positive (f x) = negative x := by
  classical
  have hfiber (c : C) : Nonempty ({x : N // negative x = c} ↪
      {y : P // positive y = c}) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Fintype.card_subtype] using hcard c
  let g (c : C) : {x : N // negative x = c} ↪ {y : P // positive y = c} :=
    Classical.choice (hfiber c)
  let f : N → P := fun x => (g (negative x) ⟨x, rfl⟩).val
  have hf (x : N) : positive (f x) = negative x := (g (negative x) ⟨x, rfl⟩).property
  have hf_eq (x : N) (c : C) (hx : negative x = c) :
      f x = (g c ⟨x, hx⟩).val := by
    subst c
    rfl
  refine ⟨⟨f, ?_⟩, hf⟩
  intro x y hxy
  have hc : negative x = negative y := (hf x).symm.trans ((congrArg positive hxy).trans (hf y))
  have hy := hf_eq y (negative x) hc.symm
  have hsub : g (negative x) ⟨x, rfl⟩ = g (negative x) ⟨y, hc.symm⟩ :=
    Subtype.ext (hxy.trans hy)
  exact congrArg (fun z : {z : N // negative z = negative x} => z.val)
    ((g (negative x)).injective hsub)

end Arxiv2411_18291
