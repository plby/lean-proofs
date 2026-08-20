/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Cover

/-!
# Minimal-counterexample infrastructure for Erdős Problem 518

This file packages the type-changing bookkeeping in the minimal-counterexample proof.  Deleting
a finite set changes the vertex type to a subtype; covers of the induced graph are lifted back to
the ambient graph using the utilities in `Cover`.  The main consequence is the opposite-colour
intersection bound: in a minimal counterexample of order `c ^ 2 + r`, a red path and a blue path
have at most `r` common vertices.
-/

open scoped SimpleGraph

namespace Erdos518

universe u

variable {V : Type u}

/-! ## Strong induction over arbitrary finite vertex types -/

/-- Strong induction on the cardinality of a finite vertex type.  The induction hypothesis is
itself polymorphic in the smaller vertex type, which is the form needed after passing to an
induced subtype. -/
theorem erdos518ForType_strong_induction
    (step : ∀ {W : Type u} [Fintype W] (H : SimpleGraph W),
      (∀ {U : Type u} [Fintype U], Fintype.card U < Fintype.card W →
        ∀ J : SimpleGraph U, Erdos518ForType J) →
      Erdos518ForType H) :
    ∀ {W : Type u} [Fintype W] (H : SimpleGraph W), Erdos518ForType H := by
  let P : ℕ → Prop := fun n ↦
    ∀ (W : Type u) [Fintype W], Fintype.card W = n →
      ∀ H : SimpleGraph W, Erdos518ForType H
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro W _ hW H
        apply step H
        intro U _ hUW J
        apply ih (Fintype.card U)
        · simpa [hW] using hUW
        · rfl
  intro W _ H
  exact hP (Fintype.card W) W rfl H

/-! ## Complements and induced subgraphs -/

/-- Taking the complementary colour commutes with passing to an induced subtype. -/
lemma compl_induce (G : SimpleGraph V) (S : Set V) :
    (G.induce S)ᶜ = Gᶜ.induce S := by
  ext x y
  simp only [SimpleGraph.compl_adj, SimpleGraph.induce_adj]
  exact and_congr Subtype.coe_injective.ne_iff.symm Iff.rfl

/-- A path of the ambient graph which contains `S` is a one-path cover of `S`. -/
lemma hasPathCoverOnAtMost_one_of_path_covers
    {G : SimpleGraph V} {S : Finset V} {p : List V}
    (hp : IsPath G p) (hSp : ∀ v ∈ S, v ∈ p) :
    HasPathCoverOnAtMost G (S : Set V) 1 := by
  refine ⟨[p], by simp, ?_⟩
  constructor
  · simpa using hp
  · intro v hv
    exact ⟨p, by simp, hSp v hv⟩

/-! ## Removing a large set and adding one path -/

/-- The cardinality of the vertex type left after deleting a finset. -/
lemma card_compl_finset_subtype [Fintype V] [DecidableEq V] (S : Finset V) :
    Fintype.card {v : V // v ∉ S} = Fintype.card V - S.card := by
  rw [Fintype.card_subtype_compl (fun v : V ↦ v ∈ S)]
  simp

/-- Minimal-counterexample extension step.

Suppose `|V| = c² + r`, a set `S` has at least `r + 1` vertices, and both a red path and a
blue path contain `S`.  If Erdős 518 holds on every strictly smaller finite vertex type, then
one of the two colours already has a cover of `V` by at most `c` paths.  Thus these hypotheses
cannot occur when both `c`-path covers fail.
-/
theorem has_colour_cover_of_remove_large_finset_local
    [Fintype V]
    (G : SimpleGraph V) (c r : ℕ)
    (hcard : Fintype.card V = c ^ 2 + r)
    (hinduced : ∀ T : Finset V, T.card < Fintype.card V →
      Erdos518ForType (G.induce (T : Set V)))
    (S : Finset V) (hS : r + 1 ≤ S.card)
    {pRed pBlue : List V}
    (hpRed : IsPath G pRed) (hRedCovers : ∀ v ∈ S, v ∈ pRed)
    (hpBlue : IsPath Gᶜ pBlue) (hBlueCovers : ∀ v ∈ S, v ∈ pBlue) :
    HasPathCoverAtMost G c ∨ HasPathCoverAtMost Gᶜ c := by
  classical
  let U : Set V := (↑Sᶜ : Set V)
  have hUcard : Fintype.card U = Fintype.card V - S.card := by
    change Fintype.card (↥Sᶜ) = Fintype.card V - S.card
    rw [Fintype.card_coe, Finset.card_compl]
  have hSnonempty : S.Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hcompllt : Sᶜ.card < Fintype.card V :=
    (Finset.card_compl_lt_iff_nonempty S).mpr hSnonempty
  have hsmall : Erdos518ForType (G.induce U) := hinduced Sᶜ hcompllt
  have hcpos : 0 < c := by
    have hSle : S.card ≤ Fintype.card V := by
      simpa using S.card_le_univ
    by_contra hc
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos hc
    subst c
    norm_num at hcard
    omega
  have hUltSquare : Fintype.card U < c ^ 2 := by
    have hSle : S.card ≤ Fintype.card V := by
      simpa using S.card_le_univ
    have hc2pos : 0 < c ^ 2 := pow_pos hcpos _
    rw [hUcard, hcard]
    omega
  have hsqrt : Nat.sqrt (Fintype.card U) + 1 ≤ c := by
    have := Nat.sqrt_lt'.2 hUltSquare
    omega
  rcases hsmall with hRed | hBlue
  · left
    have hSon : HasPathCoverOnAtMost G (S : Set V) 1 :=
      hasPathCoverOnAtMost_one_of_path_covers hpRed hRedCovers
    have hcover : HasPathCoverAtMost G (1 + Nat.sqrt (Fintype.card U)) := by
      rw [hasPathCoverAtMost_iff_on_univ]
      have hrem := hRed.lift_subtype G U
      simpa [U] using hSon.append hrem
    exact hcover.mono (by simpa [Nat.add_comm] using hsqrt)
  · right
    have hBlue' : HasPathCoverAtMost (Gᶜ.induce U) (Nat.sqrt (Fintype.card U)) := by
      rw [← compl_induce]
      exact hBlue
    have hSon : HasPathCoverOnAtMost Gᶜ (S : Set V) 1 :=
      hasPathCoverOnAtMost_one_of_path_covers hpBlue hBlueCovers
    have hcover : HasPathCoverAtMost Gᶜ (1 + Nat.sqrt (Fintype.card U)) := by
      rw [hasPathCoverAtMost_iff_on_univ]
      have hrem := hBlue'.lift_subtype Gᶜ U
      simpa [U] using hSon.append hrem
    exact hcover.mono (by simpa [Nat.add_comm] using hsqrt)

/-- A version of the preceding extension step with an induction hypothesis polymorphic in the
smaller vertex type. -/
theorem has_colour_cover_of_remove_large_finset
    [Fintype V]
    (G : SimpleGraph V) (c r : ℕ)
    (hcard : Fintype.card V = c ^ 2 + r)
    (hind : ∀ {W : Type u} [Fintype W], Fintype.card W < Fintype.card V →
      ∀ H : SimpleGraph W, Erdos518ForType H)
    (S : Finset V) (hS : r + 1 ≤ S.card)
    {pRed pBlue : List V}
    (hpRed : IsPath G pRed) (hRedCovers : ∀ v ∈ S, v ∈ pRed)
    (hpBlue : IsPath Gᶜ pBlue) (hBlueCovers : ∀ v ∈ S, v ∈ pBlue) :
    HasPathCoverAtMost G c ∨ HasPathCoverAtMost Gᶜ c := by
  classical
  let U : Set V := (S : Set V)ᶜ
  have hUcard : Fintype.card U = Fintype.card V - S.card := by
    change Fintype.card {v : V // v ∉ S} = Fintype.card V - S.card
    exact card_compl_finset_subtype S
  have hcpos : 0 < c := by
    have hSle : S.card ≤ Fintype.card V := by
      simpa using S.card_le_univ
    by_contra hc
    have hc0 : c = 0 := Nat.eq_zero_of_not_pos hc
    subst c
    norm_num at hcard
    omega
  have hUltSquare : Fintype.card U < c ^ 2 := by
    have hSle : S.card ≤ Fintype.card V := by
      simpa using S.card_le_univ
    have hc2pos : 0 < c ^ 2 := pow_pos hcpos _
    rw [hUcard, hcard]
    omega
  have hUlt : Fintype.card U < Fintype.card V := by
    rw [hcard]
    exact hUltSquare.trans_le (Nat.le_add_right _ _)
  have hsqrt : Nat.sqrt (Fintype.card U) + 1 ≤ c := by
    have := Nat.sqrt_lt'.2 hUltSquare
    omega
  have hsmall := hind hUlt (G.induce U)
  rcases hsmall with hRed | hBlue
  · left
    have hSon : HasPathCoverOnAtMost G (S : Set V) 1 :=
      hasPathCoverOnAtMost_one_of_path_covers hpRed hRedCovers
    have hcover : HasPathCoverAtMost G (1 + Nat.sqrt (Fintype.card U)) := by
      exact hasPathCoverAtMost_of_induced_compl hRed hSon
    exact hcover.mono (by simpa [Nat.add_comm] using hsqrt)
  · right
    have hBlue' : HasPathCoverAtMost (Gᶜ.induce U) (Nat.sqrt (Fintype.card U)) := by
      rw [← compl_induce]
      exact hBlue
    have hSon : HasPathCoverOnAtMost Gᶜ (S : Set V) 1 :=
      hasPathCoverOnAtMost_one_of_path_covers hpBlue hBlueCovers
    have hcover : HasPathCoverAtMost Gᶜ (1 + Nat.sqrt (Fintype.card U)) := by
      exact hasPathCoverAtMost_of_induced_compl hBlue' hSon
    exact hcover.mono (by simpa [Nat.add_comm] using hsqrt)

/-- In a counterexample at order `c² + r`, every red path and blue path have at most `r`
common vertices.  This is Lemma 3.1 (the opposite-colour intersection lemma) in the
minimal-counterexample argument. -/
theorem oppositeColour_path_intersection_card_le
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c r : ℕ)
    (hcard : Fintype.card V = c ^ 2 + r)
    (hind : ∀ {W : Type u} [Fintype W], Fintype.card W < Fintype.card V →
      ∀ H : SimpleGraph W, Erdos518ForType H)
    (hRedFail : ¬ HasPathCoverAtMost G c)
    (hBlueFail : ¬ HasPathCoverAtMost Gᶜ c)
    {pRed pBlue : List V}
    (hpRed : IsPath G pRed) (hpBlue : IsPath Gᶜ pBlue) :
    (pathSupport pRed ∩ pathSupport pBlue).card ≤ r := by
  by_contra hle
  have hlarge : r + 1 ≤ (pathSupport pRed ∩ pathSupport pBlue).card := by
    omega
  have hcover := has_colour_cover_of_remove_large_finset G c r hcard hind
    (pathSupport pRed ∩ pathSupport pBlue) hlarge hpRed
    (fun v hv ↦ mem_pathSupport.mp (Finset.mem_inter.mp hv).1) hpBlue
    (fun v hv ↦ mem_pathSupport.mp (Finset.mem_inter.mp hv).2)
  exact hcover.elim hRedFail hBlueFail

/-- Local-minimality form of the opposite-colour intersection lemma.  Unlike
`oppositeColour_path_intersection_card_le`, this asks only for the proper induced subgraphs of
the fixed colouring `G`; this is exactly the field stored by `Configuration`. -/
theorem oppositeColour_path_intersection_card_le_local
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c r : ℕ)
    (hcard : Fintype.card V = c ^ 2 + r)
    (hinduced : ∀ T : Finset V, T.card < Fintype.card V →
      Erdos518ForType (G.induce (T : Set V)))
    (hRedFail : ¬ HasPathCoverAtMost G c)
    (hBlueFail : ¬ HasPathCoverAtMost Gᶜ c)
    {pRed pBlue : List V}
    (hpRed : IsPath G pRed) (hpBlue : IsPath Gᶜ pBlue) :
    (pathSupport pRed ∩ pathSupport pBlue).card ≤ r := by
  by_contra hle
  have hlarge : r + 1 ≤ (pathSupport pRed ∩ pathSupport pBlue).card := by
    omega
  have hcover := has_colour_cover_of_remove_large_finset_local G c r hcard hinduced
    (pathSupport pRed ∩ pathSupport pBlue) hlarge hpRed
    (fun v hv ↦ mem_pathSupport.mp (Finset.mem_inter.mp hv).1) hpBlue
    (fun v hv ↦ mem_pathSupport.mp (Finset.mem_inter.mp hv).2)
  exact hcover.elim hRedFail hBlueFail

end Erdos518
