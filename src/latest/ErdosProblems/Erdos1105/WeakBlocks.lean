import ErdosProblems.Erdos1105.Triangles

namespace Erdos1105

open SimpleGraph
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Embedding the edges of one fiber into the complete graph on all vertices. -/
def fiberHom {V I : Type*} (block : V → I) (i : I) :
    (⊤ : SimpleGraph {v // block v = i}) →g (⊤ : SimpleGraph V) where
  toFun := Subtype.val
  map_rel' := fun h ↦ Subtype.val_injective.ne h

/-- Counting colors in a partition: internal edges contribute at most one
color each, and all remaining colors come from the quotient palette. -/
theorem colors_le_internal_add_cross {V I C D : Type*}
    [Fintype V] [Fintype I] [Fintype C] [Fintype D]
    (block : V → I) (c : (⊤ : SimpleGraph V).edgeSet → C)
    (hc : Function.Surjective c) (d : (⊤ : SimpleGraph I).edgeSet → D) (cross : D → C)
    (hcross : ∀ a b (hab : a ≠ b) (hne : block a ≠ block b),
      c ⟨s(a, b), hab⟩ = cross (d ⟨s(block a, block b), hne⟩)) :
    Fintype.card C ≤ (∑ i : I, (Fintype.card {v // block v = i}).choose 2) +
      Fintype.card D := by
  classical
  let g : (Σ i : I, (⊤ : SimpleGraph {v // block v = i}).edgeSet) ⊕ D → C :=
    fun x ↦ match x with
      | Sum.inl ⟨i, e⟩ => c ((fiberHom block i).mapEdgeSet e)
      | Sum.inr j => cross j
  have hg : Function.Surjective g := by
    intro col
    obtain ⟨⟨e, he⟩, rfl⟩ := hc col
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : a ≠ b := he
      by_cases h : block a = block b
      · refine ⟨Sum.inl ⟨block a, ⟨s(⟨a, rfl⟩, ⟨b, h.symm⟩),
          fun heq ↦ hab (congrArg Subtype.val heq)⟩⟩, rfl⟩
      · exact ⟨Sum.inr (d ⟨s(block a, block b), h⟩), (hcross a b hab h).symm⟩
  have h := Fintype.card_le_of_surjective g hg
  rw [Fintype.card_sum, Fintype.card_sigma] at h
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [card_edgeSet, card_edgeFinset_top_eq_card_choose_two]

lemma choose_two_add_one_le_slope {s r : ℕ} (hs : 1 ≤ s) (hsr : s ≤ r) (hr : 2 ≤ r) :
    (s.choose 2 : ℝ) + 1 ≤ (((r : ℝ) - 1) / 2 + 1 / r) * s := by
  have hsp : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsr' : (s : ℝ) ≤ r := by exact_mod_cast hsr
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hpos : (0 : ℝ) < r := by positivity
  rw [Nat.cast_choose_two ℝ s]
  apply (mul_le_mul_iff_right₀ hpos).mp
  have hprod : 0 ≤ ((r : ℝ) - s) * ((r : ℝ) * s - 2) :=
    mul_nonneg (by linarith) (by nlinarith)
  have hinv : (1 / (r : ℝ)) * r = 1 := div_mul_cancel₀ _ hpos.ne'
  nlinarith

/-- A quotient without a rainbow triangle uses at most one fewer color than
its number of blocks. -/
lemma quotient_colors_le {I D : Type*} [Fintype I] [Fintype D]
    (d : (⊤ : SimpleGraph I).edgeSet → D) (hd : Function.Surjective d)
    (htri : NoRainbowTriangle (extendColor d)) :
    Fintype.card D ≤ Fintype.card I - 1 := by
  have h := card_le_antiRamseyNum d hd (no_copy_of_noRainbowTriangle d htri)
  rwa [antiRamseyNum_cycleGraph_three] at h

/-- The sharp cycle upper bound for weakly anticyclic block colorings. -/
theorem weak_blocks_upper_bound {V I C D : Type*}
    [Fintype V] [Nonempty V] [Finite I] [Fintype C] [Finite D]
    (r : ℕ) (hr : 2 ≤ r) (block : V → I) (hblock : Function.Surjective block)
    (hsize : ∀ i, Fintype.card {v // block v = i} ≤ r)
    (c : (⊤ : SimpleGraph V).edgeSet → C) (hc : Function.Surjective c)
    (d : (⊤ : SimpleGraph I).edgeSet → D) (hd : Function.Surjective d) (cross : D → C)
    (hcross : ∀ a b (hab : a ≠ b) (hne : block a ≠ block b),
      c ⟨s(a, b), hab⟩ = cross (d ⟨s(block a, block b), hne⟩))
    (htri : NoRainbowTriangle (extendColor d)) :
    (Fintype.card C : ℝ) ≤
      (((r : ℝ) - 1) / 2 + 1 / r) * Fintype.card V - 1 := by
  classical
  let := Fintype.ofFinite I
  let := Fintype.ofFinite D
  have : Nonempty I := ⟨block (Classical.arbitrary V)⟩
  have hI : 1 ≤ Fintype.card I := Fintype.card_pos
  have hcount := colors_le_internal_add_cross block c hc d cross hcross
  have hquot := quotient_colors_le d hd htri
  have hcountR : (Fintype.card C : ℝ) ≤
      (∑ i : I, ((Fintype.card {v // block v = i}).choose 2 : ℝ)) + Fintype.card D := by
    exact_mod_cast hcount
  have hquotR : (Fintype.card D : ℝ) + 1 ≤ Fintype.card I := by
    exact_mod_cast (show Fintype.card D + 1 ≤ Fintype.card I by omega)
  have hsum : (∑ i : I, (((Fintype.card {v // block v = i}).choose 2 : ℝ) + 1)) ≤
      (((r : ℝ) - 1) / 2 + 1 / r) * Fintype.card V := by
    calc
      _ ≤ ∑ i : I, (((r : ℝ) - 1) / 2 + 1 / r) *
          (Fintype.card {v // block v = i} : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        apply choose_two_add_one_le_slope _ (hsize i) hr
        obtain ⟨v, hv⟩ := hblock i
        exact Fintype.card_pos_iff.mpr ⟨⟨v, hv⟩⟩
      _ = _ := by
        rw [← Finset.mul_sum]
        congr 1
        norm_cast
        rw [← Fintype.card_sigma]
        exact Fintype.card_congr (Equiv.sigmaFiberEquiv block)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hsum
  linarith

end Erdos1105
