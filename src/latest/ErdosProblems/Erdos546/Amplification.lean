/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos546.CopySplice
import ErdosProblems.Erdos546.Numeric
import ErdosProblems.Erdos546.Relabel
import ErdosProblems.Erdos546.SparseColor
import ErdosProblems.Erdos546.Sparsification

/-!
# The exact one-scale amplification step

This file combines high-degree deletion and copy splicing with bounded-degree
sparsification and Sudakov's sparse-colour lemma.  All losses are the literal
natural-number losses recorded in `Numeric.lean`.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos546

open Finset SimpleGraph

private lemma amplification_deletion_threshold {m s q : ℕ}
    (hm : m < s ^ 2) (hs : 0 < s) (hq : 0 < q) :
    2 * m < (2 * s / q ^ 3 + 1) * (q ^ 3 * s + 1) := by
  have hq3 : 0 < q ^ 3 := pow_pos hq _
  have hcover : 2 * s < q ^ 3 * (2 * s / q ^ 3 + 1) :=
    Nat.lt_mul_div_succ (2 * s) hq3
  have hm2 : 2 * m < 2 * s ^ 2 :=
    Nat.mul_lt_mul_of_pos_left hm (by norm_num)
  have hcover' : 2 * s ^ 2 <
      (2 * s / q ^ 3 + 1) * (q ^ 3 * s) := by
    calc
      2 * s ^ 2 = (2 * s) * s := by ring
      _ < (q ^ 3 * (2 * s / q ^ 3 + 1)) * s :=
        (Nat.mul_lt_mul_right hs).2 hcover
      _ = (2 * s / q ^ 3 + 1) * (q ^ 3 * s) := by ring
  exact hm2.trans
    (hcover'.trans_le (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)))

private lemma amplification_vertex_le_buffer {v m s : ℕ}
    (hv : v ≤ 2 * m) (hm : m < s ^ 2) (hs : 0 < s) :
    v ≤ reservoirBuffer s := by
  calc
    v ≤ 2 * m := hv
    _ ≤ 2 * s ^ 2 := Nat.mul_le_mul_left 2 hm.le
    _ ≤ 2 * s ^ 3 := by nlinarith
    _ = reservoirBuffer s := rfl

/-- The one-colour core of amplification.  The initial pair is assumed to lie
in `H`; the new pair may lie in either colour relative to `H`. -/
private theorem amplification_step_color
    {v N m q : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin N))
    (hm : G.edgeFinset.card = m) (_hmpos : 0 < m)
    (hnoiso : ∀ x, ¬G.IsIsolated x)
    (hq : 5 ≤ q) (hlegal : 2 ^ q ≤ sqrtScale m)
    {X Y : Finset (Fin N)} (hpair : MonoPair H X Y)
    (hX : q ^ 3 * sqrtScale m ≤ X.card)
    (hY : reservoirBuffer (sqrtScale m) *
      2 ^ reservoirExponent q (sqrtScale m) ≤ Y.card) :
    G ⊑ H ∨
      ∃ X' Y' : Finset (Fin N),
        HasMonoPair H X' Y' ∧
        pairTarget q (sqrtScale m) ≤ X'.card ∧
        (2 * q) ^ 3 * sqrtScale m ≤ X'.card ∧
        reservoirBuffer (sqrtScale m) *
          2 ^ reservoirExponent (2 * q) (sqrtScale m) ≤ Y'.card := by
  classical
  let s := sqrtScale m
  let D := 2 * s / q ^ 3
  let E := sparsificationLoss D q
  let L := sparsePairLoss q s
  let t := pairTarget q s
  have hs : 0 < s := by simp [s, sqrtScale]
  have hmss : m < s ^ 2 := by simpa [s] using lt_sqrtScale_sq m
  have hqpos : 0 < q := by omega
  have hdegree : D * q ^ 3 ≤ 2 * s := by
    simpa [D] using Nat.div_mul_le_self (2 * s) (q ^ 3)
  have hvertex : v ≤ reservoirBuffer s := by
    apply amplification_vertex_le_buffer
    · simpa [hm] using noIsolated_card_le_twice_edges G hnoiso
    · exact hmss
    · exact hs
  have hbufferY : reservoirBuffer s ≤ Y.card := by
    calc
      reservoirBuffer s = reservoirBuffer s * 1 := by simp
      _ ≤ reservoirBuffer s * 2 ^ reservoirExponent q s := by
        exact Nat.mul_le_mul_left _
          ((Nat.one_le_iff_ne_zero).mpr (by positivity))
      _ ≤ Y.card := by simpa [s] using hY
  obtain ⟨A, hAcard, hAdeg⟩ :=
    exists_deleted_card_le_and_maxDegree_induce_le G hm (by
      simpa [D, s] using
        amplification_deletion_threshold hmss hs hqpos)
  have hAX : A.card ≤ X.card :=
    hAcard.trans (by simpa [s] using hX)
  by_cases hDzero : D = 0
  · left
    apply isContained_of_monoPair_of_card_le_of_induce_isContained hpair hAX
    have hlezero : (G.induce (↑A : Set (Fin v))ᶜ).maxDegree ≤ 0 := by
      rw [← hDzero]
      exact hAdeg
    have hzero : (G.induce (↑A : Set (Fin v))ᶜ).maxDegree = 0 :=
      Nat.eq_zero_of_le_zero hlezero
    have hbot : G.induce (↑A : Set (Fin v))ᶜ = ⊥ :=
      (G.induce (↑A : Set (Fin v))ᶜ).maxDegree_eq_zero_iff.mp hzero
    rw [hbot, bot_isContained_iff_card_le]
    calc
      Fintype.card (↑((↑A : Set (Fin v))ᶜ) : Type) ≤ v :=
        by
          change Fintype.card {x : Fin v // x ∉ A} ≤ v
          let emb : {x : Fin v // x ∉ A} ↪ Fin v :=
            Function.Embedding.subtype _
          have hc := Fintype.card_le_of_injective emb emb.injective
          simpa only [Fintype.card_fin] using hc
      _ ≤ reservoirBuffer s := hvertex
      _ ≤ Y.card := hbufferY
      _ = Fintype.card (↑(↑Y : Set (Fin N)) : Type) := by simp
  have hDpos : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr hDzero
  let F₀ : SimpleGraph (↑((↑A : Set (Fin v))ᶜ)) :=
    G.induce (↑A : Set (Fin v))ᶜ
  let f := Fintype.card (↑((↑A : Set (Fin v))ᶜ) : Type)
  let F : SimpleGraph (Fin f) := F₀.overFin rfl
  letI : DecidableRel F.Adj := Classical.decRel _
  have hFdeg : F.maxDegree ≤ D := by
    calc
      F.maxDegree = F₀.maxDegree := by
        simpa [F] using maxDegree_overFin_eq F₀
      _ ≤ D := by simpa [F₀] using hAdeg
  by_cases hfzero : f = 0
  · left
    apply isContained_of_monoPair_of_card_le_of_induce_isContained hpair hAX
    letI : IsEmpty (↑((↑A : Set (Fin v))ᶜ) : Type) :=
      Fintype.card_eq_zero_iff.mp (by simpa [f] using hfzero)
    exact IsContained.of_isEmpty
  have hfpos : 0 < f := Nat.pos_of_ne_zero hfzero
  have hfvertex : f ≤ v := by
    dsimp [f]
    change Fintype.card {x : Fin v // x ∉ A} ≤ v
    let emb : {x : Fin v // x ∉ A} ↪ Fin v :=
      Function.Embedding.subtype _
    have hc := Fintype.card_le_of_injective emb emb.injective
    simpa only [Fintype.card_fin] using hc
  have hER : E ≤ reservoirExponent q s := by
    have hsmall := sparsificationLoss_le (D := D) (q := q) (s := s)
      hqpos hdegree
    calc
      E = sparsificationLoss D q := rfl
      _ ≤ 144 * ceilDiv s q := hsmall
      _ ≤ 2048 * ceilDiv s q :=
        Nat.mul_le_mul_right _ (by norm_num)
      _ = reservoirExponent q s := rfl
  have hFY : f * 2 ^ E ≤ Y.card := by
    calc
      f * 2 ^ E ≤ reservoirBuffer s * 2 ^ E :=
        Nat.mul_le_mul_right _ (hfvertex.trans hvertex)
      _ ≤ reservoirBuffer s * 2 ^ reservoirExponent q s :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hER)
      _ ≤ Y.card := by simpa [s] using hY
  let Hᵧ : SimpleGraph (↑Y : Set (Fin N)) := H.induce (↑Y : Set (Fin N))
  let J : SimpleGraph (Fin Y.card) :=
    Hᵧ.overFin (Fintype.card_coe Y)
  letI : DecidableRel J.Adj := Classical.decRel _
  by_cases hfree : ¬F ⊑ J
  · obtain ⟨S, hSsparse, hYS⟩ :=
      exists_squareSparse_of_boundedDegree_free F J hfpos
        (three_mul_ge_fifteen hq) hDpos hFdeg (by
          simpa [E, sparsificationLoss] using hFY) hfree
    have hbudget : reservoirExponent (2 * q) s + (E + L) ≤
        reservoirExponent q s := by
      simpa [E, L, reservoirExponent] using
        loss_budget_for_next_scale (D := D) (q := q) (s := s)
          hq hlegal hdegree
    have hEL : E + L ≤ reservoirExponent q s := by omega
    have htbuffer : t ≤ reservoirBuffer s := by
      simpa [t, reservoirBuffer] using pairTarget_le_buffer hlegal
    have hcolorSize : t * 2 ^ L ≤ S.card := by
      apply Nat.le_of_mul_le_mul_left (c := 2 ^ E) (hc := by positivity)
      calc
        2 ^ E * (t * 2 ^ L) = t * 2 ^ (E + L) := by
          simp only [pow_add]
          ring
        _ ≤ reservoirBuffer s * 2 ^ reservoirExponent q s :=
          Nat.mul_le_mul htbuffer
            (Nat.pow_le_pow_right (by norm_num) hEL)
        _ ≤ Y.card := by simpa [s] using hY
        _ ≤ 2 ^ E * S.card := by
          simpa [E, sparsificationLoss] using hYS
    let Jᵤ : SimpleGraph (↑S : Set (Fin Y.card)) :=
      J.induce (↑S : Set (Fin Y.card))
    let K : SimpleGraph (Fin S.card) :=
      Jᵤ.overFin (Fintype.card_coe S)
    have hKuniv : SquareSparse (3 * q) K Finset.univ := by
      simpa [Jᵤ, K] using squareSparse_induce_overFin_univ J S hSsparse
    obtain ⟨U₀, V₀, hUV₀, htU₀, hSV₀⟩ :=
      exists_monoPair_of_squareSparse K (three_mul_ge_fifteen hq)
        (by simpa [t] using pairTarget_ge_density_denominator hlegal)
        hKuniv (by simpa [t, L, sparsePairLoss] using hcolorSize)
    obtain ⟨U₁, V₁, hUV₁, hU₁card, hV₁card⟩ :=
      hasMonoPair_overFin_induce_to_ambient J S U₀ V₀ hUV₀
    obtain ⟨U₂, V₂, hUV₂, hU₂card, hV₂card⟩ :=
      hasMonoPair_overFin_induce_to_ambient H Y U₁ V₁ (by
        simpa [Hᵧ, J] using hUV₁)
    have hreservoir₀ : reservoirBuffer s *
        2 ^ reservoirExponent (2 * q) s ≤ V₀.card := by
      apply Nat.le_of_mul_le_mul_left (c := 2 ^ (E + L)) (hc := by positivity)
      calc
        2 ^ (E + L) *
              (reservoirBuffer s * 2 ^ reservoirExponent (2 * q) s) =
            reservoirBuffer s *
              2 ^ (reservoirExponent (2 * q) s + (E + L)) := by
          simp only [pow_add]
          ring
        _ ≤ reservoirBuffer s * 2 ^ reservoirExponent q s :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hbudget)
        _ ≤ Y.card := by simpa [s] using hY
        _ ≤ 2 ^ E * S.card := by
          simpa [E, sparsificationLoss] using hYS
        _ ≤ 2 ^ E * (2 ^ L * V₀.card) :=
          Nat.mul_le_mul_left _ (by
            simpa [L, sparsePairLoss] using hSV₀)
        _ = 2 ^ (E + L) * V₀.card := by
          simp only [pow_add]
          ring
    right
    refine ⟨U₂, V₂, hUV₂, ?_, ?_, ?_⟩
    · calc
        pairTarget q (sqrtScale m) = t := by simp [t, s]
        _ ≤ U₀.card := htU₀
        _ = U₁.card := hU₁card.symm
        _ = U₂.card := hU₂card.symm
    · calc
        (2 * q) ^ 3 * sqrtScale m ≤ pairTarget q (sqrtScale m) :=
          next_cube_le_pairTarget hq
        _ = t := by simp [t, s]
        _ ≤ U₀.card := htU₀
        _ = U₁.card := hU₁card.symm
        _ = U₂.card := hU₂card.symm
    · calc
        reservoirBuffer (sqrtScale m) *
              2 ^ reservoirExponent (2 * q) (sqrtScale m) =
            reservoirBuffer s * 2 ^ reservoirExponent (2 * q) s := by
          simp [s]
        _ ≤ V₀.card := hreservoir₀
        _ = V₁.card := hV₁card.symm
        _ = V₂.card := hV₂card.symm
  · left
    have hFJ : F ⊑ J := not_not.mp hfree
    have hrest : F₀ ⊑ Hᵧ := by
      exact (isContained_congr
        (F₀.overFinIso rfl)
        (Hᵧ.overFinIso (Fintype.card_coe Y))).mpr (by
          simpa [F, J] using hFJ)
    exact isContained_of_monoPair_of_card_le_of_induce_isContained
      hpair hAX (by simpa [F₀, Hᵧ] using hrest)

/-- Exact single-scale amplification.  Either the colouring already contains
`G` in one of its two colours, or the scale doubles and the full reservoir
invariant survives.  The raw `pairTarget` bound is retained because it is the
quantity used by the terminal crossing argument; the cubic scale bound follows
from it and is also recorded explicitly for iteration. -/
theorem amplification_step
    {v N m q : ℕ} (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (R : SimpleGraph (Fin N))
    (hm : G.edgeFinset.card = m) (hmpos : 0 < m)
    (hnoiso : ∀ x, ¬G.IsIsolated x)
    (hq : 5 ≤ q) (hlegal : 2 ^ q ≤ sqrtScale m)
    {X Y : Finset (Fin N)} (hpair : HasMonoPair R X Y)
    (hX : q ^ 3 * sqrtScale m ≤ X.card)
    (hY : reservoirBuffer (sqrtScale m) *
      2 ^ reservoirExponent q (sqrtScale m) ≤ Y.card) :
    G ⊑ R ∨ G ⊑ Rᶜ ∨
      ∃ X' Y' : Finset (Fin N),
        HasMonoPair R X' Y' ∧
        pairTarget q (sqrtScale m) ≤ X'.card ∧
        (2 * q) ^ 3 * sqrtScale m ≤ X'.card ∧
        reservoirBuffer (sqrtScale m) *
          2 ^ reservoirExponent (2 * q) (sqrtScale m) ≤ Y'.card := by
  rcases hpair with hred | hblue
  · rcases amplification_step_color G R hm hmpos hnoiso hq hlegal hred hX hY with
      hcopy | ⟨X', Y', hpair', ht, hcubic, hreservoir⟩
    · exact Or.inl hcopy
    · exact Or.inr (Or.inr ⟨X', Y', hpair', ht, hcubic, hreservoir⟩)
  · rcases amplification_step_color G Rᶜ hm hmpos hnoiso hq hlegal hblue hX hY with
      hcopy | ⟨X', Y', hpair', ht, hcubic, hreservoir⟩
    · exact Or.inr (Or.inl hcopy)
    · exact Or.inr (Or.inr ⟨X', Y',
        (hasMonoPair_compl_iff R X' Y').mp hpair', ht, hcubic, hreservoir⟩)

end Erdos546
