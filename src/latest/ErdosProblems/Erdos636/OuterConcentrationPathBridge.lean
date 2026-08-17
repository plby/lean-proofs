/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0.
-/

import ErdosProblems.Erdos636.CrowdScheduleBridge
import ErdosProblems.Erdos636.StructuralOuterConcentration

/-!
# From concentrated switching orderings to the canonical raw path

This file is the cycle-free bridge between the permutation-concentration
output and the graph-facing crowd schedule.  It reconstructs the literal
`OuterSwitchingPath.RawPath` represented by a pair of concentrated switching
orderings, proves equality of every in-range state, and records the elementary
degree-motion estimates consumed by `CrowdScheduleBridge`.
-/

open Classical SimpleGraph

namespace Erdos636
namespace OuterConcentrationPathBridge

open OuterSwitching
open OuterSwitchingPath
open StructuralOuterConcentration

universe u

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Re-encoding an ordering as a permutation -/

/-- An enumeration of a finset, regarded as an equivalence onto its subtype. -/
noncomputable def orderingEquiv (W : Finset V) {n : ℕ}
    (f : Fin n → V) (hmem : ∀ i, f i ∈ W)
    (hinj : Function.Injective f) (hsurj : ∀ v ∈ W, ∃ i, f i = v) :
    Fin n ≃ W :=
  Equiv.ofBijective (fun i ↦ ⟨f i, hmem i⟩) ⟨by
    intro i j hij
    exact hinj (congrArg Subtype.val hij), by
    rintro ⟨v, hv⟩
    obtain ⟨i, rfl⟩ := hsurj v hv
    exact ⟨i, rfl⟩⟩

/-- Reversal of a finite interval as a permutation. -/
noncomputable def finRevPermutation (n : ℕ) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective Fin.rev ⟨Fin.rev_injective, by
    intro i
    exact ⟨i.rev, Fin.rev_rev i⟩⟩

/-- The minus ordering, reversed and expressed in the canonical coordinates
of `S.Wminus`. -/
noncomputable def minusPermutationOfOrderings
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (O : SwitchingOrderings S.Wminus S.Wplus nW) :
    Equiv.Perm (Fin S.Wminus.card) :=
  (finCongr S.card_Wminus).trans
    ((finRevPermutation nW).trans
      ((orderingEquiv S.Wminus O.minus O.minus_mem O.minus_injective
        O.minus_surjective).trans (Finset.equivFin S.Wminus)))

/-- The plus ordering, expressed in the canonical coordinates of
`S.Wplus`. -/
noncomputable def plusPermutationOfOrderings
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (O : SwitchingOrderings S.Wminus S.Wplus nW) :
    Equiv.Perm (Fin S.Wplus.card) :=
  (finCongr S.card_Wplus).trans
    ((orderingEquiv S.Wplus O.plus O.plus_mem O.plus_injective
      O.plus_surjective).trans (Finset.equivFin S.Wplus))

@[simp] lemma decode_minusPermutationOfOrderings
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (O : SwitchingOrderings S.Wminus S.Wplus nW)
    (j : Fin S.Wminus.card) :
    ((Finset.equivFin S.Wminus).symm
      (minusPermutationOfOrderings O j)).1 =
        O.minus (Fin.rev (Fin.cast S.card_Wminus j)) := by
  simp only [minusPermutationOfOrderings, Equiv.trans_apply, finCongr_apply,
    finRevPermutation, Equiv.ofBijective_apply, orderingEquiv]
  exact congrArg Subtype.val
    ((Finset.equivFin S.Wminus).symm_apply_apply
      ((orderingEquiv S.Wminus O.minus O.minus_mem O.minus_injective
        O.minus_surjective) ((Fin.cast S.card_Wminus j).rev)))

@[simp] lemma decode_plusPermutationOfOrderings
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (O : SwitchingOrderings S.Wminus S.Wplus nW)
    (j : Fin S.Wplus.card) :
    ((Finset.equivFin S.Wplus).symm
      (plusPermutationOfOrderings O j)).1 =
        O.plus (Fin.cast S.card_Wplus j) := by
  simp only [plusPermutationOfOrderings, Equiv.trans_apply, finCongr_apply,
    orderingEquiv, Equiv.ofBijective_apply]
  exact congrArg Subtype.val
    ((Finset.equivFin S.Wplus).symm_apply_apply
      ((orderingEquiv S.Wplus O.plus O.plus_mem O.plus_injective
        O.plus_surjective) (Fin.cast S.card_Wplus j)))

/-- The literal raw path carried by a uniformly controlled pair of
orderings. -/
noncomputable def rawPathOfUniformDegreeControlledOrderings
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error) : RawPath S where
  minusPermutation := minusPermutationOfOrderings Q.toSwitchingOrderings
  plusPermutation := plusPermutationOfOrderings Q.toSwitchingOrderings

/-! ## Exact state transport -/

lemma rawPathOfUniformDegreeControlledOrderings_W_eq_state
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error)
    (i : ℕ) (hi : i ≤ nW) :
    (rawPathOfUniformDegreeControlledOrderings Q).W i =
      Q.toSwitchingOrderings.state i := by
  classical
  let O := Q.toSwitchingOrderings
  let P := rawPathOfUniformDegreeControlledOrderings Q
  ext v
  simp only [RawPath.W, SwitchingOrderings.state, Finset.mem_union]
  constructor
  · rintro (hv | hv)
    · left
      rw [permutationPrefix_eq_of_le] at hv
      · rw [Erdos88.BooleanSlices.signedSlicePositiveSupport,
          Finset.mem_map] at hv
        obtain ⟨r, _hr, hrv⟩ := hv
        let r' : Fin S.Wminus.card := Fin.castLE (by
          rw [S.card_Wminus]
          exact Nat.sub_le _ _) r
        let j : Fin nW := Fin.rev (Fin.cast S.card_Wminus r')
        refine Finset.mem_image.mpr ⟨j, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          dsimp [j]
          change i ≤ nW - (r.val + 1)
          omega
        · rw [← hrv]
          change O.minus j = ((Finset.equivFin S.Wminus).symm
            ((rawPathOfUniformDegreeControlledOrderings Q).minusPermutation
              r')).1
          symm
          simp [P, O, rawPathOfUniformDegreeControlledOrderings, j, r']
      · rw [S.card_Wminus]
        exact Nat.sub_le _ _
    · right
      rw [permutationPrefix_eq_of_le] at hv
      · rw [Erdos88.BooleanSlices.signedSlicePositiveSupport,
          Finset.mem_map] at hv
        obtain ⟨r, _hr, hrv⟩ := hv
        let r' : Fin S.Wplus.card := Fin.castLE (by
          rw [S.card_Wplus]
          exact hi) r
        let j : Fin nW := Fin.cast S.card_Wplus r'
        refine Finset.mem_image.mpr ⟨j, ?_, ?_⟩
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, r.isLt⟩
        · rw [← hrv]
          change O.plus j = ((Finset.equivFin S.Wplus).symm
            ((rawPathOfUniformDegreeControlledOrderings Q).plusPermutation
              r')).1
          symm
          simp [P, O, rawPathOfUniformDegreeControlledOrderings, j, r']
      · rw [S.card_Wplus]
        exact hi
  · rintro (hv | hv)
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
      left
      rw [permutationPrefix_eq_of_le]
      · rw [Erdos88.BooleanSlices.signedSlicePositiveSupport,
          Finset.mem_map]
        have hjge : i ≤ j := (Finset.mem_filter.mp hj).2
        let r : Fin (nW - i) := ⟨j.rev, by
          rw [Fin.val_rev]
          omega⟩
        let r' : Fin S.Wminus.card := Fin.castLE (by
          rw [S.card_Wminus]
          exact Nat.sub_le _ _) r
        refine ⟨r, Finset.mem_univ _, ?_⟩
        change ((Finset.equivFin S.Wminus).symm
            ((rawPathOfUniformDegreeControlledOrderings Q).minusPermutation
              r')).1 = O.minus j
        change ((Finset.equivFin S.Wminus).symm
            (minusPermutationOfOrderings O r')).1 = O.minus j
        rw [decode_minusPermutationOfOrderings]
        apply congrArg O.minus
        apply Fin.ext
        simp only [Fin.val_rev]
        change nW - (nW - (j.val + 1) + 1) = j.val
        omega
      · rw [S.card_Wminus]
        exact Nat.sub_le _ _
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
      right
      rw [permutationPrefix_eq_of_le]
      · rw [Erdos88.BooleanSlices.signedSlicePositiveSupport,
          Finset.mem_map]
        have hjlt : (j : ℕ) < i := (Finset.mem_filter.mp hj).2
        let r : Fin i := ⟨j, hjlt⟩
        let r' : Fin S.Wplus.card := Fin.castLE (by
          rw [S.card_Wplus]
          exact hi) r
        refine ⟨r, Finset.mem_univ _, ?_⟩
        change ((Finset.equivFin S.Wplus).symm
            ((rawPathOfUniformDegreeControlledOrderings Q).plusPermutation
              r')).1 = O.plus j
        simp [P, O, rawPathOfUniformDegreeControlledOrderings, r, r']
      · rw [S.card_Wplus]
        exact hi

@[simp] lemma rawPathOfUniformDegreeControlledOrderings_W_zero
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error) :
    (rawPathOfUniformDegreeControlledOrderings Q).W 0 = S.Wminus :=
  RawPath.W_zero _

@[simp] lemma rawPathOfUniformDegreeControlledOrderings_W_last
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error) :
    (rawPathOfUniformDegreeControlledOrderings Q).W nW = S.Wplus :=
  RawPath.W_last _

lemma rawPathOfUniformDegreeControlledOrderings_card
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error)
    (i : ℕ) (hi : i ≤ nW) :
    ((rawPathOfUniformDegreeControlledOrderings Q).W i).card = nW :=
  RawPath.card_W _ hi

lemma rawPathOfUniformDegreeControlledOrderings_disjoint_U0
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error) (i : ℕ) :
    Disjoint ((rawPathOfUniformDegreeControlledOrderings Q).W i) S.U0 :=
  RawPath.disjoint_W_U0 _ i

lemma rawPathOfUniformDegreeControlledOrderings_degree_control
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error)
    (i : ℕ) (hi : i ≤ nW) (x : Finset V) (hx : x ∈ S.matching) :
    |(degreeInto G ((rawPathOfUniformDegreeControlledOrderings Q).W i) x : ℝ) -
        Q.expected i| ≤ error := by
  rw [rawPathOfUniformDegreeControlledOrderings_W_eq_state Q i hi]
  exact Q.degree_control i hi x hx

lemma rawPathOfUniformDegreeControlledOrderings_degree_spread
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error)
    (i : ℕ) (hi : i ≤ nW) (x y : Finset V)
    (hx : x ∈ S.matching) (hy : y ∈ S.matching) :
    |(degreeInto G ((rawPathOfUniformDegreeControlledOrderings Q).W i) x : ℝ) -
        degreeInto G ((rawPathOfUniformDegreeControlledOrderings Q).W i) y| ≤
      2 * error := by
  rw [rawPathOfUniformDegreeControlledOrderings_W_eq_state Q i hi]
  exact StructuralOuterConcentration.UniformDegreeControlledOrderings.degree_spread
    Q i hi x y hx hy

/-! ## One-step and accumulated degree motion -/

lemma SwitchingOrderings.state_succ_sdiff_subset_pair
    {Wminus Wplus : Finset V} {nW : ℕ}
    (O : SwitchingOrderings Wminus Wplus nW)
    (i : ℕ) (hi : i < nW) :
    O.state (i + 1) \ O.state i ⊆
      {O.minus ⟨i, hi⟩, O.plus ⟨i, hi⟩} := by
  intro v hv
  obtain ⟨hvNext, hvNow⟩ := Finset.mem_sdiff.mp hv
  rcases Finset.mem_union.mp hvNext with hvMinus | hvPlus
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hvMinus
    exfalso
    apply hvNow
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, rfl⟩
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨Finset.mem_univ _, by omega⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hvPlus
    have hjlt : (j : ℕ) < i + 1 := (Finset.mem_filter.mp hj).2
    by_cases hji : (j : ℕ) < i
    · exfalso
      apply hvNow
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨j,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji⟩, rfl⟩
    · have hjeq : j = (⟨i, hi⟩ : Fin nW) := by
        apply Fin.ext
        change j.val = i
        omega
      subst j
      simp

lemma SwitchingOrderings.state_sdiff_succ_subset_pair
    {Wminus Wplus : Finset V} {nW : ℕ}
    (O : SwitchingOrderings Wminus Wplus nW)
    (i : ℕ) (hi : i < nW) :
    O.state i \ O.state (i + 1) ⊆
      {O.minus ⟨i, hi⟩, O.plus ⟨i, hi⟩} := by
  intro v hv
  obtain ⟨hvNow, hvNext⟩ := Finset.mem_sdiff.mp hv
  rcases Finset.mem_union.mp hvNow with hvMinus | hvPlus
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hvMinus
    have hjge : i ≤ (j : ℕ) := (Finset.mem_filter.mp hj).2
    by_cases hsucc : i + 1 ≤ (j : ℕ)
    · exfalso
      apply hvNext
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨j,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsucc⟩, rfl⟩
    · have hjeq : j = (⟨i, hi⟩ : Fin nW) := by
        apply Fin.ext
        change j.val = i
        omega
      subst j
      simp
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hvPlus
    exfalso
    apply hvNext
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, rfl⟩
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨Finset.mem_univ _, by omega⟩

lemma SwitchingOrderings.state_succ_sdiff_card_le_two
    {Wminus Wplus : Finset V} {nW : ℕ}
    (O : SwitchingOrderings Wminus Wplus nW)
    (i : ℕ) (hi : i < nW) :
    (O.state (i + 1) \ O.state i).card ≤ 2 := by
  calc
    _ ≤ ({O.minus ⟨i, hi⟩, O.plus ⟨i, hi⟩} : Finset V).card :=
      Finset.card_le_card (state_succ_sdiff_subset_pair O i hi)
    _ ≤ ({O.plus ⟨i, hi⟩} : Finset V).card + 1 :=
      Finset.card_insert_le _ _
    _ = 2 := by simp

lemma SwitchingOrderings.state_sdiff_succ_card_le_two
    {Wminus Wplus : Finset V} {nW : ℕ}
    (O : SwitchingOrderings Wminus Wplus nW)
    (i : ℕ) (hi : i < nW) :
    (O.state i \ O.state (i + 1)).card ≤ 2 := by
  calc
    _ ≤ ({O.minus ⟨i, hi⟩, O.plus ⟨i, hi⟩} : Finset V).card :=
      Finset.card_le_card (state_sdiff_succ_subset_pair O i hi)
    _ ≤ ({O.plus ⟨i, hi⟩} : Finset V).card + 1 :=
      Finset.card_insert_le _ _
    _ = 2 := by simp

lemma SwitchingOrderings.degreeInto_state_succ_natDist_le
    {Wminus Wplus : Finset V} {nW : ℕ}
    (G : SimpleGraph V) (O : SwitchingOrderings Wminus Wplus nW)
    (i : ℕ) (hi : i < nW) (x : Finset V) :
    Nat.dist (degreeInto G (O.state (i + 1)) x)
      (degreeInto G (O.state i) x) ≤ 2 * x.card := by
  have hforward := StructuralOuterConcentration.degreeInto_le_add_card_mul_sdiff
    G (O.state (i + 1)) (O.state i) x
  have hback := StructuralOuterConcentration.degreeInto_le_add_card_mul_sdiff
    G (O.state i) (O.state (i + 1)) x
  have hforward' : degreeInto G (O.state (i + 1)) x ≤
      degreeInto G (O.state i) x + 2 * x.card := by
    calc
      _ ≤ degreeInto G (O.state i) x +
          x.card * (O.state (i + 1) \ O.state i).card := hforward
      _ ≤ degreeInto G (O.state i) x + x.card * 2 := by
        gcongr
        exact state_succ_sdiff_card_le_two O i hi
      _ = degreeInto G (O.state i) x + 2 * x.card := by omega
  have hback' : degreeInto G (O.state i) x ≤
      degreeInto G (O.state (i + 1)) x + 2 * x.card := by
    calc
      _ ≤ degreeInto G (O.state (i + 1)) x +
          x.card * (O.state i \ O.state (i + 1)).card := hback
      _ ≤ degreeInto G (O.state (i + 1)) x + x.card * 2 := by
        gcongr
        exact state_sdiff_succ_card_le_two O i hi
      _ = degreeInto G (O.state (i + 1)) x + 2 * x.card := by omega
  unfold Nat.dist
  omega

/-- A natural-valued trajectory with step bound `step` is Lipschitz for
`Nat.dist` on its controlled time interval. -/
lemma natDist_le_step_mul_timeDist
    (f : ℕ → ℕ) (step bound i j : ℕ)
    (hstep : ∀ r < bound, Nat.dist (f (r + 1)) (f r) ≤ step)
    (hi : i ≤ bound) (hj : j ≤ bound) :
    Nat.dist (f i) (f j) ≤ step * Nat.dist i j := by
  have hforward (a d : ℕ) (had : a + d ≤ bound) :
      Nat.dist (f (a + d)) (f a) ≤ step * d := by
    induction d with
    | zero => simp
    | succ d ih =>
        have had' : a + d ≤ bound := by omega
        have hlt : a + d < bound := by omega
        calc
          Nat.dist (f (a + (d + 1))) (f a) =
              Nat.dist (f ((a + d) + 1)) (f a) := by congr 2 <;> omega
          _ ≤ Nat.dist (f ((a + d) + 1)) (f (a + d)) +
                Nat.dist (f (a + d)) (f a) :=
            Nat.dist.triangle_inequality _ _ _
          _ ≤ step + step * d := Nat.add_le_add (hstep (a + d) hlt) (ih had')
          _ = step * (d + 1) := by simp [Nat.mul_succ, Nat.add_comm]
  rcases le_total i j with hij | hji
  · have hjiEq : i + (j - i) = j := by omega
    rw [Nat.dist_eq_sub_of_le hij]
    have hf := hforward i (j - i) (by omega)
    rw [hjiEq] at hf
    simpa [Nat.dist_comm] using hf
  · have hijEq : j + (i - j) = i := by omega
    rw [Nat.dist_eq_sub_of_le_right hji]
    have hf := hforward j (i - j) (by omega)
    rw [hijEq] at hf
    exact hf

/-- Every fixed matching particle moves by at most `2*K` in one raw switch. -/
lemma matchingDegreeTrajectory_oneStep_le_two_mul_K
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error)
    (i : ℕ) (hi : i < nW) (x : Particle S) :
    Nat.dist
        (matchingDegreeTrajectory
          (rawPathOfUniformDegreeControlledOrderings Q) (i + 1) x)
        (matchingDegreeTrajectory
          (rawPathOfUniformDegreeControlledOrderings Q) i x) ≤
      2 * K := by
  simp only [matchingDegreeTrajectory]
  rw [rawPathOfUniformDegreeControlledOrderings_W_eq_state Q (i + 1) (by omega),
    rawPathOfUniformDegreeControlledOrderings_W_eq_state Q i hi.le]
  exact (SwitchingOrderings.degreeInto_state_succ_natDist_le
    G Q.toSwitchingOrderings i hi x.1).trans (by
      rw [S.matching_uniform x.1 x.2]
      exact Nat.mul_le_mul_left 2 S.k_le)

/-- Accumulated degree travel along the raw path. -/
lemma matchingDegreeTrajectory_natDist_le_two_mul_K_mul_timeDist
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error)
    (i j : ℕ) (hi : i ≤ nW) (hj : j ≤ nW) (x : Particle S) :
    Nat.dist
        (matchingDegreeTrajectory
          (rawPathOfUniformDegreeControlledOrderings Q) i x)
        (matchingDegreeTrajectory
          (rawPathOfUniformDegreeControlledOrderings Q) j x) ≤
      2 * K * Nat.dist i j := by
  exact natDist_le_step_mul_timeDist
    (fun r ↦ matchingDegreeTrajectory
      (rawPathOfUniformDegreeControlledOrderings Q) r x)
    (2 * K) nW i j
    (fun r hr ↦ matchingDegreeTrajectory_oneStep_le_two_mul_K Q r hr x) hi hj

/-- If two in-range times are at distance at most `stride`, every matching
particle travels by at most `2*K*stride`. -/
lemma matchingDegreeTrajectory_travel_le_two_mul_K_mul_stride
    {G : SimpleGraph V} {scale nW ell K stride : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error)
    (i j : ℕ) (hi : i ≤ nW) (hj : j ≤ nW)
    (hij : Nat.dist i j ≤ stride) (x : Particle S) :
    Nat.dist
        (matchingDegreeTrajectory
          (rawPathOfUniformDegreeControlledOrderings Q) i x)
        (matchingDegreeTrajectory
          (rawPathOfUniformDegreeControlledOrderings Q) j x) ≤
      2 * K * stride :=
  (matchingDegreeTrajectory_natDist_le_two_mul_K_mul_timeDist
    Q i j hi hj x).trans (Nat.mul_le_mul_left (2 * K) hij)

/-! ## The natural interval and canonical-schedule inputs -/

/-- The largest integer not exceeding the nonnegative lower endpoint of the
common concentration interval. -/
noncomputable def degreeIntervalBase
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error) (i : ℕ) : ℕ :=
  Nat.floor (max 0 (Q.expected i - error))

/-- Concentration about a common real center places all matching degrees in
one natural half-open interval.  The two extra units absorb both floor
rounding and strictness at the upper endpoint. -/
lemma degreeIntervalBase_le_and_lt_add
    {G : SimpleGraph V} {scale nW ell K span : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error)
    (herror : 0 ≤ error) (hspan : 2 * error + 2 ≤ (span : ℝ))
    (i : ℕ) (hi : i ≤ nW) (x : Finset V) (hx : x ∈ S.matching) :
    degreeIntervalBase Q i ≤
        degreeInto G ((rawPathOfUniformDegreeControlledOrderings Q).W i) x ∧
      degreeInto G ((rawPathOfUniformDegreeControlledOrderings Q).W i) x <
        degreeIntervalBase Q i + span := by
  let d : ℕ := degreeInto G
    ((rawPathOfUniformDegreeControlledOrderings Q).W i) x
  let a : ℝ := max 0 (Q.expected i - error)
  have hc := rawPathOfUniformDegreeControlledOrderings_degree_control Q i hi x hx
  rw [abs_le] at hc
  have ha0 : 0 ≤ a := by simp [a]
  have had : a ≤ (d : ℝ) := by
    apply max_le
    · positivity
    · dsimp [d]
      linarith [hc.1]
  have hfloor : ((Nat.floor a : ℕ) : ℝ) ≤ a := Nat.floor_le ha0
  have hlowerReal : ((Nat.floor a : ℕ) : ℝ) ≤ d := hfloor.trans had
  have hlower : Nat.floor a ≤ d := by exact_mod_cast hlowerReal
  have haFloor : a < ((Nat.floor a : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one a
  have hda : (d : ℝ) ≤ a + 2 * error := by
    have hmax : Q.expected i - error ≤ a := le_max_right _ _
    dsimp [d]
    linarith [hc.2]
  have hupperReal : (d : ℝ) < ((Nat.floor a : ℕ) : ℝ) + span := by
    exact lt_of_le_of_lt hda (by
      push_cast
      linarith)
  have hupper : d < Nat.floor a + span := by
    exact_mod_cast hupperReal
  simpa [degreeIntervalBase, a, d] using And.intro hlower hupper

/-- Convert a real absolute-difference bound between natural numbers to a
`Nat.dist` bound. -/
lemma natDist_le_of_abs_natCast_sub_le
    (m n spread : ℕ)
    (h : |(m : ℝ) - n| ≤ spread) : Nat.dist m n ≤ spread := by
  rcases le_total m n with hmn | hnm
  · have hreal : (n : ℝ) ≤ m + spread := by
      rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hmn))] at h
      push_cast at h ⊢
      linarith
    have hnat : n ≤ m + spread := by exact_mod_cast hreal
    rw [Nat.dist_eq_sub_of_le hmn]
    omega
  · have hreal : (m : ℝ) ≤ n + spread := by
      rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hnm))] at h
      push_cast at h ⊢
      linarith
    have hnat : m ≤ n + spread := by exact_mod_cast hreal
    rw [Nat.dist_eq_sub_of_le_right hnm]
    omega

/-- At one time, all matching particles lie within the ceiling of twice the
concentration error. -/
lemma matchingDegreeTrajectory_sameTime_le_ceil_two_mul_error
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error)
    (herror : 0 ≤ error) (i : ℕ) (hi : i ≤ nW) (x y : Particle S) :
    Nat.dist
        (matchingDegreeTrajectory
          (rawPathOfUniformDegreeControlledOrderings Q) i x)
        (matchingDegreeTrajectory
          (rawPathOfUniformDegreeControlledOrderings Q) i y) ≤
      Nat.ceil (2 * error) := by
  apply natDist_le_of_abs_natCast_sub_le
  have hreal := rawPathOfUniformDegreeControlledOrderings_degree_spread
    Q i hi x.1 y.1 x.2 y.2
  exact hreal.trans (Nat.le_ceil (2 * error))

/-- A local time below a canonical block's last coordinate maps to an
in-range global time. -/
lemma canonicalGlobalTime_le_of_le_blockLast
    {tau blockLength : ℕ}
    (q : Fin (Crowd.canonicalBlockCount tau blockLength))
    (t : ℕ) (ht : t ≤ Crowd.canonicalBlockLast tau blockLength q) :
    Crowd.canonicalGlobalTime blockLength q t ≤ tau := by
  rw [Crowd.canonicalBlockLast] at ht
  have ht' : t ≤ tau - (q : ℕ) * blockLength := ht.trans (min_le_right _ _)
  have hq : (q : ℕ) ≤ tau / blockLength := by
    have := q.isLt
    simp only [Crowd.canonicalBlockCount] at this
    omega
  have hqmul : (q : ℕ) * blockLength ≤ tau := by
    exact (Nat.mul_le_mul_right blockLength hq).trans
      (Nat.div_mul_le_self tau blockLength)
  rw [Crowd.canonicalGlobalTime]
  omega

/-- The inspection time preceding a local time is less than one stride away. -/
lemma canonicalGlobalTime_inspection_natDist_le_stride
    {tau blockLength stride : ℕ} (hstride : 0 < stride)
    (q : Fin (Crowd.canonicalBlockCount tau blockLength)) (t : ℕ) :
    Nat.dist (Crowd.canonicalGlobalTime blockLength q t)
      (Crowd.canonicalGlobalTime blockLength q ((t / stride) * stride)) ≤
        stride := by
  have hmul : (t / stride) * stride ≤ t := Nat.div_mul_le_self _ _
  have hmod : t % stride < stride := Nat.mod_lt _ hstride
  have hdecomp : (t / stride) * stride + t % stride = t := by
    simpa [Nat.mul_comm] using Nat.div_add_mod t stride
  have hglobal : Crowd.canonicalGlobalTime blockLength q ((t / stride) * stride) ≤
      Crowd.canonicalGlobalTime blockLength q t := by
    rw [Crowd.canonicalGlobalTime, Crowd.canonicalGlobalTime]
    exact Nat.add_le_add_left hmul _
  rw [Nat.dist_eq_sub_of_le_right hglobal]
  rw [Crowd.canonicalGlobalTime, Crowd.canonicalGlobalTime]
  rw [Nat.add_sub_add_left]
  omega

/-- Canonical block travel premise for `exists_scheduledCrowdedPath`. -/
lemma matchingDegreeTrajectory_canonical_travel
    {G : SimpleGraph V} {scale nW ell K blockLength stride : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error)
    (hstride : 0 < stride)
    (q : Fin (Crowd.canonicalBlockCount nW blockLength))
    (t : ℕ) (ht : t ≤ Crowd.canonicalBlockLast nW blockLength q)
    (x : Particle S) :
    Nat.dist
        (matchingDegreeTrajectory
          (rawPathOfUniformDegreeControlledOrderings Q)
          (Crowd.canonicalGlobalTime blockLength q t) x)
        (matchingDegreeTrajectory
          (rawPathOfUniformDegreeControlledOrderings Q)
          (Crowd.canonicalGlobalTime blockLength q ((t / stride) * stride)) x) ≤
      2 * K * stride := by
  apply matchingDegreeTrajectory_travel_le_two_mul_K_mul_stride Q
  · exact canonicalGlobalTime_le_of_le_blockLast q t ht
  · apply canonicalGlobalTime_le_of_le_blockLast q ((t / stride) * stride)
    exact (Nat.div_mul_le_self t stride).trans ht
  · exact canonicalGlobalTime_inspection_natDist_le_stride hstride q t

/-- Canonical inspection-time interval premise for
`exists_scheduledCrowdedPath`. -/
lemma degreeIntervalBase_canonical_controlled
    {G : SimpleGraph V} {scale nW ell K blockLength stride span : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error)
    (herror : 0 ≤ error) (hspan : 2 * error + 2 ≤ (span : ℝ))
    (q : Fin (Crowd.canonicalBlockCount nW blockLength))
    (j : ℕ) (hj : j * stride ≤ Crowd.canonicalBlockLast nW blockLength q)
    (x : Particle S) :
    degreeIntervalBase Q (Crowd.canonicalGlobalTime blockLength q (j * stride)) ≤
        matchingDegreeTrajectory (rawPathOfUniformDegreeControlledOrderings Q)
          (Crowd.canonicalGlobalTime blockLength q (j * stride)) x ∧
      matchingDegreeTrajectory (rawPathOfUniformDegreeControlledOrderings Q)
          (Crowd.canonicalGlobalTime blockLength q (j * stride)) x <
        degreeIntervalBase Q (Crowd.canonicalGlobalTime blockLength q (j * stride)) +
          span := by
  exact degreeIntervalBase_le_and_lt_add Q herror hspan _
    (canonicalGlobalTime_le_of_le_blockLast q (j * stride) hj) x.1 x.2

/-- Complete deterministic crowd-schedule bridge from one concentrated pair
of orderings.  Only the finite radius and pigeonhole inequalities remain as
premises. -/
theorem exists_scheduledCrowdedPath_of_uniformDegreeControlledOrderings
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error)
    (herror : 0 ≤ error)
    (blockLength span width threshold window stride : ℕ)
    (hblock : 0 < blockLength) (hspan : 2 * error + 2 ≤ (span : ℝ))
    (hwidth : 0 < width) (hstride : 0 < stride)
    (hradius : width + 2 * (2 * K * stride) ≤ window)
    (hcount : ∀ q : Fin (Crowd.canonicalBlockCount nW blockLength),
      (Crowd.canonicalBlockLast nW blockLength q / stride + 1) *
          Crowd.natBucketCount span width * threshold <
        Fintype.card (Particle S)) :
    Nonempty (ScheduledCrowdedPath S blockLength threshold window
      (2 * K) (Nat.ceil (2 * error))) := by
  let P := rawPathOfUniformDegreeControlledOrderings Q
  let base : Fin (Crowd.canonicalBlockCount nW blockLength) → ℕ → ℕ :=
    fun q j ↦ degreeIntervalBase Q
      (Crowd.canonicalGlobalTime blockLength q (j * stride))
  apply exists_scheduledCrowdedPath S P blockLength base
    span width threshold window stride (2 * K * stride)
      (2 * K) (Nat.ceil (2 * error)) hblock hwidth hstride
  · intro q j hj x
    exact degreeIntervalBase_canonical_controlled Q herror hspan q j hj x
  · intro q t ht x
    exact matchingDegreeTrajectory_canonical_travel Q hstride q t ht x
  · exact hradius
  · exact hcount
  · intro i hi x
    exact matchingDegreeTrajectory_oneStep_le_two_mul_K Q i hi x
  · intro i hi x y
    exact matchingDegreeTrajectory_sameTime_le_ceil_two_mul_error
      Q herror i hi x y

end

end OuterConcentrationPathBridge
end Erdos636
