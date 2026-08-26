import ErdosProblems.Erdos327.Analytic.MixedBoxAssembly

/-!
# Reduction of mixed edges to the main coordinate range

The standard mixed sieve box has `w ≤ 8X` on a dyadic range
`X ≤ u < 2X`.  The original coordinate theorem only gives `w ≤ 6u`.
This file removes the gap by splitting off edges with `a > 4b`.
The endpoint intervals permit at most one such edge.  Every remaining
edge has coordinates with `w ≤ 4u`, hence belongs to the standard box
on its dyadic `u`-scale.
-/

namespace Erdos327.Analytic

open Finset
open scoped ArithmeticFunction.Omega

noncomputable section

/-- The main part of a mixed-edge set, where the odd endpoint is at
most four times the source endpoint. -/
noncomputable def mixedMainEdges (O B : Finset ℕ) : Finset (ℕ × ℕ) :=
  (Erdos327.mixedEdges O B).filter fun e ↦ e.1 ≤ 4 * e.2

/-- The complementary exceptional mixed edges. -/
noncomputable def mixedExceptionalEdges
    (O B : Finset ℕ) : Finset (ℕ × ℕ) :=
  (Erdos327.mixedEdges O B).filter fun e ↦ ¬e.1 ≤ 4 * e.2

@[simp] theorem mem_mixedMainEdges
    {O B : Finset ℕ} {a b : ℕ} :
    (a, b) ∈ mixedMainEdges O B ↔
      (a, b) ∈ Erdos327.mixedEdges O B ∧ a ≤ 4 * b := by
  simp [mixedMainEdges]

@[simp] theorem mem_mixedExceptionalEdges
    {O B : Finset ℕ} {a b : ℕ} :
    (a, b) ∈ mixedExceptionalEdges O B ↔
      (a, b) ∈ Erdos327.mixedEdges O B ∧ 4 * b < a := by
  simp [mixedExceptionalEdges]

/-- The main and exceptional filters partition every mixed-edge set. -/
theorem card_mixedMainEdges_add_exceptional
    (O B : Finset ℕ) :
    (mixedMainEdges O B).card +
        (mixedExceptionalEdges O B).card =
      (Erdos327.mixedEdges O B).card := by
  classical
  exact Finset.card_filter_add_card_filter_not
    (s := Erdos327.mixedEdges O B) (fun e ↦ e.1 ≤ 4 * e.2)

/-- In the canonical endpoint intervals there is at most one edge with
`a > 4b`.  This is purely endpoint arithmetic: `a` is an odd member of
the first `N` positive odd integers and `b ≥ N/2`. -/
theorem card_canonical_mixedExceptionalEdges_le_one
    {L N : ℕ} {Ab Kb Ao Ko : ℝ} :
    (mixedExceptionalEdges
      (regularOddHost L Ao Ko N)
      (Erdos327.rankFilteredSource (Erdos327.upto N)
        (regularSource L Ab Kb N)
        ArithmeticFunction.cardFactors)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro e he f hf
  rcases e with ⟨a, b⟩
  rcases f with ⟨c, d⟩
  have heData := mem_mixedExceptionalEdges.mp he
  have hfData := mem_mixedExceptionalEdges.mp hf
  have heEdge := Erdos327.mem_mixedEdges.mp heData.1
  have hfEdge := Erdos327.mem_mixedEdges.mp hfData.1
  have haHost := (mem_regularOddHost.mp heEdge.1).1
  have hcHost := (mem_regularOddHost.mp hfEdge.1).1
  rcases mem_oddHost.mp haHost with ⟨ka, hkaN, hka⟩
  rcases mem_oddHost.mp hcHost with ⟨kc, hkcN, hkc⟩
  have hbRegular :
      b ∈ regularSource L Ab Kb N :=
    (Erdos327.mem_rankFilteredSource.mp heEdge.2.1).1
  have hdRegular :
      d ∈ regularSource L Ab Kb N :=
    (Erdos327.mem_rankFilteredSource.mp hfEdge.2.1).1
  have hbLower := (mem_regularSource.mp hbRegular).1
  have hdLower := (mem_regularSource.mp hdRegular).1
  apply Prod.ext
  · omega
  · omega

/-- Main mixed coordinates retain the useful inequality `w ≤ 4u`. -/
noncomputable def mixedMainCoordinateSet
    (L N : ℕ) (Ab Kb Ao Ko : ℝ) : Finset MixedTriple :=
  (mixedCoordinateSet L N Ab Kb Ao Ko).filter fun q ↦
    mixedW q ≤ 4 * mixedU q

@[simp] theorem mem_mixedMainCoordinateSet
    {L N : ℕ} {Ab Kb Ao Ko : ℝ} {q : MixedTriple} :
    q ∈ mixedMainCoordinateSet L N Ab Kb Ao Ko ↔
      q ∈ mixedCoordinateSet L N Ab Kb Ao Ko ∧
        mixedW q ≤ 4 * mixedU q := by
  simp [mixedMainCoordinateSet]

/-- The coordinate selected for a main edge belongs to the main
coordinate set and still recovers both endpoints. -/
theorem mixedMainCoordinate_of_edge
    {L N a b : ℕ} {Ab Kb Ao Ko : ℝ}
    (hL : 3 ≤ L) (hN : 2 ≤ N)
    (hedge :
      (a, b) ∈ mixedMainEdges
        (regularOddHost L Ao Ko N)
        (Erdos327.rankFilteredSource (Erdos327.upto N)
          (regularSource L Ab Kb N)
          ArithmeticFunction.cardFactors)) :
    ∃ q ∈ mixedMainCoordinateSet L N Ab Kb Ao Ko,
      mixedOddVertex q = a ∧ mixedSourceVertex q = b := by
  have hedgeData := mem_mixedMainEdges.mp hedge
  rcases mixedCoordinate_of_edge hL hN hedgeData.1 with
    ⟨q, hq, hqa, hqb⟩
  have hqData := hq
  rw [mixedCoordinateSet, mem_filter] at hqData
  rcases mem_product.mp hqData.1 with ⟨htuBox, hwBox⟩
  rcases mem_product.mp htuBox with ⟨htBox, huBox⟩
  have ht0 : 0 < mixedT q := (mem_Icc.mp htBox).1
  have hu0 : 0 < mixedU q := (mem_Icc.mp huBox).1
  have hw0 : 0 < mixedW q := (mem_Icc.mp hwBox).1
  have hx0 : 0 < mixedLinear q := by
    simp only [mixedLinear]
    omega
  have hscale0 : 0 < mixedT q * mixedLinear q :=
    Nat.mul_pos ht0 hx0
  have hscaled :
      (mixedT q * mixedLinear q) * mixedW q ≤
        (mixedT q * mixedLinear q) * (4 * mixedU q) := by
    calc
      (mixedT q * mixedLinear q) * mixedW q =
          mixedOddVertex q := by
        unfold mixedOddVertex
        ring
      _ = a := hqa
      _ ≤ 4 * b := hedgeData.2
      _ = (mixedT q * mixedLinear q) * (4 * mixedU q) := by
        rw [← hqb]
        unfold mixedSourceVertex
        ring
  have hw4u :
      mixedW q ≤ 4 * mixedU q :=
    Nat.le_of_mul_le_mul_left hscaled hscale0
  exact ⟨q, mem_mixedMainCoordinateSet.mpr ⟨hq, hw4u⟩,
    hqa, hqb⟩

/-- Main mixed edges inject into the main coordinate set. -/
theorem card_mixedMainEdges_le_mixedMainCoordinateSet
    {L N : ℕ} {Ab Kb Ao Ko : ℝ}
    (hL : 3 ≤ L) (hN : 2 ≤ N) :
    (mixedMainEdges
      (regularOddHost L Ao Ko N)
      (Erdos327.rankFilteredSource (Erdos327.upto N)
        (regularSource L Ab Kb N)
        ArithmeticFunction.cardFactors)).card ≤
      (mixedMainCoordinateSet L N Ab Kb Ao Ko).card := by
  classical
  let edges :=
    mixedMainEdges
      (regularOddHost L Ao Ko N)
      (Erdos327.rankFilteredSource (Erdos327.upto N)
        (regularSource L Ab Kb N)
        ArithmeticFunction.cardFactors)
  let f : (ℕ × ℕ) → MixedTriple := fun e ↦
    if he : e ∈ edges then
      Classical.choose (mixedMainCoordinate_of_edge hL hN he)
    else ((0, 0), 0)
  have hfData {e : ℕ × ℕ} (he : e ∈ edges) :
      f e ∈ mixedMainCoordinateSet L N Ab Kb Ao Ko ∧
        mixedOddVertex (f e) = e.1 ∧
        mixedSourceVertex (f e) = e.2 := by
    dsimp [f]
    rw [dif_pos he]
    exact Classical.choose_spec
      (mixedMainCoordinate_of_edge hL hN he)
  apply card_le_card_of_injOn f
  · intro e he
    exact (hfData he).1
  · intro e₁ he₁ e₂ he₂ heq
    have h₁ := (hfData he₁).2
    have h₂ := (hfData he₂).2
    apply Prod.ext
    · rw [← h₁.1, ← h₂.1, heq]
    · rw [← h₁.2, ← h₂.2, heq]

/-- The complete mixed-edge count is reduced to the main coordinate
count at the cost of one possible endpoint edge. -/
theorem card_mixedEdges_le_mixedMainCoordinateSet_add_one
    {L N : ℕ} {Ab Kb Ao Ko : ℝ}
    (hL : 3 ≤ L) (hN : 2 ≤ N) :
    (Erdos327.mixedEdges
      (regularOddHost L Ao Ko N)
      (Erdos327.rankFilteredSource (Erdos327.upto N)
        (regularSource L Ab Kb N)
        ArithmeticFunction.cardFactors)).card ≤
      (mixedMainCoordinateSet L N Ab Kb Ao Ko).card + 1 := by
  let O := regularOddHost L Ao Ko N
  let B :=
    Erdos327.rankFilteredSource (Erdos327.upto N)
      (regularSource L Ab Kb N)
      ArithmeticFunction.cardFactors
  have hsplit := card_mixedMainEdges_add_exceptional O B
  have hmain :=
    card_mixedMainEdges_le_mixedMainCoordinateSet
      (Ab := Ab) (Kb := Kb) (Ao := Ao) (Ko := Ko) hL hN
  have hexceptional :=
    card_canonical_mixedExceptionalEdges_le_one
      (L := L) (N := N) (Ab := Ab) (Kb := Kb)
      (Ao := Ao) (Ko := Ko)
  dsimp [O, B] at hsplit
  calc
    (Erdos327.mixedEdges
        (regularOddHost L Ao Ko N)
        (Erdos327.rankFilteredSource (Erdos327.upto N)
          (regularSource L Ab Kb N)
          ArithmeticFunction.cardFactors)).card =
        (mixedMainEdges
          (regularOddHost L Ao Ko N)
          (Erdos327.rankFilteredSource (Erdos327.upto N)
            (regularSource L Ab Kb N)
            ArithmeticFunction.cardFactors)).card +
        (mixedExceptionalEdges
          (regularOddHost L Ao Ko N)
          (Erdos327.rankFilteredSource (Erdos327.upto N)
            (regularSource L Ab Kb N)
            ArithmeticFunction.cardFactors)).card := hsplit.symm
    _ ≤ (mixedMainCoordinateSet L N Ab Kb Ao Ko).card + 1 :=
      Nat.add_le_add hmain hexceptional

/-- The `u`-dyadic part of the main coordinate set. -/
noncomputable def mixedMainCoordinateDyadicBlock
    (L N : ℕ) (Ab Kb Ao Ko : ℝ) (X : ℕ) : Finset MixedTriple :=
  (mixedMainCoordinateSet L N Ab Kb Ao Ko).filter fun q ↦
    mixedU q ∈ Ico X (2 * X)

@[simp] theorem mem_mixedMainCoordinateDyadicBlock
    {L N X : ℕ} {Ab Kb Ao Ko : ℝ} {q : MixedTriple} :
    q ∈ mixedMainCoordinateDyadicBlock L N Ab Kb Ao Ko X ↔
      q ∈ mixedMainCoordinateSet L N Ab Kb Ao Ko ∧
        mixedU q ∈ Ico X (2 * X) := by
  simp [mixedMainCoordinateDyadicBlock]

/-- Every main dyadic block is contained in the standard analytic box:
`w ≤ 4u` and `u < 2X` give `w < 8X`. -/
theorem mixedMainCoordinateDyadicBlock_subset_box
    {L N X : ℕ} {Ab Kb Ao Ko : ℝ} :
    mixedMainCoordinateDyadicBlock L N Ab Kb Ao Ko X ⊆
      mixedCoordinateBoxBlock L N Ab Kb Ao Ko X := by
  intro q hq
  have hmem := mem_mixedMainCoordinateDyadicBlock.mp hq
  have hmain := mem_mixedMainCoordinateSet.mp hmem.1
  have huBox := mem_Ico.mp hmem.2
  have hqData := hmain.1
  rw [mixedCoordinateSet, mem_filter] at hqData
  rcases mem_product.mp hqData.1 with ⟨_htuBox, hwBox⟩
  have hwLower := (mem_Icc.mp hwBox).1
  apply mem_mixedCoordinateBoxBlock.mpr
  refine ⟨hmain.1, hmem.2, mem_Icc.mpr ⟨hwLower, ?_⟩⟩
  omega

/-- Every main coordinate lies in a standard box at its binary dyadic
`u`-scale. -/
theorem mixedMainCoordinate_exists_dyadic_box
    {L N : ℕ} {Ab Kb Ao Ko : ℝ} {q : MixedTriple}
    (hq : q ∈ mixedMainCoordinateSet L N Ab Kb Ao Ko) :
    ∃ k : ℕ,
      q ∈ mixedCoordinateBoxBlock
        L N Ab Kb Ao Ko (2 ^ k) := by
  have hmain := mem_mixedMainCoordinateSet.mp hq
  have hqData := hmain.1
  rw [mixedCoordinateSet, mem_filter] at hqData
  rcases mem_product.mp hqData.1 with ⟨htuBox, _hwBox⟩
  have huLower :=
    (mem_Icc.mp (mem_product.mp htuBox).2).1
  let k := Nat.log 2 (mixedU q)
  have hu0 : mixedU q ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp huLower
  have hlower :
      2 ^ k ≤ mixedU q := by
    dsimp [k]
    exact Nat.pow_log_le_self 2 hu0
  have hupper :
      mixedU q < 2 * (2 ^ k) := by
    have h :=
      Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ))
        (mixedU q)
    dsimp [k]
    simpa [pow_succ, mul_comm] using h
  refine ⟨k, ?_⟩
  apply mixedMainCoordinateDyadicBlock_subset_box
  exact mem_mixedMainCoordinateDyadicBlock.mpr
    ⟨hq, mem_Ico.mpr ⟨hlower, hupper⟩⟩

end

end Erdos327.Analytic
