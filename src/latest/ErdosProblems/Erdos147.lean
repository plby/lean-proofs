/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 147.
https://www.erdosproblems.com/forum/thread/147

Informal authors:
- Oliver Janzer

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos147.md
-/
import ErdosProblems.Erdos147.Regularization

open Filter
open Asymptotics
open scoped SimpleGraph Topology

namespace Erdos147

set_option autoImplicit false

lemma degreeFiber_seventh_power_bound_of_order
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : ℕ) (hb : 1 < b)
    (hdegree : ∀ p : OrderedPair V, (pairAuxGraph G).degree p < b ^ 200)
    (i j : Fin 200)
    (hlarge : (directedEdgeFinset (pairAuxGraph G)).card ≤
      40000 * (relEdgeFinset
        (degreeBinRel (pairAuxGraph G) b hdegree i j)).card)
    (horder : b ^ (i.1 + 1) ≤ b ^ (j.1 + 1))
    (hfree : counterexampleGraph.Free G) :
    ((directedEdgeFinset (pairAuxGraph G)).card : ℝ) ^ 7 ≤
      auxiliarySeventhPowerConstant *
        (Fintype.card (OrderedPair V) : ℝ) ^ 9 * (b : ℝ) ^ 24 := by
  classical
  let A := pairAuxGraph G
  let L₀ := DegreeBin200 A b hdegree i
  let R₀ := DegreeBin200 A b hdegree j
  let B₀ : L₀ → R₀ → Prop := degreeBinRel A b hdegree i j
  let q : ℝ := (directedEdgeFinset A).card
  let e : ℝ := (relEdgeFinset B₀).card
  let N : ℝ := Fintype.card (OrderedPair V)
  let D₁ : ℝ := b ^ (i.1 + 1)
  let D₂ : ℝ := b ^ (j.1 + 1)
  change q ^ 7 ≤ auxiliarySeventhPowerConstant * N ^ 9 * (b : ℝ) ^ 24
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (lt_trans (by omega : 0 < 1) hb)
  have hN0 : 0 ≤ N := by positivity
  have hD₁ : 0 < D₁ := by positivity
  have hD₂ : 0 < D₂ := by positivity
  have hDord : D₁ ≤ D₂ := by
    dsimp [D₁, D₂]
    exact_mod_cast horder
  have hlargeR : q ≤ 40000 * e := by
    dsimp [q, e, A, B₀, L₀, R₀]
    exact_mod_cast hlarge
  by_cases hqzero : q = 0
  · have hconst : 0 ≤ auxiliarySeventhPowerConstant := by
      dsimp [auxiliarySeventhPowerConstant]
      positivity
    calc
      q ^ 7 = 0 := by rw [hqzero]; norm_num
      _ ≤ auxiliarySeventhPowerConstant * N ^ 9 * (b : ℝ) ^ 24 :=
        mul_nonneg (mul_nonneg hconst (pow_nonneg hN0 9))
          (pow_nonneg hb0.le 24)
  have hq : 0 < q := lt_of_le_of_ne (by positivity) (Ne.symm hqzero)
  have he : 0 < e := by nlinarith
  have hB₀nonempty : (relEdgeFinset B₀).Nonempty := by
    apply Finset.card_pos.mp
    dsimp [e] at he
    exact_mod_cast he
  obtain ⟨S, T, hS, hT, hcoreL, hcoreR⟩ :=
    exists_twoSided_relCore B₀ hB₀nonempty
  let B : CoreLeft S → CoreRight T → Prop := coreRel B₀ S T
  let fL : CoreLeft S → OrderedPair V := fun l ↦ l.1.1
  let fR : CoreRight T → OrderedPair V := fun r ↦ r.1.1
  have hfL : Function.Injective fL := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hfR : Function.Injective fR := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hmap : ∀ l r, B l r → pairComplete G (fL l) (fR r) := by
    intro l r hlr
    exact hlr
  have hcardLpos : (0 : ℝ) < Fintype.card L₀ := by
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty L₀ from ⟨hS.choose⟩)
  have hcardRpos : (0 : ℝ) < Fintype.card R₀ := by
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty R₀ from ⟨hT.choose⟩)
  have hbinL := degreeBin_card_mul_lower_le_directedEdge_card A b hdegree i
  have hbinR := degreeBin_card_mul_lower_le_directedEdge_card A b hdegree j
  have hbinLR :
      (Fintype.card L₀ : ℝ) * D₁ ≤ (b : ℝ) * q := by
    have hnat : Fintype.card L₀ * b ^ i.1 ≤ (directedEdgeFinset A).card := by
      simpa [L₀] using hbinL
    have hreal : (Fintype.card L₀ : ℝ) * (b : ℝ) ^ i.1 ≤ q := by
      dsimp [q]
      exact_mod_cast hnat
    have h := mul_le_mul_of_nonneg_left hreal (Nat.cast_nonneg b)
    calc
      (Fintype.card L₀ : ℝ) * D₁ =
          (b : ℝ) * ((Fintype.card L₀ : ℝ) * (b : ℝ) ^ i.1) := by
        dsimp [D₁]
        rw [pow_succ]
        ring
      _ ≤ (b : ℝ) * q := h
  have hbinRR :
      (Fintype.card R₀ : ℝ) * D₂ ≤ (b : ℝ) * q := by
    have hnat : Fintype.card R₀ * b ^ j.1 ≤ (directedEdgeFinset A).card := by
      simpa [R₀] using hbinR
    have hreal : (Fintype.card R₀ : ℝ) * (b : ℝ) ^ j.1 ≤ q := by
      dsimp [q]
      exact_mod_cast hnat
    have h := mul_le_mul_of_nonneg_left hreal (Nat.cast_nonneg b)
    calc
      (Fintype.card R₀ : ℝ) * D₂ =
          (b : ℝ) * ((Fintype.card R₀ : ℝ) * (b : ℝ) ^ j.1) := by
        dsimp [D₂]
        rw [pow_succ]
        ring
      _ ≤ (b : ℝ) * q := h
  have hminL (l : CoreLeft S) :
      D₁ / (160000 * (b : ℝ)) ≤ relLeftDegreeReal B l := by
    have hc : e ≤ 4 * Fintype.card L₀ * restrictedLeftDegree B₀ T l.1 := by
      dsimp [e]
      exact_mod_cast hcoreL l.1 l.2
    have h₁ := mul_le_mul_of_nonneg_left hlargeR (Nat.cast_nonneg b)
    have h₂ := mul_le_mul_of_nonneg_left hc
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 40000) (Nat.cast_nonneg b))
    have hcross : D₁ ≤
        160000 * (b : ℝ) * restrictedLeftDegree B₀ T l.1 := by
      have : (Fintype.card L₀ : ℝ) * D₁ ≤
          (Fintype.card L₀ : ℝ) *
            (160000 * (b : ℝ) * restrictedLeftDegree B₀ T l.1) := by
        calc
          (Fintype.card L₀ : ℝ) * D₁ ≤ (b : ℝ) * q := hbinLR
          _ ≤ (b : ℝ) * (40000 * e) := h₁
          _ ≤ (Fintype.card L₀ : ℝ) *
              (160000 * (b : ℝ) * restrictedLeftDegree B₀ T l.1) := by
            nlinarith [h₂]
      nlinarith
    rw [relLeftDegreeReal_coreRel B₀ S T l]
    exact (div_le_iff₀ (mul_pos (by norm_num) hb0)).2 (by nlinarith)
  have hminR (r : CoreRight T) :
      D₂ / (160000 * (b : ℝ)) ≤
        relLeftDegreeReal (fun r l ↦ B l r) r := by
    have hc : e ≤ 4 * Fintype.card R₀ * restrictedRightDegree B₀ S r.1 := by
      dsimp [e]
      exact_mod_cast hcoreR r.1 r.2
    have h₁ := mul_le_mul_of_nonneg_left hlargeR (Nat.cast_nonneg b)
    have h₂ := mul_le_mul_of_nonneg_left hc
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 40000) (Nat.cast_nonneg b))
    have hcross : D₂ ≤
        160000 * (b : ℝ) * restrictedRightDegree B₀ S r.1 := by
      have : (Fintype.card R₀ : ℝ) * D₂ ≤
          (Fintype.card R₀ : ℝ) *
            (160000 * (b : ℝ) * restrictedRightDegree B₀ S r.1) := by
        calc
          (Fintype.card R₀ : ℝ) * D₂ ≤ (b : ℝ) * q := hbinRR
          _ ≤ (b : ℝ) * (40000 * e) := h₁
          _ ≤ (Fintype.card R₀ : ℝ) *
              (160000 * (b : ℝ) * restrictedRightDegree B₀ S r.1) := by
            nlinarith [h₂]
      nlinarith
    rw [relRightDegreeReal_coreRel B₀ S T r]
    exact (div_le_iff₀ (mul_pos (by norm_num) hb0)).2 (by nlinarith)
  have hmaxL (l : CoreLeft S) : relLeftDegreeReal B l ≤ D₁ := by
    calc
      relLeftDegreeReal B l ≤ A.degree (fL l) :=
        relLeftDegreeReal_le_auxDegree G B fL fR hfR hmap l
      _ ≤ D₁ := by
        have hu := (degreeIndex200_upper A b hb hdegree (fL l)).le
        rw [l.1.2.1] at hu
        dsimp [D₁]
        exact_mod_cast hu
  have hmaxR (r : CoreRight T) :
      relLeftDegreeReal (fun r l ↦ B l r) r ≤ D₂ := by
    calc
      relLeftDegreeReal (fun r l ↦ B l r) r ≤ A.degree (fR r) :=
        relLeftDegreeReal_le_auxDegree G (fun r l ↦ B l r) fR fL hfL
          (fun r l h ↦ (pairComplete_comm G _ _).mpr (hmap l r h)) r
      _ ≤ D₂ := by
        have hu := (degreeIndex200_upper A b hb hdegree (fR r)).le
        rw [r.1.2.1] at hu
        dsimp [D₂]
        exact_mod_cast hu
  let C := pairSupportConflictVia fL fR
  have hconfL (u : CoreLeft S ⊕ CoreRight T) (r : CoreRight T) :
      leftConflictDegreeReal B C u r ≤ 8 * Real.sqrt D₂ := by
    have hlocal := leftConflictDegreeReal_le_auxConflict G B fL fR hfL hmap u r
    have hdeg : (A.degree (fR r) : ℝ) ≤ D₂ := by
      have hu := (degreeIndex200_upper A b hb hdegree (fR r)).le
      rw [r.1.2.1] at hu
      dsimp [D₂]
      exact_mod_cast hu
    have hsqrt := Real.sqrt_le_sqrt hdeg
    have hone : (1 : ℝ) ≤ Real.sqrt D₂ := by
      rw [Real.one_le_sqrt]
      dsimp [D₂]
      exact one_le_pow₀ (by exact_mod_cast (le_of_lt hb))
    nlinarith
  have hconfR (u : CoreRight T ⊕ CoreLeft S) (l : CoreLeft S) :
      leftConflictDegreeReal (fun r l ↦ B l r) (swapConflict C) u l ≤
        8 * Real.sqrt D₁ := by
    have hlocal := leftConflictDegreeReal_le_auxConflict G
      (fun r l ↦ B l r) fR fL hfR
      (fun r l h ↦ (pairComplete_comm G _ _).mpr (hmap l r h)) u l
    have hswap : ∀ x y,
        swapConflict C x y ↔ pairSupportConflictVia fR fL x y := by
      rintro (r | l') (r' | l'') <;>
        simp [C, swapConflict, pairSupportConflictVia, sumPairMap]
    have heq :
        leftConflictDegreeReal (fun r l ↦ B l r) (swapConflict C) u l =
          leftConflictDegreeReal (fun r l ↦ B l r)
            (pairSupportConflictVia fR fL) u l := by
      simp only [leftConflictDegreeReal]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hB : B l r
      · by_cases hC : swapConflict C (Sum.inl r) u
        · have hC' := (hswap (Sum.inl r) u).mp hC
          simp [hB, hC, hC']
        · have hC' : ¬pairSupportConflictVia fR fL (Sum.inl r) u :=
            fun h ↦ hC ((hswap (Sum.inl r) u).mpr h)
          simp [hB, hC, hC']
      · simp [hB]
    rw [heq]
    have hdeg : (A.degree (fL l) : ℝ) ≤ D₁ := by
      have hu := (degreeIndex200_upper A b hb hdegree (fL l)).le
      rw [l.1.2.1] at hu
      dsimp [D₁]
      exact_mod_cast hu
    have hsqrt := Real.sqrt_le_sqrt hdeg
    have hone : (1 : ℝ) ≤ Real.sqrt D₁ := by
      rw [Real.one_le_sqrt]
      dsimp [D₁]
      exact one_le_pow₀ (by exact_mod_cast (le_of_lt hb))
    nlinarith
  have hall (w : ClosedWalk (bipartiteRelGraph B) 12) :
      ∃ a c : Fin 12, a ≠ c ∧ C (w.2.1.getVert a.1) (w.2.1.getVert c.1) :=
    all_closedWalks_conflicting_of_free G B fL fR hmap hfree w
  have hcycle := homCycleCount_twelve_le_of_all_conflicting B C
    (pairSupportConflictVia_symm fL fR) D₁ D₂
    (8 * Real.sqrt D₂) (8 * Real.sqrt D₁) hD₁ hD₂
    (by positivity) (by positivity) hDord hmaxL hmaxR hconfL hconfR
    le_rfl le_rfl hall
  let K : ℝ := 16000000 * (D₂ * Real.sqrt D₁)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcycle₂ := homCycleCount_twelve_le_two_of_ten_bound
    (bipartiteRelGraph B) K hK (by simpa [K] using hcycle)
  have hLnonempty : Nonempty (CoreLeft S) := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  have hlower := homCycleCount_twelve_lower_of_minDegrees B
    (D₁ / (160000 * (b : ℝ))) (D₂ / (160000 * (b : ℝ)))
    (by positivity) (by positivity) hminL hminR
  have hcoreEdge :
      ((relEdgeFinset B).card : ℝ) ≤ N * D₁ := by
    have hsub := relEdgeFinset_coreRel_card_le B₀ S T
    have hupper := degreeBinRel_edge_card_le_card_mul_upper A b hb hdegree i j
    have hcardLN : (Fintype.card L₀ : ℝ) ≤ N := by
      dsimp [N]
      exact_mod_cast Fintype.card_le_of_injective (fun l : L₀ ↦ l.1)
        (fun _ _ h ↦ Subtype.ext h)
    calc
      ((relEdgeFinset B).card : ℝ) ≤ (relEdgeFinset B₀).card := by
        exact_mod_cast hsub
      _ ≤ (Fintype.card L₀ : ℝ) * D₁ := by
        dsimp [B₀, L₀, D₁, A]
        exact_mod_cast hupper
      _ ≤ N * D₁ := mul_le_mul_of_nonneg_right hcardLN hD₁.le
  have htwo : homCycleCount (bipartiteRelGraph B) 2 ≤ 2 * N * D₁ := by
    rw [homCycleCount_bipartiteRel_two B]
    nlinarith
  have hcombined :
      ((D₁ / (160000 * (b : ℝ))) *
        (D₂ / (160000 * (b : ℝ)))) ^ 6 ≤
        K ^ 5 * (2 * N * D₁) :=
    hlower.trans (hcycle₂.trans (mul_le_mul_of_nonneg_left htwo (pow_nonneg hK 5)))
  let x := Real.sqrt D₁
  have hx : 0 < x := Real.sqrt_pos.2 hD₁
  have hx2 : x ^ 2 = D₁ := Real.sq_sqrt hD₁.le
  let M : ℝ := 2 * 160000 ^ 12 * 16000000 ^ 5
  have hM0 : 0 ≤ M := by dsimp [M]; positivity
  have hpoly : x ^ 12 * D₂ ^ 6 ≤ M * N * (b : ℝ) ^ 12 * x ^ 7 * D₂ ^ 5 := by
    have hden : 0 < (160000 * (b : ℝ)) ^ 12 := by positivity
    have hcross : (D₁ * D₂) ^ 6 ≤
        (K ^ 5 * (2 * N * D₁)) * (160000 * (b : ℝ)) ^ 12 := by
      have heq :
          ((D₁ / (160000 * (b : ℝ))) *
            (D₂ / (160000 * (b : ℝ)))) ^ 6 =
            (D₁ * D₂) ^ 6 / (160000 * (b : ℝ)) ^ 12 := by
        field_simp
      rw [heq] at hcombined
      exact (div_le_iff₀ hden).mp hcombined
    dsimp [K, M] at hcross ⊢
    rw [← hx2] at hcross
    rw [Real.sqrt_sq hx.le] at hcross
    convert hcross using 1 <;> ring
  have hxD : x ^ 7 ≤ M * N * (b : ℝ) ^ 12 := by
    have hfactor : 0 < x ^ 7 * D₂ ^ 5 := mul_pos (pow_pos hx 7) (pow_pos hD₂ 5)
    have hcancel : x ^ 5 * D₂ ≤ M * N * (b : ℝ) ^ 12 := by
      by_contra hn
      have hlt := mul_lt_mul_of_pos_right (lt_of_not_ge hn) hfactor
      apply (not_lt_of_ge hpoly)
      convert hlt using 1 <;> ring
    have hxd2 : x ^ 2 ≤ D₂ := by rw [hx2]; exact hDord
    calc
      x ^ 7 = x ^ 5 * x ^ 2 := by ring
      _ ≤ x ^ 5 * D₂ := mul_le_mul_of_nonneg_left hxd2 (pow_nonneg hx.le 5)
      _ ≤ M * N * (b : ℝ) ^ 12 := hcancel
  have hDpow : D₁ ^ 7 ≤ M ^ 2 * N ^ 2 * (b : ℝ) ^ 24 := by
    have hsquare := pow_le_pow_left₀ (by positivity) hxD 2
    rw [← hx2]
    calc
      (x ^ 2) ^ 7 = (x ^ 7) ^ 2 := by ring
      _ ≤ (M * N * (b : ℝ) ^ 12) ^ 2 := hsquare
      _ = M ^ 2 * N ^ 2 * (b : ℝ) ^ 24 := by ring
  have hqD : q ≤ 40000 * N * D₁ := by
    have hupper := degreeBinRel_edge_card_le_card_mul_upper A b hb hdegree i j
    have hcardLN : (Fintype.card L₀ : ℝ) ≤ N := by
      dsimp [N]
      exact_mod_cast Fintype.card_le_of_injective (fun l : L₀ ↦ l.1)
        (fun _ _ h ↦ Subtype.ext h)
    calc
      q ≤ 40000 * e := hlargeR
      _ ≤ 40000 * ((Fintype.card L₀ : ℝ) * D₁) := by
        gcongr
        dsimp [e, B₀, L₀, D₁, A]
        exact_mod_cast hupper
      _ ≤ 40000 * (N * D₁) := by gcongr
      _ = 40000 * N * D₁ := by ring
  have hqpow := pow_le_pow_left₀ (by positivity : 0 ≤ q) hqD 7
  calc
    q ^ 7 ≤ (40000 * N * D₁) ^ 7 := hqpow
    _ = 40000 ^ 7 * N ^ 7 * D₁ ^ 7 := by ring
    _ ≤ 40000 ^ 7 * N ^ 7 * (M ^ 2 * N ^ 2 * (b : ℝ) ^ 24) := by
      gcongr
    _ = auxiliarySeventhPowerConstant * N ^ 9 * (b : ℝ) ^ 24 := by
      dsimp [auxiliarySeventhPowerConstant, M]
      ring

lemma degreeBinRel_swap_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : ℕ)
    (hdegree : ∀ v, G.degree v < b ^ 200) (i j : Fin 200) :
    (relEdgeFinset (degreeBinRel G b hdegree i j)).card =
      (relEdgeFinset (degreeBinRel G b hdegree j i)).card := by
  classical
  apply Finset.card_bij (fun e _ ↦ (e.2, e.1))
  · intro e he
    rw [mem_relEdgeFinset]
    exact ((mem_relEdgeFinset (degreeBinRel G b hdegree i j) e.1 e.2).mp he).symm
  · intro e₁ h₁ e₂ h₂ h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · intro e he
    refine ⟨(e.2, e.1), ?_, rfl⟩
    rw [mem_relEdgeFinset]
    exact ((mem_relEdgeFinset (degreeBinRel G b hdegree j i) e.1 e.2).mp he).symm

lemma pairAuxGraph_seventh_power_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : ℕ) (hb : 1 < b)
    (hdegree : ∀ p : OrderedPair V, (pairAuxGraph G).degree p < b ^ 200)
    (hfree : counterexampleGraph.Free G) :
    ((directedEdgeFinset (pairAuxGraph G)).card : ℝ) ^ 7 ≤
      auxiliarySeventhPowerConstant *
        (Fintype.card (OrderedPair V) : ℝ) ^ 9 * (b : ℝ) ^ 24 := by
  obtain ⟨⟨i, j⟩, hlarge⟩ :=
    exists_large_degreeEdgeFiber (pairAuxGraph G) b hdegree
  have hlarge' : (directedEdgeFinset (pairAuxGraph G)).card ≤
      40000 * (relEdgeFinset
        (degreeBinRel (pairAuxGraph G) b hdegree i j)).card := by
    simpa [degreeEdgeFiber_card_eq_rel] using hlarge
  by_cases hord : b ^ (i.1 + 1) ≤ b ^ (j.1 + 1)
  · exact degreeFiber_seventh_power_bound_of_order G b hb hdegree i j
      hlarge' hord hfree
  · have hord' : b ^ (j.1 + 1) ≤ b ^ (i.1 + 1) := le_of_lt (lt_of_not_ge hord)
    have hlarge'' : (directedEdgeFinset (pairAuxGraph G)).card ≤
        40000 * (relEdgeFinset
          (degreeBinRel (pairAuxGraph G) b hdegree j i)).card := by
      rw [← degreeBinRel_swap_card (pairAuxGraph G) b hdegree i j]
      exact hlarge'
    exact degreeFiber_seventh_power_bound_of_order G b hb hdegree j i
      hlarge'' hord' hfree

def orderedRectangleFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset ((V × V) × (V × V)) :=
  Finset.univ.filter fun z ↦
    z.1.1 ≠ z.1.2 ∧ z.2.1 ≠ z.2.2 ∧
      G.Adj z.1.1 z.2.1 ∧ G.Adj z.1.2 z.2.1 ∧
      G.Adj z.1.1 z.2.2 ∧ G.Adj z.1.2 z.2.2

@[simp] lemma mem_orderedRectangleFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : (V × V) × (V × V)) :
    z ∈ orderedRectangleFinset G ↔
      z.1.1 ≠ z.1.2 ∧ z.2.1 ≠ z.2.2 ∧
        G.Adj z.1.1 z.2.1 ∧ G.Adj z.1.2 z.2.1 ∧
        G.Adj z.1.1 z.2.2 ∧ G.Adj z.1.2 z.2.2 := by
  simp [orderedRectangleFinset]

lemma colored_rectangleCount_eq_orderedRectangleFinset_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Erdos888.ColoredGraph.rectangleCount (fun x y ↦ G.Adj x y) =
      (orderedRectangleFinset G).card := by
  classical
  rw [Erdos888.ColoredGraph.rectangleCount_eq_sum_indicator]
  have hind (x x' y y' : V) :
      Erdos888.ColoredGraph.rectangleIndicator (fun a b ↦ G.Adj a b) x x' y y' =
        if x ≠ x' ∧ y ≠ y' ∧ G.Adj x y ∧ G.Adj x' y ∧
          G.Adj x y' ∧ G.Adj x' y' then 1 else 0 := by
    by_cases h : x ≠ x' ∧ y ≠ y' ∧ G.Adj x y ∧ G.Adj x' y ∧
        G.Adj x y' ∧ G.Adj x' y'
    · simp [Erdos888.ColoredGraph.rectangleIndicator,
        Erdos888.ColoredGraph.ContainsRectangle, h]
    · simp [Erdos888.ColoredGraph.rectangleIndicator,
        Erdos888.ColoredGraph.ContainsRectangle, h]
  simp_rw [hind]
  have hprod :
      (∑ x : V, ∑ x' : V, ∑ y : V, ∑ y' : V,
        if x ≠ x' ∧ y ≠ y' ∧ G.Adj x y ∧ G.Adj x' y ∧
          G.Adj x y' ∧ G.Adj x' y' then (1 : ℝ) else 0) =
      ∑ z : (V × V) × (V × V),
        if z.1.1 ≠ z.1.2 ∧ z.2.1 ≠ z.2.2 ∧
          G.Adj z.1.1 z.2.1 ∧ G.Adj z.1.2 z.2.1 ∧
          G.Adj z.1.1 z.2.2 ∧ G.Adj z.1.2 z.2.2 then (1 : ℝ) else 0 := by
    calc
      (∑ x : V, ∑ x' : V, ∑ y : V, ∑ y' : V,
          if x ≠ x' ∧ y ≠ y' ∧ G.Adj x y ∧ G.Adj x' y ∧
            G.Adj x y' ∧ G.Adj x' y' then (1 : ℝ) else 0) =
          ∑ p : V × V, ∑ y : V, ∑ y' : V,
            if p.1 ≠ p.2 ∧ y ≠ y' ∧ G.Adj p.1 y ∧ G.Adj p.2 y ∧
              G.Adj p.1 y' ∧ G.Adj p.2 y' then (1 : ℝ) else 0 :=
        (Fintype.sum_prod_type (fun p : V × V ↦
          ∑ y : V, ∑ y' : V,
            if p.1 ≠ p.2 ∧ y ≠ y' ∧ G.Adj p.1 y ∧ G.Adj p.2 y ∧
              G.Adj p.1 y' ∧ G.Adj p.2 y' then (1 : ℝ) else 0)).symm
      _ = ∑ p : V × V, ∑ q : V × V,
            if p.1 ≠ p.2 ∧ q.1 ≠ q.2 ∧ G.Adj p.1 q.1 ∧ G.Adj p.2 q.1 ∧
              G.Adj p.1 q.2 ∧ G.Adj p.2 q.2 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        exact (Fintype.sum_prod_type (fun q : V × V ↦
          if p.1 ≠ p.2 ∧ q.1 ≠ q.2 ∧ G.Adj p.1 q.1 ∧ G.Adj p.2 q.1 ∧
            G.Adj p.1 q.2 ∧ G.Adj p.2 q.2 then (1 : ℝ) else 0)).symm
      _ = _ :=
        (Fintype.sum_prod_type (fun z : (V × V) × (V × V) ↦
          if z.1.1 ≠ z.1.2 ∧ z.2.1 ≠ z.2.2 ∧
            G.Adj z.1.1 z.2.1 ∧ G.Adj z.1.2 z.2.1 ∧
            G.Adj z.1.1 z.2.2 ∧ G.Adj z.1.2 z.2.2 then (1 : ℝ) else 0)).symm
  rw [hprod]
  rw [orderedRectangleFinset]
  exact Finset.sum_boole (R := ℝ) (fun z : (V × V) × (V × V) ↦
    z.1.1 ≠ z.1.2 ∧ z.2.1 ≠ z.2.2 ∧
      G.Adj z.1.1 z.2.1 ∧ G.Adj z.1.2 z.2.1 ∧
      G.Adj z.1.1 z.2.2 ∧ G.Adj z.1.2 z.2.2) Finset.univ

lemma orderedRectangleFinset_card_eq_pairAux_directedEdge_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (orderedRectangleFinset G).card =
      (directedEdgeFinset (pairAuxGraph G)).card := by
  classical
  apply Finset.card_bij (fun z hz ↦
    (⟨z.1, ((mem_orderedRectangleFinset G z).mp hz).1⟩,
      ⟨z.2, ((mem_orderedRectangleFinset G z).mp hz).2.1⟩))
  · intro z hz
    rw [mem_directedEdgeFinset]
    have h := ((mem_orderedRectangleFinset G z).mp hz).2.2
    exact ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩
  · intro z₁ h₁ z₂ h₂ h
    exact Prod.ext (congrArg (fun e ↦ e.1.1) h) (congrArg (fun e ↦ e.2.1) h)
  · intro e he
    refine ⟨(e.1.1, e.2.1), ?_, rfl⟩
    have hadj := (mem_directedEdgeFinset (pairAuxGraph G) e.1 e.2).mp he
    exact (mem_orderedRectangleFinset G _).mpr
      ⟨e.1.2, e.2.2, hadj.1, hadj.2.2.1, hadj.2.1, hadj.2.2.2⟩

lemma colored_rectangleCount_eq_pairAux_directedEdge_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Erdos888.ColoredGraph.rectangleCount (fun x y ↦ G.Adj x y) =
      (directedEdgeFinset (pairAuxGraph G)).card := by
  rw [colored_rectangleCount_eq_orderedRectangleFinset_card,
    orderedRectangleFinset_card_eq_pairAux_directedEdge_card]

lemma colored_edgeCount_eq_twice_card_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Erdos888.ColoredGraph.edgeCount (fun x y ↦ G.Adj x y) =
      2 * (G.edgeFinset.card : ℝ) := by
  rw [Erdos888.ColoredGraph.edgeCount_eq_card_edgeFinset]
  simp only [Erdos888.ColoredGraph.edgeFinset]
  norm_cast
  exact G.two_mul_card_edgeFinset.symm

/-- The 200-bin scale used for an `n`-vertex host. -/
noncomputable def degreeBase (n : ℕ) : ℕ :=
  Nat.ceil ((n : ℝ) ^ (1 / 100 : ℝ)) + 2

lemma degreeBase_gt_one (n : ℕ) : 1 < degreeBase n := by
  dsimp [degreeBase]
  omega

lemma card_orderedPair_fin_le_sq (n : ℕ) :
    Fintype.card (OrderedPair (Fin n)) ≤ n ^ 2 := by
  calc
    Fintype.card (OrderedPair (Fin n)) ≤ Fintype.card (Fin n × Fin n) :=
      Fintype.card_le_of_injective (fun p : OrderedPair (Fin n) ↦ p.1)
        (fun _ _ h ↦ Subtype.ext h)
    _ = n ^ 2 := by simp [pow_two]

lemma degreeBase_pow_two_hundred_ge_sq (n : ℕ) :
    n ^ 2 ≤ degreeBase n ^ 200 := by
  let x : ℝ := (n : ℝ) ^ (1 / 100 : ℝ)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hceil : x ≤ (degreeBase n : ℝ) := by
    change x ≤ ((Nat.ceil x + 2 : ℕ) : ℝ)
    calc
      x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
      _ ≤ ((Nat.ceil x + 2 : ℕ) : ℝ) := by
        norm_cast
        omega
  have hpow := pow_le_pow_left₀ hx0 hceil 200
  have hxpow : x ^ 200 = (n : ℝ) ^ 2 := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  rw [hxpow] at hpow
  exact_mod_cast hpow

lemma pairAuxGraph_degree_lt_degreeBase_pow
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : OrderedPair (Fin n)) :
    (pairAuxGraph G).degree p < degreeBase n ^ 200 := by
  exact lt_of_lt_of_le ((pairAuxGraph G).degree_lt_card_verts p)
    ((card_orderedPair_fin_le_sq n).trans (degreeBase_pow_two_hundred_ge_sq n))

lemma degreeBase_cast_le_four_rpow :
    ∀ᶠ n : ℕ in atTop,
      (degreeBase n : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 100 : ℝ) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  let x : ℝ := (n : ℝ) ^ (1 / 100 : ℝ)
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx1 : 1 ≤ x := by
    dsimp [x]
    simpa using Real.one_le_rpow hnreal (by norm_num : (0 : ℝ) ≤ 1 / 100)
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx1
  have hceil := Nat.ceil_lt_add_one hx0
  dsimp [degreeBase]
  push_cast
  dsimp [x] at hceil ⊢
  linarith

noncomputable def fourthRootMajorantConstant : ℝ :=
  auxiliarySeventhPowerConstant + 1

lemma fourthRoot_pairAux_le
    (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : counterexampleGraph.Free G) :
    Real.sqrt (Real.sqrt
      ((directedEdgeFinset (pairAuxGraph G)).card : ℝ)) ≤
      fourthRootMajorantConstant * (n : ℝ) ^ (9 / 14 : ℝ) * degreeBase n := by
  let q : ℝ := (directedEdgeFinset (pairAuxGraph G)).card
  let N : ℝ := Fintype.card (OrderedPair (Fin n))
  let b : ℝ := degreeBase n
  let c : ℝ := fourthRootMajorantConstant
  let z : ℝ := c * (n : ℝ) ^ (9 / 14 : ℝ) * b
  have hA0 : 0 ≤ auxiliarySeventhPowerConstant := by
    dsimp [auxiliarySeventhPowerConstant]
    positivity
  have hc1 : 1 ≤ c := by dsimp [c, fourthRootMajorantConstant]; linarith
  have hc0 : 0 ≤ c := le_trans (by norm_num) hc1
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hb1 : 1 ≤ b := by
    dsimp [b]
    exact_mod_cast (le_of_lt (degreeBase_gt_one n))
  have hN : N ≤ (n : ℝ) ^ 2 := by
    dsimp [N]
    exact_mod_cast card_orderedPair_fin_le_sq n
  have hq7 : q ^ 7 ≤ auxiliarySeventhPowerConstant * N ^ 9 * b ^ 24 := by
    dsimp [q, N, b]
    exact pairAuxGraph_seventh_power_bound G (degreeBase n)
      (degreeBase_gt_one n) (pairAuxGraph_degree_lt_degreeBase_pow n G) hfree
  have hnPower : ((n : ℝ) ^ (9 / 14 : ℝ)) ^ 28 = (n : ℝ) ^ 18 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
    norm_num
  have hqz : q ^ 7 ≤ z ^ 28 := by
    have hNpow : N ^ 9 ≤ (n : ℝ) ^ 18 := by
      calc
        N ^ 9 ≤ ((n : ℝ) ^ 2) ^ 9 := pow_le_pow_left₀ (by positivity) hN 9
        _ = (n : ℝ) ^ 18 := by ring
    have hbpow : b ^ 24 ≤ b ^ 28 := pow_le_pow_right₀ hb1 (by omega)
    have hc : auxiliarySeventhPowerConstant ≤ c ^ 28 :=
      (show auxiliarySeventhPowerConstant ≤ c by
        dsimp [c, fourthRootMajorantConstant]
        linarith).trans (le_self_pow₀ hc1 (by norm_num))
    calc
      q ^ 7 ≤ auxiliarySeventhPowerConstant * N ^ 9 * b ^ 24 := hq7
      _ ≤ c ^ 28 * ((n : ℝ) ^ 18) * b ^ 28 := by gcongr
      _ = c ^ 28 * (((n : ℝ) ^ (9 / 14 : ℝ)) ^ 28) * b ^ 28 := by
        rw [hnPower]
      _ = z ^ 28 := by
        dsimp [z]
        ring
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hz0 : 0 ≤ z := by dsimp [z, b]; positivity
  have hqz4 : q ≤ z ^ 4 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (7 : ℕ) ≠ 0) (pow_nonneg hz0 4)
    calc
      q ^ 7 ≤ z ^ 28 := hqz
      _ = (z ^ 4) ^ 7 := by ring
  have hsqrt0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hfourth0 : 0 ≤ Real.sqrt (Real.sqrt q) := Real.sqrt_nonneg _
  have hfourthPow : (Real.sqrt (Real.sqrt q)) ^ 4 = q := by
    have h₁ := Real.sq_sqrt hq0
    have h₂ := Real.sq_sqrt hsqrt0
    nlinarith [sq_nonneg (Real.sqrt (Real.sqrt q))]
  have hroot : Real.sqrt (Real.sqrt q) ≤ z := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) hz0
    rw [hfourthPow]
    exact hqz4
  simpa [q, z, c, b] using hroot

lemma host_edge_card_le_degreeBase_bound
    (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : counterexampleGraph.Free G) :
    (G.edgeFinset.card : ℝ) ≤
      (n : ℝ) + (n : ℝ) * Real.sqrt n +
        (n : ℝ) * (fourthRootMajorantConstant *
          (n : ℝ) ^ (9 / 14 : ℝ) * degreeBase n) := by
  have hkst := Erdos888.ColoredGraph.edgeCount_le
    (fun x : Fin n ↦ fun y : Fin n ↦ G.Adj x y)
  rw [colored_edgeCount_eq_twice_card_edges G,
    colored_rectangleCount_eq_pairAux_directedEdge_card G] at hkst
  simp only [Fintype.card_fin] at hkst
  have hnn : (0 : ℝ) ≤ n := by positivity
  have hsqrtmul : Real.sqrt ((n : ℝ) * n) = n := by
    rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_nonneg hnn]
  rw [hsqrtmul] at hkst
  have hroot := fourthRoot_pairAux_le n hn G hfree
  have hterm := mul_le_mul_of_nonneg_left hroot
    (show (0 : ℝ) ≤ 2 * n by positivity)
  nlinarith

/-- The rational exponent used after absorbing the bin-scale factor. -/
noncomputable def witnessUpperExponent : ℝ := 139 / 84

noncomputable def extremalUpperConstant : ℝ :=
  2 + 4 * fourthRootMajorantConstant

lemma host_edge_card_le_power
    (n : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hfree : counterexampleGraph.Free G)
    (hbase : (degreeBase n : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 100 : ℝ)) :
    (G.edgeFinset.card : ℝ) ≤
      extremalUpperConstant * polynomialGrowth witnessUpperExponent n := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnreal
  have hn0 : (0 : ℝ) ≤ n := hnpos.le
  have hc0 : 0 ≤ fourthRootMajorantConstant := by
    dsimp [fourthRootMajorantConstant, auxiliarySeventhPowerConstant]
    positivity
  have hpow1 : (n : ℝ) ≤ (n : ℝ) ^ witnessUpperExponent := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hnreal
        (show (1 : ℝ) ≤ witnessUpperExponent by
          norm_num [witnessUpperExponent])
  have hsqrtpow : (n : ℝ) * Real.sqrt n = (n : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring,
      Real.rpow_add hnpos, Real.rpow_one]
  have hpowThreeHalves :
      (n : ℝ) * Real.sqrt n ≤ (n : ℝ) ^ witnessUpperExponent := by
    rw [hsqrtpow]
    exact Real.rpow_le_rpow_of_exponent_le hnreal (by
      norm_num [witnessUpperExponent])
  have hbaseMul :
      (n : ℝ) * (fourthRootMajorantConstant * (n : ℝ) ^ (9 / 14 : ℝ) *
        degreeBase n) ≤
      (n : ℝ) * (fourthRootMajorantConstant * (n : ℝ) ^ (9 / 14 : ℝ) *
        (4 * (n : ℝ) ^ (1 / 100 : ℝ))) := by
    apply mul_le_mul_of_nonneg_left _ hn0
    exact mul_le_mul_of_nonneg_left hbase
      (mul_nonneg hc0 (Real.rpow_nonneg hn0 _))
  have hpowerIdentity :
      (n : ℝ) * (fourthRootMajorantConstant * (n : ℝ) ^ (9 / 14 : ℝ) *
        (4 * (n : ℝ) ^ (1 / 100 : ℝ))) =
      4 * fourthRootMajorantConstant *
        (n : ℝ) ^ (1 + 9 / 14 + 1 / 100 : ℝ) := by
    rw [Real.rpow_add hnpos (1 + 9 / 14) (1 / 100),
      Real.rpow_add hnpos 1 (9 / 14), Real.rpow_one]
    ring
  have hsmallExponent :
      (n : ℝ) ^ (1 + 9 / 14 + 1 / 100 : ℝ) ≤
        (n : ℝ) ^ witnessUpperExponent :=
    Real.rpow_le_rpow_of_exponent_le hnreal (by
      norm_num [witnessUpperExponent])
  have hthird :
      (n : ℝ) * (fourthRootMajorantConstant * (n : ℝ) ^ (9 / 14 : ℝ) *
        degreeBase n) ≤
      4 * fourthRootMajorantConstant * (n : ℝ) ^ witnessUpperExponent := by
    calc
      (n : ℝ) * (fourthRootMajorantConstant * (n : ℝ) ^ (9 / 14 : ℝ) *
          degreeBase n) ≤
          (n : ℝ) * (fourthRootMajorantConstant * (n : ℝ) ^ (9 / 14 : ℝ) *
            (4 * (n : ℝ) ^ (1 / 100 : ℝ))) := hbaseMul
      _ = 4 * fourthRootMajorantConstant *
          (n : ℝ) ^ (1 + 9 / 14 + 1 / 100 : ℝ) := hpowerIdentity
      _ ≤ 4 * fourthRootMajorantConstant *
          (n : ℝ) ^ witnessUpperExponent :=
        mul_le_mul_of_nonneg_left hsmallExponent (by positivity)
  calc
    (G.edgeFinset.card : ℝ) ≤
        (n : ℝ) + (n : ℝ) * Real.sqrt n +
          (n : ℝ) * (fourthRootMajorantConstant *
            (n : ℝ) ^ (9 / 14 : ℝ) * degreeBase n) :=
      host_edge_card_le_degreeBase_bound n hn G hfree
    _ ≤ (n : ℝ) ^ witnessUpperExponent +
          (n : ℝ) ^ witnessUpperExponent +
          4 * fourthRootMajorantConstant * (n : ℝ) ^ witnessUpperExponent :=
      add_le_add (add_le_add hpow1 hpowThreeHalves) hthird
    _ = extremalUpperConstant * polynomialGrowth witnessUpperExponent n := by
      dsimp [extremalUpperConstant, polynomialGrowth]
      ring

lemma counterexampleGraph_eventually_extremal_bound :
    ∀ᶠ n : ℕ in atTop,
      extremalGrowth counterexampleGraph n ≤
        extremalUpperConstant * polynomialGrowth witnessUpperExponent n := by
  filter_upwards [degreeBase_cast_le_four_rpow, eventually_ge_atTop 1] with n hbase hn
  have hconstant :
      0 ≤ extremalUpperConstant * polynomialGrowth witnessUpperExponent n := by
    dsimp [extremalUpperConstant, fourthRootMajorantConstant,
      auxiliarySeventhPowerConstant, polynomialGrowth]
    positivity
  have hext :
      (SimpleGraph.extremalNumber (Fintype.card (Fin n)) counterexampleGraph : ℝ) ≤
        extremalUpperConstant * polynomialGrowth witnessUpperExponent n := by
    apply (SimpleGraph.extremalNumber_le_iff_of_nonneg
      (V := Fin n) counterexampleGraph hconstant).2
    intro G _ hfree
    exact host_edge_card_le_power n hn G hfree hbase
  simpa [extremalGrowth] using hext

/-- The fully proved finite estimate, packaged in the asymptotic notation used
by the Erdős--Simonovits conjecture. -/
theorem counterexampleGraph_extremal_upper :
    extremalGrowth counterexampleGraph =O[atTop]
      polynomialGrowth witnessUpperExponent := by
  refine IsBigO.of_bound extremalUpperConstant ?_
  filter_upwards [counterexampleGraph_eventually_extremal_bound] with n hn
  have hf : 0 ≤ extremalGrowth counterexampleGraph n := by
    dsimp [extremalGrowth]
    positivity
  have hg : 0 ≤ polynomialGrowth witnessUpperExponent n := by
    dsimp [polynomialGrowth]
    positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg hg] using hn

lemma polynomialGrowth_isLittleO {a b : ℝ} (hab : a < b) :
    polynomialGrowth a =o[atTop] polynomialGrowth b := by
  refine isLittleO_of_tendsto' ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    intro hz
    have hp : 0 < polynomialGrowth b n := by
      dsimp [polynomialGrowth]
      exact Real.rpow_pos_of_pos (by exact_mod_cast hn) b
    exact (hp.ne' hz).elim
  · have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (a - b)) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp
        tendsto_natCast_atTop_atTop
      rw [show a - b = -(b - a) by ring]
      exact h
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [polynomialGrowth]
    rw [← Real.rpow_sub (by exact_mod_cast hn : (0 : ℝ) < n)]

lemma not_polynomialGrowth_isBigO_of_lt {a b : ℝ} (hab : a < b) :
    ¬polynomialGrowth b =O[atTop] polynomialGrowth a := by
  have hnonzero : ∀ᶠ n : ℕ in atTop, polynomialGrowth a n ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (Real.rpow_pos_of_pos (by exact_mod_cast hn : (0 : ℝ) < n) a).ne'
  exact (polynomialGrowth_isLittleO hab).not_isBigO
    (Filter.Eventually.frequently hnonzero)

/-- Erdős Problem 147 has a negative answer.  The witness is the bipartite,
4-regular graph `C₁₂[2]`, whose extremal exponent is at most `139/84 < 5/3`. -/
theorem not_erdosSimonovitsConjecture : ¬ErdosSimonovitsConjecture := by
  intro hconjecture
  obtain ⟨ε, hε, hlower⟩ := hconjecture (Fin 12 × Fin 2)
    counterexampleGraph 4 counterexampleGraph_isBipartite
    counterexampleGraph_minDegree
  have hlt : witnessUpperExponent <
      2 - 1 / ((4 : ℝ) - 1) + ε := by
    dsimp [witnessUpperExponent]
    norm_num at hε ⊢
    linarith
  exact (not_polynomialGrowth_isBigO_of_lt hlt)
    (hlower.trans counterexampleGraph_extremal_upper)

#print axioms not_erdosSimonovitsConjecture

end Erdos147
