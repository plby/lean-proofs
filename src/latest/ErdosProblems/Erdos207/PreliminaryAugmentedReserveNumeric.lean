/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.AggregatePreliminaryGreedyJointLaw
import ErdosProblems.Erdos207.LaterTriangleScaleUpdate

/-!
# Numeric form of the preliminary augmented-reserve update

This file absorbs the two independent powerset partitions created by the
preliminary family.  A new prescribed triangle costs `alpha`, a new
prescribed residual edge costs `eta`, and the uniform exceptional probability
is paid from the next additive error budget.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- If every vortex set is nonempty and `p ≤ 1`, the product of the
per-triangle master weights is at most one. -/
lemma laterTriangleScale_le_one
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (hnonempty : ∀ i, (W.U i).Nonempty)
    (k : Fin (ell + 1)) {p : ℝ≥0} (hp : p ≤ 1)
    (D : TripleSystemOn V) :
    laterTriangleScale W k p D ≤ 1 := by
  unfold laterTriangleScale
  apply Finset.prod_le_one
  · intro T hT
    positivity
  · intro T hT
    exact (div_le_one₀ (by
      exact_mod_cast card_pos.mpr (hnonempty (W.truncatedLevel k T)))).2 <| by
      calc
        p ≤ 1 := hp
        _ ≤ ((W.U (W.truncatedLevel k T)).card : ℝ≥0) := by
          exact_mod_cast card_pos.mpr (hnonempty (W.truncatedLevel k T))

/-- Powers of an old reserve density and of the preliminary survival density
combine into the next reserve-density power. -/
lemma reserveDensity_mul_pow_le
    (reserveDensity eta reserveDensity' : ℝ≥0) (r u R : ℕ)
    (hcard : R = r + u)
    (hreserve : reserveDensity ≤ reserveDensity')
    (heta : eta ≤ reserveDensity') :
    reserveDensity ^ r * eta ^ u ≤ reserveDensity' ^ R := by
  rw [hcard, pow_add]
  exact mul_le_mul (pow_le_pow_left' hreserve r)
    (pow_le_pow_left' heta u) (by positivity) (by positivity)

/-- Scalar heart of the preliminary update.  The error hypothesis reflects
the two contributions to the next additive budget: the old additive term and
the exceptional probability in the preliminary joint law. -/
lemma preliminaryAugmentedReservePartitionTerm_le
    (p p' reserveDensity reserveDensity' alpha eta epsilon C C' b b'
      nInv oldScale newScale : ℝ≥0)
    (a s e r t u d R : ℕ)
    (hDcard : d = s + t) (hRcard : R = r + u)
    (hCC' : C ≤ C') (hC' : 1 ≤ C') (hpp' : p ≤ p')
    (halpha : alpha ≤ 1) (hetaOne : eta ≤ 1)
    (hscale : oldScale * alpha ^ t ≤ newScale)
    (hreserve : reserveDensity ^ r * eta ^ u ≤ reserveDensity' ^ R)
    (hunit : p ^ e * reserveDensity ^ r * nInv ^ a * oldScale + b ≤ 2)
    (herror : b + 2 * epsilon ≤ b') :
    (alpha ^ t * eta ^ u + epsilon) *
        (C ^ (a + s + e + r) *
          (p ^ e * reserveDensity ^ r * nInv ^ a * oldScale + b)) ≤
      C' ^ (a + d + e + R) *
        (p' ^ e * reserveDensity' ^ R * nInv ^ a * newScale + b') := by
  let A : ℝ≥0 := alpha ^ t * eta ^ u
  let M : ℝ≥0 := p ^ e * reserveDensity ^ r * nInv ^ a * oldScale
  let M' : ℝ≥0 := p' ^ e * reserveDensity' ^ R * nInv ^ a * newScale
  have hbase : C ^ (a + s + e + r) ≤ C' ^ (a + d + e + R) := by
    calc
      C ^ (a + s + e + r) ≤ C' ^ (a + s + e + r) := by gcongr
      _ ≤ C' ^ (a + d + e + R) := by
        apply pow_le_pow_right₀ hC'
        omega
  have hA : A ≤ 1 := by
    dsimp only [A]
    calc
      alpha ^ t * eta ^ u ≤ 1 ^ t * 1 ^ u := by gcongr
      _ = 1 := by simp
  have hp : p ^ e ≤ p' ^ e := pow_le_pow_left' hpp' e
  have hmain : A * M ≤ M' := by
    dsimp only [A, M, M']
    calc
      (alpha ^ t * eta ^ u) *
          (p ^ e * reserveDensity ^ r * nInv ^ a * oldScale) =
          p ^ e * nInv ^ a *
            ((oldScale * alpha ^ t) *
              (reserveDensity ^ r * eta ^ u)) := by ring
      _ ≤ p' ^ e * nInv ^ a *
            (newScale * reserveDensity' ^ R) := by
        gcongr
      _ = p' ^ e * reserveDensity' ^ R * nInv ^ a * newScale := by ring
  have herrInner : A * b + epsilon * (M + b) ≤ b' := by
    calc
      A * b + epsilon * (M + b) ≤ 1 * b + epsilon * 2 := by
        gcongr
      _ = b + 2 * epsilon := by ring
      _ ≤ b' := herror
  calc
    (alpha ^ t * eta ^ u + epsilon) *
        (C ^ (a + s + e + r) *
          (p ^ e * reserveDensity ^ r * nInv ^ a * oldScale + b)) =
        C ^ (a + s + e + r) *
          (A * M + (A * b + epsilon * (M + b))) := by
      dsimp only [A, M]
      ring
    _ ≤ C' ^ (a + d + e + R) * (M' + b') := by
      exact mul_le_mul hbase (add_le_add hmain herrInner)
        (by positivity) (by positivity)
    _ = C' ^ (a + d + e + R) *
        (p' ^ e * reserveDensity' ^ R * nInv ^ a * newScale + b') := by
      rfl

/-- Fully geometric specialization of
`preliminaryAugmentedReservePartitionTerm_le` for one pair of powerset
parts. -/
lemma preliminaryAugmentedReservePowersetPart_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k next : Fin (ell + 1))
    (p p' reserveDensity reserveDensity' alpha eta epsilon C C' b b' : ℝ≥0)
    (Ifix Dfix : TripleSystemOn V) (Efix Rfix : Finset (Sym2 V))
    (S : TripleSystemOn V) (hSD : S ⊆ Dfix)
    (T : Finset (Sym2 V)) (hTR : T ⊆ Rfix)
    (hnonempty : ∀ i, (W.U i).Nonempty)
    (hkn : k ≤ next) (hCC' : C ≤ C') (hC' : 1 ≤ C')
    (hpp' : p ≤ p') (hpOne : p ≤ 1)
    (hreserveMono : reserveDensity ≤ reserveDensity')
    (hreserveOne : reserveDensity ≤ 1)
    (halpha : alpha ≤ 1) (hetaOne : eta ≤ 1)
    (hetaReserve : eta ≤ reserveDensity')
    (hnInv : (Fintype.card V : ℝ≥0)⁻¹ ≤ 1)
    (hbOne : b ≤ 1) (herror : b + 2 * epsilon ≤ b')
    (hnew : ∀ Q : TripleOn V,
      alpha ≤ p' / ((W.U (W.truncatedLevel next Q)).card : ℝ≥0)) :
    (alpha ^ (Dfix \ S).card * eta ^ (Rfix \ T).card + epsilon) *
        (C ^ (Ifix.card + S.card + Efix.card + T.card) *
          (p ^ Efix.card * reserveDensity ^ T.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
              laterTriangleScale W k p S + b)) ≤
      C' ^ (Ifix.card + Dfix.card + Efix.card + Rfix.card) *
        (p' ^ Efix.card * reserveDensity' ^ Rfix.card *
          (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
            laterTriangleScale W next p' Dfix + b') := by
  have hDcard : Dfix.card = S.card + (Dfix \ S).card := by
    rw [← card_sdiff_add_card_eq_card hSD]
    omega
  have hRcard : Rfix.card = T.card + (Rfix \ T).card := by
    rw [← card_sdiff_add_card_eq_card hTR]
    omega
  have hold : ∀ Q ∈ S,
      p / ((W.U (W.truncatedLevel k Q)).card : ℝ≥0) ≤
        p' / ((W.U (W.truncatedLevel next Q)).card : ℝ≥0) := by
    intro Q _hQS
    exact W.laterTrianglePointScale_mono hnonempty hkn hpp' Q
  have hscale : laterTriangleScale W k p S *
      alpha ^ (Dfix \ S).card ≤ laterTriangleScale W next p' Dfix :=
    laterTriangleScale_mul_pow_le W k next p p' alpha Dfix S hSD hold
      (fun Q _hQ ↦ hnew Q)
  have hreserve : reserveDensity ^ T.card * eta ^ (Rfix \ T).card ≤
      reserveDensity' ^ Rfix.card :=
    reserveDensity_mul_pow_le reserveDensity eta reserveDensity'
      T.card (Rfix \ T).card Rfix.card hRcard hreserveMono hetaReserve
  have hscaleOne : laterTriangleScale W k p S ≤ 1 :=
    laterTriangleScale_le_one W hnonempty k hpOne S
  have hunit : p ^ Efix.card * reserveDensity ^ T.card *
        (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
          laterTriangleScale W k p S + b ≤ 2 := by
    have hmainOne : p ^ Efix.card * reserveDensity ^ T.card *
        (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
          laterTriangleScale W k p S ≤ 1 := by
      calc
        p ^ Efix.card * reserveDensity ^ T.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
              laterTriangleScale W k p S ≤
            1 ^ Efix.card * 1 ^ T.card * 1 ^ Ifix.card * 1 := by gcongr
        _ = 1 := by simp
    calc
      p ^ Efix.card * reserveDensity ^ T.card *
          (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
            laterTriangleScale W k p S + b ≤ 1 + 1 := by gcongr
      _ = 2 := by norm_num
  exact preliminaryAugmentedReservePartitionTerm_le
    p p' reserveDensity reserveDensity' alpha eta epsilon C C' b b'
      ((Fintype.card V : ℝ≥0)⁻¹)
      (laterTriangleScale W k p S) (laterTriangleScale W next p' Dfix)
      Ifix.card S.card Efix.card T.card (Dfix \ S).card
      (Rfix \ T).card Dfix.card Rfix.card hDcard hRcard hCC' hC' hpp'
      halpha hetaOne hscale hreserve hunit herror

/-- Numeric endpoint for adjoining a preliminary greedy family and its
uncovered crossing edges to a reserve-aware master law. -/
theorem IsReserveStronglyWellDistributed.jointBind_preliminaryAugmentedReserve_of_numeric
    {Omega Xi V : Type*} [Fintype Omega] [Fintype Xi] [Fintype V]
    [DecidableEq Omega] [DecidableEq Xi] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {K : Omega → FiniteLaw Xi}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {sampled : Omega → Finset (Sym2 V)}
    {G : Omega → SimpleGraph V} {U : Finset V}
    {p reserveDensity C b p' reserveDensity' C' b' alpha eta epsilon : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed L W k initial later sampled
      p reserveDensity C b)
    (added : Omega → Xi → TripleSystemOn V)
    (hpreliminary : ∀ omega Q E,
      (K omega).probability (fun xi ↦
        Q ⊆ added omega xi ∧
        E ⊆ preliminaryResidualCrossingEdges (G omega) U
          (added omega xi)) ≤ alpha ^ Q.card * eta ^ E.card + epsilon)
    (hnonempty : ∀ i, (W.U i).Nonempty)
    (hkn : k ≤ next) (hCC' : C ≤ C') (hC' : 1 ≤ C')
    (hpp' : p ≤ p') (hpOne : p ≤ 1)
    (hreserveMono : reserveDensity ≤ reserveDensity')
    (hreserveOne : reserveDensity ≤ 1)
    (halpha : alpha ≤ 1) (hetaOne : eta ≤ 1)
    (hetaReserve : eta ≤ reserveDensity')
    (hbOne : b ≤ 1) (herror : b + 2 * epsilon ≤ b')
    (hnew : ∀ Q : TripleOn V,
      alpha ≤ p' / ((W.U (W.truncatedLevel next Q)).card : ℝ≥0)) :
    IsReserveStronglyWellDistributed (L.jointBind K) W next
      (jointInitial initial) (jointLater later added)
      (fun z ↦ preliminaryAugmentedReserve (G z.1) U (sampled z.1)
        (added z.1 z.2)) p' reserveDensity' (2 * C') b' := by
  have hVpos : 0 < Fintype.card V := by
    have hU0 := hnonempty (0 : Fin (ell + 1))
    exact Fintype.card_pos_iff.mpr ⟨hU0.choose⟩
  have hnInv : (Fintype.card V : ℝ≥0)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ (by exact_mod_cast hVpos)).2
    exact_mod_cast hVpos
  apply hstrong.jointBind_preliminaryAugmentedReserve added
    (fun Q E ↦ alpha ^ Q.card * eta ^ E.card + epsilon) hpreliminary
  intro Ifix Dfix Efix Rfix _hdisj S hS T hT
  exact preliminaryAugmentedReservePowersetPart_le W k next
    p p' reserveDensity reserveDensity' alpha eta epsilon C C' b b'
      Ifix Dfix Efix Rfix S (mem_powerset.mp hS) T (mem_powerset.mp hT)
      hnonempty hkn hCC' hC' hpp' hpOne hreserveMono hreserveOne halpha
      hetaOne hetaReserve hnInv hbOne herror hnew

/-- Numeric preliminary update for a totalized kernel whose product estimate
is available only on the positive-mass support of the old law. -/
theorem IsReserveStronglyWellDistributed.jointBind_preliminaryAugmentedReserve_of_numeric_supported
    {Omega Xi V : Type*} [Fintype Omega] [Fintype Xi] [Fintype V]
    [DecidableEq Omega] [DecidableEq Xi] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {K : Omega → FiniteLaw Xi}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {sampled : Omega → Finset (Sym2 V)}
    {G : Omega → SimpleGraph V} {U : Finset V}
    {p reserveDensity C b p' reserveDensity' C' b' alpha eta epsilon : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed L W k initial later sampled
      p reserveDensity C b)
    (added : Omega → Xi → TripleSystemOn V)
    (hpreliminary : ∀ omega, 0 < L.mass omega → ∀ Q E,
      (K omega).probability (fun xi ↦
        Q ⊆ added omega xi ∧
        E ⊆ preliminaryResidualCrossingEdges (G omega) U
          (added omega xi)) ≤ alpha ^ Q.card * eta ^ E.card + epsilon)
    (hnonempty : ∀ i, (W.U i).Nonempty)
    (hkn : k ≤ next) (hCC' : C ≤ C') (hC' : 1 ≤ C')
    (hpp' : p ≤ p') (hpOne : p ≤ 1)
    (hreserveMono : reserveDensity ≤ reserveDensity')
    (hreserveOne : reserveDensity ≤ 1)
    (halpha : alpha ≤ 1) (hetaOne : eta ≤ 1)
    (hetaReserve : eta ≤ reserveDensity')
    (hbOne : b ≤ 1) (herror : b + 2 * epsilon ≤ b')
    (hnew : ∀ Q : TripleOn V,
      alpha ≤ p' / ((W.U (W.truncatedLevel next Q)).card : ℝ≥0)) :
    IsReserveStronglyWellDistributed (L.jointBind K) W next
      (jointInitial initial) (jointLater later added)
      (fun z ↦ preliminaryAugmentedReserve (G z.1) U (sampled z.1)
        (added z.1 z.2)) p' reserveDensity' (2 * C') b' := by
  have hVpos : 0 < Fintype.card V := by
    have hU0 := hnonempty (0 : Fin (ell + 1))
    exact Fintype.card_pos_iff.mpr ⟨hU0.choose⟩
  have hnInv : (Fintype.card V : ℝ≥0)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ (by exact_mod_cast hVpos)).2
    exact_mod_cast hVpos
  apply hstrong.jointBind_preliminaryAugmentedReserve_supported added
    (fun Q E ↦ alpha ^ Q.card * eta ^ E.card + epsilon) hpreliminary
  intro Ifix Dfix Efix Rfix _hdisj S hS T hT
  exact preliminaryAugmentedReservePowersetPart_le W k next
    p p' reserveDensity reserveDensity' alpha eta epsilon C C' b b'
      Ifix Dfix Efix Rfix S (mem_powerset.mp hS) T (mem_powerset.mp hT)
      hnonempty hkn hCC' hC' hpp' hpOne hreserveMono hreserveOne halpha
      hetaOne hetaReserve hnInv hbOne herror hnew

end

end Erdos207
