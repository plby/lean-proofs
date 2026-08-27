/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveLinkFactor

/-!
# Product-scale bookkeeping for one reserve-supported link stage

The powerset expansion separates a prescribed later family into triangles
already present before the link stage and triangles supplied by that stage.
This file recombines the two products.  It deliberately states the two
pointwise comparisons as hypotheses: the geometric level calculation and
the numeric parameter hierarchy can then be discharged independently.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

lemma Vortex.truncatedLevel_mono
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) {k next : Fin (ell + 1)} (hkn : k ≤ next)
    (T : TripleOn V) :
    W.truncatedLevel k T ≤ W.truncatedLevel next T := by
  exact min_le_min_left (W.level T) hkn

/-- Moving deeper in a nonempty vortex and increasing the density parameter
can only enlarge the per-triangle master weight. -/
lemma Vortex.laterTrianglePointScale_mono
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (hnonempty : ∀ i, (W.U i).Nonempty)
    {k next : Fin (ell + 1)} (hkn : k ≤ next)
    {p p' : ℝ≥0} (hpp' : p ≤ p') (T : TripleOn V) :
    p / ((W.U (W.truncatedLevel k T)).card : ℝ≥0) ≤
      p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0) := by
  apply div_le_div₀ (by positivity) hpp'
  · exact_mod_cast card_pos.mpr (hnonempty (W.truncatedLevel next T))
  · exact_mod_cast card_le_card (W.antitone _ _ (W.truncatedLevel_mono hkn T))

/-- Recombine the old prescribed triangles and the newly supplied triangles
into the next-stage product scale. -/
lemma laterTriangleScale_mul_pow_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k next : Fin (ell + 1))
    (p p' beta : ℝ≥0) (D S : TripleSystemOn V)
    (hSD : S ⊆ D)
    (hold : ∀ T ∈ S,
      p / ((W.U (W.truncatedLevel k T)).card : ℝ≥0) ≤
        p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0))
    (hnew : ∀ T ∈ D \ S,
      beta ≤ p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0)) :
    laterTriangleScale W k p S * beta ^ (D \ S).card ≤
      laterTriangleScale W next p' D := by
  have hOldProd : laterTriangleScale W k p S ≤
      ∏ T ∈ S,
        p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0) := by
    unfold laterTriangleScale
    exact Finset.prod_le_prod' hold
  have hNewProd : beta ^ (D \ S).card ≤
      ∏ T ∈ D \ S,
        p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod' hnew
  calc
    laterTriangleScale W k p S * beta ^ (D \ S).card ≤
        (∏ T ∈ S,
          p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0)) *
        ∏ T ∈ D \ S,
          p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0) := by
      exact mul_le_mul hOldProd hNewProd (by positivity) (by positivity)
    _ = laterTriangleScale W next p' D := by
      rw [mul_comm]
      exact Finset.prod_sdiff hSD

/-- The form used after the exact reserve/link factorization: each new
triangle contributes `alpha * C^2 * reserveDensity^2`. -/
lemma laterTriangleScale_linkReserve_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k next : Fin (ell + 1))
    (p p' alpha C reserveDensity : ℝ≥0)
    (D S : TripleSystemOn V) (hSD : S ⊆ D)
    (hold : ∀ T ∈ S,
      p / ((W.U (W.truncatedLevel k T)).card : ℝ≥0) ≤
        p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0))
    (hnew : ∀ T ∈ D \ S,
      alpha * C ^ 2 * reserveDensity ^ 2 ≤
        p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0)) :
    laterTriangleScale W k p S *
        (alpha ^ (D \ S).card * C ^ (2 * (D \ S).card) *
          reserveDensity ^ (2 * (D \ S).card)) ≤
      laterTriangleScale W next p' D := by
  rw [linkReserveConstantFactor_pow]
  exact laterTriangleScale_mul_pow_le W k next p p'
    (alpha * C ^ 2 * reserveDensity ^ 2) D S hSD hold hnew

/-- A single powerset part is absorbed by the next master bound once the
triangle-scale product comparison and the two scalar monotonicities hold.
The exponent identity `|D| = |S| + |D \ S|` is supplied explicitly so this
lemma is also usable outside the particular powerset decomposition. -/
lemma reserveLinkPartitionTerm_le
    (p p' alpha reserveDensity C C' b b' nInv oldScale newScale : ℝ≥0)
    (a s e t d : ℕ)
    (hcard : d = s + t)
    (hCC' : C ≤ C') (hC' : 1 ≤ C') (hpp' : p ≤ p')
    (herrorFactor : alpha * C ^ 2 ≤ 1) (hbb' : b ≤ b')
    (hscale : oldScale *
        (alpha * C ^ 2 * reserveDensity ^ 2) ^ t ≤ newScale) :
    alpha ^ t *
        (C ^ (a + s + e + 2 * t) *
          (p ^ e * nInv ^ a * reserveDensity ^ (2 * t) * oldScale + b)) ≤
      C' ^ (a + d + e) *
        (p' ^ e * nInv ^ a * newScale + b') := by
  have hbase : C ^ (a + s + e) ≤ C' ^ (a + d + e) := by
    calc
      C ^ (a + s + e) ≤ C' ^ (a + s + e) := by gcongr
      _ ≤ C' ^ (a + d + e) := by
        apply pow_le_pow_right₀ hC'
        omega
  have hpPow : p ^ e * nInv ^ a ≤ p' ^ e * nInv ^ a := by
    gcongr
  have hmain :
      p ^ e * nInv ^ a * oldScale *
          (alpha * C ^ 2 * reserveDensity ^ 2) ^ t ≤
        p' ^ e * nInv ^ a * newScale := by
    calc
      p ^ e * nInv ^ a * oldScale *
          (alpha * C ^ 2 * reserveDensity ^ 2) ^ t =
          (p ^ e * nInv ^ a) *
            (oldScale *
              (alpha * C ^ 2 * reserveDensity ^ 2) ^ t) := by ring
      _ ≤ (p' ^ e * nInv ^ a) * newScale := by
        exact mul_le_mul hpPow hscale (by positivity) (by positivity)
      _ = p' ^ e * nInv ^ a * newScale := by ring
  have herrorPow : (alpha * C ^ 2) ^ t ≤ 1 :=
    pow_le_one₀ (by positivity) herrorFactor
  have herror : b * (alpha * C ^ 2) ^ t ≤ b' := by
    calc
      b * (alpha * C ^ 2) ^ t ≤ b * 1 := by gcongr
      _ = b := mul_one b
      _ ≤ b' := hbb'
  rw [show a + s + e + 2 * t = (a + s + e) + 2 * t by omega]
  rw [linkReservePartitionTerm_factor]
  apply mul_le_mul hbase _ (by positivity) (by positivity)
  exact add_le_add hmain herror

/-- Fully geometric/numeric specialization of
`reserveLinkPartitionTerm_le` for a powerset part `S ⊆ D`. -/
lemma reserveLinkPowersetPart_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k next : Fin (ell + 1))
    (p p' alpha reserveDensity C C' b b' : ℝ≥0)
    (Ifix Dfix : TripleSystemOn V) (Efix : Finset (Sym2 V))
    (S : TripleSystemOn V) (hSD : S ⊆ Dfix)
    (hCC' : C ≤ C') (hC' : 1 ≤ C') (hpp' : p ≤ p')
    (herrorFactor : alpha * C ^ 2 ≤ 1) (hbb' : b ≤ b')
    (hold : ∀ T ∈ S,
      p / ((W.U (W.truncatedLevel k T)).card : ℝ≥0) ≤
        p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0))
    (hnew : ∀ T ∈ Dfix \ S,
      alpha * C ^ 2 * reserveDensity ^ 2 ≤
        p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0)) :
    alpha ^ (Dfix \ S).card *
        (C ^ (Ifix.card + S.card + Efix.card +
            2 * (Dfix \ S).card) *
          (p ^ Efix.card * reserveDensity ^ (2 * (Dfix \ S).card) *
              (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
              laterTriangleScale W k p S + b)) ≤
      C' ^ (Ifix.card + Dfix.card + Efix.card) *
        (p' ^ Efix.card *
            (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card *
            laterTriangleScale W next p' Dfix + b') := by
  have hcard : Dfix.card = S.card + (Dfix \ S).card := by
    rw [← card_sdiff_add_card_eq_card hSD]
    omega
  have hscale := laterTriangleScale_mul_pow_le W k next p p'
    (alpha * C ^ 2 * reserveDensity ^ 2) Dfix S hSD hold hnew
  have h := reserveLinkPartitionTerm_le p p' alpha reserveDensity C C' b b'
    ((Fintype.card V : ℝ≥0)⁻¹)
    (laterTriangleScale W k p S) (laterTriangleScale W next p' Dfix)
    Ifix.card S.card Efix.card (Dfix \ S).card Dfix.card hcard
    hCC' hC' hpp' herrorFactor hbb' hscale
  convert h using 1 <;> ring

/-- Numeric endpoint for the reserve-aware simultaneous link update.  The
entire powerset partition is discharged by three parameter comparisons and
one uniform lower bound on the next per-triangle scale. -/
theorem IsReserveStronglyWellDistributed.jointBind_simultaneousLink_of_numeric
    {Omega O V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype O] [Fintype V] [DecidableEq V]
    {ell : ℕ} {law : FiniteLaw Omega}
    {linkLaw : Omega → FiniteLaw (TripleSystemOn V)}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {U : Finset V} {center : Omega → O ↪ V}
    {K : Omega → O → BipartiteLink V}
    {p reserveDensity C b alpha p' C' b' : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed law W k initial later reserve
      p reserveDensity C b)
    (hcenter : ∀ omega o, (K omega o).center = center omega o)
    (hout : ∀ omega o, center omega o ∉ U)
    (hleft : ∀ omega o, (K omega o).left ⊆ U)
    (hright : ∀ omega o, (K omega o).right ⊆ U)
    (hspokes : ∀ omega o, (K omega o).SpokesIn (reserve omega))
    (hstruct : ∀ omega, (linkLaw omega).SupportedOn fun M ↦
      IsSimultaneousLinkFamily (K omega) M ∧ IsPackingOn M)
    (hC4 : ∀ omega Q,
      (linkLaw omega).probability (fun M ↦ Q ⊆ M) ≤ alpha ^ Q.card)
    (hnonempty : ∀ i, (W.U i).Nonempty)
    (hkn : k ≤ next) (hCC' : C ≤ C') (hC' : 1 ≤ C')
    (hpp' : p ≤ p') (herrorFactor : alpha * C ^ 2 ≤ 1)
    (hbb' : b ≤ b')
    (hnew : ∀ T : TripleOn V,
      alpha * C ^ 2 * reserveDensity ^ 2 ≤
        p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0)) :
    IsStronglyWellDistributed (law.jointBind linkLaw) W next
      (jointInitial initial) (jointLater later (fun _omega M ↦ M))
      p' (2 * C') b' := by
  apply hstrong.jointBind_simultaneousLink_of_good_partition hcenter hout
    hleft hright hspokes hstruct hC4
  intro Ifix Dfix Efix _hdisj S hS _hpacking
  apply reserveLinkPowersetPart_le W k next p p' alpha reserveDensity C C'
    b b' Ifix Dfix Efix S (mem_powerset.mp hS) hCC' hC' hpp'
    herrorFactor hbb'
  · intro T _hTS
    exact W.laterTrianglePointScale_mono hnonempty hkn hpp' T
  · intro T _hTnew
    exact hnew T

end

end Erdos207
