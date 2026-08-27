/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.LaterTriangleScaleUpdate
import ErdosProblems.Erdos207.ReserveStrongWellDistributedAdjoin

/-!
# Numeric reserve-preserving C4 updates

This is the scalar endpoint used by the preliminary internal-cover kernels.
Their conditional inclusion factor is independent of the already exposed
reserve, so arbitrary reserve prescriptions pass unchanged to the output.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

lemma reservePreservingPartitionTerm_le
    (p p' delta reserveDensity C C' b b' nInv oldScale newScale : ℝ≥0)
    (a s e r t d : ℕ)
    (hcard : d = s + t)
    (hCC' : C ≤ C') (hC' : 1 ≤ C') (hpp' : p ≤ p')
    (hdelta : delta ≤ 1) (hbb' : b ≤ b')
    (hscale : oldScale * delta ^ t ≤ newScale) :
    delta ^ t *
        (C ^ (a + s + e + r) *
          (p ^ e * reserveDensity ^ r * nInv ^ a * oldScale + b)) ≤
      C' ^ (a + d + e + r) *
        (p' ^ e * reserveDensity ^ r * nInv ^ a * newScale + b') := by
  have hbase : C ^ (a + s + e + r) ≤ C' ^ (a + d + e + r) := by
    calc
      C ^ (a + s + e + r) ≤ C' ^ (a + s + e + r) := by gcongr
      _ ≤ C' ^ (a + d + e + r) := by
        apply pow_le_pow_right₀ hC'
        omega
  have hpPow :
      p ^ e * reserveDensity ^ r * nInv ^ a ≤
        p' ^ e * reserveDensity ^ r * nInv ^ a := by gcongr
  have hmain :
      p ^ e * reserveDensity ^ r * nInv ^ a * oldScale * delta ^ t ≤
        p' ^ e * reserveDensity ^ r * nInv ^ a * newScale := by
    calc
      p ^ e * reserveDensity ^ r * nInv ^ a * oldScale * delta ^ t =
          (p ^ e * reserveDensity ^ r * nInv ^ a) *
            (oldScale * delta ^ t) := by ring
      _ ≤ (p' ^ e * reserveDensity ^ r * nInv ^ a) * newScale := by
        exact mul_le_mul hpPow hscale (by positivity) (by positivity)
  have herrorPow : delta ^ t ≤ 1 := pow_le_one₀ (by positivity) hdelta
  calc
    delta ^ t *
        (C ^ (a + s + e + r) *
          (p ^ e * reserveDensity ^ r * nInv ^ a * oldScale + b)) =
        C ^ (a + s + e + r) *
          (p ^ e * reserveDensity ^ r * nInv ^ a * oldScale * delta ^ t +
            b * delta ^ t) := by ring
    _ ≤ C' ^ (a + d + e + r) *
        (p' ^ e * reserveDensity ^ r * nInv ^ a * newScale + b') := by
      apply mul_le_mul hbase _ (by positivity) (by positivity)
      apply add_le_add hmain
      calc
        b * delta ^ t ≤ b * 1 := by gcongr
        _ = b := mul_one b
        _ ≤ b' := hbb'

theorem IsReserveStronglyWellDistributed.jointBind_adjoin_preserve_of_numeric
    {Omega Xi V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype Xi] [DecidableEq Xi] [Fintype V] [DecidableEq V]
    {ell : ℕ} {L : FiniteLaw Omega} {K : Omega → FiniteLaw Xi}
    {W : Vortex V ell} {k next : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {p reserveDensity C b delta p' C' b' : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed L W k initial later reserve
      p reserveDensity C b)
    (added : Omega → Xi → TripleSystemOn V)
    (hadded : ∀ omega Q,
      (K omega).probability (fun xi ↦ Q ⊆ added omega xi) ≤ delta ^ Q.card)
    (hnonempty : ∀ i, (W.U i).Nonempty)
    (hkn : k ≤ next) (hCC' : C ≤ C') (hC' : 1 ≤ C')
    (hpp' : p ≤ p') (hdelta : delta ≤ 1) (hbb' : b ≤ b')
    (hnew : ∀ T : TripleOn V,
      delta ≤ p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0)) :
    IsReserveStronglyWellDistributed (L.jointBind K) W next
      (jointInitial initial) (jointLater later added) (fun z ↦ reserve z.1)
      p' reserveDensity (2 * C') b' := by
  apply hstrong.jointBind_adjoin_preserve added
    (fun Q ↦ delta ^ Q.card) hadded
  intro Ifix Dfix Efix Rfix _hdisj S hS
  have hSD : S ⊆ Dfix := mem_powerset.mp hS
  have hcard : Dfix.card = S.card + (Dfix \ S).card := by
    rw [← card_sdiff_add_card_eq_card hSD]
    omega
  apply reservePreservingPartitionTerm_le p p' delta reserveDensity C C'
    b b' ((Fintype.card V : ℝ≥0)⁻¹)
    (laterTriangleScale W k p S) (laterTriangleScale W next p' Dfix)
    Ifix.card S.card Efix.card Rfix.card (Dfix \ S).card Dfix.card
    hcard hCC' hC' hpp' hdelta hbb'
  exact laterTriangleScale_mul_pow_le W k next p p' delta Dfix S hSD
    (fun T _hTS ↦ W.laterTrianglePointScale_mono hnonempty hkn hpp' T)
    (fun T _hTnew ↦ hnew T)

end

end Erdos207
