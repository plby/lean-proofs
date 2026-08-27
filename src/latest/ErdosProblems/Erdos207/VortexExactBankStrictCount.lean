/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexExactBankCount

/-!
# The strict exact-bank profile estimate

For a singleton outside root and a nonempty exact absorber-bank part,
minimality saves one vertex globally.  If the outside remainder also has a
level-zero triangle, the prefix inequalities save the same unit at the first
vortex coordinate.  Together these are the `n / N` and `1 / n` savings in
the proof of KSSS Lemma 7.2 (WS4).
-/

namespace Erdos207

open Finset

noncomputable section

/-- Remove one unit from the first coordinate of a nonempty vortex profile. -/
def VortexProfile.dropFirst {m : ℕ} (t : VortexProfile (m + 1)) :
    VortexProfile (m + 1) :=
  Fin.cases (t 0 - 1) (fun i ↦ t i.succ)

@[simp]
lemma VortexProfile.dropFirst_zero {m : ℕ}
    (t : VortexProfile (m + 1)) : t.dropFirst 0 = t 0 - 1 := rfl

@[simp]
lemma VortexProfile.dropFirst_succ {m : ℕ}
    (t : VortexProfile (m + 1)) (i : Fin m) :
    t.dropFirst i.succ = t i.succ := rfl

lemma VortexProfile.dropFirst_mass_add_one {m : ℕ}
    (t : VortexProfile (m + 1)) (ht : 0 < t 0) :
    t.dropFirst.mass + 1 = t.mass := by
  unfold VortexProfile.mass
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [VortexProfile.dropFirst_zero, VortexProfile.dropFirst_succ]
  omega

lemma finPrefixSum_dropFirst_add_one {m k : ℕ}
    (t : VortexProfile (m + 1)) (ht : 0 < t 0) (hk : 0 < k) :
    finPrefixSum t.dropFirst k + 1 = finPrefixSum t k := by
  unfold finPrefixSum
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [VortexProfile.dropFirst_zero, VortexProfile.dropFirst_succ,
    Fin.val_zero, hk, if_true, Fin.val_succ]
  omega

/-- Removing the first profile unit removes exactly one factor of `|U₀|`. -/
lemma Vortex.profileScale_dropFirst {V : Type*} [Fintype V] [DecidableEq V]
    {m : ℕ} (W : Vortex V (m + 1)) (t : VortexProfile (m + 1))
    (ht : 0 < t 0) :
    (W.U 0).card * W.profileScale t.dropFirst = W.profileScale t := by
  unfold Vortex.profileScale
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [VortexProfile.dropFirst_zero, VortexProfile.dropFirst_succ,
    Fin.castSucc_zero]
  have hpow : (W.U 0).card ^ (t 0 - 1) * (W.U 0).card =
      (W.U 0).card ^ t 0 := by
    nth_rewrite 2 [show t 0 = (t 0 - 1) + 1 by omega]
    rw [pow_succ]
  calc
    (W.U 0).card *
        ((W.U 0).card ^ (t 0 - 1) *
          ∏ i : Fin m, (W.U i.succ.castSucc).card ^ t i.succ) =
        ((W.U 0).card ^ (t 0 - 1) * (W.U 0).card) *
          ∏ i : Fin m, (W.U i.succ.castSucc).card ^ t i.succ := by ring
    _ = (W.U 0).card ^ t 0 *
          ∏ i : Fin m, (W.U i.succ.castSucc).card ^ t i.succ := by rw [hpow]

/-- A singleton outside root together with a nonempty exact bank part spans
four fixed vertices, so at most `j-4` vertices remain free. -/
theorem exactBank_extraVertices_card_le_singleton_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    {rho j : ℕ} {B R S K E : TripleSystemOn V}
    (hrho : 5 ≤ rho) (hj : 4 ≤ j) (hjrho : j ≤ rho)
    (hRcard : R.card = 1) (hK : K.Nonempty)
    (hScard : S.card = j - 2) (hRS : R ⊆ S)
    (hE : IsErdosConfigOn rho E)
    (hEout : E \ B = S) (hEin : E ∩ B = K) :
    (verticesOn E \ verticesOn (R ∪ K)).card ≤ j - 4 := by
  let hS : S ∈ exactBankOutsideExtensions rho j B R K :=
    mem_exactBankOutsideExtensions_iff.mpr
      ⟨hScard, hRS, E, hE, hEout, hEin⟩
  have hKcard : K.card = rho - j :=
    exactBankOutsideExtensions_bank_card (by omega) (by omega) hjrho hS
  have hQcard : (R ∪ K).card = R.card + K.card :=
    exactBankOutsideExtensions_root_union_card hS
  have hQsubE : R ∪ K ⊆ E := by
    intro T hT
    rcases mem_union.mp hT with hTR | hTK
    · have hTS := hRS hTR
      exact (mem_sdiff.mp (by rw [hEout]; exact hTS)).1
    · exact (mem_inter.mp (by rw [hEin]; exact hTK)).1
  have hspanE : (verticesOn E).card = rho :=
    IsErdosConfig.vertices_card_eq hE hrho
  have hextra : (verticesOn E \ verticesOn (R ∪ K)).card =
      rho - (verticesOn (R ∪ K)).card := by
    rw [card_sdiff_of_subset (verticesOn_mono hQsubE), hspanE]
  have hroot2 : 2 ≤ (R ∪ K).card := by
    have hKpos : 1 ≤ K.card := card_pos.mpr hK
    rw [hQcard, hRcard]
    omega
  have hrootsmall : (R ∪ K).card ≤ rho - 3 := by
    rw [hQcard, hRcard, hKcard]
    omega
  have hspan := exactBankOutsideExtensions_root_span
    hroot2 hrootsmall hS
  rw [hextra]
  omega

/-- Strict cumulative profile domination for the WS4 support branch. -/
theorem exactBank_vertexProfile_prefix_singleton_nonempty
    {V : Type*} [Fintype V] [DecidableEq V] {m rho j : ℕ}
    (W : Vortex V (m + 1)) {B R S K E : TripleSystemOn V}
    (hrho : 5 ≤ rho) (hj : 4 ≤ j) (hjrho : j ≤ rho)
    (hRcard : R.card = 1) (hK : K.Nonempty)
    (hScard : S.card = j - 2) (hRS : R ⊆ S)
    (hE : IsErdosConfigOn rho E)
    (hEout : E \ B = S) (hEin : E ∩ B = K)
    (t : VortexProfile (m + 1)) (ht : W.outerProfile (S \ R) = t)
    (ht0 : 0 < t 0) :
    let extra := verticesOn E \ verticesOn (R ∪ K)
    let bound := j - 4
    (∑ i, W.vertexProfile extra i) ≤ bound ∧
      FinPrefixLe
        (padTerminalExponent (W.vertexProfile extra)
          (max bound t.dropFirst.mass))
        (profileExponentVector bound t.dropFirst) := by
  dsimp only
  let extra := verticesOn E \ verticesOn (R ∪ K)
  let bound := j - 4
  have hextraBound : extra.card ≤ bound :=
    exactBank_extraVertices_card_le_singleton_nonempty
      hrho hj hjrho hRcard hK hScard hRS hE hEout hEin
  have hvsum : (∑ i, W.vertexProfile extra i) = extra.card := by
    exact W.sum_vertexProfile extra
  refine ⟨by rw [hvsum]; exact hextraBound, ?_⟩
  intro k
  by_cases hk : k ≤ m + 1
  · rw [finPrefixSum_padTerminalExponent_of_le _ hk,
      finPrefixSum_profileExponentVector_of_le _ hk]
    by_cases hk0 : k = 0
    · subst k
      simp [finPrefixSum]
    have hkpos : 0 < k := by omega
    have hdrop := finPrefixSum_dropFirst_add_one t ht0 hkpos
    let A := W.verticesBefore extra k
    have hAE : A ⊆ verticesOn E := by
      intro x hx
      exact (mem_sdiff.mp ((W.mem_verticesBefore_iff extra x).mp hx).1).1
    have hAextra : A ⊆ extra := fun x hx ↦
      (W.mem_verticesBefore_iff extra x).mp hx |>.1
    have hAcard : A.card ≤ rho - 4 := by
      have := (card_le_card hAextra).trans hextraBound
      dsimp only [bound] at this
      omega
    have htouch : trianglesTouching E A ⊆
        W.trianglesBefore (E \ (R ∪ K)) k :=
      W.trianglesTouching_verticesBefore_subset E (R ∪ K)
    have hdiff : E \ (R ∪ K) = S \ R :=
      exactBank_sdiff_root_union hRS hEout hEin
    have hplus : A.card + 1 ≤ (W.trianglesBefore (S \ R) k).card := by
      by_cases hAempty : A = ∅
      · have ht0le : t 0 ≤ finPrefixSum t k := by
          unfold finPrefixSum
          have hsingle := single_le_sum
            (fun i (_hi : i ∈ (univ : Finset (Fin (m + 1)))) ↦
              Nat.zero_le (if i.val < k then t i else 0))
            (mem_univ (0 : Fin (m + 1)))
          simpa only [Fin.val_zero, hkpos, if_true] using hsingle
        have hone : 1 ≤ finPrefixSum t k := ht0.trans_le ht0le
        rw [hAempty, card_empty, zero_add]
        rw [← W.finPrefixSum_outerProfile (S \ R) hk, ht]
        exact hone
      · have hApos : 1 ≤ A.card :=
          Nat.one_le_iff_ne_zero.mpr (fun h ↦ hAempty (card_eq_zero.mp h))
        have hstrict := IsErdosConfig.card_add_one_le_trianglesTouching
          hE hrho A hAE hApos hAcard
        calc
          A.card + 1 ≤ (trianglesTouching E A).card := hstrict
          _ ≤ (W.trianglesBefore (E \ (R ∪ K)) k).card :=
            card_le_card htouch
          _ = (W.trianglesBefore (S \ R) k).card := by rw [hdiff]
    have hplus' : A.card + 1 ≤ finPrefixSum t k := by
      rw [← ht, W.finPrefixSum_outerProfile (S \ R) hk]
      exact hplus
    rw [W.finPrefixSum_vertexProfile extra k]
    change A.card ≤ finPrefixSum t.dropFirst k
    omega
  · have hkfull : m + 2 ≤ k := by omega
    rw [finPrefixSum_eq_sum_of_length_le _ hkfull,
      finPrefixSum_eq_sum_of_length_le _ hkfull,
      sum_padTerminalExponent (by
        rw [hvsum]
        exact hextraBound.trans (le_max_left _ _)),
      sum_profileExponentVector]

/-- One fixed nonempty bank class in the WS4 support branch has the full
ambient inverse saving.  Multiplication by `|U₀|` avoids natural-number
division in the statement. -/
theorem card_exactBankProfiledExtensions_mul_root_le_strict
    {V : Type*} [Fintype V] [DecidableEq V] {m rho j : ℕ}
    (W : Vortex V (m + 1)) {B R K : TripleSystemOn V}
    (t : VortexProfile (m + 1))
    (hrho : 5 ≤ rho) (hj : 4 ≤ j) (hjrho : j ≤ rho)
    (hRcard : R.card = 1) (hK : K.Nonempty) (ht0 : 0 < t 0)
    (hterminal : 0 < W.terminalSize) :
    (W.U 0).card * (exactBankProfiledExtensions W rho j B R K t).card ≤
      exactBankVortexCoefficient rho (m + 1) *
        W.terminalSize ^ (j - t.mass - 3) * W.profileScale t := by
  let F := exactBankProfiledExtensions W rho j B R K t
  let code : TripleSystemOn V → VortexVertexProfile (m + 1) :=
    exactBankVertexProfile W R K
  let target := W.terminalSize ^ (j - t.mass - 3) *
    W.profileScale t.dropFirst
  have hprofile : ∀ v ∈ F.image code,
      (F.filter fun S ↦ code S = v).card ≤
        2 ^ (rho ^ 3) * target := by
    intro v hv
    obtain ⟨S, hSF, hcode⟩ := mem_image.mp hv
    have hmem := mem_exactBankProfiledExtensions_iff.mp hSF
    have hdata := mem_exactBankOutsideExtensions_iff.mp hmem.1
    have hc := exactBank_completion_data hmem.1
    have hp := exactBank_vertexProfile_prefix_singleton_nonempty W
      hrho hj hjrho hRcard hK hdata.1 hdata.2.1 hc.1 hc.2.1 hc.2.2
      t hmem.2 ht0
    have hmono := W.vertexProfileMonomial_le
      (exactBankVertexProfile W R K S) t.dropFirst hp.1 hterminal hp.2
    change exactBankVertexProfile W R K S = v at hcode
    rw [hcode] at hmono
    calc
      (F.filter fun S ↦ code S = v).card ≤
          2 ^ (rho ^ 3) *
            ∏ i : Fin (m + 2), (W.U i).card ^ v i :=
        card_exactBank_profile_fiber_le W hrho v
      _ ≤ 2 ^ (rho ^ 3) * target := by
        dsimp only [target]
        have hmass := VortexProfile.dropFirst_mass_add_one t ht0
        have hexp : j - 4 - t.dropFirst.mass = j - t.mass - 3 := by
          omega
        rw [← hexp]
        gcongr
  have hprofiles : F.image code ⊆ vortexProfileBox (m + 2) rho := by
    intro v hv
    obtain ⟨S, hSF, rfl⟩ := mem_image.mp hv
    rw [mem_vortexProfileBox_iff]
    intro i
    have hmem := mem_exactBankProfiledExtensions_iff.mp hSF
    have hE := (exactBank_completion_data hmem.1).1
    calc
      exactBankVertexProfile W R K S i ≤
          (exactBankExtraVertices R K S).card :=
        card_le_card inter_subset_left
      _ ≤ (verticesOn (S ∪ K)).card := card_le_card sdiff_subset
      _ = rho := IsErdosConfig.vertices_card_eq hE hrho
  have hcard : F.card ≤ exactBankVortexCoefficient rho (m + 1) * target := by
    calc
      F.card ≤ (2 ^ (rho ^ 3) * target) * (F.image code).card :=
        card_le_mul_card_image F _ hprofile
      _ ≤ (2 ^ (rho ^ 3) * target) * (rho + 1) ^ (m + 2) := by
        gcongr
        calc
          (F.image code).card ≤ (vortexProfileBox (m + 2) rho).card :=
            card_le_card hprofiles
          _ = (rho + 1) ^ (m + 2) := card_vortexProfileBox _ _
      _ = exactBankVortexCoefficient rho (m + 1) * target := by
        dsimp only [exactBankVortexCoefficient]
        ring
  calc
    (W.U 0).card * F.card ≤
        (W.U 0).card *
          (exactBankVortexCoefficient rho (m + 1) * target) := by gcongr
    _ = exactBankVortexCoefficient rho (m + 1) *
        W.terminalSize ^ (j - t.mass - 3) * W.profileScale t := by
      dsimp only [target]
      rw [← W.profileScale_dropFirst t ht0]
      ring

/-- With a nonempty exact bank part, every nonempty outside root leaves at
most `rho - 4` vertices free.  For a singleton root this is the extra global
strictness used by WS4; for a larger root it follows from the ordinary KSSS
root exponent. -/
theorem exactBank_extraVertices_card_le_four_of_bank_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    {rho j : ℕ} {B R S K E : TripleSystemOn V}
    (hrho : 5 ≤ rho) (hj : 4 ≤ j) (hjrho : j ≤ rho)
    (hR : R.Nonempty) (hRcard : R.card ≤ j - 2) (hK : K.Nonempty)
    (hScard : S.card = j - 2) (hRS : R ⊆ S)
    (hE : IsErdosConfigOn rho E)
    (hEout : E \ B = S) (hEin : E ∩ B = K) :
    (verticesOn E \ verticesOn (R ∪ K)).card ≤ rho - 4 := by
  by_cases hRone : R.card = 1
  · exact (exactBank_extraVertices_card_le_singleton_nonempty
      hrho hj hjrho hRone hK hScard hRS hE hEout hEin).trans (by omega)
  · have hRtwo : 2 ≤ R.card := by
      have hRpos : 0 < R.card := card_pos.mpr hR
      omega
    have hrootFour : 4 ≤ vortexRootExponent j R.card :=
      (by omega : 4 ≤ R.card + 2).trans
        (add_two_le_vortexRootExponent j R.card)
    have hgeneric := exactBank_extraVertices_card_le
      hrho (by omega : 3 ≤ j) hjrho hR hRcard hScard hRS hE hEout hEin
    omega

/-- Strict cumulative profile domination in the nonlocal support branch of
W1.  One unit is removed from the first profile coordinate. -/
theorem exactBank_vertexProfile_prefix_nonempty_bank
    {V : Type*} [Fintype V] [DecidableEq V] {m rho j : ℕ}
    (W : Vortex V (m + 1)) {B R S K E : TripleSystemOn V}
    (hrho : 5 ≤ rho) (hj : 4 ≤ j) (hjrho : j ≤ rho)
    (hR : R.Nonempty) (hRcard : R.card ≤ j - 2) (hK : K.Nonempty)
    (hScard : S.card = j - 2) (hRS : R ⊆ S)
    (hE : IsErdosConfigOn rho E)
    (hEout : E \ B = S) (hEin : E ∩ B = K)
    (t : VortexProfile (m + 1)) (ht : W.outerProfile (S \ R) = t)
    (ht0 : 0 < t 0) :
    let extra := verticesOn E \ verticesOn (R ∪ K)
    let bound := j - vortexRootExponent j R.card
    (∑ i, W.vertexProfile extra i) ≤ bound ∧
      FinPrefixLe
        (padTerminalExponent (W.vertexProfile extra)
          (max bound t.dropFirst.mass))
        (profileExponentVector bound t.dropFirst) := by
  dsimp only
  let extra := verticesOn E \ verticesOn (R ∪ K)
  let bound := j - vortexRootExponent j R.card
  have hextraBound : extra.card ≤ bound :=
    exactBank_extraVertices_card_le hrho (by omega : 3 ≤ j) hjrho
      hR hRcard hScard hRS hE hEout hEin
  have hextraFour : extra.card ≤ rho - 4 :=
    exactBank_extraVertices_card_le_four_of_bank_nonempty
      hrho hj hjrho hR hRcard hK hScard hRS hE hEout hEin
  have hvsum : (∑ i, W.vertexProfile extra i) = extra.card :=
    W.sum_vertexProfile extra
  refine ⟨by rw [hvsum]; exact hextraBound, ?_⟩
  intro k
  by_cases hk : k ≤ m + 1
  · rw [finPrefixSum_padTerminalExponent_of_le _ hk,
      finPrefixSum_profileExponentVector_of_le _ hk]
    by_cases hk0 : k = 0
    · subst k
      simp [finPrefixSum]
    have hkpos : 0 < k := by omega
    have hdrop := finPrefixSum_dropFirst_add_one t ht0 hkpos
    let A := W.verticesBefore extra k
    have hAE : A ⊆ verticesOn E := by
      intro x hx
      exact (mem_sdiff.mp ((W.mem_verticesBefore_iff extra x).mp hx).1).1
    have hAextra : A ⊆ extra := fun x hx ↦
      (W.mem_verticesBefore_iff extra x).mp hx |>.1
    have hAcard : A.card ≤ rho - 4 :=
      (card_le_card hAextra).trans hextraFour
    have htouch : trianglesTouching E A ⊆
        W.trianglesBefore (E \ (R ∪ K)) k :=
      W.trianglesTouching_verticesBefore_subset E (R ∪ K)
    have hdiff : E \ (R ∪ K) = S \ R :=
      exactBank_sdiff_root_union hRS hEout hEin
    have hplus : A.card + 1 ≤ (W.trianglesBefore (S \ R) k).card := by
      by_cases hAempty : A = ∅
      · have ht0le : t 0 ≤ finPrefixSum t k := by
          unfold finPrefixSum
          have hsingle := single_le_sum
            (fun i (_hi : i ∈ (univ : Finset (Fin (m + 1)))) ↦
              Nat.zero_le (if i.val < k then t i else 0))
            (mem_univ (0 : Fin (m + 1)))
          simpa only [Fin.val_zero, hkpos, if_true] using hsingle
        have hone : 1 ≤ finPrefixSum t k := ht0.trans_le ht0le
        rw [hAempty, card_empty, zero_add]
        rw [← W.finPrefixSum_outerProfile (S \ R) hk, ht]
        exact hone
      · have hApos : 1 ≤ A.card :=
          Nat.one_le_iff_ne_zero.mpr (fun h ↦ hAempty (card_eq_zero.mp h))
        have hstrict := IsErdosConfig.card_add_one_le_trianglesTouching
          hE hrho A hAE hApos hAcard
        calc
          A.card + 1 ≤ (trianglesTouching E A).card := hstrict
          _ ≤ (W.trianglesBefore (E \ (R ∪ K)) k).card :=
            card_le_card htouch
          _ = (W.trianglesBefore (S \ R) k).card := by rw [hdiff]
    have hplus' : A.card + 1 ≤ finPrefixSum t k := by
      rw [← ht, W.finPrefixSum_outerProfile (S \ R) hk]
      exact hplus
    rw [W.finPrefixSum_vertexProfile extra k]
    change A.card ≤ finPrefixSum t.dropFirst k
    omega
  · have hkfull : m + 2 ≤ k := by omega
    rw [finPrefixSum_eq_sum_of_length_le _ hkfull,
      finPrefixSum_eq_sum_of_length_le _ hkfull,
      sum_padTerminalExponent (by
        rw [hvsum]
        exact hextraBound.trans (le_max_left _ _)),
      sum_profileExponentVector]

/-- A fixed nonempty bank class in the nonlocal W1 branch saves one ambient
root factor.  The remaining terminal exponent is stated using `dropFirst` so
no truncated-subtraction side condition is needed. -/
theorem card_exactBankProfiledExtensions_mul_root_le_nonempty_bank
    {V : Type*} [Fintype V] [DecidableEq V] {m rho j : ℕ}
    (W : Vortex V (m + 1)) {B R K : TripleSystemOn V}
    (t : VortexProfile (m + 1))
    (hrho : 5 ≤ rho) (hj : 4 ≤ j) (hjrho : j ≤ rho)
    (hR : R.Nonempty) (hRcard : R.card ≤ j - 2)
    (hK : K.Nonempty) (ht0 : 0 < t 0)
    (hterminal : 0 < W.terminalSize) :
    (W.U 0).card * (exactBankProfiledExtensions W rho j B R K t).card ≤
      exactBankVortexCoefficient rho (m + 1) *
        W.terminalSize ^
          ((j - vortexRootExponent j R.card) - t.dropFirst.mass) *
        W.profileScale t := by
  let F := exactBankProfiledExtensions W rho j B R K t
  let code : TripleSystemOn V → VortexVertexProfile (m + 1) :=
    exactBankVertexProfile W R K
  let target := W.terminalSize ^
      ((j - vortexRootExponent j R.card) - t.dropFirst.mass) *
    W.profileScale t.dropFirst
  have hprofile : ∀ v ∈ F.image code,
      (F.filter fun S ↦ code S = v).card ≤
        2 ^ (rho ^ 3) * target := by
    intro v hv
    obtain ⟨S, hSF, hcode⟩ := mem_image.mp hv
    have hmem := mem_exactBankProfiledExtensions_iff.mp hSF
    have hdata := mem_exactBankOutsideExtensions_iff.mp hmem.1
    have hc := exactBank_completion_data hmem.1
    have hp := exactBank_vertexProfile_prefix_nonempty_bank W
      hrho hj hjrho hR hRcard hK hdata.1 hdata.2.1
        hc.1 hc.2.1 hc.2.2 t hmem.2 ht0
    have hmono := W.vertexProfileMonomial_le
      (exactBankVertexProfile W R K S) t.dropFirst hp.1 hterminal hp.2
    change exactBankVertexProfile W R K S = v at hcode
    rw [hcode] at hmono
    calc
      (F.filter fun S ↦ code S = v).card ≤
          2 ^ (rho ^ 3) *
            ∏ i : Fin (m + 2), (W.U i).card ^ v i :=
        card_exactBank_profile_fiber_le W hrho v
      _ ≤ 2 ^ (rho ^ 3) * target := by
        dsimp only [target]
        gcongr
  have hprofiles : F.image code ⊆ vortexProfileBox (m + 2) rho := by
    intro v hv
    obtain ⟨S, hSF, rfl⟩ := mem_image.mp hv
    rw [mem_vortexProfileBox_iff]
    intro i
    have hmem := mem_exactBankProfiledExtensions_iff.mp hSF
    have hE := (exactBank_completion_data hmem.1).1
    calc
      exactBankVertexProfile W R K S i ≤
          (exactBankExtraVertices R K S).card :=
        card_le_card inter_subset_left
      _ ≤ (verticesOn (S ∪ K)).card := card_le_card sdiff_subset
      _ = rho := IsErdosConfig.vertices_card_eq hE hrho
  have hcard : F.card ≤
      exactBankVortexCoefficient rho (m + 1) * target := by
    calc
      F.card ≤ (2 ^ (rho ^ 3) * target) * (F.image code).card :=
        card_le_mul_card_image F _ hprofile
      _ ≤ (2 ^ (rho ^ 3) * target) * (rho + 1) ^ (m + 2) := by
        gcongr
        calc
          (F.image code).card ≤ (vortexProfileBox (m + 2) rho).card :=
            card_le_card hprofiles
          _ = (rho + 1) ^ (m + 2) := card_vortexProfileBox _ _
      _ = exactBankVortexCoefficient rho (m + 1) * target := by
        dsimp only [exactBankVortexCoefficient]
        ring
  calc
    (W.U 0).card * F.card ≤
        (W.U 0).card *
          (exactBankVortexCoefficient rho (m + 1) * target) := by gcongr
    _ = exactBankVortexCoefficient rho (m + 1) *
        W.terminalSize ^
          ((j - vortexRootExponent j R.card) - t.dropFirst.mass) *
        W.profileScale t := by
      dsimp only [target]
      rw [← W.profileScale_dropFirst t ht0]
      ring

end

end Erdos207
