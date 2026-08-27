/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexExactBank

/-! # Profiled counting in one exact absorber-bank class -/

namespace Erdos207

open Finset

noncomputable section

def exactBankProfiledExtensions
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (rho j : ℕ) (B R K : TripleSystemOn V)
    (t : VortexProfile ell) : ForbiddenFamilyOn V :=
  (exactBankOutsideExtensions rho j B R K).filter fun S ↦
    W.outerProfile (S \ R) = t

@[simp]
lemma mem_exactBankProfiledExtensions_iff
    {V : Type*} [Fintype V] [DecidableEq V] {ell rho j : ℕ}
    {W : Vortex V ell} {B R K S : TripleSystemOn V}
    {t : VortexProfile ell} :
    S ∈ exactBankProfiledExtensions W rho j B R K t ↔
      S ∈ exactBankOutsideExtensions rho j B R K ∧
        W.outerProfile (S \ R) = t := by
  simp [exactBankProfiledExtensions]

def exactBankExtraVertices
    {V : Type*} [DecidableEq V]
    (R K S : TripleSystemOn V) : Finset V :=
  verticesOn (S ∪ K) \ verticesOn (R ∪ K)

def exactBankVertexProfile
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (R K S : TripleSystemOn V) :
    VortexVertexProfile ell :=
  W.vertexProfile (exactBankExtraVertices R K S)

lemma exactBank_completion_data
    {V : Type*} [Fintype V] [DecidableEq V]
    {rho j : ℕ} {B R K S : TripleSystemOn V}
    (hS : S ∈ exactBankOutsideExtensions rho j B R K) :
    IsErdosConfigOn rho (S ∪ K) ∧
      (S ∪ K) \ B = S ∧ (S ∪ K) ∩ B = K := by
  obtain ⟨_hScard, _hRS, E, hE, hEout, hEin⟩ :=
    mem_exactBankOutsideExtensions_iff.mp hS
  have hdecomp : E = S ∪ K := exactBank_decomposition hEout hEin
  subst E
  exact ⟨hE, hEout, hEin⟩

lemma exactBank_root_subset_completion
    {V : Type*} [Fintype V] [DecidableEq V]
    {rho j : ℕ} {B R K S : TripleSystemOn V}
    (hS : S ∈ exactBankOutsideExtensions rho j B R K) :
    R ∪ K ⊆ S ∪ K := by
  have hRS := (mem_exactBankOutsideExtensions_iff.mp hS).2.1
  exact union_subset_union hRS Subset.rfl

lemma verticesOn_completion_eq_root_union_extra
    {V : Type*} [Fintype V] [DecidableEq V]
    {rho j : ℕ} {B R K S : TripleSystemOn V}
    (hS : S ∈ exactBankOutsideExtensions rho j B R K) :
    verticesOn (R ∪ K) ∪ exactBankExtraVertices R K S =
      verticesOn (S ∪ K) := by
  exact union_sdiff_of_subset
    (verticesOn_mono (exactBank_root_subset_completion hS))

/-- Once its extra vertex set is fixed, an exact-bank extension has only a
bounded number of possible triple systems. -/
lemma card_exactBank_extraVertices_fiber_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell rho j : ℕ} {W : Vortex V ell} {B R K : TripleSystemOn V}
    {t : VortexProfile ell} (hrho : 5 ≤ rho) (A : Finset V) :
    ((exactBankProfiledExtensions W rho j B R K t).filter fun S ↦
        exactBankExtraVertices R K S = A).card ≤ 2 ^ (rho ^ 3) := by
  let G := (exactBankProfiledExtensions W rho j B R K t).filter fun S ↦
    exactBankExtraVertices R K S = A
  by_cases hG : G.Nonempty
  · obtain ⟨S₀, hS₀G⟩ := hG
    have hm₀ := mem_filter.mp hS₀G
    have hS₀ := (mem_exactBankProfiledExtensions_iff.mp hm₀.1).1
    have hE₀ := (exactBank_completion_data hS₀).1
    have hspan : (verticesOn (R ∪ K) ∪ A).card = rho := by
      rw [← hm₀.2, verticesOn_completion_eq_root_union_extra hS₀]
      exact IsErdosConfig.vertices_card_eq hE₀ hrho
    have hsub : G ⊆ tripleSystemsSupportedOn (verticesOn (R ∪ K) ∪ A) := by
      intro S hSG
      have hm := mem_filter.mp hSG
      have hS := (mem_exactBankProfiledExtensions_iff.mp hm.1).1
      apply mem_tripleSystemsSupportedOn_iff.mpr
      calc
        verticesOn S ⊆ verticesOn (S ∪ K) :=
          verticesOn_mono (subset_union_left)
        _ = verticesOn (R ∪ K) ∪ exactBankExtraVertices R K S :=
          (verticesOn_completion_eq_root_union_extra hS).symm
        _ = verticesOn (R ∪ K) ∪ A := by rw [hm.2]
    calc
      G.card ≤ (tripleSystemsSupportedOn (verticesOn (R ∪ K) ∪ A)).card :=
        card_le_card hsub
      _ ≤ 2 ^ ((verticesOn (R ∪ K) ∪ A).card ^ 3) :=
        card_tripleSystemsSupportedOn_le _
      _ = 2 ^ (rho ^ 3) := by rw [hspan]
  · change G.card ≤ _
    rw [not_nonempty_iff_eq_empty.mp hG]
    simp

/-- For one fixed vertex profile, the extra vertex set and the bounded
hypergraph code give the expected monomial count. -/
lemma card_exactBank_profile_fiber_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell rho j : ℕ} (W : Vortex V ell) {B R K : TripleSystemOn V}
    {t : VortexProfile ell} (hrho : 5 ≤ rho)
    (v : VortexVertexProfile ell) :
    ((exactBankProfiledExtensions W rho j B R K t).filter fun S ↦
        exactBankVertexProfile W R K S = v).card ≤
      2 ^ (rho ^ 3) *
        ∏ i : Fin (ell + 1), (W.U i).card ^ v i := by
  let G := (exactBankProfiledExtensions W rho j B R K t).filter fun S ↦
    exactBankVertexProfile W R K S = v
  let code : TripleSystemOn V → Finset V := exactBankExtraVertices R K
  have hfiber : ∀ A ∈ G.image code,
      (G.filter fun S ↦ code S = A).card ≤ 2 ^ (rho ^ 3) := by
    intro A _hA
    calc
      (G.filter fun S ↦ code S = A).card ≤
          ((exactBankProfiledExtensions W rho j B R K t).filter fun S ↦
            exactBankExtraVertices R K S = A).card := by
        apply card_le_card
        intro S hS
        obtain ⟨hSG, hcodeA⟩ := mem_filter.mp hS
        have hbase : S ∈ exactBankProfiledExtensions W rho j B R K t := by
          change S ∈ (exactBankProfiledExtensions W rho j B R K t).filter
            (fun T ↦ exactBankVertexProfile W R K T = v) at hSG
          exact (mem_filter.mp hSG).1
        apply mem_filter.mpr
        refine ⟨hbase, ?_⟩
        simpa only [code] using hcodeA
      _ ≤ 2 ^ (rho ^ 3) := card_exactBank_extraVertices_fiber_le hrho A
  have himage : G.image code ⊆ W.vertexSetsWithProfile v := by
    intro A hA
    obtain ⟨S, hSG, rfl⟩ := mem_image.mp hA
    apply W.mem_vertexSetsWithProfile_iff v _ |>.mpr
    exact (mem_filter.mp hSG).2
  calc
    G.card ≤ 2 ^ (rho ^ 3) * (G.image code).card :=
      card_le_mul_card_image G _ hfiber
    _ ≤ 2 ^ (rho ^ 3) * (W.vertexSetsWithProfile v).card := by
      exact Nat.mul_le_mul_left _ (card_le_card himage)
    _ ≤ 2 ^ (rho ^ 3) *
        ∏ i : Fin (ell + 1), (W.U i).card ^ v i := by
      exact Nat.mul_le_mul_left _ (W.card_vertexSetsWithProfile_le v)

/-- Explicit coefficient for the exact-bank profiled count. -/
def exactBankVortexCoefficient (rho ell : ℕ) : ℕ :=
  (rho + 1) ^ (ell + 1) * 2 ^ (rho ^ 3)

/-- Exact profiled extension count for one fixed bank part. -/
theorem card_exactBankProfiledExtensions_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell rho j : ℕ}
    (W : Vortex V ell) {B R K : TripleSystemOn V}
    (t : VortexProfile ell)
    (hrho : 5 ≤ rho) (hj : 3 ≤ j) (hjrho : j ≤ rho)
    (hR : R.Nonempty) (hRcard : R.card ≤ j - 2)
    (hterminal : 0 < W.terminalSize) :
    (exactBankProfiledExtensions W rho j B R K t).card ≤
      exactBankVortexCoefficient rho ell *
        W.terminalSize ^
          (j - t.mass - vortexRootExponent j R.card) *
        W.profileScale t := by
  let F := exactBankProfiledExtensions W rho j B R K t
  let code : TripleSystemOn V → VortexVertexProfile ell :=
    exactBankVertexProfile W R K
  let target := W.terminalSize ^
      (j - t.mass - vortexRootExponent j R.card) * W.profileScale t
  have hprofile : ∀ v ∈ F.image code,
      (F.filter fun S ↦ code S = v).card ≤ 2 ^ (rho ^ 3) * target := by
    intro v hv
    obtain ⟨S, hSF, hcode⟩ := mem_image.mp hv
    have hmem := mem_exactBankProfiledExtensions_iff.mp hSF
    have hdata := mem_exactBankOutsideExtensions_iff.mp hmem.1
    have hScard := hdata.1
    have hRS := hdata.2.1
    have hc := exactBank_completion_data hmem.1
    have hp := exactBank_vertexProfile_prefix W hrho hj hjrho hR hRcard
      hScard hRS hc.1 hc.2.1 hc.2.2 t hmem.2
    have hmono := W.vertexProfileMonomial_le
      (exactBankVertexProfile W R K S) t hp.1 hterminal hp.2
    change exactBankVertexProfile W R K S = v at hcode
    rw [hcode] at hmono
    calc
      (F.filter fun S ↦ code S = v).card ≤
          2 ^ (rho ^ 3) *
            ∏ i : Fin (ell + 1), (W.U i).card ^ v i :=
        card_exactBank_profile_fiber_le W hrho v
      _ ≤ 2 ^ (rho ^ 3) * target := by
        dsimp only [target]
        have hexp : j - t.mass - vortexRootExponent j R.card =
            (j - vortexRootExponent j R.card) - t.mass := by omega
        rw [hexp]
        gcongr
  have hprofiles : F.image code ⊆ vortexProfileBox (ell + 1) rho := by
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
      _ ≤ (verticesOn (S ∪ K)).card :=
        card_le_card sdiff_subset
      _ = rho := IsErdosConfig.vertices_card_eq hE hrho
  calc
    F.card ≤ (2 ^ (rho ^ 3) * target) * (F.image code).card :=
      card_le_mul_card_image F _ hprofile
    _ ≤ (2 ^ (rho ^ 3) * target) * (rho + 1) ^ (ell + 1) := by
      gcongr
      calc
        (F.image code).card ≤ (vortexProfileBox (ell + 1) rho).card :=
          card_le_card hprofiles
        _ = (rho + 1) ^ (ell + 1) := card_vortexProfileBox _ _
    _ = exactBankVortexCoefficient rho ell *
        W.terminalSize ^
          (j - t.mass - vortexRootExponent j R.card) *
        W.profileScale t := by
      dsimp only [target, exactBankVortexCoefficient]
      ring

end

end Erdos207
