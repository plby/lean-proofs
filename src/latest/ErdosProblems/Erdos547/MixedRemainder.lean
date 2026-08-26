import ErdosProblems.Erdos547.SkewBipartiteSupport
import ErdosProblems.Erdos547.SkewSplitting

/-!
# Keeping a prescribed skew budget and extracting its unused fractional part
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {δ : ℝ}

theorem exists_mixed_remainder (σ : SkewMatching G δ) (ν : FractionalMatching G)
    (U : Finset V) (hσ : σ.RunsFrom U) (hδ : 1 ≤ δ)
    (hcap : ∀ u, σ.load u + ν.load u ≤ 1)
    (hcover : ∀ u ∈ U, σ.load u + ν.load u = 1)
    (hzero : ∀ u ∈ U, ∀ v ∈ U, ν.weight u v = 0)
    (r : ℝ) (hr : 0 ≤ r) (hsize : r ≤ σ.total) :
    ∃ τ : SkewMatching G δ, ∃ F : FractionalMatching G,
      τ.IsSuballocation σ ∧ τ.total = r ∧
      (∀ u, F.load u + τ.load u ≤ 1) ∧
      (∀ u ∈ U, F.load u + τ.load u = 1) ∧
      ∀ u ∈ U, ∀ v ∈ U, F.weight u v = 0 := by
  obtain ⟨τ, ρ, hτ, hρ, htotal, _, hloads, _⟩ := σ.exists_split_total r hr hsize
  have hruns := hσ.of_suballocation hρ
  let Q := ρ.extractFractional hδ
  have hQ (u : V) : Q.load u ≤ ρ.load u := (ρ.extractFractional_dominated hδ).load_le u
  have hFcap (u : V) : ν.load u + Q.load u ≤ 1 := by
    linarith [hcap u, hloads u, hQ u, τ.load_nonneg u]
  let F := ν.add Q hFcap
  have hFload (u : V) : F.load u = ν.load u + Q.load u := FractionalMatching.add_load _ _ _ _
  refine ⟨τ, F, hτ, htotal, ?_, ?_, ?_⟩
  · intro u
    rw [hFload]
    linarith [hcap u, hloads u, hQ u]
  · intro u hu
    rw [hFload, show Q.load u = ρ.load u from hruns.extractFractional_load hδ hu]
    linarith [hcover u hu, hloads u]
  · intro u hu v hv
    change ν.weight u v + (ρ.weight u v + ρ.weight v u) / (1 + δ) = 0
    rw [hzero u hu v hv, hruns.incoming_zero hv u, hruns.incoming_zero hu v]
    simp only [add_zero, zero_div]

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_mixed_remainder
