import ErdosProblems.Erdos547.Transport
import ErdosProblems.Erdos547.LocalAllocationChanges

/-!
# Reserving tails before allocating heads

The tail and head sets may overlap. Reserving all tail load first prevents
incoming allocations from using space required by a later tail.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem exists_capped_reservation (a : V → ℝ) (ha : ∀ u, 0 ≤ a u)
    (κ : ℝ) (hκ : 0 ≤ κ) (hs : κ ≤ ∑ u, a u) :
    ∃ r : V → ℝ, (∀ u, 0 ≤ r u) ∧ (∀ u, r u ≤ a u) ∧ (∑ u, r u) = κ := by
  have hsum : 0 ≤ ∑ u, a u := Finset.sum_nonneg fun u _ ↦ ha u
  rcases hsum.eq_or_lt with he | hpos
  · have hk : κ = 0 := by linarith
    refine ⟨fun _ ↦ 0, fun _ ↦ le_rfl, ha, ?_⟩
    simp only [Finset.sum_const_zero, hk]
  · have hratio : κ / (∑ u, a u) ≤ 1 := (div_le_one hpos).mpr hs
    refine ⟨fun u ↦ (κ / (∑ v, a v)) * a u,
      fun u ↦ mul_nonneg (div_nonneg hκ hpos.le) (ha u),
      fun u ↦ (mul_le_mul_of_nonneg_right hratio (ha u)).trans_eq (one_mul _), ?_⟩
    rw [← Finset.mul_sum, div_mul_cancel₀ _ (ne_of_gt hpos)]

open scoped Classical in
theorem exists_allocation_with_reserved_tails (P : V → V → Prop)
    (hP : ∀ u v, P u v → G.Adj u v) (r b : V → ℝ)
    (hr : ∀ u, 0 ≤ r u) (hrb : ∀ u, r u ≤ b u) (hb : ∀ u, b u ≤ 1)
    (γ : ℝ) (hγ : 0 < γ)
    (hN : ∀ x, 0 < r x → γ * (∑ u, r u) ≤
      ∑ y ∈ Finset.univ.filter (P x), (b y - r y)) :
    ∃ σ : SkewMatching G γ, (∀ u, σ.outLoad u = r u) ∧
      (∀ u, σ.load u ≤ b u) ∧ (∀ u v, ¬ P u v → σ.weight u v = 0) ∧
      σ.total = (1 + γ) * (∑ u, r u) := by
  classical
  let cap := fun u ↦ (b u - r u) / γ
  have hcap (u : V) : 0 ≤ cap u := div_nonneg (sub_nonneg.mpr (hrb u)) hγ.le
  have hneigh (x : V) (hx : 0 < r x) : (∑ u, r u) ≤
      ∑ y ∈ Finset.univ.filter (P x), cap y := by
    change _ ≤ ∑ y ∈ Finset.univ.filter (P x), (b y - r y) / γ
    rw [← Finset.sum_div]
    apply (le_div_iff₀ hγ).mpr
    simpa only [mul_comm] using hN x hx
  obtain ⟨f, hrow⟩ := Transport.exists_full_rows P r cap hr hcap hneigh
  let raw := fun u v ↦ (1 + γ) * f.weight u v
  have hden : 1 + γ ≠ 0 := by linarith
  have hload (u : V) : SkewMatching.vertexLoadOf γ raw u = r u + γ * f.col u := by
    simp only [SkewMatching.vertexLoadOf, raw, ← Finset.mul_sum]
    change (1 + γ) * f.row u / (1 + γ) + γ * ((1 + γ) * f.col u) / (1 + γ) = _
    rw [hrow]
    field_simp [hden]
  have hcapacity (u : V) : SkewMatching.vertexLoadOf γ raw u ≤ b u := by
    rw [hload]
    have hh := (le_div_iff₀ hγ).mp (f.col_bound u)
    change f.col u * γ ≤ b u - r u at hh
    linarith
  let σ := SkewMatching.ofVertexLoad hγ.le raw
    (fun u v ↦ mul_nonneg (by linarith) (f.nonnegative u v))
    (fun u v huv ↦ by
      have hn : ¬ P u v := fun hp ↦ huv (hP u v hp)
      dsimp [raw]
      rw [f.supported u v hn, mul_zero])
    (fun u ↦ (hcapacity u).trans (hb u))
  have hout (u : V) : σ.outLoad u = r u := by
    change (∑ v, (1 + γ) * f.weight u v) / (1 + γ) = _
    rw [← Finset.mul_sum]
    change (1 + γ) * f.row u / (1 + γ) = _
    rw [hrow, mul_div_cancel_left₀ _ hden]
  refine ⟨σ, hout, hcapacity, ?_, ?_⟩
  · intro u v huv
    change (1 + γ) * f.weight u v = 0
    rw [f.supported u v huv, mul_zero]
  · have hh := σ.sum_outLoad
    simp_rw [hout] at hh
    have he := (eq_div_iff hden).mp hh
    linarith

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_capped_reservation
#print axioms Erdos547.DPRS.exists_allocation_with_reserved_tails
