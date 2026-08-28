import Wikipedia.NoExoticSixSphere.OrthogonalQuantitativeDescent
import Wikipedia.NoExoticSixSphere.QuantitativeCrossingLocalization
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Supported quantitative lowering near a noncritical polygon

A compact noncritical neighborhood supplies a fixed descent interval and
endpoint threshold. Localization then gives the same quantitative interface as
the critical crossing, for arbitrary admissible parameter families.
-/

open Set unitInterval
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.OrthogonalPolygon

open GLOrthonormalization OrthogonalVertexSpace

variable {n m : ℕ}

theorem exists_compact_noncritical_neighborhood (a b : OrthogonalOperators n)
    (τ : Fin (m + 2) → ℝ) (v : Space n m) (hv : v ∈ admissible a b m)
    (hn : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v ≠ 0)
    (N : Set (Space n m)) (hN : IsOpen N) (hvN : v ∈ N) :
    ∃ W K : Set (Space n m), IsOpen W ∧ v ∈ W ∧ W ⊆ K ∧ IsCompact K ∧
      K ⊆ admissible a b m ∩ N ∧
      ∀ z ∈ K, mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) z ≠ 0 := by
  let A := N ∩ (admissible a b m ∩ jumpSquareNorm a b τ ⁻¹' Ioi 0)
  have hj : ContinuousOn (jumpSquareNorm a b τ) (admissible a b m) :=
    fun z hz ↦ (continuousAt_jumpSquareNorm a b τ hz).continuousWithinAt
  have hA : IsOpen A := hN.inter
    (hj.isOpen_inter_preimage (isOpen_admissible a b m) isOpen_Ioi)
  have hvA : v ∈ A := ⟨hvN, hv, jumpSquareNorm_pos_of_noncritical a b τ v hv hn⟩
  have hzero : (0 : Model n m) ∈ (atVertices v).symm ⁻¹' A := by
    change (atVertices v).symm 0 ∈ A
    rwa [atVertices_symm_zero]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((hA.preimage (contMDiff_atVertices_symm v).continuous).mem_nhds hzero)
  let K := (atVertices v).symm '' Metric.closedBall 0 (r / 2)
  let W := (atVertices v).source ∩ (atVertices v) ⁻¹' Metric.ball 0 (r / 2)
  have hK : IsCompact K := (isCompact_closedBall (0 : Model n m) (r / 2)).image
    (contMDiff_atVertices_symm v).continuous
  have hKA : K ⊆ A := by
    rintro _ ⟨z, hz, rfl⟩
    exact hball (Metric.closedBall_subset_ball (by linarith : r / 2 < r) hz)
  refine ⟨W, K, (atVertices v).isOpen_inter_preimage Metric.isOpen_ball,
    ⟨mem_atVertices_source v, ?_⟩, ?_, hK,
    (fun z hz ↦ ⟨(hKA hz).2.1, (hKA hz).1⟩), ?_⟩
  · change atVertices v v ∈ Metric.ball 0 (r / 2)
    rw [atVertices_self]
    exact Metric.mem_ball_self (by positivity)
  · intro z hz
    exact ⟨atVertices v z, Metric.ball_subset_closedBall hz.2, (atVertices v).left_inv hz.1⟩
  · intro z hz hcrit
    have hpos := (hKA hz).2.2
    have heq : jumpSquareNorm a b τ z = 0 := (jumpSquareNorm_eq_zero_iff a b τ z).mpr
      ((mfderiv_energy_eq_zero_iff a b τ z (hKA hz).2.1).mp hcrit)
    exact (ne_of_gt hpos) heq

theorem exists_quantitative_noncritical_crossing {M : Type*}
    [TopologicalSpace M] [CompactSpace M] [T2Space M]
    (a b : OrthogonalOperators n) (τ : Fin (m + 2) → ℝ)
    (v : Space n m) (hv : v ∈ admissible a b m)
    (hn : mfderiv 𝓘(ℝ, Model n m) 𝓘(ℝ, ℝ) (energy a b τ) v ≠ 0)
    (N : Set (Space n m)) (hN : IsOpen N) (hvN : v ∈ N)
    (l ε : ℝ) (hl : l < energy a b τ v) (hε : 0 < ε) :
    ∃ V : Set (Space n m), IsOpen V ∧ v ∈ V ∧ V ⊆ admissible a b m ∩ N ∧
      (∀ z ∈ V, l < energy a b τ z) ∧
      ∃ k : ℝ, l < k ∧ k < energy a b τ v ∧
        ∀ ρ > 0, ∃ ζ > 0, ∀ ξ : ℝ, 0 < ξ → ξ ≤ ζ →
          ∀ (p : C(M, Space n m)), (∀ x, p x ∈ admissible a b m) →
            ∀ (K : Set M), IsCompact K → K ⊆ p ⁻¹' V →
              ∃ q : C(M, Space n m), (∀ x ∈ K, energy a b τ (q x) < k) ∧
                ∃ G : ContinuousMap.HomotopyRel p q
                  ({x | energy a b τ (p x) ≤ l} ∪ (p ⁻¹' V)ᶜ),
                  ∀ t x, G (t, x) ∈ admissible a b m ∧
                    energy a b τ (G (t, x)) ≤ max (energy a b τ (p x)) (energy a b τ v + ε) ∧
                    (G (t, x) = p x ∨ G (t, x) ∈ N) ∧
                    energy a b τ (G (t, x)) < energy a b τ (p x) + ξ ∧
                    (energy a b τ (p x) - energy a b τ (G (t, x)) ≤ 2 * ζ →
                      dist (G (t, x)) (p x) < ρ) := by
  obtain ⟨W₀, C, hW₀, hvW₀, hW₀C, hC, hCsub, hCn⟩ :=
    exists_compact_noncritical_neighborhood a b τ v hv hn N hN hvN
  obtain ⟨c, hc, T₀, hT₀, hstep₀⟩ := exists_uniform_descent_in_neighborhood a b τ C hC
    (hCsub.trans inter_subset_left) hCn N hN (hCsub.trans inter_subset_right)
  let T := min T₀ ((energy a b τ v - l) / c)
  have hT : 0 < T := lt_min hT₀ (div_pos (sub_pos.mpr hl) hc)
  have hcT : 0 < c * T := mul_pos hc hT
  have hcTle : c * T ≤ energy a b τ v - l := by
    have hh := (le_div_iff₀ hc).mp (min_le_right T₀ ((energy a b τ v - l) / c))
    nlinarith
  have hstep (z) (hz : z ∈ C) (s) (hs : s ∈ Icc (0 : ℝ) T) :=
    hstep₀ z hz s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩
  let k := energy a b τ v - c * T / 2
  have hlk : l < k := by dsimp [k]; linarith
  have hk : k < energy a b τ v := by dsimp [k]; linarith
  let ceiling := min (energy a b τ v + c * T / 2) (energy a b τ v + ε)
  have hceiling : energy a b τ v < ceiling := lt_min (by linarith) (by linarith)
  let W := W₀ ∩ (admissible a b m ∩ energy a b τ ⁻¹' Ioo l ceiling)
  have hW : IsOpen W := hW₀.inter
    ((contMDiffOn_energy a b τ).continuousOn.isOpen_inter_preimage
      (isOpen_admissible a b m) isOpen_Ioo)
  have hvW : v ∈ W := ⟨hvW₀, hv, hl, hceiling⟩
  have hWC : W ⊆ C := fun _ hz ↦ hW₀C hz.1
  have hWlow : ∀ z ∈ W, l < energy a b τ z := fun z hz ↦ hz.2.2.1
  have hcross : ∀ ρ > 0, ∃ ζ > 0, ∀ ξ : ℝ, 0 < ξ → ξ ≤ ζ →
      ∀ (p : C(M, Space n m)), (∀ x, p x ∈ W) →
        ∀ (S : Set M), IsCompact S → (∀ x ∈ S, energy a b τ (p x) ≤ l) →
          ∃ q : C(M, Space n m), (∀ x, energy a b τ (q x) < k) ∧
            ∃ G : ContinuousMap.HomotopyRel p q S,
              ∀ t x, G (t, x) ∈ admissible a b m ∧
                energy a b τ (G (t, x)) < energy a b τ v + ε ∧ G (t, x) ∈ N ∧
                energy a b τ (G (t, x)) < energy a b τ (p x) + ξ ∧
                (energy a b τ (p x) - energy a b τ (G (t, x)) ≤ 2 * ζ →
                  dist (G (t, x)) (p x) < ρ) := by
    intro ρ hρ
    obtain ⟨ζ, hζ, hwindow⟩ := exists_descent_energy_window a b τ C hC
      (hCsub.trans inter_subset_left) c T hc hT.le (fun z hz s hs ↦ (hstep z hz s hs).2.2) ρ hρ
    refine ⟨ζ, hζ, ?_⟩
    intro ξ hξ hξζ p hp S hS hLow
    have hpC (x) : p x ∈ C := hWC (hp x)
    have hpA (x) : p x ∈ admissible a b m := (hCsub (hpC x)).1
    let q : C(M, Space n m) := ⟨fun x ↦ descent a b τ (p x, T),
      (continuousOn_descent a b τ).comp_continuous (p.continuous.prodMk continuous_const)
        (fun x ↦ ⟨hpA x, mem_univ T⟩)⟩
    let G : ContinuousMap.HomotopyRel p q S :=
      { toFun := fun tx ↦ descent a b τ (p tx.2, (tx.1 : ℝ) * T)
        continuous_toFun := (continuousOn_descent a b τ).comp_continuous
          ((p.continuous.comp continuous_snd).prodMk
            ((continuous_subtype_val.comp continuous_fst).mul continuous_const))
          (fun tx ↦ ⟨hpA tx.2, mem_univ _⟩)
        map_zero_left := fun x ↦ by
          change descent a b τ (p x, (0 : ℝ) * T) = p x
          rw [zero_mul, descent_zero]
        map_one_left := fun x ↦ by
          change descent a b τ (p x, (1 : ℝ) * T) = descent a b τ (p x, T)
          rw [one_mul]
        prop' := fun _ x hx ↦ ((not_lt_of_ge (hLow x hx)) (hWlow _ (hp x))).elim }
    refine ⟨q, ?_, G, fun t x ↦ ?_⟩
    · intro x
      have he := (hstep (p x) (hpC x) T ⟨hT.le, le_rfl⟩).2.2
      have hupper := (hp x).2.2.2.trans_le (min_le_left _ _)
      change energy a b τ (descent a b τ (p x, T)) < k
      dsimp [k]
      linarith
    have htime : (t : ℝ) * T ∈ Icc (0 : ℝ) T :=
      ⟨mul_nonneg t.2.1 hT.le, by nlinarith [t.2.2]⟩
    have hh := hstep (p x) (hpC x) ((t : ℝ) * T) htime
    have hnoninc : energy a b τ (G (t, x)) ≤ energy a b τ (p x) :=
      hh.2.2.trans (sub_le_self _ (mul_nonneg hc.le htime.1))
    refine ⟨hh.1, ?_, hh.2.1, ?_, hwindow (p x) (hpC x) _ htime⟩
    · exact hnoninc.trans_lt ((hp x).2.2.2.trans_le (min_le_right _ _))
    · linarith
  have htarget : (0 : Model n m) ∈ (atVertices v).target := by
    simpa only [atVertices_self] using (atVertices v).map_source (mem_atVertices_source v)
  obtain ⟨V, hV, hvV, hVW, hlocal⟩ := localize_quantitative_crossing (M := M)
    (atVertices v) (contMDiff_atVertices_symm v).continuous htarget (energy a b τ)
    (admissible a b m) W N hW (by simpa only [atVertices_symm_zero] using hvW)
    l k (energy a b τ v + ε) hcross
  refine ⟨V, hV, ?_, hVW.trans (hWC.trans hCsub),
    (fun z hz ↦ hWlow z (hVW hz)), k, hlk, hk, ?_⟩
  · simpa only [atVertices_symm_zero] using hvV
  intro ρ hρ
  obtain ⟨ζ, hζ, hlocalζ⟩ := hlocal ρ hρ
  refine ⟨ζ, hζ, ?_⟩
  intro ξ hξ hξζ p hp K hK hKV
  have he : Continuous (fun x ↦ energy a b τ (p x)) :=
    (contMDiffOn_energy a b τ).continuousOn.comp_continuous p.continuous hp
  exact hlocalζ ξ hξ hξζ p hp K hK hKV {x | energy a b τ (p x) ≤ l}
    (isClosed_le he continuous_const).isCompact (fun _ hx ↦ hx)

end NoExoticSixSphere.OrthogonalPolygon
