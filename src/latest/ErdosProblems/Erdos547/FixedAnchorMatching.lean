import ErdosProblems.Erdos547.SharedPair
import ErdosProblems.Erdos547.FixedAnchorAssembly
import ErdosProblems.Erdos547.FullOrientation
import ErdosProblems.Erdos547.PrivatePieceSaturation

/-!
# A fixed-order matching lemma for a fractional piece crossing two anchor regions
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem exists_fixed_anchor_matching (μ J : FractionalMatching G)
    (hJ : ∀ u v, J.weight u v ≤ μ.weight u v) (U : Finset V) (hcross : J.Crosses U)
    (w : EdgeWeights G) {c d : V} (hcd : G.Adj c d)
    (hfitD : ∀ u ∈ U, J.load u ≤ w.weight d u)
    (hfitC : ∀ u ∈ Uᶜ, J.load u ≤ w.weight c u)
    (γ δ a b : ℝ) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (ha : 0 < a) (hb : 0 < b)
    (hsat : a + b ≤ w.saturation μ.load c)
    (hbudget : max (a / (1 + γ)) (γ * (a / (1 + γ))) +
      min (b / (1 + δ)) (δ * (b / (1 + δ))) ≤ J.total) :
    ∃ σ : SkewMatching G γ, ∃ τ : SkewMatching G δ,
      AnchoredPair σ τ w d c ∧ PairDominated σ τ μ ∧ σ.total = a ∧ τ.total = b := by
  classical
  obtain ⟨E⟩ := exists_cross_anchor_split J Uᶜ hcross.swap w c
  let C := E.shared
  let P := E.privatePart
  have hP (u v : V) : P.weight u v ≤ J.weight u v := by
    rw [E.split_eq]
    exact le_add_of_nonneg_left (C.nonnegative u v)
  have hCfit (u : V) : C.load u ≤ w.weight c u := by
    by_cases hu : u ∈ U
    · exact E.shared_fits_inactive (by simpa only [compl_compl] using hu)
    · exact (C.load_le_of_weight_le J E.shared_le u).trans (hfitC u (Finset.mem_compl.mpr hu))
  have hDfit (u : V) (hu : u ∈ U) : C.load u ≤ w.weight d u :=
    (C.load_le_of_weight_le J E.shared_le u).trans (hfitD u hu)
  let q := min (a / orientationRate γ) P.total
  let r := a - orientationRate γ * q
  obtain ⟨hq0, hqP, hr0, hqRate, hres, hprivate⟩ :=
    private_residual_budget γ a P.total hγ ha.le P.total_nonneg
  change max (r / (1 + γ)) (γ * (r / (1 + γ))) =
    max (a / (1 + γ)) (γ * (a / (1 + γ))) - q at hres
  obtain ⟨Q, hQ, htQ⟩ := P.exists_submatching_total q hq0 hqP
  have hQJ (u v : V) : Q.weight u v ≤ J.weight u v := (hQ u v).trans (hP u v)
  obtain ⟨ρ, hρ, htρ, houtρ⟩ := exists_full_orientation Q U (hcross.mono hQJ) γ hγ
  have htρ' : ρ.total = orientationRate γ * q := by rwa [htQ] at htρ
  have hρfit : ρ.Fits (w.truncate C.load C.load_nonneg) d := by
    intro u
    by_cases hu : u ∈ U
    · have hQload := Q.load_le_of_weight_le P hQ u
      have he := E.load_eq u
      have hd := hfitD u hu
      have hh := (ρ.outLoad_le_load u).trans (hρ.load_le u)
      change ρ.outLoad u ≤ max 0 (w.weight d u - C.load u)
      apply le_trans _ (le_max_right _ _)
      change J.load u = C.load u + P.load u at he
      linarith
    · rw [houtρ u hu]
      exact (w.truncate C.load C.load_nonneg).nonnegative d u
  have hpieces (u v : V) : C.weight u v + Q.weight u v ≤ μ.weight u v := by
    have he := E.split_eq u v
    change J.weight u v = C.weight u v + P.weight u v at he
    linarith [hQ u v, hJ u v]
  have hloss : (w.truncate C.load C.load_nonneg).saturation Q.load c ≤ ρ.total := by
    have hh := E.private_piece_saturation_le Q hQ
    rw [htQ] at hh
    rw [htρ']
    exact hh.trans hqRate
  have hbound : 0 < r → max (r / (1 + γ)) (γ * (r / (1 + γ))) +
      min (b / (1 + δ)) (δ * (b / (1 + δ))) ≤ C.total := by
    intro hr
    have hq : q = P.total := hprivate hr
    have ht := E.total_eq
    change J.total = C.total + P.total at ht
    rw [hres, hq]
    linarith
  obtain ⟨σs, τs, hps, hds, hts, hchoice⟩ := exists_shared_pair C U
    (hcross.mono E.shared_le) w hcd hCfit hDfit γ δ r b hγ hδ hr0 hb hbound
  have htotal : σs.total + ρ.total = a := by rw [hts, htρ']; dsimp [r]; ring
  obtain ⟨σ, τ, hp, hd, htσ, htτ⟩ := assemble_fixed_anchor hps hds hρ hρfit hpieces hloss
    b hchoice (by rw [htotal]; exact hsat)
  exact hp.trim hd a b ha.le hb.le (htσ.trans htotal).ge htτ

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_fixed_anchor_matching
