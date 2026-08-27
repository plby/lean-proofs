/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceLinkJointInclusion
import ErdosProblems.Erdos207.SourceLinkCodeCardinality

/-! # The source marked-link moment under the actual residual-reserve joint law -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem IsResidualReserveStronglyWellDistributed.sourceLink_canonical_moment_le
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [Fintype V]
    [DecidableEq Ω] [DecidableEq Ξ] [DecidableEq V] {ell j q s : ℕ}
    {L : FiniteLaw Ω} {K : Ω → FiniteLaw Ξ} {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V} {initial later : Ω → TripleSystemOn V}
    {reserve : Ω → Finset (Sym2 V)} {p r C b : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W k G initial later reserve p r C b)
    (hstruct : L.SupportedOn fun ω ↦ Disjoint (initial ω) (later ω))
    {F : ForbiddenFamilyOn V} {y z : ℝ≥0}
    (hsource : SourceVortexWellSpread (W.prefix k) j F y z)
    (U : Finset V) (e : Sym2 V) (A : TripleSystemOn V)
    (hoff : ¬ e.IsDiag) (hcross : IsCrossingEdge U e) (hjq : j ≤ q) (hy : 1 ≤ y)
    (a : ℝ≥0) (hp : 0 < p) (hp1 : p ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1) (hu : 0 < U.card)
    (hlevel : ∀ T ∈ A, (W.prefix k).level T = Fin.last k.val)
    (hinner : ∀ T ∈ A, (T.1 ∩ U).card = 2)
    (hblock : r * a ≤ p * U.card / (W.prefix k).terminalSize) (hpa : p * a ≤ 1)
    (hw : 1 ≤ a * (W.prefix k).terminalSize / (r * p ^ 2 * U.card))
    (hscale : z * (a * (W.prefix k).terminalSize / (r * p ^ 2 * U.card)) ^ (q + 1) /
      (W.prefix k).terminalSize ≤ y)
    (candidate : Ω → Ξ → TripleSystemOn V) (J delta : ℝ≥0)
    (hsigma : a / (r * p ^ 2 * U.card) ≤ 1) (hC : 1 ≤ C) (hJ : 1 ≤ J)
    (hcandidate : ∀ ω, 0 < L.mass ω → ∀ Q,
      (K ω).probability (fun ξ ↦ Q ⊆ candidate ω ξ) ≤
        (a / (r * p ^ 2 * U.card)) ^ Q.card + J ^ Q.card * delta) :
    let d := 4 * (j - 2)
    let κ : ℝ≥0 := (4 : ℝ≥0) ^ (j - 2) * ((1 + (k.val + 1) ^ 2 : ℕ) * (j ^ k.val : ℕ)) * y
    (L.jointBind K).expectation (fun x ↦ selectedCount
      (fun c : sourceLinkMarkings (W.prefix k) F e A ↦ c.1.coordinates e)
      (sourceLinkRealizedCoordinates G U (initial x.1) (later x.1) (candidate x.1 x.2) (reserve x.1)) ^ s) ≤
      (max (C ^ 2) J) ^ (s * d) *
        (((boundedIntersectionMomentCoefficient d s : ℝ≥0) * κ) ^ s +
          (b + delta) * ((4 : ℝ≥0) ^ (j - 2) * (Fintype.card V + 1 : ℝ≥0) ^ (3 * j)) ^ s) := by
  dsimp only
  let sigma := a / (r * p ^ 2 * U.card)
  let C₀ := max (C ^ 2) J
  let d := 4 * (j - 2)
  let π := sourceLinkMixedWeight (fun _ ↦ (Fintype.card V : ℝ≥0)⁻¹)
    (vortexTripleWeight (W.prefix k) p) (fun _ ↦ sigma) (sourceLinkCanonicalEdgeWeight U p r)
  let R := fun x : Ω × Ξ ↦ sourceLinkRealizedCoordinates G U
    (initial x.1) (later x.1) (candidate x.1 x.2) (reserve x.1)
  have hC₀ : 1 ≤ C₀ := hJ.trans (le_max_right _ _)
  have hsize : ∀ c : sourceLinkMarkings (W.prefix k) F e A, (c.1.coordinates e).card ≤ d := by
    intro c
    have hd : IsSourceLinkMarking (W.prefix k) F e A c.1 := (mem_filter.mp c.2).2
    have hb := SourceLinkMarking.coordinates_card_le hd
    simpa only [(hsource.uniform c.1.system (sourceLinkUnderlyingFamily_data hd.1).1).1] using hb
  have hjoint : ∀ H : Finset (SourceLinkCoordinate V), H.card ≤ s * d →
      (L.jointBind K).probability (fun x ↦ H ⊆ R x) ≤ C₀ ^ (s * d) * setWeight π H +
        C₀ ^ (s * d) * (b + delta) := by
    intro H hH
    have hb := hstrong.jointBind_sourceLink_inclusion_le hstruct U candidate sigma J delta
      hsigma hC hJ hcandidate H
    apply hb.trans
    calc
      _ ≤ C₀ ^ (s * d) * (setWeight π H + b + delta) := by
        apply mul_le_mul_of_nonneg_right _ zero_le
        exact pow_le_pow_right₀ hC₀ hH
      _ = _ := by ring
  have hκ := hsource.sourceLink_canonical_hasExtensionBound U e A hoff hcross hjq hy p r a hp hp1 hr hr1
    hu hlevel hinner hblock hpa hw hscale
  have hb := configurationMomentBound_additive (L.jointBind K)
    (fun c : sourceLinkMarkings (W.prefix k) F e A ↦ c.1.coordinates e) R π
    (C₀ ^ (s * d)) (C₀ ^ (s * d) * (b + delta)) _ hsize hκ hjoint
  have hcount : (Fintype.card (sourceLinkMarkings (W.prefix k) F e A) : ℝ≥0) ≤
      (4 : ℝ≥0) ^ (j - 2) * (Fintype.card V + 1 : ℝ≥0) ^ (3 * j) := by
    rw [Fintype.card_coe]
    exact_mod_cast card_sourceLinkMarkings_le_polynomial (W := W.prefix k) (e := e) (A := A)
      (fun E hE ↦ (hsource.uniform E hE).2) (fun E hE ↦ (hsource.uniform E hE).1)
  apply hb.trans
  calc
    _ ≤ C₀ ^ (s * d) * ((boundedIntersectionMomentCoefficient d s : ℝ≥0) * _) ^ s +
        (C₀ ^ (s * d) * (b + delta)) *
          ((4 : ℝ≥0) ^ (j - 2) * (Fintype.card V + 1 : ℝ≥0) ^ (3 * j)) ^ s := by gcongr
    _ = _ := by ring

end

end Erdos207
