import Wikipedia.NoExoticSixSphere.GenericFamilyFlatGerm
import Wikipedia.NoExoticSixSphere.FamilyLinearPairCoordinates

/-!
# A genuine closed-double-curve chart for the original generic family

At a corank-one point with a regular residual, the actual shared-parameter
double-point closure has a local real chart. Its ambient inverse is smooth,
the chart source is swap-invariant, and swapping negates the coordinate.
Both nonlinear and fixed linear source changes are removed. The parameter
and leading-block dimensions are general; regular three-to-six families
remain a specialization.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace NoExoticSixSphere.FamilyLinearCoordinates

open OperatorRank FamilyFlattening FamilySharedTimePairs

variable {V W : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem exists_closed_curve_of_regular_residual
    {T E F : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (f : T → V → W)
    (hf : ContDiff ℝ ∞ (uncurry f))
    (p : T × V)
    (hres : ∃ c : CorankOneCoordinates.Coordinates V W E F,
      fderiv ℝ (f p.1) p.2 ∈ CorankOneCoordinates.domain c ∧
      CorankOne.residual (CorankOneCoordinates.operatorEquiv c (fderiv ℝ (f p.1) p.2)) = 0 ∧
      Bijective (fderiv ℝ (fun q : T × V ↦ CorankOne.residual
        (CorankOneCoordinates.operatorEquiv c (fderiv ℝ (f q.1) q.2))) p)) :
    ∃ c : CorankOneCoordinates.Coordinates V W E F,
    ∃ hc : (p.1, (p.2, p.2)) ∈ closure (FamilyEmbedding.doublePoints f),
    ∃ e : OpenPartialHomeomorph (closure (FamilyEmbedding.doublePoints f)) ℝ,
      (⟨(p.1, (p.2, p.2)), hc⟩ : closure (FamilyEmbedding.doublePoints f)) ∈ e.source ∧
      e ⟨(p.1, (p.2, p.2)), hc⟩ = 0 ∧
      (∀ r ∈ e.source, e r = ((c.1 r.val.2.1).2 - (c.1 r.val.2.2).2) / 2) ∧
      (∀ r ∈ e.source, FamilyEmbedding.swapClosure f r ∈ e.source) ∧
      (∀ r ∈ e.source, e (FamilyEmbedding.swapClosure f r) = -e r) ∧
      ContDiffOn ℝ ∞ (fun s ↦ (e.symm s).val) e.target := by
  obtain ⟨c, d, hd, hz, hb⟩ := exists_source_coordinates_of_regular_residual f hf p hres
  let q := (sourceEquiv c).symm p
  obtain ⟨hchanged, k, hkq, hkzero, hkapply, hkswap, hkneg, hksmooth⟩ :=
    exists_shared_closed_curve (contDiff_family c f hf) d q hd hz hb
  have hcoord : sourcePairs c (p.1, (p.2, p.2)) ∈
      closure (FamilyEmbedding.doublePoints (family c f)) := by
    rw [sourcePairs_diagonal c p]
    exact hchanged
  have hc : (p.1, (p.2, p.2)) ∈ closure (FamilyEmbedding.doublePoints f) := by
    have h := (sourcePairs_symm_doublePoints c f).closure
      (sourcePairs (T := T) c).symm.continuous hcoord
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using h
  let s₀ : closure (FamilyEmbedding.doublePoints f) := ⟨(p.1, (p.2, p.2)), hc⟩
  let t₀ : closure (FamilyEmbedding.doublePoints (family c f)) :=
    ⟨fromTrack (q, q), hchanged⟩
  let e := closedPairCoordinates c f
  have he₀ : e s₀ = t₀ := Subtype.ext (sourcePairs_diagonal c p)
  let l := e.toOpenPartialHomeomorph.trans k
  have hlq : s₀ ∈ l.source := by
    refine ⟨mem_univ _, ?_⟩
    change e s₀ ∈ k.source
    rw [he₀]
    exact hkq
  have hlapply : ∀ r ∈ l.source,
      l r = ((c.1 r.val.2.1).2 - (c.1 r.val.2.2).2) / 2 := by
    intro r hr
    change k (e r) = _
    exact hkapply (e r) hr.2
  have hlswap : ∀ r ∈ l.source, FamilyEmbedding.swapClosure f r ∈ l.source := by
    intro r hr
    refine ⟨mem_univ _, ?_⟩
    change closedPairCoordinates c f (FamilyEmbedding.swapClosure f r) ∈ k.source
    rw [closedPairCoordinates_swap]
    exact hkswap (e r) hr.2
  refine ⟨c, hc, l, hlq, ?_, hlapply, hlswap, ?_, ?_⟩
  · change k (e s₀) = 0
    rw [he₀]
    exact hkzero
  · intro r hr
    rw [hlapply _ (hlswap r hr), hlapply r hr]
    change ((c.1 r.val.2.2).2 - (c.1 r.val.2.1).2) / 2 =
      -(((c.1 r.val.2.1).2 - (c.1 r.val.2.2).2) / 2)
    ring
  · exact (sourcePairs (T := T) c).symm.contDiff.comp_contDiffOn
      (hksmooth.mono (fun _ hs ↦ hs.1))

theorem exists_closed_curve_of_regular_three_six (f : ℝ → V → W)
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hreg : RegularThreeSix (fun q : ℝ × V ↦ fderiv ℝ (f q.1) q.2))
    (p : ℝ × V) (hp : ¬ Injective (fderiv ℝ (f p.1) p.2)) :
    ∃ c : RankTwoCoordinates V W,
    ∃ hc : (p.1, (p.2, p.2)) ∈ closure (FamilyEmbedding.doublePoints f),
    ∃ e : OpenPartialHomeomorph (closure (FamilyEmbedding.doublePoints f)) ℝ,
      (⟨(p.1, (p.2, p.2)), hc⟩ : closure (FamilyEmbedding.doublePoints f)) ∈ e.source ∧
      e ⟨(p.1, (p.2, p.2)), hc⟩ = 0 ∧
      (∀ r ∈ e.source, e r = ((c.1 r.val.2.1).2 - (c.1 r.val.2.2).2) / 2) ∧
      (∀ r ∈ e.source, FamilyEmbedding.swapClosure f r ∈ e.source) ∧
      (∀ r ∈ e.source, e (FamilyEmbedding.swapClosure f r) = -e r) ∧
      ContDiffOn ℝ ∞ (fun s ↦ (e.symm s).val) e.target :=
  exists_closed_curve_of_regular_residual f hf p (hreg.residual_regular p hp)

end NoExoticSixSphere.FamilyLinearCoordinates
