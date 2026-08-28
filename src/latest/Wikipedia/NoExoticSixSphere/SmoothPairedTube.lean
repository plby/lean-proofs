import Wikipedia.NoExoticSixSphere.SmoothProductTube
import Wikipedia.NoExoticSixSphere.HilbertPairedTubeCollapse
import Wikipedia.NoExoticSixSphere.DiffeomorphProductModels

/-!
# Smooth partial inverses for paired tubes

The ordinary and Hilbert product coordinates use the actual two partial
inverses and the fixed middle-factor interchange. Both sources are full.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.OpenFiberCollapse

variable {B H M C H' N K L E F : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  [NormedAddCommGroup L] [NormedSpace ℝ L]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (Φ : PartialDiffeomorph (I.prod 𝓘(ℝ, K)) 𝓘(ℝ, E) (M × K) E ∞)
  (Ψ : PartialDiffeomorph (J.prod 𝓘(ℝ, L)) 𝓘(ℝ, F) (N × L) F ∞)
  (hΦ : Φ.source = univ) (hΨ : Ψ.source = univ)

def pairedTubePartial :
    PartialDiffeomorph ((I.prod J).prod 𝓘(ℝ, K × L)) 𝓘(ℝ, E × F)
      ((M × N) × (K × L)) (E × F) ∞ := by
  let e := (Homeomorph.prodProdProdComm M N K L).toOpenPartialHomeomorph.trans
    (Φ.toOpenPartialHomeomorph.prod Ψ.toOpenPartialHomeomorph)
  refine {
    toPartialEquiv := e.toPartialEquiv
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := ?_ }
  · have hcΦ := Φ.contMDiffOn
    have hcΨ := Ψ.contMDiffOn
    rw [hΦ] at hcΦ
    rw [hΨ] at hcΨ
    have hk : ContMDiff ((I.prod J).prod 𝓘(ℝ, K × L)) 𝓘(ℝ, K) ∞
        (fun p : (M × N) × (K × L) ↦ p.2.1) :=
      contDiff_fst.contMDiff.comp contMDiff_snd
    have hl : ContMDiff ((I.prod J).prod 𝓘(ℝ, K × L)) 𝓘(ℝ, L) ∞
        (fun p : (M × N) × (K × L) ↦ p.2.2) :=
      contDiff_snd.contMDiff.comp contMDiff_snd
    have ha := (contMDiffOn_univ.mp hcΦ).comp
      ((contMDiff_fst.comp contMDiff_fst).prodMk hk)
    have hb := (contMDiffOn_univ.mp hcΨ).comp
      ((contMDiff_snd.comp contMDiff_fst).prodMk hl)
    exact (ha.prodMk_space hb).contMDiffOn
  · have ha : ContMDiffOn 𝓘(ℝ, E × F) (I.prod 𝓘(ℝ, K)) ∞
        (fun p : E × F ↦ Φ.symm p.1) (Φ.target ×ˢ Ψ.target) :=
      Φ.contMDiffOn_invFun.comp contDiff_fst.contMDiff.contMDiffOn (fun _ hp ↦ hp.1)
    have hb : ContMDiffOn 𝓘(ℝ, E × F) (J.prod 𝓘(ℝ, L)) ∞
        (fun p : E × F ↦ Ψ.symm p.2) (Φ.target ×ˢ Ψ.target) :=
      Ψ.contMDiffOn_invFun.comp contDiff_snd.contMDiff.contMDiffOn (fun _ hp ↦ hp.2)
    have h := ((contMDiff_fst.comp_contMDiffOn ha).prodMk
      (contMDiff_fst.comp_contMDiffOn hb)).prodMk
        ((contMDiff_snd.comp_contMDiffOn ha).prodMk_space
          (contMDiff_snd.comp_contMDiffOn hb))
    exact h.mono (fun _ hp ↦ hp.1)

theorem pairedTubePartial_apply (p : (M × N) × (K × L)) :
    pairedTubePartial Φ Ψ hΦ hΨ p = pairedTube Φ Ψ p := rfl

theorem pairedTubePartial_source : (pairedTubePartial Φ Ψ hΦ hΨ).source = univ := by
  apply eq_univ_of_forall
  intro p
  change p ∈ univ ∧ ((p.1.1, p.2.1) ∈ Φ.source ∧ (p.1.2, p.2.2) ∈ Ψ.source)
  simp only [hΦ, hΨ, mem_univ, and_self]

def hilbertPairedTubePartial :
    PartialDiffeomorph ((I.prod J).prod 𝓘(ℝ, WithLp 2 (K × L)))
      𝓘(ℝ, WithLp 2 (E × F)) ((M × N) × WithLp 2 (K × L)) (WithLp 2 (E × F)) ∞ :=
  ((diffeomorphProd (Diffeomorph.refl (I.prod J) (M × N) ∞)
    (WithLp.prodContinuousLinearEquiv 2 ℝ K L).toDiffeomorph).toPartialDiffeomorph.trans
      (pairedTubePartial Φ Ψ hΦ hΨ)).trans
        (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.toDiffeomorph.toPartialDiffeomorph

theorem hilbertPairedTubePartial_apply (p : (M × N) × WithLp 2 (K × L)) :
    hilbertPairedTubePartial Φ Ψ hΦ hΨ p = hilbertPairedTube Φ Ψ p := rfl

theorem hilbertPairedTubePartial_source :
    (hilbertPairedTubePartial Φ Ψ hΦ hΨ).source = univ :=
  partialDiffeomorph_trans_source_univ _ _
    (partialDiffeomorph_trans_source_univ _ _ rfl (pairedTubePartial_source Φ Ψ hΦ hΨ)) rfl

end NoExoticSixSphere.OpenFiberCollapse
