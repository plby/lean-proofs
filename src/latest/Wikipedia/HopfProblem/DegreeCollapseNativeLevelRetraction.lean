import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenExcellentMorse
import Wikipedia.HopfProblem.DegreeCollapsePositiveLevelDisks
import Wikipedia.NoExoticSixSphere.SmoothTubularRetraction

/-!
# Construct an embedding and tubular retraction for the original regular fiber

Restrict the state's actual Euclidean embedding to the native regular
level. The state's normal frame gives an ambient tubular retraction.
Compose it with the original flow-cylinder projection on their genuine
open common domain. This constructs the required level retraction without
assuming a separate normal frame or a sphere identification for the level.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap TopologicalSpace
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation
open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {B : Type} [TopologicalSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

def nativeLevelEmbedding {a : ℝ}
    (hreg : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function) :
    let _ := RegularLevel.chartedSpace P.smooth hreg
    EuclideanEmbedding (Module.finrank ℝ (Vector 7) - 1)
      {y : S.Space // P.function y = a} := by
  let _ := RegularLevel.chartedSpace P.smooth hreg
  let : CompactSpace {y : S.Space // P.function y = a} :=
    isCompact_iff_compactSpace.mp (isClosed_eq P.function.continuous continuous_const).isCompact
  have hi := RegularLevel.contMDiff_inclusion P.smooth hreg
  refine {
    ambientDimension := S.embedding.ambientDimension
    toFun := fun y => S.embedding.toFun y.val
    smooth := S.embedding.smooth.comp hi
    closedEmbedding := (S.embedding.smooth.comp hi).continuous.isClosedEmbedding
      (S.embedding.closedEmbedding.injective.comp Subtype.val_injective)
    injective_mfderiv := ?_ }
  intro x
  change Injective (mfderiv 𝓘(ℝ, RegularLevel.Model (Vector 7)) (𝓡 S.embedding.ambientDimension)
    (S.embedding.toFun ∘ Subtype.val) x)
  rw [mfderiv_comp x (S.embedding.smooth.mdifferentiableAt (by simp))
    (hi.mdifferentiableAt (by simp))]
  exact (S.embedding.injective_mfderiv x.val).comp
    (RegularLevel.injective_mfderiv_inclusion P.smooth hreg x)

theorem nonempty_nativeLevelRetraction
    (A : AdaptedSurgeryWindows (Vector 7) P.function) {a : ℝ}
    (hreg : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (z₀ : {y : S.Space // P.function y = a}) :
    let _ := RegularLevel.chartedSpace P.smooth hreg
    Nonempty (EuclideanEmbedding.TubularRetraction (P.nativeLevelEmbedding hreg)) := by
  let _ := RegularLevel.chartedSpace P.smooth hreg
  let _ := RegularLevel.isManifold P.smooth hreg
  obtain ⟨r₀⟩ := S.embedding.nonempty_tubularRetraction S.normalFrame
  obtain ⟨Φ, hsource, _, hformula, _⟩ := FlowCancellation.exists_native_level_flow_cylinder
    P.smooth hreg A.smooth A.flow A.integral (fun y hy => A.descent y (hreg y hy)) z₀
  let U : Opens (Vector S.embedding.ambientDimension) :=
    ⟨(r₀.domain : Set _) ∩ r₀.toFun ⁻¹' Φ.target,
      r₀.smooth.continuousOn.isOpen_inter_preimage r₀.domain.isOpen Φ.open_target⟩
  let R : Vector S.embedding.ambientDimension → {y : S.Space // P.function y = a} :=
    fun y => (Φ.symm (r₀.toFun y)).1
  have hR : ContMDiffOn (𝓡 S.embedding.ambientDimension)
      𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ R U :=
    contMDiff_fst.comp_contMDiffOn (Φ.contMDiffOn_invFun.comp
      (r₀.smooth.mono inter_subset_left) (fun _ hy => hy.2))
  have hsource₀ (z : {y : S.Space // P.function y = a}) : (z, (0 : ℝ)) ∈ Φ.source := by
    rw [hsource]
    trivial
  have hΦ₀ (z : {y : S.Space // P.function y = a}) : Φ (z, (0 : ℝ)) = z.val := by
    rw [hformula, A.flow.map_zero_apply]
  have htarget₀ (z : {y : S.Space // P.function y = a}) : z.val ∈ Φ.target :=
    hΦ₀ z ▸ Φ.map_source' (hsource₀ z)
  refine ⟨{
    domain := U
    toFun := R
    smooth := hR
    fixes := ?_
    contains := ?_
    submersive := ?_ }⟩
  · intro z
    have hinv : Φ.symm (Φ (z, (0 : ℝ))) = (z, 0) := Φ.left_inv' (hsource₀ z)
    rw [hΦ₀] at hinv
    change (Φ.symm (r₀.toFun (S.embedding.toFun z.val))).1 = z
    rw [r₀.fixes]
    exact congrArg Prod.fst hinv
  · rintro y ⟨z, rfl⟩
    change S.embedding.toFun z.val ∈ U
    refine ⟨r₀.contains (mem_range_self z.val), ?_⟩
    change r₀.toFun (S.embedding.toFun z.val) ∈ Φ.target
    rw [r₀.fixes]
    exact htarget₀ z
  · change ∀ y : Vector S.embedding.ambientDimension, y ∈ U →
      Surjective (mfderiv (𝓡 S.embedding.ambientDimension)
        𝓘(ℝ, RegularLevel.Model (Vector 7)) R y)
    intro y hy
    have hr := (r₀.smooth.contMDiffAt (r₀.domain.isOpen.mem_nhds hy.1)).mdifferentiableAt
      (by simp)
    have hφ := Φ.symm.mdifferentiableAt (by simp) hy.2
    have hlocal : IsLocalDiffeomorphAt (𝓡 7)
        (𝓘(ℝ, RegularLevel.Model (Vector 7)).prod 𝓘(ℝ, ℝ)) ∞
        Φ.symm (r₀.toFun y) := ⟨Φ.symm, hy.2, fun _ _ => rfl⟩
    have hsurj := (hlocal.mfderivToContinuousLinearEquiv (by simp)).surjective
    change Surjective (mfderiv (𝓡 7) (𝓘(ℝ, RegularLevel.Model (Vector 7)).prod 𝓘(ℝ, ℝ))
      Φ.symm (r₀.toFun y)) at hsurj
    change Surjective (mfderiv (𝓡 S.embedding.ambientDimension)
      𝓘(ℝ, RegularLevel.Model (Vector 7))
      (Prod.fst ∘ (Φ.symm ∘ r₀.toFun)) y)
    rw [mfderiv_comp y mdifferentiableAt_fst (hφ.comp y hr),
      mfderiv_comp y hφ hr, mfderiv_fst]
    intro v
    obtain ⟨w, hw⟩ := hsurj (v, 0)
    obtain ⟨u, hu⟩ := r₀.submersive y hy.1 w
    refine ⟨u, ?_⟩
    change (mfderiv (𝓡 7) (𝓘(ℝ, RegularLevel.Model (Vector 7)).prod 𝓘(ℝ, ℝ))
      Φ.symm (r₀.toFun y)
      (mfderiv (𝓡 S.embedding.ambientDimension) (𝓡 7) r₀.toFun y u)).1 = v
    rw [hu]
    exact congrArg Prod.fst hw

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
