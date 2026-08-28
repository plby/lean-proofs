import Wikipedia.NoExoticSixSphere.MapDoublePointTopology
import Wikipedia.NoExoticSixSphere.GenericFamilyLocalCurve

/-!
# An equivariant closed-double-point chart at a single-map corank-one singularity

The original residual is pulled back through the actual zero-parameter
linear equivalence, so its derivative remains bijective. The general local
family construction then gives a curve in the actual closure; removing the
zero parameter preserves its topology, zero coordinate, and swap symmetry.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace NoExoticSixSphere.MapDoublePoints

open CorankOneCoordinates

variable {V W E F : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_closed_curve_of_local_regular_residual (g : V → W)
    {U : Set V} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (x : V) (hx : x ∈ U)
    (hres : ∃ c : Coordinates V W E F,
      fderiv ℝ g x ∈ domain c ∧ CorankOne.residual (operatorEquiv c (fderiv ℝ g x)) = 0 ∧
      Bijective (fderiv ℝ (fun y ↦ CorankOne.residual (operatorEquiv c (fderiv ℝ g y))) x)) :
    ∃ hc : (x, x) ∈ closure (points g),
      ∃ d : OpenPartialHomeomorph (closure (points g)) ℝ,
        (⟨(x, x), hc⟩ : closure (points g)) ∈ d.source ∧
        d ⟨(x, x), hc⟩ = 0 ∧
        (∀ r ∈ d.source, swapClosure g r ∈ d.source) ∧
        ∀ r ∈ d.source, d (swapClosure g r) = -d r := by
  let L := ContinuousLinearEquiv.uniqueProd ℝ V ZeroParameter
  have hf : ContDiffOn ℝ ∞ (uncurry (asFamily g)) (Prod.snd ⁻¹' U) :=
    hg.comp contDiff_snd.contDiffOn (fun _ hq ↦ hq)
  have hres' : ∃ c : Coordinates V W E F,
      fderiv ℝ (asFamily g 0) x ∈ domain c ∧
      CorankOne.residual (operatorEquiv c (fderiv ℝ (asFamily g 0) x)) = 0 ∧
      Bijective (fderiv ℝ (fun q : ZeroParameter × V ↦ CorankOne.residual
        (operatorEquiv c (fderiv ℝ (asFamily g q.1) q.2))) (0, x)) := by
    obtain ⟨c, hc, hz, hb⟩ := hres
    refine ⟨c, hc, hz, ?_⟩
    change Bijective (fderiv ℝ
      ((fun y ↦ CorankOne.residual (operatorEquiv c (fderiv ℝ g y))) ∘ L) (0, x))
    rw [L.comp_right_fderiv]
    exact hb.comp L.bijective
  obtain ⟨hfc, c, hcp, hcz, hcs, hcn⟩ :=
    FamilyEmbedding.exists_closed_curve_of_local_regular_residual (asFamily g)
      (hU.preimage continuous_snd) hf (0, x) hx hres'
  have hc : (x, x) ∈ closure (points g) := project_mem_closure g hfc
  let p : closure (points g) := ⟨(x, x), hc⟩
  let q : closure (FamilyEmbedding.doublePoints (asFamily g)) := ⟨(0, (x, x)), hfc⟩
  let e := familyCoordinates g
  have he : e p = q := Subtype.ext rfl
  let d := e.toOpenPartialHomeomorph.trans c
  have hp : p ∈ d.source := by
    refine ⟨mem_univ _, ?_⟩
    change e p ∈ c.source
    rw [he]
    exact hcp
  refine ⟨hc, d, hp, ?_, ?_, ?_⟩
  · change c (e p) = 0
    rw [he]
    exact hcz
  · intro r hr
    refine ⟨mem_univ _, ?_⟩
    change familyCoordinates g (swapClosure g r) ∈ c.source
    rw [familyCoordinates_swap]
    exact hcs (e r) hr.2
  · intro r hr
    change c (familyCoordinates g (swapClosure g r)) = -c (e r)
    rw [familyCoordinates_swap]
    exact hcn (e r) hr.2

end NoExoticSixSphere.MapDoublePoints
