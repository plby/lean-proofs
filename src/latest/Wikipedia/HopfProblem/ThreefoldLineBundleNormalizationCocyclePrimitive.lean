import Wikipedia.HopfProblem.ThreefoldLineBundleNormalizationCocyclePullback
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClassZero

/-!
# Genuine holomorphic primitives and their exponential coboundaries

Vanishing of the original Ext-defined holomorphic H¹ makes the actual
pulled-back additive cocycle solvable on its actual preimage cover.
Applying the original exponential gives an actual unit coboundary.
For the native coordinate convention the compatible nonzero coordinates
are `exp(-b_i)`, because the original additive primitive satisfies
`b_i - b_j = c_ij`.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.LineBundleNormalization.Cocycle

open HolomorphicFunctionSheaf.SphereH1 HolomorphicExponentialSheaf

variable {E H E' H' M N : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
    {I : ModelWithCorners ℂ E H} {J : ModelWithCorners ℂ E' H'}
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]

/-- Applying the original exponential to an actual additive coboundary
gives an actual unit coboundary on exactly the same cover. -/
theorem exponentialCocycle_solvable {κ : Type} {V : κ → Opens N}
    (c : CechOneCocycle (HolomorphicFunctionSheaf.additiveSheaf J N) V)
    (hc : c.Solvable) :
    (HolomorphicPicard.Cech.mapCocycle (exponential J N) c).Solvable := by
  obtain ⟨b, hb⟩ := hc
  refine ⟨fun i => (exponential J N).hom.app (op (V i)) (b i), ?_⟩
  intro i j
  rw [res_map, res_map, HolomorphicPicard.Cech.mapCocycle_value]
  exact ((exponential J N).hom.app (op (V i ⊓ V j))).hom.map_sub _ _ |>.symm.trans
    (congrArg ((exponential J N).hom.app (op (V i ⊓ V j))) (hb i j))

/-- The native transition convention uses the genuine nowhere-zero
coordinates `exp(-b_i)`, not their inverses. -/
theorem exponential_coordinates_compatible {κ : Type} {V : κ → Opens N}
    (c : CechOneCocycle (HolomorphicFunctionSheaf.additiveSheaf J N) V)
    (b : ∀ i : κ, HolomorphicFunctionSheaf.Section J N (V i))
    (hb : ∀ i j : κ,
      res (HolomorphicFunctionSheaf.additiveSheaf J N) inf_le_left (b i) -
        res (HolomorphicFunctionSheaf.additiveSheaf J N) inf_le_right (b j) = c.value i j)
    (i j : κ) (x : ↥(V i ⊓ V j)) :
    unitSectionEval ((HolomorphicPicard.Cech.mapCocycle (exponential J N) c).value i j) x *
        Complex.exp (-(b i) ⟨x, x.property.1⟩) =
      Complex.exp (-(b j) ⟨x, x.property.2⟩) := by
  have hv : (b i) ⟨x, x.property.1⟩ - (b j) ⟨x, x.property.2⟩ = c.value i j x :=
    congrArg (fun s : HolomorphicFunctionSheaf.Section J N (V i ⊓ V j) => s x) (hb i j)
  rw [HolomorphicPicard.Cech.mapCocycle_value, exponential_app_eval, ← Complex.exp_add, ← hv]
  congr 1
  ring

variable (f : ContMDiffMap J I N M ω) {ι : Type} {U : ι → Opens M}
    (hU : ∀ x : M, ∃ i : ι, x ∈ U i)
    (c : CechOneCocycle (HolomorphicFunctionSheaf.additiveSheaf I M) U)

/-- Original holomorphic H¹ vanishing produces a genuine holomorphic
zero-cochain primitive for the actual pulled-back additive cocycle.
No cohomological pullback comparison is needed. -/
theorem pullbackCocycle_solvable
    (hH : Subsingleton (CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf J N) 1)) :
    (pullbackCocycle f c).Solvable := by
  apply (HolomorphicPicard.CechExtension.classOf_eq_zero_iff_solvable
    (pullbackCocycle f c) (preimageCover_covers f U hU)).mp
  exact hH.elim _ _

/-- The primitive consists of actual holomorphic sections and has the
literal original earlier-minus-later restriction identity. -/
theorem exists_pullback_primitive
    (hH : Subsingleton (CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf J N) 1)) :
    ∃ b : ∀ i : ι, HolomorphicFunctionSheaf.Section J N (preimageCover f U i),
      ∀ i j : ι,
        res (HolomorphicFunctionSheaf.additiveSheaf J N) inf_le_left (b i) -
          res (HolomorphicFunctionSheaf.additiveSheaf J N) inf_le_right (b j) =
        (pullbackCocycle f c).value i j :=
  pullbackCocycle_solvable f hU c hH

/-- Exponentiating the actual pulled-back additive cocycle gives a
genuine unit coboundary whenever the original source holomorphic H¹ vanishes. -/
theorem pullbackExponentialCocycle_solvable
    (hH : Subsingleton (CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf J N) 1)) :
    (HolomorphicPicard.Cech.mapCocycle (exponential J N) (pullbackCocycle f c)).Solvable :=
  exponentialCocycle_solvable (pullbackCocycle f c) (pullbackCocycle_solvable f hU c hH)

/-- The original unit Čech extension class really vanishes, by the
proved coboundary criterion for the original sheaf extension. -/
theorem pullbackExponentialCocycle_class_eq_zero
    (hH : Subsingleton (CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf J N) 1)) :
    HolomorphicPicard.CechExtension.classOf
        (HolomorphicPicard.Cech.mapCocycle (exponential J N) (pullbackCocycle f c))
        (preimageCover_covers f U hU) = 0 :=
  HolomorphicPicard.CechExtension.classOf_eq_zero_of_solvable _
    (preimageCover_covers f U hU) (pullbackExponentialCocycle_solvable f hU c hH)

end Wikipedia.HopfProblem.LineBundleNormalization.Cocycle
