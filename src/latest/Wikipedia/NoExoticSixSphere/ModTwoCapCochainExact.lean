import Wikipedia.NoExoticSixSphere.ModTwoCapHomology
import Wikipedia.NoExoticSixSphere.ModTwoCochainComplex

/-!
# Cochain boundaries act trivially on the original homology cap map

The boundary identity gives an actual primitive when the cochain is a
coboundary and the chain is a cycle. Additivity follows on the original
cycle representatives. These are the remaining conditions for descent
to genuine cohomology classes.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.ModTwoCapProduct

variable {X : Type} [TopologicalSpace X]

/-- The same proved boundary formula in any equal specified total degree. -/
theorem boundary_capInDegree {p q n : ℕ} (h : p + q + 1 = n) (α : Cochain X p)
    (c : ModTwoChains.Chains X n) :
    ((modComplex 2 X).d (q + 1) q).hom
        (capInDegree (p := p) (q := q + 1) (n := n) (by omega) α c) =
      capInDegree (p := p) (q := q) rfl α (((modComplex 2 X).d n (p + q)).hom c) +
        capInDegree (p := p + 1) (q := q) (n := n) (by omega) (coboundary α) c := by
  subst n
  exact boundary_cap p q α c

/-- The zero cochain induces the zero map on the actual homology groups. -/
theorem homologyCap_zero (p q : ℕ) (h0 : coboundary (0 : Cochain X p) = 0) :
    homologyCap p q (0 : Cochain X p) h0 = 0 := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext (modComplex 2 X) (p + q)
  intro c
  rw [homologyCap_cycleClass, LinearMap.zero_apply]
  have he : capCycles p q (0 : Cochain X p) h0 c = 0 := by
    apply Subtype.ext
    change capInDegree (p := p) (q := q) rfl (0 : Cochain X p) c.val = 0
    rw [capInDegree_zero, LinearMap.zero_apply]
  rw [he, map_zero]

/-- The cap map on homology is additive in the original closed cochain. -/
theorem homologyCap_add (p q : ℕ) (α β : Cochain X p)
    (hα : coboundary α = 0) (hβ : coboundary β = 0) (hαβ : coboundary (α + β) = 0) :
    homologyCap p q (α + β) hαβ = homologyCap p q α hα + homologyCap p q β hβ := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext (modComplex 2 X) (p + q)
  intro c
  rw [homologyCap_cycleClass, LinearMap.add_apply,
    homologyCap_cycleClass, homologyCap_cycleClass]
  have he : capCycles p q (α + β) hαβ c = capCycles p q α hα c + capCycles p q β hβ c := by
    apply Subtype.ext
    exact LinearMap.congr_fun (capInDegree_add (p := p) (q := q) rfl α β) c.val
  exact (congrArg (ModuleHomology.cycleClass (modComplex 2 X) q) he).trans (map_add _ _ _)

/-- Capping with an actual incoming coboundary gives zero on native homology. -/
theorem homologyCap_coboundary (p q : ℕ) (β : Cochain X p) :
    homologyCap (p + 1) q (coboundary β) (coboundary_squared X p β) = 0 := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext (modComplex 2 X) ((p + 1) + q)
  intro c
  rw [homologyCap_cycleClass, LinearMap.zero_apply]
  apply (ModuleHomology.cycleClass_eq_zero_iff (modComplex 2 X) q _).mpr
  refine ⟨capInDegree (p := p) (q := q + 1) (n := (p + 1) + q) (by omega) β c.val, ?_⟩
  have hc := ModuleHomology.cycle_condition (modComplex 2 X) ((p + 1) + q) c
  rw [show ((p + 1) + q) - 1 = p + q by omega] at hc
  have he := boundary_capInDegree (p := p) (q := q) (n := (p + 1) + q) (by omega) β c.val
  rw [hc, map_zero, zero_add] at he
  exact he

end NoExoticSixSphere.ModTwoCapProduct
