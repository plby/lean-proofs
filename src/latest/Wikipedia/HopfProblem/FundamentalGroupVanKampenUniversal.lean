import Wikipedia.HopfProblem.FundamentalGroupVanKampenCompatibility
import Wikipedia.HopfProblem.FundamentalGroupVanKampenHom
import Wikipedia.HopfProblem.FundamentalGroupVanKampenInterval
import Wikipedia.HopfProblem.FundamentalGroupVanKampenSquare
import Wikipedia.HopfProblem.FundamentalGroupVanKampenUniqueness

/-!
# The actual two-open-set van Kampen universal property

Compatible homomorphisms on the fundamental groups of two path-connected
open subspaces with path-connected intersection extend uniquely to the
fundamental group of their union.  The extension is constructed by actual
finite path subdivision; actual homotopy-square subdivision proves that
it descends to the native path-homotopy quotient.

In particular, no fundamental-group pushout, presentation, monodromy
representation, or global path value is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FundamentalGroupVanKampen.TwoOpenCover

variable {X : Type*} [TopologicalSpace X] {G : Type*} [Group G]
variable (D : TwoOpenCover X) (fU : D.UGroup →* G) (fV : D.VGroup →* G)
variable (hf : D.Compatible fU fV)

/-- The global value constructed by finite subdivision of actual paths. -/
def globalPathValue : PathValue X G :=
  (D.localPathValue fU fV hf).extension D.chart_open D.chart_cover

theorem globalPathValue_extends :
    (D.globalPathValue fU fV hf).Extends (D.localPathValue fU fV hf) :=
  (D.localPathValue fU fV hf).extension_extends D.chart_open D.chart_cover

/-- Finite square subdivision proves homotopy invariance of the constructed value. -/
theorem globalPathValue_homotopyInvariant :
    (D.globalPathValue fU fV hf).HomotopyInvariant :=
  PathValue.homotopyInvariant_of_open_cover (D.globalPathValue fU fV hf)
    (D.localPathValue fU fV hf) D.chart_open D.chart_cover
    (D.globalPathValue_extends fU fV hf) (D.localPathValue_homotopyInvariant fU fV hf)

/-- The genuine induced homomorphism on the ambient fundamental group. -/
def lift : FundamentalGroup X D.base →* G :=
  (D.globalPathValue fU fV hf).fundamentalGroupHom
    (D.globalPathValue_homotopyInvariant fU fV hf) D.base

theorem lift_mk_of_mem (i : Bool) (p : Path D.base D.base)
    (hp : ∀ t, p t ∈ D.chart i) :
    D.lift fU fV hf (Path.Homotopic.Quotient.mk p) =
      (D.localValue fU fV i p hp)⁻¹ :=
  congrArg (fun a : G => a⁻¹) (D.globalPathValue_extends fU fV hf i p hp)

theorem lift_comp_inclusionU : (D.lift fU fV hf).comp D.inclusionHomU = fU := by
  ext γ
  obtain ⟨p⟩ := γ
  have h := D.lift_mk_of_mem fU fV hf false
    (p.map continuous_subtype_val) (fun t => (p t).property)
  rw [D.localValue_map_loop, inv_inv] at h
  exact h

theorem lift_comp_inclusionV : (D.lift fU fV hf).comp D.inclusionHomV = fV := by
  ext γ
  obtain ⟨p⟩ := γ
  have h := D.lift_mk_of_mem fU fV hf true
    (p.map continuous_subtype_val) (fun t => (p t).property)
  rw [D.localValue_map_loop, inv_inv] at h
  exact h

include hf in
/-- The Seifert--van Kampen universal property for the actual fundamental
groups of the space and its two open subspaces. -/
theorem exists_unique_lift :
    ∃! f : FundamentalGroup X D.base →* G,
      f.comp D.inclusionHomU = fU ∧ f.comp D.inclusionHomV = fV := by
  refine ⟨D.lift fU fV hf,
    ⟨D.lift_comp_inclusionU fU fV hf, D.lift_comp_inclusionV fU fV hf⟩, ?_⟩
  intro f h
  exact D.hom_ext f (D.lift fU fV hf)
    (h.1.trans (D.lift_comp_inclusionU fU fV hf).symm)
    (h.2.trans (D.lift_comp_inclusionV fU fV hf).symm)

end Wikipedia.HopfProblem.FundamentalGroupVanKampen.TwoOpenCover
