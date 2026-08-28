import Wikipedia.HopfProblem.CuspNormalizationGermsBasic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Analytic-germ coordinate changes between actual manifold charts

Each map is pullback along the actual composition of one chart with the
inverse of the other. Its inverse identities hold as neighbourhood
germs by the genuine open partial homeomorphism identities.
-/

noncomputable section

open Set Filter Topology IsManifold
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafManifoldStalk

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]
  (e d : OpenPartialHomeomorph M E)
  (he : e ∈ maximalAtlas 𝓘(ℂ, E) ω M)
  (hd : d ∈ maximalAtlas 𝓘(ℂ, E) ω M)
  (x : M) (hx : x ∈ e.source) (hdx : x ∈ d.source)

include he hd hx hdx in
/-- The actual coordinate change is complex analytic at the chart point. -/
theorem coordinateChange_analyticAt : AnalyticAt ℂ (d ∘ e.symm) (e x) := by
  have hd' : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω d (e.symm (e x)) := by
    simpa only [e.left_inv hx] using contMDiffAt_of_mem_maximalAtlas hd hdx
  exact (hd'.comp (e x)
    (contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hx))).contDiffAt.analyticAt

include hx in
omit [NormedSpace ℂ E] [ChartedSpace E M] in
theorem coordinateChange_basepoint : (d ∘ e.symm) (e x) = d x := by
  rw [Function.comp_apply, e.left_inv hx]

/-- Pullback between actual analytic-germ rings in two actual charts. -/
def coordinateHom : Germs.AnalyticGerm (d x) →+* Germs.AnalyticGerm (e x) :=
  Germs.pullbackAt (d ∘ e.symm) (coordinateChange_analyticAt e d he hd x hx hdx)
    (coordinateChange_basepoint e d x hx)

@[simp] theorem coordinateHom_ofAnalytic (f : E → ℂ) (hf : AnalyticAt ℂ f (d x)) :
    coordinateHom e d he hd x hx hdx (Germs.ofAnalytic f hf) =
      Germs.ofAnalytic (f ∘ d ∘ e.symm)
        (hf.comp_of_eq (coordinateChange_analyticAt e d he hd x hx hdx)
          (coordinateChange_basepoint e d x hx)) := by
  exact Germs.pullbackAt_ofAnalytic _ _ _ _ _

/-- The inverse chart identities give inverse maps on genuine germs. -/
theorem coordinateHom_inverse (φ : Germs.AnalyticGerm (d x)) :
    coordinateHom d e hd he x hdx hx (coordinateHom e d he hd x hx hdx φ) = φ := by
  obtain ⟨f, hf, rfl⟩ := Germs.exists_representative φ
  rw [coordinateHom_ofAnalytic, coordinateHom_ofAnalytic]
  apply (Germs.ofAnalytic_eq_iff _ _ _ _).mpr
  have ht : Tendsto d.symm (𝓝 (d x)) (𝓝 x) := (d.symm_map_nhds_eq hdx).le
  filter_upwards [d.open_target.mem_nhds (d.map_source hdx),
    ht.eventually (e.open_source.mem_nhds hx)] with z hzt hze
  change f (d (e.symm (e (d.symm z)))) = f z
  rw [e.left_inv hze, d.right_inv hzt]

/-- Actual analytic chart change on rings of convergent analytic germs. -/
def coordinateEquiv : Germs.AnalyticGerm (d x) ≃+* Germs.AnalyticGerm (e x) where
  toFun := coordinateHom e d he hd x hx hdx
  invFun := coordinateHom d e hd he x hdx hx
  left_inv := coordinateHom_inverse e d he hd x hx hdx
  right_inv := coordinateHom_inverse d e hd he x hdx hx
  map_mul' := map_mul (coordinateHom e d he hd x hx hdx)
  map_add' := map_add (coordinateHom e d he hd x hx hdx)

@[simp] theorem coordinateEquiv_apply (φ : Germs.AnalyticGerm (d x)) :
    coordinateEquiv e d he hd x hx hdx φ = coordinateHom e d he hd x hx hdx φ := rfl

@[simp] theorem coordinateEquiv_ofAnalytic (f : E → ℂ)
    (hf : AnalyticAt ℂ f (d x)) :
    coordinateEquiv e d he hd x hx hdx (Germs.ofAnalytic f hf) =
      Germs.ofAnalytic (f ∘ d ∘ e.symm)
        (hf.comp_of_eq (coordinateChange_analyticAt e d he hd x hx hdx)
          (coordinateChange_basepoint e d x hx)) :=
  coordinateHom_ofAnalytic e d he hd x hx hdx f hf

@[simp] theorem eval_coordinateEquiv (φ : Germs.AnalyticGerm (d x)) :
    Germs.eval (e x) (coordinateEquiv e d he hd x hx hdx φ) = Germs.eval (d x) φ :=
  Germs.eval_pullbackAt _ _ _ _

end Wikipedia.HopfProblem.CuspNormalization.SheafManifoldStalk
