import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySphereDolbeaultKernel
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySphereDolbeaultLocal
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySphereFormsSheaf
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDolbeaultSheafExact

/-!
# The genuine short exact sphere Dolbeault sequence

The two arrows are the literal inclusion of actual holomorphic functions
and the actual antiholomorphic Fréchet derivative. The kernel theorem
and the constructed Cauchy–Green local primitives prove exactness and
epimorphy on actual stalks. Thus this is a genuine short exact sequence
of Mathlib additive sheaves, with no exactness premise.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereDolbeault

open DolbeaultLocal

abbrev holomorphicSheaf := HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ) RiemannSphere
abbrev smoothSheaf := SmoothFunctions.additiveSheaf 𝓘(ℝ, ℂ) RiemannSphere

/-- The actual differential, with naturality proved from the literal
restriction rule for the Fréchet derivative. -/
def differential : smoothSheaf ⟶ SphereForms.sheaf where
  hom :=
    { app U := AddCommGrpCat.ofHom (differentialSection U.unop).toAddMonoidHom
      naturality U V h := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro s
        exact differentialSection_restrict (leOfHom h.unop) s }

/-- The actual two consecutive arrows have zero composite. -/
theorem inclusion_differential : inclusion RiemannSphere ≫ differential = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  exact differentialSection_inclusion U.unop f

/-- The actual three sheaves and actual differential maps. -/
abbrev dolbeaultComplex :
    ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of RiemannSphere)) :=
  ShortComplex.mk (inclusion RiemannSphere) differential inclusion_differential

/-- The actual holomorphic sheaf is the kernel of the actual
antiholomorphic differential, as a statement in the sheaf category. -/
theorem dolbeaultComplex_exact : dolbeaultComplex.Exact := by
  apply exact_of_section_kernels dolbeaultComplex
  intro U s hs
  exact exists_holomorphic_preimage U s hs

/-- Actual Cauchy–Green local primitives make the genuine differential
an epimorphism of sheaves. -/
instance differential_epi : Epi differential := by
  apply epi_of_local_section_lifts differential
  intro U x hx s
  obtain ⟨V, hVU, hxV, t, ht⟩ := exists_local_primitive U x hx s
  exact ⟨V, hVU, hxV, t, ht⟩

/-- The genuine one-dimensional Dolbeault sequence on the constructed
analytic sphere is short exact, without a local-solvability hypothesis. -/
theorem dolbeaultComplex_shortExact : dolbeaultComplex.ShortExact :=
  { exact := dolbeaultComplex_exact }

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereDolbeault
