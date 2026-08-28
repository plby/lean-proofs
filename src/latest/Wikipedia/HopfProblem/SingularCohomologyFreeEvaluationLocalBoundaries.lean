import Wikipedia.HopfProblem.SingularCohomologyFreeEvaluationLocalSplitting

/-!
# Splitting the actual boundary inclusion in one degree

If the outgoing differential image and the homology in degree `n` are
projective, the actual incoming boundaries split inside the chain module
in that degree.  The construction first retracts chains onto cycles and
then subtracts a linear choice of homology representatives.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SingularCohomologyFree.LocalEvaluation

open SingularMayerVietoris.ModuleHomology

variable (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)

/-- The literal incoming boundary image inside the original chain module. -/
abbrev IncomingImage := LinearMap.range (K.d (n + 1) n).hom

instance incomingImageModule : Module ℤ (IncomingImage K n) := (IncomingImage K n).module

/-- A local choice of representatives uses projectivity in this degree alone. -/
theorem exists_cycle_section [Module.Projective ℤ (K.homology n)] :
    ∃ s : K.homology n →ₗ[ℤ] Cycle K n,
      ∀ a, cycleClass K n (s a) = a :=
  exists_section (cycleClass K n) (cycleClass_surjective K n)

/-- The actual boundary inclusion splits under local, degreewise hypotheses. -/
theorem exists_boundary_retraction [Module.Projective ℤ (OutgoingImage K n)]
    [Module.Projective ℤ (K.homology n)] :
    ∃ r : K.X n →ₗ[ℤ] IncomingImage K n,
      ∀ b : IncomingImage K n, r b = b := by
  obtain ⟨r, hr⟩ := exists_cycle_retraction K n
  obtain ⟨s, hs⟩ := exists_cycle_section K n
  let t : K.X n →ₗ[ℤ] Cycle K n := r - s.comp ((cycleClass K n).comp r)
  have ht (x : K.X n) : cycleClass K n (t x) = 0 := by
    change cycleClass K n (r x - s (cycleClass K n (r x))) = 0
    rw [map_sub, hs, sub_self]
  let t₀ : K.X n →ₗ[ℤ] K.X n := (Cycle K n).subtype.comp t
  have ht₀ (x : K.X n) : t₀ x ∈ IncomingImage K n := by
    obtain ⟨b, hb⟩ := (cycleClass_eq_zero_iff K n (t x)).mp (ht x)
    exact ⟨b, hb⟩
  refine ⟨t₀.codRestrict (IncomingImage K n) ht₀, ?_⟩
  rintro ⟨_, ⟨b, rfl⟩⟩
  apply Subtype.ext
  change (r ((K.d (n + 1) n).hom b) -
    s (cycleClass K n (r ((K.d (n + 1) n).hom b)))).val = (K.d (n + 1) n).hom b
  have hrb := hr (boundaryCycle K n b)
  rw [boundaryCycle_val] at hrb
  rw [hrb, cycleClass_boundary, map_zero, sub_zero, boundaryCycle_val]

/-- A functional vanishing on cycles is an actual incoming coboundary,
provided the preceding homology and its outgoing image are projective. -/
theorem exists_coboundary_of_vanishing_on_cycles
    [Module.Projective ℤ (OutgoingImage K n)] [Module.Projective ℤ (K.homology n)]
    (φ : K.X (n + 1) →ₗ[ℤ] ℤ)
    (hφ : ∀ z : Cycle K (n + 1), φ z.val = 0) :
    ∃ ψ : K.X n →ₗ[ℤ] ℤ, ψ.comp (K.d (n + 1) n).hom = φ := by
  have hker : LinearMap.ker (K.d (n + 1) n).hom ≤ LinearMap.ker φ := by
    intro x hx
    exact hφ (mkCycle K (n + 1) x (by change (K.d (n + 1) n).hom x = 0; exact hx))
  obtain ⟨ψ₀, hψ₀⟩ := exists_factor_through_range (K.d (n + 1) n).hom φ hker
  obtain ⟨r, hr⟩ := exists_boundary_retraction K n
  refine ⟨ψ₀.comp r, ?_⟩
  ext x
  change ψ₀ (r ((K.d (n + 1) n).hom x)) = φ x
  have hrx := hr ((K.d (n + 1) n).hom.rangeRestrict x)
  change r ((K.d (n + 1) n).hom x) = (K.d (n + 1) n).hom.rangeRestrict x at hrx
  rw [hrx]
  exact LinearMap.congr_fun hψ₀ x

end Wikipedia.HopfProblem.SingularCohomologyFree.LocalEvaluation
