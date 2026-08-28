import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLocalExactStalks
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLocalExactMono
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLocalExactTopology
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainNullhomotopy

/-!
# Local exactness of the genuine sheafified singular cochain resolution

Classical local contractibility supplies a smaller open neighborhood whose
original inclusion is null-homotopic. Pullback of an original positive
cocycle to that neighborhood has a genuine cochain primitive. In degree
zero the pullback is an original constant cochain. The proved stalk and
sheafification comparison turns these actual local equations into
exactness of the native augmented sheaf complex in every degree.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.LocalExact

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- A closed zero-cochain becomes an actual constant after shrinking
along an actual null-homotopic open inclusion. -/
theorem exists_restriction_constant (hLC : LocallyContractibleSpace X)
    (U : Opens X) (x : X) (hx : x ∈ U) (c : Cochains U A 0)
    (hc : (singularCochainComplex U A).d 0 1 c = 0) :
    ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V) (a : A),
      (constantAugmentation X A).app (op V) a =
        (cochainPresheaf X A 0).map (homOfLE hVU).op c := by
  obtain ⟨V, hVU, hxV, hf⟩ := exists_open_nullhomotopic_inclusion X hLC U x hx
  obtain ⟨a, ha⟩ := nullhomotopic_pullback_closed_zero A
    ((Opens.toTopCat X).map (homOfLE hVU)).hom hf c hc
  exact ⟨V, hVU, hxV, a, ha.symm⟩

/-- Every actual positive cocycle has a primitive on a smaller original
open neighborhood. No contractibility of that neighborhood is assumed. -/
theorem exists_restriction_primitive (hLC : LocallyContractibleSpace X)
    (n : ℕ) (U : Opens X) (x : X) (hx : x ∈ U) (c : Cochains U A (n + 1))
    (hc : (singularCochainComplex U A).d (n + 1) (n + 2) c = 0) :
    ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V) (b : Cochains V A n),
      (singularCochainComplex V A).d n (n + 1) b =
        (cochainPresheaf X A (n + 1)).map (homOfLE hVU).op c := by
  obtain ⟨V, hVU, hxV, hf⟩ := exists_open_nullhomotopic_inclusion X hLC U x hx
  obtain ⟨b, hb⟩ := nullhomotopic_pullback_closed_succ A
    ((Opens.toTopCat X).map (homOfLE hVU)).hom hf n c hc
  exact ⟨V, hVU, hxV, b, hb⟩

/-- The original constant sheaf is precisely the kernel of the first
original sheafified singular coboundary. -/
theorem initialSheafComplex_exact (hLC : LocallyContractibleSpace X) :
    (initialSheafComplex X A).Exact := by
  let S : ShortComplex (TopCat.Presheaf AddCommGrpCat.{0} X) :=
    ShortComplex.mk (constantAugmentation X A) (presheafDifferential X A 0 1)
      (constantAugmentation_d X A)
  change (S.map (cochainSheafification X)).Exact
  apply sheafify_exact_of_local_kernels S
  intro U x hx c hc
  exact exists_restriction_constant X A hLC U x hx c hc

/-- The native sheafified singular cochain complex is exact at every
positive degree, for classical local contractibility. -/
theorem cochainSheafComplex_exactAt (hLC : LocallyContractibleSpace X) (n : ℕ) :
    (cochainSheafComplex X A).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2)
    (by simp) (by simp [Nat.add_assoc])]
  let S := (cochainPresheafComplex X A).sc' n (n + 1) (n + 2)
  change (S.map (cochainSheafification X)).Exact
  apply sheafify_exact_of_local_kernels S
  intro U x hx c hc
  exact exists_restriction_primitive X A hLC n U x hx c hc

/-- The positive homology sheaves of the actual cochain-sheaf complex
are zero. This is local exactness, not global cohomology vanishing. -/
theorem cochainSheafComplex_homology_isZero (hLC : LocallyContractibleSpace X) (n : ℕ) :
    IsZero ((cochainSheafComplex X A).homology (n + 1)) :=
  (cochainSheafComplex_exactAt X A hLC n).isZero_homology

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.LocalExact
