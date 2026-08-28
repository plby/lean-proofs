import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Connecting maps for acyclic resolutions

These are the genuine connecting maps of Mathlib's `Ext` long exact
sequence. Vanishing hypotheses are imposed only on the specified terms
of a resolution, never on its cohomology comparison.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The actual covariant `Ext` connecting homomorphism. -/
def connecting (P : C) {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ) :
    Ext P S.X₃ n →+ Ext P S.X₁ (n + 1) :=
  hS.extClass.postcomp P rfl

@[simp] theorem connecting_apply (P : C) {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ) (x : Ext P S.X₃ n) :
    connecting P hS n x = x.comp hS.extClass rfl := rfl

/-- Vanishing of the next cohomology of the middle term makes the
actual connecting map surjective. -/
theorem connecting_surjective (P : C) {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ) [Subsingleton (Ext P S.X₂ (n + 1))] :
    Function.Surjective (connecting P hS n) := by
  intro x
  exact Ext.covariant_sequence_exact₁ P hS x (Subsingleton.elim _ _) rfl

/-- Vanishing of the preceding cohomology of the middle term makes
the actual connecting map injective. -/
theorem connecting_injective (P : C) {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ) [Subsingleton (Ext P S.X₂ n)] :
    Function.Injective (connecting P hS n) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ P hS x rfl hx
  have hy0 : y = 0 := Subsingleton.elim _ _
  simpa only [hy0, Ext.zero_comp] using hy.symm

/-- Dimension shifting through an acyclic middle term, using the
actual connecting map as the forward map. -/
def connectingEquiv (P : C) {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
    [Subsingleton (Ext P S.X₂ n)] [Subsingleton (Ext P S.X₂ (n + 1))] :
    Ext P S.X₃ n ≃+ Ext P S.X₁ (n + 1) :=
  AddEquiv.ofBijective (connecting P hS n)
    ⟨connecting_injective P hS n, connecting_surjective P hS n⟩

@[simp] theorem connectingEquiv_apply (P : C) {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ) [Subsingleton (Ext P S.X₂ n)]
    [Subsingleton (Ext P S.X₂ (n + 1))] (x : Ext P S.X₃ n) :
    connectingEquiv P hS n x = connecting P hS n x := rfl

/-- Exactness immediately before the genuine connecting map. -/
theorem connecting_exact (P : C) {S : ShortComplex C}
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact ((Ext.mk₀ S.g).postcomp P (add_zero n))
      (connecting P hS n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Ext.covariant_sequence_exact₃' P hS n (n + 1) rfl)

/-- The connecting map commutes with a morphism of actual short
exact sequences, including actual scalar sheaf endomorphisms. -/
theorem connecting_naturality (P : C) {S T : ShortComplex C}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S ⟶ T) (n : ℕ)
    (x : Ext P S.X₃ n) :
    connecting P hT n ((Ext.mk₀ φ.τ₃).postcomp P (add_zero n) x) =
      (Ext.mk₀ φ.τ₁).postcomp P (add_zero (n + 1)) (connecting P hS n x) := by
  change (x.comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp hT.extClass rfl =
    (x.comp hS.extClass rfl).comp (Ext.mk₀ φ.τ₁) (add_zero (n + 1))
  rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    hS.extClass_naturality hT φ]

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution
