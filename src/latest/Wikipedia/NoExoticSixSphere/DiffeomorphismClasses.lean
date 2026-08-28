import Wikipedia.NoExoticSixSphere.Definitions

/-!
# Diffeomorphism classes of smooth topological spheres

This file constructs the actual quotient of smooth manifolds homeomorphic to the
standard sphere, and identifies its subsingleton property with the requested
classification. It does not define the quotient to be a one-element type, and it
does not prove that this quotient is a subsingleton in dimension six.

The quotient here is unoriented and uses diffeomorphisms. It is not a definition
of the Kervaire--Milnor group, whose construction also involves orientations,
connected sums, and h-cobordisms.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere

/-- A smooth manifold with the topology of the `n`-sphere. Its atlas is not fixed
by the homeomorphism to the standard sphere. -/
structure SmoothSphere (n : ℕ) where
  Carrier : Type
  topology : TopologicalSpace Carrier
  charts : ChartedSpace (EuclideanSpace ℝ (Fin n)) Carrier
  smooth : IsManifold (𝓡 n) ∞ Carrier
  homeomorphic : Nonempty (Carrier ≃ₜ Sphere n)

attribute [instance] SmoothSphere.topology SmoothSphere.charts SmoothSphere.smooth

namespace SmoothSphere

/-- The standard sphere is one of the candidates for the classification. -/
noncomputable def standard (n : ℕ) : SmoothSphere n where
  Carrier := Sphere n
  topology := inferInstance
  charts := inferInstance
  smooth := inferInstance
  homeomorphic := ⟨Homeomorph.refl _⟩

/-- Bundle a candidate without changing any of its geometric structures. -/
def ofManifold {n : ℕ} (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (h : Nonempty (M ≃ₜ Sphere n)) : SmoothSphere n where
  Carrier := M
  topology := inferInstance
  charts := inferInstance
  smooth := inferInstance
  homeomorphic := h

/-- The equivalence relation is existence of a genuine smooth diffeomorphism. -/
def diffeomorphSetoid (n : ℕ) : Setoid (SmoothSphere n) where
  r M N := Nonempty (M.Carrier ≃ₘ⟮𝓡 n, 𝓡 n⟯ N.Carrier)
  iseqv := {
    refl := fun M ↦ ⟨Diffeomorph.refl (𝓡 n) M.Carrier ∞⟩
    symm := fun ⟨e⟩ ↦ ⟨e.symm⟩
    trans := fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩ }

end SmoothSphere

/-- Diffeomorphism classes, defined as a quotient of all the candidate manifolds. -/
def DiffeomorphismClasses (n : ℕ) := Quotient (SmoothSphere.diffeomorphSetoid n)

/-- The class of a particular smooth sphere. -/
def SmoothSphere.diffeomorphismClass {n : ℕ} (M : SmoothSphere n) :
    DiffeomorphismClasses n :=
  Quotient.mk _ M

/-- Equality in the quotient means actual diffeomorphism, not just homeomorphism. -/
theorem class_eq_iff_nonempty_diffeomorph {n : ℕ} (M N : SmoothSphere n) :
    M.diffeomorphismClass = N.diffeomorphismClass ↔
      Nonempty (M.Carrier ≃ₘ⟮𝓡 n, 𝓡 n⟯ N.Carrier) :=
  ⟨Quotient.exact,
    fun h ↦ @Quotient.sound (SmoothSphere n) (SmoothSphere.diffeomorphSetoid n) M N h⟩

/-- A one-class classification is precisely the assertion that every candidate is
diffeomorphic to the standard sphere. -/
theorem subsingleton_classes_iff (n : ℕ) :
    Subsingleton (DiffeomorphismClasses n) ↔
      ∀ M : SmoothSphere n, Nonempty (M.Carrier ≃ₘ⟮𝓡 n, 𝓡 n⟯ Sphere n) := by
  constructor
  · intro h M
    have hclass : M.diffeomorphismClass = (SmoothSphere.standard n).diffeomorphismClass :=
      h.elim _ _
    exact (class_eq_iff_nonempty_diffeomorph M (SmoothSphere.standard n)).mp hclass
  · intro h
    constructor
    intro a b
    induction a using Quotient.inductionOn with
    | h M =>
      induction b using Quotient.inductionOn with
      | h N =>
        obtain ⟨e⟩ := h M
        obtain ⟨f⟩ := h N
        exact Quotient.sound ⟨e.trans f.symm⟩

/-- The exact dimension-six target is equivalent to triviality of the genuine
quotient. This equivalence alone is not a proof of either proposition. -/
theorem sixSphereRigidity_iff_subsingleton_classes :
    SixSphereRigidity.{0} ↔ Subsingleton (DiffeomorphismClasses 6) := by
  rw [subsingleton_classes_iff]
  constructor
  · intro h M
    exact h M.Carrier M.topology M.charts M.smooth M.homeomorphic
  · intro h M _ _ _ he
    exact h (SmoothSphere.ofManifold M he)

end NoExoticSixSphere
