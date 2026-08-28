import Wikipedia.NoExoticSixSphere.MooreLoopCommutatorAxes
import Wikipedia.NoExoticSixSphere.JamesSphereLoopMap
import Wikipedia.NoExoticSixSphere.FatWedgeCofibration

/-!
# Extend the actual sphere-loop commutator's axes contraction

The two based sphere-loop families carry the actual fat wedge to the
Moore-loop axes. Their constructed axes contraction extends across the
original sphere product by its proved homotopy-extension property. The
terminal map is constant on the entire fat wedge, while the homotopy
fixes the original common pole. No extension is an added hypothesis.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.SphereMooreCommutator

abbrev Parameter (n : ℕ) := Fin 2 → Sphere n
abbrev Boundary (n : ℕ) := FatWedge.space (spherePole n) 2

def point (n : ℕ) : Parameter n := fun _ ↦ spherePole n
def boundaryPoint (n : ℕ) : Boundary n := ⟨point n, 0, rfl⟩

variable (n : ℕ) {Y : Type} [TopologicalSpace Y] {y₀ : Y}
  (f g : C(Sphere n, Moore.Loop y₀))

def pairMap : C(Parameter n, Moore.Loop y₀ × Moore.Loop y₀) :=
  ⟨fun v ↦ (f (v 0), g (v 1)),
    (f.continuous.comp (continuous_apply 0)).prodMk (g.continuous.comp (continuous_apply 1))⟩

def commutator : C(Parameter n, Moore.Loop y₀) := Moore.Loop.commutatorMap.comp (pairMap n f g)

variable (hf : f (spherePole n) = 1) (hg : g (spherePole n) = 1)

include hf hg in
theorem commutator_point : commutator n f g (point n) = 1 := by
  change Moore.Loop.commutatorMap (f (spherePole n), g (spherePole n)) = 1
  rw [hf, hg, Moore.Loop.commutator_one_left, Moore.Loop.reverse_one, mul_one]

include hf hg in
theorem pairMap_mem_axes (v : Boundary n) :
    (pairMap n f g v.val).1 = 1 ∨ (pairMap n f g v.val).2 = 1 := by
  obtain ⟨i, hi⟩ := v.property
  fin_cases i
  · exact Or.inl ((congrArg f hi).trans hf)
  · exact Or.inr ((congrArg g hi).trans hg)

def boundaryToAxes : C(Boundary n, Moore.Loop.Axes y₀) :=
  ⟨fun v ↦ ⟨pairMap n f g v.val, pairMap_mem_axes n f g hf hg v⟩,
    ((pairMap n f g).continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem boundaryToAxes_point :
    boundaryToAxes n f g hf hg (boundaryPoint n) = Moore.Loop.axesPoint := by
  apply Subtype.ext
  exact Prod.ext hf hg

def boundaryHomotopy : C(I × Boundary n, Moore.Loop y₀) :=
  Moore.Loop.axesNullhomotopy.toContinuousMap.comp
    ((ContinuousMap.id I).prodMap (boundaryToAxes n f g hf hg))

theorem boundaryHomotopy_zero (v : Boundary n) :
    boundaryHomotopy n f g hf hg (0, v) = commutator n f g v.val :=
  Moore.Loop.axesNullhomotopy.apply_zero (boundaryToAxes n f g hf hg v)

theorem boundaryHomotopy_one (v : Boundary n) : boundaryHomotopy n f g hf hg (1, v) = 1 :=
  Moore.Loop.axesNullhomotopy.apply_one (boundaryToAxes n f g hf hg v)

theorem boundaryHomotopy_point (t : I) :
    boundaryHomotopy n f g hf hg (t, boundaryPoint n) = 1 := by
  change Moore.Loop.axesNullhomotopy (t, boundaryToAxes n f g hf hg (boundaryPoint n)) = 1
  rw [boundaryToAxes_point]
  exact (Moore.Loop.axesNullhomotopy.eq_fst t (Set.mem_singleton _)).trans
    Moore.Loop.axesMap_point

theorem exists_extension : ∃ H : C(I × Parameter n, Moore.Loop y₀),
    (∀ v, H (0, v) = commutator n f g v) ∧
      ∀ t (v : Boundary n), H (t, v.val) = boundaryHomotopy n f g hf hg (t, v) :=
  FatWedge.sphere_hasHomotopyExtension (spherePole n) 2 (TopCat.of (Moore.Loop y₀))
    (commutator n f g) (boundaryHomotopy n f g hf hg) (boundaryHomotopy_zero n f g hf hg)

def extension : C(I × Parameter n, Moore.Loop y₀) :=
  Classical.choose (exists_extension n f g hf hg)

theorem extension_zero (v : Parameter n) : extension n f g hf hg (0, v) = commutator n f g v :=
  (Classical.choose_spec (exists_extension n f g hf hg)).1 v

theorem extension_boundary (t : I) (v : Boundary n) :
    extension n f g hf hg (t, v.val) = boundaryHomotopy n f g hf hg (t, v) :=
  (Classical.choose_spec (exists_extension n f g hf hg)).2 t v

def terminal : C(Parameter n, Moore.Loop y₀) :=
  (extension n f g hf hg).comp ⟨fun v ↦ (1, v), continuous_const.prodMk continuous_id⟩

theorem terminal_boundary (v : Boundary n) : terminal n f g hf hg v.val = 1 :=
  (extension_boundary n f g hf hg 1 v).trans (boundaryHomotopy_one n f g hf hg v)

def extensionHomotopy : (commutator n f g).HomotopyRel (terminal n f g hf hg) {point n} where
  toContinuousMap := extension n f g hf hg
  map_zero_left := extension_zero n f g hf hg
  map_one_left _ := rfl
  prop' := by
    intro t v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    exact ((extension_boundary n f g hf hg t (boundaryPoint n)).trans
      (boundaryHomotopy_point n f g hf hg t)).trans (commutator_point n f g hf hg).symm

end NoExoticSixSphere.SphereMooreCommutator
