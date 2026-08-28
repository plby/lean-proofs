import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructures
import Wikipedia.NoExoticSixSphere.PathSpaceTranslation

/-!
# The actual symplectic minimum-path family and its based loop map

The map sends a quaternionic-linear complex structure `J` to `exp(π t J)`.
It is a closed embedding into the native compact-open path space. Translating
by a fixed such path gives a based loop map. No Bott comparison is assumed.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.MinimumPaths

open ComplexStructures NoExoticSixSphere.PathFamilies

variable {n : ℕ}

/-- The induced compact-open topology on paths is Hausdorff for a Hausdorff target. -/
instance path_t2Space {X : Type*} [TopologicalSpace X] [T2Space X] (a b : X) :
    T2Space (Path a b) := by
  have he : Topology.IsEmbedding (fun p : Path a b => p.toContinuousMap) :=
    ⟨⟨rfl⟩, fun p q h => Path.ext (funext fun t => congrArg (fun f : C(I, X) => f t) h)⟩
  exact he.t2Space

def family (n : ℕ) : C(I × Space n, symplecticSubgroup n) where
  toFun z := Exponential.exp (((z.1 : ℝ) * Real.pi) • z.2.val)
  continuous_toFun := by
    have ht : Continuous (fun z : I × Space n => (z.1 : ℝ) * Real.pi) :=
      (continuous_subtype_val.comp continuous_fst).mul continuous_const
    have hJ : Continuous (fun z : I × Space n => z.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact (Exponential.contMDiff_exp (n := n)).continuous.comp (ht.smul hJ)

theorem family_zero (J : Space n) : family n (0, J) = 1 := by
  change Exponential.exp (((0 : ℝ) * Real.pi) • J.val) = 1
  rw [zero_mul, zero_smul, Exponential.exp_zero]

theorem family_one (J : Space n) : family n (1, J) = antipode n := by
  change Exponential.exp (((1 : ℝ) * Real.pi) • J.val) = antipode n
  rw [one_mul, exp_pi]

/-- The minimum-path candidate in the native compact-open topology. -/
def pathMap (n : ℕ) : C(Space n, Path (1 : symplecticSubgroup n) (antipode n)) :=
  curry (family n) family_zero family_one

theorem pathMap_apply (J : Space n) (t : I) :
    pathMap n J t = Exponential.exp (((t : ℝ) * Real.pi) • J.val) := rfl

theorem pathMap_midpoint (J : Space n) :
    pathMap n J (⟨1 / 2, by norm_num⟩ : I) = toSymplectic J := by
  rw [pathMap_apply]
  change Exponential.exp (((1 / 2 : ℝ) * Real.pi) • J.val) = toSymplectic J
  rw [show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring, exp_half_pi]

theorem pathMap_injective (n : ℕ) : Function.Injective (pathMap n) := by
  intro J K h
  have he := congrArg (fun p : Path (1 : symplecticSubgroup n) (antipode n) =>
    (p (⟨1 / 2, by norm_num⟩ : I)).val.val.val) h
  rw [pathMap_midpoint, pathMap_midpoint] at he
  exact Subtype.ext (Subtype.ext he)

theorem pathMap_isClosedEmbedding (n : ℕ) : Topology.IsClosedEmbedding (pathMap n) :=
  (pathMap n).continuous.isClosedEmbedding (pathMap_injective n)

/-- A homeomorphism onto the actual family of paths, without an altered topology. -/
def pathRangeHomeomorph (n : ℕ) : Space n ≃ₜ Set.range (pathMap n) :=
  (pathMap_isClosedEmbedding n).isEmbedding.toHomeomorph

/-- Pointwise translation by a reference minimum path, now based at the identity. -/
def loopMap (J₀ : Space n) : C(Space n, Path (1 : symplecticSubgroup n) 1) :=
  (toContinuousMap (translationHomeomorph (pathMap n J₀) (Path.refl 1))).comp (pathMap n)

theorem loopMap_reference (J₀ : Space n) : loopMap J₀ J₀ = Path.refl 1 :=
  translate_reference (pathMap n J₀) (Path.refl 1)

theorem loopMap_apply (J₀ J : Space n) (t : I) :
    loopMap J₀ J t = Exponential.exp (((t : ℝ) * Real.pi) • J.val) *
      (Exponential.exp (((t : ℝ) * Real.pi) • J₀.val))⁻¹ := by
  change pathMap n J t * (pathMap n J₀ t)⁻¹ * 1 = _
  rw [mul_one, pathMap_apply, pathMap_apply]

theorem loopMap_injective (J₀ : Space n) : Function.Injective (loopMap J₀) :=
  (translationHomeomorph (pathMap n J₀) (Path.refl 1)).injective.comp (pathMap_injective n)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.MinimumPaths
