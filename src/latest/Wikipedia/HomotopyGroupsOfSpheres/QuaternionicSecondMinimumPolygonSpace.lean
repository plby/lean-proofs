import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondMinimumPolygons
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructurePolygonMinimumPaths

/-! # The actual minimum polygon locus is homeomorphic to the anticommuting structures -/

noncomputable section

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open NoExoticSixSphere.GLOrthonormalization ComplexStructures ComplexStructureVertices

variable {n m : ℕ}

def minimumSet (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ) :
    Set (ComplexStructureVertices.Space n m) :=
  {v | v ∈ admissible a b m ∧ energy a b τ v = ((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2}

variable (a b : ComplexStructures.Space n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (hanti : (Cayley.relative a b).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hsmall : ∀ P : AnticommutingStructures.Space a, ∀ i : Fin (m + 1),
      ‖(τ i.succ - τ i.castSucc) •
        (Real.pi • (AnticommutingStructures.generatorParameter P).val.val)‖ < ShortLog.radius n)

include hτ hzero hone hanti hsmall

theorem rotationVertices_mem_minimumSet (P : AnticommutingStructures.Space a) :
    rotationVertices τ P ∈ minimumSet a b τ :=
  ⟨rotationVertices_admissible a b τ hzero hone hanti P (hsmall P),
    energy_rotationVertices a b τ hzero hone hanti P (hsmall P) hτ⟩

def minimumParametrization : C(AnticommutingStructures.Space a, minimumSet a b τ) where
  toFun P := ⟨rotationVertices τ P,
    rotationVertices_mem_minimumSet a b τ hτ hzero hone hanti hsmall P⟩
  continuous_toFun := (continuous_rotationVertices a τ).subtype_mk _

theorem minimumParametrization_injective :
    Function.Injective (minimumParametrization a b τ hτ hzero hone hanti hsmall) := by
  intro P Q h
  have hp := congrArg (fun w : minimumSet a b τ ↦ path a b τ hτ w.val w.property.1 (1 / 2)) h
  have hP : path a b τ hτ (rotationVertices τ P)
      (rotationVertices_admissible a b τ hzero hone hanti P (hsmall P)) (1 / 2) = P.val := by
    have he := path_rotationVertices a b τ hzero hone hanti P (hsmall P) hτ
      (t := 1 / 2) (by norm_num)
    rw [show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring,
      AnticommutingStructures.rotation_half_pi] at he
    exact he
  have hQ : path a b τ hτ (rotationVertices τ Q)
      (rotationVertices_admissible a b τ hzero hone hanti Q (hsmall Q)) (1 / 2) = Q.val := by
    have he := path_rotationVertices a b τ hzero hone hanti Q (hsmall Q) hτ
      (t := 1 / 2) (by norm_num)
    rw [show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring,
      AnticommutingStructures.rotation_half_pi] at he
    exact he
  exact Subtype.ext (hP.symm.trans (hp.trans hQ))

variable (hcompact : IsCompact (energySublevel a b τ (((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2)))

include hcompact

theorem minimumParametrization_surjective :
    Function.Surjective (minimumParametrization a b τ hτ hzero hone hanti hsmall) := by
  intro v
  have hv : v.val ∈ energySublevel a b τ (((4 * n + 4 : ℕ) : ℝ) * Real.pi ^ 2) :=
    ⟨v.property.1, v.property.2.le⟩
  obtain ⟨P, hP⟩ := (energy_eq_min_iff_rotation a b τ hτ hzero hone _ hcompact hanti v.val hv).mp
    v.property.2
  refine ⟨P, Subtype.ext ?_⟩
  funext i
  have ht : τ i.castSucc.succ ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← hzero]
      exact hτ.monotone (Fin.zero_le _)
    · rw [← hone]
      exact hτ.monotone (Fin.le_last _)
  have he := (path_vertex a b τ hτ v.val v.property.1 i.castSucc.succ).symm.trans (hP _ ht)
  change AnticommutingStructures.rotation P (τ i.castSucc.succ * Real.pi) = v.val i
  simpa only [vertices_interior] using he.symm

def rotationMinimumHomeomorph : AnticommutingStructures.Space a ≃ₜ minimumSet a b τ :=
  IsHomeomorph.homeomorph (minimumParametrization a b τ hτ hzero hone hanti hsmall)
    (isHomeomorph_iff_continuous_bijective.mpr
      ⟨(minimumParametrization a b τ hτ hzero hone hanti hsmall).continuous,
        minimumParametrization_injective a b τ hτ hzero hone hanti hsmall,
        minimumParametrization_surjective a b τ hτ hzero hone hanti hsmall hcompact⟩)

theorem rotationMinimumHomeomorph_apply (P : AnticommutingStructures.Space a) :
    (rotationMinimumHomeomorph a b τ hτ hzero hone hanti hsmall hcompact P).val =
      rotationVertices τ P := rfl

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
