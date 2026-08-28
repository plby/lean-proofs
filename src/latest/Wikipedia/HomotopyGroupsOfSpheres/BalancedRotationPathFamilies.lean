import Wikipedia.HomotopyGroupsOfSpheres.BalancedMinimumFamilies
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryPolygonFamilyPaths

/-! # Balanced rotation path families and their exact polygon samples -/

noncomputable section

open Set
open scoped Matrix.Norms.Frobenius

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace BalancedRealInvolutions ComplexSkewMatrices
open NoExoticSixSphere.UniformTimePartition

variable {n m : ℕ} {X : Type*} [TopologicalSpace X]

def rotationPathFamily (P : C(X, BalancedRealInvolutions.Space n)) :
    C(unitInterval × X, SpecialSpace (Index n)) :=
  let R : C(ℝ × BalancedRealInvolutions.Space n, SpecialSpace (Index n)) :=
    ⟨fun z ↦ rotation z.2 z.1, continuous_rotation n⟩
  R.comp ⟨fun z ↦ ((z.1 : ℝ) * Real.pi, P z.2),
    ((continuous_subtype_val.comp continuous_fst).mul continuous_const).prodMk
      (P.continuous.comp continuous_snd)⟩

def minimumPathParameters (F : C(unitInterval × X, SpecialSpace (Index n))) : Set X :=
  {x | ∃ P : BalancedRealInvolutions.Space n,
    ∀ u : unitInterval, F (u, x) = rotation P ((u : ℝ) * Real.pi)}

theorem rotation_eq_of_paths (P Q : BalancedRealInvolutions.Space n)
    (h : ∀ u : unitInterval, rotation P ((u : ℝ) * Real.pi) =
      rotation Q ((u : ℝ) * Real.pi)) : P = Q := by
  let half : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have he := h half
  have hcoef : (half : ℝ) * Real.pi = Real.pi / 2 := by dsimp only [half]; ring
  rw [hcoef] at he
  apply Subtype.ext
  simpa only [rotation_midpoint_recover] using
    congrArg (fun B : SpecialSpace (Index n) ↦ B.val.val.val.map Complex.im) he

theorem realizedFamily_rotation (n : ℕ)
    (τ : Fin (m + 2) → ℝ) (hτ : StrictMono τ) (hzero : τ 0 = 0)
    (hone : τ (Fin.last (m + 1)) = 1)
    (hsmall : ∀ J : BalancedRealInvolutions.Space n, ∀ i : Fin (m + 1),
      ‖(τ i.succ - τ i.castSucc) • imaginaryDirection (minimumGenerator J)‖ <
        CompatibleLog.radius (Index n))
    (P : C(X, BalancedRealInvolutions.Space n))
    (hp : ∀ x, rotationFamilyVertices τ P x ∈ admissible specialIdentity (antipode n) m) :
    realizedFamily specialIdentity (antipode n) τ hτ (rotationFamilyVertices τ P) hp =
      rotationPathFamily P := by
  apply ContinuousMap.ext
  intro z
  exact path_rotationVertices τ hzero hone (P z.2) (hsmall (P z.2))
    hτ (t := (z.1 : ℝ)) z.1.property

theorem uniform_vertices_eq_rotation_of_path (n : ℕ)
    (v : VertexSpace.Space (Index n) m) (hv : v ∈ admissible specialIdentity (antipode n) m)
    (P : BalancedRealInvolutions.Space n)
    (hpath : ∀ u : unitInterval,
      path specialIdentity (antipode n) (time m) (strictMono_time m) v hv (u : ℝ) =
        rotation P ((u : ℝ) * Real.pi)) : v = rotationVertices (time m) P := by
  funext i
  have he := hpath (unitTime m i.castSucc.succ)
  change path specialIdentity (antipode n) (time m) (strictMono_time m) v hv
    (time m i.castSucc.succ) = rotation P (time m i.castSucc.succ * Real.pi) at he
  rw [path_vertex, vertices_interior] at he
  exact he

theorem uniform_mem_minimumSet_of_path (n : ℕ)
    (hsmall : ∀ J : BalancedRealInvolutions.Space n, ∀ i : Fin (m + 1),
      ‖(time m i.succ - time m i.castSucc) • imaginaryDirection (minimumGenerator J)‖ <
        CompatibleLog.radius (Index n))
    (v : VertexSpace.Space (Index n) m) (hv : v ∈ admissible specialIdentity (antipode n) m)
    (P : BalancedRealInvolutions.Space n)
    (hpath : ∀ u : unitInterval,
      path specialIdentity (antipode n) (time m) (strictMono_time m) v hv (u : ℝ) =
        rotation P ((u : ℝ) * Real.pi)) : v ∈ minimumSet n (time m) := by
  rw [uniform_vertices_eq_rotation_of_path n v hv P hpath]
  exact rotationVertices_mem_minimumSet n (time m) (strictMono_time m)
    (time_zero m) (time_last m) hsmall P

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
