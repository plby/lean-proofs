import Wikipedia.NoExoticSixSphere.SubspaceCofibration
import Wikipedia.NoExoticSixSphere.SpherePointCofibration

/-!
# Cofibrations for the actual fat wedges in finite Cartesian powers

The fat wedge consists of arrays with at least one basepoint entry.
Inductively it is the product-boundary union of the point inclusion and
the preceding fat wedge. The constructed neighborhood-deformation data
therefore supplies homotopy extension, in particular for actual spheres.
-/

noncomputable section

universe u

open CategoryTheory Set Topology unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.FatWedge

variable {X : Type u} [TopologicalSpace X] (b : X)

def space (k : ℕ) : Set (Fin k → X) := {v | ∃ i, v i = b}

omit [TopologicalSpace X] in
theorem space_zero : space b 0 = ∅ := by
  ext v
  simp [space]

def split (k : ℕ) : (Fin (k + 1) → X) ≃ₜ X × (Fin k → X) where
  toFun v := (v 0, fun i ↦ v i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv v := by
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  right_inv p := rfl
  continuous_toFun := (continuous_apply 0).prodMk
    (continuous_pi (fun i ↦ continuous_apply i.succ))
  continuous_invFun := by
    apply continuous_pi
    intro i
    exact Fin.cases continuous_fst
      (fun j ↦ (continuous_apply j).comp continuous_snd) i

theorem split_mem (k : ℕ) (p : X × (Fin k → X)) :
    p ∈ NeighborhoodProduct.boundary (SubspaceCofibration.inclusion ({b} : Set X))
      (SubspaceCofibration.inclusion (space b k)) ↔ (split k).symm p ∈ space b (k + 1) := by
  change (p.1 ∈ Set.range (SubspaceCofibration.inclusion ({b} : Set X)) ∨
    p.2 ∈ Set.range (SubspaceCofibration.inclusion (space b k))) ↔ _
  rw [SubspaceCofibration.mem_range, SubspaceCofibration.mem_range]
  change (p.1 = b ∨ ∃ i, p.2 i = b) ↔
    ∃ i, (Fin.cons p.1 p.2 : Fin (k + 1) → X) i = b
  simp only [Fin.exists_fin_succ, Fin.cons_zero, Fin.cons_succ]

def data (D : NeighborhoodDeformation.Data (SubspaceCofibration.inclusion ({b} : Set X))) :
    (k : ℕ) → NeighborhoodDeformation.Data (SubspaceCofibration.inclusion (space b k))
  | 0 => by
      rw [space_zero]
      exact SubspaceCofibration.emptyData
  | k + 1 =>
      SubspaceCofibration.transport (split k).symm (split_mem b k)
        (NeighborhoodProduct.data D (data D k))

theorem hasHomotopyExtension
    (D : NeighborhoodDeformation.Data (SubspaceCofibration.inclusion ({b} : Set X))) (k : ℕ) :
    HomotopyExtension.HasHomotopyExtension (SubspaceCofibration.inclusion (space b k)) :=
  SubspaceCofibration.hasHomotopyExtension (data b D k)

theorem isClosed (D : NeighborhoodDeformation.Data
    (SubspaceCofibration.inclusion ({b} : Set X))) (k : ℕ) : IsClosed (space b k) := by
  have h := NeighborhoodDeformation.range_isClosed (data b D k)
  have hr : Set.range (SubspaceCofibration.inclusion (space b k)) = space b k := by
    ext x
    exact SubspaceCofibration.mem_range _ x
  rwa [hr] at h

def sphereData {n : ℕ} (b : Sphere n) (k : ℕ) :
    NeighborhoodDeformation.Data (SubspaceCofibration.inclusion (space b k)) :=
  data b (SpherePointCofibration.data b) k

theorem sphere_hasHomotopyExtension {n : ℕ} (b : Sphere n) (k : ℕ) :
    HomotopyExtension.HasHomotopyExtension (SubspaceCofibration.inclusion (space b k)) :=
  SubspaceCofibration.hasHomotopyExtension (sphereData b k)

end NoExoticSixSphere.FatWedge
