import Wikipedia.HomotopyGroupsOfSpheres.SpherePinchTopology
import Wikipedia.SmoothSixDPoincare.CoverConnectingNaturality

/-!
# The actual homology map of a sphere quotient with one exceptional fiber

Both punctured-sphere covers are contractible. The quotient is an actual
homeomorphism on their intersections, so naturality of Mayer--Vietoris proves
that its original homology map is an isomorphism in degrees at least two.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.SpherePinch

open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.CuspCentralHomology
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.SmoothSixDPoincare

local instance (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) := ⟨by simp⟩

variable {n m : ℕ} (f : C(Sphere n, Sphere m)) (b : Sphere m)
variable (hq : IsQuotientMap f)
variable (hi : ∀ u v, f u ≠ b → f u = f v → u = v)
variable (p : Sphere n) (hp : f p ≠ b)

include hq hi hp in
theorem homologyMap_bijective (k : ℕ) : Function.Bijective (singularHomologyMap f (k + 2)) := by
  let : ContractibleSpace ({p}ᶜ : Set (Sphere n)) :=
    SpherePoint.puncture_contractible (n := n) p
  let : ContractibleSpace (patch f b) := patch_contractible f b hq hi
  let : ContractibleSpace ({f p}ᶜ : Set (Sphere m)) :=
    SpherePoint.puncture_contractible (n := m) (f p)
  let : ContractibleSpace ({b}ᶜ : Set (Sphere m)) :=
    SpherePoint.puncture_contractible (n := m) b
  let es := contractibleCoverHomologyHigherEquiv {p}ᶜ (patch f b)
    isClosed_singleton.isOpen_compl (patch_open f b) (source_cover f b p hp) k
  let et := contractibleCoverHomologyHigherEquiv {f p}ᶜ {b}ᶜ
    isClosed_singleton.isOpen_compl isClosed_singleton.isOpen_compl (target_cover f b p hp) k
  let eo := homotopyEquivHomologyEquiv
    (overlapHomeomorph f b hq hi p hp).toHomotopyEquiv (k + 1)
  have he (a : SingularHomology (Sphere n) (k + 2)) :
      eo (es a) = et (singularHomologyMap f (k + 2) a) := by
    have h := CoverNaturality.connecting_naturality_apply {p}ᶜ (patch f b) {f p}ᶜ {b}ᶜ
      f (maps_puncture f b hi p hp) (fun _ hx ↦ hx)
      isClosed_singleton.isOpen_compl (patch_open f b) (source_cover f b p hp)
      isClosed_singleton.isOpen_compl isClosed_singleton.isOpen_compl
      (target_cover f b p hp) (k + 1) a
    exact h
  constructor
  · intro a c hac
    apply es.injective
    apply eo.injective
    rw [he, he, hac]
  · intro a
    refine ⟨es.symm (eo.symm (et a)), et.injective ?_⟩
    rw [← he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

def homologyEquiv (k : ℕ) :
    SingularHomology (Sphere n) (k + 2) ≃ₗ[ℤ] SingularHomology (Sphere m) (k + 2) :=
  LinearEquiv.ofBijective (singularHomologyMap f (k + 2))
    (homologyMap_bijective f b hq hi p hp k)

theorem homologyEquiv_apply (k : ℕ) (a : SingularHomology (Sphere n) (k + 2)) :
    homologyEquiv f b hq hi p hp k a = singularHomologyMap f (k + 2) a := rfl

end Wikipedia.HomotopyGroupsOfSpheres.SpherePinch
