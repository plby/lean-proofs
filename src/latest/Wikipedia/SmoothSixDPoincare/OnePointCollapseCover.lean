import Wikipedia.SmoothSixDPoincare.PuncturedRadialHomotopy
import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# A genuine two-chart cover of the collapse target

The one-point compactification is covered by the complements of finite zero
and infinity. Both pieces are contractible, and their overlap has the
original unit sphere's homotopy type through radial normalization.
-/

noncomputable section

open Set Metric Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.OnePointCover

variable {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]

def oldPatch : Set (OnePoint N) := {((0 : N) : OnePoint N)}ᶜ

def finitePatch : Set (OnePoint N) := {OnePoint.infty}ᶜ

omit [NormedSpace ℝ N] in
theorem cover : oldPatch (N := N) ∪ finitePatch = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hx : x = ((0 : N) : OnePoint N)
  · right
    subst x
    exact OnePoint.coe_ne_infty 0
  · exact Or.inl hx

variable [FiniteDimensional ℝ N]

omit [NormedSpace ℝ N] [FiniteDimensional ℝ N] in
theorem oldPatch_open : IsOpen (oldPatch (N := N)) := isClosed_singleton.isOpen_compl

omit [NormedSpace ℝ N] [FiniteDimensional ℝ N] in
theorem finitePatch_open : IsOpen (finitePatch (N := N)) := isClosed_singleton.isOpen_compl

local instance (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

private def spherePunctureHomeomorph (n : ℕ)
    (a : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    ↥({a}ᶜ : Set (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) ≃ₜ
      EuclideanSpace ℝ (Fin n) :=
  (Homeomorph.setCongr (stereographic'_source (n := n) a).symm).trans
    ((stereographic' n a).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target a)).trans (Homeomorph.Set.univ _)))

/-- Deleting any single point leaves a genuine Euclidean chart. -/
def punctureHomeomorph (a : OnePoint N) :
    ↥({a}ᶜ : Set (OnePoint N)) ≃ₜ EuclideanSpace ℝ (Fin (Module.finrank ℝ N)) := by
  let e : OnePoint N ≃ₜ sphere
      (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ N + 1))) 1 :=
    onePointEquivSphereOfFinrankEq (by simp)
  let es : ↥({a}ᶜ : Set (OnePoint N)) ≃ₜ ↥({e a}ᶜ : Set _) :=
    e.subtype (fun x => by
      change x ≠ a ↔ e x ≠ e a
      exact e.injective.ne_iff.symm)
  exact es.trans (spherePunctureHomeomorph _ (e a))

theorem oldPatch_contractible : ContractibleSpace (oldPatch (N := N)) :=
  (punctureHomeomorph ((0 : N) : OnePoint N)).contractibleSpace

theorem finitePatch_contractible : ContractibleSpace (finitePatch (N := N)) :=
  (punctureHomeomorph (OnePoint.infty : OnePoint N)).contractibleSpace

omit [NormedSpace ℝ N] [FiniteDimensional ℝ N] in
theorem overlap_subset_range : oldPatch (N := N) ∩ finitePatch ⊆ range (OnePoint.some : N → _) := by
  intro x hx
  induction x using OnePoint.rec with
  | infty => exact (hx.2 rfl).elim
  | coe x => exact ⟨x, rfl⟩

omit [NormedSpace ℝ N] [FiniteDimensional ℝ N] in
theorem overlap_preimage :
    (OnePoint.some : N → OnePoint N) ⁻¹' (oldPatch ∩ finitePatch) = {u : N | u ≠ 0} := by
  ext x
  change ((x : OnePoint N) ≠ ((0 : N) : OnePoint N) ∧
    (x : OnePoint N) ≠ OnePoint.infty) ↔ x ≠ 0
  constructor
  · rintro ⟨h, -⟩ hx
    exact h (congrArg (OnePoint.some : N → OnePoint N) hx)
  · intro hx
    exact ⟨fun h => hx (OnePoint.coe_injective h), OnePoint.coe_ne_infty x⟩

omit [FiniteDimensional ℝ N] in
def overlapHomeomorph : PuncturedRadial.Space N ≃ₜ ↥(oldPatch (N := N) ∩ finitePatch) :=
  (Homeomorph.setCongr overlap_preimage.symm).trans
    (OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphOfSubsetRange overlap_subset_range)

omit [NormedSpace ℝ N] [FiniteDimensional ℝ N] in
theorem overlapHomeomorph_apply (u : PuncturedRadial.Space N) :
    (overlapHomeomorph u).val = (u.val : OnePoint N) := rfl

omit [FiniteDimensional ℝ N] in
def overlapSphereEquiv (r : ℝ) (hr : 0 < r) :
    sphere (0 : N) 1 ≃ₕ ↥(oldPatch (N := N) ∩ finitePatch) :=
  (PuncturedRadial.sphereHomotopyEquiv r hr).trans overlapHomeomorph.toHomotopyEquiv

omit [FiniteDimensional ℝ N] in
theorem overlapSphereEquiv_apply (r : ℝ) (hr : 0 < r) (u : sphere (0 : N) 1) :
    (overlapSphereEquiv r hr u).val = ((r • (u : N) : N) : OnePoint N) := rfl

end Wikipedia.SmoothSixDPoincare.OnePointCover
