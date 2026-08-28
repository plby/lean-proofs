import Wikipedia.HopfProblem.DegreeCollapseTimeCollar
import Mathlib.Topology.Constructions.SumProd

/-!
# Joining disjoint open time collars

An actual disjoint open cover gives a homeomorphism from the sum of its
two pieces. Joining coordinates on those pieces preserves the given time
function; it does not identify the two boundary components.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.TimeBandSumCoordinates

def disjointOpenSum {X : Type*} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hcover : U ∪ V = univ) : (U ⊕ V) ≃ₜ X := by
  let f : U ⊕ V → X := Sum.elim Subtype.val Subtype.val
  have hinj : Injective f := by
    intro p q he
    rcases p with p | p <;> rcases q with q | q
    · exact congrArg Sum.inl (Subtype.ext he)
    · have he' : p.val = q.val := he
      exact False.elim (Set.disjoint_left.mp hdisj p.property (he'.symm ▸ q.property))
    · have he' : p.val = q.val := he
      exact False.elim (Set.disjoint_left.mp hdisj q.property (he' ▸ p.property))
    · exact congrArg Sum.inr (Subtype.ext he)
  have hsurj : Surjective f := by
    intro x
    have hx : x ∈ U ∪ V := hcover.symm ▸ mem_univ x
    rcases hx with hx | hx
    · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
    · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩
  exact (Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen
    (continuous_subtype_val.sumElim continuous_subtype_val)
    (hU.isOpenMap_subtype_val.sumElim hV.isOpenMap_subtype_val)

theorem disjointOpenSum_inl {X : Type*} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hcover : U ∪ V = univ) (p : U) :
    disjointOpenSum U V hU hV hdisj hcover (Sum.inl p) = p.val := rfl

theorem disjointOpenSum_inr {X : Type*} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hcover : U ∪ V = univ) (p : V) :
    disjointOpenSum U V hU hV hdisj hcover (Sum.inr p) = p.val := rfl

open Wikipedia.HopfProblem.DegreeCollapse

theorem exists_time_coordinates {M B D : Type*}
    [TopologicalSpace M] [TopologicalSpace B] [TopologicalSpace D]
    (τ : M → ℝ) (δ : ℝ) (U V : Set (TimeBand τ δ))
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V) (hcover : U ∪ V = univ)
    (eU : U ≃ₜ Ioo (-δ) δ × B) (eV : V ≃ₜ Ioo (-δ) δ × D)
    (hUt : ∀ p, (eU p).1.val = τ p.val.val)
    (hVt : ∀ p, (eV p).1.val = τ p.val.val) :
    ∃ e : TimeBand τ δ ≃ₜ Ioo (-δ) δ × (B ⊕ D),
      (∀ p, (e p).1.val = τ p.val) ∧
      (∀ p : U, e p.val = ((eU p).1, Sum.inl (eU p).2)) ∧
      ∀ p : V, e p.val = ((eV p).1, Sum.inr (eV p).2) := by
  let d := disjointOpenSum U V hU hV hdisj hcover
  let e := d.symm.trans ((eU.sumCongr eV).trans Homeomorph.prodSumDistrib.symm)
  have hleft (p : U) : e p.val = ((eU p).1, Sum.inl (eU p).2) := by
    have he : d (Sum.inl p) = p.val := rfl
    rw [← he]
    change Homeomorph.prodSumDistrib.symm ((eU.sumCongr eV) (d.symm (d (Sum.inl p)))) = _
    rw [d.symm_apply_apply]
    rfl
  have hright (p : V) : e p.val = ((eV p).1, Sum.inr (eV p).2) := by
    have he : d (Sum.inr p) = p.val := rfl
    rw [← he]
    change Homeomorph.prodSumDistrib.symm ((eU.sumCongr eV) (d.symm (d (Sum.inr p)))) = _
    rw [d.symm_apply_apply]
    rfl
  refine ⟨e, ?_, hleft, hright⟩
  intro p
  have hp : p ∈ U ∪ V := hcover.symm ▸ mem_univ p
  rcases hp with hp | hp
  · rw [hleft ⟨p, hp⟩]
    exact hUt ⟨p, hp⟩
  · rw [hright ⟨p, hp⟩]
    exact hVt ⟨p, hp⟩

end NoExoticSixSphere.TimeBandSumCoordinates
