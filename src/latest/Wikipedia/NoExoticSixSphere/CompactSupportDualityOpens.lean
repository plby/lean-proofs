import Wikipedia.NoExoticSixSphere.CompactSupportDualityDirectedUnion
import Wikipedia.NoExoticSixSphere.EmptyCompactSupportDuality
import Mathlib.Geometry.Manifold.HasGroupoid

/-!
# Open-set closure of the actual cap-duality property

Original open subspaces carry their inherited charted structures.
Flattening the genuine nested subtypes is a homeomorphism, so the
proved cap transport turns the open-cover theorems into binary-sup
and directed-sup closure on the lattice of actual open subsets.
-/

noncomputable section

open TopologicalSpace
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.CompactSupportCapMap

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]

/-- The empty original open subspace satisfies actual cap duality. -/
theorem duality_opens_bot : Duality (E := E) n (⊥ : Opens M) := by
  let : IsEmpty (⊥ : Opens M) := ⟨fun x => x.property⟩
  exact duality_of_isEmpty (⊥ : Opens M) (E := E) n

/-- Flatten the actual preimage open subspace under an ambient open-subspace inclusion. -/
def nestedOpenHomeomorph (W U : Opens M) (h : U ≤ W) :
    Opens.comap (subtypeInclusion (W : Set M)) U ≃ₜ U :=
  Topology.IsEmbedding.homeomorphOfSubsetRange (f := (Subtype.val : W → M))
    Topology.IsEmbedding.subtypeVal (fun x hx => ⟨⟨x, h hx⟩, rfl⟩)

/-- Original cap duality glues to the actual union of two open subsets. -/
theorem duality_opens_sup (U V : Opens M)
    (hDU : Duality (E := E) n U) (hDV : Duality (E := E) n V)
    (hDI : Duality (E := E) n (U ⊓ V : Opens M)) :
    Duality (E := E) n (U ⊔ V : Opens M) := by
  let W := U ⊔ V
  let U' : Opens W := Opens.comap (subtypeInclusion (W : Set M)) U
  let V' : Opens W := Opens.comap (subtypeInclusion (W : Set M)) V
  let eU : U' ≃ₜ U := nestedOpenHomeomorph W U le_sup_left
  let eV : V' ≃ₜ V := nestedOpenHomeomorph W V le_sup_right
  let eI : (U' ⊓ V' : Opens W) ≃ₜ (U ⊓ V : Opens M) :=
    nestedOpenHomeomorph W (U ⊓ V) (inf_le_left.trans le_sup_left)
  let : ChartedSpace E (U' : Set W) := inferInstanceAs (ChartedSpace E U')
  let : ChartedSpace E (V' : Set W) := inferInstanceAs (ChartedSpace E V')
  let : ChartedSpace E ((U' : Set W) ∩ (V' : Set W) : Set W) :=
    inferInstanceAs (ChartedSpace E (U' ⊓ V' : Opens W))
  have hcover : (U' : Set W) ∪ (V' : Set W) = Set.univ :=
    Set.eq_univ_of_forall fun x => x.property
  exact Duality.of_open_cover (E := E) n (U' : Set W) (V' : Set W) U'.isOpen V'.isOpen hcover
    (Duality.of_homeomorph (E := E) n eU.symm hDU)
    (Duality.of_homeomorph (E := E) n eV.symm hDV)
    (Duality.of_homeomorph (E := E) n eI.symm hDI)

/-- A directed supremum of actual open subspaces with cap duality has cap duality. -/
theorem duality_opens_iSup {ι : Type*} [Nonempty ι] (U : ι → Opens M)
    (hdir : Directed (· ≤ ·) U) (hD : ∀ i, Duality (E := E) n (U i)) :
    Duality (E := E) n (⨆ i, U i : Opens M) := by
  let W : Opens M := ⨆ i, U i
  let U' (i : ι) : Opens W := Opens.comap (subtypeInclusion (W : Set M)) (U i)
  let e (i : ι) : U' i ≃ₜ U i := nestedOpenHomeomorph W (U i) (le_iSup U i)
  let : ∀ i, ChartedSpace E ((U' i : Opens W) : Set W) := fun i =>
    inferInstanceAs (ChartedSpace E (U' i))
  have hd : Directed (· ⊆ ·) (fun i => (U' i : Set W)) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, fun _ hx => hik hx, fun _ hx => hjk hx⟩
  have hc : (⋃ i, (U' i : Set W)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  exact Duality.of_directed_cover (E := E) n (fun i => (U' i : Set W))
    (fun i => (U' i).isOpen) hd hc (fun i => Duality.of_homeomorph (E := E) n (e i).symm (hD i))

/-- The whole open subspace transports back to the original ambient charted manifold. -/
theorem duality_of_opens_top (hD : Duality (E := E) n (⊤ : Opens M)) : Duality (E := E) n M :=
  Duality.of_homeomorph (E := E) n (X := (⊤ : Opens M)) (Homeomorph.Set.univ M) hD

end NoExoticSixSphere.CompactSupportCapMap
