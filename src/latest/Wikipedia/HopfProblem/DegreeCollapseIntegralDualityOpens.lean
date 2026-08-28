import Wikipedia.HopfProblem.DegreeCollapseIntegralEmptyDuality

/-!
# Open-lattice closure for integral cap duality on all homeomorphic copies

The actual nested open subtypes flatten by homeomorphisms. The proved
binary and directed cover statements therefore give closure under
binary and directed suprema in the original open-set lattice.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCapDuality

open SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] (d : ℕ)

theorem duality_opens_bot : HomeomorphicDuality d (⊥ : Opens X) := by
  let : IsEmpty (⊥ : Opens X) := ⟨fun x => x.property⟩
  exact homeomorphicDuality_of_isEmpty (⊥ : Opens X) d

/-- The actual preimage open subspace under inclusion flattens to the specified subspace. -/
def nestedOpenHomeomorph (W U : Opens X) (h : U ≤ W) :
    Opens.comap (subtypeInclusion (W : Set X)) U ≃ₜ U :=
  Topology.IsEmbedding.homeomorphOfSubsetRange (f := (Subtype.val : W → X))
    Topology.IsEmbedding.subtypeVal (fun x hx => ⟨⟨x, h hx⟩, rfl⟩)

theorem duality_opens_sup (U V : Opens X)
    (hDU : HomeomorphicDuality d U) (hDV : HomeomorphicDuality d V)
    (hDI : HomeomorphicDuality d (U ⊓ V : Opens X)) :
    HomeomorphicDuality d (U ⊔ V : Opens X) := by
  let W := U ⊔ V
  let U' : Opens W := Opens.comap (subtypeInclusion (W : Set X)) U
  let V' : Opens W := Opens.comap (subtypeInclusion (W : Set X)) V
  let eU : U' ≃ₜ U := nestedOpenHomeomorph W U le_sup_left
  let eV : V' ≃ₜ V := nestedOpenHomeomorph W V le_sup_right
  let eI : (U' ⊓ V' : Opens W) ≃ₜ (U ⊓ V : Opens X) :=
    nestedOpenHomeomorph W (U ⊓ V) (inf_le_left.trans le_sup_left)
  have hcover : (U' : Set W) ∪ (V' : Set W) = Set.univ :=
    Set.eq_univ_of_forall fun x => x.property
  exact HomeomorphicDuality.of_open_cover (U' : Set W) (V' : Set W)
    U'.isOpen V'.isOpen hcover
    (HomeomorphicDuality.of_homeomorph eU.symm hDU)
    (HomeomorphicDuality.of_homeomorph eV.symm hDV)
    (HomeomorphicDuality.of_homeomorph eI.symm hDI)

theorem duality_opens_iSup {ι : Type*} [Nonempty ι] (U : ι → Opens X)
    (hdir : Directed (· ≤ ·) U) (hD : ∀ i, HomeomorphicDuality d (U i)) :
    HomeomorphicDuality d (⨆ i, U i : Opens X) := by
  let W : Opens X := ⨆ i, U i
  let U' (i : ι) : Opens W := Opens.comap (subtypeInclusion (W : Set X)) (U i)
  let e (i : ι) : U' i ≃ₜ U i := nestedOpenHomeomorph W (U i) (le_iSup U i)
  have hd : Directed (· ⊆ ·) (fun i => (U' i : Set W)) := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, fun _ hx => hik hx, fun _ hx => hjk hx⟩
  have hc : (⋃ i, (U' i : Set W)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  exact HomeomorphicDuality.of_directed_cover (fun i => (U' i : Set W))
    (fun i => (U' i).isOpen) hd hc
    (fun i => HomeomorphicDuality.of_homeomorph (e i).symm (hD i))

theorem duality_of_opens_top (hD : HomeomorphicDuality d (⊤ : Opens X)) :
    HomeomorphicDuality d X :=
  HomeomorphicDuality.of_homeomorph (X := (⊤ : Opens X)) (Homeomorph.Set.univ X) hD

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCapDuality
