import Wikipedia.HopfProblem.DegreeCollapseIntegralDualityDirectedUnion

/-!
# Integral cap duality on every homeomorphic copy

For cover assembly, strengthen the property to every homeomorphic
copy of a space. The Euclidean calculation already proves this
stronger statement. Binary and directed closure follow by pulling
the covers back, and homeomorphism invariance follows by composition.
Taking the identity copy recovers bijectivity of the original maps.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCapDuality

def HomeomorphicDuality (d : ℕ) (X : Type) [TopologicalSpace X] : Prop :=
  ∀ (Y : Type) [TopologicalSpace Y] [T2Space Y], (Y ≃ₜ X) → Duality d Y

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {d : ℕ}

/-- The property includes the original space and its original integral cap maps. -/
theorem HomeomorphicDuality.self [T2Space X] (hD : HomeomorphicDuality d X) : Duality d X :=
  hD X (Homeomorph.refl X)

theorem HomeomorphicDuality.of_homeomorph (e : X ≃ₜ Y) (hD : HomeomorphicDuality d X) :
    HomeomorphicDuality d Y := by
  intro Z _ _ f
  exact hD Z (f.trans e.symm)

/-- The actual preimage subspace is homeomorphic to the specified target subspace. -/
def preimageHomeomorph (e : Y ≃ₜ X) (U : Set X) : (e ⁻¹' U) ≃ₜ U :=
  Topology.IsEmbedding.homeomorphOfSubsetRange (f := (e : Y → X)) e.isEmbedding
    (fun x _hx => e.surjective x)

section Euclidean

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- The actual Euclidean cap calculation holds on every such homeomorphic copy. -/
theorem homeomorphicDuality_of_euclidean_homeomorph (e : X ≃ₜ E) :
    HomeomorphicDuality (n + 3) X := by
  intro Z _ _ f
  exact duality_of_euclidean_homeomorph n (f.trans e)

end Euclidean

variable (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

include hU hV hcover in
/-- Pulling back an actual binary cover proves closure on every homeomorphic copy. -/
theorem HomeomorphicDuality.of_open_cover
    (hDU : HomeomorphicDuality d U) (hDV : HomeomorphicDuality d V)
    (hDI : HomeomorphicDuality d (U ∩ V : Set X)) : HomeomorphicDuality d X := by
  intro Z _ _ e
  let U' : Set Z := e ⁻¹' U
  let V' : Set Z := e ⁻¹' V
  have hc' : U' ∪ V' = Set.univ := by
    change e ⁻¹' U ∪ e ⁻¹' V = Set.univ
    rw [← Set.preimage_union, hcover, Set.preimage_univ]
  exact Duality.of_open_cover U' V' (hU.preimage e.continuous) (hV.preimage e.continuous) hc'
    (hDU U' (preimageHomeomorph e U))
    (hDV V' (preimageHomeomorph e V))
    (hDI (U' ∩ V' : Set Z) (preimageHomeomorph e (U ∩ V)))

omit U V hU hV hcover in
/-- Directed covers pull back to directed covers with the same actual representative arguments. -/
theorem HomeomorphicDuality.of_directed_cover {ι : Type*} [Nonempty ι]
    (W : ι → Set X) (hW : ∀ i, IsOpen (W i)) (hdir : Directed (· ⊆ ·) W)
    (hcover : ⋃ i, W i = Set.univ) (hD : ∀ i, HomeomorphicDuality d (W i)) :
    HomeomorphicDuality d X := by
  intro Z _ _ e
  let W' (i : ι) : Set Z := e ⁻¹' W i
  have hd : Directed (· ⊆ ·) W' := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, Set.preimage_mono hik, Set.preimage_mono hjk⟩
  have hcov : ⋃ i, W' i = Set.univ := by
    change ⋃ i, e ⁻¹' W i = Set.univ
    rw [← Set.preimage_iUnion, hcover, Set.preimage_univ]
  exact Duality.of_directed_cover W' (fun i => (hW i).preimage e.continuous) hd hcov
    (fun i => hD i (W' i) (preimageHomeomorph e (W i)))

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCapDuality
