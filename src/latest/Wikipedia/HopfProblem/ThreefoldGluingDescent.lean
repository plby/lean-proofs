import Wikipedia.HopfProblem.ThreefoldGluing

/-!
# Maps descended from the actual local gluing

Compatible maps on the local pieces determine a unique map on the
constructed topological gluing. Continuity is local on the pieces.
This supplies the universal property needed when later gluing additional
geometric data; it does not assume a global target map already exists.
-/

noncomputable section

open Set Topology

universe u

namespace Wikipedia.HopfProblem.ThreefoldGluing.Data

variable {B : Type u} [TopologicalSpace B] (D : ThreefoldGluing.Data B)
    {Y : Type*}

/-- Agreement on every actual overlap. -/
def Compatible (f : ∀ i, D.piece i → Y) : Prop :=
  ∀ i j x, x ∈ (D.transition i j).source → f j (D.transition i j x) = f i x

/-- The actual descended function on the categorical/topological gluing. -/
def descend (f : ∀ i, D.piece i → Y) (_hf : D.Compatible f) (x : D.Space) : Y :=
  f (D.representative x).1 (D.representative x).2

@[simp] theorem descend_inclusion (f : ∀ i, D.piece i → Y) (hf : D.Compatible f)
    (i : D.J) (x : D.piece i) : D.descend f hf (D.inclusion i x) = f i x := by
  let r := D.representative (D.inclusion i x)
  have h := (D.inclusion_eq_iff r.1 i r.2 x).mp (D.inclusion_representative _)
  change f r.1 r.2 = f i x
  rw [← h.2]
  exact (hf r.1 i r.2 h.1).symm

theorem descend_comp_inclusion (f : ∀ i, D.piece i → Y) (hf : D.Compatible f)
    (i : D.J) : D.descend f hf ∘ D.inclusion i = f i := by
  funext x
  exact D.descend_inclusion f hf i x

/-- The descended function is determined by its restrictions to the pieces. -/
theorem descend_unique (f : ∀ i, D.piece i → Y) (hf : D.Compatible f)
    (g : D.Space → Y) (hg : ∀ i x, g (D.inclusion i x) = f i x) :
    g = D.descend f hf := by
  funext x
  obtain ⟨i, z, rfl⟩ := D.inclusion_jointly_surjective x
  rw [D.descend_inclusion, hg]

theorem map_ext {f g : D.Space → Y}
    (h : ∀ i x, f (D.inclusion i x) = g (D.inclusion i x)) : f = g := by
  funext x
  obtain ⟨i, z, rfl⟩ := D.inclusion_jointly_surjective x
  exact h i z

section Topology

variable [TopologicalSpace Y]

/-- The genuine glued topology has the expected local continuity criterion. -/
theorem continuous_iff_comp_inclusion (f : D.Space → Y) :
    Continuous f ↔ ∀ i, Continuous (f ∘ D.inclusion i) := by
  constructor
  · intro hf i
    exact hf.comp (D.inclusion_openEmbedding i).continuous
  · intro hf
    rw [continuous_def]
    intro U hU
    rw [D.gluing.isOpen_iff]
    change ∀ i : D.J, IsOpen (D.inclusion i ⁻¹' (f ⁻¹' U))
    intro i
    exact hU.preimage (hf i)

theorem descend_continuous (f : ∀ i, D.piece i → Y) (hf : D.Compatible f)
    (hc : ∀ i, Continuous (f i)) : Continuous (D.descend f hf) := by
  apply (D.continuous_iff_comp_inclusion _).mpr
  intro i
  rw [D.descend_comp_inclusion]
  exact hc i

/-- A unique continuous global map is constructed from compatible local maps. -/
theorem existsUnique_continuous_descend (f : ∀ i, D.piece i → Y)
    (hf : D.Compatible f) (hc : ∀ i, Continuous (f i)) :
    ∃! g : C(D.Space, Y), ∀ i x, g (D.inclusion i x) = f i x := by
  refine ⟨⟨D.descend f hf, D.descend_continuous f hf hc⟩, ?_, ?_⟩
  · exact D.descend_inclusion f hf
  · intro g hg
    apply ContinuousMap.coe_injective
    exact D.descend_unique f hf g hg

end Topology

end Wikipedia.HopfProblem.ThreefoldGluing.Data
