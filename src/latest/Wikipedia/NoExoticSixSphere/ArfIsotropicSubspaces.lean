import Wikipedia.NoExoticSixSphere.ArfMetabolic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Order.Preorder.Finite

/-!
# Maximal subspaces on which a characteristic-two quadratic form vanishes

These are ordinary submodules of the original quadratic space. An isotropic
vector orthogonal to such a subspace can be adjoined while preserving the
vanishing condition. Maximality therefore detects every isotropic vector in
its polar orthogonal complement.
-/

namespace NoExoticSixSphere.Arf

variable {V : Type*} [AddCommGroup V] [Module F₂ V]

theorem le_polarOrthogonal_of_zero (q : QuadraticForm F₂ V) (L : Submodule F₂ V)
    (hzero : ∀ l : L, q l = 0) : L ≤ L.orthogonalBilin q.polarBilin := by
  intro v hv l hl
  change q (l + v) - q l - q v = 0
  rw [hzero ⟨l + v, L.add_mem hl hv⟩, hzero ⟨l, hl⟩, hzero ⟨v, hv⟩]
  simp

theorem quadratic_zero_sup_span (q : QuadraticForm F₂ V) (L : Submodule F₂ V)
    (hzero : ∀ l : L, q l = 0) (v : V) (hv : v ∈ L.orthogonalBilin q.polarBilin)
    (hqv : q v = 0) : ∀ x : (L ⊔ Submodule.span F₂ {v} : Submodule F₂ V), q x = 0 := by
  rintro ⟨x, hx⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hb
  rw [QuadraticMap.map_add q, hzero ⟨a, ha⟩]
  have hp : q.polarBilin a (t • v) = 0 := by
    rw [map_smul, hv a ha, smul_zero]
  change 0 + q (t • v) + q.polarBilin a (t • v) = 0
  rw [hp, QuadraticMap.map_smul, hqv]
  simp

theorem mem_of_maximal_zero_of_orthogonal (q : QuadraticForm F₂ V)
    (L : Submodule F₂ V) (hL : Maximal (fun K : Submodule F₂ V ↦ ∀ x : K, q x = 0) L)
    (v : V) (hv : v ∈ L.orthogonalBilin q.polarBilin) (hqv : q v = 0) : v ∈ L := by
  have hsup := quadratic_zero_sup_span q L hL.1 v hv hqv
  have hle : L ⊔ Submodule.span F₂ {v} ≤ L := hL.2 hsup le_sup_left
  apply hle
  exact (show Submodule.span F₂ {v} ≤ L ⊔ Submodule.span F₂ {v} from le_sup_right)
    (Submodule.subset_span (Set.mem_singleton v))

theorem exists_maximal_zero_submodule [Finite V] (q : QuadraticForm F₂ V) :
    ∃ L : Submodule F₂ V, Maximal (fun K : Submodule F₂ V ↦ ∀ x : K, q x = 0) L := by
  let : Finite (Submodule F₂ V) :=
    Finite.of_injective (fun L : Submodule F₂ V ↦ (L : Set V)) SetLike.coe_injective
  have hbot : ∀ x : (⊥ : Submodule F₂ V), q x = 0 := by
    intro x
    rw [show (x : V) = 0 from x.property]
    exact q.map_zero
  obtain ⟨L, _, hL⟩ := Finite.exists_le_maximal
    (p := fun K : Submodule F₂ V ↦ ∀ x : K, q x = 0) hbot
  exact ⟨L, hL⟩

end NoExoticSixSphere.Arf
