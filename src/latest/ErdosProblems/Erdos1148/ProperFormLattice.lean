import ErdosProblems.Erdos1148.FormLatticeCoordinates
import ErdosProblems.Erdos1148.OptimalFormEmbedding

/-! # The lattice of a primitive form has precisely the discriminant order as multiplier ring -/

namespace Erdos1148.DukeArithmetic

def latticeMultiplierRing {K : Type*} [CommRing K] (L : Submodule ℤ K) : Subring K where
  carrier := {u | ∀ z ∈ L, u * z ∈ L}
  zero_mem' := by intro z hz; rw [zero_mul]; exact L.zero_mem
  one_mem' := by intro z hz; simpa using hz
  add_mem' := by
    intro u v hu hv z hz
    rw [add_mul]
    exact L.add_mem (hu z hz) (hv z hz)
  mul_mem' := by
    intro u v hu hv z hz
    rw [mul_assoc]
    exact hu _ (hv z hz)
  neg_mem' := by
    intro u hu z hz
    rw [neg_mul]
    exact L.neg_mem (hu z hz)

noncomputable def formIdealLattice {d : ℤ} (t : ℤ × ℤ × ℤ) (ha : t.1 ≠ 0) :
    Submodule ℤ (QuadraticDiscrAlgebra d) :=
  standardRationalLattice.comap ((formLatticeCoordinates t ha).toLinearMap.restrictScalars ℤ)

lemma mem_formIdealLattice {d : ℤ} (t : ℤ × ℤ × ℤ) (ha : t.1 ≠ 0)
    (w : QuadraticDiscrAlgebra d) :
    w ∈ formIdealLattice t ha ↔ formLatticeCoordinates t ha w ∈ standardRationalLattice := Iff.rfl

theorem formIdealLattice_multiplier_ring {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) (ha : t.1 ≠ 0) :
    latticeMultiplierRing (formIdealLattice (d := d) t ha) =
      integralRationalMatrices.comap (integralFormFieldEmbedding ht).toRingHom := by
  ext w
  change (∀ z ∈ formIdealLattice t ha, w * z ∈ formIdealLattice t ha) ↔
    integralFormFieldEmbedding ht w ∈ integralRationalMatrices
  rw [← matrix_preserves_standardRationalLattice_iff]
  simp only [mem_formIdealLattice, formLatticeCoordinates_mul ht]
  constructor
  · intro h v hv
    obtain ⟨z, rfl⟩ := (formLatticeCoordinates (d := d) t ha).surjective v
    exact h z hv
  · intro h z hz
    exact h _ hz

theorem primitive_formIdealLattice_proper {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) (hprim : PrimitiveIntegralForm t) (ha : t.1 ≠ 0) :
    latticeMultiplierRing (formIdealLattice (d := d) t ha) = quadraticOrder d :=
  (formIdealLattice_multiplier_ring ht ha).trans (primitive_form_embedding_optimal ht hprim)

lemma formIdealLattice_order_mul_mem {d : ℤ} {t : ℤ × ℤ × ℤ}
    (ht : discr t = d) (ha : t.1 ≠ 0) {u z : QuadraticDiscrAlgebra d}
    (hu : u ∈ quadraticOrder d) (hz : z ∈ formIdealLattice t ha) :
    u * z ∈ formIdealLattice t ha := by
  have hu' : u ∈ latticeMultiplierRing (formIdealLattice t ha) := by
    rw [formIdealLattice_multiplier_ring ht ha]
    exact quadraticOrder_le_integral_preimage ht hu
  exact hu' z hz

end Erdos1148.DukeArithmetic
