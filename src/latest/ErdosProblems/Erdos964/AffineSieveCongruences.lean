import ErdosProblems.Erdos964.Basic
import BoundedGaps.Maynard.ImprovedGPY.CongruenceCount

/-!
# Congruence counting for affine sieve forms

Invert the leading coefficient modulo each divisor, then combine the
resulting congruences with the pre-sieving residue by CRT. This supplies
the arithmetic counting step for general affine forms, not just shifts.
-/

namespace Erdos964

open BoundedGaps.Maynard

noncomputable def affineRoot (A B m : ℕ) : ℕ :=
  (-(B : ZMod m) * (A : ZMod m)⁻¹).val

theorem affineRoot_dvd (A B m : ℕ) (hm : 0 < m) (hA : A.Coprime m) :
    m ∣ A * affineRoot A B m + B := by
  let : NeZero m := ⟨hm.ne'⟩
  apply (ZMod.natCast_eq_zero_iff _ m).mp
  rw [Nat.cast_add, Nat.cast_mul, affineRoot, ZMod.natCast_zmod_val]
  calc
    _ = -(B : ZMod m) * ((A : ZMod m) * (A : ZMod m)⁻¹) + B := by ring
    _ = 0 := by rw [ZMod.coe_mul_inv_eq_one A hA]; ring

theorem modEq_affineRoot_iff (A B m n : ℕ) (hm : 0 < m) (hA : A.Coprime m) :
    n ≡ affineRoot A B m [MOD m] ↔ m ∣ A * n + B := by
  have hroot := Nat.modEq_zero_iff_dvd.mpr (affineRoot_dvd A B m hm hA)
  constructor
  · intro hn
    exact Nat.modEq_zero_iff_dvd.mp (((hn.mul_left A).add_right B).trans hroot)
  · intro hn
    have hadd := (Nat.modEq_zero_iff_dvd.mpr hn).trans hroot.symm
    exact (Nat.ModEq.add_right_cancel' B hadd).cancel_left_of_coprime hA.symm

theorem exists_affine_sieve_crt {ι : Type*} (A B m : ι → ℕ) (l : List ι)
    (W v : ℕ) (hcompat : IsPreSievedModuliCompatible W m l)
    (hm : ∀ i ∈ l, 0 < m i) (hA : ∀ i ∈ l, (A i).Coprime (m i)) :
    ∃ c : ℕ, ∀ n : ℕ,
      n ≡ c [MOD W * (l.map m).prod] ↔
        n ≡ v [MOD W] ∧ ∀ i ∈ l, m i ∣ A i * n + B i := by
  let a := fun i => affineRoot (A i) (B i) (m i)
  refine ⟨Nat.chineseRemainderOfList (preSievedResidue v a)
    (preSievedModulus W m) (preSievedModulusList l)
    (preSievedModulusList_pairwise W m l hcompat), ?_⟩
  intro n
  rw [← preSievedModulusList_prod W m l, modEq_preSieved_crt_iff a m l W v n hcompat]
  exact and_congr_right (fun _ => forall_congr' (fun i => forall_congr'
    (fun hi => modEq_affineRoot_iff (A i) (B i) (m i) n (hm i hi) (hA i hi))))

theorem affine_sieve_count_error_le_one {ι : Type*} (A B m : ι → ℕ)
    (l : List ι) (W v N : ℕ) (hW : 0 < W)
    (hcompat : IsPreSievedModuliCompatible W m l)
    (hm : ∀ i ∈ l, 0 < m i) (hA : ∀ i ∈ l, (A i).Coprime (m i)) :
    |(((Finset.Ico N (2 * N)).filter (fun n =>
        n ≡ v [MOD W] ∧ ∀ i ∈ l, m i ∣ A i * n + B i)).card : ℝ) -
      (N : ℝ) / (W * (l.map m).prod)| ≤ 1 := by
  classical
  obtain ⟨c, hc⟩ := exists_affine_sieve_crt A B m l W v hcompat hm hA
  have hprod : 0 < (l.map m).prod := by
    apply List.prod_pos
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact hm i hi
  have hset : (Finset.Ico N (2 * N)).filter (fun n =>
      n ≡ v [MOD W] ∧ ∀ i ∈ l, m i ∣ A i * n + B i) =
      (Finset.Ico N (2 * N)).filter (fun n => n ≡ c [MOD W * (l.map m).prod]) := by
    apply Finset.filter_congr
    intro n _
    exact (hc n).symm
  rw [hset]
  obtain ⟨err, herr, heq⟩ := doublingIntervalModEq_card_decomposition N
    (W * (l.map m).prod) c (Nat.mul_pos hW hprod)
  simp only [Nat.cast_mul] at heq
  rw [heq]
  simpa only [add_sub_cancel_left] using herr

end Erdos964
