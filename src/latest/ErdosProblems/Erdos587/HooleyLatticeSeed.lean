import ErdosProblems.Erdos587.HooleyCenteredCoarseSeed
import ErdosProblems.Erdos587.HooleyResidueSeed
import ErdosProblems.Erdos587.ReserveHomogeneity

/-! # A small seed covering every generated-lattice point of a prescribed box -/

open scoped BigOperators Pointwise

namespace Erdos587.CFP

lemma delta_subsetSum_mem_generated {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) {x : G} (hx : x ∈ A.subsetSum) : x ∈ generatedSubgroup id A := by
  obtain ⟨S, hSA, rfl⟩ := Finset.mem_subsetSum_iff.mp hx
  exact AddSubgroup.sum_mem _ (fun a ha => AddSubgroup.subset_closure ⟨a, hSA ha, rfl⟩)

theorem delta_exists_full_lattice_seed {d : ℕ} (A : Finset (Fin d → ℤ))
    (L R : Fin d → ℕ) (hA : ∀ a ∈ A, ∀ i, |a i| ≤ (L i : ℤ))
    (h M r : ℕ) (hh : 0 < h) (hM : 1 ≤ M)
    (hdense : ∀ D ⊆ A, A.card ≤ D.card + r →
      2 * (nvCoordBox (fun i => 2 * (h * L i))).card < M * (h • insert 0 D).card)
    (hstable : ∀ D ⊆ A, A.card ≤ D.card + r → generatedSubgroup id D = generatedSubgroup id A) :
    let T := (nvCoordBox (fun i => 2 * (h * L i))).card
    let c := 2 * (Nat.log 2 T + 1)
    let D := M * c ^ d
    let q := denseBoxCount D d
    let F := nvDenseFactor D d * (q + 1) ^ d
    let J := (2 * q * F) ^ d
    q * (c * h) + J ^ 2 ≤ r →
    (∀ i, 2 * F * (R i + J * L i + 1) ≤ 2 * (h * L i)) →
    ∃ S ⊆ A, S.card ≤ q * (c * h) + J ^ 2 ∧
      generatedSubgroup id (A \ S) = generatedSubgroup id A ∧
      ∃ z ∈ S.subsetSum, z ∈ generatedSubgroup id A ∧
        ∀ x ∈ generatedSubgroup id A, (∀ i, |x i| ≤ (R i : ℤ)) → z + x ∈ S.subsetSum := by
  classical
  let T := (nvCoordBox (fun i => 2 * (h * L i))).card
  let c := 2 * (Nat.log 2 T + 1)
  let D := M * c ^ d
  let q := denseBoxCount D d
  let F := nvDenseFactor D d * (q + 1) ^ d
  let B := 2 * q * F
  let J := B ^ d
  dsimp only
  intro hbudget hlarge
  change q * (c * h) + J ^ 2 ≤ r at hbudget
  change ∀ i, 2 * F * (R i + J * L i + 1) ≤ 2 * (h * L i) at hlarge
  have hD : 0 < D := by dsimp [D, c]; positivity
  have hJle : J ≤ J ^ 2 := by
    by_cases hJ : J = 0
    · simp [hJ]
    · have : 1 ≤ J := by omega
      nlinarith
  obtain ⟨U, hUA, hUcard, z, P, hproper, haxis, hsub, hcard, hexc⟩ :=
    delta_exists_coarse_coordinate_seed A L hA h M r hh hM hdense
      ((Nat.le_add_right _ _).trans hbudget)
  change U.card ≤ q * (c * h) at hUcard
  obtain ⟨a, ha, z₀, hz₀, hcoarse⟩ := delta_centered_coarse_seed_of_bounds U z P hproper haxis
    hsub (fun i => 2 * (h * L i)) (fun i => R i + J * L i) (nvDenseFactor D d) q
    (nvDenseFactor_pos hD) hcard (fun i => hexc i i) hlarge
  let Δ := coordinateMultiples a
  let _ : Δ.FiniteIndex := coordinateMultiples_finiteIndex a (fun i => (ha i).1)
  have hindex : Δ.index ≤ J := by
    simpa only [Fintype.card_fin] using
      coordinateMultiples_index_le_pow a (fun i => (ha i).1) B (fun i => (ha i).2)
  have hreserve : U.card + J ≤ r :=
    (Nat.add_le_add hUcard hJle).trans hbudget
  obtain ⟨hgen, hresstable⟩ := stable_generators_after_reserving id A U hUA r J hreserve hstable
  have hseed : ∀ w ∈ Δ, (∀ i, |(w i : ℝ)| ≤ (R i : ℝ) + (Δ.index : ℝ) * L i) →
      z₀ + w ∈ U.subsetSum := by
    intro w hw hb
    apply hcoarse w hw
    intro i
    have hb' : |(w i : ℝ)| ≤ ((R i + J * L i : ℕ) : ℝ) := by
      calc
        _ ≤ (R i : ℝ) + (Δ.index : ℝ) * L i := hb i
        _ ≤ (R i : ℝ) + (J : ℝ) * L i := add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (by exact_mod_cast hindex) (by positivity))
        _ = _ := by push_cast; rfl
    exact_mod_cast hb'
  have hdisjoint : Disjoint U ((A \ U).image (fun x => (AddMonoidHom.id (Fin d → ℤ)) (id x))) := by
    change Disjoint U ((A \ U).image id)
    rw [Finset.image_id]
    exact Finset.disjoint_left.mpr (fun x hx hx' => (Finset.mem_sdiff.mp hx').2 hx)
  obtain ⟨W, hW, hWcard, hcover⟩ := delta_residue_pool_fills_lattice_box id
    (AddMonoidHom.id (Fin d → ℤ)) U (A \ U) Δ J (hindex.trans (Nat.le_succ _)) hresstable
    (fun i => (L i : ℝ)) (fun i => (R i : ℝ)) (fun _ => by positivity)
    (fun x hx i => by exact_mod_cast hA x (Finset.mem_sdiff.mp hx).1 i) z₀ hseed
    (fun _ _ _ _ h => h) hdisjoint
  let S := U ∪ W
  have hSA : S ⊆ A := Finset.union_subset hUA (hW.trans Finset.sdiff_subset)
  have hScard : S.card ≤ q * (c * h) + J ^ 2 :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add hUcard
      (hWcard.trans (Nat.pow_le_pow_left hindex 2)))
  have hSgen : generatedSubgroup id (A \ S) = generatedSubgroup id A := by
    apply hstable _ Finset.sdiff_subset
    rw [Finset.card_sdiff_of_subset hSA]
    have := Finset.card_le_card hSA
    have := hScard.trans hbudget
    omega
  refine ⟨S, hSA, hScard, hSgen, z₀,
    Finset.subsetSum_mono Finset.subset_union_left hz₀,
    (generatedSubgroup_mono id hUA) (delta_subsetSum_mem_generated U hz₀), ?_⟩
  intro x hx hb
  have hx' : x ∈ generatedSubgroup id (A \ U) := hgen.symm ▸ hx
  have hh := hcover x hx' (fun i => by exact_mod_cast hb i)
  change z₀ + x ∈ (U ∪ W.image id).subsetSum at hh
  rw [Finset.image_id] at hh
  exact hh

end Erdos587.CFP
