import ErdosProblems.Erdos587.HooleySeedBox
import ErdosProblems.Erdos587.HooleyLatticeSeed
import ErdosProblems.Erdos587.HooleySeedCostBounds

/-! # Full-width subset-sum progressions from a stable coefficient model -/

open scoped BigOperators Pointwise
open Erdos587.GeneralizedAP

namespace Erdos587.CFP

lemma delta_map_subsetSum_of_injOn {G : Type*} [AddCommGroup G] [DecidableEq G]
    (f : G →+ ℤ) (A : Finset G) (hinj : Set.InjOn f A) {x : G} (hx : x ∈ A.subsetSum) :
    f x ∈ (A.image f).subsetSum := by
  classical
  obtain ⟨S, hSA, rfl⟩ := Finset.mem_subsetSum_iff.mp hx
  refine Finset.mem_subsetSum_iff.mpr ⟨S.image f, Finset.image_subset_image hSA, ?_⟩
  rw [Finset.sum_image (hinj.mono hSA), map_sum]

theorem delta_full_width_GAP_of_stable_coefficients {d : ℕ}
    (A : Finset (Fin d → ℤ)) (L : Fin d → ℕ) (f : (Fin d → ℤ) →+ ℤ)
    [(generatedSubgroup id A).FiniteIndex]
    (hL : ∀ i, 0 < L i) (hA : ∀ a ∈ A, ∀ i, |a i| ≤ (L i : ℤ))
    (hinj : Set.InjOn f A) (hpositive : ∀ a ∈ A, 0 < f a)
    (h M k : ℕ) (hh : 0 < h) (hM : 1 ≤ M)
    (hdense : ∀ V ⊆ A, A.card ≤ V.card + h ^ 2 →
      2 * (nvCoordBox (fun i => 2 * (h * L i))).card < M * (h • insert 0 V).card)
    (hstable : ∀ V ⊆ A, A.card ≤ V.card + h ^ 2 →
      generatedSubgroup id V = generatedSubgroup id A)
    (hspan : ∀ V ⊆ A, k ≤ V.card →
      Submodule.span ℝ (intCastVec '' (V : Set (Fin d → ℤ))) = ⊤)
    (hreserve : ∀ S ⊆ A, S.card ≤ h ^ 2 → ∑ a ∈ S, f a ≤ ∑ a ∈ A \ S, f a)
    (hcard : 2 * k + h ^ 2 + 1 ≤ A.card)
    (hlarge : 16 * ((4 ^ d : ℕ) : ℝ) ≤
      (1 / ((4 ^ (d + 1) : ℕ) : ℝ)) * ((A.card - h ^ 2 : ℕ) : ℝ)) :
    let c := 2 * (Nat.log 2 (nvCoordBox (fun i => 2 * (h * L i))).card + 1)
    let D := M * c ^ d
    c ≤ D → (generatedSubgroup id A).index ≤ D ^ d →
      deltaSeedCostConstant d * D ^ deltaSeedPower d ≤ h →
    let K := ⌈32 * ((4 ^ d : ℕ) : ℝ) / (1 / ((4 ^ (d + 1) : ℕ) : ℝ))⌉₊
    let F := 9 * d * K
    let m := A.card - h ^ 2
    0 < F ∧ ∃ Q : GeneralizedAP, 0 < Q.rank ∧ Q.rank ≤ d ∧ Q.Proper ∧ Q.HasHomogeneousBase ∧
      (Q.carrier : Set ℤ) ⊆ ((A.image f).subsetSum : Set ℤ) ∧
      (∀ i, m ≤ F * Q.length i) ∧ m ^ (Q.rank + 1) ≤ 2 * F ^ Q.rank * Q.carrier.card ∧
      (Q.upperEndpoint : ℝ) ≤ (((3 : ℝ) / 2) * K + 1) * Q.coefficientSpan := by
  classical
  let c := 2 * (Nat.log 2 (nvCoordBox (fun i => 2 * (h * L i))).card + 1)
  let D := M * c ^ d
  let Γ := generatedSubgroup id A
  let R := fun i => deltaSeedLatticeFactor d * (Γ.index * (L i + 1) + 1)
  dsimp only
  intro hc hI hpower
  have hD : 0 < D := by dsimp [D, c]; positivity
  obtain ⟨hcost, hwidth⟩ := delta_seed_budgets_of_power_bound d D c h Γ.index hD hc hI hpower
  obtain ⟨S, hSA, hScost, _hgen, z, hz, hzΓ, hseed⟩ :=
    delta_exists_full_lattice_seed A L R hA h M (h ^ 2) hh hM hdense hstable hcost (hwidth L hL)
  have hScard : S.card ≤ h ^ 2 := hScost.trans hcost
  let U := A \ S
  have hUsub : U ⊆ A := Finset.sdiff_subset
  have hUcard : U.card = A.card - S.card := Finset.card_sdiff_of_subset hSA
  have hUpos : 0 < U.card := by omega
  have hmlower : A.card - h ^ 2 ≤ U.card := by omega
  have hUΓ : ∀ u ∈ U, u ∈ Γ := fun u hu => AddSubgroup.subset_closure ⟨u, hUsub hu, rfl⟩
  have hIpos : 0 < Γ.index := Nat.pos_of_ne_zero (AddSubgroup.FiniteIndex.index_ne_zero (H := Γ))
  let X := deltaSeedBox L Γ.index
  have hUbody : ∀ u ∈ U, intCastVec u ∈ X.body :=
    fun u hu => deltaSeedBox_contains L Γ.index hIpos u (hA u (hUsub hu))
  have hseed' : ∀ w : Γ.toIntSubmodule,
      intCastVec w.val ∈ bodyDilate (deltaSeedLatticeFactor d : ℝ) X.body →
        f (z + w.val) ∈ (S.image f).subsetSum := by
    intro w hw
    apply delta_map_subsetSum_of_injOn f S (hinj.mono hSA)
    exact hseed w.val w.property (deltaSeedBox_dilate_bound L Γ.index _ w.val hw)
  have hdisjoint : Disjoint (S.image f) (U.image f) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨u, hu, h⟩ := Finset.mem_image.mp hx'
    have heq : u = s := hinj (hUsub hu) (hSA hs) h
    exact (Finset.mem_sdiff.mp hu).2 (heq.symm ▸ hs)
  have hmass : (f z : ℝ) ≤ (1 : ℝ) * ∑ u ∈ U, (f u : ℝ) := by
    obtain ⟨W, hWS, hWsum⟩ := Finset.mem_subsetSum_iff.mp hz
    have hsz : f z ≤ ∑ s ∈ S, f s := by
      rw [← hWsum, map_sum]
      exact Finset.sum_le_sum_of_subset_of_nonneg hWS (fun a ha _ => (hpositive a (hSA ha)).le)
    have hh' := hsz.trans (hreserve S hSA hScard)
    simpa only [one_mul, ← Int.cast_sum] using (show (f z : ℝ) ≤ ((∑ u ∈ U, f u : ℤ) : ℝ) by
      exact_mod_cast hh')
  have hspan' : ∀ V ⊆ U, k ≤ V.card →
      Submodule.span ℝ (intCastVec '' (V : Set (Fin d → ℤ))) = ⊤ := by
    intro V hVU hVcard
    exact hspan V (hVU.trans hUsub) hVcard
  have hlarge' : 16 * ((4 ^ d : ℕ) : ℝ) ≤
      (1 / ((4 ^ (d + 1) : ℕ) : ℝ)) * U.card := hlarge.trans
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hmlower) (by positivity))
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hUpos
  have hhalf : 2 * k ≤ U.card := by omega
  obtain ⟨hF, Q, hQpos, hQrank, hQproper, hQhom, hQsub, hside, hsize, hheight⟩ :=
    delta_full_width_GAP_of_generated_lattice_seed X Γ
      (by change (generatedSubgroup id A).FiniteIndex; infer_instance) (deltaSeedBox_period L Γ)
      U hUΓ hUbody f ⟨z, hzΓ⟩ (S.image f) hseed' hdisjoint hUpos (hinj.mono hUsub)
      ⟨u, hu, ne_of_gt (hpositive u (hUsub hu))⟩ k hhalf hspan'
      1 (by norm_num) hmass hlarge'
  change (Q.carrier : Set ℤ) ⊆ ((S.image f ∪ U.image f).subsetSum : Set ℤ) at hQsub
  have himage : S.image f ∪ U.image f = A.image f := by
    rw [← Finset.image_union]
    congr 1
    exact Finset.union_sdiff_of_subset hSA
  rw [himage] at hQsub
  refine ⟨hF, Q, hQpos, hQrank, hQproper, hQhom, hQsub,
    (fun i => hmlower.trans (hside i)),
    (Nat.pow_le_pow_left hmlower _).trans hsize, ?_⟩
  simpa only [show X.rank = d from rfl, show (1 + 1 / 2 : ℝ) = 3 / 2 by norm_num] using hheight

end Erdos587.CFP
