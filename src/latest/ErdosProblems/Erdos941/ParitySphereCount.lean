import ErdosProblems.Erdos941.SphereParity

/-! # At least one sixth of each relevant sphere has the chosen parity -/

namespace Erdos941

def swapMiddle : Fin 3 → Triple → Triple
  | 0, v => v
  | 1, v => (v.2.1, v.1, v.2.2)
  | 2, v => (v.1, v.2.2, v.2.1)

def flipThird (b : Bool) (v : Triple) : Triple :=
  if b then (v.1, v.2.1, -v.2.2) else v

theorem swapMiddle_involutive (i : Fin 3) (v : Triple) : swapMiddle i (swapMiddle i v) = v := by
  fin_cases i <;> rfl

theorem flipThird_involutive (b : Bool) (v : Triple) : flipThird b (flipThird b v) = v := by
  cases b <;> simp [flipThird]

theorem swapMiddle_norm (i : Fin 3) (v : Triple) : tripleNorm (swapMiddle i v) = tripleNorm v := by
  fin_cases i <;> dsimp [swapMiddle, tripleNorm, norm3] <;> ring

theorem flipThird_norm (b : Bool) (v : Triple) : tripleNorm (flipThird b v) = tripleNorm v := by
  cases b <;> simp [flipThird, tripleNorm, norm3]

theorem exists_flipThird_parity {b : Bool} {v : Triple}
    (hA : v.1 % 2 = 1) (hB : if b then v.2.1 % 4 = 2 else v.2.1 % 2 = 1)
    (hC : v.2.2 % 2 = 1) : ∃ e : Bool, SphereParity b (flipThird e v) := by
  by_cases hCA : (4 : ℤ) ∣ v.2.2 - v.1
  · exact ⟨false, hA, hB, hCA⟩
  · refine ⟨true, hA, hB, ?_⟩
    change (4 : ℤ) ∣ -v.2.2 - v.1
    omega

theorem exists_parity_normalization (b : Bool) {v : Triple}
    (hv : tripleNorm v % 8 = if b then 6 else 3) :
    ∃ i : Fin 3, ∃ e : Bool, SphereParity b (flipThird e (swapMiddle i v)) := by
  cases b with
  | false =>
    obtain ⟨hA, hB, hC⟩ := odd_coordinates_of_norm_three hv
    obtain ⟨e, he⟩ := exists_flipThird_parity (b := false) hA hB hC
    exact ⟨0, e, he⟩
  | true =>
    rcases coordinates_of_norm_six hv with ⟨hA, hB, hC⟩ | ⟨hB, hA, hC⟩ | ⟨hC, hA, hB⟩
    · obtain ⟨e, he⟩ := exists_flipThird_parity (b := true) (v := swapMiddle 1 v) hB hA hC
      exact ⟨1, e, he⟩
    · obtain ⟨e, he⟩ := exists_flipThird_parity (b := true) (v := swapMiddle 0 v) hA hB hC
      exact ⟨0, e, he⟩
    · obtain ⟨e, he⟩ := exists_flipThird_parity (b := true) (v := swapMiddle 2 v) hA hC hB
      exact ⟨2, e, he⟩

noncomputable def paritySpherePoints (n : ℕ) (b : Bool) : Finset Triple :=
  (spherePoints n).filter (SphereParity b)

theorem sphereCount_le_six_parity_count {n : ℕ} (b : Bool)
    (hn : n % 8 = if b then 6 else 3) :
    sphereCount n ≤ 6 * (paritySpherePoints n b).card := by
  classical
  let recover : Fin 3 × Bool → Triple → Triple := fun g v => swapMiddle g.1 (flipThird g.2 v)
  have hsub : spherePoints n ⊆ Finset.univ.biUnion
      (fun g : Fin 3 × Bool => (paritySpherePoints n b).image (recover g)) := by
    intro v hv
    have hnorm := mem_spherePoints.mp hv
    have hmod : tripleNorm v % 8 = if b then 6 else 3 := by rw [hnorm]; exact_mod_cast hn
    obtain ⟨i, e, hp⟩ := exists_parity_normalization b hmod
    apply Finset.mem_biUnion.mpr
    refine ⟨(i, e), Finset.mem_univ _, Finset.mem_image.mpr ?_⟩
    refine ⟨flipThird e (swapMiddle i v), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨mem_spherePoints.mpr ?_, hp⟩
      rw [flipThird_norm, swapMiddle_norm, hnorm]
    · dsimp [recover]
      rw [flipThird_involutive, swapMiddle_involutive]
  calc
    sphereCount n ≤ (Finset.univ.biUnion
        (fun g : Fin 3 × Bool => (paritySpherePoints n b).image (recover g))).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ g : Fin 3 × Bool, ((paritySpherePoints n b).image (recover g)).card := Finset.card_biUnion_le
    _ ≤ ∑ _g : Fin 3 × Bool, (paritySpherePoints n b).card :=
      Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
    _ = _ := by simp

end Erdos941
