import ErdosProblems.Erdos192.BoundaryMaskCertificate

namespace Erdos192

theorem residue_lt (a : Fin 4) (r : Nat) : residue a r < 43435 := by
  unfold residue
  have := Int.emod_nonneg (scalarPrefix a r) (by decide : (43435 : Int) ≠ 0)
  have := Int.emod_lt_of_pos (scalarPrefix a r) (by decide : (0 : Int) < 43435)
  omega

theorem residue_injective (a : Fin 4) (r t : Fin 85)
    (h : residue a r.val = residue a t.val) : r = t := by
  have hr := scalarPrefix_mod85 a r
  have ht := scalarPrefix_mod85 a t
  unfold residue at h
  have hn1 := Int.emod_nonneg (scalarPrefix a r.val) (by decide : (43435 : Int) ≠ 0)
  have hn2 := Int.emod_nonneg (scalarPrefix a t.val) (by decide : (43435 : Int) ≠ 0)
  have heq : scalarPrefix a r.val % 43435 = scalarPrefix a t.val % 43435 := by omega
  have heq' := congrArg (fun z : Int => z % 85) heq
  rw [Int.emod_emod_of_dvd _ (by decide : (85 : Int) ∣ 43435),
    Int.emod_emod_of_dvd _ (by decide : (85 : Int) ∣ 43435), hr, ht] at heq'
  apply Fin.ext
  omega

theorem modular_balance (A B x y z : Int)
    (hA : A % 43435 = 0) (hB : B % 43435 = 0)
    (h : (B - A + x + z - 2 * y) % 43435 = 0) :
    ((-z % 43435).toNat + (2 * y % 43435).toNat) % 43435 = (x % 43435).toNat := by
  have hAB : (B - A) % 43435 = 0 := by rw [Int.sub_emod, hA, hB]; rfl
  rw [show B - A + x + z - 2 * y = (B - A) + (x + z - 2 * y) by ring,
    Int.add_emod, hAB, Int.zero_add, Int.emod_emod] at h
  have heq : x % 43435 = (-z + 2 * y) % 43435 := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    convert h using 1 <;> congr 1 <;> ring
  have hn1 := Int.emod_nonneg (-z) (by decide : (43435 : Int) ≠ 0)
  have hn2 := Int.emod_nonneg (2 * y) (by decide : (43435 : Int) ≠ 0)
  have hn3 := Int.emod_nonneg x (by decide : (43435 : Int) ≠ 0)
  apply Int.ofNat_inj.mp
  simp only [Int.natCast_emod, Int.natCast_add, Int.toNat_of_nonneg hn1,
    Int.toNat_of_nonneg hn2, Int.toNat_of_nonneg hn3]
  change (-z % 43435 + (2 * y) % 43435) % 43435 = x % 43435
  rw [← Int.add_emod]
  exact heq.symm

theorem scalarDelta_residues (a b e : Fin 4) (r s : Fin 85)
    (h : scalarDelta a b e r.val s.val % 43435 = 0) :
    (negativeResidue e ((2 * s.val + 85000 - r.val) % 85) +
      midpointResidue b s.val) % 43435 = residue a r.val :=
  modular_balance _ _ _ _ _ (scalarPrefix_full a) (scalarPrefix_full b) h

theorem boundaryCheck_verified (a b e : Fin 4) (r s : Fin 85) :
    boundaryCheck a b e r s = true := by
  by_cases h : scalarDelta a b e r.val s.val % 43435 = 0
  · have hcert := masksCertificate_true
    simp only [masksCertificate, List.all_eq_true, List.mem_finRange,
      true_implies, Bool.and_eq_true] at hcert
    obtain ⟨hm, hc⟩ := hcert a b e s
    have ht : (2 * s.val + 85000 - r.val) % 85 < 85 := Nat.mod_lt _ (by decide)
    have hp := (masksContainPrefixes a r).1
    have he := (masksContainPrefixes e ⟨_, ht⟩).2
    have hq : midpointResidue b s.val < 43435 := by
      unfold midpointResidue
      have := Int.emod_lt_of_pos (2 * scalarPrefix b s.val) (by decide : (0 : Int) < 43435)
      omega
    have he' := rotateMask_contains 43435 negativeMasks[e.val]! (midpointResidue b s.val)
      (negativeResidue e ((2 * s.val + 85000 - r.val) % 85)) (by decide) hq (by
        unfold negativeResidue
        have := Int.emod_lt_of_pos (-scalarPrefix e ((2 * s.val + 85000 - r.val) % 85))
          (by decide : (0 : Int) < 43435)
        omega) he
    rw [scalarDelta_residues a b e r s h] at he'
    have hmem := mask_intersection_mem _ _ _ _ (beq_iff_eq.mp hm) hp he'
    obtain ⟨r', hr', heq⟩ := List.mem_map.mp hmem
    have hc' := List.all_eq_true.mp hc r' hr'
    split at hc'
    next hrlt =>
      have hr := residue_injective a ⟨r', hrlt⟩ r heq
      simpa only [hr] using hc'
    next hrlt => exact Bool.noConfusion hc'
  · simp [boundaryCheck, h]

end Erdos192
