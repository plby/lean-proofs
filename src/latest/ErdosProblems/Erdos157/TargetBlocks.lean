import ErdosProblems.Erdos157.TargetLists
import ErdosProblems.Erdos157.MaskTrialFamilies
import ErdosProblems.Erdos157.EncodingGrowth

/-! Carry-compatible target digits organized into the actual tagged blocks. -/

namespace Erdos157.Elementary

open AuxiliaryModuli

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

noncomputable def blockDataBases (i : ℕ) : List ℕ :=
  Nat.card (ResidueField K i)ˣ :: (List.replicate (i + 2) 7 ++ List.replicate (i + 2) 7)

abbrev BlockTarget (i : ℕ) := PairedTargets.Digit (Nat.card (ResidueField K i)ˣ) ×
  (Fin (i + 2) → PairedTargets.Digit 7) × (Fin (i + 2) → PairedTargets.Digit 7)

noncomputable def blockTargetEquiv (i : ℕ) :
    PairedTargets.Digits (blockDataBases K i) ≃ BlockTarget K i :=
  Equiv.prodCongr (Equiv.refl _) ((PairedTargets.appendEquiv _ _).symm.trans
    (Equiv.prodCongr (PairedTargets.replicateEquiv 7 (i + 2))
      (PairedTargets.replicateEquiv 7 (i + 2))))

theorem blockDataBases_pos (i : ℕ) : ∀ b ∈ blockDataBases K i, 0 < b := by
  intro b hb
  simp only [blockDataBases, List.mem_cons, List.mem_append, List.mem_replicate] at hb
  rcases hb with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact Nat.card_pos
  · decide
  · decide

theorem place_blockDataBases (i : ℕ) : PairedTargets.place (blockDataBases K i) = blockRadix K i := by
  simp only [PairedTargets.place, blockDataBases, List.map_cons, List.map_append,
    List.map_replicate, List.prod_cons, List.prod_append, List.prod_replicate]
  change (103 * Nat.card (ResidueField K i)ˣ) * (721 ^ (i + 2) * 721 ^ (i + 2)) = _
  rw [← pow_add, show i + 2 + (i + 2) = 2 * i + 4 by omega]
  rfl

noncomputable def levelDataBases : ℕ → List ℕ
  | 0 => []
  | k + 1 => levelDataBases k ++ blockDataBases K k

theorem levelDataBases_pos (k : ℕ) : ∀ b ∈ levelDataBases K k, 0 < b := by
  induction k with
  | zero => simp [levelDataBases]
  | succ k ih =>
    intro b hb
    rcases List.mem_append.mp hb with h | h
    · exact ih b h
    · exact blockDataBases_pos K k b h

theorem blockPlace_snoc (k : ℕ) : blockPlace K 0 (k + 1) = blockPlace K 0 k * blockRadix K k := by
  rw [blockPlace_add]
  simp only [zero_add, blockPlace, mul_one]

theorem place_levelDataBases (k : ℕ) : PairedTargets.place (levelDataBases K k) = blockPlace K 0 k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [levelDataBases, PairedTargets.place_append, ih, place_blockDataBases, blockPlace_snoc]

noncomputable def levelTargetEquiv : (k : ℕ) →
    PairedTargets.Digits (levelDataBases K k) ≃ (∀ i : Fin k, BlockTarget K i)
  | 0 =>
    { toFun := fun _ i => Fin.elim0 i
      invFun := fun _ => ()
      left_inv := fun _ => rfl
      right_inv := fun _ => funext (fun i => Fin.elim0 i) }
  | k + 1 =>
    (PairedTargets.appendEquiv _ _).symm.trans
      ((Equiv.prodCongr (levelTargetEquiv k) (blockTargetEquiv K k)).trans
        ((Equiv.prodComm _ _).trans (Fin.snocEquiv (fun i => BlockTarget K i))))

noncomputable def blockTargetDigits (i : ℕ) (d : BlockTarget K i) : List (ℕ × ℕ) :=
  (103 * Nat.card (ResidueField K i)ˣ, d.1.value) ::
    (List.ofFn (fun j => (721, (d.2.1 j).value)) ++
      List.ofFn (fun j => (721, (d.2.2 j).value)))

theorem digitList_blockTarget (i : ℕ) (d : BlockTarget K i) :
    PairedTargets.digitList ((blockTargetEquiv K i).symm d) = blockTargetDigits K i d := by
  change (103 * Nat.card (ResidueField K i)ˣ, d.1.value) ::
    PairedTargets.digitList (PairedTargets.appendEquiv _ _
      ((PairedTargets.replicateEquiv 7 (i + 2)).symm d.2.1,
        (PairedTargets.replicateEquiv 7 (i + 2)).symm d.2.2)) = _
  rw [PairedTargets.digitList_append, PairedTargets.digitList_replicate,
    PairedTargets.digitList_replicate, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

noncomputable def levelTargetValue {k : ℕ} (d : ∀ i : Fin k, BlockTarget K i) : ℕ :=
  PairedTargets.value ((levelTargetEquiv K k).symm d)

noncomputable def targetMoments {k : ℕ} (d : ∀ i : Fin k, BlockTarget K i) : MaskTarget K k where
  logarithm i := ((d i).1.data.val : LogDigit K i)
  firstMoment i := (tagCoordinates i).symm (fun j => ((d i).2.1 j).data.val)
  secondMoment i := (tagCoordinates i).symm (fun j => ((d i).2.2 j).data.val)

theorem exists_level_target_expansion (k m : ℕ) (hm : 6 * blockPlace K 0 k ≤ m + 2) :
    ∃ d : (∀ i : Fin k, BlockTarget K i), ∃ z : ℕ,
      m = levelTargetValue K d + blockPlace K 0 k * z ∧ 4 ≤ z := by
  obtain ⟨d, z, he, hz⟩ := PairedTargets.exists_expansion (levelDataBases K k)
    (levelDataBases_pos K k) m (by rwa [place_levelDataBases])
  refine ⟨levelTargetEquiv K k d, z, ?_, hz⟩
  simpa only [levelTargetValue, Equiv.symm_apply_apply, place_levelDataBases] using he

end Erdos157.Elementary
