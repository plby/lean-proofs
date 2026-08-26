import ErdosProblems.Erdos157b.TargetBlocks

/-! Finite choices at one polynomial level and their local encoded values. -/

namespace Erdos157.Binary

open Erdos157.Elementary

open AuxiliaryModuli Polynomial PolynomialCharacters

variable (K : Type*) [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

abbrev LocalChoice (k : ℕ) := (∀ i : Fin k, BlockChoice i) × Fin (Fintype.card K ^ (3 * k))

noncomputable def primeAtLevelResidue (k : ℕ) (f : LevelLabel K k) (i : ℕ) : (ResidueField K i)ˣ :=
  (isUnit_mk_of_isCoprime (factor K i) f.1.1
    ((factor_irreducible K i).coprime_iff_not_dvd.mpr
      (factor_not_dvd_even_prime K (levelDegree_even k) f i))).unit

noncomputable def localValue (τ : MaskChoice K) (k : ℕ) (f : LevelLabel K k) (c : LocalChoice K k) : ℕ :=
  MixedRadix.encode ((List.ofFn (fun i : Fin k =>
    blockDigits K i (τ i) (primeAtLevelResidue K k f i) (c.1 i))).flatten) +
      blockPlace K 0 k * (1 + c.2.val)

theorem digitBlocks_eq_flatten (τ : MaskChoice K) (ω : IntegerParameters K)
    (f : Label K) (i n : ℕ) :
    digitBlocks K τ ω f i n =
      (List.ofFn (fun j : Fin n => blockDigits K (i + j) (τ (i + j))
        (labelResidue K f (i + j)) (ω.block f (i + j)))).flatten := by
  induction n generalizing i with
  | zero => simp [digitBlocks]
  | succ n ih =>
    rw [digitBlocks, List.ofFn_succ, List.flatten_cons, ih]
    simp only [Fin.val_zero, add_zero, Fin.val_succ]
    congr 3
    funext j
    rw [show i + 1 + (j : ℕ) = i + ((j : ℕ) + 1) by omega]

theorem localValue_eq_encoded (τ : MaskChoice K) (ω : IntegerParameters K)
    (f : Label K) (c : LocalChoice K f.level)
    (hc : ∀ i : Fin f.level, ω.block f i = c.1 i) (ht : ω.top f = c.2) :
    localValue K τ f.level f.2 c = encoded K τ ω f := by
  rw [encoded, digitBlocks_eq_flatten, ht]
  dsimp only [localValue]
  apply congrArg (fun a => a + blockPlace K 0 f.level * (1 + c.2.val))
  apply congrArg MixedRadix.encode
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [Nat.zero_add, hc i]
  rfl

theorem digitList_levelTarget (k : ℕ) (d : ∀ i : Fin k, BlockTarget K i) :
    PairedTargets.digitList ((levelTargetEquiv K k).symm d) =
      (List.ofFn (fun i => blockTargetDigits K i (d i))).flatten := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change PairedTargets.digitList (PairedTargets.appendEquiv _ _
      ((levelTargetEquiv K k).symm (fun i => d i.castSucc),
        (blockTargetEquiv K k).symm (d (Fin.last k)))) = _
    rw [PairedTargets.digitList_append, ih, digitList_blockTarget,
      List.ofFn_succ', List.concat_eq_append, List.flatten_concat]
    rfl

theorem levelTargetValue_eq_encode (k : ℕ) (d : ∀ i : Fin k, BlockTarget K i) :
    levelTargetValue K d =
      MixedRadix.encode ((List.ofFn (fun i => blockTargetDigits K i (d i))).flatten) := by
  rw [levelTargetValue, ← PairedTargets.encode_digitList, digitList_levelTarget]

theorem blockTargetDigits_place (i : ℕ) (d : BlockTarget K i) :
    MixedRadix.place (blockTargetDigits K i d) = blockRadix K i := by
  rw [← digitList_blockTarget, PairedTargets.place_digitList, place_blockDataBases]

end Erdos157.Binary
