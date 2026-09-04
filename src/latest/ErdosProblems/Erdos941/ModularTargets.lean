import ErdosProblems.Erdos941.ModularTargetLifting

/-! # Unconditional word reachability for the targets at 5, 7, and 13 -/

namespace Erdos941

open PairLocal

theorem exists_five_modular_target (v : ZMod 25 × ZMod 25 × ZMod 25)
    (hv : normThree (mapCoeffs (primeSquareReduce 5) v) = 0) :
    ∃ w : List Axis, (linearWord 17 w v).2.2 = 0 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨w, _, hw⟩ := exists_word_primeSquare_target (p := 5)
    17 2 2 0 0 0 1 (by decide) (alternatingWord 3) five_kernel_word
    (by decide) (by decide)
    (by
      intro z hz
      obtain ⟨w, _, hw⟩ := five_conic_word z hz
      exact ⟨w, by simpa only [map_ofNat, map_zero] using hw⟩)
    (by
      intro z
      obtain ⟨w, _, hw⟩ := five_plane_word z
      exact ⟨w, by simpa [heightLinear, map_ofNat] using hw⟩) v hv
  exact ⟨w, by simpa [heightLinear] using hw⟩

theorem exists_thirteen_modular_target (v : ZMod 169 × ZMod 169 × ZMod 169)
    (hv : normThree (mapCoeffs (primeSquareReduce 13) v) = 0) :
    ∃ w : List Axis, (linearWord 113 w v).2.2 = 0 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  obtain ⟨w, _, hw⟩ := exists_word_primeSquare_target (p := 13)
    113 1 5 0 0 0 1 (by decide) (alternatingWord 7) thirteen_kernel_word
    (by decide) (by decide)
    (by
      intro z hz
      obtain ⟨w, _, hw⟩ := thirteen_conic_word z hz
      exact ⟨w, by simpa only [map_ofNat, map_zero] using hw⟩)
    (by
      intro z
      obtain ⟨w, hw⟩ := thirteen_plane_word z
      exact ⟨w, by simpa [heightLinear, map_ofNat] using hw⟩) v hv
  exact ⟨w, by simpa [heightLinear] using hw⟩

def SevenModularTarget (v : ZMod 49 × ZMod 49 × ZMod 49) : Prop :=
  OnTargetLine (3 : ZMod 7) 5 (mapCoeffs (primeSquareReduce 7) v) ∧
    -v.1 + v.2.1 - v.2.2 = 0

theorem exists_seven_modular_target (v : ZMod 49 × ZMod 49 × ZMod 49)
    (hv : normThree (mapCoeffs (primeSquareReduce 7) v) = 0) :
    ∃ w : List Axis, SevenModularTarget (linearWord 33 w v) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨w, hl, hw⟩ := exists_word_primeSquare_target (p := 7)
    33 3 3 5 (-1) 1 (-1) (by decide) (alternatingWord 4) seven_kernel_word
    (by decide) (by decide)
    (by
      intro z hz
      obtain ⟨w, _, hw⟩ := seven_conic_word z hz
      exact ⟨w, by simpa only [map_ofNat] using hw⟩)
    (by
      intro z
      obtain ⟨w, _, hw⟩ := seven_plane_word z
      exact ⟨w, by simpa [heightLinear, map_ofNat, sub_eq_add_neg] using hw⟩) v hv
  exact ⟨w, by simpa only [map_ofNat] using hl,
    by simpa [heightLinear, sub_eq_add_neg] using hw⟩

end Erdos941
