import ErdosProblems.Erdos192.PackedData
import ErdosProblems.Erdos192.ListAPCheck

namespace Erdos192

def pairPrefix (a b : Fin 4) (n : Nat) (c : Fin 4) : Nat :=
  if n ≤ 85 then fastPrefix a n c else fastPrefix a 85 c + fastPrefix b (n - 85) c

def packedPairPrefix (a b : Fin 4) (n : Nat) : Nat :=
  if n ≤ 85 then packedPrefix a n else packedPrefix a 85 + packedPrefix b (n - 85)

def pairPrefixList (a b : Fin 4) : List Nat :=
  (List.range 171).map (packedPairPrefix a b)

def pairsCheck : Bool :=
  (List.finRange 4).all fun a =>
  (List.finRange 4).all fun b => a == b || allChecks (pairPrefixList a b)

theorem pairsCheck_true : pairsCheck = true := by decide +kernel

theorem pairPrefix_eq (a b : Fin 4) (n : Nat) (hn : n ≤ 170) (c : Fin 4) :
    pairPrefix a b n c = ((applyKeranenG [a, b]).take n).count c := by
  simp only [applyKeranenG, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  unfold pairPrefix
  split_ifs with h
  · rw [prefixData_correct a ⟨n, by omega⟩ c]
    rw [List.take_append_of_le_length (by simpa [keranenG_length] using h)]
    rfl
  · rw [prefixData_correct a ⟨85, by decide⟩ c,
      prefixData_correct b ⟨n - 85, by omega⟩ c]
    simp only [cumParikhCount, List.take_append, keranenG_length, List.count_append]
    rw [List.take_of_length_le (l := keranenG a) (by rw [keranenG_length]),
      List.take_of_length_le (l := keranenG a) (by rw [keranenG_length]; omega)]

theorem count_prefix_square {w : List (Fin 4)} (i l : Nat)
    (h : (w.drop i |>.take l).Perm (w.drop (i + l) |>.take l)) (c : Fin 4) :
    (w.take i).count c + (w.take (i + 2 * l)).count c =
      2 * (w.take (i + l)).count c := by
  have hc := h.count_eq c
  rw [show i + 2 * l = (i + l) + l by omega, List.take_add, List.count_append,
    List.take_add, List.count_append]
  omega

theorem packedPairPrefix_eq (a b : Fin 4) (n : Nat) (hn : n ≤ 170) :
    packedPairPrefix a b n = pairPrefix a b n 0 + 256 * pairPrefix a b n 1 +
      65536 * pairPrefix a b n 2 + 16777216 * pairPrefix a b n 3 := by
  unfold packedPairPrefix pairPrefix
  split_ifs with h
  · exact packedPrefix_correct a ⟨n, by omega⟩
  · rw [packedPrefix_correct a ⟨85, by decide⟩, packedPrefix_correct b ⟨n - 85, by omega⟩]
    ring

theorem keranen_pair_asf (a b : Fin 4) (hab : a ≠ b) :
    FinAbelianSquareFree (applyKeranenG [a, b]) := by
  have h := pairsCheck_true
  simp only [pairsCheck, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, beq_iff_eq] at h
  have h := (h a b).resolve_left hab
  intro i l hl hlen hp
  have hlen' : i + 2 * l ≤ 170 := by simpa [applyKeranenG_length] using hlen
  have hend : i + 2 * l < (pairPrefixList a b).length := by
    simp only [pairPrefixList, List.length_map, List.length_range]; omega
  have hs := allChecks_sound (pairPrefixList a b) h i l hl hend
  simp only [pairPrefixList, List.getElem_map, List.getElem_range] at hs
  rw [packedPairPrefix_eq a b i (by omega),
    packedPairPrefix_eq a b (i + 2 * l) (by omega),
    packedPairPrefix_eq a b (i + l) (by omega)] at hs
  have hc (c : Fin 4) : pairPrefix a b i c + pairPrefix a b (i + 2 * l) c =
      2 * pairPrefix a b (i + l) c := by
    rw [pairPrefix_eq a b i (by omega), pairPrefix_eq a b (i + 2 * l) (by omega),
      pairPrefix_eq a b (i + l) (by omega)]
    exact count_prefix_square i l hp c
  exact hs (by have := hc 0; have := hc 1; have := hc 2; have := hc 3; omega)

end Erdos192
