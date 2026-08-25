import StackExchange.Puzzling139335.N7.FullCornerPairs
import StackExchange.Puzzling139335.N7.PairFinite
import StackExchange.Puzzling139335.N8.Pairs.Local

/-!
# The actual intrinsic pair pattern for seven incidences

The three two-corner pieces have pair multiplicities `2,1`.  All three
equal would give three actual square-symmetry copies.  All three different
would give two unit partners for an actual unsplit intrinsic corner.

`PairConfiguration` records the resulting finite data of the actual
dissection.  Its existence is proved from the incidence and type bounds;
it is not an additional hypothesis of a dissection.
-/

open Set

namespace Puzzling139335.N7

open N8

noncomputable section

/-- The three actual double-corner pieces, ordered by their repeated
intrinsic pair, and the fourth single-corner piece. -/
structure PairConfiguration (d : SquareDissection) where
  double : Fin 3 → Fin 4
  singleton : Fin 4
  double_injective : Function.Injective double
  double_ne_singleton : ∀ n, double n ≠ singleton
  double_count : ∀ n, d.tileCornerCount (double n) = 2
  singleton_count : d.tileCornerCount singleton = 1
  common : Plane
  repeatedEnd : Plane
  otherEnd : Plane
  common_ne_repeatedEnd : common ≠ repeatedEnd
  common_ne_otherEnd : common ≠ otherEnd
  repeatedEnd_ne_otherEnd : repeatedEnd ≠ otherEnd
  types : d.usedCornerTypes = {common, repeatedEnd, otherEnd}
  pair_zero : intrinsicPair d (double 0) = {common, repeatedEnd}
  pair_one : intrinsicPair d (double 1) = {common, repeatedEnd}
  pair_two : intrinsicPair d (double 2) = {common, otherEnd}

/-- The actual seven-incidence dissection supplies the repeated-pair
configuration, with no unproved geometric classification premise. -/
theorem exists_pairConfiguration (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 7)
    (hused : d.usedCornerTypes.card ≤ 3) : Nonempty (PairConfiguration d) := by
  classical
  obtain ⟨σ, h0, h1, h2, h3⟩ := tile_count_pattern d hc hN
  let ι : Fin 3 → Fin 4 := fun n => σ n.castSucc
  have hιinj : Function.Injective ι := by
    intro m n hmn
    apply Fin.ext
    exact congrArg (fun k : Fin 4 => k.val) (σ.injective hmn)
  have hcount (n : Fin 3) : d.tileCornerCount (ι n) = 2 := by
    fin_cases n
    · exact h0
    · exact h1
    · exact h2
  have hne (n : Fin 3) : ι n ≠ σ 3 := by
    intro hn
    have hcast := σ.injective hn
    have hv := congrArg Fin.val hcast
    have hnlt := n.isLt
    change n.val = 3 at hv
    omega
  have hside (n : Fin 3) : ∃ s, IsLocalSide d (ι n) s :=
    exists_local_side_of_count_two d hc (ι n) (hcount n)
  choose s hs using hside
  let p : Fin 3 → Finset Plane := fun n => intrinsicPair d (ι n)
  have hcard (n : Fin 3) : (p n).card = 2 :=
    (intrinsicPair_card d (ι n)).trans (hcount n)
  have hsub (n : Fin 3) : p n ⊆ d.usedCornerTypes :=
    intrinsicPair_subset_usedCornerTypes d (ι n)
  have hnotAll : ¬(p 0 = p 1 ∧ p 0 = p 2) :=
    local_no_three_equal_pairs d hc (hs 0) (hs 1) (hs 2)
      (hιinj.ne (by decide : (0 : Fin 3) ≠ 1))
      (hιinj.ne (by decide : (0 : Fin 3) ≠ 2))
      (hιinj.ne (by decide : (1 : Fin 3) ≠ 2))
  have hnotInj : ¬ Function.Injective p := by
    intro hinj
    obtain ⟨a, b, r, hab, har, hbr, htypes, ⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩⟩ :=
      distinct_pairs_use_all_three d.usedCornerTypes p hused hcard hsub hinj
    exact no_three_unitSidePairs_of_usedTypes d hc hN hab har hbr htypes
      (local_isUnitSidePair_of_pair_eq d (hs i) hab hi)
      (local_isUnitSidePair_of_pair_eq d (hs j) hbr hj)
      (local_isUnitSidePair_of_pair_eq d (hs k) har.symm hk)
  obtain ⟨a, b, r, ρ, hab, har, hbr, htypes, hp0, hp1, hp2⟩ :=
    repeated_pairs_classification d.usedCornerTypes p hused hcard hsub hnotAll hnotInj
  exact ⟨{
    double := fun n => ι (ρ n)
    singleton := σ 3
    double_injective := hιinj.comp ρ.injective
    double_ne_singleton := fun n => hne (ρ n)
    double_count := fun n => hcount (ρ n)
    singleton_count := h3
    common := a
    repeatedEnd := b
    otherEnd := r
    common_ne_repeatedEnd := hab
    common_ne_otherEnd := har
    repeatedEnd_ne_otherEnd := hbr
    types := htypes
    pair_zero := hp0
    pair_one := hp1
    pair_two := hp2 }⟩

namespace PairConfiguration

variable {d : SquareDissection}

/-- The common type of the two different unit pairs is not an unsplit
corner type. -/
theorem common_not_full (C : PairConfiguration d) (hc : d.HasProtectedCenter) :
    C.common ∉ N5.fullCornerTypes d := by
  obtain ⟨s, hs⟩ := exists_local_side_of_count_two d hc (C.double 0) (C.double_count 0)
  obtain ⟨t, ht⟩ := exists_local_side_of_count_two d hc (C.double 2) (C.double_count 2)
  exact not_fullCornerType_of_two_partners d hc
    (local_isUnitSidePair_of_pair_eq d hs C.common_ne_repeatedEnd C.pair_zero)
    (local_isUnitSidePair_of_pair_eq d ht C.common_ne_otherEnd C.pair_two)
    C.repeatedEnd_ne_otherEnd

/-- Every actual piece is one of the three double-corner pieces or the
single-corner piece recorded by this configuration. -/
theorem exhaustive (C : PairConfiguration d) (i : Fin 4) :
    i = C.double 0 ∨ i = C.double 1 ∨ i = C.double 2 ∨ i = C.singleton := by
  have h01 := C.double_injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have h02 := C.double_injective.ne (by decide : (0 : Fin 3) ≠ 2)
  have h12 := C.double_injective.ne (by decide : (1 : Fin 3) ≠ 2)
  have h0s := C.double_ne_singleton 0
  have h1s := C.double_ne_singleton 1
  have h2s := C.double_ne_singleton 2
  have hcomplete : ∀ (a b c e x : Fin 4), a ≠ b → a ≠ c → b ≠ c →
      a ≠ e → b ≠ e → c ≠ e → x = a ∨ x = b ∨ x = c ∨ x = e := by
    decide
  exact hcomplete _ _ _ _ i h01 h02 h12 h0s h1s h2s

end PairConfiguration

end

end Puzzling139335.N7
