import StackExchange.Puzzling139335.N7.TypeReduction

/-!
# Exchanging the two repeated-pair copies

The underlying dissection and intrinsic points are unchanged.  Only the
order of the first two double-corner pieces in the configuration changes.
-/

namespace Puzzling139335.N7.PairConfiguration

noncomputable section

variable {d : SquareDissection}

/-- Exchange the two double-corner pieces using the repeated intrinsic pair. -/
def swapRepeated (C : PairConfiguration d) : PairConfiguration d where
  double n := C.double ((Equiv.swap (0 : Fin 3) 1) n)
  singleton := C.singleton
  double_injective := C.double_injective.comp (Equiv.swap 0 1).injective
  double_ne_singleton n := C.double_ne_singleton ((Equiv.swap 0 1) n)
  double_count n := C.double_count ((Equiv.swap 0 1) n)
  singleton_count := C.singleton_count
  common := C.common
  repeatedEnd := C.repeatedEnd
  otherEnd := C.otherEnd
  common_ne_repeatedEnd := C.common_ne_repeatedEnd
  common_ne_otherEnd := C.common_ne_otherEnd
  repeatedEnd_ne_otherEnd := C.repeatedEnd_ne_otherEnd
  types := C.types
  pair_zero := by simpa using C.pair_one
  pair_one := by simpa using C.pair_zero
  pair_two := by
    simpa only [Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 0)
      (by decide : (2 : Fin 3) ≠ 1)] using C.pair_two

@[simp] theorem swapRepeated_double_zero (C : PairConfiguration d) :
    C.swapRepeated.double 0 = C.double 1 := by simp [swapRepeated]

@[simp] theorem swapRepeated_double_one (C : PairConfiguration d) :
    C.swapRepeated.double 1 = C.double 0 := by simp [swapRepeated]

@[simp] theorem swapRepeated_double_two (C : PairConfiguration d) :
    C.swapRepeated.double 2 = C.double 2 := by
  change C.double ((Equiv.swap 0 1) 2) = C.double 2
  rw [Equiv.swap_apply_of_ne_of_ne (by decide : (2 : Fin 3) ≠ 0)
    (by decide : (2 : Fin 3) ≠ 1)]

@[simp] theorem swapRepeated_singleton (C : PairConfiguration d) :
    C.swapRepeated.singleton = C.singleton := rfl

@[simp] theorem swapRepeated_common (C : PairConfiguration d) :
    C.swapRepeated.common = C.common := rfl

@[simp] theorem swapRepeated_repeatedEnd (C : PairConfiguration d) :
    C.swapRepeated.repeatedEnd = C.repeatedEnd := rfl

@[simp] theorem swapRepeated_otherEnd (C : PairConfiguration d) :
    C.swapRepeated.otherEnd = C.otherEnd := rfl

end

end Puzzling139335.N7.PairConfiguration
