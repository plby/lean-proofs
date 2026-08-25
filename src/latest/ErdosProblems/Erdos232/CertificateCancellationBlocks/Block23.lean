/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock23_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights23, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt23 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 4489217 (136002196) =
      weightedMaskMass a 4719617 (136002196) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4489217, 4719617, 136002196) (by decide)]
  have h001 : weightedMaskMass a 4489224 (160471052) =
      weightedMaskMass a 4719680 (160471052) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4489224, 4719680, 160471052) (by decide)]
  have h002 : weightedMaskMass a 4489224 (-69839133) =
      weightedMaskMass a 5505056 (-69839133) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4489224, 5505056, -69839133) (by decide)]
  have h003 : weightedMaskMass a 4489225 (-120736053) =
      weightedMaskMass a 4719681 (-120736053) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4489225, 4719681, -120736053) (by decide)]
  have h004 : weightedMaskMass a 4489236 (-239857632) =
      weightedMaskMass a 4719636 (-239857632) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4489236, 4719636, -239857632) (by decide)]
  have h005 : weightedMaskMass a 4489240 (-162785421) =
      weightedMaskMass a 4719684 (-162785421) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4489240, 4719684, -162785421) (by decide)]
  have h006 : weightedMaskMass a 4491272 (113394222) =
      weightedMaskMass a 5507104 (113394222) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4491272, 5507104, 113394222) (by decide)]
  have h007 : weightedMaskMass a 4505600 (86389790) =
      weightedMaskMass a 4736000 (86389790) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4505600, 4736000, 86389790) (by decide)]
  have h008 : weightedMaskMass a 4505601 (-83590859) =
      weightedMaskMass a 4736001 (-83590859) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4505601, 4736001, -83590859) (by decide)]
  have h009 : weightedMaskMass a 4505604 (-119876439) =
      weightedMaskMass a 4736016 (-119876439) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4505604, 4736016, -119876439) (by decide)]
  have h010 : weightedMaskMass a 4505608 (-15827094) =
      weightedMaskMass a 4736064 (-15827094) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4505608, 4736064, -15827094) (by decide)]
  have h011 : weightedMaskMass a 4505609 (-56537170) =
      weightedMaskMass a 4736065 (-56537170) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4505609, 4736065, -56537170) (by decide)]
  have h012 : weightedMaskMass a 4505616 (-387746007) =
      weightedMaskMass a 4736004 (-387746007) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4505616, 4736004, -387746007) (by decide)]
  have h013 : weightedMaskMass a 4505620 (638064904) =
      weightedMaskMass a 4736020 (638064904) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4505620, 4736020, 638064904) (by decide)]
  have h014 : weightedMaskMass a 4505624 (374809555) =
      weightedMaskMass a 4736068 (374809555) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4505624, 4736068, 374809555) (by decide)]
  have h015 : weightedMaskMass a 4723776 (55712557) =
      weightedMaskMass a 5505060 (55712557) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4723776, 5505060, 55712557) (by decide)]
  have h016 : weightedMaskMass a 4751369 (-94952655) =
      weightedMaskMass a 4751425 (-94952655) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4751369, 4751425, -94952655) (by decide)]
  have h017 : weightedMaskMass a 4751384 (-35363714) =
      weightedMaskMass a 4751428 (-35363714) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4751384, 4751428, -35363714) (by decide)]
  have h018 : weightedMaskMass a 4767748 (68926203) =
      weightedMaskMass a 4767760 (68926203) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4767748, 4767760, 68926203) (by decide)]
  have h019 : weightedMaskMass a 4767752 (-43222421) =
      weightedMaskMass a 4767808 (-43222421) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4767752, 4767808, -43222421) (by decide)]
  have h020 : weightedMaskMass a 4767753 (7062562) =
      weightedMaskMass a 4767809 (7062562) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4767753, 4767809, 7062562) (by decide)]
  have h021 : weightedMaskMass a 4767768 (138658897) =
      weightedMaskMass a 4767812 (138658897) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4767768, 4767812, 138658897) (by decide)]
  have h022 : weightedMaskMass a 5505064 (-102603613) =
      weightedMaskMass a 5537800 (-102603613) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5505064, 5537800, -102603613) (by decide)]
  have h023 : weightedMaskMass a 5507112 (169269087) =
      weightedMaskMass a 5539848 (169269087) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5507112, 5539848, 169269087) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt23 s.val : ℝ)) = (((((weightedMaskMass a 4489217 (136002196) + (-weightedMaskMass a 4719617 (136002196) + weightedMaskMass a 4489224 (160471052))) + (-weightedMaskMass a 4719680 (160471052) + (weightedMaskMass a 4489224 (-69839133) + -weightedMaskMass a 5505056 (-69839133)))) + ((weightedMaskMass a 4489225 (-120736053) + (-weightedMaskMass a 4719681 (-120736053) + weightedMaskMass a 4489236 (-239857632))) + (-weightedMaskMass a 4719636 (-239857632) + (weightedMaskMass a 4489240 (-162785421) + -weightedMaskMass a 4719684 (-162785421))))) + (((weightedMaskMass a 4491272 (113394222) + (-weightedMaskMass a 5507104 (113394222) + weightedMaskMass a 4505600 (86389790))) + (-weightedMaskMass a 4736000 (86389790) + (weightedMaskMass a 4505601 (-83590859) + -weightedMaskMass a 4736001 (-83590859)))) + ((weightedMaskMass a 4505604 (-119876439) + (-weightedMaskMass a 4736016 (-119876439) + weightedMaskMass a 4505608 (-15827094))) + (-weightedMaskMass a 4736064 (-15827094) + (weightedMaskMass a 4505609 (-56537170) + -weightedMaskMass a 4736065 (-56537170)))))) + ((((weightedMaskMass a 4505616 (-387746007) + (-weightedMaskMass a 4736004 (-387746007) + weightedMaskMass a 4505620 (638064904))) + (-weightedMaskMass a 4736020 (638064904) + (weightedMaskMass a 4505624 (374809555) + -weightedMaskMass a 4736068 (374809555)))) + ((weightedMaskMass a 4723776 (55712557) + (-weightedMaskMass a 5505060 (55712557) + weightedMaskMass a 4751369 (-94952655))) + (-weightedMaskMass a 4751425 (-94952655) + (weightedMaskMass a 4751384 (-35363714) + -weightedMaskMass a 4751428 (-35363714))))) + (((weightedMaskMass a 4767748 (68926203) + (-weightedMaskMass a 4767760 (68926203) + weightedMaskMass a 4767752 (-43222421))) + (-weightedMaskMass a 4767808 (-43222421) + (weightedMaskMass a 4767753 (7062562) + -weightedMaskMass a 4767809 (7062562)))) + ((weightedMaskMass a 4767768 (138658897) + (-weightedMaskMass a 4767812 (138658897) + weightedMaskMass a 5505064 (-102603613))) + (-weightedMaskMass a 5537800 (-102603613) + (weightedMaskMass a 5507112 (169269087) + -weightedMaskMass a 5539848 (169269087))))))) := by
      simp only [atomCongruenceContributionInt23, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023]
      ring

end Erdos232
