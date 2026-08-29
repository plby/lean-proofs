/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CarrierHammockClosure

/-!
# Faithful changes of carrier-hammock representation

An injective route encoding, with carriers read through that encoding,
transports actual admissibility, cardinality, and maximal-up-to choices.
The pullback restricts to genuinely good routes; it does not add arbitrary
preimages or assume that every trace is a valid path.
-/

noncomputable section

namespace Erdos599.Blueprint.CarrierHammock

open Set Cardinal Order

universe u

variable {Route Encoded V : Type u}
variable {f : Route → Encoded} {good : Set Route}
variable {carrier : Encoded → Set V} {ends : Set V}

def encodedPullback (f : Route → Encoded) (good : Set Route)
    (H : Set Encoded) : Set Route := good ∩ f ⁻¹' H

theorem image_encodedPullback {H : Set Encoded} (hH : H ⊆ f '' good) :
    f '' encodedPullback f good H = H := by
  apply Set.Subset.antisymm
  · rintro q ⟨r, hr, rfl⟩
    exact hr.2
  · intro q hq
    obtain ⟨r, hr, rfl⟩ := hH hq
    exact ⟨r, ⟨hr, hq⟩, rfl⟩

theorem mk_encodedPullback (hf : Function.Injective f)
    {H : Set Encoded} (hH : H ⊆ f '' good) :
    #(encodedPullback f good H) = #H :=
  (Cardinal.mk_image_eq_of_injOn f _ hf.injOn).symm.trans
    (congrArg Cardinal.mk (congrArg Set.Elem (image_encodedPullback hH)))

theorem admissible_encodedPullback (hf : Function.Injective f)
    {H : Set Encoded} (hH : Admissible (f '' good) carrier ends H) :
    Admissible good (fun r ↦ carrier (f r)) ends (encodedPullback f good H) := by
  refine ⟨Set.inter_subset_left, ?_⟩
  intro r hr t ht hrt
  exact hH.2 hr.2 ht.2 (fun h ↦ hrt (hf h))

theorem admissible_image {K : Set Route}
    (hK : Admissible good (fun r ↦ carrier (f r)) ends K) :
    Admissible (f '' good) carrier ends (f '' K) := by
  constructor
  · exact Set.image_mono hK.1
  · rintro q ⟨r, hr, rfl⟩ p ⟨t, ht, rfl⟩ hqp
    exact hK.2 hr ht (fun h ↦ hqp (congrArg f h))

/-- Inclusion maximality and both cardinal branches survive a faithful
encoding with exactly the image good-route predicate. -/
theorem maximalUpTo_encodedPullback (hf : Function.Injective f)
    {rho : Cardinal.{u}} {H : Set Encoded}
    (hH : MaximalUpTo {J | Admissible (f '' good) carrier ends J} rho H) :
    MaximalUpTo {J | Admissible good (fun r ↦ carrier (f r)) ends J} rho
      (encodedPullback f good H) := by
  have hgood := admissible_encodedPullback hf hH.mem
  have hcard := mk_encodedPullback hf hH.mem.1
  rcases hH with hsmall | hlarge
  · apply maximalUpTo_of_maximal hgood _ (hcard.le.trans hsmall.2.2)
    refine ⟨hgood, ?_⟩
    intro K hK hpullK r hr
    refine ⟨hK.1 hr, ?_⟩
    apply hsmall.2.1.2 (admissible_image hK)
    · rw [← image_encodedPullback hsmall.1.1]
      exact Set.image_mono hpullK
    · exact ⟨r, hr, rfl⟩
  · obtain ⟨K, hK, hKcard⟩ := hlarge.2.2
    exact maximalUpTo_of_large hgood (hcard.trans hlarge.2.1)
      (admissible_encodedPullback hf hK)
      ((mk_encodedPullback hf hK.1).trans hKcard)

#print axioms mk_encodedPullback
#print axioms maximalUpTo_encodedPullback

end Erdos599.Blueprint.CarrierHammock
