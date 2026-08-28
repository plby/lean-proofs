import Wikipedia.HopfProblem.OrbitPairSphereCanonicalSubsegment

/-!
# Canonical subsegments on arbitrary real time intervals
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.OrbitPair.SphereCanonicalGeodesic

open NoExoticSixSphere SpherePairedGeodesic

theorem rescaled_subsegment_spec {n : ℕ} (a b : Sphere n) (hab : (a, b) ∈ nonantipodal n)
    {l u c d : ℝ} (hlu : l < u) (hcd : c < d) (hc : l ≤ c) (hd : d ≤ u) :
    (rescaledSegment a b l u c, rescaledSegment a b l u d) ∈ nonantipodal n ∧
      ∀ r : ℝ, rescaledSegment (rescaledSegment a b l u c) (rescaledSegment a b l u d) c d r =
        rescaledSegment a b l u r := by
  have hden : 0 < u - l := sub_pos.mpr hlu
  have hs : (c - l) / (u - l) ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr hc) hden.le, ?_⟩
    apply (div_le_iff₀ hden).mpr
    simpa only [one_mul] using sub_le_sub_right (hcd.le.trans hd) l
  have ht : (d - l) / (u - l) ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (sub_nonneg.mpr (hc.trans hcd.le)) hden.le, ?_⟩
    apply (div_le_iff₀ hden).mpr
    simpa only [one_mul] using sub_le_sub_right hd l
  have hst : (c - l) / (u - l) < (d - l) / (u - l) :=
    div_lt_div_of_pos_right (sub_lt_sub_right hcd l) hden
  obtain ⟨hmem, heq⟩ := subsegment_spec a b hab hs ht hst
  refine ⟨hmem, ?_⟩
  intro r
  change segment (segment a b ((c - l) / (u - l))) (segment a b ((d - l) / (u - l)))
    ((r - c) / (d - c)) = segment a b ((r - l) / (u - l))
  rw [heq]
  congr 1
  field_simp [ne_of_gt hden, ne_of_gt (sub_pos.mpr hcd)]
  ring

end Wikipedia.HopfProblem.OrbitPair.SphereCanonicalGeodesic
