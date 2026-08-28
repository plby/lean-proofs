import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# A compact quotient with closed equality relation is Hausdorff

Closedness of saturated closed sets is proved by projection from the compact
domain. The quotient map is then proper, so its product sends the closed
equality relation to the closed diagonal of the quotient.
-/

noncomputable section

open Set Function Topology

namespace Wikipedia.SmoothSixDPoincare.CompactClosedQuotient

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y]
  {q : X → Y} (hq : IsQuotientMap q)
  (hrel : IsClosed {p : X × X | q p.1 = q p.2})

include hq hrel

theorem isClosedMap : IsClosedMap q := by
  intro D hD
  apply hq.isClosed_preimage.mp
  have heq : q ⁻¹' (q '' D) =
      Prod.fst '' ({p : X × X | q p.1 = q p.2} ∩ Prod.snd ⁻¹' D) := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨(x, y), ⟨hxy.symm, hy⟩, rfl⟩
    · rintro ⟨⟨z, y⟩, ⟨hzy, hy⟩, rfl⟩
      exact ⟨y, hy, hzy.symm⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace _ (hrel.inter (hD.preimage continuous_snd))

theorem isProperMap : IsProperMap q := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨hq.continuous, isClosedMap hq hrel, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := hq.surjective y
  have heq : q ⁻¹' {q x} = (fun z => (z, x)) ⁻¹' {p : X × X | q p.1 = q p.2} := rfl
  rw [heq]
  exact (hrel.preimage (continuous_id.prodMk continuous_const)).isCompact

theorem t2Space : T2Space Y := by
  apply t2_iff_isClosed_diagonal.mpr
  have hclosed := ((isProperMap hq hrel).prodMap (isProperMap hq hrel)).isClosedMap _ hrel
  have heq : Prod.map q q '' {p : X × X | q p.1 = q p.2} = diagonal Y := by
    ext p
    constructor
    · rintro ⟨⟨x, y⟩, hxy, rfl⟩
      exact hxy
    · intro hp
      obtain ⟨x, hx⟩ := hq.surjective p.1
      obtain ⟨y, hy⟩ := hq.surjective p.2
      exact ⟨(x, y), hx.trans (hp.trans hy.symm), Prod.ext hx hy⟩
  rw [heq] at hclosed
  exact hclosed

end Wikipedia.SmoothSixDPoincare.CompactClosedQuotient
