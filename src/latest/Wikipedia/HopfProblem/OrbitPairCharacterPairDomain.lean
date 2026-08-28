import Wikipedia.HopfProblem.OrbitPairFiniteCharacterQuotient
import Wikipedia.HopfProblem.OrbitPairCharacterMatching

/-!
# The open domain of fibre transport in a finite character neighborhood

Nonvanishing of the Hermitian pairing is invariant under changing
either representative. Its actual quotient image is therefore an
open neighborhood of the diagonal in the product of orbit spaces.
-/

noncomputable section

open Set Topology
open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.OrbitPair

open SpecialPeriods SpecialPeriods.Threefold

attribute [local instance] unitCircleMulAction

theorem characterPairing_smul_ne_zero_iff (s : Finset SmoothOrbitCharacter)
    (u v : Circle) (x y : Threefold.Space) :
    characterPairing s (u • x) (v • y) ≠ 0 ↔ characterPairing s x y ≠ 0 := by
  rw [characterPairing_equivariant]
  have hv : conj (v : ℂ) ≠ 0 := by
    intro h
    exact v.coe_ne_zero ((starRingEnd ℂ).injective (h.trans (map_zero _).symm))
  constructor
  · intro h hz
    exact h (by rw [hz, mul_zero])
  · intro h
    exact mul_ne_zero (mul_ne_zero u.coe_ne_zero hv) h

variable (s : Finset SmoothOrbitCharacter)

def finitePairDomain : TopologicalSpace.Opens (finiteCharacterDomain s × finiteCharacterDomain s) :=
  ⟨{p | characterPairing s p.1.val p.2.val ≠ 0},
    isOpen_ne.preimage ((characterPairing_continuous s).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)))⟩

def finitePairProjection (p : finiteCharacterDomain s × finiteCharacterDomain s) :
    finiteCharacterOrbitImage s × finiteCharacterOrbitImage s :=
  (finiteCharacterProjection s p.1, finiteCharacterProjection s p.2)

theorem finitePairProjection_isOpenQuotientMap : IsOpenQuotientMap (finitePairProjection s) :=
  (finiteCharacterProjection_isOpenQuotientMap s).prodMap
    (finiteCharacterProjection_isOpenQuotientMap s)

def finiteTransportDomain :
    TopologicalSpace.Opens (finiteCharacterOrbitImage s × finiteCharacterOrbitImage s) :=
  ⟨finitePairProjection s '' (finitePairDomain s : Set _),
    (finitePairProjection_isOpenQuotientMap s).isOpenMap _ (finitePairDomain s).isOpen⟩

theorem finitePairProjection_mem_transport_iff (x y : finiteCharacterDomain s) :
    (finiteCharacterProjection s x, finiteCharacterProjection s y) ∈ finiteTransportDomain s ↔
      characterPairing s x.val y.val ≠ 0 := by
  constructor
  · rintro ⟨⟨z, w⟩, hzw, he⟩
    have hx : finiteCharacterProjection s x = finiteCharacterProjection s z :=
      (congrArg Prod.fst he).symm
    have hy : finiteCharacterProjection s y = finiteCharacterProjection s w :=
      (congrArg Prod.snd he).symm
    obtain ⟨u, rfl⟩ := (finiteCharacterProjection_eq_iff s x z).mp hx
    obtain ⟨v, rfl⟩ := (finiteCharacterProjection_eq_iff s y w).mp hy
    exact (characterPairing_smul_ne_zero_iff s u v z.val w.val).mpr hzw
  · intro h
    exact ⟨(x, y), h, rfl⟩

theorem finiteTransportDomain_diagonal (b : finiteCharacterOrbitImage s) :
    (b, b) ∈ finiteTransportDomain s := by
  obtain ⟨x, rfl⟩ := finiteCharacterProjection_surjective s b
  exact (finitePairProjection_mem_transport_iff s x x).mpr (characterPairing_self_ne_zero s x)

/-- The domain with its first orbit represented by an actual point upstairs. -/
abbrev FiniteTransportInput := {z : finiteCharacterDomain s × finiteCharacterOrbitImage s //
  (finiteCharacterProjection s z.1, z.2) ∈ finiteTransportDomain s}

def finiteTransportInputProjection (p : finitePairDomain s) : FiniteTransportInput s :=
  ⟨(p.val.1, finiteCharacterProjection s p.val.2), ⟨p.val, p.property, rfl⟩⟩

theorem finiteTransportInputProjection_continuous : Continuous (finiteTransportInputProjection s) :=
  (continuous_subtype_val.fst.prodMk
    ((finiteCharacterProjection_continuous s).comp continuous_subtype_val.snd)).subtype_mk _

theorem finiteTransportInputProjection_surjective : Function.Surjective (finiteTransportInputProjection s) := by
  intro z
  obtain ⟨y, hy⟩ := finiteCharacterProjection_surjective s z.val.2
  have hxy : characterPairing s z.val.1.val y.val ≠ 0 := by
    apply (finitePairProjection_mem_transport_iff s z.val.1 y).mp
    rw [hy]
    exact z.property
  exact ⟨⟨(z.val.1, y), hxy⟩, Subtype.ext (Prod.ext rfl hy)⟩

theorem finiteTransportInputProjection_isOpenMap : IsOpenMap (finiteTransportInputProjection s) := by
  have hp : IsOpenMap (Prod.map (id : finiteCharacterDomain s → finiteCharacterDomain s)
      (finiteCharacterProjection s)) :=
    IsOpenMap.id.prodMap (finiteCharacterProjection_isOpenMap s)
  exact (hp.domRestrict (finitePairDomain s).isOpen).subtype_mk _

theorem finiteTransportInputProjection_isOpenQuotientMap :
    IsOpenQuotientMap (finiteTransportInputProjection s) :=
  ⟨finiteTransportInputProjection_surjective s, finiteTransportInputProjection_continuous s,
    finiteTransportInputProjection_isOpenMap s⟩

end Wikipedia.HopfProblem.OrbitPair
