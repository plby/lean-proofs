import Wikipedia.NoExoticSixSphere.SphereExteriorPairPartition
import Wikipedia.NoExoticSixSphere.TransverseSphereIntersections

/-!
# Transport of actual cap double points

A bijective cap parametrization transports the original ordered pair types.
For a single cap, every old self-pair must survive in the retained source.
For two disjoint caps, the target consists of the original mutual pairs
other than one specified pair. No cardinality or transversality is assumed.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} (K F G : Sphere 3 → M)
  {A B S T : Set (Sphere 3)}

def sameCapPairMap (e : A ≃ S) (hval : ∀ a : A, K a.val = F (e a).val)
    (p : capPairs K A A) : SphereSelfIntersections.pairs F := by
  let x : A := ⟨p.val.val.1, p.property.1⟩
  let y : A := ⟨p.val.val.2, p.property.2⟩
  refine ⟨((e x).val, (e y).val), ?_, ?_⟩
  · intro h
    exact p.val.property.1 (congrArg Subtype.val (e.injective (Subtype.ext h)))
  · exact (hval x).symm.trans (p.val.property.2.trans (hval y))

theorem sameCapPairMap_injective (e : A ≃ S)
    (hval : ∀ a : A, K a.val = F (e a).val) :
    Injective (sameCapPairMap K F e hval) := by
  intro p q h
  have hx := congrArg (fun z : SphereSelfIntersections.pairs F ↦ z.val.1) h
  have hy := congrArg (fun z : SphereSelfIntersections.pairs F ↦ z.val.2) h
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (congrArg Subtype.val (e.injective (Subtype.ext hx)))
    (congrArg Subtype.val (e.injective (Subtype.ext hy)))

theorem sameCapPairMap_surjective (e : A ≃ S)
    (hval : ∀ a : A, K a.val = F (e a).val)
    (hout : ∀ p : SphereSelfIntersections.pairs F, p.val.1 ∈ S ∧ p.val.2 ∈ S) :
    Surjective (sameCapPairMap K F e hval) := by
  intro p
  let x := e.symm ⟨p.val.1, (hout p).1⟩
  let y := e.symm ⟨p.val.2, (hout p).2⟩
  have hx : (e x).val = p.val.1 := congrArg Subtype.val (e.apply_symm_apply _)
  have hy : (e y).val = p.val.2 := congrArg Subtype.val (e.apply_symm_apply _)
  have hne : x.val ≠ y.val := by
    intro h
    exact p.property.1 (hx.symm.trans
      ((congrArg (fun a : A ↦ (e a).val) (Subtype.ext h)).trans hy))
  have heq : K x.val = K y.val := by
    calc
      K x.val = F (e x).val := hval x
      _ = F p.val.1 := congrArg F hx
      _ = F p.val.2 := p.property.2
      _ = F (e y).val := congrArg F hy.symm
      _ = K y.val := (hval y).symm
  refine ⟨⟨⟨(x.val, y.val), hne, heq⟩, x.property, y.property⟩, ?_⟩
  exact Subtype.ext (Prod.ext hx hy)

def sameCapPairEquiv (e : A ≃ S) (hval : ∀ a : A, K a.val = F (e a).val)
    (hout : ∀ p : SphereSelfIntersections.pairs F, p.val.1 ∈ S ∧ p.val.2 ∈ S) :
    capPairs K A A ≃ SphereSelfIntersections.pairs F :=
  Equiv.ofBijective (sameCapPairMap K F e hval)
    ⟨sameCapPairMap_injective K F e hval, sameCapPairMap_surjective K F e hval hout⟩

def mutualPairsExcept (c : Sphere 3 × Sphere 3) : Type :=
  {p : MapIntersections.pairs F G // p.val ≠ c}

def mixedCapPairMap (e : A ≃ S) (d : B ≃ T)
    (hleft : ∀ a : A, K a.val = F (e a).val)
    (hright : ∀ b : B, K b.val = G (d b).val)
    (c : Sphere 3 × Sphere 3) (hc : c.1 ∉ S)
    (p : capPairs K A B) : mutualPairsExcept F G c := by
  let x : A := ⟨p.val.val.1, p.property.1⟩
  let y : B := ⟨p.val.val.2, p.property.2⟩
  refine ⟨⟨((e x).val, (d y).val), ?_⟩, ?_⟩
  · exact (hleft x).symm.trans (p.val.property.2.trans (hright y))
  · intro h
    exact hc ((congrArg Prod.fst h) ▸ (e x).property)

theorem mixedCapPairMap_injective (e : A ≃ S) (d : B ≃ T)
    (hleft : ∀ a : A, K a.val = F (e a).val)
    (hright : ∀ b : B, K b.val = G (d b).val)
    (c : Sphere 3 × Sphere 3) (hc : c.1 ∉ S) :
    Injective (mixedCapPairMap K F G e d hleft hright c hc) := by
  intro p q h
  have hx := congrArg (fun z : mutualPairsExcept F G c ↦ z.val.val.1) h
  have hy := congrArg (fun z : mutualPairsExcept F G c ↦ z.val.val.2) h
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (congrArg Subtype.val (e.injective (Subtype.ext hx)))
    (congrArg Subtype.val (d.injective (Subtype.ext hy)))

theorem mixedCapPairMap_surjective (e : A ≃ S) (d : B ≃ T)
    (hleft : ∀ a : A, K a.val = F (e a).val)
    (hright : ∀ b : B, K b.val = G (d b).val)
    (c : Sphere 3 × Sphere 3) (hc : c.1 ∉ S) (hAB : Disjoint A B)
    (hout : ∀ p : mutualPairsExcept F G c, p.val.val.1 ∈ S ∧ p.val.val.2 ∈ T) :
    Surjective (mixedCapPairMap K F G e d hleft hright c hc) := by
  intro p
  let x := e.symm ⟨p.val.val.1, (hout p).1⟩
  let y := d.symm ⟨p.val.val.2, (hout p).2⟩
  have hx : (e x).val = p.val.val.1 := congrArg Subtype.val (e.apply_symm_apply _)
  have hy : (d y).val = p.val.val.2 := congrArg Subtype.val (d.apply_symm_apply _)
  have hne : x.val ≠ y.val := by
    intro h
    exact disjoint_left.mp hAB x.property (h.symm ▸ y.property)
  have heq : K x.val = K y.val := by
    calc
      K x.val = F (e x).val := hleft x
      _ = F p.val.val.1 := congrArg F hx
      _ = G p.val.val.2 := p.val.property
      _ = G (d y).val := congrArg G hy.symm
      _ = K y.val := (hright y).symm
  refine ⟨⟨⟨(x.val, y.val), hne, heq⟩, x.property, y.property⟩, ?_⟩
  exact Subtype.ext (Subtype.ext (Prod.ext hx hy))

def mixedCapPairEquiv (e : A ≃ S) (d : B ≃ T)
    (hleft : ∀ a : A, K a.val = F (e a).val)
    (hright : ∀ b : B, K b.val = G (d b).val)
    (c : Sphere 3 × Sphere 3) (hc : c.1 ∉ S) (hAB : Disjoint A B)
    (hout : ∀ p : mutualPairsExcept F G c, p.val.val.1 ∈ S ∧ p.val.val.2 ∈ T) :
    capPairs K A B ≃ mutualPairsExcept F G c :=
  Equiv.ofBijective (mixedCapPairMap K F G e d hleft hright c hc)
    ⟨mixedCapPairMap_injective K F G e d hleft hright c hc,
      mixedCapPairMap_surjective K F G e d hleft hright c hc hAB hout⟩

end NoExoticSixSphere.SphereSumNeck
