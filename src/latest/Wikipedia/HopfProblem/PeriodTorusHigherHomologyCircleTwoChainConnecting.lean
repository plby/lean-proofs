import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleConnectingCycles

/-!
# The actual connecting class of two chains with opposite boundaries

Two actual singular chains in the cover members whose boundaries are the
opposite images of an intersection cycle give an actual small-chain cycle.
The ambient representative is their sum. The connecting homomorphism of
the proved Mayer--Vietoris sequence sends its class to the intersection
cycle class, with no additional sign or homology-identification hypothesis.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris ModuleHomology

private def biprodElement (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    (a : K.X n) (b : L.X n) : (K ⊞ L).X n :=
  ((biprod.inl : K ⟶ K ⊞ L).f n).hom a + ((biprod.inr : L ⟶ K ⊞ L).f n).hom b

private theorem biprod_lift_f_apply
    {J K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : J ⟶ K) (g : J ⟶ L)
    (n : ℕ) (z : J.X n) :
    ((biprod.lift f g).f n).hom z =
      ((biprod.inl : K ⟶ K ⊞ L).f n).hom ((f.f n).hom z) +
        ((biprod.inr : L ⟶ K ⊞ L).f n).hom ((g.f n).hom z) := by
  have htotal := congrArg (fun h => h.hom (((biprod.lift f g).f n).hom z))
    (HomologicalComplex.biprod_total_f K L n)
  have hfst := congrArg (fun h => h.hom z)
    (HomologicalComplex.biprod_lift_fst_f f g n)
  have hsnd := congrArg (fun h => h.hom z)
    (HomologicalComplex.biprod_lift_snd_f f g n)
  change ((biprod.fst : K ⊞ L ⟶ K).f n).hom (((biprod.lift f g).f n).hom z) =
    (f.f n).hom z at hfst
  change ((biprod.snd : K ⊞ L ⟶ L).f n).hom (((biprod.lift f g).f n).hom z) =
    (g.f n).hom z at hsnd
  change ((biprod.inl : K ⟶ K ⊞ L).f n).hom
      (((biprod.fst : K ⊞ L ⟶ K).f n).hom (((biprod.lift f g).f n).hom z)) +
    ((biprod.inr : L ⟶ K ⊞ L).f n).hom
      (((biprod.snd : K ⊞ L ⟶ L).f n).hom (((biprod.lift f g).f n).hom z)) =
    ((biprod.lift f g).f n).hom z at htotal
  rw [hfst, hsnd] at htotal
  exact htotal.symm

private theorem biprodElement_desc
    {K L T : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : K ⟶ T) (g : L ⟶ T)
    (n : ℕ) (a : K.X n) (b : L.X n) :
    ((biprod.desc f g).f n).hom (biprodElement K L n a b) =
      (f.f n).hom a + (g.f n).hom b := by
  change ((biprod.desc f g).f n).hom
    (((biprod.inl : K ⟶ K ⊞ L).f n).hom a +
      ((biprod.inr : L ⟶ K ⊞ L).f n).hom b) = _
  rw [map_add]
  congr 1
  · exact congrArg (fun h => h.hom a) (HomologicalComplex.biprod_inl_desc_f f g n)
  · exact congrArg (fun h => h.hom b) (HomologicalComplex.biprod_inr_desc_f f g n)

private theorem biprodElement_boundary (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (i j : ℕ) (a : K.X i) (b : L.X i) :
    ((K ⊞ L).d i j).hom (biprodElement K L i a b) =
      biprodElement K L j ((K.d i j).hom a) ((L.d i j).hom b) := by
  have hK := congrArg (fun f => f.hom a) ((biprod.inl : K ⟶ K ⊞ L).comm i j)
  have hL := congrArg (fun f => f.hom b) ((biprod.inr : L ⟶ K ⊞ L).comm i j)
  change ((K ⊞ L).d i j).hom (((biprod.inl : K ⟶ K ⊞ L).f i).hom a) =
    ((biprod.inl : K ⟶ K ⊞ L).f j).hom ((K.d i j).hom a) at hK
  change ((K ⊞ L).d i j).hom (((biprod.inr : L ⟶ K ⊞ L).f i).hom b) =
    ((biprod.inr : L ⟶ K ⊞ L).f j).hom ((L.d i j).hom b) at hL
  change ((K ⊞ L).d i j).hom
    (((biprod.inl : K ⟶ K ⊞ L).f i).hom a +
      ((biprod.inr : L ⟶ K ⊞ L).f i).hom b) = _
  rw [map_add, hK, hL]
  rfl

private theorem biprod_lift_eq_boundary
    {J K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : J ⟶ K) (g : J ⟶ L)
    (i j : ℕ) (a : K.X i) (b : L.X i) (z : J.X j)
    (ha : (K.d i j).hom a = (f.f j).hom z)
    (hb : (L.d i j).hom b = (g.f j).hom z) :
    ((biprod.lift f g).f j).hom z =
      ((K ⊞ L).d i j).hom (biprodElement K L i a b) := by
  have hlift := biprod_lift_f_apply f g j z
  have hboundary := biprodElement_boundary K L i j a b
  have hab := congrArg₂ (biprodElement K L j) ha hb
  exact hlift.trans (hab.symm.trans hboundary.symm)

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- The actual middle chain formed by the two categorical biproduct injections. -/
def twoChainMiddle (n : ℕ) (a : Chains U (n + 1)) (b : Chains V (n + 1)) :
    (middleComplex U V).X (n + 1) :=
  biprodElement (singularComplex U) (singularComplex V) (n + 1) a b

/-- The actual sum map carries the middle chain to the sum of its two small images. -/
theorem twoChainMiddle_rightMap (n : ℕ) (a : Chains U (n + 1)) (b : Chains V (n + 1)) :
    ((rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b) =
      ((toSmallLeft U V).f (n + 1)).hom a + ((toSmallRight U V).f (n + 1)).hom b :=
  biprodElement_desc (toSmallLeft U V) (toSmallRight U V) (n + 1) a b

variable (n : ℕ) (a : Chains U (n + 1)) (b : Chains V (n + 1))
  (z : Cycle (singularComplex (U ∩ V : Set X)) n)
  (ha : ((singularComplex U).d (n + 1) n).hom a =
    inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n z.1)
  (hb : ((singularComplex V).d (n + 1) n).hom b =
    -inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)) n z.1)

include ha hb in
/-- The opposite chain boundaries are exactly the actual signed intersection map. -/
theorem twoChainMiddle_boundary :
    ((leftMap U V).f n).hom z.1 =
      ((middleComplex U V).d (n + 1) n).hom (twoChainMiddle U V n a b) :=
  biprod_lift_eq_boundary (intersectionToLeft U V) (-(intersectionToRight U V))
    (n + 1) n a b z.1 ha hb

include z ha hb in
/-- The actual right image of the two-chain middle element is a cycle. -/
theorem twoChainSmallCycle_condition :
    ((smallComplex U V).d (n + 1) n).hom
      (((rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b)) = 0 := by
  have hcomm := congrArg (fun f => f.hom (twoChainMiddle U V n a b))
    ((rightMap U V).comm (n + 1) n)
  have hzero := congrArg (fun f => (f.f n).hom z.1) (leftMap_rightMap U V)
  calc
    _ = ((rightMap U V).f n).hom
        (((middleComplex U V).d (n + 1) n).hom (twoChainMiddle U V n a b)) := hcomm
    _ = ((rightMap U V).f n).hom (((leftMap U V).f n).hom z.1) :=
      congrArg ((rightMap U V).f n).hom (twoChainMiddle_boundary U V n a b z ha hb).symm
    _ = 0 := hzero

/-- The genuine small singular cycle obtained by gluing the two chains. -/
def twoChainSmallCycle : Cycle (smallComplex U V) (n + 1) :=
  mkCycle (smallComplex U V) (n + 1)
    (((rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b)) (by
      rw [Nat.add_sub_cancel]
      exact twoChainSmallCycle_condition U V n a b z ha hb)

@[simp] theorem twoChainSmallCycle_val :
    (twoChainSmallCycle U V n a b z ha hb).1 =
      ((rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b) := rfl

/-- Inclusion into the ambient singular complex gives the literal sum
of the two actual subtype-inclusion chain images. -/
theorem twoChainSmallCycle_ambient_val :
    (mapCycles (smallInclusion U V) (n + 1) (twoChainSmallCycle U V n a b z ha hb)).1 =
      inducedChain (subtypeInclusion U) (n + 1) a +
        inducedChain (subtypeInclusion V) (n + 1) b := by
  rw [mapCycles_val, twoChainSmallCycle_val, twoChainMiddle_rightMap, map_add]
  have hU := congrArg (fun f => (f.f (n + 1)).hom a) (toSmallLeft_inclusion U V)
  have hV := congrArg (fun f => (f.f (n + 1)).hom b) (toSmallRight_inclusion U V)
  exact congrArg₂ (· + ·) hU hV

/-- The actual small-chain connecting map returns the common intersection cycle class. -/
theorem smallConnectingMap_twoChain :
    smallConnectingMap U V n
        (cycleClass (smallComplex U V) (n + 1) (twoChainSmallCycle U V n a b z ha hb)) =
      cycleClass (singularComplex (U ∩ V : Set X)) n z :=
  smallConnectingMap_cycleClass U V n (twoChainSmallCycle U V n a b z ha hb)
    (twoChainMiddle U V n a b) rfl z (twoChainMiddle_boundary U V n a b z ha hb)

/-- For an open cover, the actual full Mayer--Vietoris connecting map of
the glued ambient cycle is the class of the specified intersection cycle. -/
theorem connectingHomomorphism_twoChain
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) (a : Chains U (n + 1)) (b : Chains V (n + 1))
    (z : Cycle (singularComplex (U ∩ V : Set X)) n)
    (ha : ((singularComplex U).d (n + 1) n).hom a =
      inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n z.1)
    (hb : ((singularComplex V).d (n + 1) n).hom b =
      -inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)) n z.1) :
    connectingHomomorphism U V hU hV hcover n
        (cycleClass (singularComplex X) (n + 1)
          (mapCycles (smallInclusion U V) (n + 1) (twoChainSmallCycle U V n a b z ha hb))) =
      cycleClass (singularComplex (U ∩ V : Set X)) n z :=
  connectingHomomorphism_cycleClass U V hU hV hcover n
    (twoChainSmallCycle U V n a b z ha hb) (twoChainMiddle U V n a b) rfl z
    (twoChainMiddle_boundary U V n a b z ha hb)

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
