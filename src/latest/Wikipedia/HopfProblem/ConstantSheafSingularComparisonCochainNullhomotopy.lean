import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainNullhomotopyBasic
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainPoint

/-!
# Actual primitives under nullhomotopic pullback

The constant-map pullback factors through the original point cochain complex,
where every positive cocycle has a proved primitive.  The genuine singular
homotopy component corrects that primitive for the original map.  These are
equalities of actual cochains with arbitrary abelian coefficients.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable (A : AddCommGrpCat.{0})

/-- Pullback along an actual nullhomotopic map turns every positive closed
cochain into an actual coboundary. -/
theorem nullhomotopic_pullback_closed_succ (f : C(X, Y)) (hf : f.Nullhomotopic)
    (n : ℕ) (c : Cochains Y A (n + 1))
    (hc : (singularCochainComplex Y A).d (n + 1) (n + 2) c = 0) :
    ∃ b : Cochains X A n,
      (singularCochainComplex X A).d n (n + 1) b = (singularPullback A f).f (n + 1) c := by
  obtain ⟨y, ⟨H⟩⟩ := hf
  let p : C(X, Unit) := ContinuousMap.const X ()
  let q : C(Unit, Y) := ContinuousMap.const Unit y
  let cPoint : Cochains Unit A (n + 1) := (singularPullback A q).f (n + 1) c
  have hcPoint : (singularCochainComplex Unit A).d (n + 1) (n + 2) cPoint = 0 :=
    singularPullback_closed A q (n + 1) (n + 2) c hc
  obtain ⟨b, hb⟩ := point_closed_exact A n cPoint hcPoint
  let h := singularCochainHomotopy A H
  have hconst : (singularPullback A p).f (n + 1) cPoint =
      (singularPullback A (ContinuousMap.const X y)).f (n + 1) c := by
    exact (ConcreteCategory.congr_hom
      (congrArg (fun t : singularCochainComplex Y A ⟶ singularCochainComplex X A =>
        t.f (n + 1)) (singularPullback_comp A p q)) c).symm
  have hbPull :
      (singularCochainComplex X A).d n (n + 1) ((singularPullback A p).f n b) =
        (singularPullback A (ContinuousMap.const X y)).f (n + 1) c := by
    have he := ConcreteCategory.congr_hom ((singularPullback A p).comm n (n + 1)) b
    exact he.trans ((congrArg ((singularPullback A p).f (n + 1)) hb).trans hconst)
  refine ⟨h.hom (n + 1) n c + (singularPullback A p).f n b, ?_⟩
  calc
    (singularCochainComplex X A).d n (n + 1)
        (h.hom (n + 1) n c + (singularPullback A p).f n b) =
      (singularCochainComplex X A).d n (n + 1) (h.hom (n + 1) n c) +
        (singularCochainComplex X A).d n (n + 1) ((singularPullback A p).f n b) :=
      map_add _ _ _
    _ = (singularCochainComplex X A).d n (n + 1) (h.hom (n + 1) n c) +
        (singularPullback A (ContinuousMap.const X y)).f (n + 1) c :=
      congrArg (fun a => (singularCochainComplex X A).d n (n + 1)
        (h.hom (n + 1) n c) + a) hbPull
    _ = (singularPullback A f).f (n + 1) c :=
      (homotopy_apply_closed_succ h n c hc).symm

variable (X : Type) [TopologicalSpace X] [ContractibleSpace X]

/-- A genuine contraction supplies primitives of all actual positive cocycles. -/
theorem contractible_closed_exact (n : ℕ) (c : Cochains X A (n + 1))
    (hc : (singularCochainComplex X A).d (n + 1) (n + 2) c = 0) :
    ∃ b : Cochains X A n, (singularCochainComplex X A).d n (n + 1) b = c := by
  obtain ⟨b, hb⟩ := nullhomotopic_pullback_closed_succ A (ContinuousMap.id X)
    (id_nullhomotopic X) n c hc
  refine ⟨b, ?_⟩
  simpa only [singularPullback_id, HomologicalComplex.id_f, ConcreteCategory.id_apply] using hb

/-- Closed degree-zero cochains of a genuinely contractible space are actual constants. -/
theorem contractible_closed_zero (c : Cochains X A 0)
    (hc : (singularCochainComplex X A).d 0 1 c = 0) :
    ∃ a : A, c = constantCochain X A a := by
  obtain ⟨a, ha⟩ := nullhomotopic_pullback_closed_zero A (ContinuousMap.id X)
    (id_nullhomotopic X) c hc
  refine ⟨a, ?_⟩
  simpa only [singularPullback_id, HomologicalComplex.id_f, ConcreteCategory.id_apply] using ha

/-- The native arbitrary-coefficient cochain complex of a contractible space
is exact in every positive degree. -/
theorem contractibleCochain_exactAt (n : ℕ) :
    (singularCochainComplex X A).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2)
    (by simp) (by simp [Nat.add_assoc]), ShortComplex.ab_exact_iff]
  exact contractible_closed_exact A X n

/-- Positive cohomology vanishes in the actual native cochain complex. -/
theorem contractible_cohomology_isZero (n : ℕ) :
    IsZero ((singularCochainComplex X A).homology (n + 1)) :=
  (contractibleCochain_exactAt A X n).isZero_homology

theorem contractible_cohomology_subsingleton (n : ℕ) :
    Subsingleton ((singularCochainComplex X A).homology (n + 1)) :=
  AddCommGrpCat.subsingleton_of_isZero (contractible_cohomology_isZero A X n)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
