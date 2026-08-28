import Mathlib.Topology.Sheaves.EtaleSpace
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Homotopy.Lifting

/-!
# Continuation of local function germs through their actual étale space

A local predicate defines a presheaf of functions and its étale space.  A
continuous section of the étale projection evaluates to a global function
satisfying the predicate.  When every point has a neighborhood on which all
germ maps are bijective, the actual étale projection is a covering map.  On a
simply-connected, locally path-connected base, covering-space lifting then
constructs a global section from an initial germ.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace Filter Function Set
open scoped Topology

namespace Wikipedia.HopfProblem.AnalyticRootCoverContinuation

variable {X : TopCat.{0}} {Y : Type}

/-- The presheaf of functions satisfying the specified local predicate. -/
abbrev predicatePresheaf (P : TopCat.LocalPredicate (fun _ : X => Y)) :
    TopCat.Presheaf (Type) X := TopCat.subpresheafToTypes P.toPrelocalPredicate

/-- Evaluate a function germ at its own base point.  A fixed codomain avoids
introducing any transport in the resulting global function. -/
def etaleValue (P : TopCat.LocalPredicate (fun _ : X => Y))
    (g : (predicatePresheaf P).EtaleSpace) : Y :=
  TopCat.stalkToFiber P g.base g.germ

/-- A section determines its actual point in the étale space at every point
of its domain. -/
def sectionGerm (P : TopCat.LocalPredicate (fun _ : X => Y)) (U : Opens X)
    (s : (predicatePresheaf P).obj (op U)) (x : U) :
    (predicatePresheaf P).EtaleSpace :=
  ⟨x.1, (predicatePresheaf P).germ U x.1 x.2 s⟩

theorem etaleValue_sectionGerm (P : TopCat.LocalPredicate (fun _ : X => Y))
    (U : Opens X) (s : (predicatePresheaf P).obj (op U)) (x : U) :
    etaleValue P (sectionGerm P U s x) = s.1 x :=
  TopCat.stalkToFiber_germ P U x.1 x.2 s

/-- Continuity in the étale topology means that the lifted germ is locally
the germ of one actual section, not merely equal in value at each point. -/
theorem etaleSection_localGerms (P : TopCat.LocalPredicate (fun _ : X => Y))
    (σ : C(X, (predicatePresheaf P).EtaleSpace))
    (hσ : ∀ x : X, (σ x).base = x) (x : X) :
    ∃ (U : Opens X) (_hx : x ∈ U) (s : (predicatePresheaf P).obj (op U)),
      ∀ (y : X) (hy : y ∈ U), σ y = sectionGerm P U s ⟨y, hy⟩ := by
  obtain ⟨U, hxU, s, hs⟩ :=
    TopCat.Presheaf.EtaleSpace.exists_section_of_tendsto (σ.continuous.continuousAt (x := x))
  have hvalues : ∀ᶠ y in 𝓝 x, ∃ hy : y ∈ U,
      σ y = sectionGerm P U s ⟨y, hy⟩ := by
    filter_upwards [hs] with y hy
    obtain ⟨hyU, hg⟩ := hy
    refine ⟨hσ y ▸ hyU, ?_⟩
    calc
      σ y = sectionGerm P U s ⟨(σ y).base, hyU⟩ := by
        change σ y = ⟨(σ y).base, (predicatePresheaf P).germ U (σ y).base hyU s⟩
        rw [← hg]
      _ = sectionGerm P U s ⟨y, hσ y ▸ hyU⟩ :=
        congrArg (sectionGerm P U s) (Subtype.ext (hσ y))
  obtain ⟨V, hV, hVo, hxV⟩ := eventually_nhds_iff.mp hvalues
  let W : Opens X := ⟨V, hVo⟩
  have hWU : W ≤ U := fun y hy => (hV y hy).choose
  let i : W ⟶ U := homOfLE hWU
  refine ⟨W, hxV, (predicatePresheaf P).map i.op s, ?_⟩
  intro y hy
  have hg := (hV y hy).choose_spec
  convert hg using 1
  dsimp only [sectionGerm]
  rw [(predicatePresheaf P).germ_res_apply]

/-- A continuous section of the étale projection locally evaluates to one of
the original function sections. -/
theorem etaleSection_locally (P : TopCat.LocalPredicate (fun _ : X => Y))
    (σ : C(X, (predicatePresheaf P).EtaleSpace))
    (hσ : ∀ x : X, (σ x).base = x) (x : X) :
    ∃ (U : Opens X) (_hx : x ∈ U) (s : (predicatePresheaf P).obj (op U)),
      ∀ (y : X) (hy : y ∈ U), etaleValue P (σ y) = s.1 ⟨y, hy⟩ := by
  obtain ⟨U, hxU, s, hs⟩ := etaleSection_localGerms P σ hσ x
  refine ⟨U, hxU, s, ?_⟩
  intro y hy
  rw [hs y hy, etaleValue_sectionGerm]

/-- Locality proves that evaluation of an actual continuous étale section is
a global section of the original local predicate. -/
theorem etaleSection_pred (P : TopCat.LocalPredicate (fun _ : X => Y))
    (σ : C(X, (predicatePresheaf P).EtaleSpace))
    (hσ : ∀ x : X, (σ x).base = x) :
    P.pred (U := ⊤) (fun x => etaleValue P (σ x.1)) := by
  apply P.locality
  intro x
  obtain ⟨U, hxU, s, hs⟩ := etaleSection_locally P σ hσ x.1
  refine ⟨U, hxU, homOfLE le_top, ?_⟩
  convert s.2 using 1
  funext y
  exact hs y.1 y.2

/-- The global function obtained by evaluating an actual continuous étale
section, together with the proved local predicate. -/
def sectionOfEtaleSection (P : TopCat.LocalPredicate (fun _ : X => Y))
    (σ : C(X, (predicatePresheaf P).EtaleSpace))
    (hσ : ∀ x : X, (σ x).base = x) :
    (predicatePresheaf P).obj (op ⊤) :=
  ⟨fun x => etaleValue P (σ x.1), etaleSection_pred P σ hσ⟩

/-- The constructed global section has exactly the lifted germ at every
point, including points where distinct analytic germs have the same value. -/
theorem sectionOfEtaleSection_germ (P : TopCat.LocalPredicate (fun _ : X => Y))
    (σ : C(X, (predicatePresheaf P).EtaleSpace))
    (hσ : ∀ x : X, (σ x).base = x) (x : X) :
    sectionGerm P ⊤ (sectionOfEtaleSection P σ hσ) ⟨x, trivial⟩ = σ x := by
  obtain ⟨U, hxU, s, hs⟩ := etaleSection_localGerms P σ hσ x
  let i : U ⟶ (⊤ : Opens X) := homOfLE le_top
  have heq : (predicatePresheaf P).map i.op (sectionOfEtaleSection P σ hσ) = s := by
    apply Subtype.ext
    funext y
    change etaleValue P (σ y.1) = s.1 y
    rw [hs y.1 y.2, etaleValue_sectionGerm]
  have hg : (predicatePresheaf P).germ ⊤ x trivial (sectionOfEtaleSection P σ hσ) =
      (predicatePresheaf P).germ U x hxU s := by
    rw [← (predicatePresheaf P).germ_res_apply i x hxU, heq]
  calc
    sectionGerm P ⊤ (sectionOfEtaleSection P σ hσ) ⟨x, trivial⟩ =
        sectionGerm P U s ⟨x, hxU⟩ := by
      dsimp only [sectionGerm]
      rw [hg]
    _ = σ x := (hs x hxU).symm

/-- Covering-space continuation preserves the specified initial germ. -/
theorem exists_global_section_with_germ_of_germ_bijective
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (P : TopCat.LocalPredicate (fun _ : X => Y))
    (hbij : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      ∀ (y : X) (hy : y ∈ U), Bijective ((predicatePresheaf P).germ U y hy))
    (x₀ : X) (g₀ : (predicatePresheaf P).stalk x₀) :
    ∃ s : (predicatePresheaf P).obj (op ⊤),
      (predicatePresheaf P).germ ⊤ x₀ trivial s = g₀ := by
  have hc : IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := predicatePresheaf P)) :=
    TopCat.Presheaf.EtaleSpace.isCoveringMap_base hbij
  obtain ⟨σ, hσ, -⟩ := hc.existsUnique_continuousMap_lifts
    (ContinuousMap.id X) x₀ ⟨x₀, g₀⟩ rfl
  have hbase (x : X) : (σ x).base = x := congrFun hσ.2 x
  refine ⟨sectionOfEtaleSection P σ hbase, ?_⟩
  have hg := (sectionOfEtaleSection_germ P σ hbase x₀).trans hσ.1
  simpa only [sectionGerm, TopCat.Presheaf.EtaleSpace.mk.injEq, heq_eq_eq, true_and] using hg

/-- Every initial function germ continues to an actual global function when
the local germ-bijectivity condition makes the étale projection a covering. -/
theorem exists_global_section_of_germ_bijective
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (P : TopCat.LocalPredicate (fun _ : X => Y))
    (hbij : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      ∀ (y : X) (hy : y ∈ U), Bijective ((predicatePresheaf P).germ U y hy))
    (x₀ : X) (g₀ : (predicatePresheaf P).stalk x₀) :
    Nonempty ((predicatePresheaf P).obj (op ⊤)) := by
  obtain ⟨s, -⟩ := exists_global_section_with_germ_of_germ_bijective P hbij x₀ g₀
  exact ⟨s⟩

end Wikipedia.HopfProblem.AnalyticRootCoverContinuation
