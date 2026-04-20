/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

universe u
namespace AlgebraicGeometry

open Order CategoryTheory

/--
Class saying scheme satisfies some property of the local ring at every point where the local ring is
of dimension at most `k`. This is useful to provide a common interface for properties such as
Serre's `Rₖ` and `Sₖ` detailed in stacks 033Q.
-/
@[mk_iff]
class Scheme.SatisfiesInCodimensionLE
    (k : ℕ) (X : Scheme.{u}) (P : ObjectProperty CommRingCat) where
  stalk_p : ∀ (x : X), ringKrullDim (X.presheaf.stalk x) ≤ k → P (X.presheaf.stalk x)

/--
More commonly known in the literature as a scheme satisfying `Rₖ` or being regular in codimension
`k`, this says that every local ring of dimension less than or equal to `k` is regular.
-/
@[stacks 033Q]
abbrev Scheme.IsRegularInCodimensionLE (k : ℕ) (X : Scheme.{u}) :=
  X.SatisfiesInCodimensionLE k (fun R ↦ IsRegularLocalRing R)

instance {R : Type*} [CommRing R] [r : IsRegularLocalRing R] : IsDomain R := by
  /-
  This is in PR 28683 by Nailin Guan
  -/
  sorry

/-- A finitely generated submodule whose `spanFinrank` is at most `1` is principal. -/
lemma Submodule.isPrincipal_of_fg_of_spanFinrank_le_one
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {p : Submodule R M} (hFG : p.FG) (h : p.spanFinrank ≤ 1) : p.IsPrincipal := by
  obtain ⟨s, hs, rfl⟩ := hFG.exists_span_set_encard_eq_spanFinrank
  have hle : s.encard ≤ 1 := by
    rw [hs]
    exact_mod_cast h
  obtain rfl | ⟨x, rfl⟩ := Set.encard_le_one_iff_eq.mp hle
  · exact ⟨0, by simp⟩
  · exact ⟨x, rfl⟩

/-- The maximal ideal of a regular local ring of Krull dimension at most one is principal. -/
lemma IsLocalRing.maximalIdeal_isPrincipal_of_isRegularLocalRing_of_ringKrullDim_le_one
    {R : Type*} [CommRing R] [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) :
    (IsLocalRing.maximalIdeal R).IsPrincipal :=
  Submodule.isPrincipal_of_fg_of_spanFinrank_le_one Submodule.FG.of_finite <| by
    exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).le.trans h

/-- A regular local ring of Krull dimension `1` is a principal ideal ring. -/
theorem RegularLocalRing.isPrincipalIdealRing_of_ringKrullDim_le_one
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (h : ringKrullDim R ≤ 1) : IsPrincipalIdealRing R :=
  ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 4 0).mp
    (IsLocalRing.maximalIdeal_isPrincipal_of_isRegularLocalRing_of_ringKrullDim_le_one h)

instance {R : Type*} [CommRing R]
    [IsRegularLocalRing R] [Ring.KrullDimLE 1 R] : IsPrincipalIdealRing R :=
  ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 4 0).mp
    (IsLocalRing.maximalIdeal_isPrincipal_of_isRegularLocalRing_of_ringKrullDim_le_one
      (Ring.krullDimLE_iff.mp ‹_›))

lemma isRegularLocalRing_iff_isDiscreteValuationRing_of_ringKrullDim_eq_one {R : Type*} [CommRing R]
    (h : ringKrullDim R = 1) :
    IsRegularLocalRing R ↔ ∃ _ : IsDomain R, IsDiscreteValuationRing R := by
  refine ⟨fun _ ↦ ⟨inferInstance, ?_⟩, fun ⟨_, _⟩ ↦ inferInstance⟩
  have hNF : ¬ IsField R := fun hF ↦ by
    rw [ringKrullDim_eq_zero_of_isField hF] at h; exact zero_ne_one h
  exact ((IsDiscreteValuationRing.TFAE R hNF).out 4 0).mp
    (IsLocalRing.maximalIdeal_isPrincipal_of_isRegularLocalRing_of_ringKrullDim_le_one h.le)

/--
A scheme is called *normal* if every local ring is an integrally closed domain.
-/
class IsNormal (X : Scheme.{u}) where
  domain : ∀ x : X, IsDomain (X.presheaf.stalk x)
  integrallyClosed : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

/--
A normal, locally Noetherian scheme is regular in codimension one.
-/
instance (X : Scheme.{u}) [IsLocallyNoetherian X] [l : IsNormal X] :
    X.IsRegularInCodimensionLE 1 := by
  constructor

  intro x hx

  --use l.domain x

  dsimp
  obtain a | a : ringKrullDim (X.presheaf.stalk x) = 0 ∨ ringKrullDim (X.presheaf.stalk x) = 1 :=
    sorry
  · have := l.domain x

    /-
    This follows because by assumption our ring is a domain of krull dim 0, so in particular it's a
    field. We should just write a lemma saying that a field is a regular local ring, which will
    not be very hard.
    -/
    sorry

  have m : IsDedekindDomain (X.presheaf.stalk x) := by
    rw [isDedekindDomain_iff (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact l.domain x
    · infer_instance
    · have := a.le

      /-
      Completely trivial, should be assumption. I guess we have to replace DimesionLEOne with
      KrullDimLE 1, which sounds annoying.
      -/
      sorry
    · have := l.integrallyClosed x
      exact fun _ ↦ IsIntegralClosure.isIntegral_iff.mp

  have : ¬ IsField (X.presheaf.stalk x) := by
    intro h
    let o : ringKrullDim ↑(X.presheaf.stalk x) = 0 := ringKrullDim_eq_zero_of_isField h
    rw [a] at o
    simp_all
  have := IsDiscreteValuationRing.TFAE (X.presheaf.stalk x) this
  have := (this.out 0 2).mpr m
  exact IsRegularLocalRing.instOfIsLocalRingOfIsDomainOfIsPrincipalIdealRing ↑(X.presheaf.stalk x)

end AlgebraicGeometry
