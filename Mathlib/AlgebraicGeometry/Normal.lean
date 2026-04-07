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

universe u
namespace AlgebraicGeometry

open Order

class IsIntegralInCodimensionOne (X : Scheme.{u}) where
  domain : ∀ x : X, coheight x = 1 → IsDomain (X.presheaf.stalk x)

lemma IsIntegralInCodimensionOne.stalk_domain {X : Scheme.{u}} [h : IsIntegralInCodimensionOne X]
    (x : X) (hx : coheight x = 1) :
  IsDomain (X.presheaf.stalk x) := h.domain x hx

instance {X : Scheme.{u}} [IsIntegral X] : IsIntegralInCodimensionOne X := ⟨inferInstance⟩

/--
We define a scheme to be regular in codimension one if all its stalks at codimension one are DVRs.
This is equivalent to being regular since a ring is a DVR iff it is a regular local ring of
dimension one.
-/
class IsRegularInCodimensionOne (X : Scheme.{u}) extends IsIntegralInCodimensionOne X where
  dvr : ∀ (x : X) (hx : coheight x = 1),
      have := IsIntegralInCodimensionOne.stalk_domain x hx
      IsDiscreteValuationRing (X.presheaf.stalk x)

/--
Given a codimension one point `x` of a scheme which is regular in codimension one, the stalk at `x`
is a discrete valuation ring.
-/
lemma IsRegularInCodimensionOne.stalk_dvr {X : Scheme.{u}} [h : IsRegularInCodimensionOne X]
    (x : X) (hx : coheight x = 1) :
  have := IsIntegralInCodimensionOne.stalk_domain x hx
  IsDiscreteValuationRing (X.presheaf.stalk x) := h.dvr x hx

/--
A scheme is called *normal* if every local ring is an integrally closed domain.
-/
class IsNormal (X : Scheme.{u}) where
  domain : ∀ x : X, IsDomain (X.presheaf.stalk x)
  integrallyClosed : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)

open Ring in
lemma Ring.dimensionLEOne_iff_krullDimLE_one {R : Type*} [CommRing R] [NoZeroDivisors R] :
    DimensionLEOne R ↔ KrullDimLE 1 R :=
  .trans ⟨fun h _ ↦ h.maximalOfPrime, fun h ↦ ⟨@h⟩⟩ krullDimLE_one_iff_of_noZeroDivisors.symm

/--
A normal, locally Noetherian scheme is regular in codimension one.
-/
instance (X : Scheme.{u}) [IsLocallyNoetherian X] [l : IsNormal X] :
    IsRegularInCodimensionOne X where
  domain := fun x _ ↦ l.domain x
  dvr := by
    intro x hx
    dsimp
    have a : ringKrullDim (X.presheaf.stalk x) = 1 := by
      /-
        exact IsDiscreteValuationRing.ringKrullDim_eq_one
        from the DVR branch
      -/
      sorry
    have m : IsDedekindDomain (X.presheaf.stalk x) := by
      rw [isDedekindDomain_iff (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact l.domain x
      · infer_instance

      · --rw [Ring.krullDimLE_iff]
        have := a.le

        sorry
      · have := l.integrallyClosed x
        exact fun _ ↦ IsIntegralClosure.isIntegral_iff.mp

    have : ¬ IsField (X.presheaf.stalk x) := by
      intro h
      let o : ringKrullDim ↑(X.presheaf.stalk x) = 0 := ringKrullDim_eq_zero_of_isField h
      rw [a] at o
      simp_all
    have := IsDiscreteValuationRing.TFAE (X.presheaf.stalk x) this
    exact (this.out 0 2).mpr m


/-
We wish to show in the end that a point on a scheme which is regular of codimension 1 can only lie
in one irreducible component.

The idea is that we get a singularity where the two irreducible components meet.
-/
end AlgebraicGeometry
