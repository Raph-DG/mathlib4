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

theorem RegularLocalRing.PrincilapIdealRing_of_ringKrullDim_eq_one
    {R : Type*} [CommRing R] [r : IsRegularLocalRing R]
    (h : ringKrullDim R = 1) : IsPrincipalIdealRing R := by
  classical
  have : (Submodule.spanFinrank (IsLocalRing.maximalIdeal R)) = 1 := by
    suffices (Submodule.spanFinrank (IsLocalRing.maximalIdeal R) : WithBot ℕ∞) = (1 : WithBot ℕ∞) by
      simp_all
    rw [isRegularLocalRing_iff] at r
    rwa [← h]
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ, (IsLocalRing.maximalIdeal R) = Submodule.span R {ϖ} := by
    have fg : Submodule.FG (IsLocalRing.maximalIdeal R) := Submodule.FG.of_finite
    obtain ⟨s, hs1, hs2⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank fg
    rw [this, Nat.cast_one, Set.encard_eq_one] at hs1
    obtain ⟨ϖ, hϖ⟩ := hs1
    use ϖ
    rw [← hϖ]
    exact hs2.symm
  have : Submodule.span R {ϖ} ≠ ⊤ := by
    rw [← hϖ]
    exact Ideal.IsPrime.ne_top'
  have inf := Ideal.iInf_pow_eq_bot_of_isLocalRing (Submodule.span R {ϖ}) this
  have (x : R) (hx : x ≠ 0) : ∃ n : ℕ, x ∈ (R ∙ ϖ) ^ n ∧ x ∉ (R ∙ ϖ) ^ (n + 1) := by
    by_contra!
    have b : (R ∙ ϖ) ^ 0 = ⊤ := by simp
    have : ∀ n : ℕ, x ∈ (R ∙ ϖ) ^ n := by
      intro n
      induction n with
      | zero =>
          rw [b]
          exact Submodule.mem_top
      | succ n ih =>
          exact this n ih
    rw [Submodule.eq_bot_iff] at inf
    simp only [Ideal.submodule_span_eq, Submodule.mem_iInf] at inf
    specialize inf x this
    exact hx inf
  have thingo (x : R) (hx : x ≠ 0) : ∃ (n : ℕ) (u : Rˣ), x = u * ϖ^n := by
    obtain ⟨n, hx1, hx2⟩ := this x hx
    use n
    obtain ⟨r, hr⟩ : ∃ r : R, x = r * ϖ^n := by
      rw [Submodule.span_pow] at hx1
      simp only [Set.singleton_pow, Ideal.submodule_span_eq, Ideal.mem_span_singleton] at hx1
      exact exists_eq_mul_left_of_dvd hx1
    have : IsUnit r := by
      rw [← IsLocalRing.notMem_maximalIdeal]
      intro o
      rw [hϖ] at o
      simp only [Ideal.submodule_span_eq, Ideal.mem_span_singleton] at o
      obtain ⟨m, rfl⟩ := o
      have hr' : x = m * ϖ ^ (n + 1) := by rw [hr]; ring
      have : x ∈ (R ∙ ϖ) ^ (n + 1) := by
        rw [Submodule.span_pow]
        simp only [Set.singleton_pow, Ideal.submodule_span_eq, Ideal.mem_span_singleton]
        exact dvd_of_mul_left_eq m (id (Eq.symm hr'))
      exact hx2 this
    use this.unit
    exact hr
  constructor
  intro I
  by_cases h : I = ⊥
  · simp [h, bot_isPrincipal]
  have : ∃ (n : ℕ) (u : Rˣ), u * ϖ^n ∈ I := by
    obtain ⟨r, hr⟩ : ∃ r : I, r ≠ 0 := by
      by_contra!
      simp only [Subtype.forall, Submodule.mk_eq_zero] at this
      have : I = ⊥ := (Submodule.eq_bot_iff I).mpr this
      exact h this
    have ⟨m, l, hl⟩ := thingo r (by simp [hr])
    use m, l
    rw [← hl]
    exact r.2
  let n := Nat.find this
  obtain ⟨u, hu⟩ := Nat.find_spec this
  constructor
  use ϖ^n
  apply le_antisymm
  · intro x hx
    by_cases hx' : x = 0
    · simp [hx']
    obtain ⟨m, w, hw⟩ := thingo x hx'
    simp only [Ideal.submodule_span_eq, hw, Units.isUnit, Ideal.unit_mul_mem_iff_mem]
    suffices n ≤ m by
      have : ϖ ^ m = ϖ ^ (m - n) * ϖ ^ n := by
        rw [← pow_add]
        have : (m - n) + n = m := by
          zify
          simp_all
        rw [this]
      rw [this]
      simp [Ideal.mem_span_singleton]
    have := Nat.find_min' this (m := m)
    apply this
    use w
    rw [← hw]
    exact hx
  · simp_all [n]

instance {R : Type*} [Field R] : IsPrincipalIdealRing R := inferInstance

instance {R : Type*} [CommRing R]
    [h : IsRegularLocalRing R] [k : Ring.KrullDimLE 1 R] : IsPrincipalIdealRing R := by
  rw [Ring.krullDimLE_iff] at k
  obtain h | h : ringKrullDim R = 0 ∨ ringKrullDim R = 1 := by
    have : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
    have : WithBot.unbot _ this ≤ 1 := by exact (WithBot.unbot_le_iff this).mpr k
    rw [le_iff_lt_or_eq] at this
    obtain h | h := this
    · left
      have ds : (ringKrullDim R).unbot this = 0 := by exact ENat.lt_one_iff_eq_zero.mp h
      have : (((ringKrullDim R).unbot this) : WithBot ℕ∞) = (0 : WithBot ℕ∞) := by simp [ds]
      simpa using this
    · right
      have : (((ringKrullDim R).unbot this) : WithBot ℕ∞) = (1 : WithBot ℕ∞) := by simp [h]
      simpa using this
  · have : IsField R := by
      apply (allowSynthFailures := true) Ring.KrullDimLE.isField_of_isDomain
      exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr h
    exact this.isPrincipalIdealRing
  · exact RegularLocalRing.PrincilapIdealRing_of_ringKrullDim_eq_one h

lemma isRegularLocalRing_iff_isDiscreteValuationRing_of_ringKrullDim_eq_one {R : Type*} [CommRing R]
    (h : ringKrullDim R = 1) :
    IsRegularLocalRing R ↔ ∃ _ : IsDomain R, IsDiscreteValuationRing R := by
  refine ⟨fun _ ↦ ?_, fun ⟨_, _⟩ ↦ inferInstance⟩
  have : Ring.KrullDimLE 1 R := by
    rw [Ring.krullDimLE_iff]
    exact h.le
  have : IsPrincipalIdealRing R := inferInstance
  use inferInstance
  apply IsDiscreteValuationRing.mk
  have : (⊥ : Ideal R).height = 0 := Ideal.height_bot
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at h
  suffices ((IsLocalRing.maximalIdeal R).height : WithBot ℕ∞) ≠ (⊥ : Ideal R).height by
    exact Ne.symm (Ne.symm fun a_1 ↦ this (congrArg WithBot.some (congrArg Ideal.height a_1)))
  simp [this, h]

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
