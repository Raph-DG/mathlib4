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

theorem RegularLocalRing.PrincilapIdealRing_of_ringKrullDim_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [r : IsRegularLocalRing R]
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
    --simp only [Ideal.submodule_span_eq] at hx1 hx2
    have : ∃ r : R, x = r * ϖ^n := by

      sorry

    /-
    This is more or less just a rephasing of the above statement - just take n to be the n used
    there, and unfold definitions
    -/
    sorry
  constructor
  intro I
  by_cases h : I = ⊥
  · simp [h, bot_isPrincipal]
  have : ∃ (n : ℕ) (u : Rˣ), u * ϖ^n ∈ I := by

    /-
    This is really just saying I is has a nonzero element, which is guaranteed by `h`
    -/
    sorry
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



instance {R : Type*} [CommRing R] [IsDomain R] [IsRegularLocalRing R] [Ring.KrullDimLE 1 R] :
    IsPrincipalIdealRing R := by

  /-
  Follows easily from the previous lemma
  -/
  sorry

lemma bingo {R : Type*} [CommRing R] [IsDomain R] (h : ringKrullDim R = 1) :
    IsRegularLocalRing R ↔ IsDiscreteValuationRing R := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ inferInstance⟩
  have : Ring.KrullDimLE 1 R :=
    -- This is trivial and I think in a branch somewhere (possibly it has now been merged?)
    -- Indeed it has been merged now
    sorry
  have : IsPrincipalIdealRing R := inferInstance
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

open Classical in
/--
This is the case because of our lemma above called bingo, these say essentially the same thing
-/
lemma fdsj (X : Scheme.{u}) : X.IsRegularInCodimensionLE 1 ↔
  X.SatisfiesInCodimensionLE 1
  (fun R ↦ ∃ h : IsDomain R, IsDiscreteValuationRing R) := sorry

/--
A normal, locally Noetherian scheme is regular in codimension one.
-/
instance (X : Scheme.{u}) [IsLocallyNoetherian X] [l : IsNormal X] :
    X.IsRegularInCodimensionLE 1 := by
  rw [fdsj]
  constructor
  intro x hx
  use l.domain x
  dsimp
  have a : ringKrullDim (X.presheaf.stalk x) = 1 := by
    /-
      exact IsDiscreteValuationRing.ringKrullDim_eq_one
      from the DVR branch (which we now have in mathlib :))
    -/
    sorry
  have m : IsDedekindDomain (X.presheaf.stalk x) := by
    rw [isDedekindDomain_iff (X.presheaf.stalk x) (FractionRing (X.presheaf.stalk x))]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact l.domain x
    · infer_instance
    · --rw [Ring.krullDimLE_iff]
      have := a.le
      /-
      Completely trivial, should be assumption
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
  exact (this.out 0 2).mpr m

end AlgebraicGeometry
