/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.RiemannInequality

/-!
# Weak approximation at codimension-one points

The **fundamental inequality** `deg (f)_∞ ≤ [k(X) : k(f)]` — the missing half of the degree
identity needed for Riemann's inequality — is proved by exhibiting `deg (f)_∞` many elements
of `k(X)` that are linearly independent over `k(f)`: adapted products of uniformizer powers
and residue-basis lifts at each pole of `f`. For the valuation-theoretic independence
argument these local elements must be *normalized at the other poles*, which is the classical
weak approximation theorem for the finitely many (pairwise incomparable) discrete valuations
`ord_q` at the poles.

This file proves weak approximation from pairwise *incomparability witnesses*
(`∃ h, 0 ≤ ord_q h ∧ ord_{q'} h < 0` — to be discharged from separatedness via the
uniqueness part of the valuative criterion):

* `exists_separator` (Artin's lemma): there is `z` with `ord_q z > 0` and `ord_{q'} z < 0`
  for every `q'` in a finite set, by induction using the `z^m + u` trick;
* `exists_approx`: the idempotent-style approximant `W = (1 + z^s)⁻¹`, congruent to `1` at
  `q` and vanishing at each `q'`, both to order at least `s`;
* `exists_uniformizer_approx`, `exists_residueLift_approx`: the adapted local elements —
  a uniformizer at `q` vanishing to high order at the other points, and a lift of a
  prescribed residue class at `q` vanishing to high order at the other points.

Also contains the supporting `ord` arithmetic: orders of inverses and negations, the
ultrametric equality `ord (f + g) = ord f` for `ord f < ord g`, and product/power
memberships for `ordSubmodule`.
-/

universe u

open AlgebraicGeometry Scheme CategoryTheory Order Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option linter.overlappingInstances false

namespace AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-! ### Arithmetic of orders: inverses, negation, and the ultrametric equality -/

section OrdArithmetic

/-- The order of an inverse. -/
lemma ord_inv {g : ↑X.functionField} (hg : g ≠ 0) (q : X) :
    X.ord g⁻¹ q = - X.ord g q := by
  by_cases hq : coheight q = 1
  · have h1 : g * g⁻¹ = 1 := mul_inv_cancel₀ hg
    have h2 := ord_mul hq hg (inv_ne_zero hg)
    rw [h1, ord_one] at h2
    omega
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hq,
      Scheme.ord_eq_zero_of_coheight_neq_one hq]
    ring

/-- The order of `-1` vanishes. -/
lemma ord_neg_one (q : X) : X.ord (-1 : ↑X.functionField) q = 0 := by
  by_cases hq : coheight q = 1
  · have h2 := ord_mul hq (neg_ne_zero.mpr (one_ne_zero (α := ↑X.functionField)))
      (neg_ne_zero.mpr one_ne_zero)
    rw [neg_mul_neg, one_mul, ord_one] at h2
    omega
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hq _

/-- The order of a negation. -/
lemma ord_neg (g : ↑X.functionField) (q : X) : X.ord (-g) q = X.ord g q := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [neg_zero]
  by_cases hq : coheight q = 1
  · have heq : -g = -1 * g := by ring
    rw [heq, ord_mul hq (neg_ne_zero.mpr one_ne_zero) hg, ord_neg_one]
    ring
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hq,
      Scheme.ord_eq_zero_of_coheight_neq_one hq]

variable [IsRegularInCodimensionOne X]

/-- The ultrametric equality: if `ord f < ord g`, the sum has the order of `f`. -/
lemma ord_add_of_lt {q : X} (hq : coheight q = 1) {f g : ↑X.functionField}
    (hf : f ≠ 0) (hlt : g ≠ 0 → X.ord f q < X.ord g q) :
    X.ord (f + g) q = X.ord f q := by
  haveI : IsDiscreteValuationRing ↑(X.presheaf.stalk q) :=
    IsRegularInCodimensionOne.stalk_dvr q hq
  rcases eq_or_ne g 0 with rfl | hg
  · rw [add_zero]
  have hlt' := hlt hg
  have hfg : f + g ≠ 0 := by
    intro h0
    have hgf : g = -f := by linear_combination h0
    rw [hgf, ord_neg] at hlt'
    omega
  have h1 := ord_add hq hfg
  have h2 : min (X.ord (f + g) q) (X.ord (-g) q) ≤ X.ord f q := by
    have h3 := ord_add hq (f := f + g) (g := -g) (by simpa using hf)
    simpa using h3
  rw [ord_neg] at h2
  omega

/-- Products add memberships in the order filtration. -/
lemma mul_mem_ordSubmodule {q : X} (hq : coheight q = 1) {a b : ℤ}
    {f g : ↑X.functionField} (hf : f ∈ ordSubmodule hq a) (hg : g ∈ ordSubmodule hq b) :
    f * g ∈ ordSubmodule hq (a + b) := by
  rw [mem_ordSubmodule_iff]
  intro hfg
  have hf0 : f ≠ 0 := left_ne_zero_of_mul hfg
  have hg0 : g ≠ 0 := right_ne_zero_of_mul hfg
  have h1 := hf hf0
  have h2 := hg hg0
  rw [ord_mul hq hf0 hg0]
  omega

/-- The filtration is antitone in the order bound. -/
lemma ordSubmodule_mono {q : X} (hq : coheight q = 1) {a b : ℤ} (h : a ≤ b)
    {f : ↑X.functionField} (hf : f ∈ ordSubmodule hq b) : f ∈ ordSubmodule hq a := by
  rw [mem_ordSubmodule_iff]
  intro hne
  have h1 := hf hne
  omega

end OrdArithmetic

/-! ### Artin's separator and weak approximation -/

section Approximation

variable [IsRegularInCodimensionOne X]

/-- A uniformizer at `q`, as a rational function of order exactly one. -/
lemma exists_ord_eq_one {q : X} (hq : coheight q = 1) :
    ∃ a : ↑X.functionField, a ≠ 0 ∧ X.ord a q = 1 := by
  haveI : IsDiscreteValuationRing ↑(X.presheaf.stalk q) :=
    IsRegularInCodimensionOne.stalk_dvr q hq
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible ↑(X.presheaf.stalk q)
  refine ⟨(algebraMap ↑(X.presheaf.stalk q) ↑X.functionField ϖ) ^ (1 : ℤ), ?_, ?_⟩
  · exact zpow_ne_zero _ (algebraMap_functionField_ne_zero hϖ.ne_zero)
  · rw [ord_zpow_algebraMap_irreducible hq hϖ 1]

/-- From an incomparability witness, an element strictly positive at `q` and arbitrarily
negative at `q'`. -/
lemma exists_ord_pos_ord_lt {q q' : X} (hq : coheight q = 1)
    {h : ↑X.functionField} (hhq : 0 ≤ X.ord h q) (hhq' : X.ord h q' < 0) (N : ℤ) :
    ∃ u : ↑X.functionField, u ≠ 0 ∧ 1 ≤ X.ord u q ∧ X.ord u q' < N := by
  have hh0 : h ≠ 0 := by
    intro h0
    rw [h0] at hhq'
    simp at hhq'
  obtain ⟨a, ha0, ha1⟩ := exists_ord_eq_one hq
  set M : ℕ := (X.ord a q' - N).toNat + 1 with hM
  refine ⟨a * h ^ M, mul_ne_zero ha0 (pow_ne_zero _ hh0), ?_, ?_⟩
  · by_cases hq1 : coheight q = 1
    · rw [ord_mul hq1 ha0 (pow_ne_zero _ hh0), ord_pow hh0, ha1]
      have h1 : (0 : ℤ) ≤ (M : ℤ) * X.ord h q := mul_nonneg (by positivity) hhq
      omega
    · exact absurd hq hq1
  · by_cases hq'1 : coheight q' = 1
    · rw [ord_mul hq'1 ha0 (pow_ne_zero _ hh0), ord_pow hh0]
      have h1 : (M : ℤ) * X.ord h q' ≤ (M : ℤ) * (-1) :=
        mul_le_mul_of_nonneg_left (by omega) (by positivity)
      have h2 : (X.ord a q' - N).toNat + 1 ≤ (M : ℤ) := by
        rw [hM]
        push_cast
        omega
      omega
    · rw [Scheme.ord_eq_zero_of_coheight_neq_one hq'1] at hhq'
      omega

/-- **Artin's separator.** Given pairwise incomparability witnesses between `q` and each
point of a finite set `P`, there is a rational function strictly positive at `q` and
strictly negative at every point of `P`. -/
lemma exists_separator {q : X} (hq : coheight q = 1) (P : Finset X)
    (hwit : ∀ q' ∈ P, ∃ h : ↑X.functionField, 0 ≤ X.ord h q ∧ X.ord h q' < 0) :
    ∃ z : ↑X.functionField, z ≠ 0 ∧ 1 ≤ X.ord z q ∧ ∀ q' ∈ P, X.ord z q' < 0 := by
  classical
  induction P using Finset.induction with
  | empty =>
    obtain ⟨a, ha0, ha1⟩ := exists_ord_eq_one hq
    exact ⟨a, ha0, by omega, fun q' h => absurd h (Finset.notMem_empty q')⟩
  | insert q₀ P' hq₀P' ih =>
    haveI : IsDiscreteValuationRing ↑(X.presheaf.stalk q) :=
      IsRegularInCodimensionOne.stalk_dvr q hq
    obtain ⟨z, hz0, hzq, hzP⟩ := ih fun q' h => hwit q' (Finset.mem_insert_of_mem h)
    obtain ⟨h, hhq, hhq₀⟩ := hwit q₀ (Finset.mem_insert_self q₀ P')
    obtain ⟨u, hu0, huq, huq₀⟩ := exists_ord_pos_ord_lt hq hhq hhq₀ 0
    by_cases hzq₀ : X.ord z q₀ < 0
    · exact ⟨z, hz0, hzq, fun q' hq' => by
        rcases Finset.mem_insert.mp hq' with rfl | hmem
        · exact hzq₀
        · exact hzP q' hmem⟩
    -- `ord z q₀ ≥ 0`: replace `z` by `z^m + u` for `m` large
    push_neg at hzq₀
    set m : ℕ := 1 + P'.sup fun q'' => (- X.ord u q'').toNat with hm
    have hm1 : 1 ≤ m := by omega
    have hne : z ^ m + u ≠ 0 := by
      intro h0
      have hzu : z ^ m = -u := by linear_combination h0
      have h1 : X.ord (z ^ m) q₀ = X.ord (-u) q₀ := by rw [hzu]
      rw [ord_pow hz0, ord_neg] at h1
      have h2 : (0 : ℤ) ≤ (m : ℤ) * X.ord z q₀ := mul_nonneg (by positivity) hzq₀
      omega
    refine ⟨z ^ m + u, hne, ?_, ?_⟩
    · -- at `q` both terms are strictly positive
      by_cases hq1 : coheight q = 1
      · have h1 := ord_add hq1 hne
        rw [ord_pow hz0] at h1
        have h2 : (m : ℤ) * 1 ≤ (m : ℤ) * X.ord z q :=
          mul_le_mul_of_nonneg_left hzq (by positivity)
        omega
      · exact absurd hq hq1
    · intro q' hq'
      rcases Finset.mem_insert.mp hq' with rfl | hmem
      · -- at `q₀`: the `u`-term dominates
        by_cases hq₀1 : coheight q' = 1
        · rw [add_comm]
          rw [ord_add_of_lt hq₀1 hu0 fun _ => ?_]
          · exact huq₀
          · rw [ord_pow hz0]
            have h2 : (0 : ℤ) ≤ (m : ℤ) * X.ord z q' := mul_nonneg (by positivity) hzq₀
            omega
        · rw [Scheme.ord_eq_zero_of_coheight_neq_one hq₀1] at huq₀
          omega
      · -- at `q' ∈ P'`: the `z^m`-term dominates
        have hzq' := hzP q' hmem
        have hq'1 : coheight q' = 1 := by
          by_contra h1
          rw [Scheme.ord_eq_zero_of_coheight_neq_one h1] at hzq'
          omega
        rw [ord_add_of_lt hq'1 (pow_ne_zero _ hz0) fun _ => ?_, ord_pow hz0]
        · have h2 : (m : ℤ) * X.ord z q' ≤ (m : ℤ) * (-1) :=
            mul_le_mul_of_nonneg_left (by omega) (by positivity)
          omega
        · rw [ord_pow hz0]
          -- `m·ord z q' ≤ -m < ord u q'` by the choice of `m`
          have h3 : (- X.ord u q').toNat ≤ P'.sup fun q'' => (- X.ord u q'').toNat :=
            Finset.le_sup (f := fun q'' => (- X.ord u q'').toNat) hmem
          have h4 : (m : ℤ) * X.ord z q' ≤ (m : ℤ) * (-1) :=
            mul_le_mul_of_nonneg_left (by omega) (by positivity)
          have h6 : ((- X.ord u q').toNat : ℤ) < (m : ℤ) := by
            rw [hm]
            push_cast
            omega
          omega

/-- **Weak approximation.** Given incomparability witnesses between `q` and each point of a
finite set `P`, there is a rational function congruent to `1` at `q` and vanishing at every
point of `P`, both to order at least `s`. -/
lemma exists_approx {q : X} (hq : coheight q = 1) (P : Finset X)
    (hwit : ∀ q' ∈ P, ∃ h : ↑X.functionField, 0 ≤ X.ord h q ∧ X.ord h q' < 0)
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ W : ↑X.functionField, W ≠ 0 ∧ X.ord W q = 0 ∧
      (W - 1) ∈ ordSubmodule hq (s : ℤ) ∧
      ∀ q' ∈ P, ∀ (hq' : coheight q' = 1), W ∈ ordSubmodule hq' (s : ℤ) := by
  obtain ⟨z, hz0, hzq, hzP⟩ := exists_separator hq P hwit
  set v := z ^ s with hv
  have hv0 : v ≠ 0 := pow_ne_zero _ hz0
  have hvq : (s : ℤ) ≤ X.ord v q := by
    rw [hv, ord_pow hz0]
    have h1 : (s : ℤ) * 1 ≤ (s : ℤ) * X.ord z q :=
      mul_le_mul_of_nonneg_left hzq (by positivity)
    omega
  have h1v : (1 : ↑X.functionField) + v ≠ 0 := by
    intro h0
    have hveq : v = -1 := by linear_combination h0
    have h2 : X.ord v q = 0 := by rw [hveq, ord_neg_one]
    omega
  have hord1v : X.ord (1 + v) q = X.ord (1 : ↑X.functionField) q :=
    ord_add_of_lt hq one_ne_zero fun _ => by
      rw [ord_one]
      omega
  rw [ord_one] at hord1v
  refine ⟨(1 + v)⁻¹, inv_ne_zero h1v, by rw [ord_inv h1v, hord1v, neg_zero], ?_, ?_⟩
  · -- `(1+v)⁻¹ − 1 = −v·(1+v)⁻¹` has order at least `s` at `q`
    rw [mem_ordSubmodule_iff]
    intro hne
    have heq : (1 + v)⁻¹ - 1 = -(v * (1 + v)⁻¹) := by
      field_simp
      ring
    rw [heq, ord_neg, ord_mul hq hv0 (inv_ne_zero h1v), ord_inv h1v, hord1v]
    omega
  · intro q' hq'mem hq'1
    rw [mem_ordSubmodule_iff]
    intro _
    have hzq' := hzP q' hq'mem
    have hvq' : X.ord v q' ≤ -(s : ℤ) := by
      rw [hv, ord_pow hz0]
      have h1 : (s : ℤ) * X.ord z q' ≤ (s : ℤ) * (-1) :=
        mul_le_mul_of_nonneg_left (by omega) (by positivity)
      omega
    have hord1v' : X.ord (1 + v) q' = X.ord v q' := by
      rw [add_comm]
      exact ord_add_of_lt hq'1 hv0 fun _ => by
        rw [ord_one]
        omega
    rw [ord_inv h1v, hord1v']
    omega

/-- An adapted uniformizer: order exactly one at `q`, vanishing to order at least `s` at
each point of `P`. -/
lemma exists_uniformizer_approx {q : X} (hq : coheight q = 1) (P : Finset X)
    (hwit : ∀ q' ∈ P, ∃ h : ↑X.functionField, 0 ≤ X.ord h q ∧ X.ord h q' < 0)
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ t : ↑X.functionField, t ≠ 0 ∧ X.ord t q = 1 ∧
      ∀ q' ∈ P, ∀ (hq' : coheight q' = 1), t ∈ ordSubmodule hq' (s : ℤ) := by
  classical
  obtain ⟨a, ha0, ha1⟩ := exists_ord_eq_one hq
  -- vanishing order needed at the other points: enough to absorb the poles of `a`
  set s' : ℕ := s + P.sup fun q'' => (- X.ord a q'').toNat with hs'
  obtain ⟨W, hW0, hWq, hW1, hWP⟩ := exists_approx hq P hwit s' (by omega)
  refine ⟨a * W, mul_ne_zero ha0 hW0, ?_, ?_⟩
  · rw [ord_mul hq ha0 hW0, ha1, hWq]
    omega
  · intro q' hq'mem hq'1
    rw [mem_ordSubmodule_iff]
    intro _
    have h1 := hWP q' hq'mem hq'1 hW0
    have h2 : (- X.ord a q').toNat ≤ P.sup fun q'' => (- X.ord a q'').toNat :=
      Finset.le_sup (f := fun q'' => (- X.ord a q'').toNat) hq'mem
    rw [ord_mul hq'1 ha0 hW0]
    have h4 : (s : ℤ) + ((- X.ord a q').toNat : ℤ) ≤ (s' : ℤ) := by
      rw [hs']
      push_cast
      omega
    omega

/-- An adapted residue lift: for a prescribed class `γ` in the residue field at `q`, a
rational function regular at `q` with stalk representative of residue `γ`, vanishing to
order at least `s` at each point of `P`. -/
lemma exists_residueLift_approx {q : X} (hq : coheight q = 1) (P : Finset X)
    (hwit : ∀ q' ∈ P, ∃ h : ↑X.functionField, 0 ≤ X.ord h q ∧ X.ord h q' < 0)
    (s : ℕ) (hs : 1 ≤ s) (γ : ↑(X.residueField q)) :
    ∃ (w : ↑X.functionField) (y : ↑(X.presheaf.stalk q)),
      algebraMap ↑(X.presheaf.stalk q) ↑X.functionField y = w ∧
      (X.residue q).hom y = γ ∧
      ∀ q' ∈ P, ∀ (hq' : coheight q' = 1), w ∈ ordSubmodule hq' (s : ℤ) := by
  classical
  obtain ⟨y₀, hy₀⟩ := IsLocalRing.residue_surjective (b := γ)
  have hy₀' : (X.residue q).hom y₀ = γ := hy₀
  rcases eq_or_ne y₀ 0 with rfl | hy00
  · -- the class is zero: take the zero function
    exact ⟨0, 0, map_zero _, by rw [← hy₀'], fun q' _ _ =>
      fun hne => absurd rfl hne⟩
  set w₀ := algebraMap ↑(X.presheaf.stalk q) ↑X.functionField y₀ with hw₀
  have hw₀0 : w₀ ≠ 0 := algebraMap_functionField_ne_zero hy00
  -- vanishing order needed at the other points: enough to absorb the poles of `w₀`
  set s' : ℕ := s + P.sup fun q'' => (- X.ord w₀ q'').toNat with hs'
  obtain ⟨W, hW0, hWq, hW1, hWP⟩ := exists_approx hq P hwit s' (by omega)
  -- `W` is regular at `q`; take a stalk representative
  obtain ⟨yW, hyW⟩ := (mem_range_algebraMap_iff_ord_nonneg hq W).mpr fun _ => by rw [hWq]
  refine ⟨w₀ * W, y₀ * yW, ?_, ?_, ?_⟩
  · rw [map_mul, hyW]
  · -- the residue of the corrected lift is unchanged: `residue yW = 1`
    rw [map_mul, hy₀']
    have hres1 : (X.residue q).hom yW = 1 := by
      have h1 : algebraMap ↑(X.presheaf.stalk q) ↑X.functionField (yW - 1) = W - 1 := by
        rw [map_sub, hyW, map_one]
      rcases eq_or_ne (yW - 1) 0 with h0 | h0
      · rw [sub_eq_zero.mp h0, map_one]
      · have hWne : W - 1 ≠ 0 := by
          intro hz
          rw [hz] at h1
          exact h0 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mp h1)
        have h2 : (yW - 1) ∈ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk q) := by
          rw [mem_maximalIdeal_iff_one_le_ord hq h0, h1]
          have h3 := hW1 hWne
          omega
        have h3 := (IsLocalRing.residue_eq_zero_iff _).mpr h2
        rw [map_sub, map_one, sub_eq_zero] at h3
        exact h3
    rw [hres1, mul_one]
  · intro q' hq'mem hq'1
    rw [mem_ordSubmodule_iff]
    intro _
    have h1 := hWP q' hq'mem hq'1 hW0
    have h2 : (- X.ord w₀ q').toNat ≤ P.sup fun q'' => (- X.ord w₀ q'').toNat :=
      Finset.le_sup (f := fun q'' => (- X.ord w₀ q'').toNat) hq'mem
    rw [ord_mul hq'1 hw₀0 hW0]
    have h4 : (s : ℤ) + ((- X.ord w₀ q').toNat : ℤ) ≤ (s' : ℤ) := by
      rw [hs']
      push_cast
      omega
    omega

end Approximation

end AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule
