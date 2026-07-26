/-
Copyright (c) 2026 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Approximation

/-!
# Towards the fundamental inequality `deg (f)_∞ ≤ [k(X) : k(f)]`

Chevalley's proof exhibits `deg (f)_∞` many elements of `k(X)` linearly independent over
`k(f)`: at each pole `q` of `f` with multiplicity `b_q` and residue degree `d_q`, the
products `t_q^j · w_{q,e}` (`0 ≤ j < b_q`, `e` ranging over a residue basis) of an adapted
uniformizer and adapted residue lifts (from `Approximation.lean`). Independence is an
ultrametric leading-term argument, whose valuation-theoretic inputs are proved here:

* `ord_algebraMap_const`: nonzero constants have order zero everywhere;
* `ord_aeval`: at a pole of `f`, a polynomial in `f` has order `deg p · ord f` — the top
  monomial dominates (so in particular `p(f) ≠ 0`, reproving transcendence of `f`);
* `ord_algebraMap_of_notMem_maximalIdeal`: stalk units have order zero;
* `algebraMap_stalk_smul` / `residue_smul_stalk`: compatibility of the constants with the
  stalk inclusion and the residue map.
-/

universe u

open AlgebraicGeometry Scheme CategoryTheory Order Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option linter.overlappingInstances false

namespace AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule

variable {X : Scheme.{u}} (k : Type u) [Field k] [X.Over (Spec (CommRingCat.of k))]
variable [IsIntegral X] [IsLocallyNoetherian X] [IsRegularInCodimensionOne X]

/-- Nonzero constants have order zero everywhere. -/
lemma ord_algebraMap_const {a : k} (ha : a ≠ 0) (q : X) :
    X.ord (algebraMap k ↑X.functionField a) q = 0 := by
  by_cases hq : coheight q = 1
  · have hA : algebraMap k ↑X.functionField a ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap k ↑X.functionField).injective).mpr ha
    have hA' : algebraMap k ↑X.functionField a⁻¹ ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap k ↑X.functionField).injective).mpr (inv_ne_zero ha)
    have h1 := ord_algebraMap_const_nonneg k hq a
    have h2 := ord_algebraMap_const_nonneg k hq a⁻¹
    have h3 : (algebraMap k ↑X.functionField a) * (algebraMap k ↑X.functionField a⁻¹)
        = 1 := by
      rw [← map_mul, mul_inv_cancel₀ ha, map_one]
    have h4 := ord_mul hq hA hA'
    rw [h3, ord_one] at h4
    omega
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hq _

/-- **The valuation of a polynomial in `f` at a pole of `f`**: the top monomial dominates,
so `p(f) ≠ 0` and `ord (p(f)) = deg p · ord f`. -/
lemma ord_aeval {q : X} (hq : coheight q = 1) {f : ↑X.functionField} (hf0 : f ≠ 0)
    (hford : X.ord f q < 0) (p : Polynomial k) (hp : p ≠ 0) :
    Polynomial.aeval f p ≠ 0 ∧
      X.ord (Polynomial.aeval f p) q = (p.natDegree : ℤ) * X.ord f q := by
  suffices h : ∀ n : ℕ, ∀ p : Polynomial k, p ≠ 0 → p.natDegree ≤ n →
      Polynomial.aeval f p ≠ 0 ∧
      X.ord (Polynomial.aeval f p) q = (p.natDegree : ℤ) * X.ord f q from
    h p.natDegree p hp le_rfl
  intro n
  induction n with
  | zero =>
    intro p hp hdeg
    have h0 : p.natDegree = 0 := Nat.le_zero.mp hdeg
    have hpc : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
    have ha : p.coeff 0 ≠ 0 := fun h => hp (by rw [hpc, h, map_zero])
    constructor
    · rw [hpc, Polynomial.aeval_C]
      exact (map_ne_zero_iff _ (algebraMap k ↑X.functionField).injective).mpr ha
    · rw [h0, hpc, Polynomial.aeval_C, ord_algebraMap_const k ha]
      simp
  | succ m ih =>
    intro p hp hdeg
    by_cases hdm : p.natDegree ≤ m
    · exact ih p hp hdm
    have hdeg1 : p.natDegree = m + 1 := by omega
    have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have hlcK : algebraMap k ↑X.functionField p.leadingCoeff ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap k ↑X.functionField).injective).mpr hlc
    set G : ↑X.functionField :=
      algebraMap k ↑X.functionField p.leadingCoeff * f ^ (m + 1) with hG
    have hG0 : G ≠ 0 := mul_ne_zero hlcK (pow_ne_zero _ hf0)
    have hGord : X.ord G q = ((m + 1 : ℕ) : ℤ) * X.ord f q := by
      rw [hG, ord_mul hq hlcK (pow_ne_zero _ hf0), ord_algebraMap_const k hlc,
        ord_pow hf0]
      ring
    have hsplit : Polynomial.aeval f p = Polynomial.aeval f p.eraseLead + G := by
      conv_lhs => rw [← Polynomial.eraseLead_add_C_mul_X_pow p]
      rw [map_add, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, hdeg1]
    rcases eq_or_ne p.eraseLead 0 with h0 | h0
    · rw [hsplit, h0, map_zero, zero_add]
      exact ⟨hG0, by rw [hGord, hdeg1]⟩
    · obtain ⟨hel0, helord⟩ := ih p.eraseLead h0 (by
        have h1 := Polynomial.eraseLead_natDegree_le p
        omega)
      have hexp : ((m + 1 : ℕ) : ℤ) * X.ord f q
          = (m : ℤ) * X.ord f q + X.ord f q := by
        push_cast
        ring
      have hlt : X.ord G q < X.ord (Polynomial.aeval f p.eraseLead) q := by
        rw [hGord, helord, hexp]
        have hd : (p.eraseLead.natDegree : ℤ) ≤ (m : ℤ) := by
          have h1 := Polynomial.eraseLead_natDegree_le p
          push_cast
          omega
        have h2 : (m : ℤ) * X.ord f q ≤ (p.eraseLead.natDegree : ℤ) * X.ord f q :=
          mul_le_mul_of_nonpos_right hd (le_of_lt hford)
        linarith
      have hsum : X.ord (Polynomial.aeval f p) q = X.ord G q := by
        rw [hsplit, add_comm]
        exact ord_add_of_lt hq hG0 fun _ => hlt
      refine ⟨?_, by rw [hsum, hGord, hdeg1]⟩
      intro hzero
      rw [hsplit] at hzero
      have heq : Polynomial.aeval f p.eraseLead = -G := by linear_combination hzero
      rw [heq, ord_neg] at helord
      have h3 : ((m + 1 : ℕ) : ℤ) = (p.eraseLead.natDegree : ℤ) :=
        mul_right_cancel₀ (by omega : X.ord f q ≠ 0) (hGord.symm.trans helord)
      have h4 := Polynomial.eraseLead_natDegree_le p
      have h5 : p.eraseLead.natDegree = m + 1 := by exact_mod_cast h3.symm
      omega

/-- A stalk element outside the maximal ideal has order zero. -/
lemma ord_algebraMap_of_notMem_maximalIdeal {q : X} (hq : coheight q = 1)
    {y : ↑(X.presheaf.stalk q)} (hy0 : y ≠ 0)
    (hy : y ∉ IsLocalRing.maximalIdeal ↑(X.presheaf.stalk q)) :
    X.ord (algebraMap ↑(X.presheaf.stalk q) ↑X.functionField y) q = 0 := by
  have h1 := ord_algebraMap_nonneg hq hy0
  have h2 : ¬ (1 ≤ X.ord (algebraMap ↑(X.presheaf.stalk q) ↑X.functionField y) q) :=
    fun h => hy ((mem_maximalIdeal_iff_one_le_ord hq hy0).mpr h)
  omega

/-- The stalk inclusion is `k`-linear. -/
lemma algebraMap_stalk_smul (q : X) (a : k) (y : ↑(X.presheaf.stalk q)) :
    algebraMap ↑(X.presheaf.stalk q) ↑X.functionField (a • y)
      = a • algebraMap ↑(X.presheaf.stalk q) ↑X.functionField y := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]

/-- The residue map is `k`-linear. -/
lemma residue_smul_stalk (q : X) (a : k) (y : ↑(X.presheaf.stalk q)) :
    (X.residue q).hom (a • y) = a • (X.residue q).hom y := by
  rw [Algebra.smul_def, residue_algebraMap_mul]

omit k in
/-- Powers multiply memberships in the order filtration. -/
lemma pow_mem_ordSubmodule {q : X} (hq : coheight q = 1) {a : ℤ}
    {f : ↑X.functionField} (hf : f ∈ ordSubmodule hq a) (s : ℕ) :
    f ^ s ∈ ordSubmodule hq ((s : ℤ) * a) := by
  induction s with
  | zero =>
    rw [pow_zero]
    intro _
    rw [ord_one]
    simp
  | succ n ih =>
    have h1 := mul_mem_ordSubmodule hq ih hf
    rw [← pow_succ] at h1
    have hcast : ((n + 1 : ℕ) : ℤ) * a = (n : ℤ) * a + a := by
      push_cast
      ring
    rw [hcast]
    exact h1

/-! ### The adapted family and its independence -/

section Adapted

variable [IsNoetherian X]

/-- **Independence of the adapted family.** At each pole `q` of `f`, with multiplicity
`b_q` and residue degree `d_q`, there are elements `g_{q,j,e} = t_q^j · w_{q,e}`
(`j < b_q`, `e < d_q`) such that no nontrivial `k[f]`-linear combination of them vanishes.

The proof is the ultrametric leading-term argument at the pole `q₀` carrying a coefficient
of maximal degree `d`: correcting the sum by erasing the leading monomials of the
coefficients at the minimal exponent `j₀`, everything left has order at least
`-b₀·d + j₀ + 1` at `q₀` (using the vanishing of the adapted elements at the other poles),
while the leading term has order exactly `-b₀·d + j₀`, because the residues of the `w`'s
are linearly independent. -/
theorem exists_adapted_family
    (hκ : ∀ (q : X), coheight q = 1 → Module.Finite k ↑(X.residueField q))
    {f : ↑X.functionField} (hf0 : f ≠ 0)
    (hwit : ∀ q q' : X, coheight q = 1 → coheight q' = 1 → q ≠ q' →
      ∃ h : ↑X.functionField, 0 ≤ X.ord h q ∧ X.ord h q' < 0) :
    ∃ g : (Σ q : ↥(support_finite (polePart X f)).toFinset,
        Fin ((polePart X f) q.1).toNat ×
          Fin (Module.finrank k ↑(X.residueField q.1))) → ↑X.functionField,
      ∀ c : (Σ q : ↥(support_finite (polePart X f)).toFinset,
          Fin ((polePart X f) q.1).toNat ×
            Fin (Module.finrank k ↑(X.residueField q.1))) → Polynomial k,
        (∃ σ, c σ ≠ 0) → ∑ σ, Polynomial.aeval f (c σ) * g σ ≠ 0 := by
  classical
  set B := polePart X f with hB
  set P : Finset X := (support_finite B).toFinset with hP
  have hmemP : ∀ q : X, q ∈ P ↔ B q ≠ 0 := fun q => by
    rw [hP, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hcod : ∀ q ∈ P, coheight q = 1 := fun q hq =>
    polePart_support f (Function.mem_support.mpr ((hmemP q).mp hq))
  have hBapp : ∀ q : X, B q = max 0 (- X.ord f q) := fun _ => rfl
  have hBpos : ∀ q ∈ P, 1 ≤ B q := fun q hq => by
    have h1 := (hmemP q).mp hq
    have h2 := hBapp q
    omega
  have hford : ∀ q ∈ P, X.ord f q = -(B q) := fun q hq => by
    have h1 := hBpos q hq
    have h2 := hBapp q
    omega
  set Nmax : ℕ := 1 + P.sup fun q => (B q).toNat with hNmax
  haveI : ∀ q : ↥P, Module.Finite k ↑(X.residueField q.1) :=
    fun q => hκ q.1 (hcod q.1 q.2)
  -- the adapted uniformizers
  have ht : ∀ q : ↥P, ∃ t : ↑X.functionField, t ≠ 0 ∧ X.ord t q.1 = 1 ∧
      ∀ q' ∈ P.erase q.1, ∀ (hq' : coheight q' = 1), t ∈ ordSubmodule hq' (Nmax : ℤ) :=
    fun q => exists_uniformizer_approx (hcod q.1 q.2) (P.erase q.1)
      (fun q' hq' => hwit q.1 q' (hcod q.1 q.2)
        (hcod q' (Finset.mem_of_mem_erase hq'))
        (Ne.symm (Finset.mem_erase.mp hq').1)) Nmax (by omega)
  choose t ht0 ht1 htP using ht
  -- the adapted residue lifts at the basis vectors
  have hwex : ∀ (q : ↥P) (e : Fin (Module.finrank k ↑(X.residueField q.1))),
      ∃ (w : ↑X.functionField) (y : ↑(X.presheaf.stalk q.1)),
        algebraMap ↑(X.presheaf.stalk q.1) ↑X.functionField y = w ∧
        (X.residue q.1).hom y = (Module.finBasis k ↑(X.residueField q.1)) e ∧
        ∀ q' ∈ P.erase q.1, ∀ (hq' : coheight q' = 1),
          w ∈ ordSubmodule hq' (Nmax : ℤ) :=
    fun q e => exists_residueLift_approx (hcod q.1 q.2) (P.erase q.1)
      (fun q' hq' => hwit q.1 q' (hcod q.1 q.2)
        (hcod q' (Finset.mem_of_mem_erase hq'))
        (Ne.symm (Finset.mem_erase.mp hq').1)) Nmax (by omega) _
  choose w y hwy hres hwP using hwex
  have hy0 : ∀ (q : ↥P) e, y q e ≠ 0 := fun q e h0 => by
    have h1 := hres q e
    rw [h0, map_zero] at h1
    exact (Module.Basis.ne_zero (Module.finBasis k ↑(X.residueField q.1)) e) h1.symm
  have hw0 : ∀ (q : ↥P) e, w q e ≠ 0 := fun q e => by
    rw [← hwy q e]
    exact algebraMap_functionField_ne_zero (hy0 q e)
  have hword : ∀ (q : ↥P) e, X.ord (w q e) q.1 = 0 := fun q e => by
    rw [← hwy q e]
    refine ord_algebraMap_of_notMem_maximalIdeal (hcod q.1 q.2) (hy0 q e) fun hmem => ?_
    have h1 : (X.residue q.1).hom (y q e) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmem
    rw [hres q e] at h1
    exact (Module.Basis.ne_zero _ e) h1
  -- the family
  refine ⟨fun σ => t σ.1 ^ (σ.2.1 : ℕ) * w σ.1 σ.2.2, ?_⟩
  rintro c ⟨σ₀, hσ₀⟩ hS
  -- the maximal coefficient degree and the distinguished pole
  set Sne : Finset _ := Finset.univ.filter fun σ => c σ ≠ 0 with hSne
  have hSnon : Sne.Nonempty := ⟨σ₀, by simp [hSne, hσ₀]⟩
  set d : ℕ := Sne.sup fun σ => (c σ).natDegree with hd
  obtain ⟨σs, hσsmem, hσsval⟩ :=
    Finset.exists_mem_eq_sup Sne hSnon fun σ => (c σ).natDegree
  set q₀ : ↥P := σs.1 with hq₀
  have hq₀cod : coheight q₀.1 = 1 := hcod q₀.1 q₀.2
  set b₀ : ℤ := B q₀.1 with hb₀
  have hb₀pos : 1 ≤ b₀ := hBpos q₀.1 q₀.2
  have hford₀ : X.ord f q₀.1 = -b₀ := hford q₀.1 q₀.2
  have hdle : ∀ σ, c σ ≠ 0 → (c σ).natDegree ≤ d := fun σ hσ =>
    Finset.le_sup (f := fun σ => (c σ).natDegree) (by simp [hSne, hσ])
  -- the minimal leading exponent in the `q₀`-block
  set Jset : Finset (Fin (B q₀.1).toNat ×
      Fin (Module.finrank k ↑(X.residueField q₀.1))) :=
    Finset.univ.filter fun je => c ⟨q₀, je⟩ ≠ 0 ∧ (c ⟨q₀, je⟩).natDegree = d with hJset
  have hJne : Jset.Nonempty := by
    refine ⟨σs.2, ?_⟩
    simp only [hJset, Finset.mem_filter, Finset.mem_univ, true_and]
    have hcσs : c σs ≠ 0 := by
      have h1 := hσsmem
      simp only [hSne, Finset.mem_filter, Finset.mem_univ, true_and] at h1
      exact h1
    exact ⟨hcσs, hσsval.symm⟩
  set J0 : Finset ℕ := Jset.image fun je => (je.1 : ℕ) with hJ0
  have hJ0ne : J0.Nonempty := hJne.image _
  set j₀ : ℕ := J0.min' hJ0ne with hj₀def
  have hj₀mem : j₀ ∈ J0 := Finset.min'_mem _ _
  have hj₀lt : j₀ < (B q₀.1).toNat := by
    obtain ⟨je, hje, hjeq⟩ := Finset.mem_image.mp hj₀mem
    rw [← hjeq]
    exact je.1.isLt
  have hj₀b₀ : (j₀ : ℤ) + 1 ≤ b₀ := by
    have h1 : ((B q₀.1).toNat : ℤ) = b₀ := Int.toNat_of_nonneg (by omega)
    omega
  set jF : Fin (B q₀.1).toNat := ⟨j₀, hj₀lt⟩ with hjF
  have hj₀min : ∀ je ∈ Jset, j₀ ≤ (je.1 : ℕ) := fun je hje =>
    Finset.min'_le _ _ (Finset.mem_image_of_mem _ hje)
  set E₀ : Finset (Fin (Module.finrank k ↑(X.residueField q₀.1))) :=
    Finset.univ.filter fun e =>
      c ⟨q₀, (jF, e)⟩ ≠ 0 ∧ (c ⟨q₀, (jF, e)⟩).natDegree = d with hE₀
  have hE₀ne : E₀.Nonempty := by
    obtain ⟨je, hje, hjeq⟩ := Finset.mem_image.mp hj₀mem
    have hje1 : je.1 = jF := Fin.ext hjeq
    refine ⟨je.2, ?_⟩
    simp only [hE₀, Finset.mem_filter, Finset.mem_univ, true_and]
    have hpe : ((jF, je.2) : _ × _) = je := by rw [← hje1]
    rw [hpe]
    have := hje
    simp only [hJset, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this
  -- the leading combination of residue lifts is a unit at `q₀`
  set m₀ : ℤ := -(b₀ * d) + j₀ with hm₀
  set W₀ : ↑X.functionField :=
    ∑ e ∈ E₀, (c ⟨q₀, (jF, e)⟩).leadingCoeff • w q₀ e with hW₀
  set Y₀ : ↑(X.presheaf.stalk q₀.1) :=
    ∑ e ∈ E₀, (c ⟨q₀, (jF, e)⟩).leadingCoeff • y q₀ e with hY₀
  have hWY : algebraMap ↑(X.presheaf.stalk q₀.1) ↑X.functionField Y₀ = W₀ := by
    rw [hY₀, hW₀, map_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [algebraMap_stalk_smul, hwy]
  have hresY0 : (X.residue q₀.1).hom Y₀ ≠ 0 := by
    have hresY : (X.residue q₀.1).hom Y₀ = ∑ e ∈ E₀,
        (c ⟨q₀, (jF, e)⟩).leadingCoeff • (Module.finBasis k ↑(X.residueField q₀.1)) e := by
      rw [hY₀, map_sum]
      exact Finset.sum_congr rfl fun e _ => by rw [residue_smul_stalk, hres]
    rw [hresY]
    intro h0
    obtain ⟨e₀, he₀⟩ := hE₀ne
    have hli := (Module.finBasis k ↑(X.residueField q₀.1)).linearIndependent
    have h1 := linearIndependent_iff'.mp hli E₀
      (fun e => (c ⟨q₀, (jF, e)⟩).leadingCoeff) h0 e₀ he₀
    have he₀' := he₀
    simp only [hE₀, Finset.mem_filter, Finset.mem_univ, true_and] at he₀'
    exact Polynomial.leadingCoeff_ne_zero.mpr he₀'.1 h1
  have hY00 : Y₀ ≠ 0 := fun h0 => hresY0 (by rw [h0, map_zero])
  have hW00 : W₀ ≠ 0 := by
    rw [← hWY]
    exact algebraMap_functionField_ne_zero hY00
  have hWord : X.ord W₀ q₀.1 = 0 := by
    rw [← hWY]
    exact ord_algebraMap_of_notMem_maximalIdeal hq₀cod hY00 fun hmem =>
      hresY0 ((IsLocalRing.residue_eq_zero_iff _).mpr hmem)
  -- the leading term
  set L : ↑X.functionField := f ^ d * (t q₀ ^ j₀ * W₀) with hL
  have hL0 : L ≠ 0 := mul_ne_zero (pow_ne_zero _ hf0)
    (mul_ne_zero (pow_ne_zero _ (ht0 q₀)) hW00)
  have hLord : X.ord L q₀.1 = m₀ := by
    rw [hL, ord_mul hq₀cod (pow_ne_zero _ hf0)
        (mul_ne_zero (pow_ne_zero _ (ht0 q₀)) hW00),
      ord_mul hq₀cod (pow_ne_zero _ (ht0 q₀)) hW00, ord_pow hf0, ord_pow (ht0 q₀),
      ht1 q₀, hWord, hford₀, hm₀]
    ring
  -- the corrected coefficients
  set S₀ : Finset (Σ q : ↥P, Fin (B q.1).toNat ×
      Fin (Module.finrank k ↑(X.residueField q.1))) :=
    E₀.image fun e => ⟨q₀, (jF, e)⟩ with hS₀
  have hS₀deg : ∀ σ ∈ S₀, c σ ≠ 0 ∧ (c σ).natDegree = d := by
    rintro σ hσ
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hσ
    simp only [hE₀, Finset.mem_filter, Finset.mem_univ, true_and] at he
    exact he
  set c' : _ → Polynomial k := fun σ => if σ ∈ S₀ then (c σ).eraseLead else c σ with hc'
  have hc'ne : ∀ σ, c' σ ≠ 0 → c σ ≠ 0 := by
    intro σ hσ h0
    apply hσ
    simp only [hc']
    split_ifs <;> simp [h0]
  have hc'deg : ∀ σ, c' σ ≠ 0 → (c' σ).natDegree ≤ d := by
    intro σ hσ
    simp only [hc']
    split_ifs with hmem
    · have h1 := Polynomial.eraseLead_natDegree_le (c σ)
      have h2 := (hS₀deg σ hmem).2
      omega
    · refine hdle σ ?_
      simp only [hc'] at hσ
      rw [if_neg hmem] at hσ
      exact hσ
  -- the decomposition `S = S' + L`
  have hsplit : ∑ σ, Polynomial.aeval f (c σ) * (t σ.1 ^ (σ.2.1 : ℕ) * w σ.1 σ.2.2)
      = (∑ σ, Polynomial.aeval f (c' σ) * (t σ.1 ^ (σ.2.1 : ℕ) * w σ.1 σ.2.2)) + L := by
    have hterm : ∀ σ : (Σ q : ↥P, Fin (B q.1).toNat ×
          Fin (Module.finrank k ↑(X.residueField q.1))),
        Polynomial.aeval f (c σ) * (t σ.1 ^ (σ.2.1 : ℕ) * w σ.1 σ.2.2)
        = Polynomial.aeval f (c' σ) * (t σ.1 ^ (σ.2.1 : ℕ) * w σ.1 σ.2.2)
          + (if σ ∈ S₀ then
              algebraMap k ↑X.functionField (c σ).leadingCoeff * f ^ d *
                (t σ.1 ^ (σ.2.1 : ℕ) * w σ.1 σ.2.2)
            else 0) := by
      intro σ
      by_cases hmem : σ ∈ S₀
      · rw [if_pos hmem]
        have hc'σ : c' σ = (c σ).eraseLead := by
          simp only [hc']
          rw [if_pos hmem]
        have hcs : Polynomial.aeval f (c σ)
            = Polynomial.aeval f (c' σ)
              + algebraMap k ↑X.functionField (c σ).leadingCoeff * f ^ d := by
          conv_lhs => rw [← Polynomial.eraseLead_add_C_mul_X_pow (c σ)]
          rw [map_add, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
            (hS₀deg σ hmem).2, hc'σ]
        rw [hcs, add_mul]
      · have hc'σ : c' σ = c σ := by
          simp only [hc']
          rw [if_neg hmem]
        rw [if_neg hmem, hc'σ, add_zero]
    rw [Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_image fun e _ e' _ h => by simpa using h]
    rw [hL, hW₀, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    dsimp only
    rw [Algebra.smul_def]
    ring
  -- every corrected term has order at least `m₀ + 1` at `q₀`
  have hterm_mem : ∀ σ : (Σ q : ↥P, Fin (B q.1).toNat ×
        Fin (Module.finrank k ↑(X.residueField q.1))),
      Polynomial.aeval f (c' σ) * (t σ.1 ^ (σ.2.1 : ℕ) * w σ.1 σ.2.2)
      ∈ ordSubmodule hq₀cod (m₀ + 1) := by
    rintro ⟨q, j, e⟩
    dsimp only
    by_cases hc0 : c' ⟨q, (j, e)⟩ = 0
    · rw [hc0, map_zero, zero_mul]
      exact zero_mem _
    have hcne := hc'ne _ hc0
    rcases eq_or_ne q q₀ with rfl | hqne
    · -- same block: exact valuation count
      have hineq : m₀ + 1 ≤ -(b₀ * ((c' ⟨q₀, (j, e)⟩).natDegree : ℤ)) + (j : ℕ) := by
        by_cases hmem : (⟨q₀, (j, e)⟩ : Σ q : ↥P, Fin (B q.1).toNat ×
            Fin (Module.finrank k ↑(X.residueField q.1))) ∈ S₀
        · -- erased leading term: degree dropped by one
          have hdd := (hS₀deg _ hmem).2
          have hel : c' ⟨q₀, (j, e)⟩ = (c ⟨q₀, (j, e)⟩).eraseLead := by
            simp only [hc']
            rw [if_pos hmem]
          have h1 : ((c' ⟨q₀, (j, e)⟩).natDegree : ℤ) ≤ (d : ℤ) - 1 := by
            rw [hel]
            have h2 := Polynomial.eraseLead_natDegree_le (c ⟨q₀, (j, e)⟩)
            have h3 : 1 ≤ d := by
              by_contra h4
              have h5 : d = 0 := by omega
              have h6 : (c ⟨q₀, (j, e)⟩).natDegree = 0 := by omega
              apply hc0
              rw [hel, Polynomial.eq_C_of_natDegree_eq_zero h6]
              exact Polynomial.eraseLead_C _
            push_cast
            omega
          have h2 : b₀ * ((c' ⟨q₀, (j, e)⟩).natDegree : ℤ) ≤ b₀ * ((d : ℤ) - 1) :=
            mul_le_mul_of_nonneg_left h1 (by omega)
          have h3 : b₀ * ((d : ℤ) - 1) = b₀ * d - b₀ := by ring
          have h4 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := by positivity
          linarith [hj₀b₀]
        · -- untouched coefficient
          have hel : c' ⟨q₀, (j, e)⟩ = c ⟨q₀, (j, e)⟩ := by
            simp only [hc']
            rw [if_neg hmem]
          rw [hel]
          by_cases hdd : (c ⟨q₀, (j, e)⟩).natDegree = d
          · -- maximal degree: the exponent exceeds `j₀`
            have hjJ : (j, e) ∈ Jset := by
              simp only [hJset, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hcne, hdd⟩
            have hj1 : j₀ ≤ (j : ℕ) := hj₀min _ hjJ
            have hjne : (j : ℕ) ≠ j₀ := by
              intro heq
              apply hmem
              have hjFj : j = jF := Fin.ext heq
              rw [hS₀, Finset.mem_image]
              refine ⟨e, ?_, by rw [hjFj]⟩
              simp only [hE₀, Finset.mem_filter, Finset.mem_univ, true_and]
              rw [← hjFj]
              exact ⟨hcne, hdd⟩
            rw [hdd]
            have hj2 : j₀ + 1 ≤ (j : ℕ) := by omega
            have hcast : (j₀ : ℤ) + 1 ≤ ((j : ℕ) : ℤ) := by exact_mod_cast hj2
            linarith [hm₀]
          · -- smaller degree
            have hle := hdle _ hcne
            have h1 : ((c ⟨q₀, (j, e)⟩).natDegree : ℤ) ≤ (d : ℤ) - 1 := by
              push_cast
              omega
            have h2 : b₀ * ((c ⟨q₀, (j, e)⟩).natDegree : ℤ) ≤ b₀ * ((d : ℤ) - 1) :=
              mul_le_mul_of_nonneg_left h1 (by omega)
            have h3 : b₀ * ((d : ℤ) - 1) = b₀ * d - b₀ := by ring
            have h4 : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := by positivity
            linarith [hj₀b₀]
      -- assemble via the exact orders
      intro hne
      have haev := ord_aeval k hq₀cod hf0 (by omega) _ hc0
      rw [ord_mul hq₀cod haev.1 (mul_ne_zero (pow_ne_zero _ (ht0 q₀)) (hw0 q₀ e)),
        ord_mul hq₀cod (pow_ne_zero _ (ht0 q₀)) (hw0 q₀ e), haev.2,
        ord_pow (ht0 q₀), ht1 q₀, hword q₀ e, hford₀]
      have hcomm : ((c' ⟨q₀, (j, e)⟩).natDegree : ℤ) * -b₀
          = -(b₀ * ((c' ⟨q₀, (j, e)⟩).natDegree : ℤ)) := by ring
      linarith [hineq, hcomm]
    · -- other block: everything vanishes to high order at `q₀`
      have hq₀mem : q₀.1 ∈ P.erase q.1 :=
        Finset.mem_erase.mpr ⟨fun h => hqne (Subtype.ext h.symm), q₀.2⟩
      have htmem : t q ∈ ordSubmodule hq₀cod (0 : ℤ) :=
        ordSubmodule_mono hq₀cod (by positivity) (htP q q₀.1 hq₀mem hq₀cod)
      have htpow : t q ^ (j : ℕ) ∈ ordSubmodule hq₀cod (0 : ℤ) := by
        have h1 := pow_mem_ordSubmodule hq₀cod htmem (j : ℕ)
        rwa [mul_zero] at h1
      have hwmem : w q e ∈ ordSubmodule hq₀cod (Nmax : ℤ) :=
        hwP q e q₀.1 hq₀mem hq₀cod
      have haeval : Polynomial.aeval f (c' ⟨q, (j, e)⟩)
          ∈ ordSubmodule hq₀cod (-(b₀ * d)) := by
        intro hne
        rw [(ord_aeval k hq₀cod hf0 (by omega) _ hc0).2, hford₀]
        have h1 : ((c' ⟨q, (j, e)⟩).natDegree : ℤ) ≤ (d : ℤ) := by
          exact_mod_cast hc'deg _ hc0
        have h2 : (d : ℤ) * -b₀ ≤ ((c' ⟨q, (j, e)⟩).natDegree : ℤ) * -b₀ :=
          mul_le_mul_of_nonpos_right h1 (by omega)
        have h3 : (d : ℤ) * -b₀ = -(b₀ * d) := by ring
        linarith
      have hprod := mul_mem_ordSubmodule hq₀cod haeval
        (mul_mem_ordSubmodule hq₀cod htpow hwmem)
      refine ordSubmodule_mono hq₀cod ?_ hprod
      have hsup : (B q₀.1).toNat ≤ P.sup fun q => (B q).toNat :=
        Finset.le_sup (f := fun q => (B q).toNat) q₀.2
      have h1 : (j₀ : ℤ) + 1 ≤ (Nmax : ℤ) := by
        have h2 : ((B q₀.1).toNat : ℤ) = b₀ := Int.toNat_of_nonneg (by omega)
        rw [hNmax]
        push_cast
        omega
      linarith [hm₀]
  -- conclusion: the leading term would have order at least `m₀ + 1`
  have hSmem : (∑ σ, Polynomial.aeval f (c' σ) * (t σ.1 ^ (σ.2.1 : ℕ) * w σ.1 σ.2.2))
      ∈ ordSubmodule hq₀cod (m₀ + 1) :=
    sum_mem fun σ _ => hterm_mem σ
  rw [hsplit] at hS
  have hLeq : L = -(∑ σ, Polynomial.aeval f (c' σ) *
      (t σ.1 ^ (σ.2.1 : ℕ) * w σ.1 σ.2.2)) := by
    linear_combination hS
  have hLmem : L ∈ ordSubmodule hq₀cod (m₀ + 1) := by
    rw [hLeq]
    exact neg_mem hSmem
  have hfin := hLmem hL0
  rw [hLord] at hfin
  omega

open IntermediateField in
/-- **The adapted family is `k(f)`-linearly independent**: clearing denominators through
`mem_adjoin_simple_iff` reduces to the polynomial statement of `exists_adapted_family`. -/
theorem exists_linearIndependent_adapted
    (hκ : ∀ (q : X), coheight q = 1 → Module.Finite k ↑(X.residueField q))
    {f : ↑X.functionField} (hft : Transcendental k f)
    (hwit : ∀ q q' : X, coheight q = 1 → coheight q' = 1 → q ≠ q' →
      ∃ h : ↑X.functionField, 0 ≤ X.ord h q ∧ X.ord h q' < 0) :
    ∃ g : (Σ q : ↥(support_finite (polePart X f)).toFinset,
        Fin ((polePart X f) q.1).toNat ×
          Fin (Module.finrank k ↑(X.residueField q.1))) → ↑X.functionField,
      LinearIndependent ↥(adjoin k {f}) g := by
  classical
  have hf0 : f ≠ 0 := fun h => hft (h ▸ isAlgebraic_zero)
  obtain ⟨g, hg⟩ := exists_adapted_family k hκ hf0 hwit
  refine ⟨g, ?_⟩
  rw [linearIndependent_iff']
  intro s coeffs hsum σ₁ hσ₁mem
  by_contra hne
  -- represent the coefficients as quotients of polynomials in `f`
  have hrep : ∀ σ, ∃ r t : Polynomial k,
      ((coeffs σ : ↥(adjoin k {f})) : ↑X.functionField)
        = Polynomial.aeval f r / Polynomial.aeval f t :=
    fun σ => (IntermediateField.mem_adjoin_simple_iff _ _).mp (coeffs σ).2
  choose r₀ t₀ hrt using hrep
  -- normalize: use `(0, 1)` for the zero coefficients
  set r' : _ → Polynomial k := fun σ => if coeffs σ = 0 then 0 else r₀ σ with hr'
  set t' : _ → Polynomial k := fun σ => if coeffs σ = 0 then 1 else t₀ σ with ht'
  have ht'0 : ∀ σ, Polynomial.aeval f (t' σ) ≠ 0 := by
    intro σ
    simp only [ht']
    split_ifs with h
    · rw [map_one]
      exact one_ne_zero
    · intro h0
      refine h (Subtype.ext ?_)
      rw [hrt σ, h0, div_zero]
      rfl
  have hrep' : ∀ σ, ((coeffs σ : ↥(adjoin k {f})) : ↑X.functionField)
      = Polynomial.aeval f (r' σ) / Polynomial.aeval f (t' σ) := by
    intro σ
    simp only [hr', ht']
    split_ifs with h
    · rw [h, map_zero]
      simp
    · exact hrt σ
  -- the cleared-denominator coefficients
  set cc : _ → Polynomial k :=
    fun σ => if σ ∈ s then r' σ * (Finset.univ.erase σ).prod t' else 0 with hcc
  set T : Polynomial k := ∏ σ, t' σ with hT
  -- the cleared sum vanishes
  have hA : ∑ σ, Polynomial.aeval f (cc σ) * g σ = 0 := by
    have hsum' : ∑ τ ∈ s, ((coeffs τ : ↥(adjoin k {f})) : ↑X.functionField) * g τ = 0 := by
      rw [← hsum]
      exact Finset.sum_congr rfl fun τ _ => (Algebra.smul_def (coeffs τ) (g τ)).symm
    have hstep : ∀ σ, Polynomial.aeval f (cc σ) * g σ
        = if σ ∈ s then
            Polynomial.aeval f (r' σ * (Finset.univ.erase σ).prod t') * g σ
          else 0 := by
      intro σ
      simp only [hcc]
      split_ifs with h
      · rfl
      · rw [map_zero, zero_mul]
    calc ∑ σ, Polynomial.aeval f (cc σ) * g σ
        = ∑ σ ∈ s, Polynomial.aeval f (r' σ * (Finset.univ.erase σ).prod t') * g σ := by
          rw [Finset.sum_congr rfl fun σ _ => hstep σ, Finset.sum_ite_mem,
            Finset.univ_inter]
      _ = Polynomial.aeval f T
          * ∑ τ ∈ s, ((coeffs τ : ↥(adjoin k {f})) : ↑X.functionField) * g τ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun τ hτ => ?_
          have hTs : Polynomial.aeval f T
              = Polynomial.aeval f (t' τ)
                * Polynomial.aeval f ((Finset.univ.erase τ).prod t') := by
            rw [hT, ← map_mul, Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
          rw [hrep' τ, hTs, map_mul]
          field_simp
          rw [mul_div_cancel_right₀ _ (ht'0 τ)]
      _ = 0 := by rw [hsum', mul_zero]
  -- but the coefficient at `σ₁` is nonzero
  have hccσ₁ : cc σ₁ ≠ 0 := by
    simp only [hcc]
    rw [if_pos hσ₁mem]
    refine mul_ne_zero ?_ ?_
    · intro h0
      have h1 := hrep' σ₁
      rw [h0, map_zero, zero_div] at h1
      exact hne (Subtype.ext h1)
    · refine Finset.prod_ne_zero_iff.mpr fun τ _ => ?_
      intro h0
      refine ht'0 τ ?_
      simp only [ht']
      rw [h0]
      exact map_zero _
  exact hg cc ⟨σ₁, hccσ₁⟩ hA

open IntermediateField in
/-- **The fundamental inequality** `deg (f)_∞ ≤ [k(X) : k(f)]`: the adapted family has
`deg (f)_∞` members and is `k(f)`-linearly independent. -/
theorem degree_polePart_le_finrank
    (hκ : ∀ (q : X), coheight q = 1 → Module.Finite k ↑(X.residueField q))
    (hL0 : Module.Finite k (LSubmodule X k (0 : AlgebraicCycle X ℤ)))
    {f : ↑X.functionField} (hft : Transcendental k f)
    (hwit : ∀ q q' : X, coheight q = 1 → coheight q' = 1 → q ≠ q' →
      ∃ h : ↑X.functionField, 0 ≤ X.ord h q ∧ X.ord h q' < 0) :
    (polePart X f).degree k
      ≤ (Module.finrank ↥(adjoin k {f}) ↑X.functionField : ℤ) := by
  classical
  obtain ⟨g, hli⟩ := exists_linearIndependent_adapted k hκ hft hwit
  haveI := finite_adjoin_of_transcendental k hκ hL0 hft
  have hcard := hli.fintype_card_le_finrank
  -- identify the cardinality with the degree
  set B := polePart X f with hB
  set P : Finset X := (support_finite B).toFinset with hP
  have hcod : ∀ q ∈ P, coheight q = 1 := fun q hq =>
    polePart_support f (Function.mem_support.mpr (by
      rw [hP, Set.Finite.mem_toFinset] at hq
      exact hq))
  have hBnonneg : ∀ q : X, 0 ≤ B q := fun q => by
    have h1 := polePart_nonneg f q
    rwa [show (0 : AlgebraicCycle X ℤ) q = 0 from rfl] at h1
  have hcount : ((Fintype.card (Σ q : ↥P,
      Fin (B q.1).toNat × Fin (Module.finrank k ↑(X.residueField q.1)))) : ℤ)
      = B.degree k := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_prod, Fintype.card_fin]
    rw [AlgebraicCycle.degree,
      finsum_eq_finsetSum_of_support_subset
        (fun q => B q * (Module.finrank k ↑(X.residueField q) : ℤ)) (s := P)
        (by
          intro q hq
          have hq' : B q ≠ 0 := left_ne_zero_of_mul hq
          exact Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr hq')),
      ← Finset.sum_coe_sort P
        (fun q => B q * (Module.finrank k ↑(X.residueField q) : ℤ))]
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    push_cast
    rw [Int.toNat_of_nonneg (hBnonneg q.1)]
  omega

open IntermediateField in
/-- **The degree identity** `deg (f)_∞ = [k(X) : k(f)]` for a transcendental rational
function: both inequalities of the classical theorem. -/
theorem degree_polePart_eq_finrank
    (hκ : ∀ (q : X), coheight q = 1 → Module.Finite k ↑(X.residueField q))
    (hL0 : Module.Finite k (LSubmodule X k (0 : AlgebraicCycle X ℤ)))
    {f : ↑X.functionField} (hft : Transcendental k f)
    (hwit : ∀ q q' : X, coheight q = 1 → coheight q' = 1 → q ≠ q' →
      ∃ h : ↑X.functionField, 0 ≤ X.ord h q ∧ X.ord h q' < 0) :
    (polePart X f).degree k
      = (Module.finrank ↥(adjoin k {f}) ↑X.functionField : ℤ) := by
  refine le_antisymm (degree_polePart_le_finrank k hκ hL0 hft hwit) ?_
  haveI := finite_adjoin_of_transcendental k hκ hL0 hft
  exact card_le_degree_polePart k hκ hL0 hft
    (Module.finBasis ↥(adjoin k {f}) ↑X.functionField).linearIndependent

end Adapted

end AlgebraicGeometry.AlgebraicCycle.SheafViaSubmodule
