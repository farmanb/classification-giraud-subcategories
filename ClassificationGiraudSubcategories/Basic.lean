/-
Copyright (c) 2025 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
import Mathlib.Order.PFilter
import Mathlib.RingTheory.Ideal.Colon

open scoped Pointwise

/-!
# Ideal Filters

An **ideal filter** is a filter in the lattice of ideals of a ring `A`.

## Main definitions

* `IdealFilter A`: the type of an ideal filter on a ring `A`.
* `IsUniform F` : a filter `F` is uniform if whenever `I` is an ideal in the filter, then for all
  `a : A`, the colon ideal `I.colon (Ideal.span {a})` is in `F`.
* `IsTorsionElem` : Given a filter `F`, an element, `m`, of an `A`-module, `M`, is `F`-torsion if
  there exists an ideal `L` in `F` that annihilates `m`.
* `IsTorsion` : Given a filter `F`, an `A`-module, `M`, is `F`-torsion if every element is torsion.
* `gabrielComposition` : Given two filters `F` and `G`, the Gabriel composition of `F` and `G` is
  the set of ideals `L` of `A` such that there exists an ideal `K` in `G` with `K/L` `F`-torsion.
  This is again a filter.
* `IsGabriel F` : a filter `F` is a Gabriel filter if it is uniform and satisfies axiom T4:
  for all `I : Ideal A`, if there exists `J ∈ F` such that for all `x ∈ J` the colon ideal
  `I.colon (Ideal.span {x})` is in `F`, then `I ∈ F`.

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]
* [nLab: Uniform Filter](https://ncatlab.org/nlab/show/uniform+filter)
* [nLab: Gabriel Filter](https://ncatlab.org/nlab/show/Gabriel+filter)
* [nLab: Gabriel Composition](https://ncatlab.org/nlab/show/Gabriel+composition+of+filters)

## Tags

category theory, ideal, filter, uniform filter, Gabriel filter
-/
universe u v

abbrev IdealFilter (A : Type u) [Ring A] := Order.PFilter (Ideal A)

namespace IdealFilter

variable {A : Type u} [Ring A]

structure IsUniform (F : IdealFilter A) : Prop where
  /-- If `I ∈ F`, then for every `a : A` the colon ideal `I.colon (Ideal.span {a})`
  also belongs to `F`. -/
  colon_closed {I : Ideal A} (h_I : I ∈ F) (a : A) : (I.colon (Ideal.span {a})) ∈ F

namespace IsUniform
lemma colon_mem {F : IdealFilter A} (h : F.IsUniform) {I : Ideal A} (h_I : I ∈ F) (a : A) :
    I.colon (Ideal.span {a}) ∈ F :=
  h.colon_closed h_I a
end IsUniform

/-- We say that an element `m : M` is `F`-torsion if it is annihilated by some ideal belonging to
the filter `F`.  That is, there exists `L ∈ F` such that every `a ∈ L` satisfies
`a • m = 0`. -/
def IsTorsionElem (F : IdealFilter A)
    {M : Type v} [AddCommMonoid M] [Module A M] (m : M) : Prop :=
  ∃ L ∈ F, ∀ a ∈ L, a • m = 0

/-- We say that an `A`-module `M` is `F`-torsion if every element of `M` is `F`-torsion in the
sense of `IsTorsionElem`. -/
def IsTorsion (F : IdealFilter A)
    (M : Type v) [AddCommMonoid M] [Module A M] : Prop :=
  ∀ m : M, IsTorsionElem F m

/-- We say that the quotient `K/L` is `F`-torsion if every element `k ∈ K` is annihilated
(modulo `L`) by some ideal in `F`.  Equivalently, for each `k ∈ K` there exists `I ∈ F`
such that `I ≤ L.colon (Ideal.span {k})`. That is to say, every `a ∈ I` satisfies `a * k ∈ L`.
This formulation avoids forming the quotient module explicitly. -/
def IsTorsionQuot (F : IdealFilter A) (L K : Ideal A) : Prop :=
  ∀ k ∈ K, ∃ I ∈ F, I ≤ L.colon (Ideal.span {k})

/-- If `k ∈ K`, then intersecting with `K` does not change the colon ideal. That is to say, there is
an equality of colon ideals `L.colon (Ideal.span {k}) = (L ⊓ K).colon (Ideal.span {k})` -/
lemma colon_inf_eq_of_mem (L K : Ideal A) {k : A} (h_k : k ∈ K) :
    (L ⊓ K).colon (Ideal.span ({k} : Set A)) = L.colon (Ideal.span ({k} : Set A)) := by
  -- ext `a : A` and unpack `Submodule.mem_colon`
  ext a
  constructor <;> intro h_a
  · rcases (Submodule.mem_colon).1 h_a with h
    apply (Submodule.mem_colon).2
    intro p h_p
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 h_p
    specialize h (r * k) ?_
    · exact h_p
    · rcases h with ⟨h_L, h_K⟩
      exact h_L
  · rcases (Submodule.mem_colon).1 h_a with h
    apply (Submodule.mem_colon).2
    intro p h_p
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 h_p
    have h_L : a • (r * k) ∈ L := h (r*k) h_p
    have h_K : a • (r * k) ∈ K := Ideal.mul_mem_left K a (Ideal.mul_mem_left K r h_k)
    exact ⟨h_L, h_K⟩

/-- Intersecting the left ideal with `K` does not change `IsTorsionQuot` on the right. -/
@[simp]
lemma isTorsionQuot_inter_left_iff (F : IdealFilter A) (L K : Ideal A) :
    IsTorsionQuot F L K ↔ IsTorsionQuot F (L ⊓ K) K := by
  unfold IsTorsionQuot
  constructor
  · intro h k h_k
    rcases h k h_k with ⟨I, h_I, h_I_le⟩
    refine ⟨I, h_I, ?_⟩
    · have hcol := colon_inf_eq_of_mem (L := L) (K := K) (k := k) h_k
      simpa [hcol] using h_I_le
  · intro h k h_k
    rcases h k h_k with ⟨I, h_I, h_I_le⟩
    refine ⟨I, h_I, ?_⟩
    · have hcol := colon_inf_eq_of_mem (L := L) (K := K) (k := k) h_k
      simpa [hcol] using h_I_le

@[simp] lemma isTorsion_def (F : IdealFilter A) (M : Type v) [AddCommMonoid M] [Module A M] :
    IsTorsion F M ↔ ∀ m : M, IsTorsionElem F m :=
  Iff.rfl

@[simp] lemma isTorsionQuot_def (F : IdealFilter A) (L K : Ideal A) :
    IsTorsionQuot F L K ↔ ∀ k ∈ (K : Set A), ∃ I ∈ F, I ≤ L.colon (Ideal.span {k}) :=
  Iff.rfl

/-- If `x ∈ I`, then the colon ideal `I.colon (Ideal.span {x})` is the whole ring. -/
lemma colon_span_singleton_eq_top_of_mem {I : Ideal A} {x : A} (h_x : x ∈ I) :
    I.colon (Ideal.span {x}) = ⊤ := by
  apply (Ideal.eq_top_iff_one (I.colon (Ideal.span {x}))).mpr
  apply Submodule.mem_colon.mpr
  intro p h_p
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp h_p
  simp only [one_smul, Ideal.mul_mem_left, h_x]

/-- For any filter `F` and ideal `J`, the quotient `J/J` is `F`-torsion in the sense of
`IsTorsionQuot`. -/
lemma isTorsionQuot_self (F : IdealFilter A) (I : Ideal A) :
    IsTorsionQuot F I I := by
  intro x h_x
  obtain ⟨J, h_J⟩ := F.nonempty
  exact ⟨J, h_J, by simp [colon_span_singleton_eq_top_of_mem h_x]⟩

lemma isTorsionQuot_mono_left (F : IdealFilter A)
    {I J K : Ideal A} (I_leq_J : I ≤ J) : IsTorsionQuot F I K → IsTorsionQuot F J K := by
  intro I_tors x h_x
  obtain ⟨L, ⟨L_in_F, h_L⟩⟩ := I_tors x h_x
  refine ⟨L, L_in_F, ?_⟩
  intro y h_y a h_a
  exact I_leq_J (h_L h_y h_a)

lemma isPFilter_gabrielComposition (F G : IdealFilter A) :
    Order.IsPFilter {L : Ideal A | ∃ K ∈ G, F.IsTorsionQuot L K} := by
  refine Order.IsPFilter.of_def ?nonempty ?directed ?mem_of_le
  · obtain ⟨J, h_J⟩ := G.nonempty
    exact ⟨J, J, h_J, isTorsionQuot_self F J⟩
  · rintro I ⟨K, h_K, h_IK⟩ J ⟨L, h_L, h_JL⟩
    refine ⟨I ⊓ J, ?_, inf_le_left, inf_le_right⟩
    · refine ⟨K ⊓ L, ?_, ?_⟩
      · exact Order.PFilter.inf_mem h_K h_L
      · rintro x h_x
        rcases h_x with ⟨x_K, x_L⟩
        obtain ⟨K₁, h_K₁F, h_K₁⟩ := h_IK x x_K
        obtain ⟨K₂, h_K₂F, h_K₂⟩ := h_JL x x_L
        refine ⟨K₁ ⊓ K₂, Order.PFilter.inf_mem h_K₁F h_K₂F, ?_⟩
        rintro y ⟨h_y₁, h_y₂⟩
        have h₁ := Submodule.mem_colon.mp (h_K₁ h_y₁)
        have h₂ := Submodule.mem_colon.mp (h_K₂ h_y₂)
        exact Submodule.mem_colon.mpr (fun p h_p => ⟨h₁ p h_p, h₂ p h_p⟩)
  · intro I J h_IJ ⟨K, h_K, h_IK⟩
    exact ⟨K, h_K, isTorsionQuot_mono_left F h_IJ h_IK⟩

def gabrielComposition (F G : IdealFilter A) : IdealFilter A :=
  (isPFilter_gabrielComposition F G).toPFilter

-- Declare notation for Gabriel composition
infixl:70 " • " => gabrielComposition

structure IsGabriel (F : IdealFilter A) extends F.IsUniform where
  /-- **Axiom T4 (Gabriel condition).** If there exists `J ∈ F` such that for all `x ∈ J`,
  the colon ideal `I.colon (Ideal.span {x})` belongs to `F`, then `I ∈ F`. -/
  gabriel_closed (I : Ideal A) (h : ∃ J ∈ F, ∀ x ∈ J, I.colon (Ideal.span {x}) ∈ F) : I ∈ F

theorem isGabriel_iff (F : IdealFilter A) : F.IsGabriel ↔ F.IsUniform ∧ F • F = F := by
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    ext I
    constructor <;> intro h_I
    · rcases h_I with ⟨J,h_J, h_tors⟩
      unfold IsTorsionQuot at h_tors
      refine h₂ I ⟨J, h_J, ?_⟩
      intro x h_x
      rcases h_tors x h_x with ⟨K, h_K, h_incl⟩
      exact Order.PFilter.mem_of_le h_incl h_K
    · exact ⟨I, h_I, isTorsionQuot_self F I⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    rintro I ⟨J, h_J, h_colon⟩
    rw [← h₂]
    refine ⟨J, h_J, ?_⟩
    intro x h_x
    exact ⟨I.colon (Ideal.span {x}), h_colon x h_x, by rfl⟩

end IdealFilter
