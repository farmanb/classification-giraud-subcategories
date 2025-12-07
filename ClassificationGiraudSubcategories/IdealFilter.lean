/-
Copyright (c) 2025 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.RingTheory.Ideal.Colon
/-!
# Ideal Filters

An **ideal filter** is a filter in the lattice of ideals of a ring `A`.

## Main definitions

* `IdealFilter A`: the type of an ideal filter on a ring `A`.
* `IsUniform F` : a filter `F` is uniform if whenever `I` is an ideal in the filter, then for all
`a : A`, the colon ideal `(I : a)` is in `F`.
* `IsTorsionElem` : Given a filter `F`, an element, `m`, of an `A`-module, `M`, is `F`-torsion if
there exists an ideal `L` in `F` that annihilates `m`.
* `IsTorsion` : Given a filter `F`, an `A`-module, `M`, is torsion if every element is torsion.
* `GabrielComposition` : Given two filters `F` and `G`, the Gabriel composition of `F` and `G` is
the set of ideals `L` of `A` such that there exists an ideal `K` in `G` with `K/L` `F`-torsion.
This is again a filter.
* `IsGabriel F` : a filter `F` is uniform if

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]

## Tags

category theory, ideal, filter, ultrafilter, Gabriel filter
-/
universe u v

structure IdealFilter (A : Type u) [Ring A] where
  (sets : Set (Ideal A))
  (nonempty : sets.Nonempty)
  (upward_closed : ∀ {I J : Ideal A}, I ∈ sets → I ≤ J → J ∈ sets)
  (inter_closed  : ∀ {I J : Ideal A}, I ∈ sets → J ∈ sets → I ⊓ J ∈ sets)

namespace IdealFilter

structure IsUniform {A : Type u} [Ring A] (F : IdealFilter A) : Prop where
   (colon_closed : ∀ {I : Ideal A}, I ∈ F.sets →
      ∀ a : A, (I.colon (Ideal.span {a})) ∈ F.sets)

/-- We say that an element `m : M` is `F`-torsion if it is annihilated by some ideal belonging to
the filter `F`.  That is, there exists `L ∈ F.sets` such that every `a ∈ L` satisfies
`a • m = 0`. -/
def IsTorsionElem {A : Type u} [Ring A] (F : IdealFilter A)
      {M : Type v} [AddCommMonoid M] [Module A M] (m : M) : Prop :=
   ∃ L ∈ F.sets, ∀ a ∈ L, a • m = 0

/-- We say that an `A`-module `M` is `F`-torsion if every element of `M` is `F`-torsion in the
sense of `IsTorsionElem`. -/
def IsTorsion {A : Type u} [Ring A] (F : IdealFilter A)
      (M : Type v) [AddCommMonoid M] [Module A M] : Prop :=
   ∀ m : M, IsTorsionElem F m

/-- We say that the quotient `K/L` is `F`-torsion if every element `k ∈ K` is annihilated
(modulo `L`) by some ideal in `F`.  Equivalently, for each `k ∈ K` there exists `I ∈ F.sets`
such that `I ≤ L.colon (Ideal.span {k})`. That is to say, every `a ∈ I` satisfies `a * k ∈ L`.
This formulation avoids forming the quotient module explicitly. -/
def IsTorsionQuot {A : Type u} [Ring A] (F : IdealFilter A) (L K : Ideal A) : Prop :=
   ∀ k ∈ K, ∃ I ∈ F.sets, I ≤ L.colon (Ideal.span {k})

lemma colon_inf_eq_for_mem
    {A : Type u} [Ring A] (L K : Ideal A) {k : A} (hk : k ∈ K) :
    (L ⊓ K).colon (Ideal.span ({k} : Set A)) =
      L.colon (Ideal.span ({k} : Set A)) := by
  -- ext `a : A` and unpack `Submodule.mem_colon`
  ext a
  constructor <;> intro ha
  · -- `a ∈ (L ⊓ K).colon(span{k})` ⇒ `a ∈ L.colon(span{k})`
    -- use Submodule.mem_colon to rewrite membership
    rcases (Submodule.mem_colon).1 ha with h
    -- need: ∀ p ∈ span{k}, a • p ∈ L
    apply (Submodule.mem_colon).2
    intro p hp
    -- p ∈ span{k} ⇒ p = r * k
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hp
    -- from h we know: a • (r * k) ∈ L ⊓ K
    specialize h (r * k) ?_
    · exact hp
    · rcases h with ⟨hL, hK⟩
      exact hL
  · -- same in the other direction, using that k ∈ K gives automatic K-membership
    rcases (Submodule.mem_colon).1 ha with h
    apply (Submodule.mem_colon).2
    intro p hp
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hp
    -- a • (r * k) ∈ L by h
    have hL : a • (r * k) ∈ L := by
      apply h
      exact hp
    -- and also a • (r * k) ∈ K because k ∈ K and K is an ideal
    have hK : a • (r * k) ∈ K := by
      -- use closure of K under multiplication by scalars and membership of k
      -- this is just Ideal.mul_mem_left followed by ring simp
      simpa [mul_assoc, smul_mul_assoc] using
        Ideal.mul_mem_left K a (Ideal.mul_mem_left K r hk)
    exact ⟨hL, hK⟩

@[simp]
lemma IsTorsionQuot_inter_left_iff
    {A : Type u} [Ring A] (F : IdealFilter A)
    (L K : Ideal A) :
    IsTorsionQuot F L K ↔ IsTorsionQuot F (L ⊓ K) K := by
  unfold IsTorsionQuot
  constructor
  · intro h k hk
    -- use the witness from `h`, then rewrite the colon using the lemma
    rcases h k hk with ⟨I, hI, hI_le⟩
    --refine ⟨I, hI, ?_⟩
    use I
    constructor
    · assumption
    -- `I ≤ L.colon(span{k})` and those two colon ideals are equal
    · have hcol :=
        colon_inf_eq_for_mem (L := L) (K := K) (k := k) hk
      simpa [hcol] using hI_le
  · intro h k hk
    rcases h k hk with ⟨I, hI, hI_le⟩
    --refine ⟨I, hI, ?_⟩
    use I
    constructor
    · assumption
    -- now use equality in the opposite direction
    · have hcol := colon_inf_eq_for_mem (L := L) (K := K) (k := k) hk
      simpa [hcol] using hI_le

@[simp] lemma IsTorsion_def {A : Type u} [Ring A] (F : IdealFilter A)
      (M : Type v) [AddCommMonoid M] [Module A M] : IsTorsion F M ↔ ∀ m : M, IsTorsionElem F m :=
  Iff.rfl

@[simp] lemma IsTorsionQuot_def {A : Type u} [Ring A] (F : IdealFilter A) (L K : Ideal A) :
      IsTorsionQuot F L K ↔ ∀ k ∈ (K : Set A), ∃ I ∈ F.sets, I ≤ L.colon (Ideal.span {k}) :=
  Iff.rfl

/-- If `x ∈ I`, then the colon ideal `(x : I)` is the whole ring. -/
lemma colon_span_singleton_eq_top_of_mem {A : Type u} [Ring A] {I : Ideal A} {x : A} (h_x : x ∈ I) :
    I.colon (Ideal.span {x}) = ⊤ := by
  apply (Ideal.eq_top_iff_one (I.colon (Ideal.span {x}))).mpr
  apply Submodule.mem_colon.mpr
  intro p h_p
  obtain ⟨a,rfl⟩ := Ideal.mem_span_singleton'.mp h_p
  simp only [one_smul,Ideal.mul_mem_left,h_x]

/-- For any filter `F` and ideal `J`, the quotient `J/J` is `F`-torsion in the sense of
`IsTorsionQuot`. -/
lemma IsTorsionQuot_self {A : Type u} [Ring A] (F : IdealFilter A) (I : Ideal A) :
    IsTorsionQuot F I I := by
  intro x h_x
  obtain ⟨J, h_J⟩ := F.nonempty
  --refine ⟨J, h_J, ?_⟩
  use J
  constructor
  · assumption
  · simp[colon_span_singleton_eq_top_of_mem h_x]

lemma IsTorsionQuot_mono_left {A : Type u} [Ring A] (F : IdealFilter A)
    {I J K : Ideal A} (I_leq_J : I ≤ J) : IsTorsionQuot F I K → IsTorsionQuot F J K := by
  intro I_tors x h_x
  obtain ⟨L, ⟨L_in_F, h_L⟩⟩ := I_tors x h_x
  exact ⟨L, L_in_F, fun y h_y ⦃a⦄ a_1 ↦ I_leq_J (h_L h_y a_1)⟩

def GabrielComposition {A : Type u} [Ring A] (F G : IdealFilter A) : IdealFilter A where
  sets := {L : Ideal A | ∃ K ∈ G.sets, F.IsTorsionQuot L K}
  nonempty := by
    obtain ⟨J,h_J⟩ := G.nonempty
    exact ⟨J, J, h_J, IsTorsionQuot_self F J⟩
  upward_closed := by
    rintro I J ⟨K, h_KG, h_K⟩ h_IJ
    exact ⟨K, h_KG, IsTorsionQuot_mono_left F h_IJ h_K⟩
  inter_closed := by
    rintro I J ⟨K,h_KG,h_K⟩ ⟨L,h_LG,h_L⟩
    use K ⊓ L
    constructor
    · exact G.inter_closed h_KG h_LG
    · rintro x ⟨x_K, x_L⟩
      obtain ⟨K₁, K₁_F, h_K₁⟩ := h_K x x_K
      obtain ⟨K₂, K₂_F, h_K₂⟩ := h_L x x_L
      use K₁ ⊓ K₂
      constructor
      · exact F.inter_closed K₁_F K₂_F
      · rintro y ⟨y_K₁, y_K₂⟩
        have h₁ := Submodule.mem_colon.mp (h_K₁ y_K₁)
        have h₂ := Submodule.mem_colon.mp (h_K₂ y_K₂)
        exact Submodule.mem_colon.mpr (fun p h_p => ⟨h₁ p h_p, h₂ p h_p⟩)

-- Declare notation for Gabriel composition
infixl:70 " • " => GabrielComposition

def IsGabrielFilter {A : Type u} [Ring A] (F : IdealFilter A) : Prop :=
  F.IsUniform ∧ F • F = F

end IdealFilter
