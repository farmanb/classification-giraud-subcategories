import ClassificationGiraudSubcategories.IdealFilter
import Mathlib.RingTheory.Ideal.Colon

variable (A : Type*) [Ring A]

structure RightLinearTopology extends IdealFilter A where
  (colon_closed : ∀ {I : RightIdeal A} (a : A),
    I ∈ sets → (I.colon (RightIdeal.span {a})) ∈ sets)
