import ClassificationGiraudSubcategories.RightIdeal

variable (A : Type*) [Ring A]

structure IdealFilter where
  (sets : Set (RightIdeal A))
  (nonempty : sets.Nonempty)
  (upward_closed : ∀ {I J : RightIdeal A}, I ∈ sets → I ≤ J → J ∈ sets)
  (inter_closed  : ∀ {I J : RightIdeal A}, I ∈ sets → J ∈ sets → I ⊓ J ∈ sets)
