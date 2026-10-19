import MagHK.ConstructionData
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Actual membership of the bounded potentials in the stated sum spaces. -/
noncomputable section
namespace MagHK.PotentialSpaces
open MeasureTheory MagHK.ConstructionData

/-- The scalar sum space L^(3/2)+L^∞ in ordinary Cartesian Lebesgue measure. -/
def ScalarSumSpace (v : Space → ℝ) : Prop :=
  ∃ f g : Space → ℝ, MemLp f (3 / 2) ∧ MemLp g ⊤ ∧ ∀ x, v x = f x + g x

/-- The vector sum space L^3+L^∞, using the equivalent finite product norm. -/
def VectorSumSpace (A : Space → Space) : Prop :=
  ∃ f g : Space → Space, MemLp f 3 ∧ MemLp g ⊤ ∧ ∀ x, A x = f x + g x

theorem bounded_vector_memLp (t : ℝ) (ht : 0 ≤ t) : MemLp (bounded3Vector t) ⊤ :=
  memLp_top_of_bound (bounded3Vector_smooth t ht).continuous.aestronglyMeasurable
    (t * Real.exp 2 + 1) (Filter.Eventually.of_forall (bounded3Vector_bound t ht))

theorem gaussian_vector_memLp (t : ℝ) (ht : 0 ≤ t) : MemLp (gaussian3Vector t) ⊤ :=
  memLp_top_of_bound (gaussian3Vector_smooth t ht).continuous.aestronglyMeasurable
    (t + 1) (Filter.Eventually.of_forall (gaussian3Vector_bound t ht))

theorem bounded_scalar_memLp (t c : ℝ) (ht : 0 < t) : MemLp (bounded3Scalar t c) ⊤ := by
  obtain ⟨C, hC⟩ := bounded3Scalar_bounded t c ht
  apply memLp_top_of_bound (bounded3Scalar_smooth t c ht.le).continuous.aestronglyMeasurable C
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hC x)

theorem bounded_sum_spaces (t c : ℝ) (ht : 0 < t) :
    ScalarSumSpace (bounded3Scalar t c) ∧ VectorSumSpace (bounded3Vector t) := by
  constructor
  · exact ⟨0, bounded3Scalar t c, MemLp.zero, bounded_scalar_memLp t c ht,
      fun x => by simp⟩
  · exact ⟨0, bounded3Vector t, MemLp.zero, bounded_vector_memLp t ht.le,
      fun x => by simp⟩

end MagHK.PotentialSpaces
