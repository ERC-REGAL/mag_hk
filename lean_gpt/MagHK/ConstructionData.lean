import MagHK.PotentialInfinity
import MagHK.Curvature
import MagHK.NormContinuity
import MagHK.Axial

/-!
Concrete construction data in three Cartesian coordinates. This assembles
the smoothness, global bounds, nonzero curvature and equal radial norms.
It does not assert the spectral ground-state conclusion of the manuscript.
-/

noncomputable section
namespace MagHK.ConstructionData

open MagHK.Cartesian MagHK.RadialEndpoints MagHK.Noninteracting
open scoped ContDiff

theorem boundedScalar_eq_regularProfileV (t : ℝ) (ht : 0 < t) (p : ℝ × ℝ) :
    boundedScalar t p = regularProfileV t (Real.sqrt (radiusSq p)) := by
  let r := Real.sqrt (radiusSq p)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : radiusSq p = r ^ 2 := (Real.sq_sqrt (radiusSq_nonneg p)).symm
  by_cases hr : r = 0
  · have hp0 : p = (0, 0) := by
      have hq : p.1 ^ 2 + p.2 ^ 2 = 0 := by
        change radiusSq p = 0
        rw [hrsq, hr]
        norm_num
      have hx : p.1 = 0 := by nlinarith [sq_nonneg p.2, sq_nonneg p.1]
      have hy : p.2 = 0 := by nlinarith [sq_nonneg p.2, sq_nonneg p.1]
      exact Prod.ext hx hy
    change boundedScalar t p = regularProfileV t r
    rw [hp0, hr, boundedScalar_origin, regularProfileV_at_zero]
    ring
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    exact (boundedScalar_agrees_off_axis t r p ht hrpos hrsq).trans
      (regularProfileV_eq t r hr).symm

theorem boundedScalar_bounded (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, ∀ p : ℝ × ℝ, |boundedScalar t p| ≤ C := by
  obtain ⟨C, hC⟩ := MagHK.PotentialInfinity.regularProfileV_bounded t ht
  refine ⟨C, fun p => ?_⟩
  rw [boundedScalar_eq_regularProfileV t ht p]
  exact hC _ (Real.sqrt_nonneg _)

abbrev Space := (ℝ × ℝ) × ℝ

def bounded3Vector (t : ℝ) (p : Space) : Space := (boundedVector t p.1, 0)
def bounded3Scalar (t c : ℝ) (p : Space) : ℝ :=
  boundedScalar t p.1 + MagHK.Axial.potential c p.2

def gaussian3Vector (t : ℝ) (p : Space) : Space := (gaussianVector t p.1, 0)
def gaussian3Scalar (t c : ℝ) (p : Space) : ℝ :=
  gaussianScalar t p.1 + c ^ 2 * p.2 ^ 2 - c

theorem bounded3Vector_smooth (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (bounded3Vector t) :=
  ((boundedVector_contDiff t ht).comp contDiff_fst).prodMk contDiff_const

theorem bounded3Scalar_smooth (t c : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (bounded3Scalar t c) :=
  ((boundedScalar_contDiff t ht).comp contDiff_fst).add
    ((MagHK.Axial.potential_smooth c).comp contDiff_snd)

theorem gaussian3Vector_smooth (t : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (gaussian3Vector t) :=
  ((gaussianVector_contDiff t ht).comp contDiff_fst).prodMk contDiff_const

theorem gaussian3Scalar_smooth (t c : ℝ) (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (gaussian3Scalar t c) :=
  (((gaussianScalar_contDiff t ht).comp contDiff_fst).add
    (contDiff_const.mul (contDiff_snd.pow 2))).sub contDiff_const

theorem bounded3Vector_bound (t : ℝ) (ht : 0 ≤ t) (p : Space) :
    ‖bounded3Vector t p‖ ≤ t * Real.exp 2 + 1 := by
  change max ‖boundedVector t p.1‖ ‖(0 : ℝ)‖ ≤ _
  rw [norm_zero]
  exact max_le (boundedVector_bound t ht p.1) (by positivity)

theorem gaussian3Vector_bound (t : ℝ) (ht : 0 ≤ t) (p : Space) :
    ‖gaussian3Vector t p‖ ≤ t + 1 := by
  change max ‖gaussianVector t p.1‖ ‖(0 : ℝ)‖ ≤ _
  rw [norm_zero]
  exact max_le (gaussianVector_bound t ht p.1) (by linarith)

theorem bounded3Scalar_bounded (t c : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, ∀ p : Space, |bounded3Scalar t c p| ≤ C := by
  obtain ⟨C, hC⟩ := boundedScalar_bounded t ht
  refine ⟨C + c ^ 2, fun p => ?_⟩
  exact (abs_add_le _ _).trans (add_le_add (hC p.1) (MagHK.Axial.potential_bounded c p.2))

/-- There is an actual positive normalization parameter giving smooth,
globally bounded three-dimensional potentials and nonzero planar curl.
The remaining spectral assembly is deliberately not hidden in this result. -/
theorem exists_bounded_smooth_data (c : ℝ) :
    ∃ t : ℝ, 0 < t ∧
      ContDiff ℝ ∞ (bounded3Vector t) ∧
      ContDiff ℝ ∞ (bounded3Scalar t c) ∧
      (∃ C : ℝ, ∀ p : Space, ‖bounded3Vector t p‖ ≤ C) ∧
      (∃ C : ℝ, ∀ p : Space, |bounded3Scalar t c p| ≤ C) ∧
      planarCurl (boundedVector t) ≠ 0 ∧
      radialNormF t = radialNormG t ∧ 0 < radialNormF t := by
  obtain ⟨t, ht, heq, hpos⟩ := exists_bounded_parameter
  exact ⟨t, ht, bounded3Vector_smooth t ht.le, bounded3Scalar_smooth t c ht.le,
    ⟨t * Real.exp 2 + 1, bounded3Vector_bound t ht.le⟩,
    bounded3Scalar_bounded t c ht, bounded_curl_nonzero t ht, heq, hpos⟩

end MagHK.ConstructionData
