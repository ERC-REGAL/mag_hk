import MagHK.GaussianCompactness
import MagHK.PotentialSpaces
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The confining Gaussian scalar really lies outside the scalar sum space.
No external operator or regularity premise is needed for this obstruction. -/
noncomputable section
namespace MagHK.GaussianOutside
open MeasureTheory Set
open MagHK.ConstructionData MagHK.PotentialSpaces
open scoped ENNReal

theorem volume_univ_space : volume (univ : Set Space) = ∞ := by
  change (volume : Measure ((ℝ × ℝ) × ℝ)) univ = ∞
  rw [Measure.volume_eq_prod, ← univ_prod_univ, Measure.prod_prod,
    Measure.volume_eq_prod, ← univ_prod_univ, Measure.prod_prod]
  simp [Real.volume_univ]

theorem norm_sq_le_sum (x : Space) : ‖x‖ ^ 2 ≤ x.1.1 ^ 2 + x.1.2 ^ 2 + x.2 ^ 2 := by
  simp only [Prod.norm_def, Real.norm_eq_abs]
  rcases le_total |x.1.1| |x.1.2| with h | h
  · rw [max_eq_right h]
    rcases le_total |x.1.2| |x.2| with hz | hz
    · rw [max_eq_right hz, sq_abs]
      nlinarith [sq_nonneg x.1.1, sq_nonneg x.1.2]
    · rw [max_eq_left hz, sq_abs]
      nlinarith [sq_nonneg x.1.1, sq_nonneg x.2]
  · rw [max_eq_left h]
    rcases le_total |x.1.1| |x.2| with hz | hz
    · rw [max_eq_right hz, sq_abs]
      nlinarith [sq_nonneg x.1.1, sq_nonneg x.1.2]
    · rw [max_eq_left hz, sq_abs]
      nlinarith [sq_nonneg x.1.2, sq_nonneg x.2]

theorem quadratic_not_scalar_sum (v : Space → ℝ) (C : ℝ)
    (hv : ∀ x, ‖x‖ ^ 2 - C ≤ v x) : ¬ ScalarSumSpace v := by
  rintro ⟨f, g, hf, hg, he⟩
  have htop : eLpNormEssSup g volume < ∞ := by
    simpa only [eLpNorm_exponent_top] using hg.2
  obtain ⟨B, hB⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp htop
  have hb : ∀ᵐ x, ‖g x‖ ≤ (B : ℝ) := by
    filter_upwards [hB] with x hx
    exact_mod_cast hx
  let R : ℝ := |C| + B + 2
  let s : Set Space := (Metric.closedBall 0 R)ᶜ
  have hclosed : IsClosed (Metric.closedBall (0 : Space) R) :=
    (isCompact_closedBall (0 : Space) R).isClosed
  have hs : MeasurableSet s := hclosed.measurableSet.compl
  have hR : 2 ≤ R := by dsimp [R]; nlinarith [abs_nonneg C, B.coe_nonneg]
  have hbound : ∀ᵐ x ∂volume.restrict s, ‖(1 : ℝ)‖ ≤ ‖f x‖ := by
    filter_upwards [ae_restrict_mem hs, ae_restrict_of_ae hb] with x hx hgx
    have hr : R < ‖x‖ := by
      simpa only [s, mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hx
    have hC := le_abs_self C
    have hbx := hv x
    have hgc : g x ≤ (B : ℝ) := (le_abs_self _).trans (by simpa using hgx)
    rw [he x] at hbx
    simp only [Real.norm_eq_abs, abs_one]
    have hfx := le_abs_self (f x)
    dsimp [R] at hr
    nlinarith [sq_nonneg (‖x‖ - 1)]
  have hconst : MemLp (fun _ : Space => (1 : ℝ)) (3 / 2)
      (volume.restrict s) :=
    (hf.mono_measure Measure.restrict_le_self).mono aestronglyMeasurable_const hbound
  have hfinite : volume s < ∞ := by
    have h := (memLp_const_iff (by norm_num : (3 / 2 : ℝ≥0∞) ≠ 0)
      (ENNReal.div_ne_top (by norm_num) (by norm_num) : (3 / 2 : ℝ≥0∞) ≠ ∞)).mp hconst
    simpa using h
  have hball : volume (Metric.closedBall (0 : Space) R) ≠ ∞ :=
    (isCompact_closedBall (0 : Space) R).measure_lt_top.ne
  have hinfinite : volume s = ∞ := by
    change volume (Metric.closedBall (0 : Space) R)ᶜ = ∞
    rw [measure_compl hclosed.measurableSet hball, volume_univ_space]
    exact ENNReal.top_sub hball
  rw [hinfinite] at hfinite
  exact (lt_irrefl _ hfinite)

theorem gaussian_scalar_outside (t c : ℝ) (ht : 0 ≤ t) (hc : 1 < c) :
    ¬ ScalarSumSpace (gaussian3Scalar t c) := by
  apply quadratic_not_scalar_sum _ (2 + 2 * t + c)
  intro x
  have hp := MagHK.PartnerAsymptotics.gaussianScalar_quadratic_lower_bound t
    (Real.sqrt (MagHK.Cartesian.radiusSq x.1)) ht
  rw [Real.sq_sqrt (by unfold MagHK.Cartesian.radiusSq; positivity)] at hp
  change MagHK.Cartesian.radiusSq x.1 - (2 + 2 * t) ≤ MagHK.Cartesian.gaussianScalar t x.1 at hp
  have hz : x.2 ^ 2 ≤ c ^ 2 * x.2 ^ 2 := by
    nlinarith [mul_nonneg (by nlinarith : 0 ≤ c ^ 2 - 1) (sq_nonneg x.2)]
  have hn := norm_sq_le_sum x
  change ‖x‖ ^ 2 - (2 + 2 * t + c) ≤
    MagHK.Cartesian.gaussianScalar t x.1 + c ^ 2 * x.2 ^ 2 - c
  unfold MagHK.Cartesian.radiusSq at hp
  linarith

end MagHK.GaussianOutside
