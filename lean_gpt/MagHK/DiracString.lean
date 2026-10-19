import MagHK.PotentialSpaces
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The literal north Dirac potential is outside L³ + L∞ in Cartesian
Lebesgue measure. The proof uses an infinite thin cylinder along its string.
No external analytic premise is used. Values assigned on the axis do not
matter for the conclusion. -/
noncomputable section
namespace MagHK.DiracString
open MeasureTheory Set Filter
open MagHK.ConstructionData MagHK.PotentialSpaces
open scoped ENNReal

/-- Euclidean radius in the Cartesian product coordinates used by the paper. -/
def radius (p : Space) : ℝ := Real.sqrt (p.1.1 ^ 2 + p.1.2 ^ 2 + p.2 ^ 2)

/-- North-gauge Dirac potential of strength g, extended by zero on the axis.
Off the axis this is g (1 − cos θ)/(r sin θ) e_φ. -/
def potential (g : ℝ) (p : Space) : Space :=
  let c := g * (1 - p.2 / radius p) / (p.1.1 ^ 2 + p.1.2 ^ 2)
  ((-p.1.2 * c, p.1.1 * c), 0)

/-- Its actual contraction with the azimuthal coordinate tangent. -/
theorem azimuthal_component (g : ℝ) (p : Space)
    (hp : p.1.1 ^ 2 + p.1.2 ^ 2 ≠ 0) :
    (potential g p).1.1 * (-p.1.2) + (potential g p).1.2 * p.1.1 =
      g * (1 - p.2 / radius p) := by
  unfold potential
  dsimp
  field_simp
  ring

private theorem cylinder_bound (g δ : ℝ) (hδ : 0 < δ) (p : Space)
    (hx : p.1.1 ∈ Ioo 0 δ) (hy : p.1.2 ∈ Ioo δ (2 * δ)) (hz : p.2 < 0) :
    |g| / (5 * δ) ≤ ‖potential g p‖ := by
  have hy0 : 0 < p.1.2 := lt_trans hδ hy.1
  have hQ : 0 < p.1.1 ^ 2 + p.1.2 ^ 2 := by nlinarith [sq_nonneg p.1.1]
  have hQupper : p.1.1 ^ 2 + p.1.2 ^ 2 ≤ 5 * δ ^ 2 := by
    have hxsq := (sq_le_sq₀ hx.1.le hδ.le).mpr hx.2.le
    have hysq := (sq_le_sq₀ hy0.le (by positivity : 0 ≤ 2 * δ)).mpr hy.2.le
    nlinarith
  have hr : 0 < radius p := Real.sqrt_pos.mpr (by
    nlinarith [sq_nonneg p.2])
  have hs : 1 ≤ 1 - p.2 / radius p := by
    have := div_nonpos_of_nonpos_of_nonneg hz.le hr.le
    linarith
  have ha : |(potential g p).1.1| =
      p.1.2 * |g| * (1 - p.2 / radius p) / (p.1.1 ^ 2 + p.1.2 ^ 2) := by
    simp only [potential, abs_mul, abs_neg, abs_div,
      abs_of_pos hy0, abs_of_nonneg (by linarith : 0 ≤ 1 - p.2 / radius p),
      abs_of_pos hQ]
    ring
  have hlo : |g| * δ ≤ p.1.2 * |g| * (1 - p.2 / radius p) := by
    have h₁ : |g| * δ ≤ p.1.2 * |g| := by nlinarith [abs_nonneg g, hy.1]
    have h₂ := mul_le_mul_of_nonneg_left hs (mul_nonneg hy0.le (abs_nonneg g))
    simp only [mul_one] at h₂
    exact h₁.trans h₂
  have hpart : |g| / (5 * δ) ≤ |(potential g p).1.1| := by
    rw [ha, div_le_div_iff₀ (by positivity) hQ]
    have h₁ := mul_le_mul_of_nonneg_left hQupper (abs_nonneg g)
    have h₂ := mul_le_mul_of_nonneg_right hlo (by positivity : 0 ≤ 5 * δ)
    nlinarith
  exact hpart.trans (by
    change |(potential g p).1.1| ≤ max (max |(potential g p).1.1|
      |(potential g p).1.2|) |(potential g p).2|
    exact (le_max_left _ _).trans (le_max_left _ _))

/-- Every nonzero north Dirac potential fails the manuscript's vector sum
space. This includes both monopole charges, g = ±1/2. -/
theorem outside_vector_sum (g : ℝ) (hg : g ≠ 0) : ¬ VectorSumSpace (potential g) := by
  rintro ⟨f, h, hf, hh, he⟩
  have htop : eLpNormEssSup h volume < ∞ := by
    simpa only [eLpNorm_exponent_top] using hh.2
  obtain ⟨B, hB⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp htop
  have hb : ∀ᵐ p, ‖h p‖ ≤ (B : ℝ) := by
    filter_upwards [hB] with p hp
    exact_mod_cast hp
  let δ : ℝ := |g| / (10 * ((B : ℝ) + 1))
  have hδ : 0 < δ := div_pos (abs_pos.mpr hg) (by positivity)
  let s : Set Space := (Ioo 0 δ ×ˢ Ioo δ (2 * δ)) ×ˢ Iio 0
  have hs : MeasurableSet s := (measurableSet_Ioo.prod measurableSet_Ioo).prod measurableSet_Iio
  have hlower : |g| / (5 * δ) = 2 * ((B : ℝ) + 1) := by
    dsimp [δ]
    field_simp
    ring
  have hbound : ∀ᵐ p ∂volume.restrict s, ‖(1 : ℝ)‖ ≤ ‖f p‖ := by
    filter_upwards [ae_restrict_mem hs, ae_restrict_of_ae hb] with p hp hhp
    have hlarge := cylinder_bound g δ hδ p hp.1.1 hp.1.2 hp.2
    rw [hlower, he p] at hlarge
    have hn := norm_add_le (f p) (h p)
    simp only [norm_one]
    linarith [B.coe_nonneg]
  have hconst : MemLp (fun _ : Space => (1 : ℝ)) 3 (volume.restrict s) :=
    (hf.mono_measure Measure.restrict_le_self).mono aestronglyMeasurable_const hbound
  have hfinite : volume s < ∞ := by
    have h := (memLp_const_iff (by norm_num : (3 : ℝ≥0∞) ≠ 0)
      (by norm_num : (3 : ℝ≥0∞) ≠ ∞)).mp hconst
    simpa using h
  have hinfinite : volume s = ∞ := by
    change (volume : Measure ((ℝ × ℝ) × ℝ))
      ((Ioo 0 δ ×ˢ Ioo δ (2 * δ)) ×ˢ Iio 0) = ∞
    rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod,
      Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo, Real.volume_Iio]
    rw [ENNReal.mul_top]
    simp [ENNReal.ofReal_eq_zero, not_le.mpr hδ, show δ < 2 * δ by linarith]
  rw [hinfinite] at hfinite
  exact (lt_irrefl _ hfinite)

/-- The exclusion is unchanged by arbitrary null-set modifications. -/
theorem outside_vector_sum_of_ae (g : ℝ) (hg : g ≠ 0) (A : Space → Space)
    (hA : A =ᵐ[volume] potential g) : ¬ VectorSumSpace A := by
  rintro ⟨f, h, hf, hh, he⟩
  apply outside_vector_sum g hg
  have hfe : f =ᵐ[volume] fun p => potential g p - h p := by
    filter_upwards [hA] with p hp
    rw [← hp, he p]
    simp
  refine ⟨(fun p => potential g p - h p), h, (memLp_congr_ae hfe).mp hf, hh, ?_⟩
  intro p
  simp

theorem opposite_charges_outside :
    ¬ VectorSumSpace (potential (1 / 2)) ∧ ¬ VectorSumSpace (potential (-1 / 2)) :=
  ⟨outside_vector_sum _ (by norm_num), outside_vector_sum _ (by norm_num)⟩

end MagHK.DiracString
