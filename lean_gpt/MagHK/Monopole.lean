import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Checked finite calculations in the monopole construction

This file treats the scalar, algebraic, and comparison steps in the
monopole construction. It does not construct a monopole line bundle,
its Friedrichs operator, or its representation on the two-particle
Hilbert space. Hypotheses that stand for an analytic reduction are
stated explicitly in each theorem. No such reduction is declared as
an axiom here.
-/

namespace MagHK.Monopole

noncomputable def ell : ℝ := (Real.sqrt 3 - 1) / 2
noncomputable def freeGap : ℝ := Real.sqrt 15 - Real.sqrt 3
noncomputable def coulombBound : ℝ := Real.sqrt (2 / Real.sqrt 3)

theorem sqrt_three_bounds : (173205 : ℝ) / 100000 < Real.sqrt 3 ∧
    Real.sqrt 3 < (173206 : ℝ) / 100000 := by
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hnonneg := Real.sqrt_nonneg (3 : ℝ)
  constructor <;> nlinarith

theorem sqrt_fifteen_bounds : (387298 : ℝ) / 100000 < Real.sqrt 15 ∧
    Real.sqrt 15 < (387299 : ℝ) / 100000 := by
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 15 by norm_num)
  have hnonneg := Real.sqrt_nonneg (15 : ℝ)
  constructor <;> nlinarith

theorem coulomb_bound_lt : coulombBound < (107458 : ℝ) / 100000 := by
  have hthree := sqrt_three_bounds.1
  have hpos : 0 < Real.sqrt 3 := by linarith
  have hquot : 0 ≤ 2 / Real.sqrt 3 := by positivity
  have hsquare := Real.sq_sqrt hquot
  have hquotlt : 2 / Real.sqrt 3 < ((107458 : ℝ) / 100000) ^ 2 := by
    apply (div_lt_iff₀ hpos).2
    nlinarith
  unfold coulombBound
  nlinarith [Real.sqrt_nonneg (2 / Real.sqrt 3)]

/-- A rational lower bound implying the positive gap quoted in the paper. -/
theorem explicit_gap_lower_bound : (533 : ℝ) / 500 < freeGap - coulombBound := by
  have h15 := sqrt_fifteen_bounds.1
  have h3 := sqrt_three_bounds.2
  have hc := coulomb_bound_lt
  unfold freeGap
  linarith

theorem coulomb_bound_lt_gap : coulombBound < freeGap := by
  have h := explicit_gap_lower_bound
  linarith

theorem gap_positive : 0 < freeGap := by
  have h := coulomb_bound_lt_gap
  have hn : 0 ≤ coulombBound := Real.sqrt_nonneg _
  linarith

theorem gap_lt_radial_spacing : freeGap < 4 := by
  have h15 := sqrt_fifteen_bounds.2
  have h3 := sqrt_three_bounds.1
  unfold freeGap
  linarith

theorem ell_quadratic : ell * (ell + 1) = (1 : ℝ) / 2 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  unfold ell
  nlinarith

theorem lowest_sector_limit_circle : 0 < ell ∧ ell < (1 : ℝ) / 2 := by
  have h := sqrt_three_bounds
  unfold ell
  constructor <;> linarith

theorem reciprocal_radial_moment : 1 / (ell + 1 / 2) = 2 / Real.sqrt 3 := by
  unfold ell
  have h : (Real.sqrt 3 - 1) / 2 + 1 / 2 = Real.sqrt 3 / 2 := by ring
  rw [h]
  field_simp

/-- `k` parametrizes angular momentum `j = k + 1/2` at charge `|g|=1/2`.
    This is a numerical definition, not a claim about an operator spectrum. -/
noncomputable def shellEnergy (n k : ℕ) : ℝ :=
  4 * (n : ℝ) + 2 + Real.sqrt (4 * ((k : ℝ) + 1) ^ 2 - 1)

theorem lowest_shell_energy : shellEnergy 0 0 = 2 + Real.sqrt 3 := by
  norm_num [shellEnergy]

theorem next_angular_shell_energy : shellEnergy 0 1 = 2 + Real.sqrt 15 := by
  norm_num [shellEnergy]

theorem radial_spacing (n k : ℕ) : shellEnergy (n + 1) k = shellEnergy n k + 4 := by
  simp only [shellEnergy, Nat.cast_add, Nat.cast_one]
  ring

theorem shellEnergy_angular_mono (n k l : ℕ) (hkl : k ≤ l) :
    shellEnergy n k ≤ shellEnergy n l := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hl : (k : ℝ) ≤ l := by exact_mod_cast hkl
  have hrad : 4 * ((k : ℝ) + 1) ^ 2 - 1 ≤ 4 * ((l : ℝ) + 1) ^ 2 - 1 := by
    nlinarith
  unfold shellEnergy
  linarith [Real.sqrt_le_sqrt hrad]

theorem shellEnergy_radial_mono (n m k : ℕ) (hnm : n ≤ m) :
    shellEnergy n k ≤ shellEnergy m k := by
  have hcast : (n : ℝ) ≤ m := by exact_mod_cast hnm
  unfold shellEnergy
  linarith

theorem shellEnergy_ground_bound (n k : ℕ) : 2 + Real.sqrt 3 ≤ shellEnergy n k := by
  calc
    2 + Real.sqrt 3 = shellEnergy 0 0 := lowest_shell_energy.symm
    _ ≤ shellEnergy 0 k := shellEnergy_angular_mono _ _ _ (Nat.zero_le _)
    _ ≤ shellEnergy n k := shellEnergy_radial_mono _ _ _ (Nat.zero_le _)

/-- Every shell except the lowest has energy at least the first angular excitation. -/
theorem first_excited_shell_bound (n k : ℕ) (hne : n ≠ 0 ∨ k ≠ 0) :
    2 + Real.sqrt 15 ≤ shellEnergy n k := by
  rcases hne with hn | hk
  · have hnat : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hrad := shellEnergy_radial_mono 1 n k hnat
    have hang := shellEnergy_angular_mono 1 0 k (Nat.zero_le _)
    have hgap := gap_lt_radial_spacing
    rw [radial_spacing, lowest_shell_energy] at hang
    unfold freeGap at hgap
    linarith
  · have hnat : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    calc
      2 + Real.sqrt 15 = shellEnergy 0 1 := next_angular_shell_energy.symm
      _ ≤ shellEnergy 0 k := shellEnergy_angular_mono _ _ _ hnat
      _ ≤ shellEnergy n k := shellEnergy_radial_mono _ _ _ (Nat.zero_le _)

theorem higher_sector_above_limit_circle (j : ℝ) (hj : 3 / 2 ≤ j) :
    (7 : ℝ) / 2 ≤ j * (j + 1) - 1 / 4 := by
  nlinarith

/-- The elementary quadratic identity in the radial reduction. -/
theorem angular_radial_coefficient (j g : ℝ)
    (hrad : 0 ≤ (2 * j + 1) ^ 2 - 4 * g ^ 2) :
    let l := (Real.sqrt ((2 * j + 1) ^ 2 - 4 * g ^ 2) - 1) / 2
    l * (l + 1) = j * (j + 1) - g ^ 2 := by
  have hs := Real.sq_sqrt hrad
  dsimp
  nlinarith

/-- Scalar consequence of the min–max lower bound and trial-state upper bound.
    The two inequalities supplied as hypotheses are the analytic inputs. -/
theorem interacting_gap (e0 E0 E1 C : ℝ)
    (htrial : E0 ≤ 2 * e0 + C)
    (hminmax : 2 * e0 + freeGap ≤ E1)
    (hC : C ≤ coulombBound) :
    E0 < E1 ∧ freeGap - coulombBound ≤ E1 - E0 ∧
      (533 : ℝ) / 500 < E1 - E0 := by
  have h := explicit_gap_lower_bound
  constructor
  · linarith
  constructor <;> linarith

/-- The angular Coulomb kernel after the integration has been carried out. -/
noncomputable def angularKernel (s t : ℝ) : ℝ :=
  1 / max s t - min s t / (3 * (max s t) ^ 2)

theorem angularKernel_bounds (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    0 < angularKernel s t ∧ angularKernel s t ≤ 1 / max s t ∧
    1 / max s t ≤ 1 / s := by
  have hmax : 0 < max s t := lt_of_lt_of_le hs (le_max_left _ _)
  have hmin : 0 < min s t := lt_min hs ht
  have horder : min s t ≤ max s t := min_le_max
  have hsquare : 0 < (max s t) ^ 2 := sq_pos_of_pos hmax
  have hfraction : min s t / (3 * (max s t) ^ 2) ≤ 1 / (3 * max s t) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hone : 1 / (3 * max s t) < 1 / max s t := by
    apply one_div_lt_one_div_of_lt hmax
    linarith
  unfold angularKernel
  refine ⟨by linarith, ?_, ?_⟩
  · have : 0 ≤ min s t / (3 * (max s t) ^ 2) := by positivity
    linarith
  · exact one_div_le_one_div_of_le hs (le_max_left _ _)

/-- A weighted Cauchy–Schwarz interface for the Coulomb estimate.
    `C ≤ M1` comes from the angular kernel bound, and `M1² ≤ M2`
    comes from Cauchy–Schwarz for the normalized radial probability measure. -/
theorem coulomb_from_radial_moments (C M1 M2 : ℝ)
    (hCM : C ≤ M1) (hCS : M1 ^ 2 ≤ M2)
    (hM2 : M2 = 1 / (ell + 1 / 2)) : C ≤ coulombBound := by
  rw [hM2, reciprocal_radial_moment] at hCS
  have hnonneg : 0 ≤ 2 / Real.sqrt 3 := by positivity
  have hsq := Real.sq_sqrt hnonneg
  have hsnonneg := Real.sqrt_nonneg (2 / Real.sqrt 3)
  unfold coulombBound
  nlinarith

open MeasureTheory Set

/-- Probability density corresponding to the squared radial ground function. -/
noncomputable def radialDensity (s : ℝ) : ℝ :=
  (2 / Real.Gamma (ell + 3 / 2)) *
    (s ^ (2 * ell + 2) * Real.exp (-(s ^ (2 : ℝ))))

theorem radialDensity_nonneg (s : ℝ) (hs : 0 ≤ s) : 0 ≤ radialDensity s := by
  have hell := lowest_sector_limit_circle.1
  unfold radialDensity
  positivity

/-- The actual improper integral in the normalization calculation. -/
theorem radialDensity_normalized : ∫ s in Ioi (0 : ℝ), radialDensity s = 1 := by
  have hell := lowest_sector_limit_circle.1
  have hG := Real.Gamma_pos_of_pos (show 0 < ell + 3 / 2 by linarith)
  unfold radialDensity
  rw [integral_const_mul,
    integral_rpow_mul_exp_neg_rpow (by norm_num : (0 : ℝ) < 2)
      (by linarith : (-1 : ℝ) < 2 * ell + 2)]
  have he : (2 * ell + 2 + 1) / 2 = ell + 3 / 2 := by ring
  rw [he]
  field_simp

theorem radialDensity_div_sq (s : ℝ) (hs : 0 < s) :
    radialDensity s / s ^ 2 = (2 / Real.Gamma (ell + 3 / 2)) *
      (s ^ (2 * ell) * Real.exp (-(s ^ (2 : ℝ)))) := by
  unfold radialDensity
  rw [Real.rpow_add hs, Real.rpow_two]
  field_simp

/-- The inverse-square moment used in the Coulomb estimate, with no moment hypothesis. -/
theorem radial_inverse_square_moment :
    ∫ s in Ioi (0 : ℝ), radialDensity s / s ^ 2 = 1 / (ell + 1 / 2) := by
  have hell := lowest_sector_limit_circle.1
  have hG := Real.Gamma_pos_of_pos (show 0 < ell + 1 / 2 by linarith)
  calc
    _ = ∫ s in Ioi (0 : ℝ), (2 / Real.Gamma (ell + 3 / 2)) *
          (s ^ (2 * ell) * Real.exp (-(s ^ (2 : ℝ)))) :=
      setIntegral_congr_fun measurableSet_Ioi fun s hs => radialDensity_div_sq s hs
    _ = (2 / Real.Gamma (ell + 3 / 2)) *
          ((1 / 2) * Real.Gamma ((2 * ell + 1) / 2)) := by
      rw [integral_const_mul,
        integral_rpow_mul_exp_neg_rpow (by norm_num : (0 : ℝ) < 2)
          (by linarith : (-1 : ℝ) < 2 * ell)]
    _ = 1 / (ell + 1 / 2) := by
      have he : (2 * ell + 1) / 2 = ell + 1 / 2 := by ring
      have he' : ell + 3 / 2 = (ell + 1 / 2) + 1 := by ring
      rw [he, he', Real.Gamma_add_one (by linarith : ell + 1 / 2 ≠ 0)]
      field_simp

theorem radialDensity_div (s : ℝ) (hs : 0 < s) :
    radialDensity s / s = (2 / Real.Gamma (ell + 3 / 2)) *
      (s ^ (2 * ell + 1) * Real.exp (-(s ^ (2 : ℝ)))) := by
  unfold radialDensity
  rw [show 2 * ell + 2 = (2 * ell + 1) + 1 by ring, Real.rpow_add hs,
    Real.rpow_one]
  field_simp

/-- The sharper Gamma-ratio first moment stated after the elementary estimate. -/
theorem radial_inverse_moment :
    ∫ s in Ioi (0 : ℝ), radialDensity s / s =
      Real.Gamma (ell + 1) / Real.Gamma (ell + 3 / 2) := by
  have hell := lowest_sector_limit_circle.1
  calc
    _ = ∫ s in Ioi (0 : ℝ), (2 / Real.Gamma (ell + 3 / 2)) *
          (s ^ (2 * ell + 1) * Real.exp (-(s ^ (2 : ℝ)))) :=
      setIntegral_congr_fun measurableSet_Ioi fun s hs => radialDensity_div s hs
    _ = (2 / Real.Gamma (ell + 3 / 2)) *
          ((1 / 2) * Real.Gamma ((2 * ell + 1 + 1) / 2)) := by
      rw [integral_const_mul,
        integral_rpow_mul_exp_neg_rpow (by norm_num : (0 : ℝ) < 2)
          (by linarith : (-1 : ℝ) < 2 * ell + 1)]
    _ = Real.Gamma (ell + 1) / Real.Gamma (ell + 3 / 2) := by
      rw [show (2 * ell + 1 + 1) / 2 = ell + 1 by ring]
      ring

theorem radialDensity_integrable : IntegrableOn radialDensity (Ioi (0 : ℝ)) := by
  have hell := lowest_sector_limit_circle.1
  exact (integrableOn_rpow_mul_exp_neg_rpow
    (by linarith : (-1 : ℝ) < 2 * ell + 2)
    (by norm_num : (0 : ℝ) < 2)).const_mul _

theorem radial_inverse_integrable :
    IntegrableOn (fun s => radialDensity s / s) (Ioi (0 : ℝ)) := by
  have hell := lowest_sector_limit_circle.1
  apply ((integrableOn_rpow_mul_exp_neg_rpow
    (by linarith : (-1 : ℝ) < 2 * ell + 1)
    (by norm_num : (0 : ℝ) < 2)).const_mul (2 / Real.Gamma (ell + 3 / 2))).congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  exact (radialDensity_div s hs).symm

theorem radial_inverse_square_integrable :
    IntegrableOn (fun s => radialDensity s / s ^ 2) (Ioi (0 : ℝ)) := by
  have hell := lowest_sector_limit_circle.1
  apply ((integrableOn_rpow_mul_exp_neg_rpow
    (by linarith : (-1 : ℝ) < 2 * ell)
    (by norm_num : (0 : ℝ) < 2)).const_mul (2 / Real.Gamma (ell + 3 / 2))).congr
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
  exact (radialDensity_div_sq s hs).symm

/-- Cauchy–Schwarz for these specific radial moments, proved by integrating a square. -/
theorem radial_moment_cauchy_schwarz :
    (∫ s in Ioi (0 : ℝ), radialDensity s / s) ^ 2 ≤
      ∫ s in Ioi (0 : ℝ), radialDensity s / s ^ 2 := by
  let M : ℝ := ∫ s in Ioi (0 : ℝ), radialDensity s / s
  have hnonneg : 0 ≤ ∫ s in Ioi (0 : ℝ),
      (radialDensity s / s ^ 2 - (2 * M) * (radialDensity s / s) +
        M ^ 2 * radialDensity s) := by
    apply integral_nonneg_of_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hp := radialDensity_nonneg s hs.le
    have he : radialDensity s / s ^ 2 - (2 * M) * (radialDensity s / s) +
        M ^ 2 * radialDensity s = radialDensity s * (1 / s - M) ^ 2 := by
      ring
    rw [he]
    positivity
  have hadd := integral_add (radial_inverse_square_integrable.sub
      (radial_inverse_integrable.const_mul (2 * M))) (radialDensity_integrable.const_mul (M ^ 2))
  change (∫ s in Ioi (0 : ℝ),
    (radialDensity s / s ^ 2 - (2 * M) * (radialDensity s / s)) + M ^ 2 * radialDensity s) =
    (∫ s in Ioi (0 : ℝ), radialDensity s / s ^ 2 - (2 * M) * (radialDensity s / s)) +
      ∫ s in Ioi (0 : ℝ), M ^ 2 * radialDensity s at hadd
  have hsub := integral_sub radial_inverse_square_integrable
    (radial_inverse_integrable.const_mul (2 * M))
  change (∫ s in Ioi (0 : ℝ), radialDensity s / s ^ 2 - (2 * M) * (radialDensity s / s)) =
    (∫ s in Ioi (0 : ℝ), radialDensity s / s ^ 2) -
      ∫ s in Ioi (0 : ℝ), (2 * M) * (radialDensity s / s) at hsub
  rw [hadd, hsub,
    integral_const_mul, integral_const_mul, radialDensity_normalized] at hnonneg
  change 0 ≤ _ - (2 * M) * M + M ^ 2 * 1 at hnonneg
  change M ^ 2 ≤ _
  nlinarith

/-- Fully evaluated upper bound on the first radial moment. -/
theorem radial_inverse_moment_bound :
    (∫ s in Ioi (0 : ℝ), radialDensity s / s) ≤ coulombBound := by
  apply coulomb_from_radial_moments _ _ _ le_rfl radial_moment_cauchy_schwarz
  exact radial_inverse_square_moment

/-- Iterated radial integral after the angular integration. -/
noncomputable def radialCoulombExpectation : ℝ :=
  ∫ s in Ioi (0 : ℝ), radialDensity s *
    (∫ t in Ioi (0 : ℝ), radialDensity t * angularKernel s t)

theorem inner_angular_integral_nonneg (s : ℝ) (hs : 0 < s) :
    0 ≤ ∫ t in Ioi (0 : ℝ), radialDensity t * angularKernel s t := by
  apply integral_nonneg_of_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact mul_nonneg (radialDensity_nonneg t ht.le) (angularKernel_bounds s t hs ht).1.le

theorem inner_angular_integral_bound (s : ℝ) (hs : 0 < s) :
    (∫ t in Ioi (0 : ℝ), radialDensity t * angularKernel s t) ≤ 1 / s := by
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), radialDensity t * (1 / s) := by
      apply integral_mono_of_nonneg
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact mul_nonneg (radialDensity_nonneg t ht.le)
          (angularKernel_bounds s t hs ht).1.le
      · exact radialDensity_integrable.mul_const _
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact mul_le_mul_of_nonneg_left
          ((angularKernel_bounds s t hs ht).2.1.trans
            (angularKernel_bounds s t hs ht).2.2) (radialDensity_nonneg t ht.le)
    _ = 1 / s := by rw [integral_mul_const, radialDensity_normalized, one_mul]

theorem radialCoulombExpectation_bound : radialCoulombExpectation ≤ coulombBound := by
  apply le_trans _ radial_inverse_moment_bound
  unfold radialCoulombExpectation
  apply integral_mono_of_nonneg
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact mul_nonneg (radialDensity_nonneg s hs.le) (inner_angular_integral_nonneg s hs)
  · exact radial_inverse_integrable
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left (inner_angular_integral_bound s hs)
        (radialDensity_nonneg s hs.le)

/-- The Bloch-vector dot product of two normalized spinors. -/
def blochDot (a b c d : ℂ) : ℝ :=
  (2 * (a * star b).re) * (2 * (c * star d).re) +
  (2 * (a * star b).im) * (2 * (c * star d).im) +
  (Complex.normSq a - Complex.normSq b) *
    (Complex.normSq c - Complex.normSq d)

/-- Algebra behind the angular pair probability, independent of coordinate patches. -/
theorem spinor_determinant_probability (a b c d : ℂ)
    (hab : Complex.normSq a + Complex.normSq b = 1)
    (hcd : Complex.normSq c + Complex.normSq d = 1) :
    Complex.normSq (a * d - b * c) = (1 - blochDot a b c d) / 2 := by
  have hprod : (Complex.normSq a + Complex.normSq b) *
      (Complex.normSq c + Complex.normSq d) = 1 := by rw [hab, hcd]; norm_num
  simp only [Complex.normSq_apply] at hprod
  simp only [blochDot, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith [hprod]

/-- Includes both angular normalization factors and the determinant factor `1/√2`. -/
theorem normalized_angular_pair_probability (a b c d : ℂ)
    (hab : Complex.normSq a + Complex.normSq b = 1)
    (hcd : Complex.normSq c + Complex.normSq d = 1) :
    Complex.normSq (a * d - b * c) / (8 * Real.pi ^ 2) =
      (1 - blochDot a b c d) / (16 * Real.pi ^ 2) := by
  rw [spinor_determinant_probability a b c d hab hcd]
  ring

/-- Two different admissible angles yield different Coulomb values whenever both radii
    are positive. This is the scalar obstruction used in the correlation argument. -/
theorem coulomb_angular_nonconstant (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    1 / Real.sqrt (s ^ 2 + t ^ 2 + s * t) <
      1 / Real.sqrt (s ^ 2 + t ^ 2) := by
  have hbase : 0 < s ^ 2 + t ^ 2 := by positivity
  apply one_div_lt_one_div_of_lt (Real.sqrt_pos.2 hbase)
  apply Real.sqrt_lt_sqrt hbase.le
  nlinarith

theorem no_constant_coulomb_angular_factor (s t K : ℝ) (hs : 0 < s) (ht : 0 < t) :
    ¬ (∀ μ ∈ Set.Ioo (-1 : ℝ) 1,
      1 / Real.sqrt (s ^ 2 + t ^ 2 - 2 * s * t * μ) = K) := by
  intro h
  have hleft := h (-(1 : ℝ) / 2) (by constructor <;> norm_num)
  have hzero := h 0 (by constructor <;> norm_num)
  have hstrict := coulomb_angular_nonconstant s t hs ht
  have he : s ^ 2 + t ^ 2 - 2 * s * t * (-(1 : ℝ) / 2) =
      s ^ 2 + t ^ 2 + s * t := by ring
  rw [he] at hleft
  simp only [mul_zero, sub_zero] at hzero
  linarith

theorem opposite_monopole_fluxes :
    4 * Real.pi * (1 / 2 : ℝ) ≠ 4 * Real.pi * (-1 / 2 : ℝ) := by
  have h := Real.pi_pos
  nlinarith

/-- The flux-preservation property of gauge equivalence is an explicit input. -/
theorem gauge_inequivalent_of_flux (Equivalent : ℝ → ℝ → Prop)
    (hflux : ∀ g h, Equivalent g h → 4 * Real.pi * g = 4 * Real.pi * h) :
    ¬ Equivalent (1 / 2) (-1 / 2) := by
  intro heq
  exact opposite_monopole_fluxes (hflux _ _ heq)

/-- Once the spherical integral has been reduced to `4π|c|(R-1)`, its boundedness
    on all exterior annuli forces the stationary radial flux constant to vanish. -/
theorem integrable_radial_flow_constant_zero (c M : ℝ)
    (hbound : ∀ R : ℝ, 1 ≤ R → 4 * Real.pi * |c| * (R - 1) ≤ M) : c = 0 := by
  by_contra hc
  have hcoeff : 0 < 4 * Real.pi * |c| := by
    exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (abs_pos.mpr hc)
  have hm : 0 ≤ M := by simpa using hbound 1 le_rfl
  have hquot : 0 ≤ M / (4 * Real.pi * |c|) := by positivity
  have hr : 1 ≤ M / (4 * Real.pi * |c|) + 2 := by linarith
  have h := hbound (M / (4 * Real.pi * |c|) + 2) hr
  have hmul : 4 * Real.pi * |c| * (M / (4 * Real.pi * |c|)) = M := by
    field_simp
  nlinarith

/-- The elementary Young estimate finishing the Hardy/Cauchy–Schwarz argument. -/
theorem coulomb_form_young_bound (norm kinetic ε : ℝ)
    (hkin : 0 ≤ kinetic) (heps : 0 < ε) :
    Real.sqrt 2 * norm * Real.sqrt kinetic ≤
      ε * kinetic + (1 / (2 * ε)) * norm ^ 2 := by
  have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hsk := Real.sq_sqrt hkin
  have hsq := sq_nonneg (Real.sqrt 2 * ε * Real.sqrt kinetic - norm)
  rw [sub_sq, mul_pow, mul_pow, hs2, hsk] at hsq
  apply (le_of_mul_le_mul_left ?_ heps)
  field_simp
  nlinarith

end MagHK.Monopole
