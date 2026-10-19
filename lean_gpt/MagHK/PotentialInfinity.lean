import MagHK.RadialEndpoints
import Mathlib.Topology.Order.Compact

/-! Concrete limits and boundedness of the bounded planar scalar potential. -/

noncomputable section
namespace MagHK.PotentialInfinity

open MagHK.Noninteracting MagHK.RadialEndpoints Filter Set
open scoped Topology

private theorem radialSquare_tendsto :
    Tendsto (fun r : ℝ => 1 + r ^ 2) atTop atTop :=
  tendsto_atTop_mono (fun r => by linarith) (tendsto_pow_atTop (by norm_num : 2 ≠ 0))

theorem inverseRadius_tendsto :
    Tendsto (fun r : ℝ => (Real.sqrt (1 + r ^ 2))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp radialSquare_tendsto)

theorem profileH_square (r : ℝ) : profileH r ^ 2 = 1 - 1 / (1 + r ^ 2) := by
  have hd : 1 + r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  unfold profileH
  rw [div_pow, Real.sq_sqrt (by positivity)]
  field_simp
  <;> ring

theorem profileH_tendsto_atTop : Tendsto profileH atTop (𝓝 1) := by
  have hq : Tendsto (fun r : ℝ => 1 / (1 + r ^ 2)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_apply] using! tendsto_inv_atTop_zero.comp radialSquare_tendsto
  have hs : Tendsto (fun r : ℝ => Real.sqrt (1 - 1 / (1 + r ^ 2))) atTop (𝓝 1) := by
    have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using! (hc.sub hq).sqrt
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  rw [← profileH_square, Real.sqrt_sq (profileH_bounds r hr).1]

theorem profileHPrime_tendsto_atTop : Tendsto profileHPrime atTop (𝓝 0) := by
  change Tendsto (fun r : ℝ => 1 / (Real.sqrt (1 + r ^ 2)) ^ 3) atTop (𝓝 0)
  simpa only [profileHPrime, one_div, inv_pow, zero_pow (by norm_num : 3 ≠ 0)] using!
    inverseRadius_tendsto.pow 3

theorem radius_mul_profileHPrime_tendsto :
    Tendsto (fun r : ℝ => r * profileHPrime r) atTop (𝓝 0) := by
  have h := profileH_tendsto_atTop.mul (inverseRadius_tendsto.pow 2)
  have heq (r : ℝ) : r * profileHPrime r =
      profileH r * (Real.sqrt (1 + r ^ 2))⁻¹ ^ 2 := by
    simp only [profileH, profileHPrime, div_eq_mul_inv, inv_pow]
    ring
  simpa only [← heq, zero_pow (by norm_num : 2 ≠ 0), mul_zero] using h

theorem radius_mul_profileHSecond_tendsto :
    Tendsto (fun r : ℝ => r * profileHSecond r) atTop (𝓝 0) := by
  have h := ((profileH_tendsto_atTop.pow 2).mul (inverseRadius_tendsto.pow 3)).const_mul (-3)
  have heq (r : ℝ) : r * profileHSecond r =
      -3 * (profileH r ^ 2 * (Real.sqrt (1 + r ^ 2))⁻¹ ^ 3) := by
    simp only [profileH, profileHSecond, div_eq_mul_inv, inv_pow]
    ring
  simpa only [← heq, zero_pow (by norm_num : 3 ≠ 0), mul_zero] using h

theorem profileA_tendsto_atTop (t : ℝ) (ht : 0 < t) :
    Tendsto (profileA t) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
    tendsto_inv_atTop_zero
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (profileA_pos t r ht hr).le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have h := (profileA_bounds t r ht hr).2
    rw [← one_div]
    apply (le_div_iff₀ hr).mpr
    nlinarith

private theorem profileA_correction_tendsto (t : ℝ) (ht : 0 < t) :
    Tendsto (fun r : ℝ => profileA t r * (1 - r * profileA t r)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
    (profileA_tendsto_atTop t ht)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have ha := profileA_pos t r ht hr
    have hb := profileA_bounds t r ht hr
    exact mul_nonneg ha.le (by linarith [hb.2])
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have ha := profileA_pos t r ht hr
    have hb := profileA_bounds t r ht hr
    nlinarith

theorem profileA_deriv_tendsto_atTop (t : ℝ) (ht : 0 < t) :
    Tendsto (deriv (profileA t)) atTop (𝓝 0) := by
  have hi : Tendsto (fun r : ℝ => r⁻¹ + profileH r) atTop (𝓝 1) := by
    simpa using tendsto_inv_atTop_zero.add profileH_tendsto_atTop
  have hc := profileA_correction_tendsto t ht
  have ha := (profileA_tendsto_atTop t ht).mul tendsto_inv_atTop_zero
  have hlim : Tendsto (fun r : ℝ =>
      2 * (r⁻¹ + profileH r) * (profileA t r * (1 - r * profileA t r)) -
        profileA t r * r⁻¹) atTop (𝓝 0) := by
    simpa using ((hi.const_mul 2).mul hc).sub ha
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [(profileA_hasDerivAt t r ht hr).deriv]
  field_simp
  <;> ring

def normalizedNumerator (t r : ℝ) : ℝ :=
  20 + profileHPrime r + 3 * profileH r * r⁻¹ + profileH r ^ 2 + 2 * profileA t r * r⁻¹

def normalizedDenominator (r : ℝ) : ℝ := r⁻¹ + profileH r

theorem normalizedNumerator_tendsto (t : ℝ) (ht : 0 < t) :
    Tendsto (normalizedNumerator t) atTop (𝓝 21) := by
  have hHinv := profileH_tendsto_atTop.mul tendsto_inv_atTop_zero
  have hAinv := (profileA_tendsto_atTop t ht).mul tendsto_inv_atTop_zero
  have h := ((((profileHPrime_tendsto_atTop.const_add 20).add
    (hHinv.const_mul 3)).add (profileH_tendsto_atTop.pow 2)).add (hAinv.const_mul 2))
  norm_num at h
  unfold normalizedNumerator
  simpa only [mul_assoc] using h

theorem normalizedDenominator_tendsto : Tendsto normalizedDenominator atTop (𝓝 1) := by
  simpa only [normalizedDenominator, zero_add] using!
    tendsto_inv_atTop_zero.add profileH_tendsto_atTop

theorem profileU_normalized (t r : ℝ) (hr : 0 < r) :
    profileU t r = normalizedNumerator t r / (2 * normalizedDenominator r) := by
  have hh := (profileH_bounds r hr.le).1
  have hD : 1 + r * profileH r ≠ 0 := ne_of_gt (by positivity)
  have hD' : r⁻¹ + profileH r ≠ 0 := ne_of_gt (by positivity)
  unfold profileU boundedU normalizedNumerator normalizedDenominator
  field_simp
  <;> ring

theorem profileU_tendsto_atTop (t : ℝ) (ht : 0 < t) :
    Tendsto (profileU t) atTop (𝓝 (21 / 2)) := by
  have h := (normalizedNumerator_tendsto t ht).div
    (normalizedDenominator_tendsto.const_mul 2) (by norm_num)
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (profileU_normalized t r hr).symm

def numeratorDerivative (t r : ℝ) : ℝ :=
  20 + 4 * profileHPrime r + r * profileHSecond r + profileH r ^ 2 +
    2 * profileH r * (r * profileHPrime r) + 2 * deriv (profileA t) r

theorem numeratorDerivative_tendsto (t : ℝ) (ht : 0 < t) :
    Tendsto (numeratorDerivative t) atTop (𝓝 21) := by
  have h0 := (profileHPrime_tendsto_atTop.const_mul 4).const_add 20
  have h1 := h0.add radius_mul_profileHSecond_tendsto
  have h2 := h1.add (profileH_tendsto_atTop.pow 2)
  have h3 := h2.add ((profileH_tendsto_atTop.mul radius_mul_profileHPrime_tendsto).const_mul 2)
  have h := h3.add ((profileA_deriv_tendsto_atTop t ht).const_mul 2)
  norm_num at h
  unfold numeratorDerivative
  simpa only [mul_assoc] using h

theorem profileU_deriv_normalized (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    deriv (profileU t) r = r⁻¹ *
      ((numeratorDerivative t r * normalizedDenominator r -
          normalizedNumerator t r * (profileH r + r * profileHPrime r)) /
        (2 * normalizedDenominator r ^ 2)) := by
  have hh := profileH_hasDerivAt r
  have hp := profileHPrime_hasDerivAt r
  have ha : HasDerivAt (profileA t) (deriv (profileA t) r) r :=
    (profileA_hasDerivAt t r ht hr).differentiableAt.hasDerivAt
  have hn := (((((hasDerivAt_id r).const_mul 20).add
    ((hasDerivAt_id r).mul hp)).add (hh.const_mul 3)).add
    ((hasDerivAt_id r).mul (hh.pow 2))).add (ha.const_mul 2)
  have hd := (((hasDerivAt_id r).mul hh).const_add 1).const_mul 2
  have hh0 := (profileH_bounds r hr.le).1
  have hD : 1 + r * profileH r ≠ 0 := ne_of_gt (by positivity)
  have hD' : normalizedDenominator r ≠ 0 := ne_of_gt (by
    unfold normalizedDenominator
    positivity)
  have h := hn.div hd (by positivity : 2 * (1 + r * profileH r) ≠ 0)
  have h' : HasDerivAt (profileU t)
      (r⁻¹ * ((numeratorDerivative t r * normalizedDenominator r -
        normalizedNumerator t r * (profileH r + r * profileHPrime r)) /
          (2 * normalizedDenominator r ^ 2))) r := by
    apply h.congr_deriv
    unfold numeratorDerivative normalizedNumerator normalizedDenominator at *
    simp only [id_eq, Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.div_apply,
      pow_one, mul_one, one_mul, zero_mul, mul_zero, zero_add, add_zero,
      Nat.cast_ofNat, Nat.reduceSub]
    field_simp
    <;> ring
  exact h'.deriv

theorem profileU_deriv_tendsto_atTop (t : ℝ) (ht : 0 < t) :
    Tendsto (deriv (profileU t)) atTop (𝓝 0) := by
  have hDprime := profileH_tendsto_atTop.add radius_mul_profileHPrime_tendsto
  have hnum := ((numeratorDerivative_tendsto t ht).mul normalizedDenominator_tendsto).sub
    ((normalizedNumerator_tendsto t ht).mul hDprime)
  have hden := (normalizedDenominator_tendsto.pow 2).const_mul 2
  have hlim := tendsto_inv_atTop_zero.mul (hnum.div hden (by norm_num))
  norm_num at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (profileU_deriv_normalized t r ht hr).symm

theorem profileV_tendsto_atTop (t : ℝ) (ht : 0 < t) :
    Tendsto (profileV t) atTop (𝓝 (441 / 4)) := by
  have hU := profileU_tendsto_atTop t ht
  have h := (((hU.pow 2).sub (profileU_deriv_tendsto_atTop t ht)).sub
    (hU.mul tendsto_inv_atTop_zero)).sub ((profileA_tendsto_atTop t ht).pow 2)
  norm_num at h
  simpa only [profileV, div_eq_mul_inv] using! h

theorem regularProfileV_tendsto_atTop (t : ℝ) (ht : 0 < t) :
    Tendsto (regularProfileV t) atTop (𝓝 (441 / 4)) := by
  apply (profileV_tendsto_atTop t ht).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (regularProfileV_eq t r (ne_of_gt hr)).symm

theorem continuous_halfline_bounded_of_tendsto {f : ℝ → ℝ} {L : ℝ}
    (hc : ContinuousOn f (Ici 0)) (hlim : Tendsto f atTop (𝓝 L)) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → |f r| ≤ C := by
  have htail : ∀ᶠ r in atTop, |f r| < |L| + 1 :=
    hlim.abs.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨R, hR⟩ := eventually_atTop.mp htail
  have hcompact : ContinuousOn (fun r => |f r|) (Icc 0 (max R 0)) :=
    hc.abs.mono Icc_subset_Ici_self
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hcompact
  refine ⟨max M (|L| + 1), ?_⟩
  intro r hr
  by_cases hrc : r ≤ max R 0
  · exact le_trans (hM (mem_image_of_mem _ ⟨hr, hrc⟩)) (le_max_left _ _)
  · have hrR : R ≤ r := le_trans (le_max_left _ _) (le_of_lt (lt_of_not_ge hrc))
    exact le_trans (hR r hrR).le (le_max_right _ _)

theorem regularProfileV_bounded (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → |regularProfileV t r| ≤ C :=
  continuous_halfline_bounded_of_tendsto
    (regularProfileV_contDiff t ht.le).continuous.continuousOn
    (regularProfileV_tendsto_atTop t ht)

end MagHK.PotentialInfinity
